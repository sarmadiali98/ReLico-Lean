#!/usr/bin/env python3
"""
Census of DTR constructs in the upstream corpus that the translator's frontend
must take a position on. Two groups:

  A. TOPOLOGY-DEFEATING constructs. If a model can hold or pass rebec references
     at runtime, the (receiver, msgsrv) -> senders map is not statically
     computable, so neither the fan-in port layout nor any actor-priority
     well-formedness check is decidable. These must be REJECTED by the frontend
     with a named diagnostic, and the paper needs a side condition saying so.

       A1 rebec-typed statevar        e.g. statevars { CommunicationDevice d; }
       A2 rebec-typed msgsrv param    e.g. msgsrv broadcast(CommunicationDevice r, ...)
       A3 cast of `sender`            e.g. ((CommunicationDevice)sender).m(...)
       A4 assignment from `sender`    e.g. d = (CommunicationDevice)sender;

  B. Constructs that are merely UNIMPLEMENTED but in-fragment, for sizing the
     later stages.

Also re-checks the two models my fan-in measurement flagged as anomalous, so the
headline numbers can be reported with the anomalies accounted for rather than
swept aside.

USAGE
    unzip examples.zip -d /tmp/relico_corpus      # the upstream ReLico snapshot
    python3 census_topology_constructs.py /tmp/relico_corpus

Read-only. Parses .rebeca text; touches nothing else.
"""
import re
import os
import sys
import glob


def strip_comments(text):
    text = re.sub(r'/\*.*?\*/', ' ', text, flags=re.S)
    text = re.sub(r'//[^\n]*', ' ', text)
    return text


def match_block(text, open_index):
    depth = 0
    i = open_index
    while i < len(text):
        if text[i] == '{':
            depth += 1
        elif text[i] == '}':
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return -1


def blocks(text, pattern):
    for m in re.finditer(pattern, text):
        b = text.find('{', m.end() - 1)
        if b < 0:
            continue
        e = match_block(text, b)
        if e < 0:
            continue
        yield m, text[b + 1:e - 1]


def analyse(path):
    raw_with_comments = open(path, 'r', errors='replace').read()
    raw = strip_comments(raw_with_comments)

    classes = {}
    for m, body in blocks(raw, r'\breactiveclass\s+([A-Za-z_]\w*)\s*(?:\([^)]*\))?\s*'):
        classes[m.group(1)] = body
    cnames = set(classes)

    f = {'A1': [], 'A2': [], 'A3': [], 'A4': []}

    for cname, body in classes.items():
        # A1: rebec-typed state variables
        for m, sbody in blocks(body, r'\bstatevars\b'):
            for dm in re.finditer(r'\b([A-Za-z_]\w*)\s+([A-Za-z_]\w*)\s*;', sbody):
                if dm.group(1) in cnames:
                    f['A1'].append('%s.%s %s' % (cname, dm.group(1), dm.group(2)))
        # A2: rebec-typed msgsrv parameters
        for mm in re.finditer(r'\bmsgsrv\s+([A-Za-z_]\w*)\s*\(([^)]*)\)', body):
            for param in mm.group(2).split(','):
                param = param.strip()
                if not param:
                    continue
                ty = param.split()[0]
                if ty in cnames:
                    f['A2'].append('%s.%s(%s)' % (cname, mm.group(1), param))
        # A3: send to a cast of sender
        for cm in re.finditer(r'\(\s*\(\s*([A-Za-z_]\w*)\s*\)\s*sender\s*\)\s*\.\s*([A-Za-z_]\w*)\s*\(', body):
            if cm.group(1) in cnames:
                f['A3'].append('%s: ((%s)sender).%s(...)' % (cname, cm.group(1), cm.group(2)))
        # A4: capture sender into a variable
        for am in re.finditer(r'([A-Za-z_]\w*)\s*=\s*\(\s*([A-Za-z_]\w*)\s*\)\s*sender', body):
            if am.group(2) in cnames:
                f['A4'].append('%s: %s = (%s)sender' % (cname, am.group(1), am.group(2)))

    has_live_main = any(True for _ in blocks(raw, r'\bmain\b'))
    # a main that exists only inside a comment block
    main_in_comments = (not has_live_main) and re.search(r'\bmain\b\s*\{', raw_with_comments) is not None

    return f, has_live_main, main_in_comments, len(cnames)


def main():
    root = sys.argv[1]
    paths = sorted(p for p in glob.glob(os.path.join(root, '**', '*.rebeca'), recursive=True)
                   if '__MACOSX' not in p)

    print('=' * 74)
    print('A. TOPOLOGY-DEFEATING CONSTRUCTS  (must be rejected by the frontend)')
    print('=' * 74)
    hit_models = {}
    for p in paths:
        f, live_main, main_commented, ncls = analyse(p)
        flags = [k for k in ('A1', 'A2', 'A3', 'A4') if f[k]]
        if flags:
            name = os.path.relpath(p, root)
            hit_models[name] = (f, flags)
    if not hit_models:
        print('  (none)')
    for name, (f, flags) in sorted(hit_models.items()):
        print('  %s   [%s]' % (name, ' '.join(flags)))
        for k in flags:
            for item in f[k][:4]:
                print('        %s  %s' % (k, item))
    print('')
    print('  models affected: %d of %d' % (len(hit_models), len(paths)))

    print('')
    print('=' * 74)
    print('MAIN-BLOCK HEALTH  (a model with no live main cannot be measured)')
    print('=' * 74)
    for p in paths:
        f, live_main, main_commented, ncls = analyse(p)
        if not live_main:
            print('  %-50s no live main; main inside /* */ : %s'
                  % (os.path.relpath(p, root), main_commented))


if __name__ == '__main__':
    main()
