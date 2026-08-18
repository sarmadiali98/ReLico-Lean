#!/usr/bin/env python3
"""
Measure the corpus consequence of REQUIRING actor priorities.

The user settled: absent @priority => reject. The open sub-question is the SCOPE
of "absent". Two candidate rules:

  BLANKET : every actor instance in the model must carry @priority.
  FANIN   : every actor instance that is one of >=2 senders into the SAME msgsrv
            on the SAME receiver instance must carry @priority, and those
            priorities must be pairwise distinct. Everything else is exempt.

FANIN is the rule that matches the tie rule's scope (5.3). BLANKET is simpler to
state but may reject models the paper itself uses as motivating examples.

This script computes, for all 49 upstream models, which would be REJECTED under
each rule and why. Read-only; parses .rebeca text only.

USAGE
    unzip examples.zip -d /tmp/relico_corpus      # the upstream ReLico snapshot
    python3 measure_priority_requirement.py /tmp/relico_corpus

Read-only. Parses .rebeca text; touches nothing else.
"""
import re
import sys
import os
import glob

# --------------------------------------------------------------------------
# lexical helpers
# --------------------------------------------------------------------------

def strip_comments(text):
    text = re.sub(r'/\*.*?\*/', ' ', text, flags=re.S)
    text = re.sub(r'//[^\n]*', ' ', text)
    return text


def match_block(text, open_index):
    """Given index of a '{', return index just past its matching '}'."""
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


def find_keyword_block(text, pattern):
    """Yield (match, body_text) for each `pattern ... {` construct."""
    for m in re.finditer(pattern, text):
        brace = text.find('{', m.end() - 1)
        if brace < 0:
            continue
        end = match_block(text, brace)
        if end < 0:
            continue
        yield m, text[brace + 1:end - 1]


# --------------------------------------------------------------------------
# model parsing
# --------------------------------------------------------------------------

SEND_RE = re.compile(r'\b([A-Za-z_]\w*)\s*\.\s*([A-Za-z_]\w*)\s*\(')
KNOWNREBEC_RE = re.compile(r'\b([A-Za-z_]\w*)\s+([A-Za-z_]\w*)\s*;')
MSGSRV_RE = re.compile(r'\bmsgsrv\s+([A-Za-z_]\w*)\s*\(')
INSTANCE_RE = re.compile(
    r'(?:@priority\s*\(\s*(\d+)\s*\)\s*)?'
    r'\b([A-Za-z_]\w*)\s+([A-Za-z_]\w*)\s*'
    r'\(([^()]*)\)\s*:\s*\(([^()]*)\)\s*;'
)
# statevars can legally be named like known rebecs; collect them to avoid
# mistaking a local/statevar call for a send.
RESERVED_TARGETS = {'self'}


class ReactiveClass(object):
    def __init__(self, name, body):
        self.name = name
        self.body = body
        self.knownrebecs = []          # ordered list of known-rebec NAMES
        self.msgsrvs = []              # ordered msgsrv names
        self.sends = set()             # (target_name, msgsrv_name)

        for m, kbody in find_keyword_block(body, r'\bknownrebecs\b'):
            for km in KNOWNREBEC_RE.finditer(kbody):
                self.knownrebecs.append(km.group(2))

        for m in MSGSRV_RE.finditer(body):
            self.msgsrvs.append(m.group(1))

        # Every send site anywhere in the class (constructor + all msgsrvs).
        # `may-send` over-approximation: conditionals are ignored, which is the
        # correct direction for a conservative static well-formedness check.
        known = set(self.knownrebecs) | RESERVED_TARGETS
        for sm in SEND_RE.finditer(body):
            target, srv = sm.group(1), sm.group(2)
            if target in known:
                self.sends.add((target, srv))


class Instance(object):
    def __init__(self, name, cls, priority, bindings):
        self.name = name
        self.cls = cls
        self.priority = priority       # int or None
        self.bindings = bindings       # ordered list of instance names / 'null'


class Model(object):
    def __init__(self, path):
        self.path = path
        self.name = os.path.basename(path)[:-len('.rebeca')]
        raw = strip_comments(open(path, 'r', errors='replace').read())

        self.classes = {}
        self.static_defeaters = []     # constructs that make topology non-static
        class_spans = []
        for m, cbody in find_keyword_block(raw, r'\breactiveclass\s+([A-Za-z_]\w*)\s*(?:\([^)]*\))?\s*'):
            cname = m.group(1)
            self.classes[cname] = ReactiveClass(cname, cbody)
            class_spans.append((m.start(), raw.find('{', m.end() - 1)))

        # main block: last top-level `main`
        self.instances = []
        self.parse_errors = []
        mainm = None
        for m, mbody in find_keyword_block(raw, r'\bmain\b'):
            mainm = mbody
        if mainm is None:
            self.parse_errors.append('no main block found')
            mainm = ''
        for im in INSTANCE_RE.finditer(mainm):
            prio, cls, name, binds, _args = im.groups()
            if cls not in self.classes:
                # e.g. a stray declaration or an unknown class: record, skip
                self.parse_errors.append('instance %r of unknown class %r' % (name, cls))
                continue
            bindings = [b.strip() for b in binds.split(',') if b.strip()]
            self.instances.append(
                Instance(name, cls, int(prio) if prio else None, bindings))

        self.by_name = dict((i.name, i) for i in self.instances)

        # ---- constructs that defeat STATIC topology resolution ----------
        # If any of these appear, the (receiver, msgsrv) -> senders map is not
        # statically computable, so the fan-in sets computed below are
        # UNDER-approximations and every verdict about this model is unsound.
        cnames = set(self.classes)
        for cname, cls in self.classes.items():
            cbody = cls.body
            for m, sbody in find_keyword_block(cbody, r'\bstatevars\b'):
                for dm in KNOWNREBEC_RE.finditer(sbody):
                    if dm.group(1) in cnames:
                        self.static_defeaters.append(
                            'A1 rebec-typed statevar %s.%s' % (cname, dm.group(2)))
            for mm in re.finditer(r'\bmsgsrv\s+([A-Za-z_]\w*)\s*\(([^)]*)\)', cbody):
                for param in mm.group(2).split(','):
                    param = param.strip()
                    if param and param.split()[0] in cnames:
                        self.static_defeaters.append(
                            'A2 rebec-typed param %s.%s(%s)' % (cname, mm.group(1), param))
            for cm in re.finditer(r'\(\s*\(\s*([A-Za-z_]\w*)\s*\)\s*sender\s*\)\s*\.', cbody):
                if cm.group(1) in cnames:
                    self.static_defeaters.append('A3 send to ((%s)sender) in %s'
                                                 % (cm.group(1), cname))
            for am in re.finditer(r'[A-Za-z_]\w*\s*=\s*\(\s*([A-Za-z_]\w*)\s*\)\s*sender', cbody):
                if am.group(1) in cnames:
                    self.static_defeaters.append('A4 captures sender in %s' % cname)

        self.analysable = (not self.static_defeaters) and bool(self.instances)

        # ---- resolve topology into fan-in sets -------------------------
        self.fanin = {}                # (receiver_instance, msgsrv) -> set(sender)
        self.unresolved = []
        for inst in self.instances:
            cls = self.classes[inst.cls]
            kmap = {}
            for idx, kname in enumerate(cls.knownrebecs):
                if idx < len(inst.bindings):
                    kmap[kname] = inst.bindings[idx]
            for (target, srv) in cls.sends:
                if target == 'self':
                    receiver = inst.name
                elif target in kmap:
                    receiver = kmap[target]
                else:
                    self.unresolved.append((inst.name, target, srv))
                    continue
                if receiver == 'null' or receiver not in self.by_name:
                    if receiver != 'null':
                        self.unresolved.append((inst.name, target, srv))
                    continue
                # only count it if the receiving class actually has that msgsrv
                rcls = self.classes[self.by_name[receiver].cls]
                if srv not in rcls.msgsrvs:
                    continue
                self.fanin.setdefault((receiver, srv), set()).add(inst.name)

    # ---- the two candidate rules ----------------------------------------

    def verdict_blanket(self):
        missing = [i.name for i in self.instances if i.priority is None]
        return (not missing), missing

    def verdict_fanin(self):
        """Returns (accepted, list_of_reasons)."""
        reasons = []
        for (recv, srv), senders in sorted(self.fanin.items()):
            if len(senders) < 2:
                continue
            senders = sorted(senders)
            missing = [s for s in senders if self.by_name[s].priority is None]
            prios = [self.by_name[s].priority for s in senders
                     if self.by_name[s].priority is not None]
            if missing:
                reasons.append('ABSENT  %s.%s <- {%s}; unannotated: %s'
                               % (recv, srv, ', '.join(senders), ', '.join(missing)))
            elif len(set(prios)) != len(prios):
                reasons.append('TIE     %s.%s <- {%s}; priorities %s'
                               % (recv, srv, ', '.join(senders), prios))
        return (not reasons), reasons

    def contended(self):
        return [(k, sorted(v)) for k, v in sorted(self.fanin.items()) if len(v) >= 2]


# --------------------------------------------------------------------------

def main():
    root = sys.argv[1]
    paths = sorted(p for p in glob.glob(os.path.join(root, '**', '*.rebeca'), recursive=True)
                   if '__MACOSX' not in p)
    models = [Model(p) for p in paths]
    print('parsed %d models' % len(models))

    blanket_rej, fanin_rej, both_ok = [], [], []
    for mo in models:
        b_ok, b_missing = mo.verdict_blanket()
        f_ok, f_reasons = mo.verdict_fanin()
        if not b_ok:
            blanket_rej.append((mo, b_missing))
        if not f_ok:
            fanin_rej.append((mo, f_reasons))
        if b_ok and f_ok:
            both_ok.append(mo)

    print('')
    print('=' * 74)
    print('HEADLINE')
    print('=' * 74)
    print('  models total                      : %d' % len(models))
    print('  REJECTED by BLANKET rule          : %d' % len(blanket_rej))
    print('  REJECTED by FANIN rule            : %d' % len(fanin_rej))
    print('  accepted by both                  : %d' % len(both_ok))
    print('  models with >=1 contended msgsrv  : %d'
          % sum(1 for mo in models if mo.contended()))

    print('')
    print('=' * 74)
    print('REJECTED BY FAN-IN-SCOPED RULE  (these are the real cost)')
    print('=' * 74)
    if not fanin_rej:
        print('  (none)')
    for mo, reasons in fanin_rej:
        print('  %-34s %s' % (mo.name, reasons[0]))
        for r in reasons[1:]:
            print('  %-34s %s' % ('', r))

    print('')
    print('=' * 74)
    print('REJECTED BY BLANKET BUT ACCEPTED BY FAN-IN  (what scoping buys)')
    print('=' * 74)
    fanin_rej_names = set(mo.name for mo, _ in fanin_rej)
    saved = [(mo, ms) for mo, ms in blanket_rej if mo.name not in fanin_rej_names]
    for mo, missing in saved:
        print('  %-34s unannotated-but-harmless: %s' % (mo.name, ', '.join(missing)))
    print('  --- %d models saved by scoping ---' % len(saved))

    print('')
    print('=' * 74)
    print('CONTENDED MSGSRVS  (>=2 senders -> where priority is load-bearing)')
    print('=' * 74)
    for mo in models:
        c = mo.contended()
        if not c:
            continue
        print('  %s' % mo.name)
        for (recv, srv), senders in c:
            annot = ['%s=%s' % (s, mo.by_name[s].priority) for s in senders]
            print('      %s.%s  <-  %s' % (recv, srv, ', '.join(annot)))

    print('')
    print('=' * 74)
    print('PARSE HEALTH  (unresolved sends / errors must be ~0 to trust the above)')
    print('=' * 74)
    bad = 0
    for mo in models:
        if mo.parse_errors or mo.unresolved:
            bad += 1
            print('  %s' % mo.name)
            for e in mo.parse_errors[:6]:
                print('      err: %s' % e)
            for u in mo.unresolved[:6]:
                print('      unresolved send: %s -> %s.%s' % u)
    if not bad:
        print('  clean: every send target resolved, every instance class known')
    else:
        print('  --- %d models with parse anomalies ---' % bad)

    print('')
    print('=' * 74)
    print('SANITY CROSSCHECK vs recorded corpus inventory')
    print('=' * 74)
    with_actor = [mo for mo in models if any(i.priority is not None for i in mo.instances)]
    partial = [mo for mo in with_actor if any(i.priority is None for i in mo.instances)]
    print('  models using actor @priority at all : %d   (memory says 19)' % len(with_actor))
    print('  of those, PARTIALLY annotated       : %d   (memory says 16)' % len(partial))
    ties_anywhere = []
    for mo in models:
        ps = [i.priority for i in mo.instances if i.priority is not None]
        if len(set(ps)) != len(ps):
            ties_anywhere.append(mo.name)
    print('  models with actor-priority TIES     : %d   (memory says 3: %s)'
          % (len(ties_anywhere), ', '.join(ties_anywhere)))


    print('')
    print('=' * 74)
    print('DECISION-GRADE TABLE  (only statically analysable models counted)')
    print('=' * 74)
    nonstatic = [mo for mo in models if mo.static_defeaters]
    nomain = [mo for mo in models if not mo.instances]
    clean = [mo for mo in models if mo.analysable]
    print('  49 upstream models')
    print('    - %2d with NON-STATIC topology (rebec-typed statevars/params, sender casts)'
          % len(nonstatic))
    for mo in nonstatic:
        print('         %-26s %s' % (mo.name, mo.static_defeaters[0]))
    print('    - %2d with no live main block (cannot be measured)' % len(nomain))
    for mo in nomain:
        print('         %-26s' % mo.name)
    print('    = %2d statically analysable' % len(clean))
    print('')
    c_blanket = [mo for mo in clean if not mo.verdict_blanket()[0]]
    c_fanin = [mo for mo in clean if not mo.verdict_fanin()[0]]
    c_contended = [mo for mo in clean if mo.contended()]
    print('  Of those %d:' % len(clean))
    print('    BLANKET rule rejects   %2d  (%d%%)'
          % (len(c_blanket), round(100.0 * len(c_blanket) / max(1, len(clean)))))
    print('    FANIN   rule rejects   %2d  (%d%%)'
          % (len(c_fanin), round(100.0 * len(c_fanin) / max(1, len(clean)))))
    print('    have >=1 contended msgsrv  %2d' % len(c_contended))
    print('    contended AND accepted     %2d  <- models where actor priority is'
          % len([mo for mo in c_contended if mo.verdict_fanin()[0]]))
    print('                                   load-bearing and fully specified')
    print('')
    print('  FANIN rejections among the clean set:')
    for mo in c_fanin:
        print('    %-26s %d contended msgsrv(s), first: %s'
              % (mo.name, len(mo.contended()), mo.verdict_fanin()[1][0][:70]))
    print('')
    print('  Contended AND accepted (the deterministic-fragment models):')
    for mo in c_contended:
        if mo.verdict_fanin()[0]:
            for (recv, srv), senders in mo.contended():
                print('    %-26s %s.%s <- %s' % (mo.name, recv, srv,
                      ', '.join('%s=%s' % (s, mo.by_name[s].priority) for s in senders)))
    print('')
    print('  KeepAlive check -- is `ka` EVER a sender into a contended msgsrv?')
    ka_contended = []
    for mo in models:
        for (recv, srv), senders in mo.contended():
            for s in senders:
                if s.lower().startswith('ka') or 'keepalive' in mo.by_name[s].cls.lower():
                    ka_contended.append('%s: %s -> %s.%s' % (mo.name, s, recv, srv))
    print('    %s' % ('NO -- never. The upstream exemption idiom is free.'
                      if not ka_contended else ka_contended))
    print('')
    print('  Tie rule cost -- upstream models with actor-priority ties:')
    for mo in models:
        ps = [i.priority for i in mo.instances if i.priority is not None]
        if len(set(ps)) != len(ps):
            ok, reasons = mo.verdict_fanin()
            tie_at_fanin = [r for r in reasons if r.startswith('TIE')]
            print('    %-26s contended msgsrvs: %d;  tie AT a contended msgsrv: %s'
                  % (mo.name, len(mo.contended()), 'YES' if tie_at_fanin else 'no'))


if __name__ == '__main__':
    main()
