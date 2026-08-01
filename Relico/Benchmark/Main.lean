import Std

def main (arguments : List String) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "/bin/bash"
    args :=
      #["tools/relico_bench.sh"]
        ++ arguments.toArray
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }

  child.wait
