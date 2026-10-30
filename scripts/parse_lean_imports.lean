import Lean

/-!
# Parse Lean import headers

The executable `main` reads source paths from standard input and writes one
header record followed by the imported module names for each readable file.
It is the small Lean-side parser used by the repository's import-boundary
audit script.
-/

open Lean

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let path := line.trimAscii.toString
    try
      let source ← IO.FS.readFile path
      let header ← Lean.parseImports' source path
      stdout.putStrLn s!"H\t{path}\t{header.isModule}"
      for imp in header.imports do
        let moduleName := imp.module.toString
        if moduleName != "Init" && !moduleName.startsWith "Init." then
          stdout.putStrLn s!"I\t{path}\t{moduleName}"
    catch e =>
      stdout.putStrLn s!"E\t{path}\t{e.toString.replace "\n" " "}"
