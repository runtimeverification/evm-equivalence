/-! # Stats 4 Nerds

  Script that scrapes the codebase to get statistics 4 da nerds.
 -/

open System

/--
`fileStats` are the statistics we're tracking for every file, which are
`dfs`: amount of `def` declarations
`str`: amount of `structure` declarations
`ind`: amount of `inductive` declarations
`thm`: amount of `theorem` declarations
`axs`: amount of `axsiom` declarations
-/
structure fileStats where
  dfs : Nat
  str : Nat
  ind : Nat
  thm : Nat
  axs : Nat

instance : Inhabited fileStats where
  default := {dfs := 0, str := 0, ind := 0, thm := 0, axs := 0}

instance : ToString fileStats where
  toString := fun fs =>
    s!"Definitions: {fs.dfs}\n"++
    s!"Structures : {fs.str}\n"++
    s!"Inductives:  {fs.ind}\n"++
    s!"Theorems:    {fs.thm}\n"++
    s!"Axioms:      {fs.axs}"


def fileStats.incrDfs (fs : fileStats) : fileStats :=
  {fs with dfs := fs.dfs + 1}

def fileStats.incrStr (fs : fileStats) : fileStats :=
  {fs with str := fs.str + 1}

def fileStats.incrInd (fs : fileStats) : fileStats :=
  {fs with ind := fs.ind + 1}

def fileStats.incrThm (fs : fileStats) : fileStats :=
  {fs with thm := fs.thm + 1}

def fileStats.incrAxs (fs : fileStats) : fileStats :=
  {fs with axs := fs.axs + 1}

/--
Disjunction of two `String.startsWith`
-/
def String.swOr (s : String) (s1 : String) (s2 : String) : Bool :=
  s.startsWith s1  || s.startsWith s2

/--
Criteria to count a declaration
-/
def addLineStats (fs : fileStats) (line : String) : fileStats :=
  if line.swOr "def "       "  def "       then fs.incrDfs else
  if line.swOr "structure " "  structure " then fs.incrStr else
  if line.swOr "inductive " "  inductive " then fs.incrInd else
  if line.swOr "theorem "   "  theorem "   then fs.incrThm else
  if line.swOr "axiom "     "  axiom "     then fs.incrAxs else fs

def projectDir : IO FilePath := do
  IO.currentDir

def mkSubDir (subDir : String) (dir : IO FilePath := projectDir) : IO FilePath :=
  do pure ((←dir) / {toString := subDir})

def equivalenceDir := mkSubDir "EvmEquivalence"

def kevm2LeanDir := mkSubDir "KEVM2Lean" equivalenceDir

def skipCodeGen (fp : FilePath) : IO Bool := do
  if fp = (←kevm2LeanDir) then pure false else pure true

def includeCodeGen (fp : FilePath) : IO Bool := do
  pure !(←skipCodeGen fp)

/--
Get Lean files.
Lean files are files with the `.lean` extension that don't begin with `.#`
-/
def getFiles (dir : IO FilePath) (skipFn : FilePath → IO Bool := default) : IO (Array FilePath) := do
  let mut arr ← FilePath.walkDir (←dir) skipFn
  arr := (arr.filter (fun fp : FilePath => fp.toString.endsWith ".lean"))
  pure (arr.filter (fun fp : FilePath => !fp.toString.startsWith ".#"))

/--
Adds the stats of a given file to some provided stats
-/
def addStats (fp : FilePath) (stats : fileStats := default) : IO fileStats :=  do
  if !(←fp.pathExists) || (←fp.isDir) then pure stats else
  let f ← IO.FS.Handle.mk fp .read
  let mut line ← f.getLine
  let mut s := stats
  while line.utf8ByteSize ≠ 0 do
    s := addLineStats s line
    line ← f.getLine
  pure s

def countDeclarations (dir : IO FilePath) (criteria : FilePath → IO Bool) : IO fileStats := do
  let fs ← getFiles dir criteria
  let rec countFiles (fs : List FilePath) (stats : fileStats) : IO fileStats := do
    match fs with
    | [] => pure stats
    | x :: xs => countFiles xs (←addStats x stats)
  countFiles fs.toList default

def main : IO Unit := do
  let declarations ← countDeclarations equivalenceDir skipCodeGen
  let genDeclarations ← countDeclarations kevm2LeanDir (fun _ => pure true)
  IO.println "Number of declarations for the generated code 🤖"
  IO.println genDeclarations
  IO.println ""
  IO.println "Number of declarations for the manually produced code 📝"
  IO.println declarations
