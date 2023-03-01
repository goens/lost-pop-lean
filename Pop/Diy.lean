-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

import Pop.Litmus
import Pop.Arch
import Pop.Util
import Pop.Pop

namespace Diy

declare_syntax_cat test
declare_syntax_cat init
declare_syntax_cat thread_line
declare_syntax_cat threads_header
declare_syntax_cat instruction
declare_syntax_cat assignment
declare_syntax_cat argument
declare_syntax_cat result
declare_syntax_cat result_term

syntax ident ident (str)? "{" init "}" threads_header ";" sepBy(thread_line,";") result : test
syntax sepBy(assignment,";",";",allowTrailingSep) : init
syntax ident "=" num : assignment

syntax sepBy(ident, "|") : threads_header
syntax sepBy(instruction, "|") : thread_line
syntax ident argument,* : instruction
syntax "[" ident "]" : argument
syntax "$" num : argument
syntax ident : argument

syntax "exists" result_term : result
syntax num ":" ident "=" num : result_term
syntax result_term "∧" result_term : result_term
syntax result_term "̈̈∨" result_term : result_term
syntax "(" result_term ")" : result_term

-- Example: SB.litmus
/-
syntax "[diy|" test "]" : term
def SB := [diy|
X86 SB
"Fre PodWR Fre PodWR"
{ x=0; y=0; }
 P0          | P1          ;
 MOV [y],$1  | MOV [x],$1  ; --#(a)Wy1  | (c)Wx1
 MOV EAX,[x] | MOV EAX,[y] ; --#(b)Rx0  | (d)Ry0
exists (0:EAX=0 ∧ 1:EAX=0)
]
-/
inductive TokenizerState
  | normal
  | string
  | curlyBrackets

def removeCommentsLineCharListAux : List Char → TokenizerState → List Char
  | c::cs, .normal => match c with
      | '\"' => c::(removeCommentsLineCharListAux cs .string)
      | '{'  => c::(removeCommentsLineCharListAux cs .curlyBrackets)
      | ';'  => c::[]
      | _    => c::(removeCommentsLineCharListAux cs .normal)
  | c::cs, .string => match c with
      | '\"' => c::(removeCommentsLineCharListAux cs .normal)
      | _    => c::(removeCommentsLineCharListAux cs .string)
  | c::cs, .curlyBrackets => match c with
      | '}' => c::(removeCommentsLineCharListAux cs .normal)
      | _    => c::(removeCommentsLineCharListAux cs .curlyBrackets)
  | l, _ => l

def removeCommentsLineCharList : List Char → List Char
  | l => removeCommentsLineCharListAux l .normal

def replaceAnds : List Char → List Char
  | c1::c2::cs => if c1 == '/' && c2 == '\\' then '∧'::cs else c1::(replaceAnds (c2::cs))
  | l => l

def preprocessLine : String → String :=
λ s => { data := replaceAnds (removeCommentsLineCharList s.data) }

def preprocess (input : String) : String :=
  let lines := input.splitOn "\n"
  String.intercalate "\n" $ lines.map preprocessLine

def parse (input : String) : IO Lean.Syntax := do
  let env ← Lean.importModules [{ module := `Pop.Diy }] {}
  let preprocessed := preprocess input
  match Lean.Parser.runParserCategory env `test preprocessed with
    | .error msg => IO.println s!"Error: {msg}"; return default
    | .ok stx => return stx


variable {arch : ArchType}

def mkProgram (header : Lean.TSyntax `threads_header) (threads : Lean.TSyntaxArray `thread_line) : @Pop.ProgramState arch.getInstArch :=
  -- TODO: parse program
  #[]

def mkExpected (result : Lean.TSyntax `result) : Litmus.Outcome :=
 -- TODO: parse expected
 []

def mkInitState (header : Lean.TSyntax `threads_header) (init : Lean.TSyntax `init) : @Pop.SystemState arch.getInstArch.req :=
 -- TODO: parse init
  default

def mkInitTransitions (program : @Pop.ProgramState arch.getInstArch) : List (@Pop.Transition arch.getInstArch) :=
  let basicReqs := (@Pop.ProgramState.all arch.getInstArch program).map $
     @Pop.Transition.getAcceptBasicRequest? arch.getInstArch
  let vars : List Pop.Address := Util.filterNones $ basicReqs.map λ obr => match obr with
    | none => none
    | some br =>  @Pop.BasicRequest.address? arch.getInstArch.req br
  let initWrites := @Pop.initZeroesUnpropagatedTransitions arch.getInstArch arch.getInstLitmusSyntax "default" (List.range vars.length)
  let initPropagates :=  @Pop.mkPropagateTransitions arch.getInstArch (List.range initWrites.length) (List.range program.size).tail! -- tail! : remove 0 because of accept
  initWrites ++ initPropagates

def mkLitmusTest (input : Lean.TSyntax `test) : Option $ @Litmus.Test arch.getInstArch :=
  match input with
    | `(test| $a:ident $n:ident $[$d:str]? { $ini } $header ; $[$thread_lines];* $res:result) =>
      if toString arch != a.getId.toString then panic! "Architecture mismatch: {a.getId.toString} != {arch}"
      else
        let name := n.getId.toString
        let descr := match d with
          | some str => str.getString
          | none => ""
        let program := mkProgram header thread_lines arch
        let initState := mkInitState header ini
        let initTrans := mkInitTransitions program
        let expected := mkExpected res
        some { initTransitions := i nitTrans, program := program, expected := expected, initState := initState,
               description := descr, axiomaticAllowed := .unknown, guideTraces := [], name := name : Litmus.Test }
    | _ => none

end Diy
