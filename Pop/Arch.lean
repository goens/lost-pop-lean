-- Author(s): Andrés Goens
-- See Copyright Notice in LICENSE

import Pop.Arch.PTX
import Pop.Arch.TSO
import Pop.Arch.ARM
import Pop.Arch.XC
import Pop.Arch.Compound
import Pop.Arch.CompoundXCTSO
import Pop.Util
import Litmus.PTX
import Litmus.TSO
import Litmus.ARM
import Litmus.XC
import Litmus.Compound
import Litmus.CompoundXCTSO

inductive ArchType
  | PTX
  | TSO
  | ARM
  | XC
  | Compound
  | CompoundXCTSO
  deriving Inhabited

instance : ToString ArchType where toString := λ a => match a with
  | .PTX => "PTX"
  | .TSO => "TSO"
  | .ARM => "ARM"
  | .XC => "XC"
  | .CompoundXCTSO => "Compound XC TSO"
  | .Compound => "Compound TSO-PTX"


def parseArchitecture :  List ArchType → String → Except String ArchType
  | archs, input => do
  let some n := input.trim.toNat?
    | Except.error $ s!"Invalid input (must be a number from 1 to {archs.length})"
      ++ s!"Received:{input}"
  if n == 0 then
    Except.error s!"Invalid index ({n}), must be between 1 and {archs.length}"
  let some arch := archs[n - 1]?
    | Except.error s!"Invalid index ({n}), must be between 1 and {archs.length}"
  Except.ok arch

def ArchType.available : List ArchType := [ArchType.PTX, ArchType.TSO, ArchType.Compound, ArchType.ARM]

def parseArchitectureString : String → Except String ArchType
  | "PTX" => .ok ArchType.PTX
  | "TSO" => .ok ArchType.TSO
  | "ARM" => .ok ArchType.ARM
  | "XC" => .ok ArchType.XC
  | "XCTSO" => .ok ArchType.CompoundXCTSO
  | "Compound" => .ok ArchType.Compound
  | s => .error s!"Unknown architecture ({s}). Available: {ArchType.available}"

def selectArchitecture : IO.FS.Stream → IO (Option ArchType)
  | stdin => do
    let available := ArchType.available
    let availableStr := "Select Architecture. Available:\n" ++ String.intercalate "\n" (available.zip (List.range available.length) |>.map λ (arch,n) => s!"{ n+1}. {arch}")
    let res ← Util.selectLoop availableStr (parseArchitecture available) stdin
    return res

def ArchType.getInstArch : ArchType → Pop.Arch
  | .PTX => PTX.instArch
  | .TSO => x86.instArch
  | .ARM => ARM.instArch
  | .XC => XC.instArch
  | .Compound => Compound.instArch
  | .CompoundXCTSO => CompoundXCTSO.instArch

def ArchType.getInstLitmusSyntax : (arch : ArchType) → @Pop.LitmusSyntax arch.getInstArch
  | .PTX => PTX.Litmus.instLitmusSyntaxInstArch
  | .TSO => x86.Litmus.instLitmusSyntaxInstArch
  | .XC => XC.Litmus.instLitmusSyntaxInstArch
  | .ARM => ARM.Litmus.instLitmusSyntaxInstArch
  | .Compound => Compound.Litmus.instLitmusSyntaxInstArch
  | .CompoundXCTSO => CompoundXCTSO.Litmus.instLitmusSyntaxInstArch

def x86Imported := x86.Litmus.allTests.map Compound.importTSOLitmus
def ptxImported := PTX.Litmus.allTests.map Compound.importPTXLitmus
def xcImported := XC.Litmus.allTests.map CompoundXCTSO.importXCLitmus

def ArchType.getLitmusTests : (arch : ArchType) → List (@Litmus.Test arch.getInstArch)
  | .PTX => PTX.Litmus.allTests
  | .TSO => x86.Litmus.allTests
  | .ARM => ARM.Litmus.allTests
  | .XC => XC.Litmus.allTests
  | .CompoundXCTSO => CompoundXCTSO.Litmus.allTests ++ xcImported
  | .Compound => Compound.Litmus.allTests ++ x86Imported ++ ptxImported
