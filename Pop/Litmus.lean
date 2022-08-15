import Pop.Util
import Pop.Pop


namespace Litmus
open Util Pop

variable [Arch]
abbrev Outcome := List $ ThreadId × Address × Value
abbrev Test := (List Transition × ProgramState) × Outcome  × SystemState


def addressValuePretty : Address × Value → String
  | (_, none) => "invalid outcome!"
  | (addr, some val) => s!"{addr.prettyPrint} = {val}"

def Outcome.prettyPrint : Litmus.Outcome → String
  | outcome =>
  let threads : List Litmus.Outcome := outcome.groupBy (·.1 == ·.1)
  let threadStrings := threads.map
    λ th => String.intercalate "; " $ th.map (addressValuePretty $ Prod.snd ·)
  String.intercalate " || " threadStrings


end Litmus
