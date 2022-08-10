import Pop.Util
import Pop.Pop


namespace Litmus
open Util Pop

variable [Arch]
abbrev Test := (List Transition × ProgramState) × SystemState

end Litmus
