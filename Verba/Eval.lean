import Verba.RVSDG
import Verba.Word
import Verba.BinOp

open RVSDG Word BinOp


namespace Eval

abbrev Env := List (NodeId × Word)

def envGet (env : Env) (id : NodeId) : Except EnvError Word :=
  match List.lookup id env with
  | .some val => .ok val
  | .none => .error $ .notFound id

def evalBinOp (op : BinOp) (val1 val2 : Word) : Word :=
  match op with
  | .add => val1 + val2
  | .sub => val1 - val2
  | .mul => val1 * val2
  | .signDiv => .sdiv val1 val2
  | .usignDiv => .udiv val1 val2

def getNodeVal (env : Env) (id : NodeId) : Except EvalError Word :=
   envGet env id |> .mapError EvalError.undefinedNodeId

def evalRegion (region : Region) (env : Env) : Except EvalError Word :=
  match region with
    | .result out => getNodeVal env out
    | .const id val rest =>
      let new_env := (id, val) :: env
      evalRegion rest new_env

    | .binOp id op src1_id src2_id rest => do
      let val1 ← getNodeVal env src1_id
      let val2 ← getNodeVal env src2_id

      let res := evalBinOp op val1 val2

      let new_env := (id, res) :: env

      evalRegion rest new_env

    | .gamma id cond_id thenReg elseReg rest => do
      let cond ←  getNodeVal env cond_id
      let res ← if cond = 0 then
        evalRegion elseReg env
      else
        evalRegion thenReg env

      let new_env := (id, res) :: env

      evalRegion rest new_env
