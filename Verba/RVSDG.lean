import Verba.BinOp
import Verba.Word

open BinOp
open Word

namespace RVSDG

/-
В данном файле я пишу RVSDG IR.

Это промежуточное представление состоит из регионов.
Каждый регион - это направленный ациклический граф узлов.
У региона есть набор входов и набор выходов, а так же набор внутренних узлов.


-/

-- set_option trace.Meta.synthInstance true

abbrev NodeId := Nat

inductive EnvError where
  | notFound (id : NodeId)
deriving Repr, BEq, DecidableEq

inductive EvalError where
  | undefinedNodeId (err : EnvError)
deriving Repr, BEq, DecidableEq


inductive Region where
  | result (out_id : List NodeId)
  | const (id : NodeId) (val : Word) (rest : Region)
  | binOp (id : NodeId) (op : BinOp) (src1_id src2_id : NodeId) (rest : Region)
  | gamma (id : List NodeId) (cond_id : NodeId) (thenReg elseReg : Region) (rest : Region)
deriving Repr, BEq
