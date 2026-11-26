import Verba.BinOp
import Verba.Word

open BinOp Word

namespace SimpleTestLang

inductive Stmt where
  | set   (name : String) (val : Int)
  | binOp (name : String) (op : BinOp) (src1 src2 : String)
deriving Repr, BEq

abbrev STLProg := List Stmt
