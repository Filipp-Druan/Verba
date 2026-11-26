namespace BinOp

inductive BinOp where
  | add | mul | sub | signDiv | usignDiv
deriving Repr, BEq
