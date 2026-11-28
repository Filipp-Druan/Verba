import Verba.Word
import Verba.BinOp
open Word BinOp

mutual
  inductive Expr where
    | ident (name : String)
    | num (val : Word)
    | binOp (op_name : BinOp) (left right : Expr)

  inductive Stmt where
    | letStmt (name : String) (val : Expr)
    | letMutStmt (name : String) (val : Expr)
    | ifStmt (cond : Expr) (thenBlock elseBlock : List Stmt)
    | assignStmt (name : String) (val : Expr)
end

declare_syntax_cat simple_expr
declare_syntax_cat simple_stmt

syntax ident : simple_expr
syntax num   : simple_expr
syntax:70 simple_expr:70 "*" simple_expr:71 : simple_expr
syntax:70 simple_expr:70 "/" simple_expr:71 : simple_expr
syntax:65 simple_expr:65 "+" simple_expr:66 : simple_expr
syntax:65 simple_expr:65 "-" simple_expr:66 : simple_expr

syntax "let" ident "=" simple_expr ";"       : simple_stmt
syntax "let" "mut" ident "=" simple_expr ";" : simple_stmt

syntax "if" simple_expr "{" simple_stmt* "}" "else" "{" simple_stmt* "}" : simple_stmt

syntax "simple" "{" simple_stmt* "}" : term
