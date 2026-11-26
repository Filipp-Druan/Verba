/-
В этом файле я пишу игрушечный компилятор на основе RVSDG.

У нас есть два представления программы - список стейтментов и регион.

Список стейтментов содержит в себе набор присваиваний значений переменным. Переменным можно присвоить константное значение, можно присвоить результат математической операции. В любом случае, значение должно быть присвоено переменной перед тем, как его используют:

a = 5
b = 10
c = a + b
d = c * a

Обращаться к переменным, которые не были объявлены мы не можем. При этом, допустимо, если какая-то часть кода осталась висеть в воздухе и нигде не была использована.

Регион - это направленный ациклический граф. В нём есть вычислительные узлы, которые могут получать данные из предыдущих узлов. Граф можно представить таблицей:

0) const 5
1) const 10
2) 0.* + 1.*
3) 2.* + 0.*

Граф ациклический. Последующие узлы могут брать результаты предыдущих, но предыдущие вообще ничего не знают о последующих.

На графе мы можем проводить оптимизации: частично вычислять константы и удалять мёртвый код.
-/

inductive BinOp where
  | add | mul | sub
deriving Repr, BEq

inductive Stmt where
  | set   (name : String) (val : Int)
  | binOp (name : String) (op : BinOp) (src1 src2 : String)
deriving Repr, BEq


abbrev ProgSrc := List Stmt

abbrev NodeID := Nat

inductive Node where
  | const (val : Int)
  | binOp (op : BinOp) (src1 src2 : NodeID)
deriving Repr

def isLookForward (node : Node) (index : Nat) : Prop :=
  match node with
  | .const _ => False
  | .binOp _ src1 src2 => src1 ≥ index ∨ src2 ≥ index

abbrev Region := Array Node
abbrev IdEnv := List (String × NodeID)

inductive CompileError where
  | undefinedVariable (name : String)
deriving Repr

inductive EvalError where
  | undefinedVariable (name : String)
deriving Repr

inductive ExecError where
deriving Repr

namespace IdEnv

def update (env : IdEnv) (region : Region) (name : String) : IdEnv :=
  let new_id  := Array.size region
  let new_env := (name, new_id) :: env
  new_env

def get (env : IdEnv) (name : String) : Except CompileError NodeID :=
  match env.lookup name with
  | some id => .ok id
  | none => .error $ .undefinedVariable name

end IdEnv

def compileAux (prog : ProgSrc) (aux : Region) (env : IdEnv) :
  Except CompileError (Region × IdEnv) :=

  match prog with
  | [] => .ok (aux, env)
  | stmt :: rest =>
    match stmt with
    | .set name val =>
      let new_env := env.update aux name
      let new_aux := Array.push aux (.const val)
      compileAux rest new_aux new_env

    | .binOp name op src1 src2 => do
      let src1_id ← env.get src1
      let src2_id ← env.get src2

      let new_env := env.update aux name
      let new_aux := aux.push (.binOp op src1_id src2_id)
      compileAux rest new_aux new_env

def compile (prog : ProgSrc) : Except CompileError (Region × IdEnv):=
  compileAux prog ∅ []

abbrev IntEnv := List (String × Int)

namespace IntEnv

def update (env : IntEnv) (name : String) (val : Int) : IntEnv :=
  (name, val) :: env

def get (env : IntEnv) (name : String) : Except EvalError Int :=
  match env.lookup name with
  | .some val => .ok val
  | .none => .error $ .undefinedVariable name

end IntEnv

def evalBinOp (binOp : BinOp) (num1 num2 : Int) : Int :=
  match binOp with
    | .add => num1 + num2
    | .sub => num1 - num2
    | .mul => num1 * num2

def evalAux (prog : ProgSrc) (env : IntEnv) : Except EvalError IntEnv :=
  match prog with
  | [] => .ok env
  | stmt :: rest =>
    match stmt with
      | .set name val =>
        evalAux rest (env.update name val)

      | .binOp name op name1 name2 => do
        let val1 ← env.get name1
        let val2 ← env.get name2

        evalAux rest (env.update name (evalBinOp op val1 val2))


def eval (prog : ProgSrc) : Except EvalError Int := do
  let env ← evalAux prog []
  match env with
  | [] => .ok 0
  | (_name, val) :: _ => .ok val


def example_prog : ProgSrc :=
  [
    .set "a" 5,
    .binOp "res" .add "a" "a"
  ]

#eval compile example_prog

theorem compileAux_len_sum (prog : ProgSrc) (aux : Region) (env : IdEnv)
  (h : compileAux prog aux env = .ok (res, new_env)) :
  res.size = aux.size + prog.length := by
  induction prog generalizing aux env with
  | nil =>
    simp [compileAux] at h
    simp_all
  | cons first rest ih =>
    simp_all [compileAux]
    cases first
    · grind
    · simp_all
      simp [Bind.bind, Except.bind] at h
      split at h
      · simp_all
      · grind

theorem compile_len_sum (prog : ProgSrc) (h : compile prog = .ok (reg, env)) :
  prog.length = reg.size := by
    simp [compile] at h
    have h_aux := compileAux_len_sum prog ∅ [] h
    simp_all
    rfl

-- 1. ОБЪЯВЛЯЕМ КАТЕГОРИЮ И СИНТАКСИС (каждый значок в своих кавычках!):
declare_syntax_cat sil_stmt

syntax "let" ident "=" num ";"               : sil_stmt
syntax "let" ident "=" ident "+" ident ";"   : sil_stmt
syntax "let" ident "=" ident "-" ident ";"   : sil_stmt
syntax "let" ident "=" ident "*" ident ";"   : sil_stmt

-- Блок silenti { ... } из одной или нескольких строчек:
syntax "silenti" "{" sil_stmt* "}" : term

-- -- 2. ВСЯ МОЩЬ МАКРОСОВ LEAN 4 (Никаких функций, чистое переписывание!):
-- macro_rules
--   -- Пустой блок silenti { } превращается в пустой список []:
--   | `(silenti { }) => `([])

--   -- Первая строчка `const x = 5;` превращается в `Stmt.set "x" 5 :: остаток`:
--   | `(silenti { let $x:ident = $n:num ; $rest:sil_stmt* }) =>
--     `(Stmt.set $(Lean.quote x.getId.toString) $n :: silenti { $rest* })

--   -- Строчка `const c = a + b;` превращается в `Stmt.binOp "c" .add "a" "b" :: остаток`:
--   | `(silenti { let $x:ident = $a:ident + $b:ident ; $rest:sil_stmt* }) =>
--     `(Stmt.binOp $(Lean.quote x.getId.toString) BinOp.add $(Lean.quote a.getId.toString) $(Lean.quote b.getId.toString) :: silenti { $rest* })

--   -- То же для вычитания и умножения:
--   | `(silenti { let $x:ident = $a:ident - $b:ident ; $rest:sil_stmt* }) =>
--     `(Stmt.binOp $(Lean.quote x.getId.toString) BinOp.sub $(Lean.quote a.getId.toString) $(Lean.quote b.getId.toString) :: silenti { $rest* })

--   | `(silenti { let $x:ident = $a:ident * $b:ident ; $rest:sil_stmt* }) =>
--     `(Stmt.binOp $(Lean.quote x.getId.toString) BinOp.mul $(Lean.quote a.getId.toString) $(Lean.quote b.getId.toString) :: silenti { $rest* })

-- 3. ПРОВЕРЯЕМ ПРЯМО СЕЙЧАС!
def my_prog : List Stmt := silenti {
  let a = 5;
  let b = 10;
  let c = a + b;
  let d = c * a;
}

#eval eval my_prog


