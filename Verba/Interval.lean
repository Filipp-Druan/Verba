namespace Interval

structure Interval where
  min : Int
  max : Int
deriving Repr, Inhabited

def containes (inter : Interval) (num : Int) : Prop :=
  (inter.min ≤ num) ∧ (num ≤ inter.max)

def add (in_1 in_2 : Interval) : Interval :=
  ⟨in_1.min + in_2.min, in_1.max + in_2.max⟩

def union (in_1 in_2 : Interval) : Interval :=
  let new_min := min in_1.min in_2.min
  let new_max := max in_1.max in_2.max
  ⟨new_min, new_max⟩

theorem in_add (in_1 in_2 : Interval) (n1 n2 : Int):
 (containes in_1 n1) ∧ (containes in_2 n2) → containes (add in_1 in_2) (n1 + n2) := by
 simp_all [containes, add]
 omega

theorem in_union (in_1 in_2 : Interval) (num : Int):
  (containes in_1 num) ∨ (containes in_2 num) → containes (union in_1 in_2) num := by
  simp_all [containes, union]
  omega


end Interval
