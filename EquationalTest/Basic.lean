import Mathlib.Tactic
import Duper

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ⋄ " => Magma.op

abbrev Equation1689 (M : Type _) [Magma M] := ∀ x y z : M, x = (y ⋄ x) ⋄ ((x ⋄ z) ⋄ z)

abbrev Equation2 (M : Type _) [Magma M] := ∀ x y : M, x = y

variable {M : Type _} [Magma M]

abbrev S (z x : M) := (x ⋄ z) ⋄ z

abbrev f (x y : M) := x ⋄ (S y x)

lemma f_eq (x y : M) : f x y = x ⋄ ((x ⋄ y) ⋄ y) := rfl

lemma main_eq (h : Equation1689 M) (x y z : M) : x = (y ⋄ x) ⋄ S z x := by
  duper [*]

lemma claim (h : Equation1689 M) (a b : M) (y : M) (hy : ∃ z, y = z ⋄ a) : y ⋄ S b a = a := by
  duper [*]

lemma Lemma1 (h : Equation1689 M) (a b c : M) : S b a = a ⋄ (S c b) := by
  duper [*]

lemma Lemma2 (h : Equation1689 M) (a : M) : ∃ b c d, f b c = S d a := by
  duper [*]

lemma Lemma3 (h : Equation1689 M) (a : M) : ∃ e, S e a = a := by
  duper [*]

-- use duper? to remove the warning.
theorem singleton_law (h : Equation1689 M) : Equation2 M := by
  duper [*]
