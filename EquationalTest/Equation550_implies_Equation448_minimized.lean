import Mathlib.Tactic
import Duper

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation650 (G: Type _) [Magma G] := ∀ x y z : G, x = x ◇ (y ◇ ((z ◇ x) ◇ y))

abbrev Equation448 (G: Type _) [Magma G] := ∀ x y z : G, x = x ◇ (y ◇ (z ◇ (x ◇ z)))

set_option maxHeartbeats 1000000

theorem Equation650_implies_Equation448 (G: Type _) [Magma G] (h: Equation650 G) : Equation448 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, sK2, nh⟩ := nh
  have h (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := by duper [h]
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) := by duper [h]
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X1))) = X1 := by duper [h]
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X4))) := by duper [h, eq11]
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X5))) := by duper [eq11]
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) = ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by duper [eq11]
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) = ((X2 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by duper [eq11]
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X4)) ◇ (X3 ◇ (X2 ◇ X3)))) := by duper [eq11, eq12]
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ (X2 ◇ X3)) = ((X3 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by duper [eq11, eq12]
  have eq55 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ X4)) = ((X4 ◇ (X2 ◇ X4)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by duper [eq11, eq21]
  have eq271 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = ((X2 ◇ X4) ◇ (((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X4 ◇ (X2 ◇ X4)))) := by duper [eq11, eq36]
  have eq1433 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) = (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X4)))) := by duper [eq23, eq11, eq271]
  have eq1579 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ ((X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)))))) := by duper [eq36, eq37]
  have eq1695 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = ((X3 ◇ (X0 ◇ X3)) ◇ (X4 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0)) ◇ X4))) := by duper [eq11, eq1579]
  have eq1874 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := by duper [eq31, eq1695]
  have eq1878 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X2 ◇ ((X1 ◇ ((X3 ◇ ((X4 ◇ X1) ◇ X3)) ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := by duper [eq1695, h]
  have eq2760 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2))) = X2 := by duper [eq31, eq1695, eq12]
  have eq2902 (X0 X1 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X5 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X5))) := by duper [eq21, eq23, eq55, eq1433]
  have eq3020 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by duper [eq11, eq2902, eq31, eq1878]
  have eq3226 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X3)) = ((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := by duper [eq3020, eq30]
  have eq3250 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) = X3 := by duper [eq3020, eq11, eq2760, eq2902, eq1874]
  have eq3255 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X0))) = X0 := by duper [eq2902, eq1874, eq3226, eq11, h, eq12, eq37, eq12]
  duper [h, nh, eq11, eq21, eq36, eq3255, eq3250]
