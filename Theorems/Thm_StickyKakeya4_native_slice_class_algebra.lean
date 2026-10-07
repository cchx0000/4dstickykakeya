import Theorems.Thm_StickyKakeya4_native_slice_population_algebra

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeSliceClassAlgebra
open Classical Finset NativeFiniteSliceHomogeneity NativeSlicePopulationAlgebra

lemma scaled_power_quotient {fine coarse ratio kappa : ℝ}
    (hf : 0 < fine) (hr : 0 < ratio) (hscale : coarse=ratio*fine) :
    fine^(kappa-3)/coarse^(kappa-3)=ratio^(3-kappa) := by
  rw [hscale,Real.mul_rpow hr.le hf.le]
  have hp : fine^(kappa-3)≠0 := (Real.rpow_pos_of_pos hf _).ne'
  have hq : ratio^(kappa-3)≠0 := (Real.rpow_pos_of_pos hr _).ne'
  calc
    _ = (ratio^(kappa-3))⁻¹ := by field_simp
    _ = ratio^(-(kappa-3)) := (Real.rpow_neg hr.le _).symm
    _ = _ := by congr 1; ring

/-- The global count ratio has no class-uniformity loss. This is the
cross-multiplied input for the later retained-incidence refinement. -/
theorem global_count_ratio_bounds {H Nfine Ncoarse fine coarse ratio kappa lower upper : ℝ}
    (hH : 0 < H) (hf : 0 < fine) (hr : 0 < ratio) (hscale : coarse=ratio*fine)
    (hL : 0 < lower) (hU : 0 < upper)
    (Hfine : lower*fine^(kappa-3) ≤ H*Nfine ∧ H*Nfine ≤ upper*fine^(kappa-3))
    (Hcoarse : lower*coarse^(kappa-3) ≤ H*Ncoarse ∧ H*Ncoarse ≤ upper*coarse^(kappa-3)) :
    (lower/upper)*ratio^(3-kappa)*Ncoarse ≤ Nfine ∧
      Nfine ≤ (upper/lower)*ratio^(3-kappa)*Ncoarse := by
  have hc : 0 < coarse := by rw [hscale]; positivity
  have hB : 0 < coarse^(kappa-3) := Real.rpow_pos_of_pos hc _
  let c := (lower/upper)*(fine^(kappa-3)/coarse^(kappa-3))
  let d := (upper/lower)*(fine^(kappa-3)/coarse^(kappa-3))
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hcancelC : c*(upper*coarse^(kappa-3))=lower*fine^(kappa-3) := by
    dsimp [c]
    field_simp
  have hcancelD : d*(lower*coarse^(kappa-3))=upper*fine^(kappa-3) := by
    dsimp [d]
    field_simp
  have hl : c*Ncoarse ≤ Nfine := (mul_le_mul_iff_right₀ hH).mp (calc
    H*(c*Ncoarse)=c*(H*Ncoarse) := by ring
    _ ≤ c*(upper*coarse^(kappa-3)) := mul_le_mul_of_nonneg_left Hcoarse.2 hc0
    _ = lower*fine^(kappa-3) := hcancelC
    _ ≤ H*Nfine := Hfine.1)
  have hu : Nfine ≤ d*Ncoarse := (mul_le_mul_iff_right₀ hH).mp (calc
    H*Nfine ≤ upper*fine^(kappa-3) := Hfine.2
    _ = d*(lower*coarse^(kappa-3)) := hcancelD.symm
    _ ≤ d*(H*Ncoarse) := mul_le_mul_of_nonneg_left Hcoarse.1 hd0
    _ = H*(d*Ncoarse) := by ring)
  dsimp [c,d] at hl hu
  rw [scaled_power_quotient hf hr hscale] at hl hu
  exact ⟨hl,hu⟩

/-- Uniform occupied classes turn source-derived global powers into local
class powers. The common height scale cancels exactly; no inner-parent
density or local AD certificate is used. -/
theorem class_bounds_from_global_counts {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (P : Finset X) (classes : X → Y) (C : ℕ) (hC : 0 < C)
    (Hclasses : ∀x∈P,∀y∈P,(P.filter (fun z => classes z=classes x)).card ≤
      C*(P.filter (fun z => classes z=classes y)).card)
    (H fine coarse ratio kappa lower upper : ℝ)
    (hH : 0 < H) (hf : 0 < fine) (hr : 0 < ratio) (hscale : coarse=ratio*fine)
    (hL : 0 < lower) (hU : 0 < upper)
    (Hfine : lower*fine^(kappa-3) ≤ H*P.card ∧ H*P.card ≤ upper*fine^(kappa-3))
    (Hcoarse : lower*coarse^(kappa-3) ≤ H*(P.image classes).card ∧
      H*(P.image classes).card ≤ upper*coarse^(kappa-3))
    (x : X) (hx : x∈P) :
    (lower/((C:ℝ)*upper))*ratio^(3-kappa) ≤ (P.filter (fun z => classes z=classes x)).card ∧
      ((P.filter (fun z => classes z=classes x)).card:ℝ) ≤
        (((C:ℝ)*upper)/lower)*ratio^(3-kappa) := by
  have hc : 0 < coarse := by rw [hscale]; positivity
  have hCr : (0:ℝ)<C := by exact_mod_cast hC
  have ha := fiber_card_average_cross P classes C Hclasses (classes x) (mem_image_of_mem _ hx)
  have hAu : ((P.filter (fun z => classes z=classes x)).card:ℝ)*(P.image classes).card ≤ (C:ℝ)*P.card := by
    exact_mod_cast ha.1
  have hAl : (P.card:ℝ) ≤ (C:ℝ)*(P.filter (fun z => classes z=classes x)).card*(P.image classes).card := by
    exact_mod_cast ha.2
  have hh := slice_ratio_bounds (I:=(P.card:ℝ)) (N:=(P.card:ℝ)) (Z:=((P.image classes).card:ℝ))
    (S:=((P.filter (fun z => classes z=classes x)).card:ℝ)) (H:=H) (C:=(C:ℝ))
    (A:=fine^(kappa-3)) (B:=1) (Al:=lower) (Au:=upper)
    (Zl:=lower*coarse^(kappa-3)) (Zu:=upper*coarse^(kappa-3)) (Ml:=1) (Mu:=1) (M:=1)
    hH hCr (Real.rpow_pos_of_pos hf _) (by norm_num) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) (by positivity) (by norm_num) (by norm_num) (by simp) hAu hAl
    Hfine.1 Hfine.2 Hcoarse.1 Hcoarse.2 (by norm_num) (by norm_num)
  have heL : (lower/((C:ℝ)*(upper*coarse^(kappa-3))*1))*(fine^(kappa-3)/1)=
      (lower/((C:ℝ)*upper))*(fine^(kappa-3)/coarse^(kappa-3)) := by ring
  have heU : (((C:ℝ)*upper)/((lower*coarse^(kappa-3))*1))*(fine^(kappa-3)/1)=
      (((C:ℝ)*upper)/lower)*(fine^(kappa-3)/coarse^(kappa-3)) := by ring
  rw [heL,heU,scaled_power_quotient hf hr hscale] at hh
  exact hh

end NativeSliceClassAlgebra
