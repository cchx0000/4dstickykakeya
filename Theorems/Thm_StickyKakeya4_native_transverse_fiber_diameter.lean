import Mathlib

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeTransverseFiberDiameter
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A transverse direction controls the coefficient of any approximate
intersection with a fixed linear subspace. -/
lemma transverse_scalar_bound (P : Submodule ℝ V) (v : V) (q : ℝ)
    (htrans : q ≤ Metric.infDist v (P:Set V)) (t : ℝ) (u : V) (hu : u∈P)
    (E : ℝ) (herr : ‖t•v-u‖ ≤ E) : |t| * q ≤ E := by
  by_cases ht : t=0
  · subst t
    simpa only [abs_zero,zero_mul] using (norm_nonneg _).trans herr
  have hinv : t⁻¹•u∈P := P.smul_mem _ hu
  have hh := htrans.trans (Metric.infDist_le_dist_of_mem hinv)
  rw [dist_eq_norm] at hh
  have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg t)
  have he : t•(v-t⁻¹•u)=t•v-u := by rw [smul_sub,smul_smul,mul_inv_cancel₀ ht,one_smul]
  have hn : |t| * ‖v-t⁻¹•u‖=‖t•v-u‖ := by
    rw [←he,norm_smul,Real.norm_eq_abs]
  exact hm.trans (hn.le.trans herr)

/-- Actual approximate fibers have a bounded intersection diameter. This
replaces the invalid inference that their ordinary grid centers are exactly
collinear. No exact-affine-fiber hypothesis is used. -/
theorem approximate_fiber_diameter (P : Submodule ℝ V) (v : V)
    (q h B : ℝ) (hq : 0 < q) (hh : 0 < h) (_hB : 0 ≤ B)
    (htrans : q ≤ Metric.infDist v (P:Set V)) (hv : ‖v‖ ≤ B)
    (x z y1 y2 : V)
    (hP1 : Metric.infDist (y1-z) (P:Set V) ≤ h)
    (hP2 : Metric.infDist (y2-z) (P:Set V) ≤ h)
    (hQ1 : Metric.infDist (y1-x) (Submodule.span ℝ {v}:Set V) ≤ h)
    (hQ2 : Metric.infDist (y2-x) (Submodule.span ℝ {v}:Set V) ≤ h) :
    dist y1 y2 ≤ 4*h+(8*h/q)*B := by
  have hnP : (P:Set V).Nonempty := ⟨0,P.zero_mem⟩
  have hnQ : (Submodule.span ℝ {v}:Set V).Nonempty := ⟨0,Submodule.zero_mem _⟩
  obtain ⟨u1,hu1,he1⟩ := (Metric.infDist_lt_iff hnP).mp (hP1.trans_lt (by linarith : h<2*h))
  obtain ⟨u2,hu2,he2⟩ := (Metric.infDist_lt_iff hnP).mp (hP2.trans_lt (by linarith : h<2*h))
  obtain ⟨w1,hw1,hf1⟩ := (Metric.infDist_lt_iff hnQ).mp (hQ1.trans_lt (by linarith : h<2*h))
  obtain ⟨w2,hw2,hf2⟩ := (Metric.infDist_lt_iff hnQ).mp (hQ2.trans_lt (by linarith : h<2*h))
  obtain ⟨t1,ht1⟩ := Submodule.mem_span_singleton.mp hw1
  obtain ⟨t2,ht2⟩ := Submodule.mem_span_singleton.mp hw2
  rw [←ht1,dist_eq_norm] at hf1
  rw [←ht2,dist_eq_norm] at hf2
  rw [dist_eq_norm] at he1 he2
  let d := y1-y2
  let u := u1-u2
  let t := t1-t2
  have hu : u∈P := P.sub_mem hu1 hu2
  have hdu : ‖d-u‖ ≤ 4*h := by
    have he : d-u=((y1-z)-u1)-((y2-z)-u2) := by dsimp [d,u]; abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith only [he1,he2])
  have hdt : ‖d-t•v‖ ≤ 4*h := by
    have he : d-t•v=((y1-x)-t1•v)-((y2-x)-t2•v) := by
      dsimp [d,t]
      rw [sub_smul]
      abel
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith only [hf1,hf2])
  have htu : ‖t•v-u‖ ≤ 8*h := by
    have he : t•v-u=-(d-t•v)+(d-u) := by abel
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_neg]
    linarith only [hdt,hdu]
  have htq := transverse_scalar_bound P v q htrans t u hu (8*h) htu
  have ht : |t| ≤ 8*h/q := (le_div_iff₀ hq).mpr htq
  have htv : ‖t•v‖ ≤ (8*h/q)*B := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul ht hv (norm_nonneg _) (by positivity)
  rw [dist_eq_norm]
  change ‖d‖ ≤ _
  have he : d=(d-t•v)+t•v := by abel
  calc
    ‖d‖ = ‖(d-t•v)+t•v‖ := congrArg norm he
    _ ≤ ‖d-t•v‖+‖t•v‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hdt htv

end NativeTransverseFiberDiameter
