import Mathlib

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalThreeDimensionalBandGeometry

abbrev Point3 := Fin 3 → ℝ

def projection (e : Equiv.Perm (Fin 3)) (u v : ℝ) (p : Point3) : ℝ :=
  u*p (e 0)+v*p (e 1)+p (e 2)

def root (A B C v : ℝ) : ℝ := -(v*B+C)/A

def roundedRoot (rho A B C v : ℝ) : ℤ := ⌊root A B C v/rho⌋

lemma root_abs_le_two (A B C v : ℝ) (hA : A≠0)
    (hB : |B|≤|A|) (hC : |C|≤|A|) (hv : |v|≤1) :
    |root A B C v|≤2 := by
  have hAp : 0< |A| := abs_pos.mpr hA
  have hmul := mul_le_mul hv hB (abs_nonneg B) (by norm_num : (0:ℝ)≤1)
  have htri := abs_add_le (v*B) C
  rw [abs_mul] at htri
  unfold root
  rw [abs_div,abs_neg]
  apply (div_le_iff₀ hAp).mpr
  nlinarith only [hmul,htri,hC]

lemma rounded_root_error (rho A B C v : ℝ) (hrho : 0<rho) :
    |rho*(roundedRoot rho A B C v:ℝ)-root A B C v|≤rho := by
  have hl := Int.floor_le (root A B C v/rho)
  have hu := Int.lt_floor_add_one (root A B C v/rho)
  have hl' := (le_div_iff₀ hrho).mp hl
  have hu' := (div_lt_iff₀ hrho).mp hu
  unfold roundedRoot
  exact abs_le.mpr ⟨by nlinarith only [hl',hu'],by nlinarith only [hl',hrho]⟩

/-- For every free grid coordinate there is an actual rounded normal
with controlled size, almost annihilating the fixed original displacement. -/
theorem rounded_normal_band (rho A B C v : ℝ)
    (hrho : 0<rho) (hrho1 : rho≤1) (hA : A≠0)
    (hB : |B|≤|A|) (hC : |C|≤|A|) (hv : |v|≤1) (hA2 : |A|≤2) :
    |rho*(roundedRoot rho A B C v:ℝ)|≤3 ∧
      |rho*(roundedRoot rho A B C v:ℝ)*A+v*B+C|≤2*rho := by
  have he := rounded_root_error rho A B C v hrho
  have hu := root_abs_le_two A B C v hA hB hC hv
  have htri := abs_add_le (rho*(roundedRoot rho A B C v:ℝ)-root A B C v)
    (root A B C v)
  have hid : rho*(roundedRoot rho A B C v:ℝ)*A+v*B+C=
      (rho*(roundedRoot rho A B C v:ℝ)-root A B C v)*A := by
    dsimp [root]
    field_simp
    ring
  refine ⟨?_,?_⟩
  · have hadd : rho*(roundedRoot rho A B C v:ℝ)-root A B C v+root A B C v=
        rho*(roundedRoot rho A B C v:ℝ) := by ring
    rw [hadd] at htri
    linarith only [htri,he,hu,hrho1]
  · rw [hid,abs_mul]
    have hh := mul_le_mul he hA2 (abs_nonneg A) hrho.le
    nlinarith only [hh]

/-- The rounded witness belongs to one common finite integer grid, rather
than to a displacement-dependent family of normal directions. -/
theorem rounded_normal_in_grid (rho A B C v : ℝ)
    (hrho : 0<rho) (hrho1 : rho≤1) (hA : A≠0)
    (hB : |B|≤|A|) (hC : |C|≤|A|) (hv : |v|≤1) (hA2 : |A|≤2) :
    roundedRoot rho A B C v∈Finset.Icc (-⌈3/rho⌉) ⌈3/rho⌉ := by
  have hbound := (rounded_normal_band rho A B C v hrho hrho1 hA hB hC hv hA2).1
  rw [abs_mul,abs_of_pos hrho] at hbound
  have hh : |(roundedRoot rho A B C v:ℝ)|≤3/rho :=
    (le_div_iff₀ hrho).mpr (by nlinarith only [hbound])
  have hc : |(roundedRoot rho A B C v:ℝ)|≤(⌈3/rho⌉:ℤ) := hh.trans (Int.le_ceil _)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hc
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

end OriginalThreeDimensionalBandGeometry
