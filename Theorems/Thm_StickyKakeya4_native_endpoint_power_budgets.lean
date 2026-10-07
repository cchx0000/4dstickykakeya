import Theorems.Thm_StickyKakeya4_native_endpoint_parent_bounds
import Theorems.Thm_StickyKakeya4_native_middle_window_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

noncomputable section
namespace NativeEndpointPowerBudgets
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeLocalMenuInterpolation NativeEndpointParentBounds
open NativeFixedCompactKakeyaExponent

lemma cube_cost {delta r C b gap : ℝ} (hd : 0 < delta) (hr : 0 ≤ r)
    (hratio : r ≤ delta^(-gap)) (hC : C ≤ delta^(-b)) :
    C*r^3 ≤ delta^(-(b+3*gap)) := by
  have hp := pow_le_pow_left₀ hr hratio 3
  calc
    _ ≤ delta^(-b)*(delta^(-gap))^3 :=
      mul_le_mul hC hp (pow_nonneg hr 3) (Real.rpow_pos_of_pos hd _).le
    _ = _ := by rw [←Real.rpow_mul_natCast hd.le,←Real.rpow_add hd]; congr 1; ring

lemma lower_le_one_of_cost {delta X loss target : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hX : X ≤ delta^(-loss)) (hmargin : loss ≤ target) : delta^target*X ≤ 1 := by
  calc
    _ ≤ delta^target*delta^(-loss) := mul_le_mul_of_nonneg_left hX (Real.rpow_pos_of_pos hd _).le
    _ = delta^(target-loss) := by
      simpa only [sub_eq_add_neg] using (Real.rpow_add hd target (-loss)).symm
    _ ≤ 1 := Real.rpow_le_one hd.le hd1 (sub_nonneg.mpr hmargin)

/-- The coarse scale 64/2^m costs at most three powers of its depth. -/
lemma coarse_negative_power_le_depth {s : ℝ} (hs : 0 ≤ s) (hs3 : s ≤ 3) (m : ℕ) :
    (64/((2^m:ℕ):ℝ))^(-s) ≤ ((2^m:ℕ):ℝ)^3 := by
  let r : ℝ := ((2^m:ℕ):ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : 1 ≤ r := by
    simpa only [r,Nat.cast_pow,Nat.cast_ofNat] using (one_le_pow₀ (by norm_num : (1:ℝ)≤2) : (1:ℝ)≤(2:ℝ)^m)
  have h64 : (64:ℝ)^(-s) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤64) (neg_nonpos.mpr hs)
  have hr3 : r^s ≤ r^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hr1 hs3
  change (64/r)^(-s) ≤ r^3
  calc
    _ = (64:ℝ)^(-s)*r^s := by
      rw [Real.div_rpow (by norm_num : (0:ℝ)≤64) hr.le,Real.rpow_neg hr.le,div_inv_eq_mul]
    _ ≤ 1*r^3 := mul_le_mul h64 hr3 (Real.rpow_pos_of_pos hr _).le (by norm_num)
    _ = _ := one_mul _

/-- A nonempty full shadow supplies the coarse-end lower bound directly. -/
theorem initial_coarse_lower {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hR : ∀z∈E,z.1∈R) (hne : E.Nonempty)
    (a : ℝ) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (gap target : ℝ) (hgap : (m:ℝ) ≤ gap*level) (hmargin : 3*gap ≤ target) :
    D.thickness^target*(64/((2^m:ℕ):ℝ))^(-extremalExponent) ≤
      (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E)).toReal := by
  have hd := h.1.2.1
  have hr := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgap
  have hc : ((2^m:ℕ):ℝ)^3 ≤ D.thickness^(-(3*gap)) := by
    have hh := cube_cost (C:=1) (b:=0) hd (by positivity) hr (by simp)
    simpa only [one_mul,zero_add] using hh
  have hpower := (coarse_negative_power_le_depth extremalExponent_nonneg extremalExponent_le_three m).trans hc
  exact (lower_le_one_of_cost hd h.1.2.2.1 hpower hmargin).trans
    (one_le_full_multiplicity h R E hR hne a level m)

/-- At the fine endpoint, elementary nonempty incidence and original
direction packing give both old-parent bounds on the exact E. -/
theorem terminal_old_parent_bounds {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (hR : ∀z∈E,z.1∈R) (a : ℝ)
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m ≤ level)
    (gap b target : ℝ) (hgap : ((level-m:ℕ):ℝ) ≤ gap*level)
    (hconstant : (64:ℝ)^3 ≤ D.thickness^(-b)) (hmargin : b+3*gap ≤ target)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    D.thickness^target*(localScale D.thickness m)^(-extremalExponent) ≤
        edgeMultiplicity (parentEdges D a (2^m) E p) ∧
      edgeMultiplicity (parentEdges D a (2^m) E p) ≤
        D.thickness^(-target)*(localScale D.thickness m)^(-extremalExponent) := by
  have hd := h.1.2.1
  have he := localScale_pos hd m
  have hr := NativeLocalMenuInterpolation.dyadic_gap_power hdy hgap
  have hcost := cube_cost hd (by positivity : (0:ℝ)≤((2^(level-m):ℕ):ℝ)) hr hconstant
  have hnegative : (localScale D.thickness m)^(-extremalExponent) ≤ D.thickness^(-(b+3*gap)) :=
    (local_negative_power_le_remaining hd level m hdy hm extremalExponent_le_three).trans hcost
  have hold : edgeMultiplicity (parentEdges D a (2^m) E p) ≤ D.thickness^(-(b+3*gap)) := by
    have hgeom := old_parent_dyadic_upper h R E hR a level m hdy hm p
    have hc : (5832:ℝ)*((2^(level-m):ℕ):ℝ)^3 ≤ (64:ℝ)^3*((2^(level-m):ℕ):ℝ)^3 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact hgeom.trans (hc.trans hcost)
  have hone : 1 ≤ (localScale D.thickness m)^(-extremalExponent) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos he (localScale_le_one level m hdy hm)
      (neg_nonpos.mpr extremalExponent_nonneg)
  refine ⟨(lower_le_one_of_cost hd h.1.2.2.1 hnegative hmargin).trans
    (one_le_multiplicity _ hp),?_⟩
  calc
    _ ≤ D.thickness^(-(b+3*gap)) := hold
    _ ≤ D.thickness^(-target) := Real.rpow_le_rpow_of_exponent_ge hd h.1.2.2.1 (by linarith)
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (Real.rpow_pos_of_pos hd (-target)).le

end NativeEndpointPowerBudgets
