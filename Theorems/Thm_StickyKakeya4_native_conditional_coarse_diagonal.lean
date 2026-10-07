import Theorems.Thm_StickyKakeya4_native_conditional_coarse_interpolation
import Theorems.Thm_StickyKakeya4_native_endpoint_parent_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

noncomputable section
namespace NativeConditionalCoarseDiagonal
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeDyadicParentCells NativeJointUniformCoarseRelations
open NativeIncidenceMultiplicityTower NativeEndpointParentBounds NativeConditionalCoarseInterpolation

/-- Without any fiber uniformity, an occupied conditional global shadow has
multiplicity between one and the exact six-dimensional descendant count. -/
theorem actual_conditional_bounds {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m f : ℕ) (hmf : m ≤ f)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    1 ≤ multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) ∧
    multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) ≤
      (((2^(f-m):ℕ):ℝ)^6) := by
  refine ⟨one_le_multiplicity _ (hp.image _),?_⟩
  have hcard := active_descendants_card_le D a E hmf p
  have he : ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)).image Prod.fst =
      (parentEdges D a (2^m) E p).image (fun z => parentLabel D a (2^f) z.1) := by
    simp only [image_image,Function.comp_def,physicalPair_parent]
  have hu := multiplicity_le_tube_card
    ((parentEdges D a (2^m) E p).image (physicalPair h R a level f))
  rw [he] at hu
  exact hu.trans (by exact_mod_cast hcard)

/-- The short-gap regime already has the desired two-sided power form. The
loss is controlled by the actual depth gap, not by a supplied matched profile. -/
lemma short_gap_power {delta s kappa r mu : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hs : 0 ≤ s) (hk : 0 ≤ kappa) (hk6 : kappa ≤ 6)
    (hr : 1 ≤ r) (hgap : r ≤ delta^(-s)) (hmu : 1 ≤ mu) (hu : mu ≤ r^6) :
    delta^(6*s)*r^kappa ≤ mu ∧ mu ≤ delta^(-6*s)*r^kappa := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hkr : r^kappa ≤ (delta^(-s))^kappa := Real.rpow_le_rpow hr0.le hgap hk
  rw [←Real.rpow_mul hd.le] at hkr
  have hlo : delta^(6*s)*r^kappa ≤ 1 := by
    calc
      _ ≤ delta^(6*s)*delta^(-s*kappa) := mul_le_mul_of_nonneg_left hkr (by positivity)
      _ = delta^(s*(6-kappa)) := by rw [←Real.rpow_add hd]; congr 1; ring
      _ ≤ 1 := Real.rpow_le_one hd.le hd1 (mul_nonneg hs (sub_nonneg.mpr hk6))
  have hpow6 : r^6 ≤ delta^(-6*s) := by
    have hh := pow_le_pow_left₀ hr0.le hgap 6
    rw [←Real.rpow_natCast (delta^(-s)) 6,←Real.rpow_mul hd.le] at hh
    simpa only [Nat.cast_ofNat,show -s*(6:ℝ)= -6*s by ring] using hh
  have hkr1 : 1 ≤ r^kappa := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow zero_le_one hr hk
  refine ⟨hlo.trans hmu,hu.trans (hpow6.trans ?_)⟩
  exact le_mul_of_one_le_right (by positivity) hkr1

/-- A genuine original conditional shadow satisfies the short-gap power
bounds at every off-menu pair of depths with the stated small relative gap. -/
theorem actual_short_gap_power {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m f : ℕ) (hmf : m ≤ f)
    (hdy : D.thickness=(2:ℝ)⁻¹^level) (s kappa : ℝ) (hs : 0 ≤ s)
    (hk : 0 ≤ kappa) (hk6 : kappa ≤ 6)
    (hgap : ((f-m:ℕ):ℝ) ≤ s*level)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty) :
    D.thickness^(6*s)*(((2^(f-m):ℕ):ℝ)^kappa) ≤
      multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) ∧
    multiplicity ((parentEdges D a (2^m) E p).image (physicalPair h R a level f)) ≤
      D.thickness^(-6*s)*(((2^(f-m):ℕ):ℝ)^kappa) := by
  obtain ⟨hlo,hup⟩ := actual_conditional_bounds h R E a level m f hmf p hp
  apply short_gap_power h.1.2.1 h.1.2.2.1 hs hk hk6 _
    (NativeLocalMenuInterpolation.dyadic_gap_power hdy hgap) hlo hup
  exact_mod_cast Nat.one_le_pow (f-m) 2 (by norm_num)

end NativeConditionalCoarseDiagonal
