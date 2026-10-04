import Theorems.Thm_StickyKakeya4_native_padded_source_transport
import Theorems.Thm_StickyKakeya4_native_normalized_parent_carrier_metric
import Theorems.Thm_StickyKakeya4_native_dense_retained_unit_parent
import Theorems.Thm_StickyKakeya4_native_unit_parent_dyadic
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000
noncomputable section
namespace NativePaddedSourceADLower
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativePaddedCellSource NativeContractedUnitParent NativeDenseRetainedUnitParent
open NativePaddedSourceTransport NativeNormalizedParentCarrierMetric NativeUnitParentDyadic

/-- The actual source on one whole original parent of the already pruned R. -/
def rootSource {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (a : ℝ) (p : Parent) : FiniteScaleSource (parentSubset D R a p).card :=
  source h original (parentSubset D R a p) a p (fun _ hi => (mem_filter.mp hi).2)

lemma dyadic_below_radius {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ell : ℕ,r/32 ≤ 1/((2^ell:ℕ):ℝ) ∧ 1/((2^ell:ℕ):ℝ) ≤ r/16 := by
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < r/16 by positivity) (show r/16 ≤ 1 by linarith)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have he (j : ℕ) : (1/2:ℝ)^j=1/((2^j:ℕ):ℝ) := by simp only [one_div,inv_pow,Nat.cast_pow,Nat.cast_ofNat]
  have hl : r/32 ≤ (1/2:ℝ)^(k+1) := by rw [pow_succ]; linarith only [hhi]
  exact ⟨k+1,by simpa only [he] using hl,by simpa only [he] using hlo.le⟩

/-- The source AD lower bound is obtained from the SAME original retained
ancestor fibers. The finite extra scales below the original delta use the
actual center point. No lower carrier-ball profile is assumed for the new source. -/
theorem source_carrier_lower {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (p : Parent)
    (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (H : ∀ell : Fin (level+1),∀q : Parent,
      (R.filter (fun j => parentLabel D a (2^ell.val) j=q)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun j => parentLabel D a (2^ell.val) j=q)).card:ℝ))
    (i : Fin (parentSubset D R a p).card) {r : ℝ}
    (hr : (rootSource h original R a p).thickness ≤ r) (hr1 : r ≤ 1) :
    D.thickness^zeta/(2048:ℝ)^3*(r/(rootSource h original R a p).thickness)^3 ≤
      (wzCarrierBallCount (rootSource h original R a p) i r:ℝ) := by
  let Q := parentSubset D R a p
  let S := rootSource h original R a p
  have hd:=h.1.2.1
  have hdS : 0 < S.thickness := by change 0 < D.thickness/64; positivity
  have hrp : 0 < r := hdS.trans_le hr
  have hiQ : originalLabel Q i∈Q := originalLabel_mem Q i
  have hip : parentLabel D a 1 (originalLabel Q i)=p := (mem_filter.mp hiQ).2
  change D.thickness^zeta/(2048:ℝ)^3*(r/S.thickness)^3 ≤ (wzCarrierBallCount S i r:ℝ)
  by_cases hlarge : 32*D.thickness ≤ r
  · obtain ⟨ell,helllo,hellhi⟩ := dyadic_below_radius hrp hr1
    have hdell : D.thickness ≤ 1/((2^ell:ℕ):ℝ) := (by linarith : D.thickness ≤ r/32).trans helllo
    have hpows : (1/2:ℝ)^level ≤ (1/2:ℝ)^ell := by
      simpa only [hdy,one_div,Nat.cast_pow,Nat.cast_ofNat,inv_pow] using hdell
    have hell : ell ≤ level := (pow_le_pow_iff_right_of_lt_one₀
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)).mp hpows
    let q := parentLabel D a (2^ell) (originalLabel Q i)
    have hneQ : (Q.filter (fun j => parentLabel D a (2^ell) j=q)).Nonempty :=
      ⟨originalLabel Q i,mem_filter.mpr ⟨hiQ,rfl⟩⟩
    have hfiber := unit_parent_fiber_eq D R a p ell q hneQ
    have hneR : (R.filter (fun j => parentLabel D a (2^ell) j=q)).Nonempty :=
      ⟨originalLabel Q i,mem_filter.mpr ⟨(mem_filter.mp hiQ).1,rfl⟩⟩
    have hAD := H ⟨ell,by omega⟩ q hneR
    have hscale : 16/((2^ell:ℕ):ℝ) ≤ r := by
      calc
        _ = 16*(1/((2^ell:ℕ):ℝ)) := by ring
        _ ≤ 16*(r/16) := mul_le_mul_of_nonneg_left hellhi (by norm_num)
        _ = _ := by ring
    let B := Q.filter (fun j => dist
      (direction (NativeContractedUnitParent.line D a p j),offset (NativeContractedUnitParent.line D a p j))
      (direction (NativeContractedUnitParent.line D a p (originalLabel Q i)),
        offset (NativeContractedUnitParent.line D a p (originalLabel Q i))) ≤ r)
    have hsub : Q.filter (fun j => parentLabel D a (2^ell) j=q) ⊆ B := by
      intro j hj
      have hjp : parentLabel D a 1 j=p := (mem_filter.mp (mem_filter.mp hj).1).2
      refine mem_filter.mpr ⟨(mem_filter.mp hj).1,?_⟩
      exact (same_parent_cell_carrier_dist_le D a p j (originalLabel Q i) (2^ell)
        (by positivity) hjp hip (mem_filter.mp hj).2).trans hscale
    have hcount : wzCarrierBallCount S i r=B.card := source_carrierBallCount h original Q a p
      (fun _ hj => (mem_filter.mp hj).2) i r
    have hc : ((R.filter (fun j => parentLabel D a (2^ell) j=q)).card:ℝ) ≤
        (wzCarrierBallCount S i r:ℝ) := by
      rw [←hfiber,hcount]
      exact_mod_cast card_le_card hsub
    have he : D.thickness^zeta/(2048:ℝ)^3*(r/S.thickness)^3=
        D.thickness^zeta*((r/32)/D.thickness)^3 := by
      change D.thickness^zeta/(2048:ℝ)^3*(r/(D.thickness/64))^3=_
      field_simp [hd.ne']
      ring
    rw [he]
    calc
      _ ≤ D.thickness^zeta*((1/((2^ell:ℕ):ℝ))/D.thickness)^3 := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hd _).le
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_right helllo hd.le
      _ ≤ _ := hAD.trans hc
  · have hratio : r/S.thickness ≤ 2048 := by
      apply (div_le_iff₀ hdS).mpr
      change r ≤ 2048*(D.thickness/64)
      linarith
    have hpow : (r/S.thickness)^3 ≤ (2048:ℝ)^3 :=
      pow_le_pow_left₀ (div_nonneg hrp.le hdS.le) hratio 3
    have hz1 : D.thickness^zeta ≤ 1 := Real.rpow_le_one hd.le h.1.2.2.1 hzeta
    have hmass : D.thickness^zeta*(r/S.thickness)^3 ≤ (2048:ℝ)^3 := by
      exact (mul_le_mul hz1 hpow (by positivity) (by norm_num)).trans_eq (by ring)
    have hball : ((univ : Finset (Fin Q.card)).filter
        (fun j => dist (wzCarrierPoint S j) (wzCarrierPoint S i) ≤ r)).Nonempty :=
      ⟨i,mem_filter.mpr ⟨mem_univ _,by simpa only [dist_self] using hrp.le⟩⟩
    have hcard : 1 ≤ wzCarrierBallCount S i r := card_pos.mpr hball
    calc
      _ = (D.thickness^zeta*(r/S.thickness)^3)/(2048:ℝ)^3 := by ring
      _ ≤ (2048:ℝ)^3/(2048:ℝ)^3 := div_le_div_of_nonneg_right hmass (by positivity)
      _ = 1 := div_self (by norm_num)
      _ ≤ _ := by exact_mod_cast hcard
end NativePaddedSourceADLower
