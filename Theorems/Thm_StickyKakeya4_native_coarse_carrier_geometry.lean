import Theorems.Thm_StickyKakeya4_native_coarse_representative_geometry
import Theorems.Thm_StickyKakeya4_native_coarse_cell_source
import Theorems.Thm_StickyKakeya4_native_padded_source_ad_lower
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3400000
noncomputable section
namespace NativeCoarseCarrierGeometry
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeUnitParentNormalization NativeContractedUnitParent NativeCoarseRepresentativeGeometry
open NativeNormalizedParentCarrierMetric NativeDyadicParentCells

def carrier {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (i : Fin n) : E4×E4 :=
  (direction (NativeContractedUnitParent.line D a (0,0) i),
    offset (NativeContractedUnitParent.line D a (0,0) i))

/-- The full bounded K0 chart supplies the same forward carrier bound without
requiring the two labels to belong to one unit parameter cell. -/
theorem parameter_error_carrier_dist {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (i j : Fin n) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀k,|slope (D.line i) k-slope (D.line j) k| ≤ r)
    (hb : ∀k,|shiftedIntercept (D.line i) (mesh D) (shift D a) k-
      shiftedIntercept (D.line j) (mesh D) (shift D a) k| ≤ r) :
    dist (carrier D a i) (carrier D a j) ≤ 16*r := by
  have hsu : ‖newSlope (D.line i) (0,0)-newSlope (D.line j) (0,0)‖ ≤ 2*r := by
    apply euclidean_three_norm_le_two _ r hr
    intro k
    simpa only [newSlope,PiLp.sub_apply,sub_sub_sub_cancel_right] using hs k
  have hbi : ‖newIntercept (D.line i) (mesh D) (shift D a) (0,0)-
      newIntercept (D.line j) (mesh D) (shift D a) (0,0)‖ ≤ r/2 := by
    have hh := euclidean_three_norm_le_two
      (newIntercept (D.line i) (mesh D) (shift D a) (0,0)-
        newIntercept (D.line j) (mesh D) (shift D a) (0,0)) (r/4) (by positivity) (by
      intro k
      simp only [newIntercept,PiLp.sub_apply,Pi.zero_apply,Int.cast_zero,sub_zero]
      rw [←sub_div,abs_div]
      norm_num
      linarith only [hb k])
    linarith only [hh]
  have hv : ‖newIntercept (D.line j) (mesh D) (shift D a) (0,0)‖ ≤ 1 := by
    have hh := euclidean_three_norm_le_two _ (1/2) (by norm_num) (zero_intercept_bound h hK ha j)
    linarith
  exact (contractLine_carrier_dist_le _ _).trans
    (graph_carrier_dist_le_sixteen _ _ _ _ r hr hsu hbi hv)

lemma same_parameter_cell_carrier_dist {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (i j : Fin n) (N : ℕ) (hN : 0 < N) (hcell : parentLabel D a N i=parentLabel D a N j) :
    dist (carrier D a i) (carrier D a j) ≤ 16/(N:ℝ) := by
  have hh := parameter_error_carrier_dist h hK ha i j (r:=1/(N:ℝ)) (by positivity)
    (fun k => same_floor_mul_close _ _ N hN (congrFun (congrArg Prod.fst hcell) k))
    (fun k => same_floor_mul_close _ _ N hN (congrFun (congrArg Prod.snd hcell) k))
  simpa only [mul_one_div] using hh

/-- The actual pruned ancestor lower populations put genuine representative
carriers inside every output ball. The output minimum radius already exceeds
six original coarse grid levels, so no ball-to-boundary-cell inference occurs. -/
theorem pruned_carrier_lower {n : ℕ} {D : FiniteScaleSource n} {eta a t : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hK : ∀i,D.line i∈fixedCompactClass)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (m : ℕ) (Q : Finset Parent) (rep : Parent → Fin n)
    (hrep : ∀p∈Q,parentLabel D a (2^m) (rep p)=p)
    (H : ∀ell : Fin (m+1),∀p : Parent,
      (Q.filter (fun q => ancestor m ell.val q=p)).Nonempty →
        D.thickness^t*(((2^m:ℕ):ℝ)/((2^ell.val:ℕ):ℝ))^3 ≤
          ((Q.filter (fun q => ancestor m ell.val q=p)).card:ℝ))
    (p : Parent) (hp : p∈Q) {r : ℝ} (hr : 64/((2^m:ℕ):ℝ) ≤ r) (hr1 : r ≤ 1) :
    D.thickness^t*(r/(64/((2^m:ℕ):ℝ)))^3 ≤
      ((Q.filter (fun q => dist (carrier D a (rep q)) (carrier D a (rep p)) ≤ r)).card:ℝ) := by
  have hd := h.1.2.1
  have hrp : 0 < r := (by positivity : 0 < 64/((2^m:ℕ):ℝ)).trans_le hr
  obtain ⟨k,hklo,hkhi⟩ := NativePaddedSourceADLower.dyadic_below_radius hrp hr1
  have hmk : 1/((2^m:ℕ):ℝ) ≤ 1/((2^k:ℕ):ℝ) := by
    have hh : 1/((2^m:ℕ):ℝ) ≤ r/32 := by
      calc
        _ = (64/((2^m:ℕ):ℝ))/64 := by ring
        _ ≤ r/64 := div_le_div_of_nonneg_right hr (by norm_num)
        _ ≤ r/32 := by linarith
    exact hh.trans hklo
  have hk : k ≤ m := by
    have hh : (1/2:ℝ)^m ≤ (1/2:ℝ)^k := by
      simpa only [one_div,inv_pow,Nat.cast_pow,Nat.cast_ofNat] using hmk
    exact (pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).mp hh
  let q0 := ancestor m k p
  have hne : (Q.filter (fun q => ancestor m k q=q0)).Nonempty := ⟨p,mem_filter.mpr ⟨hp,rfl⟩⟩
  have hsub : Q.filter (fun q => ancestor m k q=q0) ⊆
      Q.filter (fun q => dist (carrier D a (rep q)) (carrier D a (rep p)) ≤ r) := by
    intro q hq
    obtain ⟨hq,hanc⟩ := mem_filter.mp hq
    refine mem_filter.mpr ⟨hq,?_⟩
    have hcell : parentLabel D a (2^k) (rep q)=parentLabel D a (2^k) (rep p) := by
      rw [←parent_ancestor_eq D a hk (rep q),←parent_ancestor_eq D a hk (rep p),hrep q hq,hrep p hp]
      exact hanc
    have hh := same_parameter_cell_carrier_dist h hK ha (rep q) (rep p) (2^k) (by positivity) hcell
    have hs : 16/((2^k:ℕ):ℝ) ≤ r := by
      calc
        _ = 16*(1/((2^k:ℕ):ℝ)) := by ring
        _ ≤ 16*(r/16) := mul_le_mul_of_nonneg_left hkhi (by norm_num)
        _ = _ := by ring
    exact hh.trans hs
  have Hk := H ⟨k,by omega⟩ q0 hne
  have hratio : r/(64/((2^m:ℕ):ℝ)) ≤ ((2^m:ℕ):ℝ)/((2^k:ℕ):ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hklo (show (0:ℝ) ≤ ((2^m:ℕ):ℝ) by positivity)
    calc
      _ = ((2^m:ℕ):ℝ)*(r/64) := by field_simp
      _ ≤ ((2^m:ℕ):ℝ)*(r/32) := by gcongr; linarith
      _ ≤ ((2^m:ℕ):ℝ)*(1/((2^k:ℕ):ℝ)) := hh
      _ = _ := by ring
  calc
    _ ≤ D.thickness^t*(((2^m:ℕ):ℝ)/((2^k:ℕ):ℝ))^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio 3) (Real.rpow_pos_of_pos hd _).le
    _ ≤ _ := Hk.trans (by exact_mod_cast card_le_card hsub)

end NativeCoarseCarrierGeometry
