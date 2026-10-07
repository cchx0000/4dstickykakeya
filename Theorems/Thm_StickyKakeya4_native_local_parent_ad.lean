import Theorems.Thm_StickyKakeya4_native_local_parent_geometry
import Theorems.Thm_StickyKakeya4_native_normalized_parent_carrier_metric
import Theorems.Thm_StickyKakeya4_native_coarse_ancestor_counts
import Theorems.Thm_StickyKakeya4_native_padded_source_ad_lower

/-!
New source-faithful reconstruction; strict verification is pending.

This draft extends actual canonical geometry, not an abstract certificate.
`R` must be the ONE original retained set already constructed by
`NativeCompactAncestorRegularity.compact_original_ancestor_regularization`.
All later incidence refinements keep the backbone `parentSubset` unchanged.
The `H` below is an intermediate, already source-derived dyadic population law.
It must not be exposed as an additional hypothesis of the final source theorem.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section

namespace NativeLocalParentAD
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentGeometry
open NativeNormalizedParentCarrierMetric NativeOriginalSlopeCubePacking
open NativeUnitParentDirections NativeCoarseAncestorCounts
open scoped ENNReal

def carrier {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (i : Fin n) : E4 × E4 :=
  (direction (NativeLocalParentGeometry.line D a N p i),
    offset (NativeLocalParentGeometry.line D a N p i))

def parentSubset {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a : ℝ) (N : ℕ) (p : Parent) : Finset (Fin n) :=
  R.filter (fun i => parentLabel D a N i = p)

def ballLabels {n : ℕ} (D : FiniteScaleSource n) (Q : Finset (Fin n))
    (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n) (r : ℝ) : Finset (Fin n) :=
  Q.filter (fun j => dist (carrier D a N p j) (carrier D a N p i) ≤ r)

lemma localIntercept_norm_le_one {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) (i : Fin n)
    (hi : parentLabel D a N i = p) :
    ‖localIntercept D a N p i‖ ≤ 1 := by
  have hb (j : Fin 3) : |localIntercept D a N p i j| ≤ 1/4 := by
    have hh := (NativeLocalParentGeometry.parameter_box D a N p i hi).2 j
    exact abs_le.mpr ⟨by linarith [hh.1], hh.2.le⟩
  have hh := euclidean_three_norm_le_two _ (1/4) (by norm_num) hb
  linarith

/-- Forward carrier metric at an arbitrary original parent scale. -/
theorem parameter_error_carrier_dist {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) (i j : Fin n)
    (hj : parentLabel D a N j = p) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ k, |slope (D.line i) k-slope (D.line j) k| ≤ r)
    (hb : ∀ k, |shiftedIntercept (D.line i) (mesh D) (shift D a) k-
      shiftedIntercept (D.line j) (mesh D) (shift D a) k| ≤ r) :
    dist (carrier D a N p i) (carrier D a N p j) ≤ 16*((N:ℝ)*r) := by
  have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hsu : ‖localSlope D N p i-localSlope D N p j‖ ≤ 2*((N:ℝ)*r) := by
    apply euclidean_three_norm_le_two _ _ (mul_nonneg hNr hr)
    intro k
    have he : (localSlope D N p i-localSlope D N p j) k =
        (N:ℝ)*(slope (D.line i) k-slope (D.line j) k) := by
      dsimp [localSlope]
      ring
    rw [he, abs_mul, abs_of_nonneg hNr]
    exact mul_le_mul_of_nonneg_left (hs k) hNr
  have hbi : ‖localIntercept D a N p i-localIntercept D a N p j‖ ≤
      ((N:ℝ)*r)/2 := by
    have hh := euclidean_three_norm_le_two
      (localIntercept D a N p i-localIntercept D a N p j)
      (((N:ℝ)*r)/4) (by positivity) (by
        intro k
        have he : (localIntercept D a N p i-localIntercept D a N p j) k =
            ((N:ℝ)*(shiftedIntercept (D.line i) (mesh D) (shift D a) k-
              shiftedIntercept (D.line j) (mesh D) (shift D a) k))/4 := by
          dsimp [localIntercept]
          ring
        rw [he, abs_div, abs_mul, abs_of_nonneg hNr,
          abs_of_pos (by norm_num : (0:ℝ)<4)]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb k) hNr) (by norm_num))
    linarith
  exact (contractLine_carrier_dist_le
    (baseLine D a N p i) (baseLine D a N p j)).trans
    (graph_carrier_dist_le_sixteen _ _ _ _ ((N:ℝ)*r)
      (mul_nonneg hNr hr) hsu hbi (localIntercept_norm_le_one D a N p j hj))

/-- A finer ORIGINAL parameter atom lies in the actual normalized carrier ball. -/
theorem same_finer_cell_carrier_dist {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (p : Parent) (i j : Fin n)
    (hj : parentLabel D a N j = p) (M : ℕ) (hM : 0 < M)
    (he : parentLabel D a M i = parentLabel D a M j) :
    dist (carrier D a N p i) (carrier D a N p j) ≤ 16*(N:ℝ)/(M:ℝ) := by
  have hh := parameter_error_carrier_dist D a N p i j hj
    (r:=1/(M:ℝ)) (by positivity)
    (fun k => same_floor_mul_close _ _ M hM (congrFun (congrArg Prod.fst he) k))
    (fun k => same_floor_mul_close _ _ M hM (congrFun (congrArg Prod.snd he) k))
  simpa only [mul_one_div, mul_div_assoc] using hh

/-- The inverse slope metric uses only actual normalized directions. -/
theorem original_slope_error_le {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (p : Parent) (i j : Fin n)
    (hi : parentLabel D a N i = p) (hj : parentLabel D a N j = p)
    (k : Fin 3) :
    |slope (D.line i) k-slope (D.line j) k| ≤
      6*dist (carrier D a N p i) (carrier D a N p j)/(N:ℝ) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨_, hci, _⟩ := NativeLocalParentGeometry.valid_slab D a N p i hi
  obtain ⟨hvj, hcj, _⟩ := NativeLocalParentGeometry.valid_slab D a N p j hj
  have hh := slope_sub_le_direction_dist _ _ hvj hci hcj k
  rw [NativeLocalParentGeometry.slope_line, NativeLocalParentGeometry.slope_line] at hh
  have he : localSlope D N p i k-localSlope D N p j k =
      (N:ℝ)*(slope (D.line i) k-slope (D.line j) k) := by
    dsimp [localSlope]
    ring
  rw [he, abs_mul, abs_of_pos hNr] at hh
  have hdir : dist (direction (NativeLocalParentGeometry.line D a N p i))
      (direction (NativeLocalParentGeometry.line D a N p j)) ≤
      dist (carrier D a N p i) (carrier D a N p j) := le_max_left _ _
  apply (le_div_iff₀ hNr).mpr
  nlinarith

/-- Absolute upper AD for any subset of the actual parent, including below
the old separation scale. The additive cube formula gives the small constant125. -/
theorem ball_card_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (N : ℕ) (hN : 0 < N) (p : Parent) (Q : Finset (Fin n))
    (hQ : ∀j∈Q,parentLabel D a N j=p) (i : Fin n)
    (hi : parentLabel D a N i=p) {r : ℝ}
    (hr : (N:ℝ)*D.thickness/64 ≤ r) :
    ((ballLabels D Q a N p i r).card:ℝ) ≤
      125*(r/((N:ℝ)*D.thickness/64))^3 := by
  let A := ballLabels D Q a N p i r
  have hd := h.1.2.1
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hlocal : 0 < (N:ℝ)*D.thickness/64 := by positivity
  have hrp := hlocal.trans_le hr
  have hbox (j : Fin n) (hj : j∈A) (k : Fin 3) :
      slope (D.line i) k-6*r/(N:ℝ) ≤ slope (D.line j) k ∧
      slope (D.line j) k ≤ (slope (D.line i) k-6*r/(N:ℝ))+12*r/(N:ℝ) := by
    obtain ⟨hjQ,hjr⟩ := mem_filter.mp hj
    have hh := original_slope_error_le D a N hN p j i (hQ j hjQ) hi k
    have hh' : |slope (D.line j) k-slope (D.line i) k| ≤ 6*r/(N:ℝ) :=
      hh.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hjr (by norm_num)) hNr.le)
    obtain ⟨hlo,hhi⟩ := abs_le.mp hh'
    constructor
    · linarith
    · have he : (slope (D.line i) k-6*r/(N:ℝ))+12*r/(N:ℝ) =
          slope (D.line i) k+6*r/(N:ℝ) := by ring
      rw [he]
      linarith
  have hh := original_cube_card_le A D.line hd
    (show 0 ≤ 12*r/(N:ℝ) by positivity)
    (fun j _ => h.1.2.2.2.2.1 j) (fun j _ => h.2.1.1 j)
    (fun j _ k _ hne => h.1.2.2.2.2.2.2.2.2.2.1 j k hne)
    (fun k => slope (D.line i) k-6*r/(N:ℝ)) hbox
  have he : 16*(12*r/(N:ℝ))/D.thickness+2 =
      3*(r/((N:ℝ)*D.thickness/64))+2 := by
    field_simp [hNr.ne',hd.ne']
    ring
  rw [he] at hh
  have ht : 1 ≤ r/((N:ℝ)*D.thickness/64) := (le_div_iff₀ hlocal).mpr (by simpa using hr)
  calc
    _ ≤ (3*(r/((N:ℝ)*D.thickness/64))+2)^3 := hh
    _ ≤ (5*(r/((N:ℝ)*D.thickness/64)))^3 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    _ = _ := by ring

/-- All-radius lower AD on the FULL retained original dyadic parent.
The intermediate H is exactly what canonical original regularization constructs.
The final theorem below removes H from the source-facing endpoint. -/
theorem ball_card_lower {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (R : Finset (Fin n)) (level : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (H : ∀ell : Fin (level+1),∀q : Parent,
      (R.filter (fun j => parentLabel D a (2^ell.val) j=q)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun j => parentLabel D a (2^ell.val) j=q)).card:ℝ))
    (m : ℕ) (p : Parent) (i : Fin n)
    (hi : i∈parentSubset D R a (2^m) p) {r : ℝ}
    (hr : ((2^m:ℕ):ℝ)*D.thickness/64 ≤ r) (hr1 : r ≤ 1) :
    D.thickness^zeta/(2048:ℝ)^3*
      (r/(((2^m:ℕ):ℝ)*D.thickness/64))^3 ≤
        ((ballLabels D (parentSubset D R a (2^m) p) a (2^m) p i r).card:ℝ) := by
  let N : ℕ := 2^m
  let Q := parentSubset D R a N p
  have hd := h.1.2.1
  have hN : 0 < N := by dsimp [N]; positivity
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlocal : 0 < (N:ℝ)*D.thickness/64 := by positivity
  have hrp : 0 < r := hlocal.trans_le hr
  have hiR : i∈R := (mem_filter.mp hi).1
  have hip : parentLabel D a N i=p := (mem_filter.mp hi).2
  change D.thickness^zeta/(2048:ℝ)^3*(r/((N:ℝ)*D.thickness/64))^3 ≤
    ((ballLabels D Q a N p i r).card:ℝ)
  by_cases hlarge : 32*(N:ℝ)*D.thickness ≤ r
  · have hepos : 0 < r/(N:ℝ) := div_pos hrp hNr
    have heone : r/(N:ℝ) ≤ 1 := (div_le_one hNr).mpr (hr1.trans hN1)
    obtain ⟨ell,helllo,hellhi⟩ :=
      NativePaddedSourceADLower.dyadic_below_radius hepos heone
    have hdell : D.thickness ≤ 1/((2^ell:ℕ):ℝ) := by
      apply le_trans _ helllo
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<32)).mpr
      apply (le_div_iff₀ hNr).mpr
      nlinarith
    have hpows : (1/2:ℝ)^level ≤ (1/2:ℝ)^ell := by
      simpa only [hdy,one_div,Nat.cast_pow,Nat.cast_ofNat,inv_pow] using hdell
    have hell : ell ≤ level := (pow_le_pow_iff_right_of_lt_one₀
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).mp hpows
    have hcellSmall : 1/((2^ell:ℕ):ℝ) ≤ 1/(N:ℝ) := by
      apply hellhi.trans
      calc
        (r/(N:ℝ))/16 ≤ r/(N:ℝ) := by linarith
        _ ≤ 1/(N:ℝ) := div_le_div_of_nonneg_right hr1 hNr.le
    have hpows' : (1/2:ℝ)^ell ≤ (1/2:ℝ)^m := by
      simpa only [N,one_div,Nat.cast_pow,Nat.cast_ofNat,inv_pow] using hcellSmall
    have hmell : m ≤ ell := (pow_le_pow_iff_right_of_lt_one₀
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).mp hpows'
    let q := parentLabel D a (2^ell) i
    have hneQ : (Q.filter (fun j => parentLabel D a (2^ell) j=q)).Nonempty :=
      ⟨i,mem_filter.mpr ⟨hi,rfl⟩⟩
    have hfiber := fiber_in_ancestor_eq D R a hmell p q hneQ
    have hneR : (R.filter (fun j => parentLabel D a (2^ell) j=q)).Nonempty :=
      ⟨i,mem_filter.mpr ⟨hiR,rfl⟩⟩
    have hAD := H ⟨ell,by omega⟩ q hneR
    have hscale : 16*(N:ℝ)/((2^ell:ℕ):ℝ) ≤ r := by
      have hh := mul_le_mul_of_nonneg_left hellhi (show 0≤16*(N:ℝ) by positivity)
      have he : 16*(N:ℝ)*((r/(N:ℝ))/16)=r := by field_simp
      simpa only [he,mul_one_div] using hh
    have hsub : Q.filter (fun j => parentLabel D a (2^ell) j=q) ⊆
        ballLabels D Q a N p i r := by
      intro j hj
      obtain ⟨hjQ,hjq⟩ := mem_filter.mp hj
      refine mem_filter.mpr ⟨hjQ,?_⟩
      exact (same_finer_cell_carrier_dist D a N p j i hip (2^ell)
        (by positivity) hjq).trans hscale
    have hc : ((R.filter (fun j => parentLabel D a (2^ell) j=q)).card:ℝ) ≤
        ((ballLabels D Q a N p i r).card:ℝ) := by
      rw [←hfiber]
      exact_mod_cast card_le_card hsub
    have he : D.thickness^zeta/(2048:ℝ)^3*(r/((N:ℝ)*D.thickness/64))^3 =
        D.thickness^zeta*(((r/(N:ℝ))/32)/D.thickness)^3 := by
      field_simp [hNr.ne',hd.ne']
      ring
    rw [he]
    calc
      _ ≤ D.thickness^zeta*((1/((2^ell:ℕ):ℝ))/D.thickness)^3 := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hd _).le
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_right helllo hd.le
      _ ≤ _ := hAD.trans hc
  · have hratio : r/((N:ℝ)*D.thickness/64) ≤ 2048 := by
      apply (div_le_iff₀ hlocal).mpr
      linarith
    have hpow : (r/((N:ℝ)*D.thickness/64))^3 ≤ (2048:ℝ)^3 :=
      pow_le_pow_left₀ (div_nonneg hrp.le hlocal.le) hratio 3
    have hz1 : D.thickness^zeta ≤ 1 := Real.rpow_le_one hd.le h.1.2.2.1 hzeta
    have hmass : D.thickness^zeta*(r/((N:ℝ)*D.thickness/64))^3 ≤ (2048:ℝ)^3 := by
      exact (mul_le_mul hz1 hpow (by positivity) (by norm_num)).trans_eq (by ring)
    have hball : (ballLabels D Q a N p i r).Nonempty :=
      ⟨i,mem_filter.mpr ⟨hi,by simpa only [dist_self] using hrp.le⟩⟩
    have hcard : 1 ≤ (ballLabels D Q a N p i r).card := card_pos.mpr hball
    calc
      _ = (D.thickness^zeta*(r/((N:ℝ)*D.thickness/64))^3)/(2048:ℝ)^3 := by ring
      _ ≤ (2048:ℝ)^3/(2048:ℝ)^3 := div_le_div_of_nonneg_right hmass (by positivity)
      _ = 1 := div_self (by norm_num)
      _ ≤ _ := by exact_mod_cast hcard

/-- Source-facing endpoint: actual compact original input constructs one R,
retaining shading mass and density, on which EVERY dyadic parent has all-radius
local carrier AD. No new lower-profile premise appears in this statement. -/
theorem compact_original_local_parent_AD (K : Set MarkedLine) (hK : IsCompact K)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃delta0 : ℝ, 0 < delta0 ∧ ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀i,D.line i∈K) →
      D.thickness ≤ delta0 → eta ≤ zeta/16 →
      ∃(a : ℝ) (level : ℕ) (R : Finset (Fin n)),
        D.thickness=(2:ℝ)⁻¹^level ∧
        (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
        R.Nonempty ∧ n ≤ 2*R.card ∧
        wzTotalShadingVolume D ≤ 2*NativeOriginalPrunedMass.shadingMass D R ∧
        (ENNReal.ofReal D.thickness).rpow zeta*NativeOriginalPrunedMass.tubeMass D R ≤
          NativeOriginalPrunedMass.shadingMass D R ∧
        (∀ U : Set E4, Convex ℝ U →
          ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card : ℝ≥0∞) ≤
            (ENNReal.ofReal D.thickness).rpow (-zeta) * volume U * R.card) ∧
        (∀ell : Fin (level+1),∀p : Parent,
          (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
            D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
            ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
              D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
        ∀m : ℕ,m ≤ level → ∀p : Parent,∀i∈parentSubset D R a (2^m) p,
          ∀r : ℝ,((2^m:ℕ):ℝ)*D.thickness/64 ≤ r → r ≤ 1 →
            D.thickness^zeta/(2048:ℝ)^3*(r/(((2^m:ℕ):ℝ)*D.thickness/64))^3 ≤
              ((ballLabels D (parentSubset D R a (2^m) p) a (2^m) p i r).card:ℝ) ∧
            ((ballLabels D (parentSubset D R a (2^m) p) a (2^m) p i r).card:ℝ) ≤
              125*(r/(((2^m:ℕ):ℝ)*D.thickness/64))^3 := by
  obtain ⟨delta0,hdelta0,hbase⟩ :=
    NativeCompactAncestorRegularity.compact_original_ancestor_regularization K hK hzeta
  refine ⟨delta0,hdelta0,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,hCW,H⟩ :=
    hbase n D eta h hDK hsmall heta
  refine ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,hCW,H,?_⟩
  intro m _hm p i hi r hr hr1
  refine ⟨ball_card_lower h hzeta.le R level hdy
    (fun ell q hq => (H ell q hq).1) m p i hi hr hr1,?_⟩
  exact ball_card_upper h (2^m) (by positivity) p
    (parentSubset D R a (2^m) p)
    (fun j hj => (mem_filter.mp hj).2) i (mem_filter.mp hi).2 hr

/-- A genuine relative power window supplies the native coefficients. The
cutoff is fixed before the original source and both integer scales. -/
theorem exists_native_coefficient_cutoff (alpha e zeta : ℝ)
    (he : 0 < e) (hzeta : 0 ≤ zeta) (hgap : zeta < alpha * e) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ 1 ∧ ∀ delta : ℝ,
      0 < delta → delta ≤ d0 → ∀ N : ℕ, 0 < N →
      (N : ℝ) * delta ≤ delta ^ alpha →
      ((N : ℝ) * delta / 64) ^ e ≤ delta ^ zeta / (2048 : ℝ) ^ 3 ∧
      125 ≤ ((N : ℝ) * delta / 64) ^ (-e) := by
  obtain ⟨d0, hd0, hd01, hsmall⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < alpha * e - zeta by linarith)
    (show 0 ≤ (2048 : ℝ) ^ 3 by positivity) (show (0 : ℝ) < 1 by norm_num)
  refine ⟨d0, hd0, hd01, ?_⟩
  intro delta hd hdelta N hN hwindow
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlocal : 0 < (N : ℝ) * delta / 64 := by positivity
  have hlocalWindow : (N : ℝ) * delta / 64 ≤ delta ^ alpha := by
    have hh : (N : ℝ) * delta / 64 ≤ (N : ℝ) * delta := by
      nlinarith only [mul_pos hNr hd]
    exact hh.trans hwindow
  have hpow : ((N : ℝ) * delta / 64) ^ e ≤ delta ^ (alpha * e) := by
    calc
      _ ≤ (delta ^ alpha) ^ e := Real.rpow_le_rpow hlocal.le hlocalWindow he.le
      _ = _ := (Real.rpow_mul hd.le alpha e).symm
  have hbudget : (2048 : ℝ) ^ 3 * delta ^ (alpha * e) ≤ delta ^ zeta := by
    calc
      _ = ((2048 : ℝ) ^ 3 * delta ^ (alpha * e - zeta)) * delta ^ zeta := by
        rw [mul_assoc, ← Real.rpow_add hd]
        congr 2
        ring
      _ ≤ 1 * delta ^ zeta := mul_le_mul_of_nonneg_right (hsmall delta hd hdelta)
        (Real.rpow_nonneg hd.le _)
      _ = _ := one_mul _
  have habs := (mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (2048 : ℝ) ^ 3 by positivity)).trans hbudget
  have hpower : 0 < ((N : ℝ) * delta / 64) ^ e := Real.rpow_pos_of_pos hlocal _
  have hdeltaPower : delta ^ zeta ≤ 1 :=
    Real.rpow_le_one hd.le (hdelta.trans hd01) hzeta
  constructor
  · apply (le_div_iff₀ (show 0 < (2048 : ℝ) ^ 3 by positivity)).mpr
    simpa only [mul_comm] using habs
  · rw [Real.rpow_neg hlocal.le, ← one_div]
    apply (le_div_iff₀ hpower).mpr
    calc
      _ ≤ (2048 : ℝ) ^ 3 * ((N : ℝ) * delta / 64) ^ e :=
        mul_le_mul_of_nonneg_right (by norm_num) hpower.le
      _ ≤ 1 := habs.trans hdeltaPower

end NativeLocalParentAD
