import Theorems.Thm_StickyKakeya4_native_local_parent_volume
import Theorems.Thm_StickyKakeya4_native_compact_ancestor_regularity
import Theorems.Thm_StickyKakeya4_native_local_parent_ad

/-!
Convex-Wolff for the actual local parent tubes. The physical preimage charges
each original label once. Original direction packing and original dyadic
ancestor populations cancel the full N^3 inverse-volume loss. The endpoint
constructs one retained original set and treats every dyadic parent of it.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section

namespace NativeLocalParentCW
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeOriginalSlopeCubePacking
open NativeOriginalPrunedMass
open scoped ENNReal

/-- Literal contained-tube labels, with the actual local lines and thickness. -/
def containedLabels {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (Q : Finset (Fin n)) (U : Set E4) : Finset (Fin n) :=
  Q.filter (fun i => markedUnitTube (NativeLocalParentGeometry.line D a N p i)
    ((N : ℝ) * D.thickness / 64) ⊆ U)

/-- The original north-chart separated directions fit the literal [-2,2]^3 cube. -/
theorem original_card_upper {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) :
    (n : ℝ) ≤ 373248 * (1 / D.thickness)^3 := by
  have hb := native_cube_card_le_ratio h (univ : Finset (Fin n))
    (rho := 4) (by linarith [h.1.2.2.1]) (fun _ => -2) (by
      intro i _hi j
      have hh := abs_le.mp (slope_bound (D.line i)
        (h.1.2.2.2.2.1 i) (h.2.1.1 i) j)
      exact ⟨hh.1, by linarith [hh.2]⟩)
  simp only [card_univ, Fintype.card_fin] at hb
  exact hb.trans_eq (by ring)

/-- Each contained local tube supplies an original tube in the same preimage. -/
theorem contained_card_le_preimage {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1/2 : ℝ)) (1/2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (Q : Finset (Fin n))
    (hQ : ∀ i ∈ Q, parentLabel D a N i = p) (U : Set E4) :
    (containedLabels D a N p Q U).card ≤
      wzContainedTubeCount D (NativeLocalParentPhysicalMap.physicalMap D a N p ⁻¹' U) := by
  apply card_le_card
  intro i hi
  obtain ⟨hiQ, hiU⟩ := mem_filter.mp hi
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  intro x hx
  exact hiU (NativeLocalParentPhysicalMap.original_tube_maps h ha N hN p i
    (hQ i hiQ) (Set.mem_image_of_mem _ hx))

/-- The inverse Jacobian and original parent lower occupancy cancel N^3. -/
theorem parent_count_coefficient {n : ℕ} {D : FiniteScaleSource n} {eta zeta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (N : ℕ) (hN : 0 < N) (Q : Finset (Fin n))
    (H : D.thickness^zeta * ((1/(N : ℝ))/D.thickness)^3 ≤ (Q.card : ℝ)) :
    (512^4/(N : ℝ)^3) * (n : ℝ) ≤
      (373248*512^4 : ℝ) * D.thickness^(-zeta) * Q.card := by
  have hd := h.1.2.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (512^4/(N : ℝ)^3) * (373248*(1/D.thickness)^3) :=
      mul_le_mul_of_nonneg_left (original_card_upper h) (by positivity)
    _ = ((373248*512^4 : ℝ)*D.thickness^(-zeta)) *
        (D.thickness^zeta*((1/(N : ℝ))/D.thickness)^3) := by
      rw [Real.rpow_neg hd.le]
      field_simp [hd.ne', hNr.ne', (Real.rpow_pos_of_pos hd zeta).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left H (by positivity)

/-- Actual local relative CW, for every convex set, including infinite volume.
H is only the original ancestor population, not an output CW certificate. -/
theorem original_local_CW {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1/2 : ℝ)) (1/2 : ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (Q : Finset (Fin n))
    (hQ : ∀ i ∈ Q, parentLabel D a N i = p)
    (H : D.thickness^zeta * ((1/(N : ℝ))/D.thickness)^3 ≤ (Q.card : ℝ))
    (U : Set E4) (hU : Convex ℝ U) :
    ((containedLabels D a N p Q U).card : ℝ≥0∞) ≤
      (373248*512^4 : ℝ≥0∞) * (ENNReal.ofReal D.thickness).rpow (-eta-zeta) *
        volume U * Q.card := by
  have hd := h.1.2.1
  let d := ENNReal.ofReal D.thickness
  have hd0 : d ≠ 0 := by dsimp [d]; positivity
  have hdT : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : ENNReal.ofReal (512^4/(N : ℝ)^3) * (n : ℝ≥0∞) ≤
      (373248*512^4 : ℝ≥0∞)*d.rpow (-zeta)*Q.card := by
    simpa only [d,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 512^4/(N : ℝ)^3),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (373248*512^4 : ℝ)*D.thickness^(-zeta)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ (373248*512^4 : ℝ)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 373248),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 512),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
      ENNReal.ofReal_rpow_of_pos hd, ENNReal.rpow_eq_pow] using
        ENNReal.ofReal_le_ofReal (parent_count_coefficient h N hN Q H)
  have hexp : d.rpow (-eta)*d.rpow (-zeta) = d.rpow (-eta-zeta) := by
    simp only [ENNReal.rpow_eq_pow]
    rw [← ENNReal.rpow_add _ _ hd0 hdT]
    congr 1
  have hw := h.1.2.2.2.2.2.2.2.2.2.2.2.1
    (NativeLocalParentPhysicalMap.physicalMap D a N p ⁻¹' U)
    (NativeLocalParentVolume.convex_preimage D a N p hU)
  rw [NativeLocalParentVolume.volume_preimage D a N hN p U] at hw
  calc
    _ ≤ (wzContainedTubeCount D
        (NativeLocalParentPhysicalMap.physicalMap D a N p ⁻¹' U) : ℝ≥0∞) := by
      exact_mod_cast contained_card_le_preimage h ha N hN p Q hQ U
    _ ≤ d.rpow (-eta)*(ENNReal.ofReal (512^4/(N : ℝ)^3)*volume U)*n := hw
    _ = d.rpow (-eta)*volume U*(ENNReal.ofReal (512^4/(N : ℝ)^3)*n) := by ring
    _ ≤ d.rpow (-eta)*volume U*((373248*512^4 : ℝ≥0∞)*d.rpow (-zeta)*Q.card) :=
      mul_le_mul' le_rfl hc
    _ = (373248*512^4 : ℝ≥0∞)*(d.rpow (-eta)*d.rpow (-zeta))*volume U*Q.card := by ring
    _ = _ := by rw [hexp]

/-- Source-facing construction: one retained original R supplies all dyadic
local parent CW bounds, along with its actual retained mass and original AD.
There is no added parent CW or lower-population hypothesis in this theorem. -/
theorem compact_original_local_parent_CW (K : Set MarkedLine) (hK : IsCompact K)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i, D.line i ∈ K) →
      D.thickness ≤ delta0 → eta ≤ zeta/16 →
      ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
        D.thickness=(2 : ℝ)⁻¹^level ∧
        (∀ i, wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2 : ℝ)) (1/2 : ℝ)) ∧
        R.Nonempty ∧ n ≤ 2*R.card ∧
        wzTotalShadingVolume D ≤ 2*shadingMass D R ∧
        (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D R ≤ shadingMass D R ∧
        (∀ U : Set E4, Convex ℝ U →
          ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card : ℝ≥0∞) ≤
            (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
        ∀ (ell : Fin (level+1)) (p : Parent),
          (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
            D.thickness^zeta*((1/((2^ell.val : ℕ) : ℝ))/D.thickness)^3 ≤
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card : ℝ) ∧
            ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card : ℝ) ≤
              D.thickness^(-zeta)*((1/((2^ell.val : ℕ) : ℝ))/D.thickness)^3 ∧
            ∀ U : Set E4, Convex ℝ U →
              ((containedLabels D a (2^ell.val) p
                (R.filter (fun i => parentLabel D a (2^ell.val) i=p)) U).card : ℝ≥0∞) ≤
              (373248*512^4 : ℝ≥0∞)*(ENNReal.ofReal D.thickness).rpow (-eta-zeta)*
                volume U*(R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card := by
  obtain ⟨delta0, hdelta0, hbase⟩ :=
    NativeCompactAncestorRegularity.compact_original_ancestor_regularization K hK hzeta
  refine ⟨delta0, hdelta0, ?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a, level, R, hdy, ha, hR, hhalf, hshade, hden, hCW, H⟩ :=
    hbase n D eta h hDK hsmall heta
  refine ⟨a, level, R, hdy, ha, hR, hhalf, hshade, hden, hCW, ?_⟩
  intro ell p hp
  refine ⟨(H ell p hp).1, (H ell p hp).2, ?_⟩
  intro U hU
  exact original_local_CW h ha (2^ell.val) (by positivity) p
    (R.filter (fun i => parentLabel D a (2^ell.val) i=p))
    (fun i hi => (mem_filter.mp hi).2) (H ell p hp).1 U hU

/-- The same retained original set simultaneously has actual local carrier AD
and actual local-tube CW in every dyadic parent, with its original retained
mass, density, and ancestor populations. -/
theorem compact_original_local_parent_AD_CW (K : Set MarkedLine) (hK : IsCompact K)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i, D.line i ∈ K) →
      D.thickness ≤ delta0 → eta ≤ zeta/16 →
      ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
        D.thickness=(2 : ℝ)⁻¹^level ∧
        (∀ i, wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2 : ℝ)) (1/2 : ℝ)) ∧
        R.Nonempty ∧ n ≤ 2*R.card ∧
        wzTotalShadingVolume D ≤ 2*shadingMass D R ∧
        (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D R ≤ shadingMass D R ∧
        (∀ U : Set E4, Convex ℝ U →
          ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card : ℝ≥0∞) ≤
            (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
        (∀ (ell : Fin (level+1)) (p : Parent),
          (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
            D.thickness^zeta*((1/((2^ell.val : ℕ) : ℝ))/D.thickness)^3 ≤
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card : ℝ) ∧
            ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card : ℝ) ≤
              D.thickness^(-zeta)*((1/((2^ell.val : ℕ) : ℝ))/D.thickness)^3) ∧
        (∀ m : ℕ, m ≤ level → ∀ p : Parent,
          ∀ i ∈ NativeLocalParentAD.parentSubset D R a (2^m) p,
          ∀ r : ℝ, ((2^m : ℕ) : ℝ)*D.thickness/64 ≤ r → r ≤ 1 →
            D.thickness^zeta/(2048 : ℝ)^3*(r/(((2^m : ℕ) : ℝ)*D.thickness/64))^3 ≤
              ((NativeLocalParentAD.ballLabels D
                (NativeLocalParentAD.parentSubset D R a (2^m) p) a (2^m) p i r).card : ℝ) ∧
            ((NativeLocalParentAD.ballLabels D
              (NativeLocalParentAD.parentSubset D R a (2^m) p) a (2^m) p i r).card : ℝ) ≤
              125*(r/(((2^m : ℕ) : ℝ)*D.thickness/64))^3) ∧
        ∀ (ell : Fin (level+1)) (p : Parent),
          (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
            ∀ U : Set E4, Convex ℝ U →
              ((containedLabels D a (2^ell.val) p
                (R.filter (fun i => parentLabel D a (2^ell.val) i=p)) U).card : ℝ≥0∞) ≤
              (373248*512^4 : ℝ≥0∞)*(ENNReal.ofReal D.thickness).rpow (-eta-zeta)*
                volume U*(R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card := by
  obtain ⟨delta0, hdelta0, hbase⟩ :=
    NativeLocalParentAD.compact_original_local_parent_AD K hK hzeta
  refine ⟨delta0, hdelta0, ?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a, level, R, hdy, ha, hR, hhalf, hshade, hden, hCW, H, hAD⟩ :=
    hbase n D eta h hDK hsmall heta
  refine ⟨a, level, R, hdy, ha, hR, hhalf, hshade, hden, hCW, H, hAD, ?_⟩
  intro ell p hp U hU
  exact original_local_CW h ha (2^ell.val) (by positivity) p
    (R.filter (fun i => parentLabel D a (2^ell.val) i=p))
    (fun i hi => (mem_filter.mp hi).2) (H ell p hp).1 U hU

end NativeLocalParentCW
