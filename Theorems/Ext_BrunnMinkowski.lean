import Mathlib

/-!
Vendored from David V. Feldman's `arranging-convex-bodies`, commit
`f7b4a98089e68d4ddc42cf1bd24094f9fbf16ee3`, file
`CentroidAlignment/BrunnMinkowski.lean`, under the Apache License 2.0.
The namespace and theorem names are retained for transparent provenance.
-/

open scoped Pointwise ENNReal
open Set MeasureTheory

namespace CentroidAlignment

/-- One-dimensional additive Brunn--Minkowski for nonempty compact sets. -/
theorem bm1_add {X Y : Set ℝ} (hX : IsCompact X) (hY : IsCompact Y)
    (hXne : X.Nonempty) (hYne : Y.Nonempty) :
    volume X + volume Y ≤ volume (X + Y) := by
  let a := sSup X
  let b := sInf Y
  have ha : a ∈ X := hX.sSup_mem hXne
  have hb : b ∈ Y := hY.sInf_mem hYne
  let U : Set ℝ := b +ᵥ X
  let V : Set ℝ := a +ᵥ Y
  have hU : U ⊆ X + Y := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨x, hx, b, hb, add_comm _ _⟩
  have hV : V ⊆ X + Y := by
    rintro z ⟨y, hy, rfl⟩
    exact ⟨a, ha, y, hy, rfl⟩
  have hbddX : BddAbove X := hX.isBounded.bddAbove
  have hbddY : BddBelow Y := hY.isBounded.bddBelow
  have hinter : U ∩ V ⊆ {a + b} := by
    rintro z ⟨⟨x, hx, hzx⟩, ⟨y, hy, hzy⟩⟩
    have hxa : x ≤ a := le_csSup hbddX hx
    have hby : b ≤ y := csInf_le hbddY hy
    have heq : b + x = a + y := by
      simpa only [vadd_eq_add] using hzx.trans hzy.symm
    have hxeq : x = a := by linarith
    have hyeq : y = b := by linarith
    change z = a + b
    simpa only [vadd_eq_add, hxeq, add_comm] using hzx.symm
  have had : AEDisjoint volume U V := by
    rw [AEDisjoint]
    exact measure_mono_null hinter (measure_singleton (a + b))
  calc
    volume X + volume Y = volume U + volume V := by simp [U, V, measure_vadd]
    _ = volume (U ∪ V) := (measure_union₀ (hY.vadd a).nullMeasurableSet had).symm
    _ ≤ volume (X + Y) := measure_mono (union_subset hU hV)

/-- Weighted two-term AM--GM in `ℝ≥0∞`. -/
theorem wgm2 {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a b : ℝ≥0∞) :
    a ^ (1 - t) * b ^ t ≤ ENNReal.ofReal (1 - t) * a + ENNReal.ofReal t * b := by
  by_cases ha : a = 0
  · rcases eq_or_lt_of_le (by linarith : 0 ≤ 1 - t) with h1t | h1t
    · simp [ha, show t = 1 by linarith]
    · simp [ha, h1t]
  by_cases hb : b = 0
  · rcases eq_or_lt_of_le ht0 with ht0' | ht0'
    · simp [hb, show t = 0 by linarith]
    · simp [hb, ht0']
  by_cases ha_top : a = ⊤
  · rcases eq_or_lt_of_le ht0 with ht0' | ht0'
    · -- t = 0
      subst ht0'
      simp [ha_top]
    · rcases eq_or_lt_of_le (by linarith : 0 ≤ 1 - t) with h1t | h1t
      · -- t = 1
        simp [show t = 1 by linarith]
      · -- 0 < t < 1
        subst ha_top
        rw [ENNReal.top_rpow_of_pos h1t]
        have hb_pow_ne : b ^ t ≠ 0 := by
          by_cases hb_top : b = ⊤
          · rw [hb_top, ENNReal.top_rpow_of_pos ht0']; exact ENNReal.top_ne_zero
          · simp [hb, hb_top, ht0']
        rw [mul_comm, ENNReal.mul_top hb_pow_ne]
        rw [ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr h1t))]
        exact le_self_add (b := ENNReal.ofReal t * b)
  by_cases hb_top : b = ⊤
  · rcases eq_or_lt_of_le ht0 with ht0' | ht0'
    · -- t = 0
      subst ht0'
      simp [hb_top]
    · -- t > 0
      simp [hb_top, ht0']
  -- Both a and b are finite and nonzero
  have ha_pos : 0 < a.toReal := by
    cases a with
    | top => contradiction
    | coe r => simp only [ENNReal.coe_toReal]; exact NNReal.coe_pos.mpr (pos_of_ne_zero (by simpa using ha))
  have hb_pos : 0 < b.toReal := by
    cases b with
    | top => contradiction
    | coe r => simp only [ENNReal.coe_toReal]; exact NNReal.coe_pos.mpr (pos_of_ne_zero (by simpa using hb))
  have h := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - t) (w₂ := t) (p₁ := a.toReal) (p₂ := b.toReal)
    (by linarith) ht0 (le_of_lt ha_pos) (le_of_lt hb_pos) (by ring)
  have ha_eq : a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal (by simp [ha_top])).symm
  have hb_eq : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal (by simp [hb_top])).symm
  rw [ha_eq, hb_eq]
  rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt ha_pos) (by linarith : 0 ≤ 1 - t)]
  rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt hb_pos) ht0]
  have lhs_eq : ENNReal.ofReal (a.toReal ^ (1 - t)) * ENNReal.ofReal (b.toReal ^ t) =
      ENNReal.ofReal (a.toReal ^ (1 - t) * b.toReal ^ t) := by
    rw [ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos ha_pos (1 - t)))]
  have rhs1_eq : ENNReal.ofReal (1 - t) * ENNReal.ofReal a.toReal =
      ENNReal.ofReal ((1 - t) * a.toReal) := by
    rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 1 - t)]
  have rhs2_eq : ENNReal.ofReal t * ENNReal.ofReal b.toReal =
      ENNReal.ofReal (t * b.toReal) := by
    rw [ENNReal.ofReal_mul ht0]
  have rhs_eq : ENNReal.ofReal (1 - t) * ENNReal.ofReal a.toReal + ENNReal.ofReal t * ENNReal.ofReal b.toReal =
      ENNReal.ofReal ((1 - t) * a.toReal + t * b.toReal) := by
    rw [rhs1_eq, rhs2_eq, ENNReal.ofReal_add (mul_nonneg (by linarith : 0 ≤ 1 - t) (le_of_lt ha_pos)) (mul_nonneg ht0 (le_of_lt hb_pos))]
  rw [lhs_eq, rhs_eq]
  exact ENNReal.ofReal_le_ofReal h

section PLdimOne

/-- Inner approximation of measurable subsets of `ℝ` by compacts, in
existential form. Self-contained: exhausts by `Icc` windows and applies
finite-measure inner regularity on each window. -/
theorem exists_isCompact_lt {U : Set ℝ} (hU : MeasurableSet U) {r : ℝ≥0∞}
    (hr : r < volume U) : ∃ K, K ⊆ U ∧ IsCompact K ∧ r < volume K := by
  have hmono : Monotone (fun k : ℕ => U ∩ Icc (-(k : ℝ)) k) := by
    intro i j hij
    refine Set.inter_subset_inter_right _ (Set.Icc_subset_Icc ?_ ?_)
    · exact neg_le_neg (by exact_mod_cast hij)
    · exact_mod_cast hij
  have hUnion : (⋃ k : ℕ, U ∩ Icc (-(k : ℝ)) k) = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      exact hk.1
    · intro hx
      obtain ⟨k, hk⟩ := exists_nat_ge |x|
      exact Set.mem_iUnion.mpr ⟨k, hx, (abs_le.mp hk).1, (abs_le.mp hk).2⟩
  have hsup : volume U = ⨆ k : ℕ, volume (U ∩ Icc (-(k : ℝ)) k) := by
    conv_lhs => rw [← hUnion]
    -- NAME-RISK: `MeasureTheory.measure_iUnion_eq_iSup` needs
    -- `Directed (· ⊆ ·)`; obtain it from `hmono.directed_le`.
    exact hmono.measure_iUnion
  rw [hsup] at hr
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hr
  have hfin : volume (U ∩ Icc (-(k : ℝ)) k) ≠ ⊤ := by
    refine (lt_of_le_of_lt (measure_mono Set.inter_subset_right) ?_).ne
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hmeas : MeasurableSet (U ∩ Icc (-(k : ℝ)) k) := hU.inter measurableSet_Icc
  have hεne : volume (U ∩ Icc (-(k : ℝ)) k) - r ≠ 0 := (tsub_pos_of_lt hk).ne'
  -- NAME-RISK: `MeasurableSet.exists_isCompact_lt_add
  --   (h : μ s ≠ ⊤) (hε : ε ≠ 0) : ∃ K ⊆ s, IsCompact K ∧ μ s < μ K + ε`
  -- (inner regularity of Lebesgue/Haar for finite-measure measurable sets;
  -- if the instance route stalls, search `InnerRegularCompactLTTop`).
  obtain ⟨K, hKsub, hKcpt, hKlt⟩ := hmeas.exists_isCompact_lt_add hfin hεne
  refine ⟨K, hKsub.trans Set.inter_subset_left, hKcpt, ?_⟩
  by_contra hcon
  push_neg at hcon
  have h1 : volume (U ∩ Icc (-(k : ℝ)) k)
      < r + (volume (U ∩ Icc (-(k : ℝ)) k) - r) := by
    calc volume (U ∩ Icc (-(k : ℝ)) k)
        < volume K + (volume (U ∩ Icc (-(k : ℝ)) k) - r) := hKlt
      _ ≤ r + (volume (U ∩ Icc (-(k : ℝ)) k) - r) := by gcongr
  rw [add_tsub_cancel_of_le hk.le] at h1
  -- NAME-RISK: `add_tsub_cancel_of_le : a ≤ b → a + (b - a) = b` in ℝ≥0∞.
  exact lt_irrefl _ h1

/-- The one-dimensional superlevel inequality behind Prékopa–Leindler.
Note carefully: the Minkowski sum of the (merely measurable) sets `U`, `V`
is never formed — only sums of compact inner approximations, which are
compact and sit inside `W`; `volume W` bounds them by monotonicity alone,
with no measurability needed for `W`. -/
theorem level_volume_bound {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {U V W : Set ℝ} (hUm : MeasurableSet U) (hVm : MeasurableSet V)
    (hUne : U.Nonempty) (hVne : V.Nonempty)
    (hmem : ∀ x ∈ U, ∀ y ∈ V, (1 - t) * x + t * y ∈ W) :
    ENNReal.ofReal (1 - t) * volume U + ENNReal.ofReal t * volume V
      ≤ volume W := by
  obtain ⟨x₀, hx₀⟩ := hUne
  obtain ⟨y₀, hy₀⟩ := hVne
  -- Main computation for NONEMPTY compacts K ⊆ U, L ⊆ V.
  have claim1 : ∀ K ⊆ U, IsCompact K → K.Nonempty →
      ∀ L ⊆ V, IsCompact L → L.Nonempty →
      ENNReal.ofReal (1 - t) * volume K + ENNReal.ofReal t * volume L
        ≤ volume W := by
    intro K hKU hKc hKne L hLV hLc hLne
    have hKc' : IsCompact ((1 - t) • K) := hKc.smul (1 - t)
    -- NAME-RISK: `IsCompact.smul` (continuous scalar action on ℝ).
    have hLc' : IsCompact (t • L) := hLc.smul t
    have hKne' : ((1 - t) • K).Nonempty := hKne.smul_set
    -- NAME-RISK: `Set.Nonempty.smul_set`.
    have hLne' : (t • L).Nonempty := hLne.smul_set
    have hsum : ((1 - t) • K) + (t • L) ⊆ W := by
      rintro z hz
      obtain ⟨k', hk', l', hl', rfl⟩ := Set.mem_add.mp hz
      obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hk'
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hl'
      simpa [smul_eq_mul] using hmem x (hKU hx) y (hLV hy)
    have hscaleK : volume ((1 - t) • K) = ENNReal.ofReal (1 - t) * volume K := by
      rw [Measure.addHaar_smul volume]
      congr 2
      -- NAME-RISK: `finrank_self ℝ : Module.finrank ℝ ℝ = 1`; then `pow_one`.
      rw [Module.finrank_self, pow_one, abs_of_pos (by linarith : (0:ℝ) < 1 - t)]
    have hscaleL : volume (t • L) = ENNReal.ofReal t * volume L := by
      rw [Measure.addHaar_smul volume]
      congr 2
      rw [Module.finrank_self, pow_one, abs_of_pos ht0]
    calc ENNReal.ofReal (1 - t) * volume K + ENNReal.ofReal t * volume L
        = volume ((1 - t) • K) + volume (t • L) := by rw [hscaleK, hscaleL]
      _ ≤ volume (((1 - t) • K) + (t • L)) := bm1_add hKc' hLc' hKne' hLne'
      _ ≤ volume W := measure_mono hsum
  -- Emptiness-tolerant version, substituting singletons from `hUne`/`hVne`.
  have claim2 : ∀ K ⊆ U, IsCompact K → ∀ L ⊆ V, IsCompact L →
      ENNReal.ofReal (1 - t) * volume K + ENNReal.ofReal t * volume L
        ≤ volume W := by
    intro K hKU hKc L hLV hLc
    rcases K.eq_empty_or_nonempty with hK | hKne
    · rcases L.eq_empty_or_nonempty with hL | hLne
      · simp [hK, hL]
      · have h := claim1 {x₀} (Set.singleton_subset_iff.mpr hx₀)
          isCompact_singleton (Set.singleton_nonempty _) L hLV hLc hLne
        simpa [hK, Real.volume_singleton] using h
        -- NAME-RISK: `Real.volume_singleton : volume {a} = 0`
        -- (or `measure_singleton`).
    · rcases L.eq_empty_or_nonempty with hL | hLne
      · have h := claim1 K hKU hKc hKne {y₀}
          (Set.singleton_subset_iff.mpr hy₀) isCompact_singleton
          (Set.singleton_nonempty _)
        simpa [hL, Real.volume_singleton] using h
      · exact claim1 K hKU hKc hKne L hLV hLc hLne
  -- Convert the volumes of U, V to suprema over compact subsets.
  have hUeq : volume U
      = ⨆ K : {K : Set ℝ // K ⊆ U ∧ IsCompact K}, volume K.1 := by
    refine le_antisymm (le_of_forall_lt fun r hr => ?_)
      (iSup_le fun K => measure_mono K.2.1)
    obtain ⟨K, hKU, hKc, hrK⟩ := exists_isCompact_lt hUm hr
    exact lt_of_lt_of_le hrK
      (le_iSup (fun K : {K : Set ℝ // K ⊆ U ∧ IsCompact K} => volume K.1)
        ⟨K, hKU, hKc⟩)
  have hVeq : volume V
      = ⨆ L : {L : Set ℝ // L ⊆ V ∧ IsCompact L}, volume L.1 := by
    refine le_antisymm (le_of_forall_lt fun r hr => ?_)
      (iSup_le fun L => measure_mono L.2.1)
    obtain ⟨L, hLV, hLc, hrL⟩ := exists_isCompact_lt hVm hr
    exact lt_of_lt_of_le hrL
      (le_iSup (fun L : {L : Set ℝ // L ⊆ V ∧ IsCompact L} => volume L.1)
        ⟨L, hLV, hLc⟩)
  haveI : Nonempty {K : Set ℝ // K ⊆ U ∧ IsCompact K} :=
    ⟨⟨∅, Set.empty_subset _, isCompact_empty⟩⟩
  haveI : Nonempty {L : Set ℝ // L ⊆ V ∧ IsCompact L} :=
    ⟨⟨∅, Set.empty_subset _, isCompact_empty⟩⟩
  rw [hUeq, hVeq, ENNReal.mul_iSup, ENNReal.mul_iSup]
  -- (⨆ A) + (⨆ B) = ⨆ ⨆ (A + B) in ℝ≥0∞ with nonempty indices.
  rw [ENNReal.iSup_add]
  -- NAME-RISK: `ENNReal.iSup_add : (⨆ i, f i) + a = ⨆ i, f i + a` [Nonempty].
  refine iSup_le fun K => ?_
  rw [ENNReal.add_iSup]
  -- NAME-RISK: `ENNReal.add_iSup : a + ⨆ i, f i = ⨆ i, a + f i` [Nonempty].
  exact iSup_le fun L => claim2 K.1 K.2.1 K.2.2 L.1 L.2.1 L.2.2

/-- One-dimensional Prékopa–Leindler for `ℝ≥0∞`-valued functions,
sup-normalized form. Work-order §2.3. Both the `≤ 1` bounds and the
`1 ≤ ⨆` conditions are essential: the former makes truncation and the
layer-cake conversion painless, the latter guarantees nonempty superlevel
sets at every level below one — the classical proof breaks without it. -/
theorem pl_dim_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ y, g y ≤ 1)
    (hfs : 1 ≤ ⨆ x, f x) (hgs : 1 ≤ ⨆ y, g y)
    (hyp : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h z := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  -- Step A: truncate h at 1; the hypothesis survives because the left side
  -- is at most 1.
  set h₁ : ℝ → ℝ≥0∞ := fun z => min (h z) 1 with hh₁def
  have hh₁ : Measurable h₁ := hh.min measurable_const
  have hh₁le : ∀ z, h₁ z ≤ 1 := fun z => min_le_right _ _
  have hh₁ne : ∀ z, h₁ z ≠ ⊤ := fun z =>
    (lt_of_le_of_lt (hh₁le z) ENNReal.one_lt_top).ne
  have hyp₁ : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h₁ ((1 - t) * x + t * y) := by
    intro x y
    refine le_min (hyp x y) ?_
    exact mul_le_one' (ENNReal.rpow_le_one (hf1 x) ht1'.le)
      (ENNReal.rpow_le_one (hg1 y) ht0.le)
    -- NAME-RISK: `ENNReal.rpow_le_one : x ≤ 1 → 0 ≤ y → x ^ y ≤ 1`;
    -- `mul_le_one'` in the ordered monoid ℝ≥0∞.
  suffices hmain :
      (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t ≤ ∫⁻ z, h₁ z by
    exact hmain.trans (lintegral_mono fun z => min_le_left _ _)
  have hfne : ∀ x, f x ≠ ⊤ := fun x =>
    (lt_of_le_of_lt (hf1 x) ENNReal.one_lt_top).ne
  have hgne : ∀ y, g y ≠ ⊤ := fun y =>
    (lt_of_le_of_lt (hg1 y) ENNReal.one_lt_top).ne
  -- Superlevel sets at real levels.
  set U : ℝ → Set ℝ := fun ℓ => {x | ENNReal.ofReal ℓ < f x} with hUdef
  set V : ℝ → Set ℝ := fun ℓ => {y | ENNReal.ofReal ℓ < g y} with hVdef
  set W : ℝ → Set ℝ := fun ℓ => {z | ENNReal.ofReal ℓ < h₁ z} with hWdef
  have hUmeas : ∀ ℓ, MeasurableSet (U ℓ) := fun ℓ =>
    hf measurableSet_Ioi
  -- NAME-RISK: `{x | c < f x} = f ⁻¹' Ioi c`; if the application form
  -- `hf measurableSet_Ioi` does not elaborate, use
  -- `measurableSet_lt measurable_const hf`.
  have hVmeas : ∀ ℓ, MeasurableSet (V ℓ) := fun ℓ => hg measurableSet_Ioi
  -- Step B: the level inequality, all levels ℓ > 0.
  have hlevel : ∀ ℓ ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (1 - t) * volume (U ℓ) + ENNReal.ofReal t * volume (V ℓ)
        ≤ volume (W ℓ) := by
    intro ℓ hℓ
    rcases lt_or_ge ℓ 1 with hℓ1 | hℓ1
    · -- 0 < ℓ < 1: apply `level_volume_bound`.
      have hc0 : ENNReal.ofReal ℓ ≠ 0 := (ENNReal.ofReal_pos.mpr hℓ).ne'
      have hctop : ENNReal.ofReal ℓ ≠ ⊤ := ENNReal.ofReal_ne_top
      have hUne : (U ℓ).Nonempty := by
        have : ENNReal.ofReal ℓ < ⨆ x, f x :=
          lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr hℓ1) hfs
        obtain ⟨x, hx⟩ := lt_iSup_iff.mp this
        exact ⟨x, hx⟩
      have hVne : (V ℓ).Nonempty := by
        have : ENNReal.ofReal ℓ < ⨆ y, g y :=
          lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr hℓ1) hgs
        obtain ⟨y, hy⟩ := lt_iSup_iff.mp this
        exact ⟨y, hy⟩
      refine level_volume_bound ht0 ht1 (hUmeas ℓ) (hVmeas ℓ) hUne hVne ?_
      intro x hx y hy
      -- c = c^(1-t) * c^t < (f x)^(1-t) * (g y)^t ≤ h₁((1-t)x + ty).
      have hself : ENNReal.ofReal ℓ ^ (1 - t) * ENNReal.ofReal ℓ ^ t
          = ENNReal.ofReal ℓ := by
        rw [← ENNReal.rpow_add _ _ hc0 hctop]
        norm_num
      have hct0 : ENNReal.ofReal ℓ ^ t ≠ 0 := by
        -- NAME-RISK: `ENNReal.rpow_pos : 0 < x → x ≠ ⊤ → 0 < x ^ y`
        -- (name may be `ENNReal.rpow_pos_of_nonneg` or similar; the base is
        -- positive and finite).
        exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hℓ) hctop).ne'
      have hcttop : ENNReal.ofReal ℓ ^ t ≠ ⊤ := by
        refine (lt_of_le_of_lt (ENNReal.rpow_le_one ?_ ht0.le)
          ENNReal.one_lt_top).ne
        exact (ENNReal.ofReal_lt_one.mpr hℓ1).le
      have hstep1 : ENNReal.ofReal ℓ ^ (1 - t) * ENNReal.ofReal ℓ ^ t
          < f x ^ (1 - t) * ENNReal.ofReal ℓ ^ t := by
        simpa [mul_comm] using
          ENNReal.mul_lt_mul_right hct0 hcttop (ENNReal.rpow_lt_rpow hx ht1')
        -- NAME-RISK: `ENNReal.rpow_lt_rpow : a < b → 0 < z → a ^ z < b ^ z`.
      have hstep2 : f x ^ (1 - t) * ENNReal.ofReal ℓ ^ t
          ≤ f x ^ (1 - t) * g y ^ t :=
        mul_le_mul_right (ENNReal.rpow_le_rpow hy.le ht0.le) _
      show ENNReal.ofReal ℓ < h₁ ((1 - t) * x + t * y)
      calc ENNReal.ofReal ℓ
          = ENNReal.ofReal ℓ ^ (1 - t) * ENNReal.ofReal ℓ ^ t := hself.symm
        _ < f x ^ (1 - t) * ENNReal.ofReal ℓ ^ t := hstep1
        _ ≤ f x ^ (1 - t) * g y ^ t := hstep2
        _ ≤ h₁ ((1 - t) * x + t * y) := hyp₁ x y
    · -- ℓ ≥ 1: both superlevel sets are empty.
      have hUe : U ℓ = ∅ := by
        ext x
        simp only [hUdef, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_lt]
        exact (hf1 x).trans (ENNReal.one_le_ofReal.mpr hℓ1)
        -- NAME-RISK: `ENNReal.one_le_ofReal : 1 ≤ ofReal r ↔ 1 ≤ r`
        -- (may need the `.mpr` on the primed/unprimed variant).
      have hVe : V ℓ = ∅ := by
        ext y
        simp only [hVdef, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_lt]
        exact (hg1 y).trans (ENNReal.one_le_ofReal.mpr hℓ1)
      simp [hUe, hVe]
  -- Step C: layer cake for f, g, h₁.
  have hlayer : ∀ (φ : ℝ → ℝ≥0∞), Measurable φ → (∀ x, φ x ≠ ⊤) →
      (∫⁻ x, φ x) = ∫⁻ ℓ in Ioi (0 : ℝ), volume {x | ENNReal.ofReal ℓ < φ x} := by
    intro φ hφ hφne
    calc (∫⁻ x, φ x)
        = ∫⁻ x, ENNReal.ofReal ((φ x).toReal) := by
          congr 1
          ext x
          exact (ENNReal.ofReal_toReal (hφne x)).symm
      _ = ∫⁻ ℓ in Ioi (0 : ℝ), volume {x | ℓ < (φ x).toReal} := by
          -- NAME-RISK: exact name and argument shape from
          -- `Mathlib/MeasureTheory/Integral/Layercake.lean`:
          -- `lintegral_eq_lintegral_meas_lt (μ)
          --    (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ) :
          --    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ
          --      = ∫⁻ t in Ioi 0, μ {ω | t < f ω}`.
          exact lintegral_eq_lintegral_meas_lt volume
            (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg)
            hφ.ennreal_toReal.aemeasurable
      _ = ∫⁻ ℓ in Ioi (0 : ℝ), volume {x | ENNReal.ofReal ℓ < φ x} := by
          refine setLIntegral_congr_fun measurableSet_Ioi ?_
          -- NAME-RISK: `setLIntegral_congr_fun (hs) : (∀ᵐ/∀ x ∈ s, f = g) → …`;
          -- adjust between the a.e. and pointwise variants.
          intro ℓ hℓ
          apply congrArg volume
          ext x
          change (ℓ < (φ x).toReal) ↔ (ENNReal.ofReal ℓ < φ x)
          exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hℓ) (hφne x)).symm
          -- NAME-RISK: `ENNReal.ofReal_lt_iff_lt_toReal :
          --   0 ≤ p → q ≠ ⊤ → (ofReal p < q ↔ p < q.toReal)`.
  have hlf := hlayer f hf hfne
  have hlg := hlayer g hg hgne
  have hlh := hlayer h₁ hh₁ hh₁ne
  -- Step D: integrate the level inequality and finish with wgm2.
  have hUmble : Measurable fun ℓ : ℝ => volume (U ℓ) := by
    have hanti : Antitone fun ℓ : ℝ => volume (U ℓ) := by
      intro ℓ ℓ' hℓℓ'
      exact measure_mono fun x hx =>
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hℓℓ') hx
    exact hanti.measurable
  have hVmble : Measurable fun ℓ : ℝ => volume (V ℓ) := by
    have hanti : Antitone fun ℓ : ℝ => volume (V ℓ) := by
      intro ℓ ℓ' hℓℓ'
      exact measure_mono fun y hy =>
        lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hℓℓ') hy
    exact hanti.measurable
  have hint : ENNReal.ofReal (1 - t) * (∫⁻ x, f x)
      + ENNReal.ofReal t * (∫⁻ y, g y) ≤ ∫⁻ z, h₁ z := by
    rw [hlf, hlg, hlh]
    calc ENNReal.ofReal (1 - t) * (∫⁻ ℓ in Ioi (0:ℝ), volume (U ℓ))
          + ENNReal.ofReal t * (∫⁻ ℓ in Ioi (0:ℝ), volume (V ℓ))
        = ∫⁻ ℓ in Ioi (0:ℝ),
            (ENNReal.ofReal (1 - t) * volume (U ℓ)
              + ENNReal.ofReal t * volume (V ℓ)) := by
          rw [lintegral_add_left (hUmble.const_mul _),
            lintegral_const_mul _ hUmble, lintegral_const_mul _ hVmble]
          -- NAME-RISK: on the restricted measure the same lemma names apply;
          -- if `lintegral_const_mul` demands the unrestricted measure
          -- explicitly, use its `Measure.restrict` instantiation.
      _ ≤ ∫⁻ ℓ in Ioi (0:ℝ), volume (W ℓ) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr ?_)
          -- NAME-RISK: `ae_restrict_iff' (hs : MeasurableSet s) :
          --   (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x`;
          -- `lintegral_mono_ae` applied at the restricted measure.
          exact Filter.Eventually.of_forall hlevel
  -- Final assembly.
  calc (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t
      ≤ ENNReal.ofReal (1 - t) * (∫⁻ x, f x)
          + ENNReal.ofReal t * (∫⁻ y, g y) := wgm2 ht0.le ht1.le _ _
    _ ≤ ∫⁻ z, h₁ z := hint
end PLdimOne

/-- Multiplicative Brunn--Minkowski on the coordinate-function model. -/
theorem bm_mult_pi : ∀ (d : ℕ) {t : ℝ}, 0 < t → t < 1 →
    ∀ {A B : Set (Fin d → ℝ)}, IsCompact A → IsCompact B →
    A.Nonempty → B.Nonempty →
    volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B) := by
  -- Helper for first-coordinate slices: sliceFst T τ = {y | (τ, y) ∈ T}
  let sliceFst (α : Type) (T : Set (ℝ × α)) (τ : ℝ) : Set α := {y | (τ, y) ∈ T}
  have measurableSet_sliceFst {α : Type} [MeasurableSpace α] {T : Set (ℝ × α)} (hT : MeasurableSet T) (τ : ℝ) : MeasurableSet (sliceFst α T τ) :=
    hT.preimage (measurable_const.prodMk measurable_id)
  have isCompact_sliceFst {α : Type} [TopologicalSpace α] [T2Space α] {T : Set (ℝ × α)} (hT : IsCompact T) (τ : ℝ) : IsCompact (sliceFst α T τ) := by
    refine IsCompact.of_isClosed_subset (hT.image continuous_snd) ?_ ?_
    · exact hT.isClosed.preimage (continuous_const.prodMk continuous_id)
    · exact fun y hy => ⟨(τ, y), hy, rfl⟩
  have volume_eq_lintegral_sliceFst {d : ℕ} {T : Set (ℝ × (Fin d → ℝ))} (hT : MeasurableSet T) : volume T = ∫⁻ τ, volume (sliceFst (Fin d → ℝ) T τ) := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_apply hT]; rfl
  have measurable_volume_sliceFst {d : ℕ} {T : Set (ℝ × (Fin d → ℝ))} (hT : MeasurableSet T) : Measurable fun τ => volume (sliceFst (Fin d → ℝ) T τ) := by
    have h1 : (fun τ => volume (sliceFst (Fin d → ℝ) T τ)) = (fun τ => volume (Prod.mk τ ⁻¹' T)) := by rfl
    rw [h1]
    exact measurable_measure_prodMk_left hT
  have iSup_volume_sliceFst_ne_top {d : ℕ} {T : Set (ℝ × (Fin d → ℝ))} (hT : IsCompact T) : (⨆ τ, volume (sliceFst (Fin d → ℝ) T τ)) ≠ ⊤ := by
    have hb : ∀ τ, volume (sliceFst (Fin d → ℝ) T τ) ≤ volume (Prod.snd '' T) := fun τ =>
      measure_mono fun y hy => ⟨(τ, y), hy, rfl⟩
    exact (lt_of_le_of_lt (iSup_le hb) (hT.image continuous_snd).measure_lt_top).ne
  have sliceFst_combo_subset {d : ℕ} {t : ℝ} (A B : Set (ℝ × (Fin d → ℝ))) (τ σ : ℝ) :
      (1 - t) • sliceFst (Fin d → ℝ) A τ + t • sliceFst (Fin d → ℝ) B σ ⊆ sliceFst (Fin d → ℝ) ((1 - t) • A + t • B) ((1 - t) * τ + t * σ) := by
    rintro z hz
    obtain ⟨a', ha', b', hb', rfl⟩ := Set.mem_add.mp hz
    obtain ⟨y₁, hy₁, rfl⟩ := Set.mem_smul_set.mp ha'
    obtain ⟨y₂, hy₂, rfl⟩ := Set.mem_smul_set.mp hb'
    show ((1 - t) * τ + t * σ, (1 - t) • y₁ + t • y₂) ∈ (1 - t) • A + t • B
    refine Set.mem_add.mpr ⟨(1 - t) • ((τ, y₁) : ℝ × (Fin d → ℝ)),
      Set.smul_mem_smul_set hy₁, t • ((σ, y₂) : ℝ × (Fin d → ℝ)),
      Set.smul_mem_smul_set hy₂, ?_⟩
    simp [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  have bm_mult_step : ∀ {d : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
      (ih : ∀ {A B : Set (Fin d → ℝ)}, IsCompact A → IsCompact B → A.Nonempty → B.Nonempty →
        volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B))
      {A B : Set (ℝ × (Fin d → ℝ))} (hA : IsCompact A) (hB : IsCompact B)
      (hAne : A.Nonempty) (hBne : B.Nonempty),
      volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B) := by
    intro d t ht0 ht1 ih A B hA hB hAne hBne
    have ht1' : (0 : ℝ) < 1 - t := by linarith
    set S : Set (ℝ × (Fin d → ℝ)) := (1 - t) • A + t • B with hSdef
    have hScpt : IsCompact S := (hA.smul _).add (hB.smul _)
    set F : ℝ → ℝ≥0∞ := fun τ => volume (sliceFst (Fin d → ℝ) A τ) with hFdef
    set G : ℝ → ℝ≥0∞ := fun σ => volume (sliceFst (Fin d → ℝ) B σ) with hGdef
    set H : ℝ → ℝ≥0∞ := fun ζ => volume (sliceFst (Fin d → ℝ) S ζ) with hHdef
    have hFm : Measurable F := measurable_volume_sliceFst hA.measurableSet
    have hGm : Measurable G := measurable_volume_sliceFst hB.measurableSet
    have hHm : Measurable H := measurable_volume_sliceFst hScpt.measurableSet
    have hvolA : volume A = ∫⁻ τ, F τ := volume_eq_lintegral_sliceFst hA.measurableSet
    have hvolB : volume B = ∫⁻ σ, G σ := volume_eq_lintegral_sliceFst hB.measurableSet
    have hvolS : volume S = ∫⁻ ζ, H ζ := volume_eq_lintegral_sliceFst hScpt.measurableSet
    set MF : ℝ≥0∞ := ⨆ τ, F τ with hMFdef
    set MG : ℝ≥0∞ := ⨆ σ, G σ with hMGdef
    have hMFtop : MF ≠ ⊤ := iSup_volume_sliceFst_ne_top hA
    have hMGtop : MG ≠ ⊤ := iSup_volume_sliceFst_ne_top hB
    rcases eq_or_ne MF 0 with hMF0 | hMF0
    · have hF0 : ∀ τ, F τ = 0 := fun τ => le_antisymm (hMF0 ▸ le_iSup F τ) bot_le
      have hA0 : volume A = 0 := by rw [hvolA]; simp [hF0]
      rw [hA0, ENNReal.zero_rpow_of_pos ht1', zero_mul]
      exact bot_le
    rcases eq_or_ne MG 0 with hMG0 | hMG0
    · have hG0 : ∀ σ, G σ = 0 := fun σ => le_antisymm (hMG0 ▸ le_iSup G σ) bot_le
      have hB0 : volume B = 0 := by rw [hvolB]; simp [hG0]
      rw [hB0, ENNReal.zero_rpow_of_pos ht0, mul_zero]
      exact bot_le
    set F' : ℝ → ℝ≥0∞ := fun τ => F τ * MF⁻¹ with hF'def
    set G' : ℝ → ℝ≥0∞ := fun σ => G σ * MG⁻¹ with hG'def
    set D : ℝ≥0∞ := MF ^ (1 - t) * MG ^ t with hDdef
    have hMFrpow0 : MF ^ (1 - t) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hMF0) hMFtop).ne'
    have hMFrpowtop : MF ^ (1 - t) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht1'.le hMFtop
    have hMGrpow0 : MG ^ t ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hMG0) hMGtop).ne'
    have hMGrpowtop : MG ^ t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht0.le hMGtop
    have hD0 : D ≠ 0 := mul_ne_zero hMFrpow0 hMGrpow0
    have hDtop : D ≠ ⊤ := ENNReal.mul_ne_top hMFrpowtop hMGrpowtop
    have hDinv_eq : D⁻¹ = (MF⁻¹) ^ (1 - t) * (MG⁻¹) ^ t := by
      rw [hDdef, ENNReal.mul_inv (Or.inl hMFrpow0) (Or.inl hMFrpowtop), ← ENNReal.inv_rpow, ← ENNReal.inv_rpow]
    have collapse : ∀ X Y : ℝ≥0∞, (X * MF⁻¹) ^ (1 - t) * (Y * MG⁻¹) ^ t = X ^ (1 - t) * Y ^ t * D⁻¹ := by
      intro X Y
      rw [ENNReal.mul_rpow_of_nonneg _ _ ht1'.le, ENNReal.mul_rpow_of_nonneg _ _ ht0.le, hDinv_eq]
      ring
    have hF'1 : ∀ τ, F' τ ≤ 1 := by
      intro τ
      calc F τ * MF⁻¹ ≤ MF * MF⁻¹ := mul_le_mul_left (le_iSup F τ) _
        _ = 1 := ENNReal.mul_inv_cancel hMF0 hMFtop
    have hG'1 : ∀ σ, G' σ ≤ 1 := by
      intro σ
      calc G σ * MG⁻¹ ≤ MG * MG⁻¹ := mul_le_mul_left (le_iSup G σ) _
        _ = 1 := ENNReal.mul_inv_cancel hMG0 hMGtop
    have hF's : 1 ≤ ⨆ τ, F' τ := by
      have h : (⨆ τ, F τ * MF⁻¹) = MF * MF⁻¹ := by rw [← ENNReal.iSup_mul]
      rw [hF'def] at *; rw [h, ENNReal.mul_inv_cancel hMF0 hMFtop]
    have hG's : 1 ≤ ⨆ σ, G' σ := by
      have h : (⨆ σ, G σ * MG⁻¹) = MG * MG⁻¹ := by rw [← ENNReal.iSup_mul]
      rw [hG'def] at *; rw [h, ENNReal.mul_inv_cancel hMG0 hMGtop]
    have hyp' : ∀ τ σ, F' τ ^ (1 - t) * G' σ ^ t ≤ H ((1 - t) * τ + t * σ) * D⁻¹ := by
      intro τ σ
      rw [collapse]
      refine mul_le_mul_left ?_ D⁻¹
      rcases eq_or_ne (F τ) 0 with hFτ | hFτ
      · rw [hFτ, ENNReal.zero_rpow_of_pos ht1', zero_mul]; exact bot_le
      rcases eq_or_ne (G σ) 0 with hGσ | hGσ
      · rw [hGσ, ENNReal.zero_rpow_of_pos ht0, mul_zero]; exact bot_le
      have hAne' : (sliceFst (Fin d → ℝ) A τ).Nonempty := nonempty_of_measure_ne_zero hFτ
      have hBne' : (sliceFst (Fin d → ℝ) B σ).Nonempty := nonempty_of_measure_ne_zero hGσ
      calc F τ ^ (1 - t) * G σ ^ t
          ≤ volume ((1 - t) • sliceFst (Fin d → ℝ) A τ + t • sliceFst (Fin d → ℝ) B σ) :=
            ih (isCompact_sliceFst hA τ) (isCompact_sliceFst hB σ) hAne' hBne'
        _ ≤ H ((1 - t) * τ + t * σ) := measure_mono (sliceFst_combo_subset A B τ σ)
    have hpl := pl_dim_one ht0 ht1 (hFm.mul_const _) (hGm.mul_const _) (hHm.mul_const _) hF'1 hG'1 hF's hG's hyp'
    have hIF : (∫⁻ τ, F' τ) = (∫⁻ τ, F τ) * MF⁻¹ := lintegral_mul_const _ hFm
    have hIG : (∫⁻ σ, G' σ) = (∫⁻ σ, G σ) * MG⁻¹ := lintegral_mul_const _ hGm
    have hIH : (∫⁻ ζ, H ζ * D⁻¹) = (∫⁻ ζ, H ζ) * D⁻¹ := lintegral_mul_const _ hHm
    rw [hIF, hIG, hIH, collapse] at hpl
    have hfinal : (∫⁻ τ, F τ) ^ (1 - t) * (∫⁻ σ, G σ) ^ t ≤ ∫⁻ ζ, H ζ := by
      have h1 := mul_le_mul_left hpl D
      have key : ∀ x : ℝ≥0∞, x * D⁻¹ * D = x := fun x => by
        rw [mul_assoc, mul_comm D⁻¹ D, ENNReal.mul_inv_cancel hD0 hDtop, mul_one]
      rw [key, key] at h1
      exact h1
    rw [hvolA, hvolB, hvolS]
    exact hfinal
  intro d
  induction d with
  | zero =>
    intro t ht0 ht1 A B hA hB hAne hBne
    haveI : Subsingleton (Fin 0 → ℝ) := ⟨fun f g => funext fun i => i.elim0⟩
    have huniv : ∀ {S : Set (Fin 0 → ℝ)}, S.Nonempty → S = Set.univ := by
      intro S hS
      ext x
      simp only [Set.mem_univ, iff_true]
      obtain ⟨s, hs⟩ := hS
      rwa [Subsingleton.elim x s]
    have hSne : ((1 - t) • A + t • B).Nonempty := by
      obtain ⟨a, ha⟩ := hAne
      obtain ⟨b, hb⟩ := hBne
      exact ⟨(1 - t) • a + t • b, Set.mem_add.mpr
        ⟨_, Set.smul_mem_smul_set ha, _, Set.smul_mem_smul_set hb, rfl⟩⟩
    have huniv_S : (1 - t) • (Set.univ : Set (Fin 0 → ℝ)) + t • (Set.univ : Set (Fin 0 → ℝ)) = Set.univ := by
      have huniv_eq : (Set.univ : Set (Fin 0 → ℝ)) = {(0 : Fin 0 → ℝ)} := by
        ext x; simp [Subsingleton.elim x 0]
      have hsmul : ∀ c : ℝ, c • (Set.univ : Set (Fin 0 → ℝ)) = Set.univ := fun c => by
        rw [huniv_eq]
        simp [Set.smul_set_singleton]
      rw [hsmul (1 - t), hsmul t]
      rw [huniv_eq]
      ext x
      simp [Set.mem_singleton_iff]
    rw [huniv hAne]
    rw [huniv hBne]
    rw [huniv_S]
    set v : ℝ≥0∞ := volume (Set.univ : Set (Fin 0 → ℝ)) with hv
    by_cases hv0 : v = 0
    · rw [hv0, ENNReal.zero_rpow_of_pos (by linarith), zero_mul]
    by_cases hvt : v = ⊤
    · rw [hvt, ENNReal.top_rpow_of_pos (by linarith),
        ENNReal.top_rpow_of_pos ht0, ENNReal.top_mul_top]
    · calc v ^ (1 - t) * v ^ t
        = v ^ ((1 - t) + t) := (ENNReal.rpow_add _ _ hv0 hvt).symm
      _ = v ^ (1 : ℝ) := by norm_num
      _ = v := by rw [ENNReal.rpow_one v]
      _ ≤ v := le_refl v
  | succ d ihd =>
    intro t ht0 ht1 A B hA hB hAne hBne
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with hedef
    have hmp : MeasurePreserving e volume volume :=
      MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    have he_apply : ∀ f : Fin (d + 1) → ℝ, e f = (f 0, fun j => f ((0 : Fin (d + 1)).succAbove j)) := by
      intro f; rfl
    have he_add : ∀ f g : Fin (d + 1) → ℝ, e (f + g) = e f + e g := by
      intro f g; rw [he_apply, he_apply, he_apply]; exact Prod.ext (by simp) (by funext j; simp)
    have he_smul : ∀ (c : ℝ) (f : Fin (d + 1) → ℝ), e (c • f) = c • e f := by
      intro c f; rw [he_apply, he_apply]; exact Prod.ext (by simp) (by funext j; simp)
    have he_cont : Continuous ⇑e := by
      have h : ⇑e = fun f : Fin (d + 1) → ℝ => ((f 0, fun j => f ((0 : Fin (d + 1)).succAbove j)) : ℝ × (Fin d → ℝ)) := funext he_apply
      rw [h]; exact (continuous_apply 0).prodMk (continuous_pi fun j => continuous_apply _)
    have hvol_img : ∀ {S : Set (Fin (d + 1) → ℝ)}, MeasurableSet S → volume (e '' S) = volume S := by
      intro S hS
      simp [Set.image_eq_preimage_of_inverse e.symm_apply_apply e.apply_symm_apply]
      exact (MeasurePreserving.symm e hmp).measure_preimage hS.nullMeasurableSet
    have himg_combo : e '' ((1 - t) • A + t • B) = (1 - t) • (e '' A) + t • (e '' B) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨a', ha', b', hb', rfl⟩ := Set.mem_add.mp hw
        obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.mp ha'
        obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.mp hb'
        rw [he_add, he_smul, he_smul]
        exact Set.mem_add.mpr ⟨_, Set.smul_mem_smul_set ⟨a, ha, rfl⟩, _, Set.smul_mem_smul_set ⟨b, hb, rfl⟩, rfl⟩
      · rintro hz
        obtain ⟨a', ha', b', hb', rfl⟩ := Set.mem_add.mp hz
        obtain ⟨ya, hya, rfl⟩ := Set.mem_smul_set.mp ha'
        obtain ⟨a, ha, rfl⟩ := hya
        obtain ⟨yb, hyb, rfl⟩ := Set.mem_smul_set.mp hb'
        obtain ⟨b, hb, rfl⟩ := hyb
        exact ⟨(1 - t) • a + t • b, Set.mem_add.mpr
          ⟨_, Set.smul_mem_smul_set ha, _, Set.smul_mem_smul_set hb, rfl⟩,
          by rw [he_add, he_smul, he_smul]⟩
    have h1 : volume ((1 - t) • A + t • B) = volume ((1 - t) • (e '' A) + t • (e '' B)) := by
      rw [← himg_combo, hvol_img ((hA.smul _).add (hB.smul _)).measurableSet]
    have h2 : volume A = volume (e '' A) := (hvol_img hA.measurableSet).symm
    have h3 : volume B = volume (e '' B) := (hvol_img hB.measurableSet).symm
    rw [h1, h2, h3]
    exact bm_mult_step ht0 ht1 (fun hA' hB' hne1 hne2 => ihd ht0 ht1 hA' hB' hne1 hne2)
      (hA.image he_cont) (hB.image he_cont) (hAne.image _) (hBne.image _)

end CentroidAlignment

namespace CentroidAlignment

theorem bm_mult_euclidean {n : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {A B : Set (EuclideanSpace ℝ (Fin n))} (hA : IsCompact A)
    (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B) := by
  set e := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm with hedef
  have hmp : MeasurePreserving e volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  -- The underlying function is the `WithLp` identity, so additivity and
  -- homogeneity are definitional.
  have he_add : ∀ f g : EuclideanSpace ℝ (Fin n), e (f + g) = e f + e g := by
    intro f g; rfl
    -- NAME-RISK: if not `rfl`, use `WithLp.equiv_add`-style simp lemmas
    -- (`EuclideanSpace.measurableEquiv` is `WithLp.equiv 2 _` underneath).
  have he_smul : ∀ (c : ℝ) (f : EuclideanSpace ℝ (Fin n)),
      e (c • f) = c • e f := by
    intro c f; rfl
    -- NAME-RISK: fallback `WithLp.equiv_smul`.
  have he_cont : Continuous ⇑e := by
    exact PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)
    -- NAME-RISK: `PiLp.continuous_equiv (p) (α) :
    --   Continuous (WithLp.equiv p (∀ i, α i))`; if the coercion does not
    -- match syntactically, insert `show Continuous ⇑(WithLp.equiv 2 _)`.
  have hvol_img : ∀ {S : Set (EuclideanSpace ℝ (Fin n))}, MeasurableSet S →
      volume (e '' S) = volume S := by
    intro S hS
    rw [MeasurableEquiv.image_eq_preimage_symm]
    exact (MeasurePreserving.symm e hmp).measure_preimage hS.nullMeasurableSet
  have himg_combo : e '' ((1 - t) • A + t • B)
      = (1 - t) • (e '' A) + t • (e '' B) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨a', ha', b', hb', rfl⟩ := Set.mem_add.mp hw
      obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.mp ha'
      obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.mp hb'
      rw [he_add, he_smul, he_smul]
      exact Set.mem_add.mpr ⟨_, Set.smul_mem_smul_set ⟨a, ha, rfl⟩, _,
        Set.smul_mem_smul_set ⟨b, hb, rfl⟩, rfl⟩
    · rintro hz
      obtain ⟨a', ha', b', hb', rfl⟩ := Set.mem_add.mp hz
      obtain ⟨ya, hya, rfl⟩ := Set.mem_smul_set.mp ha'
      obtain ⟨a, ha, rfl⟩ := hya
      obtain ⟨yb, hyb, rfl⟩ := Set.mem_smul_set.mp hb'
      obtain ⟨b, hb, rfl⟩ := hyb
      exact ⟨(1 - t) • a + t • b, Set.mem_add.mpr
        ⟨_, Set.smul_mem_smul_set ha, _, Set.smul_mem_smul_set hb, rfl⟩,
        by rw [he_add, he_smul, he_smul]⟩
  have h1 : volume ((1 - t) • A + t • B)
      = volume ((1 - t) • (e '' A) + t • (e '' B)) := by
    rw [← himg_combo, hvol_img ((hA.smul _).add (hB.smul _)).measurableSet]
  have h2 : volume A = volume (e '' A) := (hvol_img hA.measurableSet).symm
  have h3 : volume B = volume (e '' B) := (hvol_img hB.measurableSet).symm
  rw [h1, h2, h3]
  exact bm_mult_pi n ht0 ht1 (hA.image he_cont) (hB.image he_cont)
    (hAne.image _) (hBne.image _)

/-- Additive Brunn–Minkowski on `EuclideanSpace`, all compact nonempty
sets. -/
theorem bm_add {n : ℕ} (hn : 1 ≤ n) {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A) (hB : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume A ^ ((n : ℝ)⁻¹) + volume B ^ ((n : ℝ)⁻¹)
      ≤ volume (A + B) ^ ((n : ℝ)⁻¹) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rcases eq_or_ne (volume A) 0 with hvA | hvA
  · obtain ⟨a, ha⟩ := hAne
    have hle : volume B ≤ volume (A + B) := by
      calc volume B = volume (a +ᵥ B) := (measure_vadd volume a B).symm
        -- NAME-RISK: `measure_vadd` argument order as in the compiled main
        -- file (`measure_vadd volume v K`).
        _ ≤ volume (A + B) := measure_mono (by
            rintro x ⟨b, hb, rfl⟩
            exact Set.mem_add.mpr ⟨a, ha, b, hb, rfl⟩)
    rw [hvA, ENNReal.zero_rpow_of_pos (by positivity), zero_add]
    exact ENNReal.rpow_le_rpow hle (by positivity)
  rcases eq_or_ne (volume B) 0 with hvB | hvB
  · obtain ⟨b, hb⟩ := hBne
    have hle : volume A ≤ volume (A + B) := by
      calc volume A = volume (b +ᵥ A) := (measure_vadd volume b A).symm
        _ ≤ volume (A + B) := measure_mono (by
            rintro x ⟨a, ha, rfl⟩
            exact Set.mem_add.mpr ⟨a, ha, b, hb, add_comm a b⟩)
    rw [hvB, ENNReal.zero_rpow_of_pos (by positivity), add_zero]
    exact ENNReal.rpow_le_rpow hle (by positivity)
  have hvAtop : volume A ≠ ⊤ := hA.measure_lt_top.ne
  have hvBtop : volume B ≠ ⊤ := hB.measure_lt_top.ne
  set a : ℝ := (volume A).toReal with hadef
  set b : ℝ := (volume B).toReal with hbdef
  have ha0 : 0 < a := ENNReal.toReal_pos hvA hvAtop
  have hb0 : 0 < b := ENNReal.toReal_pos hvB hvBtop
  set α : ℝ := a ^ ((n : ℝ)⁻¹) with hαdef
  set β : ℝ := b ^ ((n : ℝ)⁻¹) with hβdef
  have hα0 : 0 < α := Real.rpow_pos_of_pos ha0 _
  have hβ0 : 0 < β := Real.rpow_pos_of_pos hb0 _
  have hαn : α ^ n = a := by
    rw [hαdef, ← Real.rpow_natCast (a ^ ((n : ℝ)⁻¹)) n,
      ← Real.rpow_mul ha0.le, inv_mul_cancel₀ hnR.ne', Real.rpow_one]
    -- NAME-RISK: `Real.rpow_mul (hx : 0 ≤ x) : x ^ (y * z) = (x ^ y) ^ z`
    -- (orientation of the rewrite may need `.symm`).
  have hβn : β ^ n = b := by
    rw [hβdef, ← Real.rpow_natCast (b ^ ((n : ℝ)⁻¹)) n,
      ← Real.rpow_mul hb0.le, inv_mul_cancel₀ hnR.ne', Real.rpow_one]
  set t : ℝ := β / (α + β) with htdef
  have ht0 : 0 < t := div_pos hβ0 (by positivity)
  have ht1 : t < 1 := by
    rw [htdef, div_lt_one (by positivity)]
    linarith
  have h1t : 1 - t = α / (α + β) := by
    rw [htdef]
    field_simp
    ring
  have h1t0 : (0 : ℝ) < 1 - t := by linarith
  have hAeq : (1 - t) • ((1 - t)⁻¹ • A) = A := by
    rw [smul_smul, mul_inv_cancel₀ h1t0.ne', one_smul]
  have hBeq : t • (t⁻¹ • B) = B := by
    rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  have hAv : volume A = ENNReal.ofReal (α ^ n) := by
    rw [hαn, hadef, ENNReal.ofReal_toReal hvAtop]
  have hBv : volume B = ENNReal.ofReal (β ^ n) := by
    rw [hβn, hbdef, ENNReal.ofReal_toReal hvBtop]
  have hscaleA : volume ((1 - t)⁻¹ • A) = ENNReal.ofReal ((α + β) ^ n) := by
    rw [Measure.addHaar_smul volume, finrank_euclideanSpace, Fintype.card_fin]
    have habs : |(1 - t)⁻¹| = (α + β) / α := by
      rw [abs_of_pos (inv_pos.mpr h1t0), h1t, inv_div]
    rw [abs_pow, habs, hAv, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hα0.ne')]
  have hscaleB : volume (t⁻¹ • B) = ENNReal.ofReal ((α + β) ^ n) := by
    rw [Measure.addHaar_smul volume, finrank_euclideanSpace, Fintype.card_fin]
    have habs : |t⁻¹| = (α + β) / β := by
      rw [abs_of_pos (inv_pos.mpr ht0), htdef, inv_div]
    rw [abs_pow, habs, hBv, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hβ0.ne')]
  have hbm := bm_mult_euclidean ht0 ht1 (hA.smul (1 - t)⁻¹) (hB.smul t⁻¹)
    (hAne.smul_set) (hBne.smul_set)
  rw [hAeq, hBeq, hscaleA, hscaleB] at hbm
  have hX0 : ENNReal.ofReal ((α + β) ^ n) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hcollapse : ENNReal.ofReal ((α + β) ^ n) ^ (1 - t)
      * ENNReal.ofReal ((α + β) ^ n) ^ t = ENNReal.ofReal ((α + β) ^ n) := by
    rw [← ENNReal.rpow_add _ _ hX0 ENNReal.ofReal_ne_top]
    norm_num
  rw [hcollapse] at hbm
  have hmono := ENNReal.rpow_le_rpow hbm
    (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
  have hL : (ENNReal.ofReal ((α + β) ^ n)) ^ ((n : ℝ)⁻¹)
      = ENNReal.ofReal (α + β) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast (α + β) n, ← Real.rpow_mul (by positivity),
      mul_inv_cancel₀ hnR.ne', Real.rpow_one]
  have hAterm : volume A ^ ((n : ℝ)⁻¹) = ENNReal.ofReal α := by
    rw [show volume A = ENNReal.ofReal a from
      (ENNReal.ofReal_toReal hvAtop).symm,
      ENNReal.ofReal_rpow_of_nonneg ha0.le (by positivity)]
  have hBterm : volume B ^ ((n : ℝ)⁻¹) = ENNReal.ofReal β := by
    rw [show volume B = ENNReal.ofReal b from
      (ENNReal.ofReal_toReal hvBtop).symm,
      ENNReal.ofReal_rpow_of_nonneg hb0.le (by positivity)]
  calc volume A ^ ((n : ℝ)⁻¹) + volume B ^ ((n : ℝ)⁻¹)
      = ENNReal.ofReal α + ENNReal.ofReal β := by rw [hAterm, hBterm]
    _ = ENNReal.ofReal (α + β) := (ENNReal.ofReal_add hα0.le hβ0.le).symm
    _ = (ENNReal.ofReal ((α + β) ^ n)) ^ ((n : ℝ)⁻¹) := hL.symm
    _ ≤ volume (A + B) ^ ((n : ℝ)⁻¹) := hmono

end CentroidAlignment
