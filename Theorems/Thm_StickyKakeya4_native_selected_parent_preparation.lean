import Theorems.Thm_StickyKakeya4_native_parent_refinement

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace NativeSelectedParentPreparation

open NativeOriginalParentAssembly NativeParentRefinement NativeDyadicTubeStopping NativeDyadicTubeEpoch NativeParentSpines
open NativeAngularChartSelection ActualTubeFootprintProfiles DisjointProfileEpochs
open NativeFractionalReferenceComposition
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

noncomputable section
attribute [local instance] Classical.propDecidable

def epochCost (A : Finset Plane) (N : ℕ) : ℕ :=
  4 * (Fintype.card (Index N) * rank 2 A.card)

def angularCost (lo hi m : ℕ) : ℕ := angularBudget (angularResolution (hi - lo) m) m

def sourceMassCost (A : Finset Plane) (N m Q L lo hi : ℕ) (K t : ℝ) : ℝ :=
  (epochCost A N : ℝ) * (refinementCost (m + 1) L : ℝ) * (Q : ℝ) ^ 2 * spatialConstant K t * K *
    ((Q : ℝ) ^ 2 * (Q : ℝ) ^ 2 * (angularCost lo hi m : ℝ))

/-- Constructed data on ORIGINAL source labels. The per-parent output uses
physical chart coordinates, with an injective chart map and unchanged original
cardinality. It is produced from original AD, never assumed at the caller. -/
structure Selection (A : Finset Plane) {δ ε K t : ℝ} {Nold : ℕ} {E₀ : Finset A}
    (D : StoppedProfile (position A) δ ε K t Nold E₀)
    (j : Fin 2) (m Q₁ L₁ Q₂ L₂ Hwork : ℕ) where
  index : ℕ
  index_lt : index < m
  points : Finset A
  nonempty : points.Nonempty
  subset : points ⊆ E₀
  angle : GridLabel 1 → ℝ
  angle_bound : ∀ c, |angle c| ≤ 1
  retained : A.card ≤
    (epochCost A Nold * refinementCost (m + 1) L₁ * Q₁ ^ 2 * Q₁ ^ 2 * angularCost D.pair.1 D.pair.2 m) * points.card
  parent_mass : ∀ c, (parent A points (scale δ (workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (index + 1))) c).Nonempty →
    (scale δ (workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (index + 1)) / δ) ^ t ≤
      sourceMassCost A Nold m Q₁ L₁ D.pair.1 D.pair.2 K t *
        ((parent A points (scale δ (workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (index + 1))) c).card : ℝ)
  refined : ∀ c, (parent A points (scale δ (workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (index + 1))) c).Nonempty →
    let i := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m index
    let k := workingLevel D.pair.1 (D.pair.2 - D.pair.1) m (index + 1)
    Nonempty (RefinedParent ((parent A points (scale δ k) c).image (chartPosition A j))
      (scale δ i / 64) (angle c) (ActualScalarADProfiles.workingRadii (k - i + 6) Hwork)
      (2 ^ (k - i + 6)) Q₂ L₂ δ K t D.exponent D.loss
      (spineConstant Nold (m + 1) Q₁ L₁ K t D.loss))

/-- Original AD constructs the stopped epoch, a genuine maximizing-coordinate
chart, an actual adjacent angular scale pair, and separated fractional outputs
in EVERY surviving parent. Every profile query and spine is derived internally. -/
theorem exists_original_AD_selection (A : Finset Plane) (δ ε K t : ℝ) (Nold m Q₁ L₁ Q₂ L₂ Hwork : ℕ)
    (hne : A.Nonempty) (hδ : 0 < δ) (hN : 0 < Nold) (htop : scale δ Nold ≤ 1 / 64)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hlarge : 4 * (Real.log 72 / Real.log 2) < ε ^ CoverProfileStopping.stepBudget ε * (Nold : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t)
    (hm : 0 < m) (hQ₁ : 4 ≤ Q₁) (hheight₁ : A.card ≤ Q₁ ^ L₁)
    (hQ₂ : 4 ≤ Q₂) (hheight₂ : A.card ≤ Q₂ ^ L₂) (hHwork : 0 < Hwork) :
    ∃ e : Epoch A (Index Nold), ∃ D : StoppedProfile (position A) δ ε K t Nold e.start,
      D.pair = e.index.val ∧ ∃ j : Fin 2, Nonempty (Selection A D j m Q₁ L₁ Q₂ L₂ Hwork) := by
  classical
  obtain ⟨e, D, hD, T, j, Fs, _hFs, _hdisj, hret, hT, hcore⟩ :=
    exists_native_chart_parent_preparation A δ ε K t Nold hne hδ hN (htop.trans (by norm_num))
      hε hεhalf hK ht ht2 hlarge hdiam hAD
  let M := D.pair.2 - D.pair.1
  let levels := workingLevel D.pair.1 M m
  let n := angularResolution M m
  let Bang := angularBudget n m
  have hn : 0 < n := angularResolution_pos M m
  have hlevels : ∀ k : Fin (m + 1), D.pair.1 ≤ levels k ∧ levels k ≤ D.pair.2 :=
    fun k => workingLevel_bounds _ _ _ _ D.valid.1 hm (by omega)
  obtain ⟨B⟩ := hcore m Q₁ L₁ n hQ₁ hheight₁ (fun k => levels k) hlevels
  obtain ⟨i, hi, Ω, hΩ, hΩne, angle, hangle, hlocal, hglobal, _hparents, _hwhole, hwitness⟩ :=
    select_parent_core_angles A Fs D T j (fun F hF => (hT F hF).2.1)
      (fun F hF => (hT F hF).2.2) hm hn (angularBudget_power n hm) levels
      (fun k _hk => workingLevel_mono _ _ _ (Nat.le_succ k)) B
  have hB₀ : B.points ⊆ e.start := by
    intro q hq
    obtain ⟨F, hF, hqF⟩ := (mem_support Fs q).mp (B.subset hq)
    exact (hT F hF).1 hqF
  have hcost : 0 < (refinementCost (m + 1) L₁ : ℝ) := by unfold refinementCost; positivity
  have hQpos : (0 : ℝ) < Q₁ := by exact_mod_cast (show 0 < Q₁ by omega)
  have hHpos := zero_lt_one.trans_le (D.loss_ge_one hδ hε.le hK ht)
  have hKpos := zero_lt_one.trans_le hK
  have hell : 0 < spineConstant Nold (m + 1) Q₁ L₁ K t D.loss := by
    unfold spineConstant
    exact div_pos (pruningRate_pos Nold hK) (by positivity)
  refine ⟨e, D, hD, j, ⟨{
    index := i
    index_lt := hi
    points := Ω
    nonempty := hΩne
    subset := hΩ.trans hB₀
    angle := angle
    angle_bound := hangle
    retained := ?_
    parent_mass := ?_
    refined := ?_
  }⟩⟩
  · have hb := Nat.mul_le_mul_left (epochCost A Nold) B.retained
    have ha := Nat.mul_le_mul_left (epochCost A Nold * refinementCost (m + 1) L₁) hglobal
    exact hret.trans (hb.trans (by simpa only [Nat.mul_assoc, angularCost, n, M] using ha))
  · intro c hc
    obtain ⟨q, hq⟩ := hc
    have hqΩ : q ∈ Ω := (Finset.mem_filter.mp hq).1
    have hqc : grid (position A) (scale δ (levels (i + 1))) q = c := (Finset.mem_filter.mp hq).2
    have hmass := B.parent_mass ⟨i + 1, by omega⟩ q (hΩ hqΩ)
    dsimp only at hmass
    rw [hqc] at hmass
    have hloc : ((parent A B.points (scale δ (levels (i + 1))) c).card : ℝ) ≤
        ((Q₁ : ℝ) ^ 2 * (Q₁ : ℝ) ^ 2 * (Bang : ℝ)) *
          ((parent A Ω (scale δ (levels (i + 1))) c).card : ℝ) := by exact_mod_cast hlocal c
    have hcoeff : 0 ≤ (epochCost A Nold : ℝ) * (refinementCost (m + 1) L₁ : ℝ) *
        (Q₁ : ℝ) ^ 2 * spatialConstant K t * K := by
      have hsp := (spatialConstant_pos (t := t) hK).le
      positivity
    have hh := hmass.trans (mul_le_mul_of_nonneg_left hloc hcoeff)
    simpa only [sourceMassCost, epochCost, angularCost, Bang, n, M, mul_assoc] using hh
  · intro c hc
    exact refine_parent D Fs B.points Ω hΩ B.subset (fun F hF => (hT F hF).1)
      T j (fun F hF => (hT F hF).2.1) (levels i) (levels (i + 1))
      (hlevels ⟨i, by omega⟩).1 (workingLevel_mono _ _ _ (Nat.le_succ i)) (hlevels ⟨i + 1, by omega⟩).2
      angle hangle (1 / (n : ℝ)) _ (by positivity) hell (workingLevel_angle_scale hδ _ _ i hm)
      hwitness Q₂ L₂ Hwork hHwork hQ₂ hheight₂ hδ hε.le htop hK ht ht2 hdiam hAD c hc

end
end NativeSelectedParentPreparation
