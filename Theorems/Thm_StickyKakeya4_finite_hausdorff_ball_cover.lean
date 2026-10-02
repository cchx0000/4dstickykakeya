import Theorems.Thm_StickyKakeya4_wz_readback_bookkeeping

open scoped ENNReal NNReal Topology
open MeasureTheory

noncomputable section

namespace StickyKakeya4

/-- A positive summable error allowance permits a strict radius inflation
without charging any fixed positive amount to every covering set. -/
theorem exists_radius_inflation_with_rpow_cost
    {a rho q delta : ℝ} (ha : a < rho) (hq : 0 ≤ q) (hdelta : 0 < delta) :
    ∃ r : ℝ, a < r ∧ r < rho ∧ r ^ q < a ^ q + delta := by
  have hcost : ∀ᶠ r in nhds a, r ^ q < a ^ q + delta :=
    (Real.continuous_rpow_const hq).continuousAt.eventually
      (gt_mem_nhds (by linarith : a ^ q < a ^ q + delta))
  have hrho : ∀ᶠ r in nhds a, r < rho := gt_mem_nhds ha
  obtain ⟨l, u, hau, hsub⟩ := (hrho.and hcost).exists_Ioo_subset
  obtain ⟨r, har, hru⟩ := exists_between hau.2
  exact ⟨r, har, hsub ⟨hau.1.trans har, hru⟩⟩

/-- A compact set of Hausdorff dimension strictly below `q` has arbitrarily
fine finite open-ball covers whose *actual radii* have arbitrarily small
`q`-power sum. Individually summable inflation errors handle diameter-zero
pieces and make the cover open before compactness is used. -/
theorem exists_finite_radius_cost_ball_cover_of_compact_dimH_lt
    {X : Type*} [MetricSpace X] [Nonempty X]
    (s : Set X) (hs : IsCompact s)
    {q : NNReal} (hdim : dimH s < (q : ENNReal))
    {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ F : Finset ℕ, ∃ center : ℕ → X, ∃ radius : ℕ → ℝ,
      s ⊆ ⋃ n ∈ (F : Set ℕ), Metric.ball (center n) (radius n) ∧
      (∀ n, 0 < radius n ∧ radius n < rho) ∧
      (∑ n ∈ F, radius n ^ (q : ℝ)) < epsilon := by
  classical
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have hqposE : (0 : ENNReal) < q := bot_le.trans_lt hdim
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposE
  have hrhalf : 0 < rho / 2 := half_pos hrho
  have hehalf : 0 < epsilon / 2 := half_pos hepsilon
  obtain ⟨cover, hcover, hdiam, hcost⟩ :=
    exists_small_diameter_cover_of_dimH_lt s hdim
      (ENNReal.ofReal_pos.mpr hrhalf) (ENNReal.ofReal_pos.mpr hehalf)
  have hdiamtop (n : ℕ) : Metric.ediam (cover n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam n)
  have hdiamreal (n : ℕ) : (Metric.ediam (cover n)).toReal ≤ rho / 2 := by
    simpa only [ENNReal.toReal_ofReal hrhalf.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam n)
  have hcost' : (∑' n, (Metric.ediam (cover n)).rpow (q : ℝ)) <
      ENNReal.ofReal (epsilon / 2) := by
    convert hcost using 1
    congr 1
    funext n
    by_cases hn : (cover n).Nonempty
    · simp only [iSup_pos hn]
    · have he : cover n = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simp [he, ENNReal.zero_rpow_of_pos hqpos]
  obtain ⟨delta, hdeltapos, hdeltasum⟩ :=
    (Set.countable_univ : (Set.univ : Set ℕ).Countable).exists_pos_forall_sum_le
      (show 0 < epsilon / 4 by linarith)
  have hinflate (n : ℕ) : ∃ r : ℝ,
      (Metric.ediam (cover n)).toReal < r ∧ r < rho ∧
      r ^ (q : ℝ) < (Metric.ediam (cover n)).toReal ^ (q : ℝ) + delta n :=
    exists_radius_inflation_with_rpow_cost
      (lt_of_le_of_lt (hdiamreal n) (by linarith)) q.coe_nonneg (hdeltapos n)
  choose radius hradius using hinflate
  let center : ℕ → X := fun n =>
    if h : (cover n).Nonempty then h.choose else Classical.choice inferInstance
  have hcenter : ∀ n, (cover n).Nonempty → center n ∈ cover n := by
    intro n hn
    simp only [center, dif_pos hn]
    exact hn.choose_spec
  have hpiece : ∀ n, cover n ⊆ Metric.ball (center n) (radius n) := by
    intro n x hx
    have hed : edist x (center n) ≤ Metric.ediam (cover n) :=
      Metric.edist_le_ediam_of_mem hx (hcenter n ⟨x, hx⟩)
    have hdist : dist x (center n) ≤ (Metric.ediam (cover n)).toReal := by
      simpa [edist_dist] using ENNReal.toReal_mono (hdiamtop n) hed
    exact hdist.trans_lt (hradius n).1
  have hballs : s ⊆ ⋃ n, Metric.ball (center n) (radius n) := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨n, hpiece n hxn⟩
  obtain ⟨F, hF⟩ := hs.elim_finite_subcover
    (fun n => Metric.ball (center n) (radius n))
    (fun _ => Metric.isOpen_ball) hballs
  refine ⟨F, center, radius, hF, fun n =>
    ⟨lt_of_le_of_lt ENNReal.toReal_nonneg (hradius n).1, (hradius n).2.1⟩, ?_⟩
  have hfinitecostE : (∑ n ∈ F, (Metric.ediam (cover n)).rpow (q : ℝ)) <
      ENNReal.ofReal (epsilon / 2) :=
    (ENNReal.sum_le_tsum F).trans_lt hcost'
  have hfinitecost : (∑ n ∈ F, (Metric.ediam (cover n)).toReal ^ (q : ℝ)) <
      epsilon / 2 := by
    rw [← ENNReal.toReal_ofReal hehalf.le]
    have hfin : (∑ n ∈ F, (Metric.ediam (cover n)).rpow (q : ℝ)) ≠ ⊤ :=
      ne_top_of_lt hfinitecostE
    have h := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hfinitecostE
    simp only [ENNReal.rpow_eq_pow] at h
    rw [ENNReal.toReal_sum (s := F) (fun n _ => ENNReal.rpow_ne_top_of_nonneg
      q.coe_nonneg (hdiamtop n))] at h
    simpa only [← ENNReal.toReal_rpow] using h
  have hsum : (∑ n ∈ F, radius n ^ (q : ℝ)) ≤
      (∑ n ∈ F, (Metric.ediam (cover n)).toReal ^ (q : ℝ)) +
        ∑ n ∈ F, delta n := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun n _ => (hradius n).2.2.le
  have hdeltaF := hdeltasum F (Set.subset_univ _)
  linarith

/-- The same actual-radius-cost cover indexed by a standard finite type. -/
theorem exists_fin_radius_cost_ball_cover_of_compact_dimH_lt
    {X : Type*} [MetricSpace X] [Nonempty X]
    (s : Set X) (hs : IsCompact s)
    {q : NNReal} (hdim : dimH s < (q : ENNReal))
    {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ center : Fin N → X, ∃ radius : Fin N → ℝ,
      s ⊆ ⋃ n, Metric.ball (center n) (radius n) ∧
      (∀ n, 0 < radius n ∧ radius n < rho) ∧
      (∑ n, radius n ^ (q : ℝ)) < epsilon := by
  classical
  obtain ⟨F, center, radius, hcover, hradius, hcost⟩ :=
    exists_finite_radius_cost_ball_cover_of_compact_dimH_lt s hs hdim hrho hepsilon
  let e : Fin F.card ≃ F := F.equivFin.symm
  refine ⟨F.card, fun i => center (e i), fun i => radius (e i), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion.mp (hcover hx) |>.imp fun n => Set.mem_iUnion.mp
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨n, hn⟩, ?_⟩
    simpa using hxn
  · exact fun i => hradius (e i)
  · have heq : (∑ i : Fin F.card, radius (e i) ^ (q : ℝ)) =
        ∑ n ∈ F, radius n ^ (q : ℝ) := by
      exact (e.sum_comp (fun n : F => radius n ^ (q : ℝ))).trans
        (Finset.sum_coe_sort F (fun n => radius n ^ (q : ℝ)))
    exact heq.trans_lt hcost

end StickyKakeya4
