import Mathlib
import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace ADGridCoverMenus

open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators

noncomputable section

abbrev Point (d : ℕ) := Fin d → ℝ
abbrev GridLabel (d : ℕ) := Fin d → ℤ

def gridLabel {d : ℕ} (r : ℝ) (p : Point d) : GridLabel d := fun i => ⌊p i / r⌋

/-- A box in the ORIGINAL grid, centered at the center's original grid label. -/
def netBox {d : ℕ} (r : ℝ) (c : Point d) : Finset (GridLabel d) :=
  Fintype.piFinset fun i => Finset.Icc (⌊c i / r⌋ - 1) (⌊c i / r⌋ + 1)

lemma netBox_card {d : ℕ} (r : ℝ) (c : Point d) : (netBox r c).card = 3 ^ d := by
  have hcoord : ∀ i : Fin d, (Finset.Icc (⌊c i / r⌋ - 1) (⌊c i / r⌋ + 1)).card = 3 := by
    intro i
    have hcard : ((Finset.Icc (⌊c i / r⌋ - 1) (⌊c i / r⌋ + 1)).card : ℤ) = 3 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hcard
  simp [netBox, Fintype.card_piFinset, hcoord]

lemma gridLabel_mem_netBox {d : ℕ} {r : ℝ} (hr : 0 < r) {p c : Point d}
    (hpc : dist p c ≤ r) : gridLabel r p ∈ netBox r c := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hdist : |p i - c i| ≤ r := by
    simpa only [Real.dist_eq] using (dist_le_pi_dist p c i).trans hpc
  obtain ⟨hlow, hhigh⟩ := abs_le.mp hdist
  have hlower : c i / r - 1 ≤ p i / r := by
    have h := div_le_div_of_nonneg_right (show c i - r ≤ p i by linarith) hr.le
    simpa only [sub_div, div_self hr.ne'] using h
  have hupper : p i / r ≤ c i / r + 1 := by
    have h := div_le_div_of_nonneg_right (show p i ≤ c i + r by linarith) hr.le
    simpa only [add_div, div_self hr.ne'] using h
  apply Finset.mem_Icc.mpr
  constructor
  · simpa only [Int.floor_sub_one, gridLabel] using Int.floor_mono hlower
  · simpa only [Int.floor_add_one, gridLabel] using Int.floor_mono hupper

/-- The AD upper bound extends beyond radius one using the actual diameter
bound, rather than evaluating the local hypothesis outside its stated range. -/
lemma AD_upper_all_radii {X : Type*} [PseudoMetricSpace X]
    (P : Finset X) {ρ L t : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hL : 0 < L) (ht : 0 ≤ t)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ 1)
    (hAD : ADBounds P ρ L t) {c : X} (hc : c ∈ P)
    {R : ℝ} (hρR : ρ ≤ R) :
    ((carrierBall P c R).card : ℝ) ≤ L * (R / ρ) ^ t := by
  classical
  by_cases hR : R ≤ 1
  · exact (hAD c hc R hρR hR).2
  · have hRone : 1 ≤ R := le_of_lt (lt_of_not_ge hR)
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hRone
    have hglobal := global_scaled_card_le P ⟨c, hc⟩ hρone hdiam
      (scaled_bounds_of_ADBounds hρ hL hAD)
    have hsub : carrierBall P c R ⊆ P := by
      intro p hp
      exact ((mem_carrierBall P p c R).mp hp).1
    have hcard : ((carrierBall P c R).card : ℝ) ≤ (P.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hmass := (mul_le_mul_of_nonneg_left hcard (Real.rpow_pos_of_pos hρ t).le).trans hglobal
    have hpow : (1 : ℝ) ≤ R ^ t := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hRone ht
    rw [Real.div_rpow hRpos.le hρ.le, ← mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hρ t)).mpr
    nlinarith

lemma owner_mem_three_ball {X : Type*} [PseudoMetricSpace X]
    (P C : Finset X) (hC : C.Nonempty) {r τ : ℝ}
    (hcover : ∀ p ∈ P, ∃ c ∈ C, dist p c < r) (hrτ : r ≤ τ)
    {x p : X} (hx : x ∈ P) (hp : p ∈ carrierBall P x τ) :
    owner C hC p ∈ carrierBall C (owner C hC x) (3 * τ) := by
  obtain ⟨hpP, hpx⟩ := (mem_carrierBall P p x τ).mp hp
  have hpnear := owner_dist_lt P C hC hcover hpP
  have hxnear := owner_dist_lt P C hC hcover hx
  have htriangle : dist (owner C hC p) (owner C hC x) ≤
      dist p (owner C hC p) + dist p x + dist x (owner C hC x) := by
    calc
      dist (owner C hC p) (owner C hC x) ≤
          dist (owner C hC p) p + dist p (owner C hC x) := dist_triangle _ _ _
      _ ≤ dist (owner C hC p) p + (dist p x + dist x (owner C hC x)) :=
        add_le_add le_rfl (dist_triangle p x (owner C hC x))
      _ = _ := by rw [dist_comm (owner C hC p) p]; ring
  exact (mem_carrierBall C _ _ _).mpr ⟨owner_mem C hC p, by linarith⟩

/-- An actual fixed-grid menu is constructed from the original AD set and the
proved global Voronoi coarsening. No net size or occupied-cell count is assumed. -/
theorem exists_AD_grid_menu {d : ℕ} (A : Finset (Point d))
    {δ r τ K t : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hrτ : r ≤ τ) (hτ : τ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A δ K t) {x : Point d} (hx : x ∈ A) :
    ∃ menu : Finset (GridLabel d),
      (carrierBall A x τ).image (gridLabel r) ⊆ menu ∧
      (menu.card : ℝ) ≤ (3 : ℝ) ^ d * (18 : ℝ) ^ t * K ^ 2 * (τ / r) ^ t := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  have hτpos : 0 < τ := hr.trans_le hrτ
  have hrone : r ≤ 1 := hrτ.trans hτ
  obtain ⟨C, hC, hCA, hsep, hcover, hcoarse, _, _, _⟩ :=
    exists_AD_coarsening A ⟨x, hx⟩ hδ hδr hrone hK ht hdiam hAD
  let S := carrierBall C (owner C hC x) (3 * τ)
  let menu := S.biUnion (netBox r)
  have hmenu : (carrierBall A x τ).image (gridLabel r) ⊆ menu := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_biUnion.mpr
    refine ⟨owner C hC p, owner_mem_three_ball A C hC hcover hrτ hx hp, ?_⟩
    apply gridLabel_mem_netBox hr
    exact (owner_dist_lt A C hC hcover ((mem_carrierBall A p x τ).mp hp).1).le
  have hdiamC : ∀ p ∈ C, ∀ q ∈ C, dist p q ≤ 1 :=
    fun p hp q hq => hdiam p (hCA hp) q (hCA hq)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hcoarsepos : 0 < (6 : ℝ) ^ t * K ^ 2 :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) t) (sq_pos_of_pos hKpos)
  have hScard : (S.card : ℝ) ≤ ((6 : ℝ) ^ t * K ^ 2) * ((3 * τ) / r) ^ t :=
    AD_upper_all_radii C hr hrone hcoarsepos ht hdiamC hcoarse (owner_mem C hC x)
      (by linarith)
  have hmenuNat : menu.card ≤ S.card * 3 ^ d := by
    calc
      menu.card ≤ ∑ c ∈ S, (netBox r c).card := Finset.card_biUnion_le
      _ = _ := by simp [netBox_card]
  have hmenuR : (menu.card : ℝ) ≤ (S.card : ℝ) * (3 : ℝ) ^ d := by exact_mod_cast hmenuNat
  have hbound := mul_le_mul_of_nonneg_right hScard (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)
  have hratio : (3 * τ) / r = 3 * (τ / r) := by ring
  have hpowers : (18 : ℝ) ^ t = (6 : ℝ) ^ t * (3 : ℝ) ^ t := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  refine ⟨menu, hmenu, ?_⟩
  rw [hratio, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (div_nonneg hτpos.le hr.le)] at hbound
  rw [hpowers]
  nlinarith

/-- The covering number is the actual number of occupied ORIGINAL floor cells. -/
theorem occupied_grid_cells_le {d : ℕ} (A : Finset (Point d))
    {δ r τ K t : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hrτ : r ≤ τ) (hτ : τ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t)
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A δ K t) {x : Point d} (hx : x ∈ A) :
    (((carrierBall A x τ).image (gridLabel r)).card : ℝ) ≤
      (3 : ℝ) ^ d * (18 : ℝ) ^ t * K ^ 2 * (τ / r) ^ t := by
  obtain ⟨menu, hsub, hcard⟩ := exists_AD_grid_menu A hδ hδr hrτ hτ hK ht hdiam hAD hx
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcard

lemma dimensional_constant {d : ℕ} {t : ℝ} (htd : t ≤ (d : ℝ)) :
    (3 : ℝ) ^ d * (18 : ℝ) ^ t ≤ (9 : ℝ) ^ d * (6 : ℝ) ^ t := by
  have hthree : (3 : ℝ) ^ t ≤ (3 : ℝ) ^ d := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) htd
  have h18 : (18 : ℝ) ^ t = (3 : ℝ) ^ t * (6 : ℝ) ^ t := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  calc
    (3 : ℝ) ^ d * (18 : ℝ) ^ t = ((3 : ℝ) ^ d * (3 : ℝ) ^ t) * (6 : ℝ) ^ t := by
      rw [h18]
      ring
    _ ≤ ((3 : ℝ) ^ d * (3 : ℝ) ^ d) * (6 : ℝ) ^ t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hthree (by positivity))
        (Real.rpow_nonneg (by norm_num) t)
    _ = (9 : ℝ) ^ d * (6 : ℝ) ^ t := by rw [← mul_pow]; norm_num

/-- With t≤d, the constant has the desired form C_d·6^t K². -/
theorem exists_AD_grid_menu_dimensional {d : ℕ} (A : Finset (Point d))
    {δ r τ K t : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hrτ : r ≤ τ) (hτ : τ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (htd : t ≤ (d : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A δ K t) {x : Point d} (hx : x ∈ A) :
    ∃ menu : Finset (GridLabel d),
      (carrierBall A x τ).image (gridLabel r) ⊆ menu ∧
      (menu.card : ℝ) ≤ (9 : ℝ) ^ d * (6 : ℝ) ^ t * K ^ 2 * (τ / r) ^ t := by
  obtain ⟨menu, hsub, hcard⟩ := exists_AD_grid_menu A hδ hδr hrτ hτ hK ht hdiam hAD hx
  have hfactor : 0 ≤ K ^ 2 * (τ / r) ^ t :=
    mul_nonneg (sq_nonneg K) (Real.rpow_nonneg (div_nonneg (by linarith) (by linarith)) t)
  have hbound := mul_le_mul_of_nonneg_right (dimensional_constant htd) hfactor
  refine ⟨menu, hsub, ?_⟩
  nlinarith

/-- The entire original set has a fixed-grid menu and an actual cardinal lower
bound. These are the two quantitative inputs to the one-time pruning budget. -/
theorem exists_global_AD_grid_menu {d : ℕ} (A : Finset (Point d)) (hA : A.Nonempty)
    {δ r K t : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hr : r ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (htd : t ≤ (d : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A δ K t) :
    ∃ menu : Finset (GridLabel d), A.image (gridLabel r) ⊆ menu ∧
      (menu.card : ℝ) ≤ (9 : ℝ) ^ d * (6 : ℝ) ^ t * K ^ 2 * (1 / r) ^ t ∧
      (1 / δ) ^ t / K ≤ (A.card : ℝ) := by
  obtain ⟨x, hx⟩ := hA
  have hball : carrierBall A x 1 = A :=
    FiniteVoronoiADCoarsening.carrierBall_one_eq A hdiam hx
  obtain ⟨menu, hsub, hcard⟩ :=
    exists_AD_grid_menu_dimensional A hδ hδr hr le_rfl hK ht htd hdiam hAD hx
  rw [hball] at hsub
  have hlower := (hAD x hx 1 (hδr.trans hr) le_rfl).1
  rw [hball] at hlower
  exact ⟨menu, hsub, hcard, hlower⟩

/-- Every actual subset inside the parent ball inherits its fixed-grid count. -/
theorem subset_occupied_grid_cells_le {d : ℕ} (A E : Finset (Point d))
    {δ r τ K t : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hrτ : r ≤ τ) (hτ : τ ≤ 1)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (htd : t ≤ (d : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A δ K t) {x : Point d} (hx : x ∈ A)
    (hE : E ⊆ carrierBall A x τ) :
    ((E.image (gridLabel r)).card : ℝ) ≤
      (9 : ℝ) ^ d * (6 : ℝ) ^ t * K ^ 2 * (τ / r) ^ t := by
  obtain ⟨menu, hsub, hcard⟩ :=
    exists_AD_grid_menu_dimensional A hδ hδr hrτ hτ hK ht htd hdiam hAD hx
  exact (Nat.cast_le.mpr (Finset.card_le_card
    ((Finset.image_subset_image hE).trans hsub))).trans hcard

/-- Parent balls larger than one are handled by the global menu, so tube
constant enlargements do not require an AD assumption beyond the unit scale. -/
theorem subset_occupied_grid_cells_le_all_radii {d : ℕ} (A E : Finset (Point d))
    {δ r R K t : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hrone : r ≤ 1) (hrR : r ≤ R)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (htd : t ≤ (d : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A δ K t) {x : Point d} (hx : x ∈ A)
    (hE : E ⊆ carrierBall A x R) :
    ((E.image (gridLabel r)).card : ℝ) ≤
      (9 : ℝ) ^ d * (6 : ℝ) ^ t * K ^ 2 * (R / r) ^ t := by
  classical
  by_cases hR : R ≤ 1
  · exact subset_occupied_grid_cells_le A E hδ hδr hrR hR hK ht htd hdiam hAD hx hE
  · obtain ⟨menu, hmenu, hcard, _⟩ :=
      exists_global_AD_grid_menu A ⟨x, hx⟩ hδ hδr hrone hK ht htd hdiam hAD
    have hEA : E ⊆ A := by
      intro p hp
      exact ((mem_carrierBall A p x R).mp (hE hp)).1
    have hgrid : ((E.image (gridLabel r)).card : ℝ) ≤ (menu.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card ((Finset.image_subset_image hEA).trans hmenu))
    have hr : 0 < r := hδ.trans_le hδr
    have hratio : 1 / r ≤ R / r := div_le_div_of_nonneg_right (le_of_lt (lt_of_not_ge hR)) hr.le
    have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 / r) hratio ht
    have hfactor : 0 ≤ (9 : ℝ) ^ d * (6 : ℝ) ^ t * K ^ 2 := by positivity
    exact hgrid.trans (hcard.trans (mul_le_mul_of_nonneg_left hpow hfactor))

/-- Any actual subfamily of bounded diameter has the required AD cover-profile
bound. In particular a tube footprint can be used here once its elementary
diameter bound is established; no covering-number certificate is assumed. -/
theorem diameter_subset_occupied_grid_cells_le {d : ℕ} (A E : Finset (Point d))
    {δ r R K t : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hrone : r ≤ 1) (hrR : r ≤ R)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (htd : t ≤ (d : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A δ K t) (hEA : E ⊆ A)
    (hEdiam : ∀ p ∈ E, ∀ q ∈ E, dist p q ≤ R) :
    ((E.image (gridLabel r)).card : ℝ) ≤
      (9 : ℝ) ^ d * (6 : ℝ) ^ t * K ^ 2 * (R / r) ^ t := by
  classical
  by_cases hE : E.Nonempty
  · obtain ⟨x, hx⟩ := hE
    apply subset_occupied_grid_cells_le_all_radii A E hδ hδr hrone hrR hK ht htd hdiam hAD (hEA hx)
    intro p hp
    exact (mem_carrierBall A p x R).mpr ⟨hEA hp, hEdiam p hp x hx⟩
  · have hz : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    rw [hz, Finset.image_empty, Finset.card_empty, Nat.cast_zero]
    have hr : 0 < r := hδ.trans_le hδr
    have hR : 0 < R := hr.trans_le hrR
    positivity

/-- The actual finite maximum over tube footprints satisfies the AD exponent
bound. Every per-footprint count is derived from original metric AD and its
literal diameter; neither a maximizing footprint nor a count bound is assumed. -/
theorem finite_footprint_profile_AD_bound {d : ℕ}
    (A E : Finset (Point d)) (tubes : Finset (Finset (Point d)))
    {δ r R K t : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hrone : r ≤ 1) (hrR : r ≤ R)
    (hK : 1 ≤ K) (ht : 0 ≤ t) (htd : t ≤ (d : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1)
    (hAD : ADBounds A δ K t) (hEA : E ⊆ A)
    (hfootprint : ∀ W ∈ tubes, ∀ p ∈ E ∩ W, ∀ q ∈ E ∩ W, dist p q ≤ R) :
    ((tubes.sup (fun W => ((E ∩ W).image (gridLabel r)).card) : ℕ) : ℝ) ≤
      (9 : ℝ) ^ d * (6 : ℝ) ^ t * K ^ 2 * (R / r) ^ t := by
  classical
  by_cases hT : tubes.Nonempty
  · obtain ⟨W, hW, hmax⟩ := Finset.exists_mem_eq_sup tubes hT
      (fun W => ((E ∩ W).image (gridLabel r)).card)
    rw [hmax]
    exact diameter_subset_occupied_grid_cells_le A (E ∩ W) hδ hδr hrone hrR hK ht htd
      hdiam hAD (Finset.inter_subset_left.trans hEA) (hfootprint W hW)
  · have hz : tubes = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp only [hz, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero]
    have hr : 0 < r := hδ.trans_le hδr
    have hR : 0 < R := hr.trans_le hrR
    positivity

end
end ADGridCoverMenus
