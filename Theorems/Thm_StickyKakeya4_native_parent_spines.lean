import Theorems.Thm_StickyKakeya4_native_dyadic_tube_epoch
import Theorems.Thm_StickyKakeya4_tube_expansion_cover
import Theorems.Thm_StickyKakeya4_uniform_grain_partitions

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace NativeParentSpines

open NativeDyadicTubeStopping NativeDyadicTubeEpoch ActualTubeFootprintProfiles
open DisjointProfileEpochs FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section FiniteFibers
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def owner (Fs : List (Finset α)) (a : α) : Finset α :=
  if ha : a ∈ support Fs then Classical.choose ((mem_support Fs a).mp ha) else ∅

lemma owner_spec (Fs : List (Finset α)) {a : α} (ha : a ∈ support Fs) :
    owner Fs a ∈ Fs ∧ a ∈ owner Fs a := by
  simp only [owner, dif_pos ha]
  exact Classical.choose_spec ((mem_support Fs a).mp ha)

def pairedMenu (cell : α → β) : List (Finset α) → Finset (Finset α × β)
  | [] => ∅
  | F :: Fs => (F.image cell).image (fun c => (F, c)) ∪ pairedMenu cell Fs

lemma mem_pairedMenu_of (cell : α → β) {Fs : List (Finset α)} {F : Finset α}
    (hF : F ∈ Fs) {c : β} (hc : c ∈ F.image cell) : (F, c) ∈ pairedMenu cell Fs := by
  induction Fs with
  | nil => simp at hF
  | cons G Fs ih =>
    rcases List.mem_cons.mp hF with rfl | hF
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)
    · exact Finset.mem_union_right _ (ih hF)

lemma pair_label_image_subset (Fs : List (Finset α)) (cell : α → β) :
    (support Fs).image (fun a => (owner Fs a, cell a)) ⊆ pairedMenu cell Fs := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  have ho := owner_spec Fs ha
  exact mem_pairedMenu_of cell ho.1 (Finset.mem_image_of_mem cell ho.2)

lemma pairedMenu_card_le (Fs : List (Finset α)) (cell : α → β) (M : ℝ)
    (hM : ∀ F ∈ Fs, ((F.image cell).card : ℝ) ≤ M) :
    ((pairedMenu cell Fs).card : ℝ) ≤ (Fs.length : ℝ) * M := by
  induction Fs with
  | nil => simp [pairedMenu]
  | cons F Fs ih =>
    have hF := hM F (by simp)
    have htail := ih (fun G hG => hM G (by simp [hG]))
    have hcard : ((pairedMenu cell (F :: Fs)).card : ℝ) ≤
        ((F.image cell).card : ℝ) + ((pairedMenu cell Fs).card : ℝ) := by
      exact_mod_cast (Finset.card_union_le ((F.image cell).image (fun c => (F, c)))
        (pairedMenu cell Fs)).trans (Nat.add_le_add_right (Finset.card_image_le) _)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith only [hcard, hF, htail]

lemma pair_label_menu_le (Fs : List (Finset α)) (cell : α → β) (M : ℝ)
    (hM : ∀ F ∈ Fs, ((F.image cell).card : ℝ) ≤ M) :
    (((support Fs).image (fun a => (owner Fs a, cell a))).card : ℝ) ≤ (Fs.length : ℝ) * M :=
  (Nat.cast_le.mpr (Finset.card_le_card (pair_label_image_subset Fs cell))).trans
    (pairedMenu_card_le Fs cell M hM)

lemma support_card_lower (Fs : List (Finset α)) (hdisj : Fs.Pairwise Disjoint)
    (f : ℝ) (hF : ∀ F ∈ Fs, f ≤ (F.card : ℝ)) :
    (Fs.length : ℝ) * f ≤ ((support Fs).card : ℝ) := by
  rw [support_card Fs hdisj]
  have hsum : ∀ Gs : List (Finset α), (∀ G ∈ Gs, f ≤ (G.card : ℝ)) →
      (Gs.length : ℝ) * f ≤ (mass Gs : ℝ) := by
    intro Gs
    induction Gs with
    | nil => simp
    | cons G Gs ih =>
      intro hG
      have hhead := hG G (by simp)
      have htail := ih (fun H hH => hG H (by simp [hH]))
      simp only [List.length_cons, mass_cons, Nat.cast_add, Nat.cast_one]
      linarith only [hhead, htail]
  exact hsum Fs hF
end FiniteFibers

/-- An ORIGINAL rho-cell has an AD upper population even for an arbitrary
retained restriction. Source AD is evaluated at rho>=delta, at a real anchor. -/
lemma original_cell_card_le (A : Finset Plane) (S : Finset A) {δ ρ K t : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρone : ρ ≤ 1) (hK : 1 ≤ K)
    (hAD : ADBounds A δ K t) (c : GridLabel 1) :
    ((S.filter (fun a => grid (position A) ρ a = c)).card : ℝ) ≤ K * (ρ / δ) ^ t := by
  classical
  let F := S.filter (fun a => grid (position A) ρ a = c)
  have hρ : 0 < ρ := hδ.trans_le hδρ
  by_cases hF : F.Nonempty
  · obtain ⟨a, ha⟩ := hF
    have hsub : F.image (position A) ⊆ carrierBall A (position A a) ρ := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      apply (mem_carrierBall A _ _ _).mpr
      refine ⟨q.property, ?_⟩
      have heq : grid (position A) ρ q = grid (position A) ρ a :=
        (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp ha).2.symm
      exact (SeparatedAlignmentPatches.same_cell_dist_lt ρ hρ (position A q) (position A a) heq).le
    have hcard : (F.card : ℝ) ≤ ((carrierBall A (position A a) ρ).card : ℝ) := by
      have hc := Finset.card_le_card hsub
      have himage : (F.image (position A)).card = F.card :=
        Finset.card_image_of_injective F (show Function.Injective (position A) from Subtype.val_injective)
      rw [himage] at hc
      exact_mod_cast hc
    exact hcard.trans (hAD (position A a) a.property ρ hδρ hρone).2
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card : ℝ) ≤ _
    rw [hz, Finset.card_empty, Nat.cast_zero]
    have hKpos : 0 < K := zero_lt_one.trans_le hK
    positivity

lemma mass_le_original_grid_cells (A : Finset Plane) (S : Finset A) {δ ρ K t : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρone : ρ ≤ 1) (hK : 1 ≤ K)
    (hAD : ADBounds A δ K t) :
    (S.card : ℝ) ≤ ((S.image (grid (position A) ρ)).card : ℝ) * (K * (ρ / δ) ^ t) := by
  exact FractionalFiberAlignment.card_le_cells_mul_real_capacity S S (grid (position A) ρ)
    (Finset.Subset.refl S) (K * (ρ / δ) ^ t)
    (original_cell_card_le A S hδ hδρ hρone hK hAD)

/-- A whole-cell source fiber meets only the SAME stopped profile's actual
b-parents. The loss is 25 from the literal width-two cover in the plane. -/
lemma fiber_parent_menu_le (A : Finset Plane) {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset A}
    (D : StoppedProfile (position A) δ ε K t N E₀) (hδ : 0 < δ)
    (F : Finset A) (hF : F ⊆ E₀) (T : TubeData 1)
    (hT : ∀ a ∈ F, InTube T (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a))
    (j : ℕ) (hlo : D.pair.1 ≤ j) (hhi : j ≤ D.pair.2) :
    ((F.image (grid (position A) (scale δ j))).card : ℝ) ≤
      25 * D.loss * (scale δ D.pair.2 / scale δ j) ^ D.exponent := by
  have hb : 0 < scale δ j := scale_pos hδ _
  have hrb : scale δ D.pair.1 ≤ scale δ j := scale_mono hδ.le hlo
  have hsub : F ⊆ E₀ ∩ trace (position A) (2 * scale δ j) (scale δ D.pair.2) T := by
    intro a ha
    refine Finset.mem_inter.mpr ⟨hF ha, (mem_trace _ _ _ _ _).mpr ?_⟩
    obtain ⟨u, hu, he⟩ := hT a ha
    exact ⟨u, hu, fun i => (he i).trans (by linarith only [hrb])⟩
  have hcover := TubeExpansionCover.expanded_tube_le_actual_profile (position A)
    (grid (position A) (scale δ j)) E₀ T (tau := scale δ D.pair.2) hb 2
  have hcard : (F.image (grid (position A) (scale δ j))).card ≤
      25 * coverProfile (position A) (scale δ j) (scale δ D.pair.2) E₀ := by
    have hh := Finset.card_le_card (Finset.image_subset_image
      (f := grid (position A) (scale δ j)) hsub)
    exact hh.trans (by simpa [coverProfile, FiniteCoverProfileEpochs.coverCount] using hcover)
  have hcount : ((F.image (grid (position A) (scale δ j))).card : ℝ) ≤
      25 * (coverProfile (position A) (scale δ j) (scale δ D.pair.2) E₀ : ℝ) := by exact_mod_cast hcard
  have hprofile := (D.nested_upper (j, D.pair.2) ⟨hlo, le_refl _, hhi⟩).le
  change (coverProfile (position A) (scale δ j) (scale δ D.pair.2) E₀ : ℝ) ≤
    D.loss * (scale δ D.pair.2 / scale δ j) ^ D.exponent at hprofile
  nlinarith only [hcount, hprofile]


def refinementCost (m L : ℕ) : ℕ := 2 * (4 * (m + (m + m))) ^ ((m + (m + m)) * L)

def UniformPartition {α β : Type*} (B : Finset α) (label : α → β) (Q : ℕ) : Prop :=
  ∀ x y, x ∈ B → y ∈ B →
    SelfUniform.degree (fun _ => 1) (fun a b => label a = label b) B x ≤
      Q ^ 2 * SelfUniform.degree (fun _ => 1) (fun a b => label a = label b) B y

lemma unit_degree_eq_card {α β : Type*} [DecidableEq β] (B : Finset α) (label : α → β) (x : α) :
    SelfUniform.degree (fun _ => 1) (fun a b => label a = label b) B x =
      (B.filter (fun a => label a = label x)).card := by
  classical
  simp [SelfUniform.degree, eq_comm]

/-- One simultaneous construction reserves angular/spatial uniformity on the
same retained set that supplies parent and source-fiber-parent richness. -/
theorem exists_uniform_parent_core (A : Finset Plane) (Fs : List (Finset A))
    {m Q L : ℕ} (hm : 0 < m) (hQ : 4 ≤ Q) (b : Fin m → ℝ)
    (angle : Fin m → A → ℤ) (hne : (support Fs).Nonempty)
    (hheight : (support Fs).card ≤ Q ^ L) :
    ∃ B ⊆ support Fs, B.Nonempty ∧
      (support Fs).card ≤ refinementCost m L * B.card ∧
      (∀ j, UniformPartition B (grid (position A) (b j)) Q) ∧
      (∀ j, UniformPartition B (fun a => (grid (position A) (b j) a, angle j a)) Q) ∧
      (∀ j, UniformPartition B (fun a => (owner Fs a, grid (position A) (b j) a)) Q) := by
  classical
  let rel : Fin (m + (m + m)) → A → A → Prop :=
    Fin.addCases (fun j x y => grid (position A) (b j) x = grid (position A) (b j) y)
      (Fin.addCases
        (fun j x y => (grid (position A) (b j) x, angle j x) = (grid (position A) (b j) y, angle j y))
        (fun j x y => (owner Fs x, grid (position A) (b j) x) = (owner Fs y, grid (position A) (b j) y)))
  have href : ∀ i x, rel i x x := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j x
      simp only [rel, Fin.addCases_left]
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro j x
        simp only [rel, Fin.addCases_right, Fin.addCases_left]
      · intro j x
        simp only [rel, Fin.addCases_right]
  have hsym : ∀ i x y, rel i x y → rel i y x := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j x y h
      simp only [rel, Fin.addCases_left] at h ⊢
      exact h.symm
    · intro k
      refine Fin.addCases ?_ ?_ k
      · intro j x y h
        simp only [rel, Fin.addCases_right, Fin.addCases_left] at h ⊢
        exact h.symm
      · intro j x y h
        simp only [rel, Fin.addCases_right] at h ⊢
        exact h.symm
  obtain ⟨B, hB, hneB, hret, huniform⟩ := SelfUniform.weighted_self_uniform_refinement
    (show 0 < m + (m + m) by omega) hQ (fun _ : A => 1) rel href hsym
    (support Fs) hne (fun _ _ => Nat.zero_lt_one) (by simpa [SelfUniform.mass] using hheight)
  refine ⟨B, hB, hneB, ?_, ?_, ?_, ?_⟩
  · simpa [SelfUniform.mass, refinementCost] using hret
  · intro j
    simpa only [UniformPartition, rel, Fin.addCases_left] using huniform (Fin.castAdd (m + m) j)
  · intro j
    simpa only [UniformPartition, rel, Fin.addCases_right, Fin.addCases_left] using
      huniform (Fin.natAdd m (Fin.castAdd m j))
  · intro j
    simpa only [UniformPartition, rel, Fin.addCases_right] using huniform (Fin.natAdd m (Fin.natAdd m j))

/-- The actual retained spine is a subset of one source fiber inside one
literal parent. Its anchor is the original point itself. -/
def parentSpine (A : Finset Plane) (Fs : List (Finset A)) (B : Finset A) (b : ℝ) (q : A) : Finset A :=
  B.filter (fun a => (owner Fs a, grid (position A) b a) = (owner Fs q, grid (position A) b q))

lemma parentSpine_anchor (A : Finset Plane) (Fs : List (Finset A)) (B : Finset A)
    (b : ℝ) {q : A} (hq : q ∈ B) : q ∈ parentSpine A Fs B b q := by
  simp [parentSpine, hq]

lemma parentSpine_subset_owner (A : Finset Plane) (Fs : List (Finset A)) (B : Finset A)
    (hB : B ⊆ support Fs) (b : ℝ) (q : A) : parentSpine A Fs B b q ⊆ owner Fs q := by
  intro a ha
  obtain ⟨haB, heq⟩ := Finset.mem_filter.mp ha
  have ho := (owner_spec Fs (hB haB)).2
  have howner : owner Fs a = owner Fs q := congrArg Prod.fst heq
  rwa [howner] at ho

lemma parentSpine_same_cell (A : Finset Plane) (Fs : List (Finset A)) (B : Finset A)
    (b : ℝ) (q : A) :
    ∀ a ∈ parentSpine A Fs B b q, grid (position A) b a = grid (position A) b q := by
  intro a ha
  exact congrArg Prod.snd (Finset.mem_filter.mp ha).2

/-- Finite cancellation of the number of actual disjoint fibers. Both the
source mass and the menu refer to the SAME original fiber family. -/
lemma parentSpine_point_richness (A : Finset Plane) (Fs : List (Finset A))
    (B : Finset A) (hB : B ⊆ support Fs) (hdisj : Fs.Pairwise Disjoint)
    (Q C : ℕ) (b f M : ℝ)
    (hret : (support Fs).card ≤ C * B.card)
    (hlarge : ∀ F ∈ Fs, f ≤ (F.card : ℝ))
    (hmenu : ∀ F ∈ Fs, ((F.image (grid (position A) b)).card : ℝ) ≤ M)
    (huniform : UniformPartition B (fun a => (owner Fs a, grid (position A) b a)) Q)
    {q : A} (hq : q ∈ B) :
    f ≤ (C : ℝ) * (Q : ℝ) ^ 2 * M * ((parentSpine A Fs B b q).card : ℝ) := by
  have hsource := support_card_lower Fs hdisj f hlarge
  have hgrain := SelfUniform.partition_richness_of_self_uniform (fun _ : A => 1)
    (fun a => (owner Fs a, grid (position A) b a)) Q hB huniform hq
  rw [unit_degree_eq_card] at hgrain
  simp only [SelfUniform.mass, Finset.sum_const, smul_eq_mul, mul_one] at hgrain
  have hgrainR : (B.card : ℝ) ≤ (Q : ℝ) ^ 2 *
      (((support Fs).image (fun a => (owner Fs a, grid (position A) b a))).card : ℝ) *
      ((parentSpine A Fs B b q).card : ℝ) := by
    have hnat : B.card ≤ Q ^ 2 *
        ((support Fs).image (fun a => (owner Fs a, grid (position A) b a))).card *
        (parentSpine A Fs B b q).card := by
      simpa only [parentSpine, Finset.filter_congr_decidable] using hgrain
    exact_mod_cast hnat
  have hmenuR := pair_label_menu_le Fs (grid (position A) b) M hmenu
  have hretR : ((support Fs).card : ℝ) ≤ (C : ℝ) * (B.card : ℝ) := by exact_mod_cast hret
  have hL : (0 : ℝ) < Fs.length := by
    have hsrc : (support Fs).Nonempty := ⟨q, hB hq⟩
    have hlist : Fs ≠ [] := by intro he; simp [he, support] at hsrc
    exact_mod_cast List.length_pos_iff.mpr hlist
  have hmenuscaled := mul_le_mul_of_nonneg_left hmenuR
    (show 0 ≤ (Q : ℝ) ^ 2 by positivity)
  have hmenuscaled' := mul_le_mul_of_nonneg_right hmenuscaled
    (show 0 ≤ ((parentSpine A Fs B b q).card : ℝ) by positivity)
  have hBbound := hgrainR.trans hmenuscaled'
  have hscaled := mul_le_mul_of_nonneg_left hBbound (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  have hwhole : (Fs.length : ℝ) * f ≤ (Fs.length : ℝ) *
      ((C : ℝ) * (Q : ℝ) ^ 2 * M * ((parentSpine A Fs B b q).card : ℝ)) := by
    calc
      _ ≤ ((support Fs).card : ℝ) := hsource
      _ ≤ (C : ℝ) * (B.card : ℝ) := hretR
      _ ≤ _ := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled
  exact (mul_le_mul_iff_right₀ hL).mp hwhole


lemma spine_power_cancellation {ρ τ b δ rate K H C s t Z : ℝ}
    (hρ : 0 < ρ) (hτ : 0 < τ) (hb : 0 < b) (hδ : 0 < δ)
    (hK : 0 < K) (hH : 0 < H) (hC : 0 < C)
    (h : (rate / 4) * (ρ / δ) ^ t * (τ / ρ) ^ s ≤
      C * (25 * H * (τ / b) ^ s) * (K * (ρ / δ) ^ t) * Z) :
    rate / (100 * C * H * K) * (b / ρ) ^ s ≤ Z := by
  have hratio : τ / ρ = (τ / b) * (b / ρ) := by field_simp
  have hpow : (τ / ρ) ^ s = (τ / b) ^ s * (b / ρ) ^ s := by
    rw [hratio, Real.mul_rpow (by positivity : 0 ≤ τ / b) (by positivity : 0 ≤ b / ρ)]
  have hcommon : 0 < (ρ / δ) ^ t * (τ / b) ^ s := by positivity
  have hscaled : ((ρ / δ) ^ t * (τ / b) ^ s) * (rate * (b / ρ) ^ s) ≤
      ((ρ / δ) ^ t * (τ / b) ^ s) * (100 * C * H * K * Z) := by
    have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)
    rw [hpow] at hh
    nlinarith only [hh]
  have hc := (mul_le_mul_iff_right₀ hcommon).mp hscaled
  have hden : 0 < 100 * C * H * K := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  simpa only [mul_comm] using hc

lemma parent_power_cancellation {δ b K t W C Z : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hK : 0 < K)
    (hlower : (1 / δ) ^ t ≤ K * W) (hupper : W ≤ C * (1 / b) ^ t * Z) :
    (b / δ) ^ t ≤ (K * C) * Z := by
  have hleft : (b / δ) ^ t = b ^ t * (1 / δ) ^ t := by
    rw [← Real.mul_rpow hb.le (by positivity : 0 ≤ 1 / δ)]
    congr 1
    ring
  have hcancel : b ^ t * (1 / b) ^ t = 1 := by
    rw [← Real.mul_rpow hb.le (by positivity : 0 ≤ 1 / b)]
    simp [hb.ne']
  calc
    (b / δ) ^ t = b ^ t * (1 / δ) ^ t := hleft
    _ ≤ b ^ t * (K * W) := mul_le_mul_of_nonneg_left hlower (Real.rpow_nonneg hb.le _)
    _ ≤ b ^ t * (K * (C * (1 / b) ^ t * Z)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hupper hK.le) (Real.rpow_nonneg hb.le _)
    _ = (K * C) * Z := by
      calc
        _ = (b ^ t * (1 / b) ^ t) * ((K * C) * Z) := by ring
        _ = _ := by rw [hcancel, one_mul]

def spineConstant (N m Q L : ℕ) (K t H : ℝ) : ℝ :=
  pruningRate N K t / (100 * (refinementCost m L : ℝ) * (Q : ℝ) ^ 2 * H * K)

structure ParentCore (A : Finset Plane) (Fs : List (Finset A))
    {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset A}
    (D : StoppedProfile (position A) δ ε K t N E₀)
    (C₀ Q L : ℕ) {m : ℕ} (level : Fin m → ℕ) (angle : Fin m → A → ℤ) where
  points : Finset A
  subset : points ⊆ support Fs
  nonempty : points.Nonempty
  retained : (support Fs).card ≤ refinementCost m L * points.card
  spatial_uniform : ∀ j, UniformPartition points (grid (position A) (scale δ (level j))) Q
  angular_uniform : ∀ j, UniformPartition points
    (fun a => (grid (position A) (scale δ (level j)) a, angle j a)) Q
  fiber_uniform : ∀ j, UniformPartition points
    (fun a => (owner Fs a, grid (position A) (scale δ (level j)) a)) Q
  spine_rich : ∀ j q, q ∈ points →
    spineConstant N m Q L K t D.loss * (scale δ (level j) / scale δ D.pair.1) ^ D.exponent ≤
      (((parentSpine A Fs points (scale δ (level j)) q).image
        (grid (position A) (scale δ D.pair.1))).card : ℝ)
  parent_mass : ∀ j q, q ∈ points →
    (scale δ (level j) / δ) ^ t ≤
      ((C₀ : ℝ) * (refinementCost m L : ℝ) * (Q : ℝ) ^ 2 * spatialConstant K t * K) *
        ((points.filter (fun a => grid (position A) (scale δ (level j)) a =
          grid (position A) (scale δ (level j)) q)).card : ℝ)
  spine_tube : ∀ q, q ∈ points → ∃ T : TubeData 1,
    InTube T (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A q) ∧
    ∀ j a, a ∈ parentSpine A Fs points (scale δ (level j)) q →
      InTube T (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a)

/-- Actual simultaneous parent-spine construction. Source fiber richness and
source retention are the outputs of the preceding native epoch; the parent
richness and rho-grid spine bounds are constructed on one retained B. -/
theorem exists_parent_core (A : Finset Plane) {δ ε K t : ℝ} {N : ℕ} {E₀ : Finset A}
    (D : StoppedProfile (position A) δ ε K t N E₀) (Fs : List (Finset A))
    (hδ : 0 < δ) (hε : 0 ≤ ε) (htop : scale δ N ≤ 1) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) (hAD : ADBounds A δ K t)
    (hsource : (support Fs).Nonempty) (hdisj : Fs.Pairwise Disjoint)
    (hsub : ∀ F ∈ Fs, F ⊆ E₀)
    (hfiber : ∀ F ∈ Fs,
      pruningRate N K t / 4 * (scale δ D.pair.1 / δ) ^ t *
        (scale δ D.pair.2 / scale δ D.pair.1) ^ D.exponent ≤ (F.card : ℝ))
    (htube : ∀ F ∈ Fs, ∃ T : TubeData 1,
      ∀ a ∈ F, InTube T (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a))
    {C₀ m Q L : ℕ} (hm : 0 < m) (hQ : 4 ≤ Q)
    (hOriginal : A.card ≤ C₀ * (support Fs).card)
    (level : Fin m → ℕ) (hlevel : ∀ j, D.pair.1 ≤ level j ∧ level j ≤ D.pair.2)
    (angle : Fin m → A → ℤ) (hheight : (support Fs).card ≤ Q ^ L) :
    Nonempty (ParentCore A Fs D C₀ Q L level angle) := by
  classical
  obtain ⟨B, hB, hBne, hret, hspatial, hangular, hfibuniform⟩ :=
    exists_uniform_parent_core A Fs hm hQ (fun j => scale δ (level j)) angle hsource hheight
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hHpos : 0 < D.loss := zero_lt_one.trans_le (D.loss_ge_one hδ hε hK ht)
  have hρ : 0 < scale δ D.pair.1 := scale_pos hδ _
  have hτ : 0 < scale δ D.pair.2 := scale_pos hδ _
  have hδρ : δ ≤ scale δ D.pair.1 := by simpa only [scale_zero] using scale_mono hδ.le (Nat.zero_le D.pair.1)
  have hρone : scale δ D.pair.1 ≤ 1 :=
    (scale_mono hδ.le (D.valid.1.trans D.valid.2)).trans htop
  have hcost : (0 : ℝ) < refinementCost m L := by
    unfold refinementCost
    have hd : 0 < m + (m + m) := by omega
    positivity
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hCpos : 0 < (refinementCost m L : ℝ) * (Q : ℝ) ^ 2 := by positivity
  refine ⟨⟨B, hB, hBne, hret, hspatial, hangular, hfibuniform, ?_, ?_, ?_⟩⟩
  · intro j q hq
    have hb : 0 < scale δ (level j) := scale_pos hδ _
    have hmenu : ∀ F ∈ Fs, ((F.image (grid (position A) (scale δ (level j)))).card : ℝ) ≤
        25 * D.loss * (scale δ D.pair.2 / scale δ (level j)) ^ D.exponent := by
      intro F hF
      obtain ⟨T, hT⟩ := htube F hF
      exact fiber_parent_menu_le A D hδ F (hsub F hF) T hT (level j) (hlevel j).1 (hlevel j).2
    have hpoint := parentSpine_point_richness A Fs B hB hdisj Q (refinementCost m L)
      (scale δ (level j)) _ _ hret hfiber hmenu (hfibuniform j) hq
    have hcap := mass_le_original_grid_cells A (parentSpine A Fs B (scale δ (level j)) q)
      hδ hδρ hρone hK hAD
    have hmcap := mul_le_mul_of_nonneg_left hcap
      (show 0 ≤ (refinementCost m L : ℝ) * (Q : ℝ) ^ 2 *
        (25 * D.loss * (scale δ D.pair.2 / scale δ (level j)) ^ D.exponent) by positivity)
    have hfull := hpoint.trans hmcap
    have hclean : pruningRate N K t / 4 * (scale δ D.pair.1 / δ) ^ t *
        (scale δ D.pair.2 / scale δ D.pair.1) ^ D.exponent ≤
      ((refinementCost m L : ℝ) * (Q : ℝ) ^ 2) *
        (25 * D.loss * (scale δ D.pair.2 / scale δ (level j)) ^ D.exponent) *
        (K * (scale δ D.pair.1 / δ) ^ t) *
        (((parentSpine A Fs B (scale δ (level j)) q).image (grid (position A) (scale δ D.pair.1))).card : ℝ) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hfull
    have hcancel := spine_power_cancellation hρ hτ hb hδ hKpos hHpos hCpos hclean
    simpa only [spineConstant, mul_assoc] using hcancel
  · intro j q hq
    have hb : 0 < scale δ (level j) := scale_pos hδ _
    have hδb : δ ≤ scale δ (level j) := hδρ.trans (scale_mono hδ.le (hlevel j).1)
    have hbone : scale δ (level j) ≤ 1 :=
      (scale_mono hδ.le ((hlevel j).2.trans D.valid.2)).trans htop
    have hgrid := ADGridCoverMenus.diameter_subset_occupied_grid_cells_le A A hδ hδb hbone hbone
      hK ht ht2 hdiam hAD (Finset.Subset.refl A) hdiam
    have hmenu : (((support Fs).image (grid (position A) (scale δ (level j)))).card : ℝ) ≤
        spatialConstant K t * (1 / scale δ (level j)) ^ t := by
      apply le_trans ?_ hgrid
      exact_mod_cast Finset.card_le_card (show (support Fs).image (grid (position A) (scale δ (level j))) ⊆
          A.image (ADGridCoverMenus.gridLabel (scale δ (level j))) from by
        intro c hc
        obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hc
        exact Finset.mem_image_of_mem _ a.property)
    have hgrain := SelfUniform.partition_richness_of_self_uniform (fun _ : A => 1)
      (grid (position A) (scale δ (level j))) Q hB (hspatial j) hq
    rw [unit_degree_eq_card] at hgrain
    simp only [SelfUniform.mass, Finset.sum_const, smul_eq_mul, mul_one] at hgrain
    have hgrainR : (B.card : ℝ) ≤ (Q : ℝ) ^ 2 *
        (((support Fs).image (grid (position A) (scale δ (level j)))).card : ℝ) *
        ((B.filter (fun a => grid (position A) (scale δ (level j)) a = grid (position A) (scale δ (level j)) q)).card : ℝ) := by exact_mod_cast hgrain
    have hmenuScaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmenu (sq_nonneg (Q : ℝ)))
      (show (0 : ℝ) ≤ (B.filter (fun a => grid (position A) (scale δ (level j)) a = grid (position A) (scale δ (level j)) q)).card by positivity)
    have hBbound := hgrainR.trans hmenuScaled
    have hOriginalR : (A.card : ℝ) ≤ (C₀ : ℝ) * ((support Fs).card : ℝ) := by exact_mod_cast hOriginal
    have hretR : ((support Fs).card : ℝ) ≤ (refinementCost m L : ℝ) * (B.card : ℝ) := by exact_mod_cast hret
    have htotal := hOriginalR.trans (mul_le_mul_of_nonneg_left
      (hretR.trans (mul_le_mul_of_nonneg_left hBbound (Nat.cast_nonneg _))) (Nat.cast_nonneg C₀))
    have hAne : A.Nonempty := by obtain ⟨a, _ha⟩ := hsource; exact ⟨position A a, a.property⟩
    have hδone : δ ≤ 1 := hδρ.trans hρone
    have hlower := original_card_lower A hAne hδ hδone hK hAD
    have hcancel := parent_power_cancellation hδ hb hKpos hlower
      (show (A.card : ℝ) ≤ ((C₀ : ℝ) * (refinementCost m L : ℝ) * (Q : ℝ) ^ 2 * spatialConstant K t) *
        (1 / scale δ (level j)) ^ t *
        ((B.filter (fun a => grid (position A) (scale δ (level j)) a = grid (position A) (scale δ (level j)) q)).card : ℝ) by
        simpa only [mul_assoc] using htotal)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcancel
  · intro q hq
    have ho := owner_spec Fs (hB hq)
    obtain ⟨T, hT⟩ := htube (owner Fs q) ho.1
    refine ⟨T, hT q ho.2, ?_⟩
    intro j a ha
    exact hT a (parentSpine_subset_owner A Fs B hB _ q ha)


/-- Native original-AD constructor through the first parent/spine refinement.
There is no retained-set, fiber-richness, parent-mass or tube-menu certificate
among the inputs. Candidate dyadic parents and literal angular maps can be
chosen after the constructed stopped epoch and its exposed actual tube witnesses,
and are tested on the SAME core. -/
theorem exists_native_parent_preparation (A : Finset Plane) (δ ε K t : ℝ) (N : ℕ)
    (hne : A.Nonempty) (hδ : 0 < δ) (hN : 0 < N) (htop : scale δ N ≤ 1)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hK : 1 ≤ K) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hlarge : 4 * (Real.log 72 / Real.log 2) < ε ^ CoverProfileStopping.stepBudget ε * (N : ℝ))
    (hdiam : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ 1) (hAD : ADBounds A δ K t) :
    ∃ e : Epoch A (Index N), ∃ D : StoppedProfile (position A) δ ε K t N e.start,
      D.pair = e.index.val ∧ e.pieces.Pairwise Disjoint ∧
      A.card ≤ 2 * (Fintype.card (Index N) * rank 2 A.card) * (support e.pieces).card ∧
      (∀ F ∈ e.pieces, ∃ T : TubeData 1,
        ∀ a ∈ F, InTube T (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a)) ∧
      ∀ (m Q L : ℕ), 0 < m → 4 ≤ Q → A.card ≤ Q ^ L →
        ∀ (level : Fin m → ℕ), (∀ j, D.pair.1 ≤ level j ∧ level j ≤ D.pair.2) →
        ∀ (angle : Fin m → A → ℤ),
          Nonempty (ParentCore A e.pieces D (2 * (Fintype.card (Index N) * rank 2 A.card)) Q L level angle) := by
  classical
  obtain ⟨e, D, hD, _hFnonempty, hdisj, hret, _hphysical, hpieces⟩ :=
    exists_native_disjoint_epoch A δ ε K t N hne hδ hN htop hε hεhalf hK ht ht2 hlarge hdiam hAD
  have hsource : (support e.pieces).Nonempty := by
    apply Finset.card_pos.mp
    have hApos := hne.card_pos
    by_contra h
    have hz : (support e.pieces).card = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at hret
    omega
  have hsub : ∀ F ∈ e.pieces, F ⊆ e.start := by
    intro F hF
    obtain ⟨E, hE, T, _hreg, hFE, _hwhole, _hTube, _hgrid, _hmass⟩ := hpieces F hF
    exact hFE.trans hE
  have hfiber : ∀ F ∈ e.pieces,
      pruningRate N K t / 4 * (scale δ D.pair.1 / δ) ^ t *
        (scale δ D.pair.2 / scale δ D.pair.1) ^ D.exponent ≤ (F.card : ℝ) := by
    intro F hF
    obtain ⟨E, _hE, T, _hreg, _hFE, _hwhole, _hTube, _hgrid, hmass⟩ := hpieces F hF
    have hr : realThreshold δ N K t e.index = pruningRate N K t * (scale δ D.pair.1 / δ) ^ t := by
      simp only [realThreshold, hD]
    rw [hr] at hmass
    convert hmass using 1; ring
  have htube : ∀ F ∈ e.pieces, ∃ T : TubeData 1,
      ∀ a ∈ F, InTube T (2 * scale δ D.pair.1) (scale δ D.pair.2) (position A a) := by
    intro F hF
    obtain ⟨E, _hE, T, _hreg, _hFE, _hwhole, hTube, _hgrid, _hmass⟩ := hpieces F hF
    exact ⟨T, by simpa only [hD] using hTube⟩
  refine ⟨e, D, hD, hdisj, hret, htube, ?_⟩
  intro m Q L hm hQ hheight level hlevel angle
  have hheight' : (support e.pieces).card ≤ Q ^ L := by
    have hcard := Finset.card_le_card (Finset.subset_univ (support e.pieces))
    rw [source_card] at hcard
    exact hcard.trans hheight
  exact exists_parent_core A D e.pieces hδ hε.le htop hK ht ht2 hdiam hAD hsource hdisj hsub hfiber htube
    hm hQ hret level hlevel angle hheight'

end
end NativeParentSpines
