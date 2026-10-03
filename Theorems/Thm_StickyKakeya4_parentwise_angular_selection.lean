import Theorems.Thm_StickyKakeya4_angular_menu_stabilization

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace ParentwiseAngularSelection

open SelfUniform CompatibleTupleSelection AngularMenuStabilization
open scoped BigOperators

variable {α σ τ : Type*} [DecidableEq σ] [DecidableEq τ]

/-- Actual weighted menu incidences admit a maximizing angular choice. -/
theorem maximum_menu_choice (w : α → ℕ) (S : Finset α) (G : α → Finset τ)
    (U : Finset τ) (hU : U.Nonempty) (hG : ∀ a ∈ S, G a ⊆ U) :
    ∃ u ∈ U,
      (∑ a ∈ S, w a * (G a).card) ≤
        U.card * mass w (S.filter (fun a => u ∈ G a)) := by
  classical
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image U
    (fun v => mass w (S.filter (fun a => v ∈ G a))) hU
  have hsum : (∑ v ∈ U, mass w (S.filter (fun a => v ∈ G a))) =
      ∑ a ∈ S, w a * (G a).card := by
    simp only [mass, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    have he : U.filter (fun v => v ∈ G a) = G a := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun hv => hv.2, fun hv => ⟨hG a ha hv, hv⟩⟩
    rw [← Finset.sum_filter, he]
    simp [Nat.mul_comm]
  refine ⟨u, hu, ?_⟩
  calc
    (∑ a ∈ S, w a * (G a).card) =
        ∑ v ∈ U, mass w (S.filter (fun a => v ∈ G a)) := hsum.symm
    _ ≤ ∑ _v ∈ U, mass w (S.filter (fun a => u ∈ G a)) :=
      Finset.sum_le_sum (fun v hv => hmax v hv)
    _ = _ := by simp

/-- Nested original point cells give literal inclusion of each child's menu. -/
lemma child_menu_subset_parent (A : Finset α) (p q : α → σ) (θ : α → τ)
    (hnested : ∀ a b, a ∈ A → b ∈ A → p a = p b → q a = q b)
    {a : α} (ha : a ∈ A) : menu A p θ (p a) ⊆ menu A q θ (q a) := by
  intro u hu
  obtain ⟨b, hb, hθ⟩ := Finset.mem_image.mp hu
  obtain ⟨hbA, hpb⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_image.mpr ⟨b,
    Finset.mem_filter.mpr ⟨hbA, hnested b a hbA ha hpb⟩, hθ⟩

/-- With a common winning scale and derived menu comparison, choose the
maximum-weight angle independently in EVERY occupied original parent.
No per-parent regularity or retained-set certificate is assumed. -/
theorem select_in_each_parent (w : α → ℕ) (A : Finset α)
    (p q : α → σ) (θ : α → τ) (K B D : ℕ)
    (hne : A.Nonempty) (hD : 0 < D)
    (hnested : ∀ a b, a ∈ A → b ∈ A → p a = p b → q a = q b)
    (hlower : ∀ a ∈ A, D ≤ K * (menu A p θ (p a)).card)
    (hupper : ∀ c, (menu A q θ c).card ≤ B * D) :
    ∃ E ⊆ A, ∃ angle : σ → τ,
      (∀ c, mass w (cell A q c) ≤ K * B * mass w (cell E q c)) ∧
      mass w A ≤ K * B * mass w E ∧
      (∀ a b, a ∈ E → b ∈ A → p b = p a → b ∈ E) ∧
      (∀ a ∈ E, ∃ b ∈ E, p b = p a ∧ θ b = angle (q a)) := by
  classical
  obtain ⟨a₀, ha₀⟩ := hne
  let G : α → Finset τ := fun a => menu A p θ (p a)
  have hchoose : ∀ c ∈ A.image q, ∃ u ∈ menu A q θ c,
      mass w (cell A q c) ≤ K * B * mass w ((cell A q c).filter (fun a => u ∈ G a)) := by
    intro c hc
    obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp hc
    have hU : (menu A q θ c).Nonempty :=
      ⟨θ a, Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hqa⟩, rfl⟩⟩
    have hG : ∀ b ∈ cell A q c, G b ⊆ menu A q θ c := by
      intro b hb
      obtain ⟨hbA, hqb⟩ := Finset.mem_filter.mp hb
      simpa only [G, hqb] using child_menu_subset_parent A p q θ hnested hbA
    obtain ⟨u, hu, hmass⟩ := maximum_menu_choice w (cell A q c) G
      (menu A q θ c) hU hG
    refine ⟨u, hu, ?_⟩
    have hl : D * mass w (cell A q c) ≤
        K * (∑ b ∈ cell A q c, w b * (G b).card) := by
      unfold mass
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      have hbA := (Finset.mem_filter.mp hb).1
      have hh := Nat.mul_le_mul_left (w b) (hlower b hbA)
      dsimp [G]
      nlinarith only [hh]
    have hh : D * mass w (cell A q c) ≤
        D * (K * B * mass w ((cell A q c).filter (fun a => u ∈ G a))) := by
      calc
        _ ≤ K * (∑ b ∈ cell A q c, w b * (G b).card) := hl
        _ ≤ K * ((menu A q θ c).card *
            mass w ((cell A q c).filter (fun a => u ∈ G a))) := Nat.mul_le_mul_left K hmass
        _ ≤ K * ((B * D) * mass w ((cell A q c).filter (fun a => u ∈ G a))) :=
          Nat.mul_le_mul_left K (Nat.mul_le_mul_right _ (hupper c))
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hh hD
  let angle : σ → τ := fun c =>
    if hc : c ∈ A.image q then Classical.choose (hchoose c hc) else θ a₀
  have hangle : ∀ c ∈ A.image q,
      mass w (cell A q c) ≤ K * B * mass w ((cell A q c).filter (fun a => angle c ∈ G a)) := by
    intro c hc
    simpa only [angle, dif_pos hc] using (Classical.choose_spec (hchoose c hc)).2
  let E := A.filter (fun a => angle (q a) ∈ G a)
  have hEA : E ⊆ A := Finset.filter_subset _ _
  have hlocal : ∀ c, cell E q c = (cell A q c).filter (fun a => angle c ∈ G a) := by
    intro c
    ext a
    simp only [E, cell, Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, hang⟩, hqa⟩
      exact ⟨⟨ha, hqa⟩, by simpa only [hqa] using hang⟩
    · rintro ⟨⟨ha, hqa⟩, hang⟩
      exact ⟨⟨ha, by simpa only [hqa] using hang⟩, hqa⟩
  have hret : ∀ c, mass w (cell A q c) ≤ K * B * mass w (cell E q c) := by
    intro c
    by_cases hc : c ∈ A.image q
    · rw [hlocal]
      exact hangle c hc
    · have hempty : cell A q c = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨haA, hqa⟩ := Finset.mem_filter.mp ha
        exact hc (Finset.mem_image.mpr ⟨a, haA, hqa⟩)
      simp only [hempty, mass, Finset.sum_empty, Nat.zero_le]
  have hwhole : ∀ a b, a ∈ E → b ∈ A → p b = p a → b ∈ E := by
    intro a b ha hb hpa
    obtain ⟨haA, hang⟩ := Finset.mem_filter.mp ha
    have hqa := hnested b a hb haA hpa
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_⟩
    simpa only [G, hpa, hqa] using hang
  refine ⟨E, hEA, angle, hret, ?_, hwhole, ?_⟩
  · have hsumE : mass w E = ∑ c ∈ A.image q, mass w (cell E q c) := by
      simpa only [mass, cell, Finset.sum_filter] using
        (Finset.sum_fiberwise_of_maps_to (s := E) (t := A.image q) (g := q)
          (fun a ha => Finset.mem_image_of_mem q (hEA ha)) w).symm
    calc
      mass w A = ∑ c ∈ A.image q, mass w (cell A q c) := mass_eq_sum_partition w A q
      _ ≤ ∑ c ∈ A.image q, K * B * mass w (cell E q c) :=
        Finset.sum_le_sum (fun c _ => hret c)
      _ = K * B * mass w E := by rw [← Finset.mul_sum, ← hsumE]
  · intro a ha
    have hang := (Finset.mem_filter.mp ha).2
    obtain ⟨b, hb, hθ⟩ := Finset.mem_image.mp hang
    obtain ⟨hbA, hpb⟩ := Finset.mem_filter.mp hb
    exact ⟨b, hwhole a b ha hbA hpb, hpb, hθ⟩

/-- Original same-set spatial/joint comparisons construct ONE winning adjacent
scale and locally dense, whole-child angular selections in EVERY parent.
All original parents survive. The common scale, angular menus and witnesses
are conclusions, not extra regularity assumptions. -/
theorem stabilize_and_select_parentwise (w : α → ℕ) (A : Finset α)
    (p : ℕ → α → σ) (θ : α → τ) (Kₛ Kⱼ B m : ℕ)
    (hm : 0 < m) (hne : A.Nonempty) (hw : ∀ a ∈ A, 0 < w a)
    (hnested : ∀ i, i < m → ∀ a b, a ∈ A → b ∈ A →
      p i a = p i b → p (i + 1) a = p (i + 1) b)
    (hspatial : ∀ i, i ≤ m → ∀ a b, a ∈ A → b ∈ A →
      mass w (cell A (p i) (p i a)) ≤ Kₛ * mass w (cell A (p i) (p i b)))
    (hjoint : ∀ i, i ≤ m → ∀ a b, a ∈ A → b ∈ A →
      mass w (joint A (p i) θ (p i a) (θ a)) ≤
        Kⱼ * mass w (joint A (p i) θ (p i b) (θ b)))
    (hbudget : (A.image θ).card ≤ B ^ m) :
    ∃ i < m,
      maxMenu A (p (i + 1)) θ ≤ B * maxMenu A (p i) θ ∧
      ∃ E ⊆ A, E.Nonempty ∧ ∃ angle : σ → τ,
        (∀ c, mass w (cell A (p (i + 1)) c) ≤
          Kₛ * Kⱼ * B * mass w (cell E (p (i + 1)) c)) ∧
        mass w A ≤ Kₛ * Kⱼ * B * mass w E ∧
        E.image (p (i + 1)) = A.image (p (i + 1)) ∧
        (∀ a b, a ∈ E → b ∈ A → p i b = p i a → b ∈ E) ∧
        (∀ a ∈ E, ∃ b ∈ E, p i b = p i a ∧ θ b = angle (p (i + 1) a)) := by
  classical
  obtain ⟨i, hi, hstep⟩ := adjacent_growth_step (fun j => maxMenu A (p j) θ) B m hm
    (maxMenu_pos A (p 0) θ hne)
    ((maxMenu_le_angular_menu A (p m) θ).trans hbudget)
  have hlower : ∀ a ∈ A,
      maxMenu A (p i) θ ≤ (Kₛ * Kⱼ) * (menu A (p i) θ (p i a)).card := by
    intro a ha
    exact maxMenu_le_occupied_menu w A (p i) θ Kₛ Kⱼ hne hw
      (hspatial i (by omega)) (hjoint i (by omega)) (Finset.mem_image_of_mem (p i) ha)
  have hupper : ∀ c, (menu A (p (i + 1)) θ c).card ≤ B * maxMenu A (p i) θ := by
    intro c
    exact (menu_card_le_max A (p (i + 1)) θ c).trans hstep
  obtain ⟨E, hEA, angle, hlocal, hglobal, hwhole, hwitness⟩ :=
    select_in_each_parent w A (p i) (p (i + 1)) θ (Kₛ * Kⱼ) B
      (maxMenu A (p i) θ) hne (maxMenu_pos A (p i) θ hne)
      (hnested i hi) hlower hupper
  have hEpos : 0 < mass w E := by
    have hApos := mass_pos w hne hw
    by_contra h
    have hz : mass w E = 0 := by omega
    rw [hz, Nat.mul_zero] at hglobal
    omega
  have hparent : E.image (p (i + 1)) = A.image (p (i + 1)) := by
    apply Finset.Subset.antisymm (Finset.image_subset_image hEA)
    intro c hc
    obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hc
    have hcellpos : 0 < mass w (cell A (p (i + 1)) c) := by
      apply mass_pos w
      · exact ⟨a, Finset.mem_filter.mpr ⟨ha, hac⟩⟩
      · intro b hb
        exact hw b (Finset.mem_filter.mp hb).1
    have hfinalpos : 0 < mass w (cell E (p (i + 1)) c) := by
      have h := hlocal c
      by_contra hneg
      have hz : mass w (cell E (p (i + 1)) c) = 0 := by omega
      rw [hz, Nat.mul_zero] at h
      omega
    obtain ⟨b, hb⟩ := nonempty_of_mass_pos w hfinalpos
    obtain ⟨hbE, hbc⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_image.mpr ⟨b, hbE, hbc⟩
  exact ⟨i, hi, hstep, E, hEA, nonempty_of_mass_pos w hEpos, angle,
    hlocal, hglobal, hparent, hwhole, hwitness⟩

end ParentwiseAngularSelection
