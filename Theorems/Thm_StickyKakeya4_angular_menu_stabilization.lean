import Theorems.Thm_StickyKakeya4_compatible_tuple_selection

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1800000

namespace AngularMenuStabilization

open SelfUniform CompatibleTupleSelection

variable {α σ τ : Type*} [DecidableEq σ] [DecidableEq τ]

def cell (A : Finset α) (p : α → σ) (c : σ) : Finset α := A.filter (fun a => p a = c)

def menu (A : Finset α) (p : α → σ) (θ : α → τ) (c : σ) : Finset τ := (cell A p c).image θ

def joint (A : Finset α) (p : α → σ) (θ : α → τ) (c : σ) (u : τ) : Finset α :=
  A.filter (fun a => p a = c ∧ θ a = u)

def maxMenu (A : Finset α) (p : α → σ) (θ : α → τ) : ℕ :=
  (A.image p).sup (fun c => (menu A p θ c).card)

lemma cell_mass_partition (w : α → ℕ) (A : Finset α) (p : α → σ) (θ : α → τ) (c : σ) :
    mass w (cell A p c) = ∑ u ∈ menu A p θ c, mass w (joint A p θ c u) := by
  simpa only [cell, menu, joint, Finset.filter_filter] using
    mass_eq_sum_partition w (cell A p c) θ

lemma menu_card_le_max (A : Finset α) (p : α → σ) (θ : α → τ) (c : σ) :
    (menu A p θ c).card ≤ maxMenu A p θ := by
  by_cases hc : c ∈ A.image p
  · exact Finset.le_sup (s := A.image p) (f := fun c => (menu A p θ c).card) hc
  · have he : menu A p θ c = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨a, ha, _hu⟩ := Finset.mem_image.mp hu
      obtain ⟨haA, hac⟩ := Finset.mem_filter.mp ha
      exact hc (Finset.mem_image.mpr ⟨a, haA, hac⟩)
    rw [he]
    exact Nat.zero_le _

lemma maxMenu_pos (A : Finset α) (p : α → σ) (θ : α → τ) (hne : A.Nonempty) :
    0 < maxMenu A p θ := by
  obtain ⟨a, ha⟩ := hne
  have hm : (menu A p θ (p a)).Nonempty :=
    ⟨θ a, Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩, rfl⟩⟩
  exact (Finset.card_pos.mpr hm).trans_le (menu_card_le_max A p θ (p a))

lemma maxMenu_le_angular_menu (A : Finset α) (p : α → σ) (θ : α → τ) :
    maxMenu A p θ ≤ (A.image θ).card := by
  apply Finset.sup_le
  intro c _hc
  exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

/-- Actual nested cells on the SAME original point set give monotone maximum
angular menus. No comparison between independently refined sets is used. -/
lemma maxMenu_mono (A : Finset α) (p q : α → σ) (θ : α → τ)
    (hnested : ∀ a b, a ∈ A → b ∈ A → p a = p b → q a = q b) :
    maxMenu A p θ ≤ maxMenu A q θ := by
  apply Finset.sup_le
  intro c hc
  obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp hc
  have hsub : menu A p θ c ⊆ menu A q θ (q a) := by
    intro u hu
    obtain ⟨b, hb, hθb⟩ := Finset.mem_image.mp hu
    obtain ⟨hbA, hpb⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_image.mpr ⟨b,
      Finset.mem_filter.mpr ⟨hbA, hnested b a hbA ha (hpb.trans hpa.symm)⟩, hθb⟩
  exact (Finset.card_le_card hsub).trans (menu_card_le_max A q θ (q a))

/-- Spatial mass comparison and JOINT spatial-angular mass comparison imply
menu-cardinality comparison by summing actual joint classes. A positive
maximum joint-class mass is constructed from the original finite set. -/
theorem occupied_menu_card_comparison (w : α → ℕ) (A : Finset α)
    (p : α → σ) (θ : α → τ) (Kₛ Kⱼ : ℕ) (hne : A.Nonempty)
    (hw : ∀ a ∈ A, 0 < w a)
    (hspatial : ∀ a b, a ∈ A → b ∈ A →
      mass w (cell A p (p a)) ≤ Kₛ * mass w (cell A p (p b)))
    (hjoint : ∀ a b, a ∈ A → b ∈ A →
      mass w (joint A p θ (p a) (θ a)) ≤ Kⱼ * mass w (joint A p θ (p b) (θ b)))
    {c e : σ} (hc : c ∈ A.image p) (he : e ∈ A.image p) :
    (menu A p θ c).card ≤ Kₛ * Kⱼ * (menu A p θ e).card := by
  classical
  obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image A
    (fun a => mass w (joint A p θ (p a) (θ a))) hne
  let M := mass w (joint A p θ (p r) (θ r))
  have hM : 0 < M := mass_pos w
    ⟨r, Finset.mem_filter.mpr ⟨hr, rfl, rfl⟩⟩
    (fun a ha => hw a (Finset.mem_filter.mp ha).1)
  have hlow : (menu A p θ c).card * M ≤ Kⱼ * mass w (cell A p c) := by
    calc
      (menu A p θ c).card * M = ∑ _u ∈ menu A p θ c, M := by simp
      _ ≤ ∑ u ∈ menu A p θ c, Kⱼ * mass w (joint A p θ c u) := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨a, ha, hθa⟩ := Finset.mem_image.mp hu
        obtain ⟨haA, hpa⟩ := Finset.mem_filter.mp ha
        simpa only [M, hpa, hθa] using hjoint r a hr haA
      _ = Kⱼ * mass w (cell A p c) := by rw [← Finset.mul_sum, ← cell_mass_partition]
  have hupp : mass w (cell A p e) ≤ (menu A p θ e).card * M := by
    calc
      mass w (cell A p e) = ∑ u ∈ menu A p θ e, mass w (joint A p θ e u) :=
        cell_mass_partition w A p θ e
      _ ≤ ∑ _u ∈ menu A p θ e, M := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨a, ha, hθa⟩ := Finset.mem_image.mp hu
        obtain ⟨haA, hpa⟩ := Finset.mem_filter.mp ha
        simpa only [M, hpa, hθa] using hmax a haA
      _ = (menu A p θ e).card * M := by simp
  obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp hc
  obtain ⟨b, hb, hpb⟩ := Finset.mem_image.mp he
  have hspace : mass w (cell A p c) ≤ Kₛ * mass w (cell A p e) := by
    simpa only [hpa, hpb] using hspatial a b ha hb
  apply Nat.le_of_mul_le_mul_right (c := M) _ hM
  calc
    (menu A p θ c).card * M ≤ Kⱼ * mass w (cell A p c) := hlow
    _ ≤ Kⱼ * (Kₛ * mass w (cell A p e)) := Nat.mul_le_mul_left _ hspace
    _ ≤ Kⱼ * (Kₛ * ((menu A p θ e).card * M)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hupp)
    _ = (Kₛ * Kⱼ * (menu A p θ e).card) * M := by ring

lemma maxMenu_le_occupied_menu (w : α → ℕ) (A : Finset α)
    (p : α → σ) (θ : α → τ) (Kₛ Kⱼ : ℕ) (hne : A.Nonempty)
    (hw : ∀ a ∈ A, 0 < w a)
    (hspatial : ∀ a b, a ∈ A → b ∈ A →
      mass w (cell A p (p a)) ≤ Kₛ * mass w (cell A p (p b)))
    (hjoint : ∀ a b, a ∈ A → b ∈ A →
      mass w (joint A p θ (p a) (θ a)) ≤ Kⱼ * mass w (joint A p θ (p b) (θ b)))
    {c : σ} (hc : c ∈ A.image p) :
    maxMenu A p θ ≤ Kₛ * Kⱼ * (menu A p θ c).card := by
  apply Finset.sup_le
  intro e he
  exact occupied_menu_card_comparison w A p θ Kₛ Kⱼ hne hw hspatial hjoint he hc

/-- A finite angular-menu budget forces an adjacent growth ratio at most B.
Monotonicity is not an extra hypothesis of this numerical implication. -/
lemma adjacent_growth_step (D : ℕ → ℕ) (B m : ℕ) (hm : 0 < m)
    (hD₀ : 1 ≤ D 0) (hDm : D m ≤ B ^ m) :
    ∃ i < m, D (i + 1) ≤ B * D i := by
  by_contra h
  push Not at h
  have hg : ∀ i, i ≤ m → B ^ i ≤ D i := by
    intro i
    induction i with
    | zero =>
      intro _hi
      simpa using hD₀
    | succ i ih =>
      intro hi
      calc
        B ^ (i + 1) = B * B ^ i := by rw [pow_succ]; ring
        _ ≤ B * D i := Nat.mul_le_mul_left _ (ih (by omega))
        _ ≤ D (i + 1) := Nat.le_of_lt (h i (by omega))
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hlast : B ^ (n + 1) < D (n + 1) := by
    calc
      B ^ (n + 1) = B * B ^ n := by rw [pow_succ]; ring
      _ ≤ B * D n := Nat.mul_le_mul_left _ (hg n (by omega))
      _ < D (n + 1) := h n (by omega)
  change D (n + 1) ≤ B ^ (n + 1) at hDm
  exact (Nat.not_lt_of_ge hDm) hlast

/-- Stabilize actual angular menus on one fixed finite original point set.
Both required partition-mass comparisons refer to this SAME set. Menu
comparability, the adjacent scale pair, and the common angular choices are
all derived. The retained set is a union of WHOLE original fine-cell fibers,
and every retained child has a genuine retained point witnessing its parent's
chosen angular bin.

The temporary cell weights are sums of original weights. The final labels and
weights are unchanged, and the total loss is `Kₛ * Kⱼ * B`. -/
theorem stabilize_and_select (w : α → ℕ) (A : Finset α)
    (p : ℕ → α → σ) (θ : α → τ) (Kₛ Kⱼ B m : ℕ)
    (hm : 0 < m) (hne : A.Nonempty) (hw : ∀ a ∈ A, 0 < w a)
    (hnested : ∀ i, i < m → ∀ a b, a ∈ A → b ∈ A → p i a = p i b → p (i + 1) a = p (i + 1) b)
    (hspatial : ∀ i, i ≤ m → ∀ a b, a ∈ A → b ∈ A →
      mass w (cell A (p i) (p i a)) ≤ Kₛ * mass w (cell A (p i) (p i b)))
    (hjoint : ∀ i, i ≤ m → ∀ a b, a ∈ A → b ∈ A →
      mass w (joint A (p i) θ (p i a) (θ a)) ≤ Kⱼ * mass w (joint A (p i) θ (p i b) (θ b)))
    (hbudget : (A.image θ).card ≤ B ^ m) :
    (∀ j, j < m → maxMenu A (p j) θ ≤ maxMenu A (p (j + 1)) θ) ∧
    ∃ i < m,
      maxMenu A (p (i + 1)) θ ≤ B * maxMenu A (p i) θ ∧
      (∀ c ∈ A.image (p i), maxMenu A (p i) θ ≤ Kₛ * Kⱼ * (menu A (p i) θ c).card) ∧
      ∃ E ⊆ A, E.Nonempty ∧
        mass w A ≤ Kₛ * Kⱼ * B * mass w E ∧
        (∀ a b, a ∈ E → b ∈ A → p i b = p i a → b ∈ E) ∧
        ∃ angle : σ → τ, ∀ a ∈ E,
          ∃ b ∈ E, p i b = p i a ∧ θ b = angle (p (i + 1) a) := by
  classical
  refine ⟨fun j hj => maxMenu_mono A (p j) (p (j + 1)) θ (hnested j hj), ?_⟩
  obtain ⟨i, hi, hstep⟩ := adjacent_growth_step (fun j => maxMenu A (p j) θ) B m hm
    (maxMenu_pos A (p 0) θ hne) ((maxMenu_le_angular_menu A (p m) θ).trans hbudget)
  have hcompare : ∀ c ∈ A.image (p i),
      maxMenu A (p i) θ ≤ Kₛ * Kⱼ * (menu A (p i) θ c).card := by
    intro c hc
    exact maxMenu_le_occupied_menu w A (p i) θ Kₛ Kⱼ hne hw
      (hspatial i (by omega)) (hjoint i (by omega)) hc
  refine ⟨i, hi, hstep, hcompare, ?_⟩
  let I := A.image (p i)
  let W : σ → ℕ := fun c => mass w (cell A (p i) c)
  let G : σ → Finset τ := menu A (p i) θ
  obtain ⟨a₀, ha₀⟩ := hne
  let : Nonempty α := ⟨a₀⟩
  let rep : σ → α := fun c => Classical.epsilon (fun a => a ∈ A ∧ p i a = c)
  have hrep : ∀ c ∈ I, rep c ∈ A ∧ p i (rep c) = c := by
    intro c hc
    exact Classical.epsilon_spec (Finset.mem_image.mp hc)
  let parent : σ → σ := fun c => p (i + 1) (rep c)
  have hparent : ∀ a ∈ A, parent (p i a) = p (i + 1) a := by
    intro a ha
    have hr := hrep (p i a) (Finset.mem_image_of_mem (p i) ha)
    exact hnested i hi (rep (p i a)) a hr.1 ha hr.2
  have hroot : ∀ t,
      (((goodPairs I G).filter (fun z => parent z.1 = t)).image (fun z => z.2)).card ≤
        maxMenu A (p (i + 1)) θ := by
    intro t
    have hsub : ((goodPairs I G).filter (fun z => parent z.1 = t)).image (fun z => z.2) ⊆
        menu A (p (i + 1)) θ t := by
      intro u hu
      obtain ⟨z, hz, hzu⟩ := Finset.mem_image.mp hu
      obtain ⟨hzGood, hzparent⟩ := Finset.mem_filter.mp hz
      obtain ⟨_hzI, hzG⟩ := (mem_goodPairs I G z).mp hzGood
      obtain ⟨a, haCell, hθa⟩ := Finset.mem_image.mp hzG
      obtain ⟨haA, hpa⟩ := Finset.mem_filter.mp haCell
      have hp := hparent a haA
      rw [hpa] at hp
      exact Finset.mem_image.mpr ⟨a,
        Finset.mem_filter.mpr ⟨haA, hp.symm.trans hzparent⟩, hθa.trans hzu⟩
    exact (Finset.card_le_card hsub).trans (menu_card_le_max A (p (i + 1)) θ t)
  obtain ⟨Pairs, hPairs, S, _hSI, hS, _hinj, _hpairMass, hselected, hcompatible⟩ :=
    weighted_good_tuple_family_selection W I G (fun _ => parent) (fun _ u => u)
      (fun _ => maxMenu A (p (i + 1)) θ) 0
      (by intro j hj; omega) hroot (by intro j hj; omega) (fun _ => rfl)
  have hselected' : (∑ c ∈ I, W c * (G c).card) ≤
      maxMenu A (p (i + 1)) θ * mass W S := by simpa using hselected
  let E := S.biUnion (cell A (p i))
  have hdisj : Set.PairwiseDisjoint (↑S) (cell A (p i)) := by
    intro c _hc e _he hce
    apply Finset.disjoint_left.mpr
    intro a hac hae
    exact hce ((Finset.mem_filter.mp hac).2.symm.trans (Finset.mem_filter.mp hae).2)
  have hEmass : mass w E = mass W S := Finset.sum_biUnion hdisj
  have hEA : E ⊆ A := by
    intro a ha
    obtain ⟨c, _hc, hac⟩ := Finset.mem_biUnion.mp ha
    exact (Finset.mem_filter.mp hac).1
  have hwhole : ∀ a b, a ∈ E → b ∈ A → p i b = p i a → b ∈ E := by
    intro a b ha hb hba
    obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨c, hc,
      Finset.mem_filter.mpr ⟨hb, hba.trans (Finset.mem_filter.mp hac).2⟩⟩
  have htotal : mass w A = mass W I := mass_eq_sum_partition w A (p i)
  have hpairLower : maxMenu A (p i) θ * mass w A ≤
      (Kₛ * Kⱼ) * (∑ c ∈ I, W c * (G c).card) := by
    rw [htotal]
    calc
      maxMenu A (p i) θ * mass W I = ∑ c ∈ I, W c * maxMenu A (p i) θ := by
        simp only [mass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _hc
        exact Nat.mul_comm _ _
      _ ≤ ∑ c ∈ I, W c * ((Kₛ * Kⱼ) * (G c).card) :=
        Finset.sum_le_sum (fun c hc => Nat.mul_le_mul_left _ (hcompare c hc))
      _ = (Kₛ * Kⱼ) * (∑ c ∈ I, W c * (G c).card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _hc
        ring
  have hret : mass w A ≤ Kₛ * Kⱼ * B * mass w E := by
    apply Nat.le_of_mul_le_mul_right (c := maxMenu A (p i) θ) _ (maxMenu_pos A (p i) θ ⟨a₀, ha₀⟩)
    calc
      mass w A * maxMenu A (p i) θ = maxMenu A (p i) θ * mass w A := Nat.mul_comm _ _
      _ ≤ (Kₛ * Kⱼ) * (∑ c ∈ I, W c * (G c).card) := hpairLower
      _ ≤ (Kₛ * Kⱼ) * (maxMenu A (p (i + 1)) θ * mass W S) := Nat.mul_le_mul_left _ hselected'
      _ ≤ (Kₛ * Kⱼ) * ((B * maxMenu A (p i) θ) * mass W S) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hstep)
      _ = (Kₛ * Kⱼ * B * mass w E) * maxMenu A (p i) θ := by rw [hEmass]; ring
  have hEpos : 0 < mass w E := by
    have hApos := mass_pos w ⟨a₀, ha₀⟩ hw
    by_contra h
    have hz : mass w E = 0 := by omega
    rw [hz, Nat.mul_zero] at hret
    omega
  have hpairFor : ∀ a ∈ E, ∃ z ∈ Pairs, z.1 = p i a := by
    intro a ha
    obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
    rw [hS] at hc
    obtain ⟨z, hz, hzc⟩ := Finset.mem_image.mp hc
    exact ⟨z, hz, hzc.trans (Finset.mem_filter.mp hac).2.symm⟩
  let : Nonempty (σ × τ) := ⟨(p i a₀, θ a₀)⟩
  let picked : σ → σ × τ := fun t => Classical.epsilon (fun z => z ∈ Pairs ∧ parent z.1 = t)
  let angle : σ → τ := fun t => (picked t).2
  refine ⟨E, hEA, nonempty_of_mass_pos w hEpos, hret, hwhole, angle, ?_⟩
  intro a ha
  obtain ⟨z, hz, hza⟩ := hpairFor a ha
  have hzparent : parent z.1 = p (i + 1) a := by rw [hza]; exact hparent a (hEA ha)
  have hex : ∃ z : σ × τ, z ∈ Pairs ∧ parent z.1 = p (i + 1) a := ⟨z, hz, hzparent⟩
  have hchosen : picked (p (i + 1) a) ∈ Pairs ∧ parent (picked (p (i + 1) a)).1 = p (i + 1) a :=
    Classical.epsilon_spec hex
  have hangle : z.2 = angle (p (i + 1) a) :=
    hcompatible 0 (by omega) z (picked (p (i + 1) a)) hz hchosen.1 (hzparent.trans hchosen.2.symm)
  have hzG := ((mem_goodPairs I G z).mp (hPairs hz)).2
  obtain ⟨b, hbCell, hθb⟩ := Finset.mem_image.mp hzG
  obtain ⟨hbA, hpb⟩ := Finset.mem_filter.mp hbCell
  have hba : p i b = p i a := hpb.trans hza
  exact ⟨b, hwhole a b ha hbA hba, hba, hθb.trans hangle⟩

end AngularMenuStabilization
