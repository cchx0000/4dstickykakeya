import Theorems.Thm_StickyKakeya4_grid_quotient_ad

set_option autoImplicit false
set_option warningAsError true

namespace GridRichNeighborQuotient

open GridQuotientAD

noncomputable section

/-- All points over quotient labels with a rich full fiber. -/
def richRestriction {k l : ℕ} (A : Finset (Point k l)) (L : ℝ) :
    Finset (Point k l) := by
  classical
  exact A.filter fun p => L ≤ ((fiber A p.2).card : ℝ)

theorem mem_richRestriction {k l : ℕ} (A : Finset (Point k l)) (L : ℝ)
    (p : Point k l) :
    p ∈ richRestriction A L ↔ p ∈ A ∧ L ≤ ((fiber A p.2).card : ℝ) := by
  classical
  exact Finset.mem_filter

theorem richRestriction_subset {k l : ℕ} (A : Finset (Point k l)) (L : ℝ) :
    richRestriction A L ⊆ A := by
  classical
  exact Finset.filter_subset _ _

theorem mem_rich_image_iff {k l : ℕ} (A : Finset (Point k l)) (L : ℝ)
    (y : Lattice l) :
    y ∈ (richRestriction A L).image Prod.snd ↔
      y ∈ A.image Prod.snd ∧ L ≤ ((fiber A y).card : ℝ) := by
  classical
  constructor
  · intro hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    rcases Finset.mem_filter.mp hp with ⟨hpA, hpL⟩
    exact ⟨Finset.mem_image.mpr ⟨p, hpA, rfl⟩, hpL⟩
  · rintro ⟨hy, hL⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hL⟩, rfl⟩

theorem fiber_richRestriction {k l : ℕ} (A : Finset (Point k l)) (L : ℝ)
    (y : Lattice l) (hy : L ≤ ((fiber A y).card : ℝ)) :
    fiber (richRestriction A L) y = fiber A y := by
  classical
  ext p
  simp only [fiber, Finset.mem_filter, mem_richRestriction]
  constructor
  · rintro ⟨⟨hp, _hL⟩, heq⟩
    exact ⟨hp, heq⟩
  · rintro ⟨hp, heq⟩
    exact ⟨⟨hp, heq.symm ▸ hy⟩, heq⟩

theorem richRestriction_dense {k l : ℕ} (A : Finset (Point k l)) (L : ℝ) :
    ∀ y ∈ (richRestriction A L).image Prod.snd,
      L ≤ ((fiber (richRestriction A L) y).card : ℝ) := by
  intro y hy
  have hrich := ((mem_rich_image_iff A L y).mp hy).2
  rwa [fiber_richRestriction A L y hrich]

theorem ambientBox_mono {k l : ℕ} {A B : Finset (Point k l)} (hAB : A ⊆ B)
    (a : Point k l) (R : ℕ) : ambientBox A a R ⊆ ambientBox B a R := by
  exact Finset.filter_subset_filter _ hAB

theorem slab_mono {k l : ℕ} {A B : Finset (Point k l)} (hAB : A ⊆ B)
    (y : Lattice l) (R : ℕ) : slab A y R ⊆ slab B y R := by
  exact Finset.filter_subset_filter _ hAB

/-- Only upper ambient counts are inherited by restriction. -/
theorem richRestriction_ambient_upper {k l : ℕ} (A : Finset (Point k l))
    (L U : ℝ) (R : ℕ)
    (hupper : ∀ a ∈ A, ((ambientBox A a R).card : ℝ) ≤ U) :
    ∀ a ∈ richRestriction A L,
      ((ambientBox (richRestriction A L) a R).card : ℝ) ≤ U := by
  intro a ha
  have hcard : ((ambientBox (richRestriction A L) a R).card : ℝ) ≤
      ((ambientBox A a R).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (ambientBox_mono (richRestriction_subset A L) a R)
  exact hcard.trans (hupper a (richRestriction_subset A L ha))

theorem box_symmetric {l : ℕ} (x y : Lattice l) (C : ℕ)
    (hxy : x ∈ box y C) : y ∈ box x C := by
  rw [mem_box_iff] at hxy ⊢
  intro i
  simpa only [abs_sub_comm] using hxy i

theorem box_triangle {l : ℕ} (x y z : Lattice l) (R C : ℕ)
    (hxy : x ∈ box y R) (hzx : z ∈ box x C) : z ∈ box y (R + C) := by
  rw [mem_box_iff] at hxy hzx ⊢
  intro i
  rcases abs_le.mp (hxy i) with ⟨hx0, hx1⟩
  rcases abs_le.mp (hzx i) with ⟨hz0, hz1⟩
  apply abs_le.mpr
  push_cast
  constructor <;> omega

/-- Choose a rich neighbor from the original occupied quotient labels. -/
theorem exists_rich_neighbor_map {k l : ℕ} (A : Finset (Point k l)) (L : ℝ) (C : ℕ)
    (hnear : ∀ y ∈ A.image Prod.snd, ∃ z ∈ A.image Prod.snd,
      z ∈ box y C ∧ L ≤ ((fiber A z).card : ℝ)) :
    ∃ f : Lattice l → Lattice l, ∀ y ∈ A.image Prod.snd,
      f y ∈ (richRestriction A L).image Prod.snd ∧ f y ∈ box y C := by
  classical
  let f : Lattice l → Lattice l := fun y =>
    if hy : y ∈ A.image Prod.snd then (hnear y hy).choose else y
  refine ⟨f, ?_⟩
  intro y hy
  have hs := (hnear y hy).choose_spec
  simp only [f, dif_pos hy]
  exact ⟨(mem_rich_image_iff A L _).mpr ⟨hs.1, hs.2.2⟩, hs.2.1⟩

/-- Assignment multiplicity is bounded by an actual lattice `C`-box. -/
theorem neighbor_map_fiber_card_le {l : ℕ} (S : Finset (Lattice l))
    (f : Lattice l → Lattice l) (C : ℕ)
    (hnear : ∀ y ∈ S, f y ∈ box y C) (z : Lattice l) :
    (S.filter fun y => f y = z).card ≤ (2 * C + 1) ^ l := by
  rw [← box_card z C]
  apply Finset.card_le_card
  intro y hy
  rcases Finset.mem_filter.mp hy with ⟨hyS, hfy⟩
  have := box_symmetric (f y) y C (hnear y hyS)
  rwa [hfy] at this

/-- Every original quotient box maps to rich labels in radius `R+C`, with
geometrically bounded multiplicity.  Individual original fibers may be small. -/
theorem quotient_card_le_rich_neighbors {k l : ℕ}
    (A : Finset (Point k l)) (L : ℝ) (C R : ℕ) (y : Lattice l)
    (hnear : ∀ z ∈ A.image Prod.snd, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ L ≤ ((fiber A w).card : ℝ)) :
    (quotientBox A y R).card ≤
      (2 * C + 1) ^ l * (quotientBox (richRestriction A L) y (R + C)).card := by
  obtain ⟨f, hf⟩ := exists_rich_neighbor_map A L C hnear
  apply Finset.card_le_mul_card_image_of_maps_to (f := f)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzY, hzy⟩
    exact Finset.mem_filter.mpr
      ⟨(hf z hzY).1, box_triangle z y (f z) R C hzy (hf z hzY).2⟩
  · intro w _hw
    exact neighbor_map_fiber_card_le (quotientBox A y R) f C
      (fun z hz => (hf z (Finset.mem_filter.mp hz).1).2) w

/-- Exact finite mass transfer to the full original slab. -/
theorem quotient_mass_le_slab {k l : ℕ}
    (A : Finset (Point k l)) (L : ℝ) (C R : ℕ) (y : Lattice l) (hL : 0 ≤ L)
    (hnear : ∀ z ∈ A.image Prod.snd, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ L ≤ ((fiber A w).card : ℝ)) :
    L * ((quotientBox A y R).card : ℝ) ≤
      ((2 * C + 1 : ℕ) : ℝ) ^ l * ((slab A y (R + C)).card : ℝ) := by
  have htransfer : ((quotientBox A y R).card : ℝ) ≤
      ((2 * C + 1 : ℕ) : ℝ) ^ l *
        ((quotientBox (richRestriction A L) y (R + C)).card : ℝ) := by
    exact_mod_cast quotient_card_le_rich_neighbors A L C R y hnear
  have hdense := dense_fibers_le_slab (richRestriction A L) y (R + C) L
    (richRestriction_dense A L)
  have hslab : ((slab (richRestriction A L) y (R + C)).card : ℝ) ≤
      ((slab A y (R + C)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (slab_mono (richRestriction_subset A L) y (R + C))
  calc
    _ ≤ L * (((2 * C + 1 : ℕ) : ℝ) ^ l *
        ((quotientBox (richRestriction A L) y (R + C)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left htransfer hL
    _ = ((2 * C + 1 : ℕ) : ℝ) ^ l *
        (L * ((quotientBox (richRestriction A L) y (R + C)).card : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hdense.trans hslab) (by positivity)

/-- Exact geometric upper count at arbitrary radii with `1 ≤ R+C`. -/
theorem quotient_mass_le_cells {k l : ℕ}
    (A : Finset (Point k l)) (L U : ℝ) (N C R : ℕ) (y : Lattice l)
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hRC : 1 ≤ R + C)
    (hbounded : ∀ p ∈ A, ∀ i, |p.1 i| ≤ (N : ℤ))
    (hnear : ∀ z ∈ A.image Prod.snd, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ L ≤ ((fiber A w).card : ℝ))
    (hupper : ∀ a ∈ A, ((ambientBox A a (2 * (R + C))).card : ℝ) ≤ U) :
    L * ((quotientBox A y R).card : ℝ) ≤
      ((2 * C + 1 : ℕ) : ℝ) ^ l * ((2 * N / (R + C) + 1 : ℕ) : ℝ) ^ k * U := by
  have hslab := slab_card_le_cells_mul A y N (R + C) U hRC hU hbounded hupper
  calc
    _ ≤ ((2 * C + 1 : ℕ) : ℝ) ^ l * ((slab A y (R + C)).card : ℝ) :=
      quotient_mass_le_slab A L C R y hL hnear
    _ ≤ ((2 * C + 1 : ℕ) : ℝ) ^ l *
        (((2 * N / (R + C) + 1 : ℕ) : ℝ) ^ k * U) :=
      mul_le_mul_of_nonneg_left hslab (by positivity)
    _ = _ := by ring

/-- Generic finite quotient box; its labels need not be `snd(A)`. -/
def setBox {l : ℕ} (U : Finset (Lattice l)) (y : Lattice l) (R : ℕ) :=
  U.filter fun z => z ∈ box y R

theorem setBox_mono_radius {l : ℕ} (U : Finset (Lattice l)) (y : Lattice l)
    {R S : ℕ} (hRS : R ≤ S) : setBox U y R ⊆ setBox U y S := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzU, hzy⟩
  exact Finset.mem_filter.mpr ⟨hzU, box_mono y hRS hzy⟩

theorem setBox_card_le_of_near_map {l : ℕ} (U V : Finset (Lattice l))
    (f : Lattice l → Lattice l) (C R : ℕ) (y : Lattice l)
    (hf : ∀ z ∈ U, f z ∈ V ∧ f z ∈ box z C) :
    (setBox U y R).card ≤ (2 * C + 1) ^ l * (setBox V y (R + C)).card := by
  apply Finset.card_le_mul_card_image_of_maps_to (f := f)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzU, hzy⟩
    exact Finset.mem_filter.mpr
      ⟨(hf z hzU).1, box_triangle z y (f z) R C hzy (hf z hzU).2⟩
  · intro w _hw
    exact neighbor_map_fiber_card_le (setBox U y R) f C
      (fun z hz => (hf z (Finset.mem_filter.mp hz).1).2) w

theorem exists_near_map {l : ℕ} (U V : Finset (Lattice l)) (C : ℕ)
    (hnear : ∀ z ∈ U, ∃ w ∈ V, w ∈ box z C) :
    ∃ f : Lattice l → Lattice l, ∀ z ∈ U, f z ∈ V ∧ f z ∈ box z C := by
  classical
  let f : Lattice l → Lattice l := fun z =>
    if hz : z ∈ U then (hnear z hz).choose else z
  refine ⟨f, ?_⟩
  intro z hz
  simpa only [f, dif_pos hz] using (hnear z hz).choose_spec

/-- Actual upper transport when the requested quotient `U` differs from `snd(A)`. -/
theorem setBox_card_le_rich_neighbors {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l)) (L : ℝ)
    (C R : ℕ) (y : Lattice l)
    (hnear : ∀ z ∈ U, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ L ≤ ((fiber A w).card : ℝ)) :
    (setBox U y R).card ≤
      (2 * C + 1) ^ l * (quotientBox (richRestriction A L) y (R + C)).card := by
  obtain ⟨f, hf⟩ := exists_near_map U ((richRestriction A L).image Prod.snd) C (by
    intro z hz
    obtain ⟨w, hw, hwz, hrich⟩ := hnear z hz
    exact ⟨w, (mem_rich_image_iff A L w).mpr ⟨hw, hrich⟩, hwz⟩)
  exact setBox_card_le_of_near_map U ((richRestriction A L).image Prod.snd) f C R y hf

theorem setBox_mass_le_slab {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l)) (L : ℝ)
    (C R : ℕ) (y : Lattice l) (hL : 0 ≤ L)
    (hnear : ∀ z ∈ U, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ L ≤ ((fiber A w).card : ℝ)) :
    L * ((setBox U y R).card : ℝ) ≤
      ((2 * C + 1 : ℕ) : ℝ) ^ l * ((slab A y (R + C)).card : ℝ) := by
  have htransfer : ((setBox U y R).card : ℝ) ≤
      ((2 * C + 1 : ℕ) : ℝ) ^ l *
        ((quotientBox (richRestriction A L) y (R + C)).card : ℝ) := by
    exact_mod_cast setBox_card_le_rich_neighbors A U L C R y hnear
  have hdense := dense_fibers_le_slab (richRestriction A L) y (R + C) L
    (richRestriction_dense A L)
  have hslab : ((slab (richRestriction A L) y (R + C)).card : ℝ) ≤
      ((slab A y (R + C)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (slab_mono (richRestriction_subset A L) y (R + C))
  calc
    _ ≤ L * (((2 * C + 1 : ℕ) : ℝ) ^ l *
        ((quotientBox (richRestriction A L) y (R + C)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left htransfer hL
    _ = ((2 * C + 1 : ℕ) : ℝ) ^ l *
        (L * ((quotientBox (richRestriction A L) y (R + C)).card : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hdense.trans hslab) (by positivity)

theorem setBox_mass_le_cells {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l)) (L H : ℝ)
    (N C R : ℕ) (y : Lattice l)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hRC : 1 ≤ R + C)
    (hbounded : ∀ p ∈ A, ∀ i, |p.1 i| ≤ (N : ℤ))
    (hnear : ∀ z ∈ U, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ L ≤ ((fiber A w).card : ℝ))
    (hupper : ∀ a ∈ A, ((ambientBox A a (2 * (R + C))).card : ℝ) ≤ H) :
    L * ((setBox U y R).card : ℝ) ≤
      ((2 * C + 1 : ℕ) : ℝ) ^ l * ((2 * N / (R + C) + 1 : ℕ) : ℝ) ^ k * H := by
  have hslab := slab_card_le_cells_mul A y N (R + C) H hRC hH hbounded hupper
  calc
    _ ≤ ((2 * C + 1 : ℕ) : ℝ) ^ l * ((slab A y (R + C)).card : ℝ) :=
      setBox_mass_le_slab A U L C R y hL hnear
    _ ≤ ((2 * C + 1 : ℕ) : ℝ) ^ l *
        (((2 * N / (R + C) + 1 : ℕ) : ℝ) ^ k * H) :=
      mul_le_mul_of_nonneg_left hslab (by positivity)
    _ = _ := by ring

/-- Lower transport uses all ambient quotient labels, never a rich restriction. -/
theorem full_quotient_card_le_setBox {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l))
    (C R : ℕ) (y v : Lattice l) (hvy : v ∈ box y C)
    (hback : ∀ z ∈ A.image Prod.snd, ∃ w ∈ U, w ∈ box z C) :
    (quotientBox A v R).card ≤ (2 * C + 1) ^ l * (setBox U y (R + 2 * C)).card := by
  obtain ⟨f, hf⟩ := exists_near_map (A.image Prod.snd) U C hback
  have hcount := setBox_card_le_of_near_map (A.image Prod.snd) U f C R v hf
  have hsub : setBox U v (R + C) ⊆ setBox U y (R + 2 * C) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwU, hwv⟩
    apply Finset.mem_filter.mpr
    refine ⟨hwU, ?_⟩
    have h := box_triangle v y w C (R + C) hvy hwv
    simpa only [show C + (R + C) = R + 2 * C by omega] using h
  exact hcount.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))

/-- Exact lower bound about a requested quotient point with a nearby ambient witness. -/
theorem ambient_lower_le_setBox {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l)) (a : Point k l)
    (C R : ℕ) (y : Lattice l) (L : ℝ)
    (hay : a.2 ∈ box y C)
    (hback : ∀ z ∈ A.image Prod.snd, ∃ w ∈ U, w ∈ box z C)
    (hlower : L ≤ ((ambientBox A a R).card : ℝ)) :
    L ≤ ((2 * R + 1 : ℕ) : ℝ) ^ k * ((2 * C + 1 : ℕ) : ℝ) ^ l *
      ((setBox U y (R + 2 * C)).card : ℝ) := by
  have hcap : ((ambientBox A a R).card : ℝ) ≤
      ((2 * R + 1 : ℕ) : ℝ) ^ k * ((quotientBox A a.2 R).card : ℝ) := by
    exact_mod_cast ambientBox_card_le_fiber_capacity A a R
  have htransport : ((quotientBox A a.2 R).card : ℝ) ≤
      ((2 * C + 1 : ℕ) : ℝ) ^ l * ((setBox U y (R + 2 * C)).card : ℝ) := by
    exact_mod_cast full_quotient_card_le_setBox A U C R y a.2 hay hback
  calc
    L ≤ ((2 * R + 1 : ℕ) : ℝ) ^ k * ((quotientBox A a.2 R).card : ℝ) :=
      hlower.trans hcap
    _ ≤ ((2 * R + 1 : ℕ) : ℝ) ^ k *
        (((2 * C + 1 : ℕ) : ℝ) ^ l * ((setBox U y (R + 2 * C)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left htransport (by positivity)
    _ = _ := by ring

theorem cell_count_scaled_le_four (k N S : ℕ) (hSN : S ≤ 2 * N) :
    ((2 * N / S + 1 : ℕ) : ℝ) ^ k * (S : ℝ) ^ k ≤ (4 : ℝ) ^ k * (N : ℝ) ^ k := by
  have hnat : (2 * N / S + 1) * S ≤ 4 * N := by
    have := Nat.div_mul_le_self (2 * N) S
    nlinarith
  have hreal : ((2 * N / S + 1 : ℕ) : ℝ) * (S : ℝ) ≤ 4 * (N : ℝ) := by
    exact_mod_cast hnat
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hreal k

/-- Nearby rich fibers give an upper power law at the enlarged radius `R+C`. -/
theorem setBox_upper_shifted {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l))
    (N C R : ℕ) (y : Lattice l) (lam K t : ℝ)
    (hlam : 0 < lam) (hK : 0 ≤ K) (hRC : 1 ≤ R + C) (hRCN : R + C ≤ 2 * N)
    (hbounded : ∀ p ∈ A, ∀ i, |p.1 i| ≤ (N : ℤ))
    (hnear : ∀ z ∈ U, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ lam * (N : ℝ) ^ k ≤ ((fiber A w).card : ℝ))
    (hupper : ∀ a ∈ A, ((ambientBox A a (2 * (R + C))).card : ℝ) ≤
      K * ((2 * (R + C) : ℕ) : ℝ) ^ t) :
    ((setBox U y R).card : ℝ) ≤
      (((2 * C + 1 : ℕ) : ℝ) ^ l * (4 : ℝ) ^ k * (2 : ℝ) ^ t * K / lam) *
        ((R + C : ℕ) : ℝ) ^ (t - k) := by
  have hSp : (0 : ℝ) < ((R + C : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + C)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hH : 0 ≤ K * ((2 * (R + C) : ℕ) : ℝ) ^ t := by positivity
  have htotal := setBox_mass_le_cells A U (lam * (N : ℝ) ^ k)
    (K * ((2 * (R + C) : ℕ) : ℝ) ^ t) N C R y
    (by positivity) hH hRC hbounded hnear hupper
  have hscaled :
      (lam * (N : ℝ) ^ k * ((setBox U y R).card : ℝ)) * ((R + C : ℕ) : ℝ) ^ k ≤
        ((2 * C + 1 : ℕ) : ℝ) ^ l * ((4 : ℝ) ^ k * (N : ℝ) ^ k) *
          (K * ((2 * (R + C) : ℕ) : ℝ) ^ t) := by
    calc
      _ ≤ (((2 * C + 1 : ℕ) : ℝ) ^ l * ((2 * N / (R + C) + 1 : ℕ) : ℝ) ^ k *
          (K * ((2 * (R + C) : ℕ) : ℝ) ^ t)) * ((R + C : ℕ) : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right htotal (by positivity)
      _ = ((2 * C + 1 : ℕ) : ℝ) ^ l *
          (((2 * N / (R + C) + 1 : ℕ) : ℝ) ^ k * ((R + C : ℕ) : ℝ) ^ k) *
            (K * ((2 * (R + C) : ℕ) : ℝ) ^ t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cell_count_scaled_le_four k N (R + C) hRCN)
          (by positivity)) hH
  have hcancel : lam * ((setBox U y R).card : ℝ) * ((R + C : ℕ) : ℝ) ^ k ≤
      ((2 * C + 1 : ℕ) : ℝ) ^ l * (4 : ℝ) ^ k *
        (K * ((2 * (R + C) : ℕ) : ℝ) ^ t) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hNp k)).mp
    nlinarith only [hscaled]
  have hpow : ((2 * (R + C) : ℕ) : ℝ) ^ t =
      (2 : ℝ) ^ t * ((R + C : ℕ) : ℝ) ^ t := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    exact Real.mul_rpow (by norm_num) hSp.le
  rw [hpow] at hcancel
  rw [Real.rpow_sub_natCast hSp.ne']
  calc
    ((setBox U y R).card : ℝ) ≤
        (((2 * C + 1 : ℕ) : ℝ) ^ l * (4 : ℝ) ^ k * (2 : ℝ) ^ t * K *
          ((R + C : ℕ) : ℝ) ^ t) / (lam * ((R + C : ℕ) : ℝ) ^ k) := by
      apply (le_div_iff₀ (mul_pos hlam (pow_pos hSp k))).mpr
      nlinarith only [hcancel]
    _ = _ := by ring

/-- Dimension-only upper coefficient, including the small-radius range.
For `R≥1`, the exact inequality `R+C ≤ (C+1)R` controls all radii uniformly. -/
theorem setBox_upper_AD {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l))
    (N C R : ℕ) (y : Lattice l) (lam K t : ℝ)
    (hlam : 0 < lam) (hK : 0 ≤ K) (hkt : (k : ℝ) ≤ t)
    (htdim : t ≤ ((k + l : ℕ) : ℝ))
    (hR : 1 ≤ R) (hRN : R ≤ N) (hCN : C ≤ N)
    (hbounded : ∀ p ∈ A, ∀ i, |p.1 i| ≤ (N : ℤ))
    (hnear : ∀ z ∈ U, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ lam * (N : ℝ) ^ k ≤ ((fiber A w).card : ℝ))
    (hupper : ∀ a ∈ A, ((ambientBox A a (2 * (R + C))).card : ℝ) ≤
      K * ((2 * (R + C) : ℕ) : ℝ) ^ t) :
    ((setBox U y R).card : ℝ) ≤
      (((2 * C + 1 : ℕ) : ℝ) ^ l * (4 : ℝ) ^ k * (2 : ℝ) ^ (k + l) *
        ((C + 1 : ℕ) : ℝ) ^ l * K / lam) * (R : ℝ) ^ (t - k) := by
  have hRp : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hs0 : 0 ≤ t - k := sub_nonneg.mpr hkt
  have hsl : t - (k : ℝ) ≤ (l : ℝ) := by push_cast at htdim; linarith
  have h2 : (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (k + l) := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) htdim
  have hC1 : (1 : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ C + 1)
  have hCpow : ((C + 1 : ℕ) : ℝ) ^ (t - k) ≤ ((C + 1 : ℕ) : ℝ) ^ l := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hC1 hsl
  have hRC : ((R + C : ℕ) : ℝ) ≤ ((C + 1 : ℕ) : ℝ) * (R : ℝ) := by
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hC0 : (0 : ℝ) ≤ C := by positivity
    push_cast
    nlinarith
  have hrad : ((R + C : ℕ) : ℝ) ^ (t - k) ≤
      ((C + 1 : ℕ) : ℝ) ^ l * (R : ℝ) ^ (t - k) := by
    calc
      _ ≤ (((C + 1 : ℕ) : ℝ) * (R : ℝ)) ^ (t - k) :=
        Real.rpow_le_rpow (by positivity) hRC hs0
      _ = ((C + 1 : ℕ) : ℝ) ^ (t - k) * (R : ℝ) ^ (t - k) :=
        Real.mul_rpow (by positivity) hRp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hCpow (by positivity)
  have hcoeff := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2
        (by positivity : (0 : ℝ) ≤ ((2 * C + 1 : ℕ) : ℝ) ^ l * (4 : ℝ) ^ k)) hK) hlam.le
  calc
    _ ≤ (((2 * C + 1 : ℕ) : ℝ) ^ l * (4 : ℝ) ^ k * (2 : ℝ) ^ t * K / lam) *
        ((R + C : ℕ) : ℝ) ^ (t - k) :=
      setBox_upper_shifted A U N C R y lam K t hlam hK (by omega) (by omega)
        hbounded hnear hupper
    _ ≤ (((2 * C + 1 : ℕ) : ℝ) ^ l * (4 : ℝ) ^ k * (2 : ℝ) ^ (k + l) * K / lam) *
        (((C + 1 : ℕ) : ℝ) ^ l * (R : ℝ) ^ (t - k)) :=
      mul_le_mul hcoeff hrad (by positivity) (by positivity)
    _ = _ := by ring

/-- The original quotient has both AD bounds even if its own fibers are small;
only a uniformly nearby rich original fiber is required. -/
theorem original_quotient_AD {k l : ℕ}
    (A : Finset (Point k l)) (N C : ℕ) (lam c K t : ℝ)
    (hlam : 0 < lam) (hK : 0 ≤ K) (hkt : (k : ℝ) ≤ t)
    (htdim : t ≤ ((k + l : ℕ) : ℝ)) (hCN : C ≤ N)
    (hbounded : ∀ p ∈ A, ∀ i, |p.1 i| ≤ (N : ℤ))
    (hnear : ∀ z ∈ A.image Prod.snd, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ lam * (N : ℝ) ^ k ≤ ((fiber A w).card : ℝ))
    (hlower : ∀ a ∈ A, ∀ R : ℕ, 1 ≤ R → R ≤ N →
      c * (R : ℝ) ^ t ≤ ((ambientBox A a R).card : ℝ))
    (hupper : ∀ a ∈ A, ∀ S : ℕ, 1 ≤ S → S ≤ 4 * N →
      ((ambientBox A a S).card : ℝ) ≤ K * (S : ℝ) ^ t) :
    0 ≤ t - k ∧ ∀ y ∈ A.image Prod.snd, ∀ R : ℕ, 1 ≤ R → R ≤ N →
      (c / (3 : ℝ) ^ k) * (R : ℝ) ^ (t - k) ≤ ((quotientBox A y R).card : ℝ) ∧
      ((quotientBox A y R).card : ℝ) ≤
        (((2 * C + 1 : ℕ) : ℝ) ^ l * (4 : ℝ) ^ k * (2 : ℝ) ^ (k + l) *
          ((C + 1 : ℕ) : ℝ) ^ l * K / lam) * (R : ℝ) ^ (t - k) := by
  refine ⟨sub_nonneg.mpr hkt, ?_⟩
  intro y hy R hR hRN
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
  constructor
  · exact quotient_lower A a R c t hR (hlower a ha R hR hRN)
  · exact setBox_upper_AD A (A.image Prod.snd) N C R a.2 lam K t
      hlam hK hkt htdim hR hRN hCN hbounded hnear
      (fun a ha => hupper a ha (2 * (R + C)) (by omega) (by omega))

/-- At radii at least `4C`, full ambient lower AD transfers to the requested
quotient using radius `R-2C`, which is at least `R/2`. -/
theorem setBox_lower_large {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l)) (a : Point k l)
    (C R : ℕ) (y : Lattice l) (c t : ℝ)
    (hc : 0 ≤ c) (hkt : (k : ℝ) ≤ t) (htdim : t ≤ ((k + l : ℕ) : ℝ))
    (hR : 1 ≤ R) (hlarge : 4 * C ≤ R) (hay : a.2 ∈ box y C)
    (hback : ∀ z ∈ A.image Prod.snd, ∃ w ∈ U, w ∈ box z C)
    (hlower : c * ((R - 2 * C : ℕ) : ℝ) ^ t ≤
      ((ambientBox A a (R - 2 * C)).card : ℝ)) :
    (c / ((3 : ℝ) ^ k * ((2 * C + 1 : ℕ) : ℝ) ^ l * (2 : ℝ) ^ l)) *
      (R : ℝ) ^ (t - k) ≤ ((setBox U y R).card : ℝ) := by
  have hr : 1 ≤ R - 2 * C := by omega
  have hrp : (0 : ℝ) < ((R - 2 * C : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < R - 2 * C)
  have hsl : t - (k : ℝ) ≤ (l : ℝ) := by push_cast at htdim; linarith
  have h2pow : (2 : ℝ) ^ (t - k) ≤ (2 : ℝ) ^ l := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hsl
  have hRr : (R : ℝ) ≤ 2 * ((R - 2 * C : ℕ) : ℝ) := by
    exact_mod_cast (by omega : R ≤ 2 * (R - 2 * C))
  have hpower : (R : ℝ) ^ (t - k) ≤
      (2 : ℝ) ^ l * ((R - 2 * C : ℕ) : ℝ) ^ (t - k) := by
    calc
      _ ≤ (2 * ((R - 2 * C : ℕ) : ℝ)) ^ (t - k) :=
        Real.rpow_le_rpow (by positivity) hRr (sub_nonneg.mpr hkt)
      _ = (2 : ℝ) ^ (t - k) * ((R - 2 * C : ℕ) : ℝ) ^ (t - k) :=
        Real.mul_rpow (by norm_num) hrp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h2pow (by positivity)
  have htransport : ((quotientBox A a.2 (R - 2 * C)).card : ℝ) ≤
      ((2 * C + 1 : ℕ) : ℝ) ^ l * ((setBox U y R).card : ℝ) := by
    have h := full_quotient_card_le_setBox A U C (R - 2 * C) y a.2 hay hback
    rw [Nat.sub_add_cancel (by omega : 2 * C ≤ R)] at h
    exact_mod_cast h
  have hlow := (quotient_lower A a (R - 2 * C) c t hr hlower).trans htransport
  have hmain : (c / (3 : ℝ) ^ k) * (R : ℝ) ^ (t - k) ≤
      (((2 * C + 1 : ℕ) : ℝ) ^ l * (2 : ℝ) ^ l) * ((setBox U y R).card : ℝ) := by
    calc
      _ ≤ (c / (3 : ℝ) ^ k) *
          ((2 : ℝ) ^ l * ((R - 2 * C : ℕ) : ℝ) ^ (t - k)) :=
        mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = (2 : ℝ) ^ l *
          ((c / (3 : ℝ) ^ k) * ((R - 2 * C : ℕ) : ℝ) ^ (t - k)) := by ring
      _ ≤ (2 : ℝ) ^ l *
          (((2 * C + 1 : ℕ) : ℝ) ^ l * ((setBox U y R).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = _ := by ring
  calc
    _ = ((c / (3 : ℝ) ^ k) * (R : ℝ) ^ (t - k)) /
        (((2 * C + 1 : ℕ) : ℝ) ^ l * (2 : ℝ) ^ l) := by ring
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hmain])

/-- Full lower AD for a nearby requested quotient, with small radii handled
by the occupied center itself. -/
theorem setBox_lower_AD {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l)) (N C R : ℕ)
    (y : Lattice l) (c t : ℝ)
    (hc : 0 ≤ c) (hkt : (k : ℝ) ≤ t) (htdim : t ≤ ((k + l : ℕ) : ℝ))
    (hy : y ∈ U) (hR : 1 ≤ R) (hRN : R ≤ N)
    (hwitness : ∃ a ∈ A, a.2 ∈ box y C)
    (hback : ∀ z ∈ A.image Prod.snd, ∃ w ∈ U, w ∈ box z C)
    (hlower : ∀ a ∈ A, ∀ S : ℕ, 1 ≤ S → S ≤ N →
      c * (S : ℝ) ^ t ≤ ((ambientBox A a S).card : ℝ)) :
    min (c / ((3 : ℝ) ^ k * ((2 * C + 1 : ℕ) : ℝ) ^ l * (2 : ℝ) ^ l))
        (1 / ((4 * C + 1 : ℕ) : ℝ) ^ l) *
      (R : ℝ) ^ (t - k) ≤ ((setBox U y R).card : ℝ) := by
  by_cases hlarge : 4 * C ≤ R
  · obtain ⟨a, ha, hay⟩ := hwitness
    have hlocal := hlower a ha (R - 2 * C) (by omega) (by omega)
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (setBox_lower_large A U a C R y c t hc hkt htdim hR hlarge hay hback hlocal)
  · have hsmall : R ≤ 4 * C + 1 := by omega
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hsl : t - (k : ℝ) ≤ (l : ℝ) := by push_cast at htdim; linarith
    have hpower : (R : ℝ) ^ (t - k) ≤ ((4 * C + 1 : ℕ) : ℝ) ^ l := by
      calc
        _ ≤ (R : ℝ) ^ l := by
          simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hR1 hsl
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hsmall) l
    have hself : y ∈ setBox U y R := by
      apply Finset.mem_filter.mpr
      refine ⟨hy, (mem_box_iff y y R).mpr ?_⟩
      intro i
      simp
    have hcount : (1 : ℝ) ≤ ((setBox U y R).card : ℝ) := by
      have hnat : 1 ≤ (setBox U y R).card := Finset.card_pos.mpr ⟨y, hself⟩
      exact_mod_cast hnat
    calc
      _ ≤ (1 / ((4 * C + 1 : ℕ) : ℝ) ^ l) * (R : ℝ) ^ (t - k) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ 1 := by
        rw [one_div_mul_eq_div]
        apply (div_le_iff₀ (by positivity)).mpr
        simpa only [one_mul] using hpower
      _ ≤ _ := hcount

theorem nearby_lower_constant_pos (k l C : ℕ) (c : ℝ) (hc : 0 < c) :
    0 < min (c / ((3 : ℝ) ^ k * ((2 * C + 1 : ℕ) : ℝ) ^ l * (2 : ℝ) ^ l))
      (1 / ((4 * C + 1 : ℕ) : ℝ) ^ l) := by
  exact lt_min (by positivity) (by positivity)

/-- Two possibly different coarse quotient sets have genuine AD bounds when
the requested set has nearby rich ambient fibers and the full ambient quotient
has nearby requested labels.  No lower estimate of a rich restriction is used. -/
theorem nearby_quotient_AD {k l : ℕ}
    (A : Finset (Point k l)) (U : Finset (Lattice l)) (N C : ℕ) (lam c K t : ℝ)
    (hlam : 0 < lam) (hc : 0 ≤ c) (hK : 0 ≤ K) (hkt : (k : ℝ) ≤ t)
    (htdim : t ≤ ((k + l : ℕ) : ℝ)) (hCN : C ≤ N)
    (hbounded : ∀ p ∈ A, ∀ i, |p.1 i| ≤ (N : ℤ))
    (hnear : ∀ z ∈ U, ∃ w ∈ A.image Prod.snd,
      w ∈ box z C ∧ lam * (N : ℝ) ^ k ≤ ((fiber A w).card : ℝ))
    (hback : ∀ z ∈ A.image Prod.snd, ∃ w ∈ U, w ∈ box z C)
    (hlower : ∀ a ∈ A, ∀ R : ℕ, 1 ≤ R → R ≤ N →
      c * (R : ℝ) ^ t ≤ ((ambientBox A a R).card : ℝ))
    (hupper : ∀ a ∈ A, ∀ S : ℕ, 1 ≤ S → S ≤ 4 * N →
      ((ambientBox A a S).card : ℝ) ≤ K * (S : ℝ) ^ t) :
    0 ≤ t - k ∧ ∀ y ∈ U, ∀ R : ℕ, 1 ≤ R → R ≤ N →
      min (c / ((3 : ℝ) ^ k * ((2 * C + 1 : ℕ) : ℝ) ^ l * (2 : ℝ) ^ l))
          (1 / ((4 * C + 1 : ℕ) : ℝ) ^ l) *
        (R : ℝ) ^ (t - k) ≤ ((setBox U y R).card : ℝ) ∧
      ((setBox U y R).card : ℝ) ≤
        (((2 * C + 1 : ℕ) : ℝ) ^ l * (4 : ℝ) ^ k * (2 : ℝ) ^ (k + l) *
          ((C + 1 : ℕ) : ℝ) ^ l * K / lam) * (R : ℝ) ^ (t - k) := by
  refine ⟨sub_nonneg.mpr hkt, ?_⟩
  intro y hy R hR hRN
  constructor
  · apply setBox_lower_AD A U N C R y c t hc hkt htdim hy hR hRN ?_ hback hlower
    obtain ⟨v, hv, hvy, _hrich⟩ := hnear y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨a, ha, hvy⟩
  · exact setBox_upper_AD A U N C R y lam K t hlam hK hkt htdim hR hRN hCN
      hbounded hnear (fun a ha => hupper a ha (2 * (R + C)) (by omega) (by omega))

end
end GridRichNeighborQuotient
