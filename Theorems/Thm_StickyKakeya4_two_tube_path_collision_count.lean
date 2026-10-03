import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1400000

namespace TwoTubePathCollisionCount

variable {P T : Type*} [DecidableEq P] [DecidableEq T]

def points (I : Finset (P × T)) : Finset P := I.image Prod.fst

def tubes (I : Finset (P × T)) : Finset T := I.image Prod.snd

/-- Original point and tube labels of a four-edge, two-tube incidence walk.
Repeated vertices and tubes are allowed; no time separation is asserted. -/
structure Path (P T : Type*) where
  point₀ : P
  tube₁ : T
  point₁ : P
  tube₂ : T
  point₂ : P
  deriving DecidableEq

/-- A half-walk from the central point `p` through an original tube to an
original outer point, represented by its outer incidence `(point, tube)`. -/
def halfPaths (I : Finset (P × T)) (p : P) : Finset (P × T) :=
  I.filter (fun e => (p, e.2) ∈ I)

def tubeDegree (I : Finset (P × T)) (t : T) : ℕ :=
  ((points I).filter (fun p => (p, t) ∈ I)).card

def pathEmbedding : (Σ _ : P, (P × T) × (P × T)) ↪ Path P T where
  toFun x := ⟨x.2.1.1, x.2.1.2, x.1, x.2.2.2, x.2.2.1⟩
  inj' := by
    rintro ⟨m, ⟨p, s⟩, ⟨r, t⟩⟩ ⟨m', ⟨p', s'⟩, ⟨r', t'⟩⟩ h
    simp only [Path.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl

/-- The actual finite set of all four-edge walks in the given incidence set. -/
def paths (I : Finset (P × T)) : Finset (Path P T) :=
  ((points I).sigma (fun p => (halfPaths I p).product (halfPaths I p))).map pathEmbedding

@[simp] theorem mem_paths (I : Finset (P × T)) (a : Path P T) :
    a ∈ paths I ↔ (a.point₀, a.tube₁) ∈ I ∧ (a.point₁, a.tube₁) ∈ I ∧
      (a.point₁, a.tube₂) ∈ I ∧ (a.point₂, a.tube₂) ∈ I := by
  constructor
  · intro h
    obtain ⟨⟨m, ⟨p, s⟩, ⟨r, t⟩⟩, hz, rfl⟩ := Finset.mem_map.mp h
    obtain ⟨_hm, hpair⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hl, hr⟩ := Finset.mem_product.mp hpair
    obtain ⟨hlI, hmI⟩ := Finset.mem_filter.mp hl
    obtain ⟨hrI, hmI'⟩ := Finset.mem_filter.mp hr
    exact ⟨hlI, hmI, hmI', hrI⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨a.point₁, (a.point₀, a.tube₁), (a.point₂, a.tube₂)⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_image_of_mem Prod.fst h₁, ?_⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨h₀, h₁⟩, Finset.mem_filter.mpr ⟨h₃, h₂⟩⟩
    · cases a
      rfl

lemma tubeDegree_eq_fiber_card (I : Finset (P × T)) (t : T) :
    tubeDegree I t = (I.filter (fun e => e.2 = t)).card := by
  apply Finset.card_bij (fun p _hp => (p, t))
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).2, rfl⟩
  · intro p _hp q _hq hpq
    exact congrArg Prod.fst hpq
  · rintro ⟨p, u⟩ he
    obtain ⟨heI, hut⟩ := Finset.mem_filter.mp he
    change u = t at hut
    subst u
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem Prod.fst heI, heI⟩, rfl⟩

lemma card_incidence_eq_sum_tubeDegree (I : Finset (P × T)) :
    I.card = ∑ t ∈ tubes I, tubeDegree I t := by
  simpa only [tubes, tubeDegree_eq_fiber_card] using
    Finset.card_eq_sum_card_image Prod.snd I

/-- Count ordered same-fiber pairs by first summing the fiber size at each
original element, or by summing squared fiber sizes over occupied labels. -/
lemma sum_fiber_card_eq_sum_sq {α β : Type*} [DecidableEq β]
    (A : Finset α) (f : α → β) :
    (∑ a ∈ A, (A.filter (fun b => f b = f a)).card) =
      ∑ u ∈ A.image f, (A.filter (fun a => f a = u)).card ^ 2 := by
  simpa only [Finset.sum_const, Nat.nsmul_eq_mul, ← pow_two] using
    (Finset.sum_fiberwise_of_maps_to' (s := A) (t := A.image f) (g := f)
      (fun a ha => Finset.mem_image_of_mem f ha)
      (fun u => (A.filter (fun a => f a = u)).card)).symm

lemma sum_halfPaths_eq_sum_tubeDegree_sq (I : Finset (P × T)) :
    (∑ p ∈ points I, (halfPaths I p).card) = ∑ t ∈ tubes I, tubeDegree I t ^ 2 := by
  calc
    (∑ p ∈ points I, (halfPaths I p).card) = ∑ e ∈ I, tubeDegree I e.2 := by
      simp only [halfPaths, tubeDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ = ∑ t ∈ tubes I, tubeDegree I t ^ 2 := by
      simpa only [tubes, tubeDegree_eq_fiber_card] using
        sum_fiber_card_eq_sum_sq I Prod.snd

lemma card_paths_eq_sum_halfPaths_sq (I : Finset (P × T)) :
    (paths I).card = ∑ p ∈ points I, (halfPaths I p).card ^ 2 := by
  simp only [paths, Finset.card_map, Finset.card_sigma, Finset.product_eq_sprod, Finset.card_product, pow_two]

lemma nat_sum_sq_le_card_mul_sum_sq {α : Type*} (A : Finset α) (f : α → ℕ) :
    (∑ a ∈ A, f a) ^ 2 ≤ A.card * ∑ a ∈ A, f a ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℕ)) f

/-- Two applications of finite Cauchy-Schwarz give the genuine incidence-walk
count, without any degree lower bound or nonempty-set assumption. -/
theorem fourth_power_walk_bound (I : Finset (P × T)) :
    I.card ^ 4 ≤ (points I).card * (tubes I).card ^ 2 * (paths I).card := by
  have ht : I.card ^ 2 ≤ (tubes I).card * ∑ p ∈ points I, (halfPaths I p).card := by
    rw [card_incidence_eq_sum_tubeDegree, sum_halfPaths_eq_sum_tubeDegree_sq]
    exact nat_sum_sq_le_card_mul_sum_sq (tubes I) (tubeDegree I)
  have hp : (∑ p ∈ points I, (halfPaths I p).card) ^ 2 ≤
      (points I).card * (paths I).card := by
    rw [card_paths_eq_sum_halfPaths_sq]
    exact nat_sum_sq_le_card_mul_sum_sq (points I) (fun p => (halfPaths I p).card)
  calc
    I.card ^ 4 = (I.card ^ 2) ^ 2 := by ring
    _ ≤ ((tubes I).card * ∑ p ∈ points I, (halfPaths I p).card) ^ 2 :=
      Nat.pow_le_pow_left ht 2
    _ = (tubes I).card ^ 2 * (∑ p ∈ points I, (halfPaths I p).card) ^ 2 := by ring
    _ ≤ (tubes I).card ^ 2 * ((points I).card * (paths I).card) :=
      Nat.mul_le_mul_left _ hp
    _ = (points I).card * (tubes I).card ^ 2 * (paths I).card := by ring

/-- The same estimate for any specified ambient original point and tube sets. -/
theorem fourth_power_walk_bound_of_subset (I : Finset (P × T))
    (P₀ : Finset P) (T₀ : Finset T) (hI : I ⊆ P₀.product T₀) :
    I.card ^ 4 ≤ P₀.card * T₀.card ^ 2 * (paths I).card := by
  have hP : (points I).card ≤ P₀.card := Finset.card_le_card (by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_product.mp (hI he)).1)
  have hT : (tubes I).card ≤ T₀.card := Finset.card_le_card (by
    intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_product.mp (hI he)).2)
  exact (fourth_power_walk_bound I).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul hP (Nat.pow_le_pow_left hT 2)))

/-- Ordered pairs of original objects that have exactly the same chosen label. -/
def collisions {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (g : α → β) : Finset (α × α) :=
  (A.product A).filter (fun z => g z.1 = g z.2)

@[simp] theorem mem_collisions {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (g : α → β) (z : α × α) :
    z ∈ collisions A g ↔ z.1 ∈ A ∧ z.2 ∈ A ∧ g z.1 = g z.2 := by
  simp only [collisions, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, and_assoc]

lemma card_collisions_eq_sum_fiber_sq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (g : α → β) :
    (collisions A g).card = ∑ u ∈ A.image g, (A.filter (fun a => g a = u)).card ^ 2 := by
  calc
    (collisions A g).card = ∑ a ∈ A, (A.filter (fun b => g b = g a)).card := by
      simp only [collisions, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [eq_comm]
    _ = ∑ u ∈ A.image g, (A.filter (fun a => g a = u)).card ^ 2 :=
      sum_fiber_card_eq_sum_sq A g

/-- Finite Cauchy on the occupied label fibers constructs and counts collisions.
The diagonal and all other ordered colliding pairs are included. -/
theorem square_card_le_image_mul_collisions {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (g : α → β) :
    A.card ^ 2 ≤ (A.image g).card * (collisions A g).card := by
  rw [Finset.card_eq_sum_card_image g A, card_collisions_eq_sum_fiber_sq]
  exact nat_sum_sq_le_card_mul_sum_sq (A.image g) (fun u => (A.filter (fun a => g a = u)).card)

/-- The eighth-power combinatorial input: genuine original-label incidence
walks are first counted, then paired by an arbitrary finite collision label.
The label-image estimate is the only caller-supplied counting hypothesis.
No nondegenerate times or geometric W-tuple conditions are inferred. -/
theorem eighth_power_collision_bound {Z Λ : Type*} [DecidableEq Λ]
    (I : Finset (P × T)) (P₀ : Finset P) (T₀ : Finset T)
    (Z₀ : Finset Z) (M : ℕ) (g : Path P T → Λ)
    (hI : I ⊆ P₀.product T₀)
    (hlabel : ((paths I).image g).card ≤ P₀.card * Z₀.card ^ 2 * M) :
    I.card ^ 8 ≤ P₀.card ^ 3 * T₀.card ^ 4 * Z₀.card ^ 2 * M *
      (collisions (paths I) g).card := by
  have hw := fourth_power_walk_bound_of_subset I P₀ T₀ hI
  have hc := square_card_le_image_mul_collisions (paths I) g
  calc
    I.card ^ 8 = (I.card ^ 4) ^ 2 := by ring
    _ ≤ (P₀.card * T₀.card ^ 2 * (paths I).card) ^ 2 := Nat.pow_le_pow_left hw 2
    _ = P₀.card ^ 2 * T₀.card ^ 4 * (paths I).card ^ 2 := by ring
    _ ≤ P₀.card ^ 2 * T₀.card ^ 4 *
        (((paths I).image g).card * (collisions (paths I) g).card) := Nat.mul_le_mul_left _ hc
    _ ≤ P₀.card ^ 2 * T₀.card ^ 4 *
        ((P₀.card * Z₀.card ^ 2 * M) * (collisions (paths I) g).card) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlabel)
    _ = P₀.card ^ 3 * T₀.card ^ 4 * Z₀.card ^ 2 * M *
        (collisions (paths I) g).card := by ring

end TwoTubePathCollisionCount
