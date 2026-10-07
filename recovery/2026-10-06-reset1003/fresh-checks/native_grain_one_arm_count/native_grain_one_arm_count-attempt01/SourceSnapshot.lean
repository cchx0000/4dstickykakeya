import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

noncomputable section
open Classical Finset

namespace NativeGrainOneArmCount
open TwoTubePathCollisionCount
variable {P T G H X A : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq G]
  [DecidableEq H] [DecidableEq X] [DecidableEq A]

/-- A marked half-path retains its middle point and its original outer
incidence. No geometric image or conditional law is substituted. -/
def halfEmbedding : (Σ _ : P, P × T) ↪ (P × (P × T)) where
  toFun x := (x.1,x.2)
  inj' := by rintro ⟨p,e⟩ ⟨q,f⟩ h; cases h; rfl

def halves (I : Finset (P × T)) : Finset (P × (P × T)) :=
  ((points I).sigma (halfPaths I)).map halfEmbedding

@[simp] theorem mem_halves (I : Finset (P × T)) (x : P × (P × T)) :
    x ∈ halves I ↔ x.2 ∈ I ∧ (x.1,x.2.2) ∈ I := by
  rcases x with ⟨p,e⟩
  constructor
  · intro h
    obtain ⟨⟨q,f⟩,hf,heq⟩ := mem_map.mp h
    change (q,f)=(p,e) at heq
    cases heq
    exact mem_filter.mp (mem_sigma.mp hf).2
  · rintro ⟨he,hp⟩
    apply mem_map.mpr
    exact ⟨⟨p,e⟩,mem_sigma.mpr ⟨mem_image_of_mem Prod.fst hp,
      mem_filter.mpr ⟨he,hp⟩⟩,rfl⟩

theorem halves_card (I : Finset (P × T)) :
    (halves I).card = ∑ p ∈ points I, (halfPaths I p).card := by
  simp only [halves,card_map,card_sigma]

theorem square_incidence_le_tubes_halves (I : Finset (P × T)) :
    I.card^2 ≤ (tubes I).card*(halves I).card := by
  rw [halves_card,sum_halfPaths_eq_sum_tubeDegree_sq,card_incidence_eq_sum_tubeDegree]
  exact nat_sum_sq_le_card_mul_sum_sq (tubes I) (tubeDegree I)

/-- The grain relation replaces the identity of the two middle points.
The six retained coordinates are precisely an original one-arm path. -/
def arms (I : Finset (P × T)) (grain : P → G) :=
  collisions (halves I) (fun x => grain x.1)

@[simp] theorem mem_arms (I : Finset (P × T)) (grain : P → G)
    (w : (P × (P × T)) × (P × (P × T))) :
    w ∈ arms I grain ↔
      w.1.2 ∈ I ∧ (w.1.1,w.1.2.2) ∈ I ∧
      w.2.2 ∈ I ∧ (w.2.1,w.2.2.2) ∈ I ∧ grain w.1.1=grain w.2.1 := by
  simp only [arms,mem_collisions,mem_halves,and_assoc]

theorem half_grain_image (I : Finset (P × T)) (grain : P → G) :
    (halves I).image (fun x => grain x.1)=(points I).image grain := by
  apply Finset.Subset.antisymm
  · intro g hg
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hg
    exact mem_image_of_mem grain (mem_image_of_mem Prod.fst ((mem_halves I x).mp hx).2)
  · intro g hg
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hg
    obtain ⟨⟨p',t⟩,he,hp'⟩ := mem_image.mp hp
    change p'=p at hp'
    subst p'
    exact mem_image.mpr ⟨(p,(p,t)),(mem_halves I _).mpr ⟨he,he⟩,rfl⟩

/-- Two finite Cauchy inequalities give the actual grain-mixed path count.
It needs neither minimum degree nor a prescribed fraction in each grain. -/
theorem fourth_power_one_arm_bound (I : Finset (P × T)) (grain : P → G) :
    I.card^4 ≤ (tubes I).card^2*((points I).image grain).card*(arms I grain).card := by
  have hi := square_incidence_le_tubes_halves I
  have hg := square_card_le_image_mul_collisions (halves I) (fun x => grain x.1)
  rw [half_grain_image] at hg
  change (halves I).card^2 ≤ ((points I).image grain).card*(arms I grain).card at hg
  calc
    I.card^4 = (I.card^2)^2 := by ring
    _ ≤ ((tubes I).card*(halves I).card)^2 := Nat.pow_le_pow_left hi 2
    _ = (tubes I).card^2*(halves I).card^2 := by ring
    _ ≤ (tubes I).card^2*(((points I).image grain).card*(arms I grain).card) :=
      Nat.mul_le_mul_left _ hg
    _ = _ := by ring

/-- The actual Section20 collision key: original start, intermediate and
terminal heights, moved-point spatial cell, and terminal direction cell. -/
def armLabel (height : P → H) (xcell : P → X) (angle : T → A)
    (w : (P × (P × T)) × (P × (P × T))) : P × H × H × X × A :=
  (w.1.2.1,height w.1.1,height w.2.2.1,xcell w.2.1,angle w.2.2.2)

def lTuples (I : Finset (P × T)) (grain : P → G)
    (height : P → H) (xcell : P → X) (angle : T → A) :=
  collisions (arms I grain) (armLabel height xcell angle)

/-- Every constructed pair has both original one-arm paths and the five
literal equalities needed to read back an L-tuple. Metric closeness comes
from the actual chosen spatial and angular cells, not from this count. -/
theorem l_tuple_conditions (I : Finset (P × T)) (grain : P → G)
    (height : P → H) (xcell : P → X) (angle : T → A)
    (u v : (P × (P × T)) × (P × (P × T)))
    (h : (u,v) ∈ lTuples I grain height xcell angle) :
    u ∈ arms I grain ∧ v ∈ arms I grain ∧
      u.1.2.1=v.1.2.1 ∧ height u.1.1=height v.1.1 ∧
      height u.2.2.1=height v.2.2.1 ∧ xcell u.2.1=xcell v.2.1 ∧
      angle u.2.2.2=angle v.2.2.2 := by
  obtain ⟨hu,hv,hkey⟩ := (mem_collisions _ _ _).mp h
  exact ⟨hu,hv,by simpa only [armLabel,Prod.mk.injEq] using hkey⟩

/-- Exact finite lower count with the genuine occupied-key cardinality.
Geometric control of this key image remains a separate source obligation. -/
theorem eighth_power_l_tuple_bound (I : Finset (P × T)) (grain : P → G)
    (height : P → H) (xcell : P → X) (angle : T → A) :
    I.card^8 ≤ (tubes I).card^4*((points I).image grain).card^2*
      ((arms I grain).image (armLabel height xcell angle)).card*
      (lTuples I grain height xcell angle).card := by
  have ha := fourth_power_one_arm_bound I grain
  have hl := square_card_le_image_mul_collisions (arms I grain) (armLabel height xcell angle)
  change (arms I grain).card^2 ≤
    ((arms I grain).image (armLabel height xcell angle)).card*
      (lTuples I grain height xcell angle).card at hl
  calc
    I.card^8 = (I.card^4)^2 := by ring
    _ ≤ ((tubes I).card^2*((points I).image grain).card*(arms I grain).card)^2 :=
      Nat.pow_le_pow_left ha 2
    _ = (tubes I).card^4*((points I).image grain).card^2*(arms I grain).card^2 := by ring
    _ ≤ (tubes I).card^4*((points I).image grain).card^2*
        (((arms I grain).image (armLabel height xcell angle)).card*
          (lTuples I grain height xcell angle).card) := Nat.mul_le_mul_left _ hl
    _ = _ := by ring

end NativeGrainOneArmCount
