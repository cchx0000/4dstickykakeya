import Theorems.Thm_StickyKakeya4_self_uniform_incidence_refinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace NativeWeightedPointPopulations
open SelfUniform
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {ι X Y : Type*} [DecidableEq X] [DecidableEq Y]

def projectedWeight (w : ι → ℕ) (p : ι → X) (I : Finset ι) (x : X) : ℕ :=
  ∑ a ∈ I, if p a = x then w a else 0

def classPoints (P : Finset X) (f : X → Y) (x : X) : Finset X :=
  P.filter (fun y => f y = f x)

lemma projectedWeight_pos (w : ι → ℕ) (p : ι → X) (I : Finset ι)
    (hw : ∀ a ∈ I, 0 < w a) {x : X} (hx : x ∈ I.image p) : 0 < projectedWeight w p I x := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  have hle : w a ≤ projectedWeight w p I (p a) := by
    unfold projectedWeight
    simpa using Finset.single_le_sum
      (f := fun b => if p b = p a then w b else 0) (fun _ _ => Nat.zero_le _) ha
  exact (hw a ha).trans_le hle

lemma projectedWeight_mass_preimage (w : ι → ℕ) (p : ι → X) (I : Finset ι) (S : Finset X) :
    mass (projectedWeight w p I) S = mass w (I.filter (fun a => p a ∈ S)) := by
  unfold mass projectedWeight
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hp : p a ∈ S <;> simp [hp, eq_comm]

lemma degree_eq_projectedWeight (w : ι → ℕ) (p : ι → X) (I : Finset ι) (a : ι) :
    degree w (fun b c => p b = p c) I a = projectedWeight w p I (p a) := by
  unfold degree projectedWeight
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases h : p a = p b <;> simp [h, eq_comm]

lemma projected_class_mass (w : ι → ℕ) (p : ι → X) (I : Finset ι) (f : X → Y) (a : ι) :
    mass (projectedWeight w p I) (classPoints (I.image p) f (p a)) =
      degree w (fun b c => f (p b) = f (p c)) I a := by
  rw [projectedWeight_mass_preimage]
  unfold mass degree
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  have hp : p b ∈ I.image p := Finset.mem_image_of_mem p hb
  by_cases h : f (p a) = f (p b) <;> simp [classPoints, hp, h, eq_comm]

/-- Two weighted uniformities on the SAME original-label set imply uniform
DISTINCT geometric point populations. All point multiplicities are summed
exactly, then a constructed positive maximum is cancelled. -/
theorem cardinality_uniform_of_weighted_degrees
    (w : ι → ℕ) (p : ι → X) (I : Finset ι) (f : X → Y) (Q : ℕ)
    (hne : I.Nonempty) (hw : ∀ a ∈ I, 0 < w a)
    (hpoint : ∀ x ∈ I.image p, ∀ y ∈ I.image p,
      projectedWeight w p I x ≤ Q ^ 2 * projectedWeight w p I y)
    (hclass : ∀ a ∈ I, ∀ b ∈ I,
      degree w (fun c d => f (p c) = f (p d)) I a ≤
        Q ^ 2 * degree w (fun c d => f (p c) = f (p d)) I b) :
    ∀ x ∈ I.image p, ∀ y ∈ I.image p,
      (classPoints (I.image p) f x).card ≤ Q ^ 4 * (classPoints (I.image p) f y).card := by
  let P := I.image p
  let W := projectedWeight w p I
  obtain ⟨x0, hx0, hmax⟩ := Finset.exists_max_image P W (hne.image p)
  have hD : 0 < W x0 := projectedWeight_pos w p I hw hx0
  have hlo (S : Finset X) (hS : S ⊆ P) : W x0 * S.card ≤ Q ^ 2 * mass W S := by
    calc
      _ = ∑ _x ∈ S, W x0 := by simp [mul_comm]
      _ ≤ ∑ x ∈ S, Q ^ 2 * W x := by
        apply Finset.sum_le_sum
        intro x hx
        exact hpoint x0 hx0 x (hS hx)
      _ = _ := by simp only [mass, Finset.mul_sum]
  have hup (S : Finset X) (hS : S ⊆ P) : mass W S ≤ W x0 * S.card := by
    calc
      _ ≤ ∑ _x ∈ S, W x0 := Finset.sum_le_sum (fun x hx => hmax x (hS hx))
      _ = _ := by simp [mul_comm]
  intro x hx y hy
  have hxy : mass W (classPoints P f x) ≤ Q ^ 2 * mass W (classPoints P f y) := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [show W = projectedWeight w p I from rfl, projected_class_mass, projected_class_mass]
    exact hclass a ha b hb
  have hmul : W x0 * (classPoints P f x).card ≤ W x0 * (Q ^ 4 * (classPoints P f y).card) := by
    calc
      _ ≤ Q ^ 2 * mass W (classPoints P f x) := hlo _ (Finset.filter_subset _ _)
      _ ≤ Q ^ 2 * (Q ^ 2 * mass W (classPoints P f y)) := Nat.mul_le_mul_left _ hxy
      _ ≤ Q ^ 2 * (Q ^ 2 * (W x0 * (classPoints P f y).card)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hup _ (Finset.filter_subset _ _)))
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hmul hD
end
end NativeWeightedPointPopulations
