import Theorems.Thm_StickyKakeya4_native_coarse_shading_uniformity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

noncomputable section
namespace NativeFiniteSliceHomogeneity
open Classical Finset NativeCoarseShadingUniformity
open scoped BigOperators

/-- A bounded number of occupied classes per height turns actual class
fiber homogeneity into height fiber homogeneity. No heights are filled in. -/
theorem coarsen_fiber_comparison {A X Y : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (E : Finset A) (f : A → X) (g : X → Y) (K C : ℕ)
    (hf : ∀a∈E,∀b∈E,(E.filter (fun z => f z=f a)).card ≤
      K*(E.filter (fun z => f z=f b)).card)
    (hcap : ∀y,((E.image f).filter (fun x => g x=y)).card ≤ C) :
    ∀a∈E,∀b∈E,(E.filter (fun z => g (f z)=g (f a))).card ≤
      C*K*(E.filter (fun z => g (f z)=g (f b))).card := by
  intro a _ha b hb
  have hsub : E.filter (fun z => f z=f b)⊆E.filter (fun z => g (f z)=g (f b)) := by
    intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).1,congrArg g (mem_filter.mp hz).2⟩
  calc
    _ = ∑x∈(E.image f).filter (fun x => g x=g (f a)),(E.filter (fun z => f z=x)).card :=
      nested_fiber_card_sum E f g (g (f a))
    _ ≤ ∑_x∈(E.image f).filter (fun x => g x=g (f a)),K*(E.filter (fun z => f z=f b)).card := by
      apply sum_le_sum
      intro x hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp (mem_filter.mp hx).1
      exact hf z hz b hb
    _ = ((E.image f).filter (fun x => g x=g (f a))).card*(K*(E.filter (fun z => f z=f b)).card) := by
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id]
    _ ≤ C*(K*(E.filter (fun z => f z=f b)).card) := Nat.mul_le_mul_right _ (hcap _)
    _ = (C*K)*(E.filter (fun z => f z=f b)).card := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (card_le_card hsub)

/-- Every occupied height contains a comparable fraction of all points.
The two cross inequalities retain the actual number of occupied heights. -/
theorem fiber_card_average_cross {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (P : Finset X) (height : X → Y) (K : ℕ)
    (H : ∀x∈P,∀y∈P,(P.filter (fun z => height z=height x)).card ≤
      K*(P.filter (fun z => height z=height y)).card)
    (z : Y) (hz : z∈P.image height) :
    (P.filter (fun x => height x=z)).card*(P.image height).card ≤ K*P.card ∧
      P.card ≤ K*(P.filter (fun x => height x=z)).card*(P.image height).card := by
  obtain ⟨x,hx,hxz⟩ := mem_image.mp hz
  have hs : P.card=∑y∈P.image height,(P.filter (fun x => height x=y)).card :=
    card_eq_sum_card_image height P
  constructor
  · calc
      _ = ∑_y∈P.image height,(P.filter (fun x => height x=z)).card := by simp [Nat.mul_comm]
      _ ≤ ∑y∈P.image height,K*(P.filter (fun x => height x=y)).card := by
        apply sum_le_sum
        intro y hy
        obtain ⟨v,hv,hvy⟩ := mem_image.mp hy
        simpa only [hxz,hvy] using H x hx v hv
      _ = K*P.card := by rw [←mul_sum,←hs]
  · calc
      _ = ∑y∈P.image height,(P.filter (fun x => height x=y)).card := hs
      _ ≤ ∑_y∈P.image height,K*(P.filter (fun x => height x=z)).card := by
        apply sum_le_sum
        intro y hy
        obtain ⟨v,hv,hvy⟩ := mem_image.mp hy
        simpa only [hxz,hvy] using H v hv x hx
      _ = _ := by simp [Nat.mul_comm]

end NativeFiniteSliceHomogeneity
