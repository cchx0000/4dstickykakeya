import Theorems.Thm_StickyKakeya4_native_pointwise_angular_trim

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeTrimmedAngularClassCounts
open Classical Finset
open scoped BigOperators

lemma coarse_fiber_image {A X Y : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (T : Finset A) (f : A → X) (coarse : X → Y) (y : Y) :
    ((T.filter (fun z => coarse (f z)=y)).image f)=(T.image f).filter (fun x => coarse x=y) := by
  ext x
  simp only [mem_image,mem_filter]
  constructor
  · rintro ⟨z,⟨hz,hy⟩,rfl⟩
    exact ⟨⟨z,hz,rfl⟩,hy⟩
  · rintro ⟨⟨z,hz,rfl⟩,hy⟩
    exact ⟨z,⟨hz,hy⟩,rfl⟩

lemma nested_fiber {A X Y : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (T : Finset A) (f : A → X) (coarse : X → Y) (x : X) (y : Y) (hy : coarse x=y) :
    (T.filter (fun z => coarse (f z)=y)).filter (fun z => f z=x)=T.filter (fun z => f z=x) := by
  ext z
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hz,_⟩,hx⟩
    exact ⟨hz,hx⟩
  · rintro ⟨hz,hx⟩
    exact ⟨⟨hz,(congrArg coarse hx).trans hy⟩,hx⟩

/-- Actual coarse incidence weight is the sum of the actual fine-fiber
weights over DISTINCT fine labels. This is the necessary weighted/unweighted
conversion after angular trimming. -/
lemma coarse_weight_sum {A X Y : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (T : Finset A) (f : A → X) (coarse : X → Y) (y : Y) :
    ((T.filter (fun z => coarse (f z)=y)).card:ℝ)=
      ∑x∈(T.image f).filter (fun x => coarse x=y),((T.filter (fun z => f z=x)).card:ℝ) := by
  have hh := card_eq_sum_card_image f (T.filter (fun z => coarse (f z)=y))
  rw [coarse_fiber_image] at hh
  have he : ∑x∈(T.image f).filter (fun x => coarse x=y),
      ((T.filter (fun z => coarse (f z)=y)).filter (fun z => f z=x)).card=
      ∑x∈(T.image f).filter (fun x => coarse x=y),(T.filter (fun z => f z=x)).card := by
    apply sum_congr rfl
    intro x hx
    rw [nested_fiber T f coarse x y (mem_filter.mp hx).2]
  exact_mod_cast hh.trans he

/-- Rich retained coarse classes and ORIGINAL fine-fiber uppers imply a
lower bound for distinct retained fine directions. -/
theorem distinct_class_lower {A X Y : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (I T : Finset A) (hTI : T⊆I) (f : A → X) (coarse : X → Y)
    (y : Y) (L Ufine : ℝ)
    (hL : L ≤ ((T.filter (fun z => coarse (f z)=y)).card:ℝ))
    (hU : ∀x,((I.filter (fun z => f z=x)).card:ℝ) ≤ Ufine) :
    L ≤ Ufine*((T.image f).filter (fun x => coarse x=y)).card := by
  calc
    _ ≤ ((T.filter (fun z => coarse (f z)=y)).card:ℝ) := hL
    _ = ∑x∈(T.image f).filter (fun x => coarse x=y),((T.filter (fun z => f z=x)).card:ℝ) :=
      coarse_weight_sum T f coarse y
    _ ≤ ∑_x∈(T.image f).filter (fun x => coarse x=y),Ufine := by
      apply sum_le_sum
      intro x _
      exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hTI))).trans (hU x)
    _ = _ := by simp; ring

/-- Rich retained FINE classes are indispensable for the opposite direction:
an ORIGINAL coarse-weight upper then gives a distinct-direction upper. -/
theorem distinct_class_upper {A X Y : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (I T : Finset A) (hTI : T⊆I) (f : A → X) (coarse : X → Y)
    (y : Y) (Lfine U : ℝ)
    (hL : ∀x∈T.image f,Lfine ≤ ((T.filter (fun z => f z=x)).card:ℝ))
    (hU : ((I.filter (fun z => coarse (f z)=y)).card:ℝ) ≤ U) :
    Lfine*((T.image f).filter (fun x => coarse x=y)).card ≤ U := by
  calc
    _ = ∑_x∈(T.image f).filter (fun x => coarse x=y),Lfine := by simp; ring
    _ ≤ ∑x∈(T.image f).filter (fun x => coarse x=y),((T.filter (fun z => f z=x)).card:ℝ) :=
      sum_le_sum (fun x hx => hL x (mem_filter.mp hx).1)
    _ = ((T.filter (fun z => coarse (f z)=y)).card:ℝ) := (coarse_weight_sum T f coarse y).symm
    _ ≤ ((I.filter (fun z => coarse (f z)=y)).card:ℝ) :=
      Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hTI))
    _ ≤ _ := hU

end NativeTrimmedAngularClassCounts
