import Theorems.Thm_StickyKakeya4_native_lipschitz_local_height_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeLipschitzHeightEdgeLift
open Classical Finset NativeMatrixHeightWholePoint SeparatedAlignmentPatches
open NativeLipschitzCoarseHeightSelection NativeLipschitzLocalHeightSelection

lemma lift_cell_card {E P : Type*} [DecidableEq P] (A : Finset E)
    (point : E → P) (S : Finset P) (cell : P → ℤ) (c : ℤ) :
    ((edgeLift A point S).filter (fun x => cell (point x)=c)).card=
      mass (S.filter (fun p => cell p=c)) (fun p => (A.filter (fun x => point x=p)).card) := by
  have he : (edgeLift A point S).filter (fun x => cell (point x)=c)=
      edgeLift A point (S.filter (fun p => cell p=c)) := by
    ext x
    simp only [edgeLift,mem_filter,and_assoc]
  rw [he,edgeLift_card]

lemma source_cell_card {E P : Type*} [DecidableEq P] (A : Finset E)
    (point : E → P) (cell : P → ℤ) (c : ℤ) :
    (A.filter (fun x => cell (point x)=c)).card=
      mass ((A.image point).filter (fun p => cell p=c))
        (fun p => (A.filter (fun x => point x=p)).card) := by
  have he : edgeLift A point (A.image point)=A := by
    apply filter_eq_self.mpr
    intro x hx
    exact mem_image_of_mem point hx
  rw [←lift_cell_card A point (A.image point) cell c,he]

/-- The local best-bin operator acts on original point labels with their
actual incidence-fiber weights. Every surviving point keeps its full old
fiber, and every surviving coarse cell retains at least 1/q of its own
old incidence count. The witness field is fixed before later subsets. -/
theorem select_original_edges {E P V : Type*} [DecidableEq P] [NormedAddCommGroup V]
    (A : Finset E) (hA : A.Nonempty) (point : E → P)
    (height : P → ℝ) (F : P → V) (L R origin B : ℝ)
    (hL : 0 ≤ L) (hR : 0 < R) (hB : 0 ≤ B)
    (hF : ∀p∈A.image point,‖F p‖ ≤ B)
    (hLip : ∀p∈A.image point,∀q∈A.image point,
      dist (F p) (F q) ≤ L*|height p-height q|) :
    let q:=subdivisions L
    ∃S⊆A.image point,
      let T:=edgeLift A point S
      let field:=selectedField S height F R origin
      T.Nonempty ∧ T⊆A ∧ A.card ≤ (8*q)*T.card ∧
      (A.card:ℝ) ≤ (16*max 1 L)*(T.card:ℝ) ∧
      (∀p∈S,T.filter (fun x => point x=p)=A.filter (fun x => point x=p)) ∧
      (∀c∈T.image (fun x => coarse R origin (height (point x))),
        (A.filter (fun x => coarse R origin (height (point x))=c)).card ≤
          q*(T.filter (fun x => coarse R origin (height (point x))=c)).card) ∧
      (∀p∈A.image point,∀v∈S,fine R origin q (height p)=fine R origin q (height v) → p∈S) ∧
      (∀x∈T,∀y∈T,coarse R origin (height (point x))%8=coarse R origin (height (point y))%8) ∧
      (∀x∈T,∀y∈T,coarse R origin (height (point x))=coarse R origin (height (point y)) →
        fine R origin q (height (point x))=fine R origin q (height (point y))) ∧
      (∀c,‖field c‖ ≤ B) ∧
      (∀U⊆T,∀x∈U,dist (field (coarse R origin (height (point x)))) (F (point x)) ≤ R) ∧
      ∀U⊆T,∀x∈U,∀y∈U,
        dist (field (coarse R origin (height (point x))))
          (field (coarse R origin (height (point y)))) ≤
        ((9/8:ℝ)*L)*dist (center R origin (coarse R origin (height (point x))))
          (center R origin (coarse R origin (height (point y)))) := by
  intro q
  let weights := fun p => (A.filter (fun x => point x=p)).card
  obtain ⟨best,color,hS,hret,hretR,hlocal,hfine,hbound,hclose,hfield⟩ :=
    select_locally_retained_field (A.image point) weights height F L R origin B hL hR hB hF hLip
  let hq : 0 < q := (subdivisions_bounds L).1
  let S := (A.image point).filter (fun p => residue q hq (fine R origin q (height p))=
    best (coarse R origin (height p)) ∧ residue 8 (by decide) (coarse R origin (height p))=color)
  let T := edgeLift A point S
  have hmass : mass (A.image point) weights=A.card := (card_eq_sum_card_image point A).symm
  have hretN : A.card ≤ (8*q)*T.card := by
    rw [hmass,←edgeLift_card A point S] at hret
    exact hret
  have hretReal : (A.card:ℝ) ≤ (16*max 1 L)*(T.card:ℝ) := by
    rw [hmass,←edgeLift_card A point S] at hretR
    exact hretR
  have hT : T.Nonempty := by
    by_contra hn
    have hz : T.card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    rw [hz,mul_zero] at hretN
    exact (Nat.not_le_of_lt (card_pos.mpr hA)) hretN
  refine ⟨S,hS,hT,filter_subset _ _,hretN,hretReal,
    fun p hp => edgeLift_fiber A point S p hp,?_,?_,?_,?_,hbound,?_,?_⟩
  · intro c hc
    obtain ⟨x,hx,hxc⟩ := mem_image.mp hc
    have hcS : c∈S.image (fun p => coarse R origin (height p)) :=
      mem_image.mpr ⟨point x,(mem_filter.mp hx).2,hxc⟩
    have hh := hlocal c hcS
    rw [←source_cell_card A point (fun p => coarse R origin (height p)) c,
      ←lift_cell_card A point S (fun p => coarse R origin (height p)) c] at hh
    exact hh
  · intro p hp v hv he
    have hc : coarse R origin (height p)=coarse R origin (height v) := by
      rw [coarse_eq_fine_div _ _ _ q hq,coarse_eq_fine_div _ _ _ q hq,he]
    apply mem_filter.mpr
    refine ⟨hp,?_⟩
    rw [he,hc]
    exact (mem_filter.mp hv).2
  · intro x hx y hy
    have hxS := (mem_filter.mp hx).2
    have hyS := (mem_filter.mp hy).2
    exact residue_eq_emod (hL:=by decide)
      ((mem_filter.mp hxS).2.2.trans (mem_filter.mp hyS).2.2.symm)
  · intro x hx y hy he
    exact hfine (point x) (mem_filter.mp hx).2 (point y) (mem_filter.mp hy).2 he
  · intro U hUT x hx
    exact hclose S (Subset.refl _) (point x) (mem_filter.mp (hUT hx)).2
  · intro U hUT x hx y hy
    exact hfield S (Subset.refl _) (point x) (mem_filter.mp (hUT hx)).2
      (point y) (mem_filter.mp (hUT hy)).2

end NativeLipschitzHeightEdgeLift
