import Theorems.Thm_StickyKakeya4_canonical_angular_offset_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace HeightGraphResidueSeparation
open Classical Finset StickyKakeya4 CanonicalGridRecoding CanonicalConfiguredPointRounding
open CanonicalConfiguredE4Bridge CanonicalAngularOffsetGeometry
open NativeMatrixHeightWholePoint SeparatedAlignmentPatches
open scoped BigOperators

abbrev Parameter := Fin 4 → ℤ

def parameterX (s : Split) (a : Parameter) : Grid (tangentDim s) :=
  fun j => a (tangentIndex s j)

def parameterY (s : Split) (a : Parameter) : Grid (normalDim s) :=
  fun i => a (normalIndex s i)

/-- F is a function ONLY of the coarse integer height index. -/
def graphGrid (s : Split) (base : ℝ)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (a : Parameter) : E4 :=
  assemble s (center base (parameterX s a))
    (graphPoint (F (a 3)) (center base (parameterX s a)) (center base (parameterY s a)))
    (base*((a 3:ℝ)+1/2))

theorem graphGrid_height (s : Split) (base : ℝ)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) (a : Parameter) :
    graphGrid s base F a 3=base*((a 3:ℝ)+1/2) := by
  cases s <;> rfl

theorem graphGrid_tangent (s : Split) (base : ℝ)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (a : Parameter) (j : Fin (tangentDim s)) :
    graphGrid s base F a (tangentIndex s j)=center base (parameterX s a) j := by
  cases s <;> fin_cases j <;> rfl

theorem graphGrid_normal (s : Split) (base : ℝ)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (a : Parameter) (i : Fin (normalDim s)) :
    graphGrid s base F a (normalIndex s i)=
      graphPoint (F (a 3)) (center base (parameterX s a)) (center base (parameterY s a)) i := by
  cases s <;> fin_cases i <;> rfl

lemma parameter_ext (s : Split) {a b : Parameter}
    (hz : a 3=b 3) (hx : parameterX s a=parameterX s b)
    (hy : parameterY s a=parameterY s b) : a=b := by
  funext j
  cases s with
  | oneTwo =>
      fin_cases j
      · exact congrFun hx 0
      · exact congrFun hy 0
      · exact congrFun hy 1
      · exact hz
  | twoOne =>
      fin_cases j
      · exact congrFun hx 0
      · exact congrFun hx 1
      · exact congrFun hy 0
      · exact hz

lemma midpoint_distance (base : ℝ) (hb : 0 < base) (a b : ℤ) :
    dist (base*((a:ℝ)+1/2)) (base*((b:ℝ)+1/2))=base*|(a:ℝ)-(b:ℝ)| := by
  rw [Real.dist_eq]
  have he : base*((a:ℝ)+1/2)-base*((b:ℝ)+1/2)=base*((a:ℝ)-(b:ℝ)) := by ring
  rw [he,abs_mul,abs_of_pos hb]

lemma colored_coordinate_gap (base : ℝ) (hb : 0 < base) (q : ℕ) (hq : 0 < q)
    {a b : Parameter} (H : color q hq a=color q hq b) (j : Fin 4) (hne : a j≠b j) :
    base*(q:ℝ)≤dist (base*((a j:ℝ)+1/2)) (base*((b j:ℝ)+1/2)) := by
  rw [midpoint_distance base hb]
  exact mul_le_mul_of_nonneg_left
    (real_residue_spacing hq (residue_eq_emod (congrFun H j)) hne) hb.le

/-- Three actual coordinate cases: height, tangent, then normal.
No bound or regularity of the height-dependent matrix is needed. -/
theorem graphGrid_residue_separation (s : Split) (base : ℝ) (hb : 0 < base)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (q : ℕ) (hq : 0 < q) {a b : Parameter}
    (H : color q hq a=color q hq b) (hne : a≠b) :
    base*(q:ℝ)≤dist (graphGrid s base F a) (graphGrid s base F b) := by
  by_cases hz : a 3=b 3
  · by_cases hx : parameterX s a=parameterX s b
    · have hy : parameterY s a≠parameterY s b := fun h => hne (parameter_ext s hz hx h)
      obtain ⟨i,hi⟩ : ∃i,parameterY s a i≠parameterY s b i := by
        by_contra h
        push Not at h
        exact hy (funext h)
      have hc := colored_coordinate_gap base hb q hq H (normalIndex s i) hi
      have he : dist (graphGrid s base F a (normalIndex s i))
          (graphGrid s base F b (normalIndex s i))=
          dist (center base (parameterY s a) i) (center base (parameterY s b) i) := by
        rw [graphGrid_normal,graphGrid_normal]
        simp only [graphPoint,hz,hx,dist_add_right]
      change base*(q:ℝ)≤dist (center base (parameterY s a) i) (center base (parameterY s b) i) at hc
      rw [←he] at hc
      exact hc.trans (PiLp.dist_apply_le _ _ (normalIndex s i))
    · obtain ⟨j,hj⟩ : ∃j,parameterX s a j≠parameterX s b j := by
        by_contra h
        push Not at h
        exact hx (funext h)
      have hc := colored_coordinate_gap base hb q hq H (tangentIndex s j) hj
      have hh := PiLp.dist_apply_le (graphGrid s base F a) (graphGrid s base F b) (tangentIndex s j)
      rw [graphGrid_tangent,graphGrid_tangent] at hh
      exact hc.trans hh
  · have hc := colored_coordinate_gap base hb q hq H 3 hz
    have hh := PiLp.dist_apply_le (graphGrid s base F a) (graphGrid s base F b) (3:Fin 4)
    rw [graphGrid_height,graphGrid_height] at hh
    exact hc.trans hh

theorem graphGrid_separated (s : Split) (base : ℝ) (hb : 0 < base)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    {a b : Parameter} (hne : a≠b) : base≤dist (graphGrid s base F a) (graphGrid s base F b) := by
  simpa only [Nat.cast_one,mul_one] using graphGrid_residue_separation s base hb F 1
    (by decide) (Subsingleton.elim _ _) hne

theorem graphGrid_injective (s : Split) (base : ℝ) (hb : 0 < base)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ) :
    Function.Injective (graphGrid s base F) := by
  intro a b he
  by_contra hne
  have hh := graphGrid_separated s base hb F hne
  rw [he,dist_self] at hh
  exact (not_lt_of_ge hh) hb

/-- One GLOBAL maximum-weight residue class in the four integer parameters.
The graph is not resampled and the original labels retain their weights. -/
theorem select_original_weighted_points {P : Type*}
    (S : Finset P) (w : P → ℕ) (parameter : P → Parameter)
    (s : Split) (base : ℝ) (hb : 0 < base)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (q : ℕ) (hq : 0 < q) :
    ∃B⊆S,mass S w≤q^4*mass B w ∧
      ∀p∈B,∀r∈B,parameter p≠parameter r →
        base*(q:ℝ)≤dist (graphGrid s base F (parameter p)) (graphGrid s base F (parameter r)) := by
  let : Nonempty (Fin 4 → Fin q) := ⟨fun _ => ⟨0,hq⟩⟩
  obtain ⟨c,hret⟩ := maximum_weight_color S w (fun p => color q hq (parameter p))
  let B := S.filter (fun p => color q hq (parameter p)=c)
  refine ⟨B,filter_subset _ _,?_,?_⟩
  · simpa only [mass,Fintype.card_fun,Fintype.card_fin] using hret
  · intro p hp r hr hne
    exact graphGrid_residue_separation s base hb F q hq
      ((mem_filter.mp hp).2.trans (mem_filter.mp hr).2.symm) hne

/-- Actual original-edge lift of the global residue choice. Every surviving
original point keeps its entire incidence fiber; only the geometric image
is asserted separated, allowing repeated original witnesses of one point. -/
theorem select_original_edges {E P : Type*} [DecidableEq P]
    (I : Finset E) (point : E → P) (parameter : P → Parameter)
    (s : Split) (base : ℝ) (hb : 0 < base)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (q : ℕ) (hq : 0 < q) :
    ∃B⊆I.image point,let J := edgeLift I point B
      J⊆I ∧ I.card≤q^4*J.card ∧
      (∀p∈B,J.filter (fun e => point e=p)=I.filter (fun e => point e=p)) ∧
      (∀x∈J.image (fun e => graphGrid s base F (parameter (point e))),
        ∀y∈J.image (fun e => graphGrid s base F (parameter (point e))),x≠y → base*(q:ℝ)≤dist x y) := by
  let w := fun p => (I.filter (fun e => point e=p)).card
  have hmass : mass (I.image point) w=I.card := (card_eq_sum_card_image point I).symm
  obtain ⟨B,hB,hret,hsep⟩ := select_original_weighted_points (I.image point) w parameter s base hb F q hq
  rw [hmass,←edgeLift_card I point B] at hret
  refine ⟨B,hB,filter_subset _ _,hret,(fun p hp => edgeLift_fiber I point B p hp),?_⟩
  intro x hx y hy hxy
  obtain ⟨e,he,rfl⟩ := mem_image.mp hx
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hy
  have hne : parameter (point e)≠parameter (point f) := by
    intro hh
    exact hxy (congrArg (graphGrid s base F) hh)
  exact hsep (point e) (mem_filter.mp he).2 (point f) (mem_filter.mp hf).2 hne

end HeightGraphResidueSeparation
