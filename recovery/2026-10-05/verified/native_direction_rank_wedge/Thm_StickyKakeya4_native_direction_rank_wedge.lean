import Theorems.Thm_StickyKakeya4_native_direction_rank_dichotomy
import Theorems.Thm_StickyKakeya4_native_separated_gram_determinant

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeDirectionRankWedge
open Classical Finset NativeDirectionRankDichotomy
open scoped BigOperators
attribute [local instance] IsWellOrder.toHasWellFounded

variable {α V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
lemma cons_image_after_zero (v : α → V) (a : α) (xs : List α) :
    (fun i : Fin (a::xs).length => v ((a::xs).get i)) '' Set.Ioi 0 =
      Set.range (fun i : Fin xs.length => v (xs.get i)) := by
  ext x
  constructor
  · rintro ⟨i,hi,rfl⟩
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero (ne_of_gt hi)
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨j.succ,Fin.succ_pos j,rfl⟩

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
lemma cons_image_after_succ (v : α → V) (a : α) (xs : List α)
    (j : Fin xs.length) :
    (fun i : Fin (a::xs).length => v ((a::xs).get i)) '' Set.Ioi j.succ =
      (fun i : Fin xs.length => v (xs.get i)) '' Set.Ioi j := by
  ext x
  constructor
  · rintro ⟨i,hi,rfl⟩
    have hi0 : i ≠ 0 := ne_of_gt ((Fin.succ_pos j).trans hi)
    obtain ⟨k,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
    exact ⟨k,Fin.succ_lt_succ_iff.mp hi,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨k.succ,Fin.succ_lt_succ_iff.mpr hk,rfl⟩

/-- The chain's reverse chronological convention gives genuine distance from
the span of all later indices, with no change of its original labels. -/
theorem separated_tail_distances (v : α → V) (r : ℝ) (xs : List α)
    (hxs : Separated v r xs) :
    ∀ i : Fin xs.length, r ≤ Metric.infDist (v (xs.get i))
      (Submodule.span ℝ
        ((fun j : Fin xs.length => v (xs.get j)) '' Set.Ioi i) : Set V) := by
  induction xs with
  | nil => exact fun i => Fin.elim0 i
  | cons a xs ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [cons_image_after_zero]
      exact hxs.2.le
    · rw [cons_image_after_succ]
      exact ih hxs.1 j

/-- Quantitative Gram lower bound for the actual separated tuple supplied by
the rank dichotomy. Opposite index order matches its tail spans, so the Gram
matrix itself and all original labels remain literally unchanged. -/
theorem separated_gram_det_lower (v : α → V) (r : ℝ) (hr : 0 < r)
    (xs : List α) (hxs : Separated v r xs) :
    r^(2*xs.length) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det := by
  let f : OrderDual (Fin xs.length) → V := fun i => v (xs.get i)
  have hf : LinearIndependent ℝ f := separated_linearIndependent v r hr xs hxs
  have hdist : ∀ i : OrderDual (Fin xs.length), r ≤ Metric.infDist (f i)
      (Submodule.span ℝ (f '' Set.Iio i) : Set V) :=
    separated_tail_distances v r xs hxs
  have hh := NativeSeparatedGramDeterminant.gram_det_lower_of_span_distance f hf r hr.le hdist
  let e : OrderDual (Fin xs.length) ≃ Fin xs.length := Equiv.refl _
  have hdet : (Matrix.gram ℝ f).det =
      (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det :=
    Matrix.det_submatrix_equiv_self e (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i)))
  rw [hdet] at hh
  simpa only [Fintype.card_orderDual, Fintype.card_fin] using hh

/-- Every weighted chain produced from the original labels has the same
quantitative transversality, proved from its actual selection rule. -/
theorem chains_gram_det_lower [DecidableEq α] (A : Finset α) (v : α → V)
    (r : ℝ) (hr : 0 < r) (n : ℕ) (xs : List α) (hxs : xs ∈ chains A v r n) :
    r^(2*n) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det := by
  have hh := separated_gram_det_lower v r hr xs (chains_separated A v r n xs hxs)
  calc
    _ = r^(2*xs.length) := by rw [chains_length A v r n xs hxs]
    _ ≤ _ := hh

/-- The actual weighted rank selection now supplies a quantitative Gram lower
bound on every produced original-label tuple, without a transversality input. -/
theorem concentration_or_many_transverse_chains [DecidableEq α] [FiniteDimensional ℝ V]
    (A : Finset α) (v : α → V) (r : ℝ) (hr : 0 < r)
    (w : α → ℝ) (hw : ∀a, 0 ≤ w a) (ell : ℕ) (B : ℝ) (hB : B ≤ mass w A) :
    (∃P : Submodule ℝ V, Module.finrank ℝ P < ell ∧
      B < mass w (nearLabels A v r P)) ∨
    ((mass w A-B)^ell ≤ chainMass A v r w ell ∧
      ∀xs∈chains A v r ell, xs.length=ell ∧ (∀z∈xs,z∈A) ∧
        Separated v r xs ∧ LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
        r^(2*ell) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det) := by
  rcases concentration_or_many_chains A v r hr w hw ell B hB with hc | ht
  · exact Or.inl hc
  · refine Or.inr ⟨ht.1,?_⟩
    intro xs hxs
    obtain ⟨hlen,hlabels,hsep,hli,_hdet⟩ := ht.2 xs hxs
    exact ⟨hlen,hlabels,hsep,hli,chains_gram_det_lower A v r hr ell xs hxs⟩

/-- Direct source-facing WZ tuple alternative at one unchanged original cell.
The graph vectors are the actual (slope,1) vectors of the original lines. -/
theorem incident_slope_quantitative_dichotomy {n : ℕ} (D : StickyKakeya4.FiniteScaleSource n)
    (E : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (k : NativeCommonCubicalMesh.Index) (w : (Fin n × NativeCommonCubicalMesh.Index) → ℝ)
    (hw : ∀z,0 ≤ w z) (ell : ℕ) (r : ℝ) (hr : 0 < r) (B : ℝ)
    (hB : B ≤ mass w (E.filter (fun z => z.2=k))) :
    let A := E.filter (fun z => z.2=k)
    let v := fun z : Fin n × NativeCommonCubicalMesh.Index => slopeVector D z.1
    (∃P : Submodule ℝ StickyKakeya4.E4, Module.finrank ℝ P < ell ∧
      B < mass w (nearLabels A v r P)) ∨
    ((mass w A-B)^ell ≤ chainMass A v r w ell ∧
      ∀xs∈chains A v r ell, xs.length=ell ∧ (∀z∈xs,z∈A) ∧
        Separated v r xs ∧ LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
        r^(2*ell) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det) :=
  concentration_or_many_transverse_chains _ _ r hr w hw ell B hB

end NativeDirectionRankWedge
