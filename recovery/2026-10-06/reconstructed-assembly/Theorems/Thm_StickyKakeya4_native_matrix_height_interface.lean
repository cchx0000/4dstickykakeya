/- NEW DRAFT, 2026-10-06. UNVERIFIED: no source or imported-axiom check.
The matrix norm is explicitly the elementwise supremum norm used by the
native chart sources. Vectorization is proved here, not supplied as input. -/
import Theorems.Thm_StickyKakeya4_native_matrix_height_wholepoint
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
noncomputable section

namespace NativeMatrixHeightInterface
open Classical Finset NativeMatrixHeightWholePoint
open scoped BigOperators Matrix.Norms.Elementwise

/-- The rank-two matrix has exactly one column; all its entries occur in
this literal two-coordinate vector. -/
theorem two_by_one_distance (A B : Matrix (Fin 2) (Fin 1) ℝ) :
    dist (fun i : Fin 2 => A i 0) (fun i : Fin 2 => B i 0)=‖A-B‖ := by
  apply le_antisymm
  · apply (dist_pi_le_iff_of_nonneg (norm_nonneg (A-B))).mpr
    intro i
    simpa only [Real.dist_eq,Real.norm_eq_abs,Matrix.sub_apply] using
      (Matrix.norm_entry_le_entrywise_sup_norm (A-B) (i:=i) (j:=0))
  · apply (Matrix.norm_le_iff dist_nonneg).mpr
    intro i j
    have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simpa only [Real.dist_eq,Real.norm_eq_abs,Matrix.sub_apply] using
      (dist_le_pi_dist (fun i : Fin 2 => A i 0) (fun i : Fin 2 => B i 0) i)

/-- The rank-three matrix has exactly one row; all its entries occur in
this literal two-coordinate vector. -/
theorem one_by_two_distance (A B : Matrix (Fin 1) (Fin 2) ℝ) :
    dist (fun j : Fin 2 => A 0 j) (fun j : Fin 2 => B 0 j)=‖A-B‖ := by
  apply le_antisymm
  · apply (dist_pi_le_iff_of_nonneg (norm_nonneg (A-B))).mpr
    intro j
    simpa only [Real.dist_eq,Real.norm_eq_abs,Matrix.sub_apply] using
      (Matrix.norm_entry_le_entrywise_sup_norm (A-B) (i:=0) (j:=j))
  · apply (Matrix.norm_le_iff dist_nonneg).mpr
    intro i j
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simpa only [Real.dist_eq,Real.norm_eq_abs,Matrix.sub_apply] using
      (dist_le_pi_dist (fun j : Fin 2 => A 0 j) (fun j : Fin 2 => B 0 j) j)

lemma entry_count (ell : ℕ) (hell : ell=2 ∨ ell=3) :
    Fintype.card (Fin (4-ell) × Fin (ell-1))=2 := by
  rcases hell with rfl | rfl <;> norm_num

/-- A proved two-entry readback for either actual rank. The existential
only abbreviates one of the two explicit coordinate maps above. -/
theorem exists_entry_readback (ell : ℕ) (hell : ell=2 ∨ ell=3) :
    ∃entry : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ → (Fin 2 → ℝ),
      ∀A B,dist (entry A) (entry B)=‖A-B‖ := by
  rcases hell with rfl | rfl
  · exact ⟨fun A i => A i 0,two_by_one_distance⟩
  · exact ⟨fun A j => A 0 j,one_by_two_distance⟩

/-- The source matrix function F and its height label are fixed marks.
Its original elementwise matrix Lipschitz inequality supplies the vector
inequality internally. The selected set gets a literal matrix norm bound
with constant one on every prepared actual height grid. -/
theorem select_matrix_points {P H : Type*}
    (ell : ℕ) (hell : ell=2 ∨ ell=3) (K : ℕ)
    (A : Finset P) (w : P → ℕ) (height : P → ℝ) (label : P → H)
    (F : H → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (L d : ℝ) (hL : 0 ≤ L) (hd : 0 < d)
    (rho shift : Fin K → ℝ) (hbase : ∀i,d ≤ rho i)
    (hLip : ∀x∈A,∀y∈A,‖F (label x)-F (label y)‖ ≤ L*|height x-height y|) :
    ∃B⊆A,mass A w ≤ (modulus L)^(2*K)*mass B w ∧
      (mass A w:ℝ) ≤ (9*(1+L)^2)^K*mass B w ∧
      ∀i,∀x∈B,∀y∈B,
        heightCell (rho i) (shift i) (height x)=heightCell (rho i) (shift i) (height y) →
          ‖F (label x)-F (label y)‖ < rho i := by
  obtain ⟨entry,hentry⟩ := exists_entry_readback ell hell
  have hEntryLip : ∀x∈A,∀y∈A,
      dist (entry (F (label x))) (entry (F (label y))) ≤ L*|height x-height y| := by
    intro x hx y hy
    rw [hentry]
    exact hLip x hx y hy
  obtain ⟨B,hBA,hret,hretR,hcoh⟩ := select_above_base K A w height
    (fun x => entry (F (label x))) L d hL hd rho shift hbase hEntryLip
  refine ⟨B,hBA,hret,hretR,?_⟩
  intro i x hx y hy heq
  have hh := hcoh i x hx y hy heq
  rw [hentry] at hh
  exact hh

/-- Actual original-edge realization. Each surviving original point keeps
its entire old edge fiber. The two-entry vector is internal and the final
conclusion is on the unchanged source matrix F itself. -/
theorem select_matrix_edges {E P H : Type*} [DecidableEq P]
    (ell : ℕ) (hell : ell=2 ∨ ell=3) (K : ℕ)
    (A : Finset E) (point : E → P) (height : P → ℝ) (label : P → H)
    (F : H → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (L d : ℝ) (hL : 0 ≤ L) (hd : 0 < d)
    (rho shift : Fin K → ℝ) (hbase : ∀i,d ≤ rho i)
    (hLip : ∀x∈A.image point,∀y∈A.image point,
      ‖F (label x)-F (label y)‖ ≤ L*|height x-height y|) :
    ∃B⊆A.image point,let T := edgeLift A point B
      T⊆A ∧ A.card ≤ (modulus L)^(2*K)*T.card ∧
      (A.card:ℝ) ≤ (9*(1+L)^2)^K*T.card ∧
      (∀p∈B,T.filter (fun x => point x=p)=A.filter (fun x => point x=p)) ∧
      ∀i,∀x∈T,∀y∈T,
        heightCell (rho i) (shift i) (height (point x))=
          heightCell (rho i) (shift i) (height (point y)) →
        ‖F (label (point x))-F (label (point y))‖ < rho i := by
  obtain ⟨entry,hentry⟩ := exists_entry_readback ell hell
  have hEntryLip : ∀x∈A.image point,∀y∈A.image point,
      dist (entry (F (label x))) (entry (F (label y))) ≤ L*|height x-height y| := by
    intro x hx y hy
    rw [hentry]
    exact hLip x hx y hy
  obtain ⟨B,hB,hTA,hret,hretR,hfiber,hcoh⟩ := select_original_edge_menu A point K height
    (fun x => entry (F (label x))) L d hL hd rho shift hbase hEntryLip
  refine ⟨B,hB,hTA,hret,hretR,hfiber,?_⟩
  intro i x hx y hy heq
  have hh := hcoh i x hx y hy heq
  rw [hentry] at hh
  exact hh

end NativeMatrixHeightInterface
