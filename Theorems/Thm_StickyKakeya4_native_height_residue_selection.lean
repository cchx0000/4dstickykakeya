import Theorems.Thm_StickyKakeya4_native_parent_height_alignment

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeHeightResidueSelection
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeParentHeightAlignment NativeWeightedHeightNodeSelection
open NativeCompatibleAngularCandidates
open scoped BigOperators

/-- Equal modulo-three coarse cells cannot straddle a boundary at a distance
smaller than one cell width. Negative original height labels are included. -/
lemma same_residue_close_quotient (x y d : ℤ) (hd : 0 < d)
    (hmod : (x/d)%3=(y/d)%3) (hclose : |x-y|<d) : x/d=y/d := by
  have hx0 := Int.emod_nonneg x hd.ne'
  have hy0 := Int.emod_nonneg y hd.ne'
  have hxd := Int.emod_lt_of_pos x hd
  have hyd := Int.emod_lt_of_pos y hd
  have hx := Int.emod_add_mul_ediv x d
  have hy := Int.emod_add_mul_ediv y d
  have hdist := abs_lt.mp hclose
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hgap : x/d+3 ≤ y/d := by omega
    have hm := mul_le_mul_of_nonneg_right hgap hd.le
    nlinarith
  · have hgap : y/d+3 ≤ x/d := by omega
    have hm := mul_le_mul_of_nonneg_right hgap hd.le
    nlinarith

/-- A fixed finite menu costs only3^J of ORIGINAL node weight. It imposes one
coarse-height residue per scale without any height-density premise. -/
theorem select_height_residues {J : ℕ} (A : Finset Index) (w : Index → ℕ)
    (m : ℕ) (depth : Fin J → ℕ) (hpos : 0<∑u∈A,w u) :
    ∃B⊆A,B.Nonempty ∧ (∑u∈A,w u) ≤ 3^J*(∑u∈B,w u) ∧
      ∀j u v,u∈B→v∈B→
        spatialAncestor m (depth j) u (3:Fin 4)%3=
          spatialAncestor m (depth j) v (3:Fin 4)%3 := by
  let color : Fin J → Index → Fin 3 := fun j u =>
    ⟨(spatialAncestor m (depth j) u (3:Fin 4)%3).toNat,by
      have h0 := Int.emod_nonneg (spatialAncestor m (depth j) u (3:Fin 4)) (by norm_num : (3:ℤ)≠0)
      have h3 := Int.emod_lt_of_pos (spatialAncestor m (depth j) u (3:Fin 4)) (by norm_num : (0:ℤ)<3)
      omega⟩
  have hcap : ∀j t,((A.filter (fun _ => ()=t)).image (color j)).card ≤ 3 := by
    intro j t
    exact (card_le_univ _).trans_eq (Fintype.card_fin 3)
  obtain ⟨B,hBA,hBn,hmass,halign⟩ := weighted_height_node_selection_nonempty
    w A color (fun _ _ => ()) 3 hcap hpos
  refine ⟨B,hBA,hBn,hmass,?_⟩
  intro j u v hu hv
  have hh := congrArg Fin.val (halign j u v hu hv rfl)
  change (spatialAncestor m (depth j) u (3:Fin 4)%3).toNat=
    (spatialAncestor m (depth j) v (3:Fin 4)%3).toNat at hh
  have hu0 := Int.emod_nonneg (spatialAncestor m (depth j) u (3:Fin 4)) (by norm_num : (3:ℤ)≠0)
  have hv0 := Int.emod_nonneg (spatialAncestor m (depth j) v (3:Fin 4)) (by norm_num : (3:ℤ)≠0)
  omega

/-- The actual selected raw nodes share a coarser HEIGHT ancestor whenever
their fine height labels are closer than that ancestor width. -/
lemma selected_close_heights_same_ancestor {m d : ℕ} {u v : Index}
    (hmod : spatialAncestor m d u (3:Fin 4)%3=spatialAncestor m d v (3:Fin 4)%3)
    (hclose : |u (3:Fin 4)-v (3:Fin 4)| < ((2^(m-d):ℕ):ℤ)) :
    spatialAncestor m d u (3:Fin 4)=spatialAncestor m d v (3:Fin 4) := by
  exact same_residue_close_quotient _ _ _ (by positivity) hmod hclose

/-- Apply the residue selection to whole ORIGINAL incidence nodes. The
existing exact mixed-grain preservation lemmas apply to this literal nodeCut. -/
theorem exists_residue_separated_node_cut {n J : ℕ} (D : FiniteScaleSource n)
    (m : ℕ) (depth : Fin J → ℕ) (E : Finset (Fin n × Index)) (hEn : E.Nonempty) :
    ∃B⊆E.image (fineNode D m),B.Nonempty ∧ (nodeCut D m E B).Nonempty ∧
      E.card ≤ 3^J*(nodeCut D m E B).card ∧
      ∀j u v,u∈B→v∈B→
        |u (3:Fin 4)-v (3:Fin 4)| < ((2^(m-depth j):ℕ):ℤ)→
          spatialAncestor m (depth j) u (3:Fin 4)=spatialAncestor m (depth j) v (3:Fin 4) := by
  have hpos : 0<∑u∈E.image (fineNode D m),nodeWeight D m E u := by
    rw [nodeWeight_total]
    exact card_pos.mpr hEn
  obtain ⟨B,hBE,hBn,hmass,hcolor⟩ := select_height_residues
    (E.image (fineNode D m)) (nodeWeight D m E) m depth hpos
  have hcount : E.card ≤ 3^J*(nodeCut D m E B).card := by
    rw [nodeCut_card]
    simpa only [nodeWeight_total] using hmass
  have hcut : (nodeCut D m E B).Nonempty := by
    apply card_pos.mp
    have hh := card_pos.mpr hEn
    by_contra hn
    have hz : (nodeCut D m E B).card=0 := by omega
    rw [hz,Nat.mul_zero] at hcount
    omega
  refine ⟨B,hBE,hBn,hcut,hcount,?_⟩
  intro j u v hu hv hclose
  exact selected_close_heights_same_ancestor (hcolor j u v hu hv) hclose

end NativeHeightResidueSelection
