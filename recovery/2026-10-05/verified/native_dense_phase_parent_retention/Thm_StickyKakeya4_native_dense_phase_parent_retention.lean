import Theorems.Thm_StickyKakeya4_native_parent_point_region_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeDensePhaseParentRetention
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeParentPointRegionCounts NativeIncidenceMultiplicityTower
open scoped BigOperators

/-- Actual total edge retention selects one occupied original class with
the same paid local retention ratio. No lower is asserted in other classes. -/
theorem exists_retained_fiber {A P : Type*} [DecidableEq P]
    (I J : Finset A) (hJI : J⊆I) (hI : I.Nonempty) (f : A → P)
    (lambda G : ℝ) (hlambda : 0<lambda) (hret : lambda*(I.card:ℝ) ≤ G*J.card) :
    ∃p∈I.image f,(I.filter (fun z => f z=p)).Nonempty ∧
      (J.filter (fun z => f z=p)).Nonempty ∧
      lambda*((I.filter (fun z => f z=p)).card:ℝ) ≤ G*(J.filter (fun z => f z=p)).card := by
  have hsI : (∑p∈I.image f,((I.filter (fun z => f z=p)).card:ℝ))=(I.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image f I).symm
  have hsJ : (∑p∈I.image f,((J.filter (fun z => f z=p)).card:ℝ))=(J.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_fiberwise (s:=J) (t:=I.image f)
      (f:=f) (fun z hz => mem_image_of_mem f (hJI hz))).symm
  have hs : (∑p∈I.image f,lambda*((I.filter (fun z => f z=p)).card:ℝ)) ≤
      ∑p∈I.image f,G*((J.filter (fun z => f z=p)).card:ℝ) := by
    rw [←mul_sum,←mul_sum,hsI,hsJ]
    exact hret
  obtain ⟨p,hp,hlocal⟩ := exists_le_of_sum_le (hI.image f) hs
  have hIp : (I.filter (fun z => f z=p)).Nonempty := by
    obtain ⟨z,hz,hzp⟩ := mem_image.mp hp
    exact ⟨z,mem_filter.mpr ⟨hz,hzp⟩⟩
  have hJp : (J.filter (fun z => f z=p)).Nonempty := by
    have hpos : (0:ℝ)<lambda*((I.filter (fun z => f z=p)).card:ℝ) :=
      mul_pos hlambda (by exact_mod_cast card_pos.mpr hIp)
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero,mul_zero] at hlocal
    linarith
  exact ⟨p,hp,hIp,hJp,hlocal⟩

/-- On an unchanged uniform reference, actual edge retention implies
support retention with only two radix powers. No uniformity of J is used. -/
theorem support_retention {T X : Type*} [DecidableEq T] [DecidableEq X]
    (I J : Finset (T × X)) (hJI : J⊆I) (hI : I.Nonempty) (Q : ℕ)
    (H : HasUniformFibers I Q Prod.snd) (lambda G : ℝ) (hG : 0 ≤ G)
    (hret : lambda*(I.card:ℝ) ≤ G*J.card) :
    lambda*(I.image Prod.snd).card ≤ G*(Q:ℝ)^2*(J.image Prod.snd).card := by
  have hIp : (0:ℝ)<(I.image Prod.snd).card := by exact_mod_cast card_pos.mpr (hI.image Prod.snd)
  have hIc : (0:ℝ)<I.card := by exact_mod_cast card_pos.mpr hI
  have hmu : 0 < multiplicity I := div_pos hIc hIp
  have hread : multiplicity I*(I.image Prod.snd).card=(I.card:ℝ) :=
    div_mul_cancel₀ _ hIp.ne'
  have hupper := subset_region_upper I J hJI Q H (fun _ => True)
  simp only [regionEdges,regionPoints,filter_true] at hupper
  have hcross : multiplicity I*(lambda*(I.image Prod.snd).card) ≤
      multiplicity I*(G*(Q:ℝ)^2*(J.image Prod.snd).card) := by
    calc
      _ = lambda*(multiplicity I*(I.image Prod.snd).card) := by ring
      _ = lambda*(I.card:ℝ) := by rw [hread]
      _ ≤ G*J.card := hret
      _ ≤ G*((Q:ℝ)^2*multiplicity I*(J.image Prod.snd).card) := mul_le_mul_of_nonneg_left hupper hG
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hmu).mp hcross

/-- The actual E1 source and paid final edge retention select a literal
coarse phase-parent with both local edge and distinct-old-point retention.
The reference parent remains E1 and its original R is never replaced. -/
theorem source_dense_parent {n d g level : ℕ} {D : FiniteScaleSource n}
    {eta zeta a : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 J : Finset (Fin n × Index)) (hJ : J⊆E1)
    (L : ℕ) (schedule : Fin g → Fin (level+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : IsCore D original R a eta zeta (menuSize d g) g L
      (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E1)
    (j : Fin g) (lambda G : ℝ) (hlambda : 0<lambda) (hG : 0 ≤ G)
    (hret : lambda*(E1.card:ℝ) ≤ G*J.card) :
    ∃p∈R.image (parentLabel D a (2^(schedule j).val)),
      (parentEdges D a (2^(schedule j).val) E1 p).Nonempty ∧
      (parentEdges D a (2^(schedule j).val) J p).Nonempty ∧
      lambda*((parentEdges D a (2^(schedule j).val) E1 p).card:ℝ) ≤
        G*(parentEdges D a (2^(schedule j).val) J p).card ∧
      lambda*((parentEdges D a (2^(schedule j).val) E1 p).image Prod.snd).card ≤
        G*(coreRadix original R L:ℝ)^2*((parentEdges D a (2^(schedule j).val) J p).image Prod.snd).card := by
  obtain ⟨p,hp,hI,hJp,hlocal⟩ := exists_retained_fiber E1 J hJ H.2.1
    (fun z => parentLabel D a (2^(schedule j).val) z.1) lambda G hlambda hret
  have hsub : parentEdges D a (2^(schedule j).val) J p⊆parentEdges D a (2^(schedule j).val) E1 p :=
    filter_subset_filter _ hJ
  refine ⟨p,?_,hI,hJp,hlocal,?_⟩
  · obtain ⟨z,hz,hzp⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨z.1,(mem_filter.mp (H.1 hz)).2,hzp⟩
  · exact support_retention _ _ hsub hI _
      (core_parent_point_uniformity h original R E1 L schedule Rel H j p) lambda G hG hlocal

/-- A point cut and a phase-parent restriction commute as literal edge
filters. Their mass must still use the restricted parent's point weights. -/
lemma parent_region_commute {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) (test : Index → Prop) :
    parentEdges D a N (regionEdges E test) p=regionEdges (parentEdges D a N E p) test := by
  ext z
  simp only [parentEdges,regionEdges,mem_filter]
  tauto

end NativeDensePhaseParentRetention
