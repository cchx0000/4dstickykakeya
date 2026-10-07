import Theorems.Thm_StickyKakeya4_native_conditional_coarse_interpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeRankOneReferenceUpper
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeIncidenceMultiplicityTower NativeCoarseUniformImageDegrees NativeConditionedPairMenu
open scoped BigOperators

lemma point_degree_le_reference_mean {T X : Type*} [DecidableEq T] [DecidableEq X]
    (I : Finset (T × X)) (rad : ℕ) (H : HasUniformFibers I rad Prod.snd) (x : X) :
    ((I.filter (fun z => z.2=x)).card:ℝ) ≤ (rad:ℝ)^2*multiplicity I := by
  by_cases hI : I.Nonempty
  · have hs : (0:ℝ) < (I.image Prod.snd).card := by
      exact_mod_cast card_pos.mpr (hI.image Prod.snd)
    have hc := point_fiber_card_cross I (fun z => z) (rad^2) H x
    simp only [image_id'] at hc
    change ((I.filter (fun z => z.2=x)).card:ℝ) ≤ (rad:ℝ)^2*((I.card:ℝ)/(I.image Prod.snd).card)
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hs).mpr
    exact_mod_cast hc
  · rw [not_nonempty_iff_eq_empty.mp hI]
    simp [NativeIncidenceMultiplicityTower.multiplicity]

/-- A geometrically bounded number of parent labels at each retained point,
combined with the ORIGINAL reference point degrees, bounds the selected
multiplicity. There is no native admission or inverse retention for F. -/
theorem selected_parent_cap_upper {T X P : Type*} [DecidableEq T]
    [DecidableEq X] [DecidableEq P] (I F : Finset (T × X)) (hFI : F ⊆ I)
    (f : T → P) (rad K : ℕ) (U : ℝ) (hU : 0 ≤ U)
    (H : ∀p,HasUniformFibers (parent I f p) rad Prod.snd)
    (hupper : ∀p,(parent I f p).Nonempty → multiplicity (parent I f p) ≤ U)
    (hcap : ∀x∈F.image Prod.snd,
      ((F.filter (fun z => z.2=x)).image (fun z => f z.1)).card ≤ K) :
    multiplicity F ≤ (K:ℝ)*(rad:ℝ)^2*U := by
  have hrow (x : X) (hx : x∈F.image Prod.snd) :
      ((F.filter (fun z => z.2=x)).card:ℝ) ≤ (K:ℝ)*(rad:ℝ)^2*U := by
    let A := F.filter (fun z => z.2=x)
    have he : (A.card:ℝ) = ∑p∈A.image (fun z => f z.1),
        ((A.filter (fun z => f z.1=p)).card:ℝ) := by
      exact_mod_cast card_eq_sum_card_image (fun z => f z.1) A
    have hsingle (p : P) (hp : p∈A.image (fun z => f z.1)) :
        ((A.filter (fun z => f z.1=p)).card:ℝ) ≤ (rad:ℝ)^2*U := by
      have hsub : A.filter (fun z => f z.1=p) ⊆
          (parent I f p).filter (fun z => z.2=x) := by
        intro z hz
        obtain ⟨hzA,hzp⟩ := mem_filter.mp hz
        obtain ⟨hzF,hzx⟩ := mem_filter.mp hzA
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨hFI hzF,hzp⟩,hzx⟩
      obtain ⟨z,hz,hzp⟩ := mem_image.mp hp
      have hpn : (parent I f p).Nonempty :=
        ⟨z,mem_filter.mpr ⟨hFI (mem_filter.mp hz).1,hzp⟩⟩
      have hb := point_degree_le_reference_mean (parent I f p) rad (H p) x
      have hc : ((A.filter (fun z => f z.1=p)).card:ℝ) ≤
          ((parent I f p).filter (fun z => z.2=x)).card := by exact_mod_cast card_le_card hsub
      exact hc.trans (hb.trans (mul_le_mul_of_nonneg_left (hupper p hpn) (sq_nonneg _)))
    change (A.card:ℝ) ≤ _
    rw [he]
    calc
      _ ≤ ∑_p∈A.image (fun z => f z.1),(rad:ℝ)^2*U := sum_le_sum hsingle
      _ = ((A.image (fun z => f z.1)).card:ℝ)*((rad:ℝ)^2*U) := by simp
      _ ≤ (K:ℝ)*((rad:ℝ)^2*U) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcap x hx) (mul_nonneg (sq_nonneg _) hU)
      _ = _ := by ring
  by_cases hF : F.Nonempty
  · have hs : (0:ℝ) < (F.image Prod.snd).card := by
      exact_mod_cast card_pos.mpr (hF.image Prod.snd)
    have he : (F.card:ℝ) = ∑x∈F.image Prod.snd,((F.filter (fun z => z.2=x)).card:ℝ) := by
      exact_mod_cast card_eq_sum_card_image Prod.snd F
    apply (div_le_iff₀ hs).mpr
    rw [he]
    calc
      _ ≤ ∑_x∈F.image Prod.snd,(K:ℝ)*(rad:ℝ)^2*U := sum_le_sum hrow
      _ = _ := by simp; ring
  · rw [not_nonempty_iff_eq_empty.mp hF]
    simp only [NativeIncidenceMultiplicityTower.multiplicity,image_empty,card_empty,Nat.cast_zero,div_zero]
    positivity

/-- Direct old-incidence readback: the installed original parent/point
relation supplies the required conditional degrees for every parent. -/
theorem original_selected_parent_cap_upper {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (m : ℕ) (E1 F : Finset (Fin n × Index)) (hF : F ⊆ E1)
    (rad K : ℕ) (U : ℝ) (hU : 0 ≤ U)
    (H : HasUniformFibers E1 rad (formalPair D a m))
    (hupper : ∀p,(parentEdges D a (2^m) E1 p).Nonempty →
      multiplicity (parentEdges D a (2^m) E1 p) ≤ U)
    (hcap : ∀k∈F.image Prod.snd,
      ((F.filter (fun z => z.2=k)).image (fun z => parentLabel D a (2^m) z.1)).card ≤ K) :
    multiplicity F ≤ (K:ℝ)*(rad:ℝ)^2*U := by
  apply selected_parent_cap_upper E1 F hF (parentLabel D a (2^m)) rad K U hU _ hupper hcap
  intro p
  exact conditioned_uniformity E1 (fun z => parentLabel D a (2^m) z.1) Prod.snd rad H p

end NativeRankOneReferenceUpper
