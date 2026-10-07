import Theorems.Thm_StickyKakeya4_compact_front

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace MarkedIsometricChart
open Classical StickyKakeya4
open scoped RealInnerProductSpace

def point (O : E4 ≃ₗᵢ[ℝ] E4) (c x : E4) : E4 := O (x-c)

/-- The affine mark changes along with the perpendicular offset. Keeping
only the rotated direction would describe the wrong unit segment. -/
def line (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (l : MarkedLine) : MarkedLine :=
  ((O (direction l),O (offset l-c+(inner ℝ c (direction l)) • direction l)),
    mark l-(inner ℝ c (direction l)))

lemma point_isometry (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) : Isometry (point O c) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [point,LinearIsometryEquiv.dist_map,dist_sub_right]

lemma point_surjective (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) : Function.Surjective (point O c) := by
  intro x
  refine ⟨O.symm x+c,?_⟩
  simp only [point,add_sub_cancel_right,LinearIsometryEquiv.apply_symm_apply]

lemma valid_line (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (l : MarkedLine) (hl : IsValidLine l) :
    IsValidLine (line O c l) := by
  constructor
  · simpa only [line,direction,LinearIsometryEquiv.norm_map] using hl.1
  · change inner ℝ (O (offset l-c+(inner ℝ c (direction l)) • direction l)) (O (direction l))=0
    rw [LinearIsometryEquiv.inner_map_map,inner_add_left,inner_sub_left,real_inner_smul_left,
      real_inner_self_eq_norm_sq,hl.1,hl.2]
    ring

/-- The physical relative time remains the SAME original unit-interval
parameter under the isometric chart. -/
theorem raw_front_readback (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (l : MarkedLine) (t : ℝ) :
    rawFrontParam (line O c l,t)=point O c (rawFrontParam (l,t)) := by
  change O (offset l-c+(inner ℝ c (direction l)) • direction l)+
    ((mark l-(inner ℝ c (direction l)))+t) • O (direction l)=O ((offset l+(mark l+t) • direction l)-c)
  rw [←map_smul,←map_add]
  congr 1
  rw [add_assoc,←add_smul]
  have hs : (inner ℝ c (direction l))+(mark l-(inner ℝ c (direction l))+t)=mark l+t := by ring
  rw [hs]
  abel

/-- Exact front support, including every original affine mark. -/
theorem unitFront_image (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (L : Set MarkedLine) :
    unitFront (line O c '' L)=point O c '' unitFront L := by
  ext x
  constructor
  · rintro ⟨l,⟨l0,hl0,rfl⟩,t,ht,rfl⟩
    refine ⟨rawFrontParam (l0,t),⟨l0,hl0,t,ht,rfl⟩,?_⟩
    exact (raw_front_readback O c l0 t).symm
  · rintro ⟨x,⟨l,hl,t,ht,rfl⟩,rfl⟩
    exact ⟨line O c l,Set.mem_image_of_mem _ hl,t,ht,(raw_front_readback O c l t).symm⟩

theorem tube_membership (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (l : MarkedLine) (delta : ℝ) (x : E4) :
    point O c x∈markedUnitTube (line O c l) delta ↔ x∈markedUnitTube l delta := by
  have hf : unitFront {line O c l}=point O c '' unitFront {l} := by
    simpa only [Set.image_singleton] using unitFront_image O c {l}
  change Metric.infDist (point O c x) (unitFront {line O c l})≤delta ↔
    Metric.infDist x (unitFront {l})≤delta
  rw [hf,Metric.infDist_image (point_isometry O c)]

theorem tube_image (O : E4 ≃ₗᵢ[ℝ] E4) (c : E4) (l : MarkedLine) (delta : ℝ) :
    markedUnitTube (line O c l) delta=point O c '' markedUnitTube l delta := by
  ext x
  obtain ⟨y,rfl⟩ := point_surjective O c x
  rw [tube_membership]
  constructor
  · intro hy
    exact Set.mem_image_of_mem _ hy
  · rintro ⟨z,hz,he⟩
    have hzy := (point_isometry O c).injective he
    simpa only [hzy] using hz

end MarkedIsometricChart
