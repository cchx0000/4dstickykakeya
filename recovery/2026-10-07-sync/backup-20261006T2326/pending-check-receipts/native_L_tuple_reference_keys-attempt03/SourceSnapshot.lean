import Theorems.Thm_StickyKakeya4_native_grain_one_arm_count
import Theorems.Thm_StickyKakeya4_native_literal_reference_angular_cube_source_draft_2214

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section

namespace NativeLTupleReferenceKeys
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry
open NativeGenericReferenceData NativePhysicalReferenceData NativeOriginalParentDensityCore
open NativeTangentGridCoarsening NativeGrainOneArmCount NativeLiteralReferenceShadowCubeDraft2150

abbrev Arm (n : ℕ) := (Index × (Index × Fin n)) × (Index × (Index × Fin n))

def reversed {n : ℕ} (E : Finset (Fin n × Index)) : Finset (Index × Fin n) :=
  E.image Prod.swap

def originalArms {n : ℕ} {G : Type*} [DecidableEq G]
    (E : Finset (Fin n × Index)) (grain : Index → G) : Finset (Arm n) :=
  arms (reversed E) grain

def terminalIncidence {n : ℕ} (w : Arm n) : Fin n × Index := (w.2.2.2,w.2.1)

/-- The last tube and its moved middle point form one genuine old incidence. -/
theorem terminal_incidence_mem {n : ℕ} {G : Type*} [DecidableEq G]
    (E : Finset (Fin n × Index)) (grain : Index → G) (w : Arm n)
    (hw : w ∈ originalArms E grain) : terminalIncidence w ∈ E := by
  have hm := ((mem_arms (reversed E) grain w).mp hw).2.2.2.1
  obtain ⟨z,hz,he⟩ := mem_image.mp hm
  have hs := congrArg Prod.swap he
  have hzEq : z=terminalIncidence w := by simpa [terminalIncidence] using hs
  rw [hzEq] at hz
  exact hz

/-- The occupied last-parent labels over one actual arm-key fiber are
controlled by the same Reference's physical shadow mean. Only the genuine
moved-point common cloud is needed; no direction-intersection count enters. -/
theorem reference_key_fiber_upper {n : ℕ} {G B : Type*} [DecidableEq G] [DecidableEq B]
    {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (hPhysical : HasPhysicalUniformities ref)
    (j : Fin (g+1)) (E : Finset (Fin n × Index)) (hE : E ⊆ ref.E1)
    (grain : Index → G) (base : Arm n → B) (b : B)
    (hCloud : ∀w∈originalArms E grain,∀v∈originalArms E grain,base w=base v →
      dist (cellCenter (mesh D) w.2.1) (cellCenter (mesh D) v.2.1) ≤
        128/((2^(ref.schedule j).val:ℕ):ℝ)) :
    ((((originalArms E grain).filter (fun w => base w=b)).image
      (fun w => parentLabel D ref.a (2^(ref.schedule j).val) w.2.2.2)).card:ℝ) ≤
      625*(coreRadix ref.original ref.R L:ℝ)^4*D.thickness^(-seed)*
        (64/((2^(ref.schedule j).val:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent) := by
  let F := (originalArms E grain).filter (fun w => base w=b)
  let J := F.image terminalIncidence
  by_cases hF : F.Nonempty
  · obtain ⟨v,hv⟩ := hF
    have hJE : J ⊆ ref.E1 := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      exact hE (terminal_incidence_mem E grain w (mem_filter.mp hw).1)
    have hBall : ∀z∈J,dist (cellCenter (mesh D) z.2) (cellCenter (mesh D) v.2.1) ≤
        128/((2^(ref.schedule j).val:ℕ):ℝ) := by
      intro z hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      exact hCloud w (mem_filter.mp hw).1 v (mem_filter.mp hv).1
        ((mem_filter.mp hw).2.trans (mem_filter.mp hv).2.symm)
    have hb := reference_native_ball_parent_upper ref hPhysical j J hJE
      (cellCenter (mesh D) v.2.1) hBall
    simpa only [J,F,image_image,Function.comp_def,terminalIncidence] using hb
  · have hh : F=∅ := not_nonempty_iff_eq_empty.mp hF
    change ((F.image _).card:ℝ) ≤ _
    rw [hh,image_empty,card_empty,Nat.cast_zero]
    have hd := h.1.2.1
    positivity

/-- The entire L-key menu is derived from actual cloud populations, rather
than supplied as a cardinality certificate. The base key may include the
original start, both heights and moved-point spatial cell. -/
theorem reference_key_count {n : ℕ} {G B : Type*} [DecidableEq G] [DecidableEq B]
    {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (hPhysical : HasPhysicalUniformities ref)
    (j : Fin (g+1)) (E : Finset (Fin n × Index)) (hE : E ⊆ ref.E1)
    (grain : Index → G) (base : Arm n → B)
    (hCloud : ∀w∈originalArms E grain,∀v∈originalArms E grain,base w=base v →
      dist (cellCenter (mesh D) w.2.1) (cellCenter (mesh D) v.2.1) ≤
        128/((2^(ref.schedule j).val:ℕ):ℝ)) :
    (((originalArms E grain).image
      (fun w => (base w,parentLabel D ref.a (2^(ref.schedule j).val) w.2.2.2))).card:ℝ) ≤
      (625*(coreRadix ref.original ref.R L:ℝ)^4*D.thickness^(-seed)*
        (64/((2^(ref.schedule j).val:ℕ):ℝ))^(-NativeFixedCompactKakeyaExponent.extremalExponent))*
          ((originalArms E grain).image base).card := by
  let phase := fun w : Arm n => parentLabel D ref.a (2^(ref.schedule j).val) w.2.2.2
  apply image_card_le_real_mul_of_fiber_images (originalArms E grain) (fun w => (base w,phase w)) base
  intro b _hb
  let F := (originalArms E grain).filter (fun w => base w=b)
  have he : F.image (fun w => (base w,phase w))=(F.image phase).image (fun p => (b,p)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hq
      exact mem_image.mpr ⟨phase w,mem_image_of_mem phase hw,
        Prod.ext (mem_filter.mp hw).2.symm rfl⟩
    · intro hq
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hp
      exact mem_image.mpr ⟨w,hw,Prod.ext (mem_filter.mp hw).2 rfl⟩
  change ((F.image (fun w => (base w,phase w))).card:ℝ) ≤ _
  rw [he]
  exact (Nat.cast_le.mpr card_image_le).trans
    (reference_key_fiber_upper ref hPhysical j E hE grain base b hCloud)

end NativeLTupleReferenceKeys
