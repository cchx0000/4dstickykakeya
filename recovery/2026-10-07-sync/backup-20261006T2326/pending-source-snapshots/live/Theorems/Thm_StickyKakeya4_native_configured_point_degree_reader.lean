/- UNVERIFIED draft after the 2026-10-06 10:03 reset.
The three actual third-core slots are read on the same original T. -/
import Theorems.Thm_StickyKakeya4_native_configured_third_relation
import Theorems.Thm_StickyKakeya4_native_retained_slice_count_transfer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeConfiguredPointDegreeReader
open Classical Finset StickyKakeya4 NativeOriginalParentSelection
open NativeJointUniformCoarseRelations NativeConfiguredThirdRelation
open NativeRetainedSliceCountTransfer CanonicalConfiguredE4Bridge
open NativeHorizontalGrainSlice NativeReferenceXYGridPoints SelfUniform

/-- The actual height cell in the final /512 physical coordinates. -/
def height (m R : ℕ) (x : E4) : ℤ := ⌊x (3 : Fin 4) / ((mu m * (R : ℝ)) / 512)⌋

section ActualKeys
variable {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
  (s : Split) (P : Submodule ℝ E4) (hP : P ≤ heightKernel)
  (hd : Module.finrank ℝ P = tangentDim s)
  (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
  (R u : ℕ)

lemma height_readback (hR : 0 < R) (k : NativeCommonCubicalMesh.Index) :
    height m R (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R k) =
      NativeTranslatedGrainHeightOverlap.translatedHeight D a m k / ((8 * R : ℕ) : ℤ) := by
  rw [height, NativeActualConfiguredPoint.point, NativeActualConfiguredPoint.graphGrid_height,
    NativeActualConfiguredPoint.sourceLabel_height]
  have hh := NativeConfiguredTimeCoarsening.floor_finalTime
    (mu m * (R : ℝ)) (mul_pos (mu_pos m) (by exact_mod_cast hR)) 1
    (NativeTranslatedGrainHeightOverlap.translatedHeight D a m k / ((8 * R : ℕ) : ℤ))
  simpa using hh

/-- The actual coarse-Y key is constant on complete configured-point
fibers. This is recovered from the literal graph coordinates, without a
claim that the four integer graph parameters are physical cube indices. -/
theorem coarseY_eq_of_point_eq (hR : 0 < R)
    (k l : NativeCommonCubicalMesh.Index)
    (he : NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R k =
      NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R l) :
    coarseYKey D a m p s P hP hd F Fcfg R k =
      coarseYKey D a m p s P hP hd F Fcfg R l := by
  have hh := (NativeActualConfiguredResidue.graphGrid_eq_iff_keys s (mu m) R
    (mu_pos m) hR F Fcfg
    (NativeActualConfiguredPoint.sourceLabel D a m p s P hP hd F k)
    (NativeActualConfiguredPoint.sourceLabel D a m p s P hP hd F l)).mp he
  exact Prod.ext hh.1 hh.2.2

/-- A literal whole-coarse-Y selection also keeps every surviving
configured-point fiber whole. Its third-core point weights are therefore
unchanged until a subsequent geometric recoding or finer cut occurs. -/
theorem coarseY_cut_point_fibers (hR : 0 < R)
    (T : Finset (Fin n × NativeCommonCubicalMesh.Index))
    (B : Finset (ℤ × CanonicalGridRecoding.Grid (normalDim s))) :
    let point := fun z : Fin n × NativeCommonCubicalMesh.Index =>
      NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2
    let U := T.filter (fun z => coarseYKey D a m p s P hP hd F Fcfg R z.2 ∈ B)
    ∀ x ∈ U, U.filter (fun z => point z = point x) = T.filter (fun z => point z = point x) := by
  intro point U x hx
  have hB := (mem_filter.mp hx).2
  ext z
  simp only [U, mem_filter]
  constructor
  · exact fun hz => ⟨hz.1.1, hz.2⟩
  · rintro ⟨hz, he⟩
    have hkey := coarseY_eq_of_point_eq D a m p s P hP hd F Fcfg R hR z.2 x.2 he
    exact ⟨⟨hz, by simpa only [hkey] using hB⟩, he⟩

/-- Restricting to a final height is a union of entire actual point fibers
and entire geometric-pair fibers, independently of the old fine heights. -/
theorem height_fibers (T : Finset (Fin n × NativeCommonCubicalMesh.Index)) (h : ℤ) :
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    let Tz := T.filter (fun z => height m R (pair z).2 = h)
    ∀ x ∈ Tz,
      Tz.filter (fun z => pair z = pair x) = T.filter (fun z => pair z = pair x) ∧
      Tz.filter (fun z => (pair z).2 = (pair x).2) =
        T.filter (fun z => (pair z).2 = (pair x).2) := by
  intro pair Tz x hx
  have hh := (mem_filter.mp hx).2
  constructor
  · ext z
    simp only [Tz, mem_filter]
    constructor
    · exact fun hz => ⟨hz.1.1, hz.2⟩
    · rintro ⟨hz, he⟩
      exact ⟨⟨hz, by simpa only [he] using hh⟩, he⟩
  · ext z
    simp only [Tz, mem_filter]
    constructor
    · exact fun hz => ⟨hz.1.1, hz.2⟩
    · rintro ⟨hz, he⟩
      exact ⟨⟨hz, by simpa only [he] using hh⟩, he⟩

/-- The same original restriction has precisely the corresponding height
layer in its deduplicated pair image. No geometric pairs are filled in. -/
theorem height_image (T : Finset (Fin n × NativeCommonCubicalMesh.Index)) (h : ℤ) :
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    (T.filter (fun z => height m R (pair z).2 = h)).image pair =
      (T.image pair).filter (fun z => height m R z.2 = h) := by
  intro pair
  ext z
  constructor
  · rintro hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    exact mem_filter.mpr ⟨mem_image_of_mem pair (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩
  · rintro hz
    obtain ⟨hz, hh⟩ := mem_filter.mp hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, hh⟩, rfl⟩

/-- The actual point fiber in the deduplicated incidence image is the
image of its complete original antecedent fiber. -/
theorem point_image (T : Finset (Fin n × NativeCommonCubicalMesh.Index)) (x : E4) :
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    (T.filter (fun z => (pair z).2 = x)).image pair =
      (T.image pair).filter (fun z => z.2 = x) := by
  intro pair
  ext z
  constructor
  · rintro hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    exact mem_filter.mpr ⟨mem_image_of_mem pair (mem_filter.mp hw).1, (mem_filter.mp hw).2⟩
  · rintro hz
    obtain ⟨hz, he⟩ := mem_filter.mp hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    exact mem_image.mpr ⟨w, mem_filter.mpr ⟨hw, he⟩, rfl⟩

/-- A geometric degree is exactly a DISTINCT final phase-parent count
on the original point antecedents. No original-edge cardinal is used in
place of that count. This reads the angular population upper into G(T). -/
theorem point_degree_eq_phase_count
    (T : Finset (Fin n × NativeCommonCubicalMesh.Index)) (x : E4) :
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    ((T.image pair).filter (fun z => z.2 = x)).card =
      ((T.filter (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2 = x)).image
        (fun z => NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^(u+12)) z.1)).card := by
  intro pair
  rw [← point_image D a m p s P hP hd F Fcfg R u T x]
  let E := T.filter (fun z => (pair z).2 = x)
  have hinj : Set.InjOn (Prod.fst : Parent × E4 → Parent) (E.image pair) := by
    intro z hz w hw he
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hz
    obtain ⟨v', hv', rfl⟩ := mem_image.mp hw
    exact Prod.ext he ((mem_filter.mp hv).2.trans (mem_filter.mp hv').2.symm)
  calc
    _ = ((E.image pair).image Prod.fst).card := (card_image_of_injOn hinj).symm
    _ = _ := by rw [image_image]; rfl

/-- Decode the two installed comparisons directly into point degrees of
G = the literal geometric-pair image. The Q^4 factor comes from the existing
weighted-to-distinct-population theorem, not from a new uniformity premise. -/
theorem from_caller {d : ℕ}
    (extra : Fin d → (Fin n × NativeCommonCubicalMesh.Index) →
      (Fin n × NativeCommonCubicalMesh.Index) → Prop)
    (T : Finset (Fin n × NativeCommonCubicalMesh.Index)) (Q : ℕ)
    (H : ∀ j x y, x ∈ T → y ∈ T →
      degree (fun _ : Fin n × NativeCommonCubicalMesh.Index => 1)
        (completeRelations D a m p s P hP hd F Fcfg R u extra j) T x ≤
      Q ^ 2 * degree (fun _ : Fin n × NativeCommonCubicalMesh.Index => 1)
        (completeRelations D a m p s P hP hd F Fcfg R u extra j) T y) :
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    HasUniformFibers (T.image pair) (Q ^ 2) Prod.snd ∧
      ∀ h : ℤ,
        let Tz := T.filter (fun z => height m R (pair z).2 = h)
        HasUniformFibers Tz Q pair ∧
          HasUniformFibers Tz Q (fun z => (pair z).2) ∧
          HasUniformFibers (Tz.image pair) (Q ^ 2) Prod.snd := by
  intro pair
  have HP : HasUniformFibers T Q pair :=
    caller_geometricPair_uniformity D a m p s P hP hd F Fcfg R u extra T Q H
  have HX : HasUniformFibers T Q (fun z => (pair z).2) :=
    caller_configuredPoint_uniformity D a m p s P hP hd F Fcfg R u extra T Q H
  have hG := point_class_homogeneity T pair Prod.snd Q HP HX
  constructor
  · intro x hx y hy
    simpa only [show (Q ^ 2) ^ 2 = Q ^ 4 by ring] using hG x hx y hy
  · intro h Tz
    have hTZ : Tz ⊆ T := filter_subset _ _
    have hf := height_fibers D a m p s P hP hd F Fcfg R u T h
    have HPz : HasUniformFibers Tz Q pair := by
      intro x hx y hy
      rw [(hf x hx).1, (hf y hy).1]
      exact HP x (hTZ hx) y (hTZ hy)
    have HXz : HasUniformFibers Tz Q (fun z => (pair z).2) := by
      intro x hx y hy
      rw [(hf x hx).2, (hf y hy).2]
      exact HX x (hTZ hx) y (hTZ hy)
    refine ⟨HPz, HXz, ?_⟩
    have hh := point_class_homogeneity Tz pair Prod.snd Q HPz HXz
    intro x hx y hy
    simpa only [show (Q ^ 2) ^ 2 = Q ^ 4 by ring] using hh x hx y hy

/-- Original weighted edges, geometric pairs, and physical points remain
three literal finite sets. Their retention costs are read from the actual
same-height uniformities, with no population or AD certificate. -/
theorem retention_from_caller {d : ℕ}
    (extra : Fin d → (Fin n × NativeCommonCubicalMesh.Index) →
      (Fin n × NativeCommonCubicalMesh.Index) → Prop)
    (T : Finset (Fin n × NativeCommonCubicalMesh.Index)) (Q : ℕ)
    (H : ∀ j x y, x ∈ T → y ∈ T →
      degree (fun _ : Fin n × NativeCommonCubicalMesh.Index => 1)
        (completeRelations D a m p s P hP hd F Fcfg R u extra j) T x ≤
      Q ^ 2 * degree (fun _ : Fin n × NativeCommonCubicalMesh.Index => 1)
        (completeRelations D a m p s P hP hd F Fcfg R u extra j) T y)
    (h : ℤ) :
    let pair := geometricPairKey D a m p s P hP hd F Fcfg R u
    let Tz := T.filter (fun z => height m R (pair z).2 = h)
    let Gz := Tz.image pair
    (∀ U ⊆ Tz, ∀ lambda loss : ℝ, 0 ≤ loss →
      lambda * (Tz.card : ℝ) ≤ loss * U.card →
      lambda * (Gz.card : ℝ) ≤ loss * (Q : ℝ)^2 * (U.image pair).card ∧
      lambda * ((Gz.image Prod.snd).card : ℝ) ≤
        loss * (Q : ℝ)^2 * ((U.image pair).image Prod.snd).card) ∧
    (∀ J ⊆ Gz, ∀ lambda loss : ℝ, 0 ≤ loss →
      lambda * (Gz.card : ℝ) ≤ loss * J.card →
      lambda * ((Gz.image Prod.snd).card : ℝ) ≤
        loss * (Q : ℝ)^4 * (J.image Prod.snd).card) := by
  intro pair Tz Gz
  obtain ⟨HP, HX, HG⟩ := (from_caller D a m p s P hP hd F Fcfg R u extra T Q H).2 h
  by_cases hn : Tz.Nonempty
  · constructor
    · intro U hU lambda loss hloss hret
      have hp := point_image_retention Tz U hU hn pair Q HP lambda loss hloss hret
      have hx := point_image_retention Tz U hU hn (fun z => (pair z).2) Q HX lambda loss hloss hret
      refine ⟨hp, ?_⟩
      simpa only [Gz, image_image, Function.comp_apply] using hx
    · intro J hJ lambda loss hloss hret
      have hh := point_image_retention Gz J hJ (hn.image pair) Prod.snd (Q^2) HG
        lambda loss hloss hret
      simpa only [Nat.cast_pow, show ((Q : ℝ)^2)^2 = (Q : ℝ)^4 by ring] using hh
  · have he : Tz = ∅ := not_nonempty_iff_eq_empty.mp hn
    constructor
    · intro U hU lambda loss _hloss _hret
      have hUe : U = ∅ := eq_empty_of_subset_empty (by simpa only [he] using hU)
      simp only [Gz, he, hUe, image_empty, card_empty, Nat.cast_zero, mul_zero, le_refl, and_self]
    · intro J hJ lambda loss _hloss _hret
      have hJe : J = ∅ := eq_empty_of_subset_empty (by simpa only [Gz, he, image_empty] using hJ)
      simp only [Gz, he, hJe, image_empty, card_empty, Nat.cast_zero, mul_zero, le_refl]

end ActualKeys

end NativeConfiguredPointDegreeReader
