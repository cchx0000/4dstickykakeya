import Theorems.Thm_StickyKakeya4_native_dyadic_coarse_normalization
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000
noncomputable section
namespace NativeCoarseActualHeightVertices
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalSlicePopulation OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open NativeOriginalHeightVertices (height height_index_eq floor_height)
open NativeOriginalParentSelection NativeSourceCoarseReadback NativeDyadicCoarseNormalization
variable {T : Type*} [DecidableEq T]
def actualHeights (I : Finset (Cell×T)) (mesh : ℝ) : Finset ℝ :=
  I.image (fun e => height mesh e.1)
/-- Actual coarse grid labels have the explicit 30^3 occupancy cap from
 their proved residual13 times mesh. No old-chart identification is used. -/
theorem coarse_pointsAt_bound (I : Finset (Cell×T)) {mesh : ℝ} (hm : 0 < mesh)
    (a b : T→Fin 3→ℝ)
    (hres : ∀ c t,(c,t)∈I→∀ j,
      |(ShearBinFibers.oldCenter mesh c).1 j-b t j-a t j*height mesh c|≤13*mesh)
    (t : T) (z : ℝ) :
    ((pointsAt I (height mesh) t z).card:ℝ)≤27000 := by
  let S := pointsAt I (height mesh) t z
  let box : Finset (Fin 3→ℤ) := Fintype.piFinset fun j=>
    TubeBinCount.coordinateBins 13 ((b t j+a t j*z)/mesh)
  have hinj : Set.InjOn Prod.fst (S:Set Cell) := by
    intro c hc d hd hcd
    apply Prod.ext hcd
    apply height_index_eq hm
    exact ((mem_pointsAt I (height mesh) t z c).mp hc).2.trans
      ((mem_pointsAt I (height mesh) t z d).mp hd).2.symm
  have hsub : S.image Prod.fst⊆box := by
    intro q hq
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hq
    obtain ⟨hcE,hcz⟩ := (mem_pointsAt I (height mesh) t z c).mp hc
    apply Fintype.mem_piFinset.mpr
    intro j
    have hh := hres c t hcE j
    rw [hcz] at hh
    have he : ((c.1 j:ℝ)+1/2)-(b t j+a t j*z)/mesh=
        ((ShearBinFibers.oldCenter mesh c).1 j-b t j-a t j*z)/mesh := by
      dsimp [ShearBinFibers.oldCenter]
      field_simp [hm.ne']
      ring
    have hn : |((c.1 j:ℝ)+1/2)-(b t j+a t j*z)/mesh|≤13 := by
      rw [he,abs_div,abs_of_pos hm]
      exact (div_le_iff₀ hm).mpr hh
    have hb : |(c.1 j:ℝ)-(b t j+a t j*z)/mesh|≤(13:ℝ)+1 := by
      obtain ⟨hlo,hhi⟩ := abs_le.mp hn
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    simpa only [Int.floor_intCast] using TubeBinCount.floor_mem_coordinateBins 13
      (c.1 j:ℝ) ((b t j+a t j*z)/mesh) hb
  have hc : box.card=27000 := by simp [box,Fintype.card_piFinset,TubeBinCount.coordinateBins_card]
  have hs : S.card=(S.image Prod.fst).card := (card_image_iff.mpr hinj).symm
  exact_mod_cast (show S.card≤27000 by rw [hs,←hc]; exact card_le_card hsub)

/-- The actual normalized coarse heights have their cardinality bound from
 the original integer labels and the proved normalized unit box. -/
theorem actual_heights_bound (I : Finset (Cell×T)) {mesh : ℝ} (hm : 0 < mesh) (hm1 : mesh ≤ 1)
    (htime : ∀ c t, (c,t) ∈ I → |height mesh c| ≤ 1) : mesh*((actualHeights I mesh).card:ℝ) ≤ 4 := by
  have hread : NativeOriginalHeightVertices.heights (I.image Prod.swap) mesh=actualHeights I mesh := by
    simp only [NativeOriginalHeightVertices.heights,actualHeights,image_image]
    rfl
  rw [←hread]
  apply NativeOriginalHeightVertices.heights_bound (I.image Prod.swap) hm hm1
  intro t c htc
  obtain ⟨⟨d,s⟩,he,hds⟩ := mem_image.mp htc
  have hs : s=t := congrArg Prod.fst hds
  have hd : d=c := congrArg Prod.snd hds
  subst s
  subst d
  exact htime c t he
omit [DecidableEq T] in
/-- Separation belongs to the same actual height image, at its actual mesh. -/
theorem actual_heights_separated (I : Finset (Cell×T)) {mesh : ℝ} (hm : 0 < mesh) :
    ∀ z ∈ actualHeights I mesh, ∀ w ∈ actualHeights I mesh, z ≠ w → mesh ≤ |z-w| := by
  intro z hz w hw hzw
  obtain ⟨e,_he,rfl⟩ := mem_image.mp hz
  obtain ⟨f,_hf,rfl⟩ := mem_image.mp hw
  have hidx : e.1.2 ≠ f.1.2 := by
    intro hh
    apply hzw
    simp only [height,ShearBinFibers.oldCenter,hh]
  exact NativeCoarseOriginalHeights.integer_center_gap hm e.1.2 f.1.2 hidx
/-- A genuine average incidence density supplies the original W vertex mass
 on the actual coarse I,Z, with every occupancy and height cap derived. -/
theorem actual_coarse_height_vertex_density (I : Finset (Cell×T)) {mesh lambda : ℝ}
    (hm : 0 < mesh) (hm1 : mesh ≤ 1) (a b : T → Fin 3 → ℝ)
    (htime : ∀ c t, (c,t) ∈ I → |height mesh c| ≤ 1)
    (hres : ∀ c t, (c,t) ∈ I → ∀ j,
      |(ShearBinFibers.oldCenter mesh c).1 j-b t j-a t j*height mesh c| ≤ 13*mesh)
    (hden : lambda*(TwoTubePathCollisionCount.tubes I).card ≤ mesh*(I.card:ℝ)) :
    (lambda/108000)*((actualHeights I mesh).card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤
      (vertices I (height mesh)).card := by
  have hh := OriginalHeightVertexDensity.original_average_height_density I (height mesh) (actualHeights I mesh)
    hm.le (show (0:ℝ)<27000 by norm_num) (show (0:ℝ)<4 by norm_num)
    (coarse_pointsAt_bound I hm a b hres) hden (actual_heights_bound I hm hm1 htime)
  simpa only [show (27000:ℝ)*4=108000 by norm_num] using hh

/-- End-to-end SAME E0 to actual normalized coarse I,Z vertex density.
 The geometry is the R=32 physical image from the source constructor.
 This is aggregate density, not per-tube shading regularity. -/
theorem exists_native_coarse_height_vertices {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i,D.shading i=wzCellShading (NativeOriginalParentSelection.mesh D) cells i)
    (hne : (NativeCubicalIncidenceCounts.incidences cells).Nonempty) (hexp : 0 ≤ eta+beta)
    (htube : ∀ i,(ENNReal.ofReal D.thickness).rpow (3+beta) ≤
      MeasureTheory.volume (markedUnitTube (D.line i) D.thickness))
    (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*(D.thickness/8) ≤ 1)
    {L d : ℕ} (hL : 0 < L) (radii timeDiv : Fin d → ℕ) (offsetMesh slopeMesh : Fin d → ℝ) :
    ∃ a : ℝ, ∃ p ∈ parents D a N, ∃ E0 : Finset (Fin n × Index),
      E0 ⊆ NativeCubicalIncidenceCounts.incidences cells ∧
      let P := data D cells a N p
      let I := originalFamily P (shift D a) E0
      let deltaNew := (N:ℝ)*D.thickness/256
      let Z := I.image (fun e => NativeCoarseOriginalIncidences.height P 32 e.1)
      P.Hypotheses ∧ I.Nonempty ∧ TwoTubePathCollisionCount.tubes I=E0.image Prod.fst ∧
      E0.card ≤ N*I.card ∧
      (D.thickness^(eta+beta)/(32*(NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ)))*
        (TwoTubePathCollisionCount.tubes I).card ≤ deltaNew*(I.card:ℝ) ∧
      (∀ e ∈ I, |NativeCoarseOriginalIncidences.height P 32 e.1| ≤ 1 ∧
        (∀ j, |(NativeCoarseOriginalIncidences.coordinates P 32 e.1).1 j| ≤ 1) ∧
        (∀ j, |(NativeCoarseOriginalIncidences.coordinates P 32 e.1).1 j-P.offset e.2 j/32-
          P.slope e.2 j*NativeCoarseOriginalIncidences.height P 32 e.1| ≤ 13*deltaNew)) ∧
      (D.thickness^(eta+beta)/(3456000*(NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ)))*
        (Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card ≤
          (vertices I (NativeCoarseOriginalIncidences.height P 32)).card := by
  obtain ⟨a,p,hp,E0,hE0,hP,hI,hT,hcap,hden,hgeo⟩ := exists_actual_dyadic_coarse_family
    h cells hcells hne hexp htube N hN hscale hL radii timeDiv offsetMesh slopeMesh
  let P := data D cells a N p
  let I := originalFamily P (shift D a) E0
  let mesh : ℝ := (N:ℝ)*D.thickness/256
  change ∀ e ∈ I, |NativeCoarseOriginalIncidences.height P 32 e.1| ≤ 1 ∧
    (∀ j, |(NativeCoarseOriginalIncidences.coordinates P 32 e.1).1 j| ≤ 1) ∧
    (∀ j, |(NativeCoarseOriginalIncidences.coordinates P 32 e.1).1 j-P.offset e.2 j/32-
      P.slope e.2 j*NativeCoarseOriginalIncidences.height P 32 e.1| ≤ 13*mesh) at hgeo
  have hmesh : P.σ/32=mesh := native_dyadic_scale D cells a N p
  have hm : 0 < mesh := by rw [←hmesh]; exact div_pos (P.scale_pos hP) (by norm_num)
  have hm1 : mesh ≤ 1 := by dsimp [mesh]; nlinarith only [hscale]
  have hheight : NativeCoarseOriginalIncidences.height P 32=height mesh := by
    funext c
    simp only [NativeCoarseOriginalIncidences.height,NativeCoarseOriginalIncidences.coordinates,height,hmesh]
  have htime : ∀ c t, (c,t) ∈ I → |height mesh c| ≤ 1 := by
    intro c t hct
    simpa only [hheight] using (hgeo (c,t) hct).1
  have hres : ∀ c t, (c,t) ∈ I → ∀ j,
      |(ShearBinFibers.oldCenter mesh c).1 j-P.offset t j/32-P.slope t j*height mesh c| ≤ 13*mesh := by
    intro c t hct j
    simpa only [NativeCoarseOriginalIncidences.coordinates,hmesh,hheight] using (hgeo (c,t) hct).2.2 j
  have hv := actual_coarse_height_vertex_density I hm hm1 P.slope (fun t j => P.offset t j/32) htime hres hden
  refine ⟨a,p,hp,E0,hE0,hP,hI,hT,hcap,hden,hgeo,?_⟩
  have hcoef : (32*(NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ))*108000=
      3456000*(NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ) := by ring
  change (D.thickness^(eta+beta)/(3456000*(NativeSelectedPhysicalMultiplicity.refinementLoss d L:ℝ)))*
    ((I.image (fun e => NativeCoarseOriginalIncidences.height P 32 e.1)).card:ℝ)*
      (TwoTubePathCollisionCount.tubes I).card ≤ (vertices I (NativeCoarseOriginalIncidences.height P 32)).card
  rw [hheight]
  simpa only [actualHeights,div_div,hcoef] using hv
end NativeCoarseActualHeightVertices
