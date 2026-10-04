import Theorems.Thm_StickyKakeya4_native_dense_source_refinement
import Theorems.Thm_StickyKakeya4_original_height_vertex_density
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeOriginalHeightVertices
open Classical Finset NativeOriginalSlicePopulation OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open scoped BigOperators
variable {T : Type*} [DecidableEq T]

def pointTube (E : Finset (T×Cell)) : Finset (Cell×T) := E.image Prod.swap
def height (mesh : ℝ) (c : Cell) : ℝ := (ShearBinFibers.oldCenter mesh c).2
def heights (E : Finset (T×Cell)) (mesh : ℝ) : Finset ℝ := (E.image Prod.snd).image (height mesh)
lemma mem_pointTube (E : Finset (T×Cell)) (c : Cell) (t : T) :
    (c,t)∈pointTube E ↔ (t,c)∈E := by
  rcases c with ⟨cs,ct⟩
  simp [pointTube,Prod.swap]
lemma pointTube_card (E : Finset (T×Cell)) : (pointTube E).card=E.card :=
  card_image_of_injective _ Prod.swap_injective
lemma pointTube_tubes (E : Finset (T×Cell)) :
    TwoTubePathCollisionCount.tubes (pointTube E)=E.image Prod.fst := by
  simp only [TwoTubePathCollisionCount.tubes,pointTube,image_image]
  rfl
lemma height_index_eq {mesh : ℝ} (hm : 0 < mesh) {c d : Cell}
    (h : height mesh c=height mesh d) : c.2=d.2 := by
  dsimp [height,ShearBinFibers.oldCenter] at h
  have hh : (c.2:ℝ)=(d.2:ℝ) := by nlinarith
  exact_mod_cast hh
lemma floor_height {mesh : ℝ} (hm : 0 < mesh) (c : Cell) : ⌊height mesh c/mesh⌋=c.2 := by
  have he : height mesh c/mesh=(c.2:ℝ)+1/2 := by dsimp [height,ShearBinFibers.oldCenter]; field_simp [hm.ne']
  rw [he,Int.floor_intCast_add]
  norm_num

/-- Integer source cells, at a fixed actual height and fixed original tube,
fit in the explicit 28^3 spatial box. No separated surrogate points are used. -/
theorem pointsAt_bound (E : Finset (T×Cell)) {mesh : ℝ} (hm : 0 < mesh)
    (a b : T→Fin 3→ℝ)
    (hres : ∀ t c,(t,c)∈E→∀ j,
      |(ShearBinFibers.oldCenter mesh c).1 j-b t j-a t j*height mesh c|≤12*mesh)
    (t : T) (z : ℝ) :
    ((pointsAt (pointTube E) (height mesh) t z).card:ℝ)≤21952 := by
  let S := pointsAt (pointTube E) (height mesh) t z
  let box : Finset (Fin 3→ℤ) := Fintype.piFinset fun j=>
    TubeBinCount.coordinateBins 12 ((b t j+a t j*z)/mesh)
  have hinj : Set.InjOn Prod.fst (S:Set Cell) := by
    intro c hc d hd hcd
    apply Prod.ext hcd
    apply height_index_eq hm
    exact ((mem_pointsAt (pointTube E) (height mesh) t z c).mp hc).2.trans
      ((mem_pointsAt (pointTube E) (height mesh) t z d).mp hd).2.symm
  have hsub : S.image Prod.fst⊆box := by
    intro q hq
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hq
    obtain ⟨hcE,hcz⟩ := (mem_pointsAt (pointTube E) (height mesh) t z c).mp hc
    have hct := (mem_pointTube E c t).mp hcE
    apply Fintype.mem_piFinset.mpr
    intro j
    have hh := hres t c hct j
    rw [hcz] at hh
    have he : ((c.1 j:ℝ)+1/2)-(b t j+a t j*z)/mesh=
        ((ShearBinFibers.oldCenter mesh c).1 j-b t j-a t j*z)/mesh := by
      dsimp [ShearBinFibers.oldCenter]
      field_simp [hm.ne']
      ring
    have hn : |((c.1 j:ℝ)+1/2)-(b t j+a t j*z)/mesh|≤12 := by
      rw [he,abs_div,abs_of_pos hm]
      exact (div_le_iff₀ hm).mpr hh
    have hb : |(c.1 j:ℝ)-(b t j+a t j*z)/mesh|≤(12:ℝ)+1 := by
      obtain ⟨hlo,hhi⟩ := abs_le.mp hn
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    simpa only [Int.floor_intCast] using TubeBinCount.floor_mem_coordinateBins 12
      (c.1 j:ℝ) ((b t j+a t j*z)/mesh) hb
  have hc : box.card=21952 := by simp [box,Fintype.card_piFinset,TubeBinCount.coordinateBins_card]
  have hs : S.card=(S.image Prod.fst).card := (card_image_iff.mpr hinj).symm
  exact_mod_cast (show S.card≤21952 by rw [hs,←hc]; exact card_le_card hsub)

omit [DecidableEq T] in
/-- The actual original chart-height alphabet has its cardinality cap from
integer time labels and the proved bounded original time window. -/
theorem heights_bound (E : Finset (T×Cell)) {mesh : ℝ} (hm : 0 < mesh) (hm1 : mesh≤1)
    (htime : ∀ t c,(t,c)∈E→|height mesh c|≤1) :
    mesh*((heights E mesh).card:ℝ)≤4 := by
  have hsub : heights E mesh⊆(TubeBinCount.timeBins mesh).image (fun k:ℤ=>mesh*((k:ℝ)+1/2)) := by
    intro z hz
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hz
    obtain ⟨⟨t,d⟩,htd,he⟩ := mem_image.mp hc
    change d=c at he
    subst d
    refine mem_image.mpr ⟨c.2,?_,rfl⟩
    have hh := TubeBinCount.floor_time_mem mesh (height mesh c) hm (htime t c htd)
    rwa [floor_height hm c] at hh
  have hc : (heights E mesh).card≤(TubeBinCount.timeBins mesh).card :=
    (card_le_card hsub).trans card_image_le
  have hh := mul_le_mul_of_nonneg_left (show ((heights E mesh).card:ℝ)≤(TubeBinCount.timeBins mesh).card by exact_mod_cast hc) hm.le
  exact hh.trans (by simpa only [mul_comm] using TubeBinCount.timeBins_card_mul_scale_le mesh hm hm1)

/-- Actual original grid incidence density supplies the phase consumer's
height/tube vertex mass on the very same original labels. -/
theorem original_height_vertex_density (E : Finset (T×Cell)) {mesh lam : ℝ} (F : ℕ)
    (hm : 0 < mesh) (hm1 : mesh≤1) (hF : 0<F)
    (a b : T→Fin 3→ℝ) (htime : ∀ t c,(t,c)∈E→|height mesh c|≤1)
    (hres : ∀ t c,(t,c)∈E→∀ j,
      |(ShearBinFibers.oldCenter mesh c).1 j-b t j-a t j*height mesh c|≤12*mesh)
    (hden : lam*(E.image Prod.fst).card≤(F:ℝ)*mesh*E.card) :
    (lam/(87808*(F:ℝ)))*((heights E mesh).card:ℝ)*
      (TwoTubePathCollisionCount.tubes (pointTube E)).card≤
        (vertices (pointTube E) (height mesh)).card := by
  have hFr : (0:ℝ)<F := by exact_mod_cast hF
  have hmass : (lam/(F:ℝ))*(TwoTubePathCollisionCount.tubes (pointTube E)).card≤
      mesh*((pointTube E).card:ℝ) := by
    rw [pointTube_tubes,pointTube_card]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hFr).mpr
    simpa only [div_mul_eq_mul_div,mul_assoc,mul_comm,mul_left_comm] using hden
  have hh := OriginalHeightVertexDensity.original_average_height_density
    (pointTube E) (height mesh) (heights E mesh) hm.le
    (show (0:ℝ)<21952 by norm_num) (show (0:ℝ)<4 by norm_num)
    (pointsAt_bound E hm a b hres) hmass (heights_bound E hm hm1 htime)
  have he : (lam/(F:ℝ))/(21952*4)=lam/(87808*(F:ℝ)) := by field_simp; ring
  simpa only [he] using hh

end NativeOriginalHeightVertices
