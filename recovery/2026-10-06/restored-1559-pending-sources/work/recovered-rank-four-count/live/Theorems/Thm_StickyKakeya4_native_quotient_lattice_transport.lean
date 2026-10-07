import Theorems.Thm_StickyKakeya4_native_two_map_retained_slice_labels
import Theorems.Thm_StickyKakeya4_native_slice_class_balls
import Theorems.Thm_StickyKakeya4_finite_voronoi_real_ad_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeQuotientLatticeTransport
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open GridQuotientAD NativeTwoMapRetainedSliceLabels NativeSliceClassBalls
open NativeAnisotropicSliceLabels NativeSliceCountComparison

/-- The same occupied XY labels at one literal translated height. -/
def productSlice {k l : ℕ} (S : Finset (XY k l)) (height : ℤ) : Finset (Point k l) :=
  (S.filter (fun z => z.1=height)).image Prod.snd

def atHeight {k l : ℕ} (hd : k+l=3) (height : ℤ) (p : Point k l) : Index :=
  encode hd (height,p)

lemma atHeight_injective {k l : ℕ} (hd : k+l=3) (height : ℤ) :
    Function.Injective (atHeight hd height) := by
  intro p q hpq
  exact congrArg Prod.snd ((encode_injective hd) hpq)

lemma height_slice_eq {k l : ℕ} (hd : k+l=3) (S : Finset (XY k l)) (height : ℤ) :
    heightSlice (S.image (encode hd)) height=(productSlice S height).image (atHeight hd height) := by
  ext u
  simp only [heightSlice,productSlice,mem_filter,mem_image]
  constructor
  · rintro ⟨⟨z,hz,rfl⟩,hh⟩
    have hzh : z.1=height := by simpa only [encode_height] using hh
    refine ⟨z.2,⟨z,⟨hz,hzh⟩,rfl⟩,?_⟩
    dsimp only [atHeight]
    congr 1
    exact Prod.ext hzh.symm rfl
  · rintro ⟨p,⟨z,⟨hz,hzh⟩,rfl⟩,rfl⟩
    have he : atHeight hd height z.2=encode hd z := by
      dsimp only [atHeight]
      congr 1
      exact Prod.ext hzh.symm rfl
    rw [he]
    exact ⟨⟨z,hz,rfl⟩,by simpa only [encode_height] using hzh⟩

lemma spatial_box_iff {k l : ℕ} (hd : k+l=3) (height : ℤ)
    (p q : Point k l) (R : ℕ) :
    (∀i : Fin 3,|atHeight hd height p i.castSucc-atHeight hd height q i.castSucc|≤(R:ℤ)) ↔
      p.1∈box q.1 R ∧ p.2∈box q.2 R := by
  rw [mem_box_iff,mem_box_iff]
  constructor
  · intro H
    constructor
    · intro j
      simpa only [atHeight,encode_left] using H (Fin.cast hd (Fin.castAdd l j))
    · intro j
      simpa only [atHeight,encode_right] using H (Fin.cast hd (Fin.natAdd k j))
  · rintro ⟨HX,HY⟩ i
    have hcast : Fin.cast hd (Fin.cast hd.symm i)=i := Fin.ext rfl
    rw [←hcast]
    generalize Fin.cast hd.symm i=j
    refine Fin.addCases ?_ ?_ j
    · intro z
      simpa only [atHeight,encode_left] using HX z
    · intro z
      simpa only [atHeight,encode_right] using HY z

/-- Exact finite-set identification, with no change of point set or weights. -/
lemma spatial_ball_eq {k l : ℕ} (hd : k+l=3) (height : ℤ)
    (A : Finset (Point k l)) (p : Point k l) (R : ℕ) :
    spatialBall (A.image (atHeight hd height)) R (atHeight hd height p)=
      (ambientBox A p R).image (atHeight hd height) := by
  ext u
  simp only [spatialBall,ambientBox,mem_filter,mem_image]
  constructor
  · rintro ⟨⟨q,hq,rfl⟩,_hh,hbox⟩
    exact ⟨q,⟨hq,(spatial_box_iff hd height q p R).mp hbox⟩,rfl⟩
  · rintro ⟨q,⟨hq,hbox⟩,rfl⟩
    exact ⟨⟨q,hq,rfl⟩,by simp only [atHeight,encode_height],
      (spatial_box_iff hd height q p R).mpr hbox⟩

lemma ambient_box_real_card {k l : ℕ} (hd : k+l=3) (height : ℤ)
    (A : Finset (Point k l)) (p : Point k l) {mu : ℝ} (hmu : 0 < mu) (R : ℕ) :
    ((realizedSlice (A.image (atHeight hd height)) mu height).filter
      (fun x => dist x (realized mu (atHeight hd height p)) ≤ mu*(R:ℝ))).card=
        (ambientBox A p R).card := by
  have hh : atHeight hd height p (3:Fin 4)=height := encode_height hd _
  have he := realized_ball_card (A.image (atHeight hd height)) hmu R (atHeight hd height p)
  rw [hh,spatial_ball_eq] at he
  exact he.trans (card_image_of_injective _ (atHeight_injective hd height))

lemma realized_slice_eq {k l : ℕ} (hd : k+l=3) (S : Finset (XY k l))
    (height : ℤ) (mu : ℝ) :
    realizedSlice (S.image (encode hd)) mu height=
      realizedSlice ((productSlice S height).image (atHeight hd height)) mu height := by
  unfold realizedSlice
  rw [height_slice_eq]
  congr 1
  symm
  apply filter_eq_self.mpr
  intro u hu
  obtain ⟨p,_hp,rfl⟩ := mem_image.mp hu
  exact encode_height hd _

/-- Actual sup-metric AD bounds become the exact integer boxes required by
GridQuotientAD; the physical radius restriction is explicit. -/
theorem ambient_bounds_of_AD {k l : ℕ} (hd : k+l=3) (S : Finset (XY k l))
    (height : ℤ) {mu K t : ℝ} (hmu : 0 < mu)
    (H : FiniteVoronoiRealADCoarsening.ADBounds
      (realizedSlice (S.image (encode hd)) mu height) mu K t)
    (p : Point k l) (hp : p∈productSlice S height) (R : ℕ)
    (hR : 1≤R) (hRone : mu*(R:ℝ)≤1) :
    (R:ℝ)^t/K≤((ambientBox (productSlice S height) p R).card:ℝ) ∧
      ((ambientBox (productSlice S height) p R).card:ℝ)≤K*(R:ℝ)^t := by
  rw [realized_slice_eq hd S height mu] at H
  have hcenter : realized mu (atHeight hd height p)∈
      realizedSlice ((productSlice S height).image (atHeight hd height)) mu height := by
    apply mem_image.mpr
    refine ⟨atHeight hd height p,mem_filter.mpr ⟨mem_image.mpr ⟨p,hp,rfl⟩,?_⟩,rfl⟩
    exact encode_height hd _
  have hlow : mu ≤ mu*(R:ℝ) := by
    have hh : (1:ℝ)≤R := by exact_mod_cast hR
    nlinarith only [hh,hmu]
  have hh := H _ hcenter (mu*(R:ℝ)) hlow hRone
  have he : mu*(R:ℝ)/mu=(R:ℝ) := by field_simp
  dsimp only [FiniteVoronoiPopulation.carrierBall] at hh
  rw [ambient_box_real_card hd height _ p hmu R,he] at hh
  exact hh

end NativeQuotientLatticeTransport
