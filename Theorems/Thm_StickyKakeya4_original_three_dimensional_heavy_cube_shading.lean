import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_parameters
import Theorems.Thm_StickyKakeya4_graph_tube_grid_cover

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace OriginalThreeDimensionalTubeCells
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters

def cell (rho : ℝ) (x : Point3) : Fin 3→ℤ := fun j => ⌊x j/rho⌋

/-- The actual bounded pair tube meets at most 384/rho literal global
rho-cubes, derived from its original largest-coordinate graph geometry. -/
theorem original_pair_tube_cell_count (P : Finset Point3) (z : Pair3) (rho : ℝ)
    (i : Fin 3) (hrho : 0<rho) (hrho1 : rho≤1)
    (hne : z.2 i-z.1 i≠0) (hmax : ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hbox : ∀ p∈P, ∀ j, |p j|≤1) :
    (((physicalPairTube3 P rho z).image (cell rho)).card : ℝ)*rho≤384 := by
  let T := physicalPairTube3 P rho z
  let a : Fin 2→ℝ := fun j => slope z i (i.succAbove j)
  let b : Fin 2→ℝ := fun j => offset z i (i.succAbove j)
  have hc := GraphTubeGridCover.occupied_cells_bound T (GraphTubeGridCover.chart i)
    rho (-1) 2 2 a b hrho (by linarith only [hrho1])
    (fun j => original_slope_bound z i hne hmax (i.succAbove j))
    (fun x hx => by
      have hh := hbox x (Finset.mem_filter.mp hx).1 i
      dsimp [GraphTubeGridCover.chart]
      constructor <;> linarith only [(abs_le.mp hh).1,(abs_le.mp hh).2])
    (fun x hx j => by
      have hh := original_tube_graph_residual z i x rho hne hmax (Finset.mem_filter.mp hx).2 (i.succAbove j)
      change |x (i.succAbove j)-offset z i (i.succAbove j)-slope z i (i.succAbove j)*x i|≤2*rho
      have he : x (i.succAbove j)-offset z i (i.succAbove j)-slope z i (i.succAbove j)*x i=
          x (i.succAbove j)-(slope z i (i.succAbove j)*x i+offset z i (i.succAbove j)) := by ring
      rw [he]
      exact hh)
  have heq : T.image (fun x => GraphTubeGridCover.gridBin rho (GraphTubeGridCover.chart i x))=
      (T.image (cell rho)).image (GraphTubeGridCover.integerChart i) := by
    rw [Finset.image_image]
    rfl
  rw [heq,Finset.card_image_of_injective _ (GraphTubeGridCover.integerChart_injective i)] at hc
  norm_num at hc
  exact hc

/-- A common actual cube is Euclidean-small, independently of its
location. This is the physical support transfer for the heavy-cube shading. -/
theorem original_cell_distance (rho : ℝ) (x y : Point3) (hrho : 0<rho)
    (hcell : cell rho x=cell rho y) : distance3 x y≤2*rho := by
  have hb (j : Fin 3) : |x j-y j|≤rho :=
    FiniteTransverseMenuGrowth.same_floor_abs_sub_le hrho (congrFun hcell j)
  have hs (j : Fin 3) : (x j-y j)^2≤rho^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb j) 2
  unfold distance3
  apply (Real.sqrt_le_left (by positivity : 0≤2*rho)).mpr
  nlinarith only [hs 0,hs 1,hs 2,sq_nonneg rho]

end OriginalThreeDimensionalTubeCells

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalHeavyCubes
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeCells

def cubeFiber (P : Finset Point3) (rho : ℝ) (c : Fin 3→ℤ) : Finset Point3 :=
  P.filter (fun x => cell rho x=c)

def heavyCubes (P : Finset Point3) (rho W : ℝ) : Finset (Fin 3→ℤ) :=
  (P.image (cell rho)).filter (fun c => W≤((cubeFiber P rho c).card : ℝ))

def kept (P T : Finset Point3) (rho W : ℝ) : Finset Point3 :=
  T.filter (fun x => cell rho x∈heavyCubes P rho W)

/-- Global heavy cubes have disjoint original fibers, so their complete
mass is paid once by the original point source. -/
theorem original_heavy_cube_budget (P : Finset Point3) (rho W : ℝ) :
    W*(heavyCubes P rho W).card≤P.card := by
  have hlow : W*(heavyCubes P rho W).card≤
      ∑ c∈heavyCubes P rho W, ((cubeFiber P rho c).card : ℝ) := by
    calc
      _ = ∑ _c∈heavyCubes P rho W, W := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2)
  have hpart := Finset.sum_card_fiberwise_eq_card_filter P (heavyCubes P rho W) (cell rho)
  have hpartR : (∑ c∈heavyCubes P rho W, ((cubeFiber P rho c).card : ℝ))=
      ((P.filter (fun x => cell rho x∈heavyCubes P rho W)).card : ℝ) := by
    exact_mod_cast hpart
  rw [hpartR] at hlow
  exact hlow.trans (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _)))

/-- Deleting globally light cubes costs at most threshold times the
actual number of original cube labels met by this particular tube. -/
theorem original_light_cube_loss (P T : Finset Point3) (rho W : ℝ)
    (hTP : T⊆P) (hW : 0≤W) :
    ((T.filter (fun x => cell rho x∉heavyCubes P rho W)).card : ℝ)≤
      (T.image (cell rho)).card*W := by
  let B := T.filter (fun x => cell rho x∉heavyCubes P rho W)
  apply FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers B (T.image (cell rho)) (cell rho) W
  · intro x hx
    exact Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).1,rfl⟩
  · intro c _hc
    by_cases hne : (B.filter (fun x => cell rho x=c)).Nonempty
    · obtain ⟨x,hx⟩ := hne
      obtain ⟨hxB,hxc⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxT,hxlight⟩ := Finset.mem_filter.mp hxB
      have hlt : ((cubeFiber P rho c).card : ℝ)<W := by
        by_contra hh
        apply hxlight
        rw [hxc]
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,hTP hxT,hxc⟩,le_of_not_gt hh⟩
      have hsub : B.filter (fun x => cell rho x=c)⊆cubeFiber P rho c := by
        intro y hy
        obtain ⟨hyB,hyc⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_filter.mpr ⟨hTP (Finset.mem_filter.mp hyB).1,hyc⟩
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hlt.le
    · have he : B.filter (fun x => cell rho x=c)=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simpa only [he,Finset.card_empty,Nat.cast_zero] using hW

/-- Actual rich original pair tubes retain half their mass after one
GLOBAL heavy-cube cut. No per-tube renormalization is performed. -/
theorem original_rich_tube_kept_mass (P : Finset Point3) (z : Pair3) (rho nu : ℝ)
    (i : Fin 3) (hrho : 0<rho) (hrho1 : rho≤1) (hnu : 0≤nu)
    (hne : z.2 i-z.1 i≠0) (hmax : ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hbox : ∀ p∈P, ∀ j, |p j|≤1)
    (hrich : nu*rho*P.card≤((physicalPairTube3 P rho z).card : ℝ)) :
    nu*rho*P.card/2≤
      ((kept P (physicalPairTube3 P rho z) rho (nu*rho^2*P.card/768)).card : ℝ) := by
  let T := physicalPairTube3 P rho z
  let W := nu*rho^2*P.card/768
  have hW : 0≤W := by dsimp [W]; positivity
  have hloss := original_light_cube_loss P T rho W (Finset.filter_subset _ _) hW
  have hc := original_pair_tube_cell_count P z rho i hrho hrho1 hne hmax hbox
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0≤nu*rho*P.card/768 by positivity)
  have hbound : (T.image (cell rho)).card*W≤nu*rho*P.card/2 := by
    dsimp [T,W]
    nlinarith only [hm]
  have hpart := Finset.card_filter_add_card_filter_not (s:=T)
    (fun x => cell rho x∈heavyCubes P rho W)
  have hpartR : ((kept P T rho W).card : ℝ)+
      ((T.filter (fun x => cell rho x∉heavyCubes P rho W)).card : ℝ)=T.card := by
    exact_mod_cast hpart
  change nu*rho*P.card/2≤((kept P T rho W).card : ℝ)
  change nu*rho*P.card≤(T.card : ℝ) at hrich
  linarith only [hloss,hbound,hpartR,hrich]

end OriginalThreeDimensionalHeavyCubes

namespace OriginalThreeDimensionalHeavyCubes
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeCells

/-- Original Euclidean two-Frostman bounds control each actual cube fiber. -/
theorem original_cube_two_frostman (P : Finset Point3) (delta eta rho : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card)
    (c : Fin 3→ℤ) : ((cubeFiber P rho c).card : ℝ)≤4*delta^(-eta)*rho^2*P.card := by
  have hrho : 0<rho := hd.trans_le hquery
  have hK : 1≤delta^(-eta) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd hd1
      (show -eta≤0 by linarith only [heta])
  by_cases hne : (cubeFiber P rho c).Nonempty
  · obtain ⟨p,hp⟩ := hne
    obtain ⟨hpP,hpc⟩ := Finset.mem_filter.mp hp
    by_cases hs : 2*rho≤1
    · have hsub : cubeFiber P rho c⊆P.filter (fun q => distance3 p q≤2*rho) := by
        intro q hq
        obtain ⟨hqP,hqc⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨hqP,original_cell_distance rho p q hrho (hpc.trans hqc.symm)⟩
      have hc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (hfrostman p hpP (2*rho) (by linarith only [hquery,hrho]) hs)
      nlinarith only [hc]
    · have hc : ((cubeFiber P rho c).card : ℝ)≤P.card :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      have hh : 1≤4*delta^(-eta)*rho^2 := by
        have hm := mul_le_mul_of_nonneg_right hK (sq_nonneg rho)
        nlinarith only [hm,lt_of_not_ge hs]
      exact hc.trans (by
        have hm := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg P.card)
        simpa only [one_mul] using hm)
  · have he : cubeFiber P rho c=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

/-- The global heavy cubes have the required inverse-square-scale budget
and every actual rich tube has a quantitatively dense original cube shading.
The source is unchanged; both counts are derived from its literal fibers. -/
theorem original_rich_tube_heavy_cube_shading (P : Finset Point3) (z : Pair3)
    (delta eta rho nu : ℝ) (i : Fin 3)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho)
    (hrho1 : rho≤1) (hnu : 0≤nu) (hP : P.Nonempty)
    (hne : z.2 i-z.1 i≠0) (hmax : ∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|)
    (hbox : ∀ p∈P, ∀ j, |p j|≤1)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card)
    (hrich : nu*rho*P.card≤((physicalPairTube3 P rho z).card : ℝ)) :
    let W := nu*rho^2*P.card/768
    let Q := kept P (physicalPairTube3 P rho z) rho W
    nu*rho^2*(heavyCubes P rho W).card≤768 ∧
      nu≤8*delta^(-eta)*rho*(Q.image (cell rho)).card ∧
      nu*rho*P.card/2≤(Q.card : ℝ) := by
  have hrho : 0<rho := hd.trans_le hquery
  have hPp : 0<(P.card : ℝ) := by exact_mod_cast hP.card_pos
  let W := nu*rho^2*P.card/768
  let Q := kept P (physicalPairTube3 P rho z) rho W
  have hkeep := original_rich_tube_kept_mass P z rho nu i hrho hrho1 hnu hne hmax hbox hrich
  have hbudget := original_heavy_cube_budget P rho W
  have hglobal : nu*rho^2*(heavyCubes P rho W).card≤768 := by
    apply (mul_le_mul_iff_of_pos_right hPp).mp
    dsimp [W] at hbudget ⊢
    nlinarith only [hbudget]
  have hsub : Q⊆P := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hcount := FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers Q (Q.image (cell rho))
    (cell rho) (4*delta^(-eta)*rho^2*P.card)
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) (by
      intro c _hc
      have hf : Q.filter (fun x => cell rho x=c)⊆cubeFiber P rho c := by
        intro x hx
        obtain ⟨hxQ,hxc⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hsub hxQ,hxc⟩
      exact (Nat.cast_le.mpr (Finset.card_le_card hf)).trans
        (original_cube_two_frostman P delta eta rho hd hd1 heta hquery hfrostman c))
  refine ⟨hglobal,?_,hkeep⟩
  apply (mul_le_mul_iff_of_pos_right (mul_pos hrho hPp)).mp
  change nu*rho*P.card/2≤(Q.card : ℝ) at hkeep
  nlinarith only [hkeep,hcount]

end OriginalThreeDimensionalHeavyCubes

namespace OriginalThreeDimensionalTubeCells
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab

/-- Replacing a shaded original point by ANY original point of its same
global cube enlarges the genuine physical tube by only a factor four. -/
theorem original_same_cell_tube_transfer (z : Pair3) (rho : ℝ) (x y : Point3)
    (hrho : 0<rho) (hcell : cell rho x=cell rho y)
    (hx : x∈physicalTube3 z.1 z.2 rho) : y∈physicalTube3 z.1 z.2 (4*rho) := by
  obtain ⟨l,hl⟩ := hx
  have he (j : Fin 3) := (original_coordinate_le_distance x (linePoint3 z.1 z.2 l) j).trans hl
  have hc (j : Fin 3) : |y j-x j|≤rho :=
    FiniteTransverseMenuGrowth.same_floor_abs_sub_le hrho (congrFun hcell.symm j)
  have hcoord (j : Fin 3) : |y j-linePoint3 z.1 z.2 l j|≤2*rho := by
    have ht := abs_sub_le (y j) (x j) (linePoint3 z.1 z.2 l j)
    linarith only [ht,hc j,he j]
  refine ⟨l,?_⟩
  unfold distance3
  apply (Real.sqrt_le_left (by positivity : 0≤4*rho)).mpr
  have hs (j : Fin 3) : (y j-linePoint3 z.1 z.2 l j)^2≤(2*rho)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoord j) 2
  nlinarith only [hs 0,hs 1,hs 2,sq_nonneg rho]

end OriginalThreeDimensionalTubeCells

namespace OriginalThreeDimensionalHeavyCubes
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeCells

/-- One global choice of ACTUAL original representatives supplies dense
physical shadings for every original rich tube simultaneously. Its source
population and support are constructed, never assumed. -/
theorem exists_original_global_heavy_cube_shading
    (P : Finset Point3) (delta eta rho nu : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (heta : 0≤eta) (hquery : delta≤rho)
    (hrho1 : rho≤1) (hnu : 0≤nu) (hP : P.Nonempty)
    (hbox : ∀ p∈P, ∀ j, |p j|≤1)
    (hfrostman : ∀ p∈P, ∀ R : ℝ, delta≤R → R≤1 →
      ((P.filter (fun q => distance3 p q≤R)).card : ℝ)≤delta^(-eta)*R^2*P.card) :
    ∃ H : Finset Point3, H⊆P ∧ Set.InjOn (cell rho) H ∧
      nu*rho^2*H.card≤768 ∧
      ∀ (z : Pair3) (i : Fin 3), z.2 i-z.1 i≠0 →
        (∀ j, |z.2 j-z.1 j|≤|z.2 i-z.1 i|) →
        nu*rho*P.card≤((physicalPairTube3 P rho z).card : ℝ) →
        ∃ Y : Finset Point3, Y⊆H ∧ Y⊆physicalPairTube3 P (4*rho) z ∧
          nu≤8*delta^(-eta)*rho*Y.card := by
  have hrho : 0<rho := hd.trans_le hquery
  have hPp : 0<(P.card : ℝ) := by exact_mod_cast hP.card_pos
  let W := nu*rho^2*P.card/768
  obtain ⟨H,hHP,hinj,himage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (↑P : Set Point3) (heavyCubes P rho W) (by
      intro c hc
      obtain ⟨x,hx,heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
      exact ⟨x,hx,heq⟩)
  have hcH : H.card=(heavyCubes P rho W).card := by
    rw [← himage,Finset.card_image_of_injOn hinj]
  have hglobal : nu*rho^2*H.card≤768 := by
    rw [hcH]
    apply (mul_le_mul_iff_of_pos_right hPp).mp
    have hb := original_heavy_cube_budget P rho W
    dsimp [W] at hb ⊢
    nlinarith only [hb]
  refine ⟨H,hHP,hinj,hglobal,?_⟩
  intro z i hne hmax hrich
  let Q := kept P (physicalPairTube3 P rho z) rho W
  let C := Q.image (cell rho)
  let Y := H.filter (fun y => cell rho y∈C)
  have hC : C⊆heavyCubes P rho W := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp hx).2
  have hYH : Y⊆H := Finset.filter_subset _ _
  have hYimage : Y.image (cell rho)=C := by
    ext c
    constructor
    · intro hc
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hc
      exact (Finset.mem_filter.mp hy).2
    · intro hc
      have hhc : c∈H.image (cell rho) := by rw [himage]; exact hC hc
      obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hhc
      exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,by simpa only [heq] using hc⟩,heq⟩
  have hYcard : Y.card=C.card := by
    rw [← hYimage,Finset.card_image_of_injOn (hinj.mono hYH)]
  have hsource := original_rich_tube_heavy_cube_shading P z delta eta rho nu i hd hd1 heta
    hquery hrho1 hnu hP hne hmax hbox hfrostman hrich
  refine ⟨Y,hYH,?_,?_⟩
  · intro y hy
    obtain ⟨hyH,hyC⟩ := Finset.mem_filter.mp hy
    obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hyC
    have hxT := (Finset.mem_filter.mp hx).1
    exact Finset.mem_filter.mpr ⟨hHP hyH,original_same_cell_tube_transfer z rho x y hrho hxy
      (Finset.mem_filter.mp hxT).2⟩
  · rw [hYcard]
    exact hsource.2.1

end OriginalThreeDimensionalHeavyCubes
