import Theorems.Thm_StickyKakeya4_original_three_dimensional_cover_ball_uniformity
import Theorems.Thm_StickyKakeya4_original_three_dimensional_heavy_cube_shading
import Theorems.Thm_StickyKakeya4_finite_voronoi_population
import Theorems.Thm_StickyKakeya4_residual_phase_localization

/- Source component: OriginalThreeDimensionalUniformBallCover -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalUniformBallCover
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSlabProjection OriginalThreeDimensionalCoverBallUniformity
open FiniteVoronoiPopulation StickyKakeya4 StickyKakeya4.ResidualPhaseLocalization

def ballCoverConstant : ℕ := max 1 (Classical.choose
  (exists_uniform_expanded_indexed_ball_card_bound.{0,0} OriginalThreeDimensionalCoverBallUniformity.E3 3 (by norm_num)))

/-- A genuine maximal finite net inside the original outer ball covers it
by a fixed number of smaller ORIGINAL-point-centered balls. Original ball
uniformity therefore compares the outer ball with any original inner ball. -/
theorem original_uniform_outer_ball_population
    (P : Finset Point3) (delta K R : ℝ) (a b : Point3)
    (hd : 0 < delta) (hK : 0 ≤ K) (hR : 0 < R)
    (hquery : delta ≤ R/3) (hR1 : R/3 ≤ 1) (hb : b∈P)
    (hsep : ∀ x∈P, ∀ y∈P, x≠y → delta ≤ distance3 x y)
    (huniform : OriginalCoverUniform P delta K) :
    ((originalOpenBall P a R).card : ℝ) ≤
      (ballCoverConstant : ℝ)*(packingConstant : ℝ)*K*(originalOpenBall P b (R/3)).card := by
  let F := originalOpenBall P a R
  let FE := F.image point
  obtain ⟨C,hCF,hCsep,hCcover⟩ := exists_separated_net FE (show 0 < R/3 by positivity)
  have hCP (c : OriginalThreeDimensionalCoverBallUniformity.E3) (hc : c∈C) : WithLp.ofLp c∈F := by
    obtain ⟨x,hx,hxc⟩ := Finset.mem_image.mp (hCF hc)
    have he : x=WithLp.ofLp c := by simpa only [point,WithLp.ofLp_toLp] using congrArg WithLp.ofLp hxc
    simpa only [← he] using hx
  have hcap : C.card ≤ ballCoverConstant := by
    have hJ := Classical.choose_spec
      (exists_uniform_expanded_indexed_ball_card_bound.{0,0} OriginalThreeDimensionalCoverBallUniformity.E3 3 (by norm_num))
    apply (hJ (R/3) (by positivity) (point a) C id ?_ ?_).trans (le_max_right _ _)
    · intro c hc
      have hcF := hCP c hc
      have hh := (Finset.mem_filter.mp hcF).2
      rw [distance3_eq_euclidean] at hh
      change dist (point a) c < R at hh
      dsimp only [id]
      rw [dist_comm]
      linarith only [hh]
    · intro c hc d hd hne
      have hs := hCsep c hc d hd hne
      exact (by linarith only [hR] : (R/3)/2 ≤ R/3).trans hs
  have hcover : F⊆C.biUnion (fun c => originalOpenBall P (WithLp.ofLp c) (R/3)) := by
    intro x hx
    obtain ⟨c,hc,hxc⟩ := hCcover (point x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    refine Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,?_⟩⟩
    rw [distance3_eq_euclidean]
    simpa only [point,WithLp.toLp_ofLp,dist_comm] using hxc
  have hball (c : OriginalThreeDimensionalCoverBallUniformity.E3) (hc : c∈C) :
      ((originalOpenBall P (WithLp.ofLp c) (R/3)).card : ℝ) ≤
        (packingConstant : ℝ)*K*(originalOpenBall P b (R/3)).card :=
    original_cover_uniform_cardinal_ball_comparison P delta K hd hK hsep huniform
      (WithLp.ofLp c) (Finset.mem_filter.mp (hCP c hc)).1 b hb (R/3) hquery hR1
  calc
    _ ≤ ∑ c∈C,((originalOpenBall P (WithLp.ofLp c) (R/3)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ _c∈C,(packingConstant : ℝ)*K*(originalOpenBall P b (R/3)).card := Finset.sum_le_sum hball
    _ = (C.card : ℝ)*((packingConstant : ℝ)*K*(originalOpenBall P b (R/3)).card) := by simp
    _ ≤ (ballCoverConstant : ℝ)*((packingConstant : ℝ)*K*(originalOpenBall P b (R/3)).card) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcap) (by positivity)
    _ = _ := by ring

end OriginalThreeDimensionalUniformBallCover

/- Source component: OriginalThreeDimensionalGridUniformity -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

noncomputable section
open scoped BigOperators ENNReal
namespace OriginalThreeDimensionalGridUniformity
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSlabProjection OriginalThreeDimensionalCoverBallUniformity
open OriginalThreeDimensionalTubeCells StickyKakeya4

def gridCover (P : Finset Point3) (delta : ℝ) : ℕ := (P.image (cell delta)).card

/-- Definition3.5's actual occupied half-open mesh cubes, evaluated in the
original metric balls. For dyadic delta these are the literal dyadic cubes. -/
def OriginalGridUniform (P : Finset Point3) (delta K : ℝ) : Prop :=
  ∀ a∈P,∀ b∈P,∀ R : ℝ,delta ≤ R → R ≤ 1 →
    (gridCover (originalOpenBall P a R) delta : ℝ) ≤
      K*gridCover (originalOpenBall P b R) delta

theorem original_grid_cell_capacity (P : Finset Point3) (delta : ℝ)
    (hd : 0 < delta) (hsep : ∀ x∈P,∀ y∈P,x≠y → delta ≤ distance3 x y)
    (k : Fin 3→ℤ) :
    (P.filter (fun x => cell delta x=k)).card ≤ packingConstant := by
  let S := P.filter (fun x => cell delta x=k)
  by_cases hS : S.Nonempty
  · obtain ⟨y,hy⟩ := hS
    have hK := Classical.choose_spec (exists_uniform_separated_ball_card_bound OriginalThreeDimensionalCoverBallUniformity.E3)
    have hnear (x : OriginalThreeDimensionalCoverBallUniformity.E3) (hx : x∈S.image point) : dist x (point y) ≤ 2*delta := by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      have hcell := (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hy).2.symm
      have hh := original_cell_distance delta p y hd hcell
      simpa only [distance3_eq_euclidean,point] using hh
    have hseparated (x : OriginalThreeDimensionalCoverBallUniformity.E3) (hx : x∈S.image point) (z : OriginalThreeDimensionalCoverBallUniformity.E3) (hz : z∈S.image point)
        (hne : x≠z) : (2*delta)/2 ≤ dist x z := by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      have hpq : p≠q := fun he => hne (congrArg point he)
      have hh := hsep p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hpq
      simpa only [mul_div_cancel_left₀ delta (by norm_num : (2:ℝ)≠0),distance3_eq_euclidean,point] using hh
    have hbound := hK (2*delta) (by positivity) (point y) (S.image point) hnear hseparated
    rw [Finset.card_image_of_injective _ (show Function.Injective point from WithLp.toLp_injective 2)] at hbound
    exact hbound.trans (le_max_right _ _)
  · change S.card ≤ packingConstant
    rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty]
    exact Nat.zero_le _

/-- Fine separation controls the occupancy of every actual fine cube, so
the original cardinality and literal occupied-grid count are comparable. -/
theorem original_cardinal_grid_cover_bounds (P : Finset Point3) (delta : ℝ)
    (hd : 0 < delta) (hsep : ∀ x∈P,∀ y∈P,x≠y → delta ≤ distance3 x y) :
    gridCover P delta ≤ P.card ∧ P.card ≤ packingConstant*gridCover P delta := by
  refine ⟨Finset.card_image_le,?_⟩
  rw [Finset.card_eq_sum_card_image (cell delta) P]
  calc
    _ ≤ ∑ _k∈P.image (cell delta),packingConstant :=
      Finset.sum_le_sum (fun k _hk => original_grid_cell_capacity P delta hd hsep k)
    _ = _ := by simp [gridCover,Nat.mul_comm]

/-- The literal original dyadic-grid ball uniformity supplies the metric
cover-uniformity input of the full-fiber construction, with a fixed,
explicitly retained dimensional coefficient. -/
theorem original_grid_uniform_implies_cover_uniform (P : Finset Point3) (delta K : ℝ)
    (hd : 0 < delta) (hK : 0 ≤ K)
    (hsep : ∀ x∈P,∀ y∈P,x≠y → delta ≤ distance3 x y)
    (huniform : OriginalGridUniform P delta K) :
    OriginalCoverUniform P delta ((packingConstant : ℝ)^2*K) := by
  intro a ha b hb R hR hR1
  let A := originalOpenBall P a R
  let B := originalOpenBall P b R
  have hsepA (x : Point3) (hx : x∈A) (y : Point3) (hy : y∈A) (hne : x≠y) :=
    hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne
  have hsepB (x : Point3) (hx : x∈B) (y : Point3) (hy : y∈B) (hne : x≠y) :=
    hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hne
  have hNA := (original_cardinal_mesh_cover_bounds A delta hd hsepA).1
  have hNB := (original_cardinal_mesh_cover_bounds B delta hd hsepB).2
  have hGA : (A.card : ℝ≥0∞) ≤ (packingConstant : ℝ≥0∞)*gridCover A delta := by
    exact_mod_cast (original_cardinal_grid_cover_bounds A delta hd hsepA).2
  have hGB : (gridCover B delta : ℝ≥0∞) ≤ B.card := by
    exact_mod_cast (original_cardinal_grid_cover_bounds B delta hd hsepB).1
  have hU : (gridCover A delta : ℝ≥0∞) ≤ ENNReal.ofReal K*gridCover B delta := by
    have hh := ENNReal.ofReal_le_ofReal (huniform a ha b hb R hR hR1)
    simpa only [ENNReal.ofReal_mul hK,ENNReal.ofReal_natCast] using hh
  calc
    _ ≤ (A.card : ℝ≥0∞) := hNA
    _ ≤ (packingConstant : ℝ≥0∞)*gridCover A delta := hGA
    _ ≤ (packingConstant : ℝ≥0∞)*(ENNReal.ofReal K*gridCover B delta) :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    _ ≤ (packingConstant : ℝ≥0∞)*(ENNReal.ofReal K*B.card) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGB (by positivity)) (by positivity)
    _ ≤ (packingConstant : ℝ≥0∞)*(ENNReal.ofReal K*((packingConstant : ℝ≥0∞)*meshCover B delta)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNB (by positivity)) (by positivity)
    _ = ENNReal.ofReal ((packingConstant : ℝ)^2*K)*meshCover B delta := by
      rw [ENNReal.ofReal_mul (sq_nonneg _),ENNReal.ofReal_pow (Nat.cast_nonneg packingConstant) 2,
        ENNReal.ofReal_natCast]
      ring

end OriginalThreeDimensionalGridUniformity

/- Source component: OriginalThreeDimensionalVoronoiFibers -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalVoronoiFibers
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSlabProjection OriginalThreeDimensionalCoverBallUniformity
open OriginalThreeDimensionalUniformBallCover

def originalOwner (C : Finset Point3) (hC : C.Nonempty) (x : Point3) : Point3 :=
  WithLp.ofLp (FiniteVoronoiPopulation.owner (C.image point) (hC.image point) (point x))

def originalCarrier (P C : Finset Point3) (hC : C.Nonempty) (R : ℝ) : Finset Point3 :=
  P.filter (fun x => distance3 x (originalOwner C hC x) < R)

def originalFiber (P C : Finset Point3) (hC : C.Nonempty) (R : ℝ) (c : Point3) : Finset Point3 :=
  (originalCarrier P C hC R).filter (fun x => originalOwner C hC x=c)

theorem original_owner_mem (C : Finset Point3) (hC : C.Nonempty) (x : Point3) :
    originalOwner C hC x∈C := by
  obtain ⟨c,hc,he⟩ := Finset.mem_image.mp
    (FiniteVoronoiPopulation.owner_mem (C.image point) (hC.image point) (point x))
  have he' := congrArg WithLp.ofLp he
  simpa only [point,WithLp.ofLp_toLp,originalOwner] using he' ▸ hc

theorem original_owner_min (C : Finset Point3) (hC : C.Nonempty) (x c : Point3) (hc : c∈C) :
    distance3 x (originalOwner C hC x) ≤ distance3 x c := by
  have hh := FiniteVoronoiPopulation.owner_min (C.image point) (hC.image point)
    (point x) (point c) (Finset.mem_image_of_mem point hc)
  simpa only [distance3_eq_euclidean,originalOwner,point,WithLp.toLp_ofLp] using hh

/-- The finite net centers are actual original source points. Its nearest
owner is the genuine Euclidean owner, regardless of Point3's ambient Pi metric. -/
theorem exists_original_euclidean_owner_net (S : Finset Point3) (hS : S.Nonempty)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : Finset Point3, ∃ hC : C.Nonempty,
      C⊆S ∧ (∀ c∈C, ∀ d∈C, c≠d → R ≤ distance3 c d) ∧
      ∀ x∈S, distance3 x (originalOwner C hC x) < R := by
  obtain ⟨D,hDS,hsep,hcover⟩ := FiniteVoronoiPopulation.exists_separated_net (S.image point) hR
  have hD : D.Nonempty := by
    obtain ⟨x,hx⟩ := hS
    obtain ⟨d,hd,_hxd⟩ := hcover (point x) (Finset.mem_image_of_mem point hx)
    exact ⟨d,hd⟩
  let C := D.image WithLp.ofLp
  have hC : C.Nonempty := hD.image WithLp.ofLp
  have hCS : C⊆S := by
    intro c hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp (hDS hd)
    have he' := congrArg WithLp.ofLp he
    simpa only [point,WithLp.ofLp_toLp] using he' ▸ hx
  refine ⟨C,hC,hCS,?_,?_⟩
  · intro c hc d hd hne
    obtain ⟨ce,hce,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨de,hde,rfl⟩ := Finset.mem_image.mp hd
    have hned : ce≠de := fun he => hne (congrArg WithLp.ofLp he)
    simpa only [distance3_eq_euclidean,WithLp.toLp_ofLp] using hsep ce hce de hde hned
  · intro x hx
    obtain ⟨d,hd,hxd⟩ := hcover (point x) (Finset.mem_image_of_mem point hx)
    have hnear : distance3 x (WithLp.ofLp d) < R := by
      simpa only [distance3_eq_euclidean,WithLp.toLp_ofLp,point] using hxd
    exact (original_owner_min C hC x (WithLp.ofLp d) (Finset.mem_image_of_mem WithLp.ofLp hd)).trans_lt hnear

/-- Each fiber contains a FULL original inner ball and is contained in a
full original outer ball. The inner population is not restricted to the core. -/
theorem original_full_fiber_ball_sandwich (P C : Finset Point3) (hC : C.Nonempty)
    (R : ℝ) (hR : 0 < R) (hsep : ∀ c∈C, ∀ d∈C, c≠d → R ≤ distance3 c d)
    (c : Point3) (hc : c∈C) :
    originalOpenBall P c (R/3)⊆originalFiber P C hC R c ∧
      originalFiber P C hC R c⊆originalOpenBall P c R := by
  constructor
  · intro x hx
    obtain ⟨hxP,hxc⟩ := Finset.mem_filter.mp hx
    have hsym : distance3 x c=distance3 c x := by simp only [distance3_eq_euclidean,dist_comm]
    have hmin := original_owner_min C hC x c hc
    have he : originalOwner C hC x=c := by
      by_contra hne
      have hs := hsep c hc (originalOwner C hC x) (original_owner_mem C hC x) (fun he => hne he.symm)
      have ht : distance3 c (originalOwner C hC x) ≤ distance3 c x+distance3 x (originalOwner C hC x) := by
        simp only [distance3_eq_euclidean]
        exact dist_triangle _ _ _
      rw [hsym] at hmin
      linarith only [hs,ht,hmin,hxc,hR]
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxP,?_⟩,he⟩
    rw [he,hsym]
    linarith only [hxc,hR]
  · intro x hx
    obtain ⟨hxU,he⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxP,hnear⟩ := Finset.mem_filter.mp hxU
    rw [he] at hnear
    exact Finset.mem_filter.mpr ⟨hxP,by simpa only [distance3_eq_euclidean,dist_comm] using hnear⟩

/-- The truncated full-original fibers retain every net-covered endpoint,
are disjoint, and conserve their actual original source population exactly. -/
theorem original_full_fiber_partition (P S C : Finset Point3) (hC : C.Nonempty) (R : ℝ)
    (hSP : S⊆P) (hnear : ∀ x∈S,distance3 x (originalOwner C hC x) < R) :
    S⊆originalCarrier P C hC R ∧ originalCarrier P C hC R⊆P ∧
      (∑ c∈C,(originalFiber P C hC R c).card)=(originalCarrier P C hC R).card ∧
      ∀ c∈C,∀ d∈C,c≠d → Disjoint (originalFiber P C hC R c) (originalFiber P C hC R d) := by
  refine ⟨fun x hx => Finset.mem_filter.mpr ⟨hSP hx,hnear x hx⟩,Finset.filter_subset _ _,?_,?_⟩
  · exact (Finset.card_eq_sum_card_fiberwise (s:=originalCarrier P C hC R) (t:=C)
      (f:=originalOwner C hC) (fun x _hx => original_owner_mem C hC x)).symm
  · intro c _hc d _hd hne
    apply Finset.disjoint_left.mpr
    intro x hxc hxd
    exact hne ((Finset.mem_filter.mp hxc).2.symm.trans (Finset.mem_filter.mp hxd).2)

/-- Actual original ball uniformity balances the full fibers of an actual
separated owner family. No fiber-comparability premise is supplied. -/
theorem original_uniform_full_fiber_population (P C : Finset Point3) (hC : C.Nonempty)
    (delta K R : ℝ) (hd : 0 < delta) (hK : 0 ≤ K) (hR : 0 < R)
    (hquery : delta ≤ R/3) (hR1 : R/3 ≤ 1) (hCP : C⊆P)
    (hseparated : ∀ x∈P,∀ y∈P,x≠y → delta ≤ distance3 x y)
    (huniform : OriginalCoverUniform P delta K)
    (hsep : ∀ c∈C,∀ d∈C,c≠d → R ≤ distance3 c d) :
    ∀ c∈C,∀ d∈C,
      ((originalFiber P C hC R c).card : ℝ) ≤
        (ballCoverConstant : ℝ)*(packingConstant : ℝ)*K*(originalFiber P C hC R d).card := by
  intro c hc d hdC
  have hcS := (original_full_fiber_ball_sandwich P C hC R hR hsep c hc).2
  have hdS := (original_full_fiber_ball_sandwich P C hC R hR hsep d hdC).1
  have hball := original_uniform_outer_ball_population P delta K R c d hd hK hR hquery hR1
    (hCP hdC) hseparated huniform
  exact (Nat.cast_le.mpr (Finset.card_le_card hcS)).trans (hball.trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hdS)) (by positivity)))


/-- Choose the actual minimum full-fiber population. Every original center
then has a positive common lower mass and the derived uniform upper mass. -/
theorem exists_original_common_fiber_population (P C : Finset Point3) (hC : C.Nonempty)
    (delta K R : ℝ) (hd : 0 < delta) (hK : 0 ≤ K) (hR : 0 < R)
    (hquery : delta ≤ R/3) (hR1 : R/3 ≤ 1) (hCP : C⊆P)
    (hseparated : ∀ x∈P,∀ y∈P,x≠y → delta ≤ distance3 x y)
    (huniform : OriginalCoverUniform P delta K)
    (hsep : ∀ c∈C,∀ d∈C,c≠d → R ≤ distance3 c d) :
    ∃ M : ℕ, 0 < M ∧ ∀ c∈C,
      M ≤ (originalFiber P C hC R c).card ∧
      ((originalFiber P C hC R c).card : ℝ) ≤
        (ballCoverConstant : ℝ)*(packingConstant : ℝ)*K*M := by
  obtain ⟨c0,hc0,hmin⟩ := Finset.exists_min_image C
    (fun c => (originalFiber P C hC R c).card) hC
  have hcF : c0∈originalFiber P C hC R c0 := by
    apply (original_full_fiber_ball_sandwich P C hC R hR hsep c0 hc0).1
    apply Finset.mem_filter.mpr
    refine ⟨hCP hc0,?_⟩
    simpa only [distance3_eq_euclidean,dist_self] using (show 0 < R/3 by positivity)
  refine ⟨(originalFiber P C hC R c0).card,Finset.card_pos.mpr ⟨c0,hcF⟩,?_⟩
  intro c hc
  exact ⟨hmin c hc,original_uniform_full_fiber_population P C hC delta K R hd hK hR hquery hR1
    hCP hseparated huniform hsep c hc c0 hc0⟩

end OriginalThreeDimensionalVoronoiFibers

/- Source component: OriginalThreeDimensionalGridBalancedFibers -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalGridBalancedFibers
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalCoverBallUniformity OriginalThreeDimensionalGridUniformity
open OriginalThreeDimensionalUniformBallCover OriginalThreeDimensionalVoronoiFibers

def uniformFiberConstant (K : ℝ) : ℝ :=
  (ballCoverConstant : ℝ)*(packingConstant : ℝ)^3*K

/-- The printed original occupied-grid uniformity constructs an actual
Euclidean net in the retained endpoint source, balanced FULL original fibers,
and exact population conservation. No balance or representative population
is supplied as an input. -/
theorem exists_original_grid_balanced_fibers (P S : Finset Point3) (delta K R : ℝ)
    (hS : S.Nonempty) (hSP : S⊆P) (hd : 0 < delta) (hK : 0 ≤ K) (hR : 0 < R)
    (hquery : delta ≤ R/3) (hR1 : R/3 ≤ 1)
    (hseparated : ∀ x∈P,∀ y∈P,x≠y → delta ≤ distance3 x y)
    (huniform : OriginalGridUniform P delta K) :
    ∃ C : Finset Point3,∃ hC : C.Nonempty,∃ M : ℕ,
      0 < M ∧ C⊆S ∧ (∀ c∈C,∀ d∈C,c≠d → R ≤ distance3 c d) ∧
      (∀ x∈S,distance3 x (originalOwner C hC x) < R) ∧
      S⊆originalCarrier P C hC R ∧ originalCarrier P C hC R⊆P ∧
      (∑ c∈C,(originalFiber P C hC R c).card)=(originalCarrier P C hC R).card ∧
      (∀ c∈C,∀ d∈C,c≠d → Disjoint (originalFiber P C hC R c) (originalFiber P C hC R d)) ∧
      1 ≤ uniformFiberConstant K ∧
      ∀ c∈C,
        M ≤ (originalFiber P C hC R c).card ∧
        ((originalFiber P C hC R c).card : ℝ) ≤ uniformFiberConstant K*M ∧
        originalOpenBall P c (R/3)⊆originalFiber P C hC R c ∧
        originalFiber P C hC R c⊆originalOpenBall P c R := by
  obtain ⟨C,hC,hCS,hsep,hnear⟩ := exists_original_euclidean_owner_net S hS R hR
  have hcover := original_grid_uniform_implies_cover_uniform P delta K hd hK hseparated huniform
  obtain ⟨M,hM,hpop⟩ := exists_original_common_fiber_population P C hC delta
    ((packingConstant : ℝ)^2*K) R hd (by positivity) hR hquery hR1 (hCS.trans hSP)
    hseparated hcover hsep
  have hupper (c : Point3) (hc : c∈C) :
      ((originalFiber P C hC R c).card : ℝ) ≤ uniformFiberConstant K*M := by
    have he : (ballCoverConstant : ℝ)*(packingConstant : ℝ)*((packingConstant : ℝ)^2*K)*M=
        uniformFiberConstant K*M := by unfold uniformFiberConstant; ring
    exact (hpop c hc).2.trans_eq he
  have hconstant : 1 ≤ uniformFiberConstant K := by
    obtain ⟨c,hc⟩ := hC
    have hm : (0:ℝ) < M := by exact_mod_cast hM
    apply (mul_le_mul_iff_of_pos_right hm).mp
    simpa only [one_mul] using (Nat.cast_le.mpr (hpop c hc).1).trans (hupper c hc)
  obtain ⟨hSU,hUP,hsum,hdisj⟩ := original_full_fiber_partition P S C hC R hSP hnear
  refine ⟨C,hC,M,hM,hCS,hsep,hnear,hSU,hUP,hsum,hdisj,hconstant,?_⟩
  intro c hc
  exact ⟨(hpop c hc).1,hupper c hc,original_full_fiber_ball_sandwich P C hC R hR hsep c hc⟩

end OriginalThreeDimensionalGridBalancedFibers
