import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_slab
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace OriginalThreeDimensionalTubeCover
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab NativeTangentGridCoarsening

/-- Quantizing an actual point's largest-displacement coordinate controls
the whole original Euclidean tube fiber, independently of pair length. -/
theorem original_tube_coordinate_fiber_diameter (p q x y : Point3) (rho : ℝ)
    (i : Fin 3) (hrho : 0<rho)
    (hmax : ∀ j, |q j-p j|≤|q i-p i|)
    (hx : x∈physicalTube3 p q rho) (hy : y∈physicalTube3 p q rho)
    (hbin : ⌊x i/rho⌋=⌊y i/rho⌋) : distance3 x y≤10*rho := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  have hxerr (j : Fin 3) : |x j-linePoint3 p q a j|≤rho :=
    (original_coordinate_le_distance x (linePoint3 p q a) j).trans ha
  have hyerr (j : Fin 3) : |y j-linePoint3 p q b j|≤rho :=
    (original_coordinate_le_distance y (linePoint3 p q b) j).trans hb
  have hxi := coarse_floor_interval hrho (rfl : ⌊x i/rho⌋=⌊x i/rho⌋)
  have hyi := coarse_floor_interval hrho hbin.symm
  have hxy : |x i-y i|≤rho := abs_le.mpr ⟨by linarith only [hxi.1,hxi.2,hyi.1,hyi.2],
    by linarith only [hxi.1,hxi.2,hyi.1,hyi.2]⟩
  have hlinei : |a-b| * |q i-p i|≤3*rho := by
    have h1 := abs_sub_le (linePoint3 p q a i) (x i) (y i)
    have h2 := abs_sub_le (linePoint3 p q a i) (y i) (linePoint3 p q b i)
    have he : linePoint3 p q a i-linePoint3 p q b i=(a-b)*(q i-p i) := by dsimp [linePoint3]; ring
    rw [he,abs_mul] at h2
    have hxe : |linePoint3 p q a i-x i|≤rho := by simpa only [abs_sub_comm] using hxerr i
    linarith only [h1,h2,hxe,hyerr i,hxy]
  have hcoord (j : Fin 3) : |x j-y j|≤5*rho := by
    have hlinej := (mul_le_mul_of_nonneg_left (hmax j) (abs_nonneg (a-b))).trans hlinei
    have he : linePoint3 p q a j-linePoint3 p q b j=(a-b)*(q j-p j) := by dsimp [linePoint3]; ring
    have h1 := abs_sub_le (x j) (linePoint3 p q a j) (linePoint3 p q b j)
    have h2 := abs_sub_le (x j) (linePoint3 p q b j) (y j)
    rw [he,abs_mul] at h1
    have hye : |linePoint3 p q b j-y j|≤rho := by simpa only [abs_sub_comm] using hyerr j
    linarith only [h1,h2,hxerr j,hye,hlinej]
  have hs (j : Fin 3) : (x j-y j)^2≤(5*rho)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x j-y j)) (hcoord j) 2
  unfold distance3
  apply (Real.sqrt_le_left (by positivity : 0≤10*rho)).mpr
  nlinarith only [hs 0,hs 1,hs 2,sq_nonneg rho]

/-- A bounded original tube is covered by balls of radius 10rho centered
at actual original tube points. There are at most 4/rho centers, with no
factor involving the original pair separation. -/
theorem exists_original_tube_ball_centers (P : Finset Point3) (z : Pair3) (rho : ℝ)
    (hrho : 0<rho) (hrho1 : rho≤1) (hbox : ∀ p∈P, ∀ i, |p i|≤1) :
    ∃ C : Finset Point3, C⊆physicalPairTube3 P rho z ∧ (C.card : ℝ)*rho≤4 ∧
      ∀ x∈physicalPairTube3 P rho z, ∃ y∈C, distance3 y x≤10*rho := by
  let T := physicalPairTube3 P rho z
  obtain ⟨i,_hi,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun j => |z.2 j-z.1 j|) Finset.univ_nonempty
  let f : Point3→ℤ := fun p => ⌊p i/rho⌋
  obtain ⟨C,hCT,hinj,himage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (↑T : Set Point3) (T.image f) (by
      intro k hk
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
      exact ⟨p,hp,rfl⟩)
  have hcount := scalar_interval_grid_card T (fun p => p i) (c:= -1) (L:=2) hrho (by norm_num)
    (fun p hp => by
      have hh := hbox p (Finset.mem_filter.mp hp).1 i
      exact ⟨(abs_le.mp hh).1,by linarith only [(abs_le.mp hh).2]⟩)
  have hcard : (C.card : ℝ)≤2/rho+2 := by
    rw [← Finset.card_image_of_injOn hinj,himage]
    exact hcount
  have hCrho := mul_le_mul_of_nonneg_right hcard hrho.le
  have hdiv : (2/rho+2)*rho=2+2*rho := by field_simp
  rw [hdiv] at hCrho
  refine ⟨C,hCT,by linarith only [hCrho,hrho1],?_⟩
  intro x hx
  have hxcell : f x∈C.image f := by rw [himage]; exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  obtain ⟨y,hy,hbin⟩ := Finset.mem_image.mp hxcell
  refine ⟨y,hy,?_⟩
  exact original_tube_coordinate_fiber_diameter z.1 z.2 y x rho i hrho
    (fun j => hmax j (Finset.mem_univ j)) (Finset.mem_filter.mp (hCT hy)).2
    (Finset.mem_filter.mp hx).2 hbin

end OriginalThreeDimensionalTubeCover
