import Theorems.Thm_StickyKakeya4_original_three_dimensional_band_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

noncomputable section
namespace OriginalThreeDimensionalDirectionGrid
open Classical OriginalThreeDimensionalBandGeometry

abbrev DirectionLabel := Equiv.Perm (Fin 3) × (ℤ × ℤ)
def freeGrid (rho : ℝ) : Finset ℤ := Finset.Icc 0 ⌊1/rho⌋
def normalGrid (rho : ℝ) : Finset DirectionLabel :=
  Finset.univ.product ((Finset.Icc (-⌈3/rho⌉) ⌈3/rho⌉).product (freeGrid rho))
def value (rho : ℝ) (d : DirectionLabel) (p : Point3) : ℝ :=
  projection d.1 (rho*d.2.1) (rho*d.2.2) p
def pairBand (rho : ℝ) (p q : Point3) : Finset DirectionLabel :=
  (normalGrid rho).filter (fun d => |value rho d q-value rho d p|≤2*rho)

lemma free_grid_value (rho : ℝ) (hrho : 0<rho) (k : ℤ) (hk : k∈freeGrid rho) :
    0≤rho*(k:ℝ) ∧ rho*(k:ℝ)≤1 := by
  obtain ⟨hk0,hk1⟩ := Finset.mem_Icc.mp hk
  have hk0r : (0:ℝ)≤k := by exact_mod_cast hk0
  have hk1r : (k:ℝ)≤(⌊1/rho⌋:ℤ) := by exact_mod_cast hk1
  have hb := hk1r.trans (Int.floor_le _)
  refine ⟨mul_nonneg hrho.le hk0r,?_⟩
  have hh := (le_div_iff₀ hrho).mp hb
  nlinarith only [hh]

lemma free_grid_mass (rho : ℝ) (hrho : 0<rho) :
    1≤rho*(freeGrid rho).card := by
  have hM : (0:ℤ)≤⌊1/rho⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc := Int.card_Icc_of_le (a:=0) (b:=⌊1/rho⌋) (by omega)
  have hcR : ((freeGrid rho).card : ℝ)=(⌊1/rho⌋:ℤ)+1 := by
    dsimp [freeGrid]
    simpa only [sub_zero] using (show ((Finset.Icc 0 ⌊1/rho⌋).card : ℝ)=(⌊1/rho⌋:ℤ)+1-0 by exact_mod_cast hc)
  have hh := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one (1/rho))
  rw [hcR]
  nlinarith only [hh]

/-- One common rational direction family has quadratic grid size. Labels
retain their chart, so no unproved spherical-net estimate is used. -/
theorem normal_grid_card (rho : ℝ) (hrho : 0<rho) (hrho1 : rho≤1) :
    (normalGrid rho).card*rho^2≤108 := by
  let U := Finset.Icc (-⌈3/rho⌉) ⌈3/rho⌉
  let V := freeGrid rho
  have hN : (0:ℤ)≤⌈3/rho⌉ := by
    have hh : (0:ℝ)≤(⌈3/rho⌉:ℤ) := (by positivity : (0:ℝ)≤3/rho).trans (Int.le_ceil _)
    exact_mod_cast hh
  have hM : (0:ℤ)≤⌊1/rho⌋ := Int.floor_nonneg.mpr (by positivity)
  have huI := Int.card_Icc_of_le (a:= -⌈3/rho⌉) (b:=⌈3/rho⌉) (by omega)
  have huR : (U.card : ℝ)=2*(⌈3/rho⌉:ℤ)+1 := by
    have hh : (U.card : ℝ)=(⌈3/rho⌉:ℤ)+1-(-(⌈3/rho⌉:ℤ)) := by exact_mod_cast huI
    linarith only [hh]
  have hvI := Int.card_Icc_of_le (a:=0) (b:=⌊1/rho⌋) (by omega)
  have hvR : (V.card : ℝ)=(⌊1/rho⌋:ℤ)+1 := by
    dsimp [V,freeGrid]
    simpa only [sub_zero] using (show ((Finset.Icc 0 ⌊1/rho⌋).card : ℝ)=(⌊1/rho⌋:ℤ)+1-0 by exact_mod_cast hvI)
  have hceil := Int.ceil_lt_add_one (3/rho)
  have hceil' := mul_lt_mul_of_pos_right hceil hrho
  have hdiv : (3/rho+1)*rho=3+rho := by field_simp
  rw [hdiv] at hceil'
  have hfloor := (le_div_iff₀ hrho).mp (Int.floor_le (1/rho))
  have hu : (U.card : ℝ)*rho≤9 := by rw [huR]; nlinarith only [hceil',hrho1]
  have hv : (V.card : ℝ)*rho≤2 := by rw [hvR]; nlinarith only [hfloor,hrho1]
  have hprod := mul_le_mul hu hv (by positivity : (0:ℝ)≤V.card*rho) (by norm_num : (0:ℝ)≤9)
  have hcard : (normalGrid rho).card=6*U.card*V.card := by
    simp only [normalGrid,Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_perm,Fintype.card_fin]
    norm_num [U,V]
    ring
  rw [hcard]
  push_cast
  nlinarith only [hprod]

/-- Every distinct original bounded pair has at least rho^{-1} labels in
its true near-orthogonal band. This is the common-direction multiplicity
needed by the three-dimensional heavy-slice double count. -/
theorem original_pair_band_mass (rho : ℝ) (p q : Point3)
    (hrho : 0<rho) (hrho1 : rho≤1) (hne : p≠q)
    (hp : ∀ i, |p i|≤1) (hq : ∀ i, |q i|≤1) :
    1≤rho*(pairBand rho p q).card := by
  obtain ⟨i,_hi,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun j => |q j-p j|) (Finset.univ_nonempty)
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 i
  let A := q (e 0)-p (e 0)
  let B := q (e 1)-p (e 1)
  let C := q (e 2)-p (e 2)
  have hei : e 0=i := by simp [e]
  have hA : A≠0 := by
    intro hz
    apply hne
    funext j
    have hb := hmax j (Finset.mem_univ j)
    have hi0 : q i-p i=0 := by simpa only [A,hei] using hz
    rw [hi0,abs_zero] at hb
    exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))).symm
  have hB : |B|≤|A| := by simpa only [A,B,hei] using hmax (e 1) (Finset.mem_univ _)
  have hC : |C|≤|A| := by simpa only [A,C,hei] using hmax (e 2) (Finset.mem_univ _)
  have hA2 : |A|≤2 := by
    have hh := abs_sub (q (e 0)) (p (e 0))
    dsimp [A]
    linarith only [hh,hq (e 0),hp (e 0)]
  let f : ℤ→DirectionLabel := fun k => (e,(roundedRoot rho A B C (rho*k),k))
  have hsub : (freeGrid rho).image f⊆pairBand rho p q := by
    intro d hd
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hd
    have hv := free_grid_value rho hrho k hk
    have hvabs : |rho*(k:ℝ)|≤1 := by rw [abs_of_nonneg hv.1]; exact hv.2
    have hin := rounded_normal_in_grid rho A B C (rho*k) hrho hrho1 hA hB hC hvabs hA2
    have hband := (rounded_normal_band rho A B C (rho*k) hrho hrho1 hA hB hC hvabs hA2).2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr ⟨hin,hk⟩⟩
    · change |projection e (rho*roundedRoot rho A B C (rho*k)) (rho*k) q-
        projection e (rho*roundedRoot rho A B C (rho*k)) (rho*k) p|≤2*rho
      have he : projection e (rho*roundedRoot rho A B C (rho*k)) (rho*k) q-
          projection e (rho*roundedRoot rho A B C (rho*k)) (rho*k) p=
          rho*roundedRoot rho A B C (rho*k)*A+(rho*k)*B+C := by
        dsimp [projection,A,B,C]
        ring
      rw [he]
      exact hband
  have hf : Function.Injective f := by intro j k he; exact congrArg (fun d : DirectionLabel => d.2.2) he
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf] at hcard
  exact (free_grid_mass rho hrho).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) hrho.le)

end OriginalThreeDimensionalDirectionGrid
