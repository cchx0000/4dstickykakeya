import Theorems.Thm_StickyKakeya4_original_three_dimensional_unit_slabs
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace OriginalThreeDimensionalTubeSlab
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalDirectionGrid
open OriginalThreeDimensionalHeavySlabs OriginalThreeDimensionalHeavySliceGraph
open OriginalThreeDimensionalUnitSlabs

/-- Literal Euclidean distance on the original three coordinates. -/
def distance3 (p q : Point3) : ℝ :=
  Real.sqrt ((p 0-q 0)^2+(p 1-q 1)^2+(p 2-q 2)^2)

def linePoint3 (p q : Point3) (l : ℝ) : Point3 := fun i => p i+l*(q i-p i)

/-- Closed physical Euclidean tube around the full affine pair line.
Membership supplies a genuine point of that line within Euclidean rho. -/
def physicalTube3 (p q : Point3) (rho : ℝ) : Set Point3 :=
  {z | ∃ l : ℝ, distance3 z (linePoint3 p q l)≤rho}

def physicalPairTube3 (P : Finset Point3) (rho : ℝ) (z : Pair3) : Finset Point3 :=
  P.filter (fun p => p∈physicalTube3 z.1 z.2 rho)

def chartValue (e : Equiv.Perm (Fin 3)) (nx ny nz : ℝ) (p : Point3) : ℝ :=
  nx*p (e 0)+ny*p (e 1)+nz*p (e 2)

/-- Each true coordinate error is controlled by Euclidean distance. -/
theorem original_coordinate_le_distance (p q : Point3) (i : Fin 3) :
    |p i-q i|≤distance3 p q := by
  unfold distance3
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  fin_cases i <;> simp only [Fin.reduceFinMk] <;>
    linarith only [sq_nonneg (p 0-q 0),sq_nonneg (p 1-q 1),sq_nonneg (p 2-q 2)]


/-- An actual largest original displacement coordinate controls a positive
Euclidean separation; the factor two is a harmless bound for sqrt(3). -/
theorem exists_original_large_coordinate (p q : Point3) (r : ℝ)
    (_hr : 0<r) (hsep : r≤distance3 p q) :
    ∃ i : Fin 3, (∀ j, |q j-p j|≤|q i-p i|) ∧ r≤2*|q i-p i| := by
  obtain ⟨i,_hi,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun j => |q j-p j|) Finset.univ_nonempty
  have hm (j : Fin 3) : |q j-p j|≤|q i-p i| := hmax j (Finset.mem_univ _)
  have h0 := pow_le_pow_left₀ (abs_nonneg (q 0-p 0)) (hm 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg (q 1-p 1)) (hm 1) 2
  have h2 := pow_le_pow_left₀ (abs_nonneg (q 2-p 2)) (hm 2) 2
  simp only [sq_abs] at h0 h1 h2
  have hsum := add_le_add (add_le_add h0 h1) h2
  have hdmax : distance3 p q≤2*|q i-p i| := by
    unfold distance3
    apply (Real.sqrt_le_left (by positivity : 0≤2*|q i-p i|)).mpr
    rw [sub_sq_comm (p 0) (q 0),sub_sq_comm (p 1) (q 1),sub_sq_comm (p 2) (q 2)]
    nlinarith only [hsum,sq_nonneg (q i-p i),sq_abs (q i-p i)]
  exact ⟨i,hm,hsep.trans hdmax⟩


/-- The line parameter is derived from that actual largest coordinate.
The original endpoint is in [-1,1]^3 and the query point in [-2,2]^3. -/
theorem original_affine_parameter_bound (p q z : Point3) (rho r l : ℝ)
    (hr : 0<r) (hrho1 : rho≤1) (hsep : r≤distance3 p q)
    (hp : ∀ i, |p i|≤1) (hz : ∀ i, |z i|≤2)
    (htube : distance3 z (linePoint3 p q l)≤rho) : |l|≤8/r := by
  obtain ⟨i,_hmax,hlarge⟩ := exists_original_large_coordinate p q r hr hsep
  have herr := (original_coordinate_le_distance z (linePoint3 p q l) i).trans htube
  have htriangle := abs_add_le (z i-p i) (linePoint3 p q l i-z i)
  have hfirst := abs_sub (z i) (p i)
  have heq : (z i-p i)+(linePoint3 p q l i-z i)=l*(q i-p i) := by
    dsimp [linePoint3]
    ring
  rw [heq,abs_mul] at htriangle
  have herr' : |linePoint3 p q l i-z i|≤rho := by simpa only [abs_sub_comm] using herr
  have hproduct : |l| * |q i-p i|≤4 := by
    linarith only [htriangle,hfirst,hz i,hp i,herr',hrho1]
  have hh := mul_le_mul_of_nonneg_left hlarge (abs_nonneg l)
  apply (le_div_iff₀ hr).mpr
  nlinarith only [hh,hproduct]


/-- The bounded original portion of a true Euclidean pair tube lies in
an enlargement of the SAME original unit-normal slab. No containment
hypothesis is supplied. -/
theorem original_physical_tube_in_unit_slab
    (p q z : Point3) (e : Equiv.Perm (Fin 3)) (nx ny nz c rho r : ℝ)
    (hrho : 0<rho) (hrho1 : rho≤1) (hr : 0<r) (hr1 : r≤1)
    (hunit : nx^2+ny^2+nz^2=1)
    (hp : ∀ i, |p i|≤1) (hz : ∀ i, |z i|≤2)
    (hsep : r≤distance3 p q)
    (hpslab : |chartValue e nx ny nz p-c|≤3*rho)
    (hqslab : |chartValue e nx ny nz q-c|≤3*rho)
    (htube : z∈physicalTube3 p q rho) :
    |chartValue e nx ny nz z-c|≤54*rho/r := by
  obtain ⟨l,hl⟩ := htube
  have hlbound := original_affine_parameter_bound p q z rho r l hr hrho1 hsep hp hz hl
  have hn (v : ℝ) (hv : v^2≤1) : |v|≤1 := by
    nlinarith only [hv,sq_abs v,abs_nonneg v]
  have hnx : |nx|≤1 := hn nx (by nlinarith only [hunit,sq_nonneg ny,sq_nonneg nz])
  have hny : |ny|≤1 := hn ny (by nlinarith only [hunit,sq_nonneg nx,sq_nonneg nz])
  have hnz : |nz|≤1 := hn nz (by nlinarith only [hunit,sq_nonneg nx,sq_nonneg ny])
  have herr (i : Fin 3) : |z i-linePoint3 p q l i|≤rho :=
    (original_coordinate_le_distance z (linePoint3 p q l) i).trans hl
  have hlinearError : |chartValue e nx ny nz z-chartValue e nx ny nz (linePoint3 p q l)|≤3*rho := by
    have hx := mul_le_mul hnx (herr (e 0)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hy := mul_le_mul hny (herr (e 1)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hz' := mul_le_mul hnz (herr (e 2)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hid : chartValue e nx ny nz z-chartValue e nx ny nz (linePoint3 p q l)=
        nx*(z (e 0)-linePoint3 p q l (e 0))+
          ny*(z (e 1)-linePoint3 p q l (e 1))+
          nz*(z (e 2)-linePoint3 p q l (e 2)) := by dsimp [chartValue]; ring
    rw [hid]
    have htri1 := abs_add_le
      (nx*(z (e 0)-linePoint3 p q l (e 0))) (ny*(z (e 1)-linePoint3 p q l (e 1)))
    have htri2 := abs_add_le
      (nx*(z (e 0)-linePoint3 p q l (e 0))+ny*(z (e 1)-linePoint3 p q l (e 1)))
      (nz*(z (e 2)-linePoint3 p q l (e 2)))
    simp only [abs_mul] at htri1 htri2
    linarith only [hx,hy,hz',htri1,htri2]
  have hend : |chartValue e nx ny nz q-chartValue e nx ny nz p|≤6*rho := by
    have hh := abs_sub (chartValue e nx ny nz q-c) (chartValue e nx ny nz p-c)
    have heq : chartValue e nx ny nz q-c-(chartValue e nx ny nz p-c)=
        chartValue e nx ny nz q-chartValue e nx ny nz p := by ring
    rw [heq] at hh
    linarith only [hh,hpslab,hqslab]
  have hline : |chartValue e nx ny nz (linePoint3 p q l)-c|≤3*rho+(8/r)*(6*rho) := by
    have heq : chartValue e nx ny nz (linePoint3 p q l)-c=
        (chartValue e nx ny nz p-c)+l*(chartValue e nx ny nz q-chartValue e nx ny nz p) := by
      dsimp [chartValue,linePoint3]
      ring
    rw [heq]
    have hh := abs_add_le (chartValue e nx ny nz p-c)
      (l*(chartValue e nx ny nz q-chartValue e nx ny nz p))
    rw [abs_mul] at hh
    have hm := mul_le_mul hlbound hend (abs_nonneg _) (by positivity : (0:ℝ)≤8/r)
    linarith only [hh,hpslab,hm]
  have hfinal := abs_add_le (chartValue e nx ny nz z-chartValue e nx ny nz (linePoint3 p q l))
    (chartValue e nx ny nz (linePoint3 p q l)-c)
  have heq : chartValue e nx ny nz z-chartValue e nx ny nz (linePoint3 p q l)+
      (chartValue e nx ny nz (linePoint3 p q l)-c)=chartValue e nx ny nz z-c := by ring
  rw [heq] at hfinal
  have ht : |chartValue e nx ny nz z-c|≤6*rho+(8/r)*(6*rho) := by
    linarith only [hfinal,hlinearError,hline]
  have hscale : 6*rho+(8/r)*(6*rho)≤54*rho/r := by
    apply (le_div_iff₀ hr).mpr
    have he : (6*rho+(8/r)*(6*rho))*r=6*rho*r+48*rho := by field_simp; ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hr1 (show 0≤6*rho by positivity)]
  exact ht.trans hscale


/-- Every actual retained heavy direction has a literal original heavy
slab whose enlargement contains the bounded Euclidean tube through the
same original pair. -/
theorem retained_heavy_slab_contains_original_tube
    (P : Finset Point3) (rho H r : ℝ) (z : Pair3) (d : DirectionLabel)
    (hrho : 0<rho) (hrho1 : rho≤1) (hr : 0<r) (hr1 : r≤1)
    (hp : ∀ i, |z.1 i|≤1) (hsep : r≤distance3 z.1 z.2)
    (hd : d∈goodDirections P rho H z) :
    ∃ k : ℤ, H≤((slabPoints P rho d k).card : ℝ) ∧
      z.1∈slabPoints P rho d k ∧ z.2∈slabPoints P rho d k ∧
      ∀ x : Point3, (∀ i, |x i|≤2) → x∈physicalTube3 z.1 z.2 rho →
        |unitValue rho d x-rho*k/normalLength rho d|≤54*rho/r := by
  obtain ⟨k,hm,hpS,hqS,hslab⟩ := retained_direction_original_slab P rho H z d hrho.le hd
  refine ⟨k,hm,hpS,hqS,?_⟩
  have he (x : Point3) : chartValue d.1 (rho*d.2.1/normalLength rho d)
      (rho*d.2.2/normalLength rho d) (1/normalLength rho d) x=unitValue rho d x := by
    dsimp [chartValue,unitValue,value,projection]
    ring
  intro x hx hxtube
  have hh := original_physical_tube_in_unit_slab z.1 z.2 x d.1
    (rho*d.2.1/normalLength rho d) (rho*d.2.2/normalLength rho d)
    (1/normalLength rho d) (rho*k/normalLength rho d) rho r hrho hrho1 hr hr1
    (original_normal_coefficients_unit rho d) hp hx hsep
    (by simpa only [he] using hslab z.1 hpS) (by simpa only [he] using hslab z.2 hqS) hxtube
  simpa only [he] using hh

end OriginalThreeDimensionalTubeSlab
