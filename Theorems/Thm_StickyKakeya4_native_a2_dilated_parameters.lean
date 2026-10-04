import Theorems.Thm_StickyKakeya4_native_a2_power_budget
import Theorems.Thm_StickyKakeya4_native_a2_parameter_identities

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

noncomputable section
namespace NativeA2DilatedParameters
open NativeA2PowerBudget

/-- Every original profile query remains legal with a fixed physical tube
dilation C>=1; only the small delta threshold changes. -/
theorem dilated_geometric_scales (delta eps1 C : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (he1 : eps1<1/8) (hC : 1≤C)
    (hsmall : delta^eps1≤1/(1408*C)) :
    let theta := delta^eps1
    11*(2*C*theta^4)/(theta^2)=22*C*theta^2 ∧
    4*(11*(2*C*theta^4)/(theta^2))/(theta/8)=704*C*theta ∧
    delta≤2*theta^2 ∧ 2*theta^2≤1 ∧
    delta≤2*(704*C*theta) ∧ 2*(704*C*theta)≤1 ∧
    3*(22*C*theta^2)+2*(theta/8)≤theta/2 := by
  let theta := delta^eps1
  have ht : 0<theta := Real.rpow_pos_of_pos hd _
  have ht0 : theta≠0 := ne_of_gt ht
  have hCpos : 0<C := zero_lt_one.trans_le hC
  have hsmall' : C*theta≤1/1408 := by
    have h := (le_div_iff₀ (show 0<1408*C by positivity)).mp hsmall
    change theta*(1408*C)≤1 at h
    nlinarith only [h]
  have htC : theta≤C*theta := by nlinarith only [mul_le_mul_of_nonneg_right hC ht.le]
  have htSmall : theta≤1/1408 := htC.trans hsmall'
  have hbase := NativeA2ParameterIdentities.native_geometric_scales delta eps1
    hd hd1 he1 htSmall
  have hw : 11*(2*C*theta^4)/(theta^2)=22*C*theta^2 := by field_simp; ring
  have hR : 4*(11*(2*C*theta^4)/(theta^2))/(theta/8)=704*C*theta := by
    rw [hw]
    field_simp
    ring
  have hlin := mul_le_mul_of_nonneg_left hsmall' ht.le
  refine ⟨hw,hR,hbase.2.2.1,hbase.2.2.2.1,?_,?_,?_⟩
  · have hlow := hbase.2.2.2.2.1
    nlinarith only [hlow,htC]
  · nlinarith only [hsmall']
  · nlinarith only [hlin,ht]

/-- Exact native transverse exponent with an arbitrary nonnegative fixed
radius constant, before the t<=2 estimate. -/
theorem transverse_constant_power_identity (delta eps1 t chi B : ℝ)
    (hd : 0<delta) (hB : 0≤B) :
    delta^(-chi)*(B*delta^eps1)^t=
      (delta^chi)^2*B^t*delta^(t*eps1-3*chi) := by
  rw [Real.mul_rpow hB (Real.rpow_nonneg hd.le _),← Real.rpow_mul hd.le]
  calc
    _ = B^t*(delta^(-chi)*delta^(eps1*t)) := by ring
    _ = B^t*delta^(-chi+eps1*t) := by rw [← Real.rpow_add hd]
    _ = B^t*delta^(chi*2+(t*eps1-3*chi)) := by congr 2; ring
    _ = _ := by rw [Real.rpow_add hd,Real.rpow_mul hd.le,Real.rpow_two]; ring

/-- Fixed dilations preserve the target graph-density exponent. -/
theorem dilated_power_budget (delta t eps1 eps2 chi C : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (ht : 0<t)
    (he1small : eps1<1/8) (hC : 1≤C) (hchi : chi≤t*eps1/12)
    (htransverse : delta^(t*eps1/4)≤1/(48*(704*C)^2))
    (htwoends : delta^(eps2/2)≤1/12)
    (hdiagonal : delta^(t/2)≤1/12) :
    16*(704*C)^2*delta^(t*eps1-3*chi)+4*delta^eps2+4*delta^(t-chi)
      ≤delta^(min (t*eps1/2) (eps2/2)) := by
  have hCpos : 0<C := zero_lt_one.trans_le hC
  have hasmall : t*eps1<t/8 := by nlinarith only [mul_pos ht (sub_pos.mpr he1small)]
  have hq1 : min (t*eps1/2) (eps2/2)≤t*eps1/2 := min_le_left _ _
  have hq2 : min (t*eps1/2) (eps2/2)≤eps2/2 := min_le_right _ _
  have hconstant : 16*(704*C)^2*delta^(t*eps1/4)≤1/3 := by
    have hh := (le_div_iff₀ (show 0<48*(704*C)^2 by positivity)).mp htransverse
    nlinarith only [hh]
  have h1 := absorb_power_term delta (16*(704*C)^2) (t*eps1-3*chi)
    (min (t*eps1/2) (eps2/2)) (t*eps1/4) hd hd1 (by positivity)
    (by nlinarith only [hchi,hq1]) hconstant
  have h2 := absorb_power_term delta 4 eps2
    (min (t*eps1/2) (eps2/2)) (eps2/2) hd hd1 (by norm_num)
    (by linarith only [hq2]) (by linarith only [htwoends])
  have h3 := absorb_power_term delta 4 (t-chi)
    (min (t*eps1/2) (eps2/2)) (t/2) hd hd1 (by norm_num)
    (by nlinarith only [hchi,hq1,hasmall,ht]) (by linarith only [hdiagonal])
  linarith only [h1,h2,h3]

/-- The threshold depends on the fixed dilation C, but is uniform over all
subsequently chosen admissible chi. -/
theorem exists_dilated_native_threshold (t eps1 eps2 C : ℝ)
    (ht : 0<t) (he1 : 0<eps1) (he2 : 0<eps2) (hC : 1≤C) :
    ∃ d : ℝ, 0<d ∧ d≤1/2 ∧ ∀ delta : ℝ, 0<delta → delta≤d →
      delta^eps1≤1/(1408*C) ∧ delta^(7*t*eps1/4)≤1/8 ∧
      delta^(t*eps1/4)≤1/(48*(704*C)^2) ∧ delta^(eps2/2)≤1/12 ∧
      delta^(t/2)≤1/12 := by
  have hCpos : 0<C := zero_lt_one.trans_le hC
  obtain ⟨d0,hd0,h0⟩ := exists_power_threshold eps1 (1/(1408*C)) he1 (by positivity)
  obtain ⟨d1,hd1,h1⟩ := exists_power_threshold (7*t*eps1/4) (1/8) (by positivity) (by norm_num)
  obtain ⟨d2,hd2,h2⟩ := exists_power_threshold (t*eps1/4) (1/(48*(704*C)^2)) (by positivity) (by positivity)
  obtain ⟨d3,hd3,h3⟩ := exists_power_threshold (eps2/2) (1/12) (by positivity) (by norm_num)
  obtain ⟨d4,hd4,h4⟩ := exists_power_threshold (t/2) (1/12) (by positivity) (by norm_num)
  let d := min (1/2) (min d0 (min d1 (min d2 (min d3 d4))))
  have hdpos : 0<d := by dsimp [d]; positivity
  refine ⟨d,hdpos,min_le_left _ _,?_⟩
  intro delta hdelta hle
  have hh : delta≤min d0 (min d1 (min d2 (min d3 d4))) :=
    hle.trans (min_le_right _ _)
  obtain ⟨hdd0,hdd1,hdd2,hdd3,hdd4⟩ :=
    (show delta≤d0 ∧ delta≤d1 ∧ delta≤d2 ∧ delta≤d3 ∧ delta≤d4 by
      simpa only [le_min_iff] using hh)
  exact ⟨h0 delta hdelta hdd0,h1 delta hdelta hdd1,h2 delta hdelta hdd2,
    h3 delta hdelta hdd3,h4 delta hdelta hdd4⟩

end NativeA2DilatedParameters
