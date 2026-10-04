import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

noncomputable section
namespace NativeA2PowerBudget

/-- A positive-power threshold, with a literal positive choice independent
of any subsequently chosen loss exponent. -/
theorem exists_power_threshold (e c : ℝ) (he : 0<e) (hc : 0<c) :
    ∃ d : ℝ, 0<d ∧ ∀ delta : ℝ, 0<delta → delta≤d → delta^e≤c := by
  refine ⟨c^(e⁻¹),Real.rpow_pos_of_pos hc _,?_⟩
  intro delta hd hdd
  exact (Real.rpow_le_rpow hd.le hdd he.le).trans_eq
    (Real.rpow_inv_rpow hc.le (ne_of_gt he))

/-- Each of three original bad-pair terms pays one third of the target
power. The exponent comparison is kept separate from its fixed constant. -/
theorem absorb_power_term (delta C a q gap : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (hC : 0≤C)
    (ha : q+gap≤a) (hsmall : C*delta^gap≤1/3) :
    C*delta^a≤delta^q/3 := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1 ha
  have hm := mul_le_mul_of_nonneg_left hp hC
  rw [Real.rpow_add hd] at hm
  have hb := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hd.le q)
  nlinarith only [hm,hb]

/-- All source A.2 losses are absorbed uniformly in 0<chi<=t*eps1/12.
The Euclidean-to-box factor four is included in the overlap condition. -/
theorem native_power_budget (delta t eps1 eps2 chi : ℝ)
    (hd : 0<delta) (hd1 : delta≤1) (ht : 0<t)
    (he1 : 0<eps1) (he1small : eps1<1/8) ( _he2 : 0<eps2)
    (hchi : chi≤t*eps1/12)
    (hoverlap : delta^(7*t*eps1/4)≤1/8)
    (htransverse : delta^(t*eps1/4)≤1/(48*704^2))
    (htwoends : delta^(eps2/2)≤1/12)
    (hdiagonal : delta^(t/2)≤1/12) :
    8*delta^(2*t*eps1-3*chi)≤1 ∧
      16*704^2*delta^(t*eps1-3*chi)+4*delta^eps2+4*delta^(t-chi)
        ≤delta^(min (t*eps1/2) (eps2/2)) := by
  have ha : 0<t*eps1 := mul_pos ht he1
  have hasmall : t*eps1<t/8 := by nlinarith only [mul_pos ht (sub_pos.mpr he1small)]
  have hq1 : min (t*eps1/2) (eps2/2)≤t*eps1/2 := min_le_left _ _
  have hq2 : min (t*eps1/2) (eps2/2)≤eps2/2 := min_le_right _ _
  have hp := Real.rpow_le_rpow_of_exponent_ge hd hd1
    (show 7*t*eps1/4≤2*t*eps1-3*chi by nlinarith only [hchi])
  constructor
  · nlinarith only [hp,hoverlap]
  · have h1 := absorb_power_term delta (16*704^2) (t*eps1-3*chi)
      (min (t*eps1/2) (eps2/2)) (t*eps1/4) hd hd1 (by norm_num)
      (by nlinarith only [hchi,hq1]) (by nlinarith only [htransverse])
    have h2 := absorb_power_term delta 4 eps2
      (min (t*eps1/2) (eps2/2)) (eps2/2) hd hd1 (by norm_num)
      (by linarith only [hq2]) (by linarith only [htwoends])
    have h3 := absorb_power_term delta 4 (t-chi)
      (min (t*eps1/2) (eps2/2)) (t/2) hd hd1 (by norm_num)
      (by nlinarith only [hchi,hq1,hasmall,ht]) (by linarith only [hdiagonal])
    linarith only [h1,h2,h3]

/-- One original small-scale threshold serves EVERY admissible chi. -/
theorem exists_native_threshold (t eps1 eps2 : ℝ)
    (ht : 0<t) (he1 : 0<eps1) (he2 : 0<eps2) :
    ∃ d : ℝ, 0<d ∧ d≤1/2 ∧ ∀ delta : ℝ, 0<delta → delta≤d →
      delta^eps1≤1/1408 ∧ delta^(7*t*eps1/4)≤1/8 ∧
      delta^(t*eps1/4)≤1/(48*704^2) ∧ delta^(eps2/2)≤1/12 ∧
      delta^(t/2)≤1/12 := by
  obtain ⟨d0,hd0,h0⟩ := exists_power_threshold eps1 (1/1408) he1 (by norm_num)
  obtain ⟨d1,hd1,h1⟩ := exists_power_threshold (7*t*eps1/4) (1/8) (by positivity) (by norm_num)
  obtain ⟨d2,hd2,h2⟩ := exists_power_threshold (t*eps1/4) (1/(48*704^2)) (by positivity) (by norm_num)
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

end NativeA2PowerBudget
