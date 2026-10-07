import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable section
namespace NativePaidParentScaleBudget
open Classical Finset NativeJointUniformCoarseRelations

/-- A nonempty incidence set contains a nonempty self-fiber, so its
uniformity radix cannot vanish. -/
lemma uniform_radix_pos {A B : Type*} [DecidableEq A] [DecidableEq B]
    (E : Finset A) (hEne : E.Nonempty) (f : A → B) (Q : ℕ)
    (HU : HasUniformFibers E Q f) : 0 < Q := by
  obtain ⟨x,hx⟩ := hEne
  have hfiber : 0 < (E.filter (fun z => f z=f x)).card :=
    Finset.card_pos.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩
  have hself := HU x hx x hx
  by_contra hQ
  have hzero : Q=0 := by omega
  simp only [hzero,zero_pow (by decide : 2≠0),zero_mul] at hself
  omega

/-- The actual first-stage transfer budget already pays the fixed 729
comparison factor together with the square of the uniformity radix. -/
lemma geometry_radix_cost {delta eta cost : ℝ} (hd : 0 < delta)
    (hd1 : delta ≤ 1) (heta : 0 ≤ eta) (F Q : ℕ) (hF : 0 < F)
    (hcost : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤
      delta^(-cost)) :
    (729:ℝ)*(Q:ℝ)^2 ≤ delta^(-cost) := by
  have hF1 : (1:ℝ) ≤ F := by exact_mod_cast hF
  have hC : (729:ℝ) ≤ (125*175616*16384:ℝ)*(F:ℝ) := by nlinarith
  have hp : 1 ≤ delta^(-eta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr heta)
  have hs := mul_le_mul_of_nonneg_right hC (sq_nonneg (Q:ℝ))
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2 by positivity)
  have hm' : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2 ≤
      (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) := by
    simpa only [mul_one] using hm
  exact hs.trans (hm'.trans hcost)

/-- The exact geometric parent-transfer denominator loses ten powers of
the scale ratio and the already paid radix cost. -/
lemma transfer_denominator_cost {delta r cost gap : ℝ} (hd : 0 < delta)
    (hr : 0 ≤ r) (Q : ℕ) (hratio : r ≤ delta^(-gap))
    (hrad : (729:ℝ)*(Q:ℝ)^2 ≤ delta^(-cost)) :
    (729:ℝ)*r^(10:ℕ)*(Q:ℝ)^2 ≤ delta^(-(cost+10*gap)) := by
  have hp := pow_le_pow_left₀ hr hratio 10
  calc
    _ = ((729:ℝ)*(Q:ℝ)^2)*r^(10:ℕ) := by ring
    _ ≤ delta^(-cost)*(delta^(-gap))^(10:ℕ) :=
      mul_le_mul hrad hp (pow_nonneg hr 10) (Real.rpow_pos_of_pos hd _).le
    _ = _ := by
      rw [←Real.rpow_mul_natCast hd.le,←Real.rpow_add hd]
      congr 1
      ring

/-- Absorb the fixed actual denominator into the original-scale power,
preserving the conditional near-extremal coefficient. -/
lemma absorbed_lower {delta theta r tau cost gap P M : ℝ}
    (hd : 0 < delta) (htheta : 0 ≤ theta) (hr : 0 < r) (Q : ℕ)
    (hQ : 0 < Q) (hP : 0 ≤ P)
    (hden : (729:ℝ)*r^(10:ℕ)*(Q:ℝ)^2 ≤ delta^(-(cost+10*gap)))
    (hnear : (theta/((729:ℝ)*r^(10:ℕ)*(Q:ℝ)^2))*delta^tau*P ≤ M) :
    theta*delta^(tau+cost+10*gap)*P ≤ M := by
  have hQr : (0:ℝ) < Q := by exact_mod_cast hQ
  have hdenpos : (0:ℝ) < (729:ℝ)*r^(10:ℕ)*(Q:ℝ)^2 := by positivity
  have hcostpos : 0 < delta^(cost+10*gap) := Real.rpow_pos_of_pos hd _
  have hcancel : delta^(-(cost+10*gap))*delta^(cost+10*gap)=1 := by
    rw [←Real.rpow_add hd]
    simp
  have hpaid : ((729:ℝ)*r^(10:ℕ)*(Q:ℝ)^2)*delta^(cost+10*gap) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right hden hcostpos.le).trans_eq hcancel
  have hinv : delta^(cost+10*gap) ≤ 1/((729:ℝ)*r^(10:ℕ)*(Q:ℝ)^2) := by
    apply (le_div_iff₀ hdenpos).mpr
    simpa only [mul_comm] using hpaid
  have hcoef : theta*delta^(cost+10*gap) ≤ theta/((729:ℝ)*r^(10:ℕ)*(Q:ℝ)^2) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv htheta
  calc
    _ = (theta*delta^(cost+10*gap))*delta^tau*P := by
      rw [show tau+cost+10*gap=(cost+10*gap)+tau by ring,Real.rpow_add hd]
      ring
    _ ≤ (theta/((729:ℝ)*r^(10:ℕ)*(Q:ℝ)^2))*delta^tau*P :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (Real.rpow_pos_of_pos hd tau).le) hP
    _ ≤ M := hnear

end NativePaidParentScaleBudget
