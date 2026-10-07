import Theorems.Thm_StickyKakeya4_native_direction_rank_dichotomy
import Theorems.Thm_StickyKakeya4_native_transverse_fiber_diameter

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeSeparatedSpanControl
open Classical NativeDirectionRankDichotomy NativeTransverseFiberDiameter
open scoped BigOperators
variable {α V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def coefficientCost (B q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => 1/q+(1+B/q)*coefficientCost B q n

lemma coefficientCost_nonneg {B q : ℝ} (hB : 0 ≤ B) (hq : 0 < q) (n : ℕ) :
    0 ≤ coefficientCost B q n := by
  induction n with
  | zero => simp [coefficientCost]
  | succ n ih => simp only [coefficientCost]; positivity

/-- Actual successive span separation bounds all coefficients in the
original ordered vector family; no inverse-frame certificate is supplied. -/
theorem coefficient_sum_bound (v : α → V) (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (xs : List α) (hsep : Separated v q xs) (hv : ∀a∈xs,‖v a‖ ≤ B)
    (c : Fin xs.length → ℝ) :
    (∑i,|c i|) ≤ coefficientCost B q xs.length * ‖∑i,c i • v (xs.get i)‖ := by
  induction xs with
  | nil => simp [coefficientCost]
  | cons a xs ih =>
    let tail : V := ∑i : Fin xs.length,c i.succ • v (xs.get i)
    let total : V := ∑i : Fin (a::xs).length,c i • v ((a::xs).get i)
    have htotal : total=c 0 • v a+tail := by simp [total,tail,Fin.sum_univ_succ]
    have htailP : tail∈spanOf v xs := by
      apply Submodule.sum_mem
      intro i _hi
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i,rfl⟩
    have hscalar := transverse_scalar_bound (spanOf v xs) (v a) q hsep.2.le
      (c 0) (-tail) ((spanOf v xs).neg_mem htailP) ‖total‖ (by
        rw [htotal]
        simp only [sub_neg_eq_add,le_refl])
    have hc0 : |c 0| ≤ ‖total‖/q := (le_div_iff₀ hq).mpr hscalar
    have htail : ‖tail‖ ≤ (1+B/q)*‖total‖ := by
      have he : tail=total-c 0 • v a := by rw [htotal]; abel
      calc
        ‖tail‖ = ‖total-c 0 • v a‖ := congrArg norm he
        _ ≤ ‖total‖+‖c 0 • v a‖ := norm_sub_le _ _
        _ = ‖total‖+|c 0| * ‖v a‖ := by rw [norm_smul,Real.norm_eq_abs]
        _ ≤ ‖total‖+(‖total‖/q)*B :=
          add_le_add le_rfl (mul_le_mul hc0 (hv a (by simp)) (norm_nonneg _) (by positivity))
        _ = _ := by ring
    have hi := ih hsep.1 (fun b hb => hv b (by simp [hb])) (fun i : Fin xs.length => c i.succ)
    change (∑i : Fin xs.length,|c i.succ|) ≤ coefficientCost B q xs.length*‖tail‖ at hi
    change (∑ i : Fin (xs.length+1), |c i|) ≤ coefficientCost B q (xs.length+1) * ‖total‖
    rw [Fin.sum_univ_succ]
    calc
      _ ≤ ‖total‖/q+coefficientCost B q xs.length*‖tail‖ := add_le_add hc0 hi
      _ ≤ ‖total‖/q+coefficientCost B q xs.length*((1+B/q)*‖total‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left htail (coefficientCost_nonneg hB hq _))
      _ = coefficientCost B q (a::xs).length*‖total‖ := by simp only [List.length_cons,coefficientCost]; ring

/-- A separated finite family close to P has its entire span quantitatively
close to P. This is a forward span estimate; reverse plane control requires
the separate equal-dimension/invertibility argument. -/
theorem span_near_plane (v : α → V) (q B h : ℝ) (hq : 0 < q) (hB : 0 ≤ B) (hh : 0 < h)
    (xs : List α) (hsep : Separated v q xs) (hv : ∀a∈xs,‖v a‖ ≤ B)
    (P : Submodule ℝ V) (hnear : ∀a∈xs,Metric.infDist (v a) (P:Set V) ≤ h)
    (w : V) (hw : w∈spanOf v xs) :
    Metric.infDist w (P:Set V) ≤ 2*h*coefficientCost B q xs.length*‖w‖ := by
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  have hchoice : ∀i : Fin xs.length,∃u∈P,‖v (xs.get i)-u‖ ≤ 2*h := by
    intro i
    obtain ⟨u,hu,he⟩ := (Metric.infDist_lt_iff
      (show (P:Set V).Nonempty from ⟨0,P.zero_mem⟩)).mp
      ((hnear (xs.get i) (List.get_mem xs i)).trans_lt (by linarith : h<2*h))
    exact ⟨u,hu,by simpa only [dist_eq_norm] using he.le⟩
  choose u hu he using hchoice
  have hp : (∑i,c i • u i)∈P := P.sum_mem (fun i _hi => P.smul_mem _ (hu i))
  apply (Metric.infDist_le_dist_of_mem hp).trans
  rw [dist_eq_norm,←hc,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑i,‖c i • v (xs.get i)-c i • u i‖ := norm_sum_le _ _
    _ = ∑i,|c i| * ‖v (xs.get i)-u i‖ := by simp only [←smul_sub,norm_smul,Real.norm_eq_abs]
    _ ≤ ∑i,|c i| * (2*h) := Finset.sum_le_sum (fun i _hi => mul_le_mul_of_nonneg_left (he i) (abs_nonneg _))
    _ = (2*h)*(∑i,|c i|) := by rw [←Finset.sum_mul]; ring
    _ ≤ (2*h)*(coefficientCost B q xs.length*‖∑i,c i • v (xs.get i)‖) :=
      mul_le_mul_of_nonneg_left (coefficient_sum_bound v q B hq hB xs hsep hv c) (by positivity)
    _ = _ := by rw [hc]; ring

end NativeSeparatedSpanControl
