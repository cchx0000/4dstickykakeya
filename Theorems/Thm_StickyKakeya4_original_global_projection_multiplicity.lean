import Theorems.Thm_StickyKakeya4_original_two_projection_cartesian
import Theorems.Thm_StickyKakeya4_backward_fiber_grains

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical

namespace OriginalGlobalProjectionMultiplicity
open BackwardFiberGrains OriginalTwoProjectionCartesian ProjectionAnnulusEnergy

/-- Selecting dense original classes preserves their whole original fibers. -/
lemma selected_fiber_eq {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (Q : Finset X) (f : X → Y) (t : ℝ) {p : X}
    (hp : p ∈ denseClassRestriction Q f (fun _ => (1:ℝ)) t) :
    (denseClassRestriction Q f (fun _ => (1:ℝ)) t).filter (fun x => f x=f p)=
      Q.filter (fun x => f x=f p) := by
  have ht := (Finset.mem_filter.mp hp).2
  ext x
  simp only [denseClassRestriction,Finset.mem_filter]
  constructor
  · intro hx
    exact ⟨hx.1.1,hx.2⟩
  · intro hx
    exact ⟨⟨hx.1,by simpa only [hx.2] using ht⟩,hx.2⟩

/-- Literal small projected covers give globally rich original projection
fibers while retaining half the original query mass. No local upper
multiplicity or scalar Frostman conclusion is asserted. -/
theorem exists_original_global_projection_multiplicity
    (P Q : Finset Point) {delta lam q K : ℝ}
    (hP : P.Nonempty) (hd : 0 < delta) (hq : 0 < q) (hK : 0 < K)
    (hQP : Q ⊆ P) (hmass : q*(P.card : ℝ) ≤ Q.card)
    (hcover : ((alphabet Q delta lam).card : ℝ) ≤ K*Real.sqrt P.card) :
    ∃ R : Finset Point, R ⊆ Q ∧ (q/2)*(P.card : ℝ) ≤ R.card ∧
      ∀ p ∈ R,
        q*Real.sqrt P.card/(2*K) ≤
          (R.filter (fun x => scalarCode delta lam x=scalarCode delta lam p)).card ∧
        R.filter (fun x => scalarCode delta lam x=scalarCode delta lam p)=
          Q.filter (fun x => scalarCode delta lam x=scalarCode delta lam p) ∧
        q*Real.sqrt P.card/(2*K) ≤
          (P.filter (fun x => |projection lam x-projection lam p| ≤ delta)).card := by
  let f := scalarCode delta lam
  let I := Q.image f
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hQpos : (0 : ℝ) < Q.card := (mul_pos hq hPpos).trans_le hmass
  have hQnon : Q.Nonempty := Finset.card_pos.mp (by exact_mod_cast hQpos)
  have hInon : I.Nonempty := hQnon.image f
  have hIpos : (0 : ℝ) < I.card := by exact_mod_cast hInon.card_pos
  let t := (Q.card : ℝ)/(2*I.card)
  let R := denseClassRestriction Q f (fun _ => (1:ℝ)) t
  have hc := dense_class_retains_half Q f (fun _ => (1:ℝ)) I.card 1 hInon.card_pos
    (fun _ _ => by norm_num) (by simpa using hQpos)
    (by
      rw [Nat.mul_one]
      apply le_of_eq
      congr 1
      ext z
      simp [I])
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_one,classMass] at hc
  have hret : (Q.card : ℝ)/2 ≤ R.card := by
    exact hc.1
  have hfiber : ∀ p ∈ R, t ≤ (R.filter (fun x => f x=f p)).card := by
    intro p hp
    convert hc.2 p hp using 1
    congr 1
    congr 1
    ext x
    simp only [Finset.mem_filter]
    rfl
  have hRq : R ⊆ Q := Finset.filter_subset _ _
  have hRmass : (q/2)*(P.card : ℝ) ≤ R.card := by linarith
  have hthreshold : q*Real.sqrt P.card/(2*K) ≤ t := by
    have hIbound : (I.card : ℝ) ≤ K*Real.sqrt P.card := hcover
    have hs := Real.sq_sqrt hPpos.le
    have hm1 := mul_le_mul_of_nonneg_left hIbound
      (show 0 ≤ q*Real.sqrt P.card by positivity)
    have hm1' : q*Real.sqrt P.card*(I.card : ℝ) ≤ q*K*P.card := by
      calc
        _ ≤ q*Real.sqrt P.card*(K*Real.sqrt P.card) := hm1
        _ = q*K*(Real.sqrt P.card)^2 := by ring
        _ = _ := by rw [hs]
    have hm2 := mul_le_mul_of_nonneg_left hmass hK.le
    dsimp [t]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*K) (by positivity : (0:ℝ) < 2*I.card)).mpr
    nlinarith only [hm1',hm2]
  refine ⟨R,hRq,hRmass,?_⟩
  intro p hp
  have hm := hthreshold.trans (hfiber p hp)
  have heq := selected_fiber_eq Q f t hp
  have hsub : R.filter (fun x => f x=f p) ⊆
      P.filter (fun x => |projection lam x-projection lam p| ≤ delta) := by
    intro x hx
    obtain ⟨hxR,hxp⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hQP (hRq hxR),same_scalar_code_close hd hxp⟩
  exact ⟨hm,heq,hm.trans (Nat.cast_le.mpr (Finset.card_le_card hsub))⟩

end OriginalGlobalProjectionMultiplicity
