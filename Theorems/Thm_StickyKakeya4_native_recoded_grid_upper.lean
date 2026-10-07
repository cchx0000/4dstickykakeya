import Theorems.Thm_StickyKakeya4_native_literal_grid_overlap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeRecodedGridUpper
open Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open NativeLiteralGridOverlap NativeFiniteSliceUnionAD
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma incidence_sum_swap {ι X : Type*} (S : Finset ι) (T : Finset X) (rel : ι → X → Prop) :
    (∑k∈S, ((T.filter (rel k)).card:ℝ)) =
      ∑a∈T, ((S.filter (fun k => rel k a)).card:ℝ) := by
  classical
  have hn : (∑k∈S, (T.filter (rel k)).card) =
      ∑a∈T, (S.filter (fun k => rel k a)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  exact_mod_cast hn

/-- Every coarse grid label has an actual original source witness. Source
rho-balls around those witnesses have AD lower mass; their overlap is
bounded by the literal grid lemma. The global source count is used by the
arbitrary-center upper whenever its enclosing radius exceeds one. -/
theorem grid_ball_upper_of_witnesses {l : ℕ}
    (A : Finset (Fin l → ℝ)) (B : Finset (Fin l → ℤ))
    (witness : (Fin l → ℤ) → (Fin l → ℝ)) (N : ℕ)
    {mu rho K s : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s) (hglobal : (A.card:ℝ) ≤ K*mu^(-s))
    (hmem : ∀k∈B, witness k∈A)
    (hclose : ∀k∈B, dist (center rho k) (witness k) ≤ (N:ℝ)*rho)
    (x : Fin l → ℝ) (r : ℝ) (hrhor : rho ≤ r) (hr1 : r ≤ 1) :
    ((B.filter (fun k => dist (center rho k) x ≤ r)).card:ℝ) ≤
      (((4*N+5)^l:ℕ):ℝ)*K^2*(2*((N:ℝ)+2))^s*(r/rho)^s := by
  classical
  have hrho : 0 < rho := hmu.trans_le hmurho
  have hr : 0 < r := hrho.trans_le hrhor
  have hrho1 : rho ≤ 1 := hrhor.trans hr1
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hN2 : (1:ℝ) ≤ (N:ℝ)+2 := by linarith only [hN0]
  let S := B.filter (fun k => dist (center rho k) x ≤ r)
  let R := ((N:ℝ)+2)*r
  let T := carrierBall A x R
  let M : ℝ := (((4*N+5)^l:ℕ):ℝ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hRtest : mu ≤ R := hmurho.trans (hrhor.trans (le_mul_of_one_le_left hr.le hN2))
  have hSA : ∀k∈S, k∈B := fun k hk => (Finset.mem_filter.mp hk).1
  have hfoot : ∀k∈S, T.filter (fun a => dist a (witness k) ≤ rho) =
      carrierBall A (witness k) rho := by
    intro k hk
    have hkB := hSA k hk
    have hkx := (Finset.mem_filter.mp hk).2
    have hwk : dist (witness k) (center rho k) ≤ (N:ℝ)*rho := by
      simpa only [dist_comm] using hclose k hkB
    have hsub : carrierBall A (witness k) rho ⊆ T := by
      intro a ha
      obtain ⟨haA,haw⟩ := (mem_carrierBall A a (witness k) rho).mp ha
      apply (mem_carrierBall A a x R).mpr
      refine ⟨haA,?_⟩
      have ht1 := dist_triangle a (witness k) x
      have ht2 := dist_triangle (witness k) (center rho k) x
      have hscale := mul_le_mul_of_nonneg_left hrhor (show (0:ℝ) ≤ (N:ℝ)+1 by positivity)
      dsimp [R]
      linarith only [ht1,ht2,haw,hwk,hkx,hscale]
    ext a
    constructor
    · intro ha
      obtain ⟨haT,haw⟩ := Finset.mem_filter.mp ha
      exact (mem_carrierBall A a (witness k) rho).mpr
        ⟨((mem_carrierBall A a x R).mp haT).1,haw⟩
    · intro ha
      exact Finset.mem_filter.mpr ⟨hsub ha,((mem_carrierBall A a (witness k) rho).mp ha).2⟩
  have hrows : (S.card:ℝ)*((rho/mu)^s/K) ≤
      ∑k∈S, ((T.filter (fun a => dist a (witness k) ≤ rho)).card:ℝ) := by
    calc
      _ = ∑_k∈S, (rho/mu)^s/K := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [hfoot k hk]
        exact (hAD (witness k) (hmem k (hSA k hk)) rho hmurho hrho1).1
  have hcols : ∀a∈T, ((S.filter (fun k => dist a (witness k) ≤ rho)).card:ℝ) ≤ M := by
    intro a _ha
    have hsub : S.filter (fun k => dist a (witness k) ≤ rho) ⊆
        B.filter (fun k => dist (center rho k) a ≤ ((N+1:ℕ):ℝ)*rho) := by
      intro k hk
      obtain ⟨hkS,haw⟩ := Finset.mem_filter.mp hk
      have hkB := hSA k hkS
      have hwa : dist (witness k) a ≤ rho := by simpa only [dist_comm] using haw
      have hc := hclose k hkB
      have ht := dist_triangle (center rho k) (witness k) a
      apply Finset.mem_filter.mpr
      refine ⟨hkB,?_⟩
      push_cast
      linarith only [hc,hwa,ht]
    have hcard : (S.filter (fun k => dist a (witness k) ≤ rho)).card ≤ (4*N+5)^l := by
      calc
        _ ≤ (B.filter (fun k => dist (center rho k) a ≤ ((N+1:ℕ):ℝ)*rho)).card :=
          Finset.card_le_card hsub
        _ ≤ (4*(N+1)+1)^l := grid_ball_card_le B hrho a (N+1)
        _ = (4*N+5)^l := by rfl
    dsimp only [M]
    exact_mod_cast hcard
  have hcounts : (S.card:ℝ)*((rho/mu)^s/K) ≤ (T.card:ℝ)*M := by
    calc
      _ ≤ ∑k∈S, ((T.filter (fun a => dist a (witness k) ≤ rho)).card:ℝ) := hrows
      _ = ∑a∈T, ((S.filter (fun k => dist a (witness k) ≤ rho)).card:ℝ) :=
        incidence_sum_swap S T (fun k a => dist a (witness k) ≤ rho)
      _ ≤ ∑_a∈T, M := Finset.sum_le_sum hcols
      _ = _ := by simp
  have hcounts' : ((S.card:ℝ)*(rho/mu)^s)/K ≤ (T.card:ℝ)*M := by
    simpa only [mul_div_assoc] using hcounts
  have hmass := (div_le_iff₀ hK0).mp hcounts'
  have hTupper := arbitrary_center_ball_upper A hmu hK0 hs hAD hglobal x hRtest
  have hRpow : (2:ℝ)^s*K*(R/mu)^s = K*(2*((N:ℝ)+2))^s*(r/mu)^s := by
    have heq : R/mu = ((N:ℝ)+2)*(r/mu) := by dsimp [R]; ring
    rw [heq,Real.mul_rpow (by positivity : (0:ℝ) ≤ (N:ℝ)+2) (div_nonneg hr.le hmu.le),
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ (N:ℝ)+2)]
    ring
  have hratio : (r/mu)^s = (r/rho)^s*(rho/mu)^s := by
    have heq : r/mu = (r/rho)*(rho/mu) := by field_simp
    rw [heq,Real.mul_rpow (div_nonneg hr.le hrho.le) (div_nonneg hrho.le hmu.le)]
  rw [hRpow,hratio] at hTupper
  have hfinal : (S.card:ℝ)*(rho/mu)^s ≤
      (M*K^2*(2*((N:ℝ)+2))^s*(r/rho)^s)*(rho/mu)^s := by
    calc
      _ ≤ (T.card:ℝ)*M*K := hmass
      _ ≤ (K*(2*((N:ℝ)+2))^s*((r/rho)^s*(rho/mu)^s))*M*K :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTupper hM) hK0.le
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos (div_pos hrho hmu) s)).mp hfinal

/-- Source-facing actual-grid upper bound. Witnesses are selected from the
literal original fine set. The large-radius argument uses hglobal, and no
AD property of the recoded set is an input. -/
theorem actual_grid_ball_upper {l : ℕ}
    (A : Finset (Fin l → ℝ)) (B : Finset (Fin l → ℤ))
    {mu rho alpha K s : ℝ} (hmu : 0 < mu) (hmurho : mu ≤ rho) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hAD : ADBounds A mu K s) (hglobal : (A.card:ℝ) ≤ K*mu^(-s))
    (hnear : ∀k∈B, ∃a∈A, dist (center rho k) a ≤ alpha*rho)
    (x : Fin l → ℝ) (r : ℝ) (hrhor : rho ≤ r) (hr1 : r ≤ 1) :
    ((carrierBall (B.image (center rho)) x r).card:ℝ) ≤
      (((4*⌈alpha⌉₊+5)^l:ℕ):ℝ)*K^2*(2*((⌈alpha⌉₊:ℝ)+2))^s*(r/rho)^s := by
  classical
  have hrho : 0 < rho := hmu.trans_le hmurho
  let witness : (Fin l → ℤ) → (Fin l → ℝ) :=
    fun k => if hk : k∈B then Classical.choose (hnear k hk) else 0
  have hmem : ∀k∈B, witness k∈A := by
    intro k hk
    dsimp [witness]
    rw [dif_pos hk]
    exact (Classical.choose_spec (hnear k hk)).1
  have hclose : ∀k∈B, dist (center rho k) (witness k) ≤ (⌈alpha⌉₊:ℝ)*rho := by
    intro k hk
    dsimp [witness]
    rw [dif_pos hk]
    exact (Classical.choose_spec (hnear k hk)).2.trans
      (mul_le_mul_of_nonneg_right (Nat.le_ceil alpha) hrho.le)
  rw [realized_ball_card B hrho x r]
  exact grid_ball_upper_of_witnesses A B witness ⌈alpha⌉₊ hmu hmurho hK hs hAD hglobal hmem hclose
    x r hrhor hr1

end NativeRecodedGridUpper
