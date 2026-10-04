import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalTripleQueryCounts
variable {X Y : Type*} [DecidableEq X]

def query (P : Finset X) (Q : Y → Finset X) (c : Y) : Finset X :=
  P.filter (fun p => p ∈ Q c)
def tripleQuery (P : Finset X) (Q : Y → Finset X) (a b c : Y) : Finset X :=
  P.filter (fun p => p ∈ Q a ∧ p ∈ Q b ∧ p ∈ Q c)
def degree (C : Finset Y) (Q : Y → Finset X) (p : X) : ℕ :=
  (C.filter (fun c => p ∈ Q c)).card

lemma query_eq (P : Finset X) (Q : Y → Finset X) {c : Y} (hQ : Q c ⊆ P) :
    query P Q c=Q c := by
  ext p
  exact ⟨fun hp => (Finset.mem_filter.mp hp).2,
    fun hp => Finset.mem_filter.mpr ⟨hQ hp,hp⟩⟩

lemma sum_queries_eq_degrees (P : Finset X) (C : Finset Y) (Q : Y → Finset X) :
    (∑ c ∈ C, ((query P Q c).card : ℝ)) = ∑ p ∈ P, (degree C Q p : ℝ) := by
  simp only [query,degree,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  exact Finset.sum_comm

lemma degree_cube (C : Finset Y) (Q : Y → Finset X) (p : X) :
    (degree C Q p : ℝ)^3 =
      ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, (if p∈Q a ∧ p∈Q b ∧ p∈Q c then (1:ℝ) else 0) := by
  have he : (degree C Q p : ℝ)=∑ c ∈ C, (if p∈Q c then (1:ℝ) else 0) := by
    simp only [degree,Finset.card_eq_sum_ones,Finset.sum_filter,
      Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [he,show (3:ℕ)=2+1 by norm_num,pow_succ,pow_two]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _hc
  split_ifs <;> simp_all

/-- Count precisely the same original point/slope triples in both orders. -/
theorem sum_triple_queries (P : Finset X) (C : Finset Y) (Q : Y → Finset X) :
    (∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, ((tripleQuery P Q a b c).card : ℝ)) =
      ∑ p ∈ P, (degree C Q p : ℝ)^3 := by
  simp_rw [degree_cube]
  simp only [tripleQuery,Finset.card_eq_sum_ones,Finset.sum_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp_rw [Finset.sum_comm (s:=C) (t:=P)]

/-- The cubic count is obtained from the actual original dense queries and
mathlib's finite power-mean inequality. -/
theorem original_query_cubic_mass (P : Finset X) (C : Finset Y) (Q : Y → Finset X)
    {q : ℝ} (hP : P.Nonempty) (hq : 0 ≤ q)
    (hQ : ∀ c ∈ C, Q c ⊆ P) (hmass : ∀ c ∈ C, q*(P.card : ℝ) ≤ (Q c).card) :
    q^3*(C.card : ℝ)^3*P.card ≤
      ∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, ((tripleQuery P Q a b c).card : ℝ) := by
  have hsum : q*(P.card : ℝ)*C.card ≤ ∑ p ∈ P, (degree C Q p : ℝ) := by
    rw [← sum_queries_eq_degrees]
    calc
      _ = ∑ _c ∈ C, q*(P.card : ℝ) := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun c hc => by rw [query_eq P Q (hQ c hc)]; exact hmass c hc)
  have hp := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg P
    (f:=fun p => (degree C Q p : ℝ)) (p:=3) (by norm_num)
    (fun p _hp => Nat.cast_nonneg (degree C Q p))
  norm_num only [show (3:ℝ)-1=2 by norm_num,Real.rpow_ofNat] at hp
  have hlo := pow_le_pow_left₀ (show 0 ≤ q*(P.card : ℝ)*C.card by positivity) hsum 3
  have hchain := hlo.trans hp
  rw [← sum_triple_queries P C Q] at hchain
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  apply (mul_le_mul_iff_left₀ (show 0 < (P.card : ℝ)^2 by positivity)).mp
  nlinarith only [hchain]

end OriginalTripleQueryCounts
