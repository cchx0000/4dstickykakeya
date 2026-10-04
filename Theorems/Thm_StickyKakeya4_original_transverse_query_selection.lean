import Theorems.Thm_StickyKakeya4_original_triple_query_counts
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
open Classical
open scoped BigOperators

namespace OriginalTransverseQuerySelection
open OriginalTripleQueryCounts
variable {X : Type*} [DecidableEq X]

def pairWeight (P : Finset X) (C : Finset ℝ) (Q : ℝ → Finset X) (a b : ℝ) : ℝ :=
  ∑ c ∈ C, ((tripleQuery P Q a b c).card : ℝ)

lemma triple_query_card_le (P : Finset X) (Q : ℝ → Finset X) (a b c : ℝ) :
    ((tripleQuery P Q a b c).card : ℝ) ≤ P.card := by
  exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

lemma pair_weight_upper (P : Finset X) (C : Finset ℝ) (Q : ℝ → Finset X) (a b : ℝ) :
    pairWeight P C Q a b ≤ (C.card : ℝ)*P.card := by
  calc
    _ ≤ ∑ _c ∈ C, (P.card : ℝ) := Finset.sum_le_sum (fun c _hc => triple_query_card_le P Q a b c)
    _ = _ := by simp

/-- The native short-interval count bounds all close first-two-slope triples. -/
theorem close_pair_weight_bound (P : Finset X) (C : Finset ℝ) (Q : ℝ → Finset X)
    {h kappa : ℝ}
    (hclose : ∀ a ∈ C, ((C.filter (fun b => |a-b|<h)).card : ℝ) ≤ kappa*C.card) :
    (∑ a ∈ C, ∑ b ∈ C.filter (fun b => |a-b|<h), pairWeight P C Q a b) ≤
      kappa*(C.card : ℝ)^3*P.card := by
  have hrow : ∀ a ∈ C,
      (∑ b ∈ C.filter (fun b => |a-b|<h), pairWeight P C Q a b) ≤
        kappa*(C.card : ℝ)^2*P.card := by
    intro a ha
    calc
      _ ≤ ∑ _b ∈ C.filter (fun b => |a-b|<h), (C.card : ℝ)*P.card :=
        Finset.sum_le_sum (fun b _hb => pair_weight_upper P C Q a b)
      _ = ((C.filter (fun b => |a-b|<h)).card : ℝ)*(C.card : ℝ)*P.card := by
        simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ (kappa*C.card)*(C.card : ℝ)*P.card := by
        gcongr
        exact hclose a ha
      _ = _ := by ring
  calc
    _ ≤ ∑ _a ∈ C, kappa*(C.card : ℝ)^2*P.card := Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- Choose two transverse original slopes using the cubic original incidence
count, keeping substantial total mass for the third original slope. -/
theorem exists_transverse_pair_with_common_mass
    (P : Finset X) (C : Finset ℝ) (Q : ℝ → Finset X) {q h : ℝ}
    (hP : P.Nonempty) (hC : C.Nonempty) (hq : 0 < q)
    (hQ : ∀ c ∈ C, Q c ⊆ P) (hmass : ∀ c ∈ C, q*(P.card : ℝ) ≤ (Q c).card)
    (hclose : ∀ a ∈ C, ((C.filter (fun b => |a-b|<h)).card : ℝ) ≤ (q^3/2)*C.card) :
    ∃ a ∈ C, ∃ b ∈ C, h ≤ |a-b| ∧ (q^3/2)*(C.card : ℝ)*P.card ≤ pairWeight P C Q a b := by
  have hcube := original_query_cubic_mass P C Q hP hq.le hQ hmass
  have hnear := close_pair_weight_bound P C Q hclose
  have hsplitrow (a : ℝ) : (∑ b ∈ C, pairWeight P C Q a b)=
      (∑ b ∈ C.filter (fun b => |a-b|<h), pairWeight P C Q a b)+
      ∑ b ∈ C, (if h ≤ |a-b| then pairWeight P C Q a b else 0) := by
    rw [Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hab : h ≤ |a-b|
    · simp [hab,not_lt.mpr hab]
    · simp [hab,lt_of_not_ge hab]
  have hsplit : (∑ a ∈ C, ∑ b ∈ C, ∑ c ∈ C, ((tripleQuery P Q a b c).card : ℝ))=
      (∑ a ∈ C, ∑ b ∈ C.filter (fun b => |a-b|<h), pairWeight P C Q a b)+
      ∑ a ∈ C, ∑ b ∈ C, (if h ≤ |a-b| then pairWeight P C Q a b else 0) := by
    change (∑ a ∈ C, ∑ b ∈ C, pairWeight P C Q a b)=_
    simp_rw [hsplitrow]
    exact Finset.sum_add_distrib
  have hfar : (q^3/2)*(C.card : ℝ)^3*P.card ≤
      ∑ a ∈ C, ∑ b ∈ C, (if h ≤ |a-b| then pairWeight P C Q a b else 0) := by
    linarith only [hcube,hnear,hsplit]
  have havg : (∑ _a ∈ C, ∑ _b ∈ C, (q^3/2)*(C.card : ℝ)*P.card) ≤
      ∑ a ∈ C, ∑ b ∈ C, (if h ≤ |a-b| then pairWeight P C Q a b else 0) := by
    calc
      _ = (q^3/2)*(C.card : ℝ)^3*P.card := by
        simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := hfar
  obtain ⟨a,ha,hwa⟩ := Finset.exists_le_of_sum_le hC havg
  obtain ⟨b,hb,hwb⟩ := Finset.exists_le_of_sum_le hC hwa
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hpos : 0 < (q^3/2)*(C.card : ℝ)*P.card := by positivity
  have hab : h ≤ |a-b| := by
    by_contra hn
    rw [if_neg hn] at hwb
    linarith
  exact ⟨a,ha,b,hb,hab,by simpa only [if_pos hab] using hwb⟩

lemma triple_query_eq_inter (P : Finset X) (Q : ℝ → Finset X) (a b c : ℝ)
    (ha : Q a ⊆ P) : tripleQuery P Q a b c=(Q a ∩ Q b) ∩ Q c := by
  ext p
  simp only [tripleQuery,Finset.mem_filter,Finset.mem_inter]
  exact ⟨fun hp => ⟨⟨hp.2.1,hp.2.2.1⟩,hp.2.2.2⟩,
    fun hp => ⟨ha hp.1.1,hp.1.1,hp.1.2,hp.2⟩⟩

/-- The common carrier and every retained query are literal original
intersections. No arbitrary pairwise-overlap hypothesis is used. -/
theorem exists_original_transverse_common_queries
    (P : Finset X) (C : Finset ℝ) (Q : ℝ → Finset X) {q h : ℝ}
    (hP : P.Nonempty) (hC : C.Nonempty) (hq : 0 < q)
    (hQ : ∀ c ∈ C, Q c ⊆ P) (hmass : ∀ c ∈ C, q*(P.card : ℝ) ≤ (Q c).card)
    (hclose : ∀ a ∈ C, ((C.filter (fun b => |a-b|<h)).card : ℝ) ≤ (q^3/2)*C.card) :
    ∃ a ∈ C, ∃ b ∈ C, h ≤ |a-b| ∧
      ∃ C' : Finset ℝ, C' ⊆ C ∧ (q^3/4)*(C.card : ℝ) ≤ C'.card ∧
        (Q a ∩ Q b) ⊆ P ∧ (q^3/4)*(P.card : ℝ) ≤ (Q a ∩ Q b).card ∧
        ∀ c ∈ C', (q^3/4)*(P.card : ℝ) ≤ ((Q a ∩ Q b) ∩ Q c).card := by
  obtain ⟨a,ha,b,hb,hab,hweight⟩ :=
    exists_transverse_pair_with_common_mass P C Q hP hC hq hQ hmass hclose
  let C' := C.filter (fun c => (q^3/4)*(P.card : ℝ) ≤ (tripleQuery P Q a b c).card)
  have hC'sub : C' ⊆ C := Finset.filter_subset _ _
  have hterm : ∀ c ∈ C, ((tripleQuery P Q a b c).card : ℝ) ≤
      (if c ∈ C' then (P.card : ℝ) else 0)+(q^3/4)*P.card := by
    intro c hc
    by_cases hrich : c ∈ C'
    · rw [if_pos hrich]
      have hu := triple_query_card_le P Q a b c
      have hn : 0 ≤ (q^3/4)*(P.card : ℝ) := by positivity
      linarith
    · rw [if_neg hrich,zero_add]
      exact le_of_lt (lt_of_not_ge (fun h => hrich (Finset.mem_filter.mpr ⟨hc,h⟩)))
  have hfilter : C.filter (fun c => c ∈ C')=C' := by
    ext c
    exact ⟨fun hc => (Finset.mem_filter.mp hc).2,
      fun hc => Finset.mem_filter.mpr ⟨hC'sub hc,hc⟩⟩
  have hu : pairWeight P C Q a b ≤ (C'.card : ℝ)*P.card+(q^3/4)*(P.card : ℝ)*C.card := by
    calc
      _ ≤ ∑ c ∈ C, ((if c ∈ C' then (P.card : ℝ) else 0)+(q^3/4)*P.card) :=
        Finset.sum_le_sum hterm
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter,hfilter]
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hC'mass : (q^3/4)*(C.card : ℝ) ≤ C'.card := by
    apply (mul_le_mul_iff_left₀ hPpos).mp
    nlinarith only [hweight,hu]
  have hC'pos : (0 : ℝ) < C'.card := (by positivity : 0 < (q^3/4)*(C.card : ℝ)).trans_le hC'mass
  have hC'non : C'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hC'pos)
  have hqueries : ∀ c ∈ C', (q^3/4)*(P.card : ℝ) ≤ ((Q a ∩ Q b) ∩ Q c).card := by
    intro c hc
    rw [← triple_query_eq_inter P Q a b c (hQ a ha)]
    exact (Finset.mem_filter.mp hc).2
  obtain ⟨c,hc⟩ := hC'non
  have hcarrier := (hqueries c hc).trans
    (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left))
  exact ⟨a,ha,b,hb,hab,C',hC'sub,hC'mass,
    (Finset.inter_subset_left.trans (hQ a ha)),hcarrier,hqueries⟩

end OriginalTransverseQuerySelection
