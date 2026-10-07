import Theorems.Thm_StickyKakeya4_weighted_rich_directional_layers

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeSimultaneousWeightedGrainCore
open Classical Finset RichDirectionalLayers WeightedRichDirectionalLayers
open scoped BigOperators

/-- Original occupied classes pay at most one deficient-fiber deletion each. -/
def classBudget {α : Type*} {J : ℕ} {β : Fin J → Type*}
    (A : Finset α) (f : (j : Fin J) → α → β j) (k : Fin J → ℕ) : ℕ :=
  ∑j,(A.image (f j)).card*(k j-1)

/-- Delete one ENTIRE current grain class, preserving all other original labels
and their original weights. A deleted class can never reappear in a subset. -/
def eraseFiber {α β : Type*} (A : Finset α) (f : α → β) (c : β) : Finset α :=
  A.filter (fun x => f x≠c)

lemma eraseFiber_subset {α β : Type*} (A : Finset α) (f : α → β) (c : β) :
    eraseFiber A f c ⊆ A := filter_subset _ _

lemma eraseFiber_mass {α β : Type*} (A : Finset α) (f : α → β) (w : α → ℕ) (c : β) :
    mass A w=mass (eraseFiber A f c) w+mass (classFiber A f c) w := by
  simpa only [mass,eraseFiber,classFiber,Nat.add_comm] using
    (sum_filter_add_sum_filter_not A (fun x => f x=c) w).symm

/-- The deleted class disappears in its own map, and no other map gains a
class. This is the once-per-original-(level,class) charging inequality. -/
theorem eraseFiber_budget {α : Type*} {J : ℕ} {β : Fin J → Type*}
    (A : Finset α) (f : (j : Fin J) → α → β j) (k : Fin J → ℕ)
    (j : Fin J) (x : α) (hx : x∈A) :
    classBudget (eraseFiber A (f j) (f j x)) f k+(k j-1) ≤ classBudget A f k := by
  let B := eraseFiber A (f j) (f j x)
  have hBA : B⊆A := eraseFiber_subset A (f j) (f j x)
  have hcard (i : Fin J) : (B.image (f i)).card ≤ (A.image (f i)).card :=
    card_le_card (image_subset_image hBA)
  have hstrict : (B.image (f j)).card+1 ≤ (A.image (f j)).card := by
    apply Nat.succ_le_of_lt
    apply card_lt_card
    apply ssubset_iff_subset_ne.mpr
    refine ⟨image_subset_image hBA,?_⟩
    intro he
    have hcx : f j x∈B.image (f j) := by rw [he]; exact mem_image_of_mem (f j) hx
    obtain ⟨y,hy,hyx⟩ := mem_image.mp hcx
    exact (mem_filter.mp hy).2 hyx
  have hterm (i : Fin J) :
      (B.image (f i)).card*(k i-1)+(if i=j then k j-1 else 0) ≤
        (A.image (f i)).card*(k i-1) := by
    by_cases hi : i=j
    · subst i
      simpa only [ite_true,Nat.add_mul,one_mul] using Nat.mul_le_mul_right (k j-1) hstrict
    · simp only [if_neg hi,add_zero]
      exact Nat.mul_le_mul_right (k i-1) (hcard i)
  have hs := sum_le_sum (fun i (_hi : i∈(univ : Finset (Fin J))) => hterm i)
  simpa [classBudget,sum_add_distrib,B] using hs

/-- Simultaneous final density for every fixed map, obtained by terminating
whole-fiber deletion. All masses use the unchanged original integer weights.
Unlike a one-pass restriction, density is checked on the FINAL common core. -/
theorem exists_simultaneous_dense_core {α : Type*} {J : ℕ} {β : Fin J → Type*}
    (A : Finset α) (f : (j : Fin J) → α → β j) (w : α → ℕ) (k : Fin J → ℕ) :
    ∃K⊆A, (∀j,∀c∈K.image (f j), k j ≤ mass (classFiber K (f j) c) w) ∧
      mass A w ≤ mass K w+classBudget A f k := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hgood : ∀j,∀c∈A.image (f j), k j ≤ mass (classFiber A (f j) c) w
    · exact ⟨A,Subset.refl _,hgood,Nat.le_add_right _ _⟩
    · push Not at hgood
      obtain ⟨j,c,hc,hbad⟩ := hgood
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hc
      let B := eraseFiber A (f j) (f j x)
      have hBA : B⊂A := by
        apply filter_ssubset.mpr
        exact ⟨x,hx,by simp⟩
      obtain ⟨K,hKB,hmin,hmass⟩ := ih B hBA
      have hcost := eraseFiber_budget A f k j x hx
      have hsplit := eraseFiber_mass A (f j) w (f j x)
      have hsmall : mass (classFiber A (f j) (f j x)) w ≤ k j-1 := by omega
      refine ⟨K,hKB.trans (eraseFiber_subset A (f j) (f j x)),hmin,?_⟩
      change mass B w ≤ mass K w+classBudget B f k at hmass
      change classBudget B f k+(k j-1) ≤ classBudget A f k at hcost
      change mass A w=mass B w+mass (classFiber A (f j) (f j x)) w at hsplit
      omega

/-- The mass inequality is an actual bound for the discarded ORIGINAL labels. -/
theorem removed_mass_le {α : Type*} (A K : Finset α) (w : α → ℕ) (budget : ℕ)
    (hKA : K⊆A) (hbound : mass A w ≤ mass K w+budget) :
    mass (A\K) w ≤ budget := by
  have hsplit := sum_sdiff hKA (f:=w)
  change mass (A\K) w+mass K w=mass A w at hsplit
  omega

/-- A source-derived class-count budget gives a nonempty simultaneous core
with at least half the original mass. No final dense core is an input. -/
theorem exists_simultaneous_dense_core_half {α : Type*} {J : ℕ} {β : Fin J → Type*}
    (A : Finset α) (f : (j : Fin J) → α → β j) (w : α → ℕ) (k : Fin J → ℕ)
    (hpos : 0 < mass A w) (hbudget : 2*classBudget A f k ≤ mass A w) :
    ∃K⊆A, K.Nonempty ∧ mass A w ≤ 2*mass K w ∧
      mass (A\K) w ≤ classBudget A f k ∧
      (∀j,∀c∈K.image (f j), k j ≤ mass (classFiber K (f j) c) w) := by
  obtain ⟨K,hKA,hmin,hmass⟩ := exists_simultaneous_dense_core A f w k
  have hhalf : mass A w ≤ 2*mass K w := by omega
  have hKpos : 0 < mass K w := by omega
  have hKne : K.Nonempty := by
    by_contra hne
    have hz : mass K w=0 := by rw [not_nonempty_iff_eq_empty.mp hne]; simp [mass]
    omega
  exact ⟨K,hKA,hKne,hhalf,removed_mass_le A K w _ hKA hmass,hmin⟩

end NativeSimultaneousWeightedGrainCore
