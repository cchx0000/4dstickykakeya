/- NEW DRAFT, 2026-10-06. UNVERIFIED: no source or imported-axiom check.
Only the restored 999-module baseline was read. No original/raw/translated
height identification is assumed: height is an explicit real coordinate. -/
import Theorems.Thm_StickyKakeya4_separated_alignment_patches
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section

namespace NativeMatrixHeightWholePoint
open Classical Finset SeparatedAlignmentPatches
open scoped BigOperators

def mass {A : Type*} (S : Finset A) (w : A → ℕ) : ℕ := ∑ x∈S,w x

def heightCell (rho shift h : ℝ) : ℤ := ⌊(h-shift)/rho⌋

def modulus (L : ℝ) : ℕ := ⌈L⌉₊+2

lemma modulus_pos (L : ℝ) : 0 < modulus L := by unfold modulus; omega

lemma same_height_cell_close {rho shift h k : ℝ} (hrho : 0 < rho)
    (heq : heightCell rho shift h=heightCell rho shift k) : |h-k| < rho := by
  have hh0 := (le_div_iff₀ hrho).mp (Int.floor_le ((h-shift)/rho))
  have hh1 := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one ((h-shift)/rho))
  have hk0 := (le_div_iff₀ hrho).mp (Int.floor_le ((k-shift)/rho))
  have hk1 := (div_lt_iff₀ hrho).mp (Int.lt_floor_add_one ((k-shift)/rho))
  change ⌊(h-shift)/rho⌋=⌊(k-shift)/rho⌋ at heq
  rw [heq] at hh0 hh1
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

/-- Select a maximum ORIGINAL-weight color separately in every occupied
height cell. Empty sets and zero weights require no additional assumption. -/
theorem select_color_per_cell {A C B : Type*} [DecidableEq C]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (S : Finset A) (w : A → ℕ) (hcell : A → C) (paint : A → B) :
    ∃chi : C → B,let T := S.filter (fun x => paint x=chi (hcell x))
      T⊆S ∧
      (∀c,mass (S.filter (fun x => hcell x=c)) w ≤
        Fintype.card B*mass (T.filter (fun x => hcell x=c)) w) ∧
      mass S w ≤ Fintype.card B*mass T w ∧
      ∀x∈T,∀y∈T,hcell x=hcell y → paint x=paint y := by
  choose chi hchi using fun c => maximum_weight_color
    (S.filter (fun x => hcell x=c)) w paint
  let T := S.filter (fun x => paint x=chi (hcell x))
  have hTS : T⊆S := filter_subset _ _
  have hlocal (c : C) :
      T.filter (fun x => hcell x=c)=
        (S.filter (fun x => hcell x=c)).filter (fun x => paint x=chi c) := by
    ext x
    simp only [T,mem_filter]
    constructor
    · rintro ⟨⟨hx,hcolor⟩,hc⟩
      exact ⟨⟨hx,hc⟩,by simpa only [hc] using hcolor⟩
    · rintro ⟨⟨hx,hc⟩,hcolor⟩
      exact ⟨⟨hx,by simpa only [hc] using hcolor⟩,hc⟩
  have hret (c : C) : mass (S.filter (fun x => hcell x=c)) w ≤
      Fintype.card B*mass (T.filter (fun x => hcell x=c)) w := by
    rw [hlocal]
    exact hchi c
  have hsumS : ∑ c∈S.image hcell,mass (S.filter (fun x => hcell x=c)) w=mass S w :=
    sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem hcell hx) w
  have hsumT : ∑ c∈S.image hcell,mass (T.filter (fun x => hcell x=c)) w=mass T w :=
    sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem hcell (hTS hx)) w
  refine ⟨chi,hTS,hret,?_,?_⟩
  · calc
      mass S w = ∑ c∈S.image hcell,mass (S.filter (fun x => hcell x=c)) w := hsumS.symm
      _ ≤ ∑ c∈S.image hcell,Fintype.card B*mass (T.filter (fun x => hcell x=c)) w :=
        sum_le_sum (fun c _ => hret c)
      _ = Fintype.card B*mass T w := by rw [←mul_sum,hsumT]
  · intro x hx y hy heq
    exact (mem_filter.mp hx).2.trans (by rw [heq]; exact (mem_filter.mp hy).2.symm)

/-- The two matrix entries are represented by the sup-metric vector F.
No point, height, or matrix value is moved. Residue colors form a fixed
palette of size (ceil(L)+2)^2; equal colors in one height cell force equal
actual quantized matrix entries. -/
theorem select_one_height_scale {A : Type*}
    (S : Finset A) (w : A → ℕ) (height : A → ℝ) (F : A → Fin 2 → ℝ)
    (L rho shift : ℝ) (hL : 0 ≤ L) (hrho : 0 < rho)
    (hLip : ∀x∈S,∀y∈S,dist (F x) (F y) ≤ L*|height x-height y|) :
    ∃T⊆S,mass S w ≤ (modulus L)^2*mass T w ∧
      ∀x∈T,∀y∈T,heightCell rho shift (height x)=heightCell rho shift (height y) →
        dist (F x) (F y) < rho := by
  let M := modulus L
  have hM : 0 < M := modulus_pos L
  letI : Nonempty (Fin 2 → Fin M) := ⟨fun _ => ⟨0,hM⟩⟩
  let paint := fun x => color M hM (cell rho (F x))
  let hc := fun x => heightCell rho shift (height x)
  obtain ⟨chi,hTS,_hlocal,hret,hcolor⟩ := select_color_per_cell S w hc paint
  let T := S.filter (fun x => paint x=chi (hc x))
  refine ⟨T,hTS,?_,?_⟩
  · simpa only [Fintype.card_fun,Fintype.card_fin] using hret
  · intro x hx y hy heq
    have hh := same_height_cell_close hrho heq
    have hclose : dist (F x) (F y) < (L+1)*rho := by
      have hl := hLip x (hTS hx) y (hTS hy)
      have hm := mul_le_mul_of_nonneg_left hh.le hL
      nlinarith only [hl,hm,hrho]
    have hgap : (L+1)*rho ≤ ((M:ℝ)-1)*rho := by
      apply mul_le_mul_of_nonneg_right _ hrho.le
      have hceil := Nat.le_ceil L
      dsimp only [M,modulus]
      push_cast
      linarith
    have he := close_same_color_cell_eq rho ((L+1)*rho) hrho M hM hgap (F x) (F y)
      (hcolor x hx y hy heq) hclose
    exact same_cell_dist_lt rho hrho (F x) (F y) he

/-- Later selections preserve every earlier matrix coherence conclusion.
The same original natural weights are used in all rounds. -/
theorem select_height_menu {A I : Type*} [DecidableEq I]
    (menu : Finset I) (S : Finset A) (w : A → ℕ)
    (height : A → ℝ) (F : A → Fin 2 → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (rho shift : I → ℝ) (hrho : ∀i,0 < rho i)
    (hLip : ∀x∈S,∀y∈S,dist (F x) (F y) ≤ L*|height x-height y|) :
    ∃T⊆S,mass S w ≤ (modulus L)^(2*menu.card)*mass T w ∧
      ∀i∈menu,∀x∈T,∀y∈T,
        heightCell (rho i) (shift i) (height x)=heightCell (rho i) (shift i) (height y) →
          dist (F x) (F y) < rho i := by
  induction menu using Finset.induction_on generalizing S with
  | empty =>
      refine ⟨S,Subset.refl _,?_,?_⟩
      · simp
      · intro i hi
        exact False.elim (not_mem_empty i hi)
  | @insert i menu hi ih =>
      obtain ⟨S1,hS1,hret1,hcoh1⟩ := select_one_height_scale S w height F L
        (rho i) (shift i) hL (hrho i) hLip
      obtain ⟨T,hT,hret,hcoh⟩ := ih S1 (fun x hx y hy => hLip x (hS1 hx) y (hS1 hy))
      refine ⟨T,hT.trans hS1,?_,?_⟩
      · calc
          mass S w ≤ (modulus L)^2*mass S1 w := hret1
          _ ≤ (modulus L)^2*((modulus L)^(2*menu.card)*mass T w) := Nat.mul_le_mul_left _ hret
          _ = (modulus L)^(2*(insert i menu).card)*mass T w := by
            rw [card_insert_of_notMem hi,←mul_assoc,←pow_add]
            congr 2
            omega
      · intro j hj x hx y hy heq
        rcases mem_insert.mp hj with rfl | hj
        · exact hcoh1 x (hT hx) y (hT hy) heq
        · exact hcoh j hj x hx y hy heq

lemma modulus_cost (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ((modulus L)^(2*K):ℝ) ≤ (9*(1+L)^2)^K := by
  have hceil := Nat.ceil_lt_add_one hL
  have hM : (modulus L:ℝ) ≤ 3*(1+L) := by
    dsimp [modulus]
    push_cast
    linarith
  have hM0 : (0:ℝ) ≤ modulus L := Nat.cast_nonneg _
  have hpow : (modulus L:ℝ)^2 ≤ 9*(1+L)^2 := by nlinarith
  rw [pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) hpow K

/-- Explicit final-base specialization. The height coordinate is supplied
literally by the source caller; no equality with an old grid is assumed. -/
theorem select_above_base {A : Type*} (K : ℕ) (S : Finset A) (w : A → ℕ)
    (height : A → ℝ) (F : A → Fin 2 → ℝ) (L d : ℝ) (hL : 0 ≤ L) (hd : 0 < d)
    (rho shift : Fin K → ℝ) (hbase : ∀i,d ≤ rho i)
    (hLip : ∀x∈S,∀y∈S,dist (F x) (F y) ≤ L*|height x-height y|) :
    ∃T⊆S,mass S w ≤ (modulus L)^(2*K)*mass T w ∧
      (mass S w:ℝ) ≤ (9*(1+L)^2)^K*mass T w ∧
      ∀i,∀x∈T,∀y∈T,
        heightCell (rho i) (shift i) (height x)=heightCell (rho i) (shift i) (height y) →
          dist (F x) (F y) < rho i := by
  obtain ⟨T,hTS,hret,hcoh⟩ := select_height_menu univ S w height F L hL rho shift
    (fun i => hd.trans_le (hbase i)) hLip
  have hret' : mass S w ≤ (modulus L)^(2*K)*mass T w := by simpa using hret
  refine ⟨T,hTS,hret',?_,fun i => hcoh i (mem_univ i)⟩
  calc
    (mass S w:ℝ) ≤ ((modulus L)^(2*K):ℝ)*mass T w := by exact_mod_cast hret'
    _ ≤ (9*(1+L)^2)^K*mass T w :=
      mul_le_mul_of_nonneg_right (modulus_cost L hL K) (Nat.cast_nonneg _)

def edgeLift {E P : Type*} [DecidableEq P]
    (A : Finset E) (point : E → P) (S : Finset P) : Finset E :=
  A.filter (fun x => point x∈S)

lemma edgeLift_fiber {E P : Type*} [DecidableEq P]
    (A : Finset E) (point : E → P) (S : Finset P) (p : P) (hp : p∈S) :
    (edgeLift A point S).filter (fun x => point x=p)=A.filter (fun x => point x=p) := by
  ext x
  simp only [edgeLift,mem_filter]
  constructor
  · exact fun hx => ⟨hx.1.1,hx.2⟩
  · rintro ⟨hx,heq⟩
    exact ⟨⟨hx,heq ▸ hp⟩,heq⟩

lemma edgeLift_card {E P : Type*} [DecidableEq P]
    (A : Finset E) (point : E → P) (S : Finset P) :
    (edgeLift A point S).card=mass S (fun p => (A.filter (fun x => point x=p)).card) := by
  exact (sum_card_fiberwise_eq_card_filter A S point).symm

/-- Choose original point labels with their original incidence-fiber weights,
then keep every old edge at each surviving point. No extra edge core is used. -/
theorem select_original_edge_menu {E P : Type*} [DecidableEq P]
    (A : Finset E) (point : E → P) (K : ℕ)
    (height : P → ℝ) (F : P → Fin 2 → ℝ) (L d : ℝ) (hL : 0 ≤ L) (hd : 0 < d)
    (rho shift : Fin K → ℝ) (hbase : ∀i,d ≤ rho i)
    (hLip : ∀x∈A.image point,∀y∈A.image point,
      dist (F x) (F y) ≤ L*|height x-height y|) :
    ∃S⊆A.image point,let T := edgeLift A point S
      T⊆A ∧ A.card ≤ (modulus L)^(2*K)*T.card ∧
      (A.card:ℝ) ≤ (9*(1+L)^2)^K*T.card ∧
      (∀p∈S,T.filter (fun x => point x=p)=A.filter (fun x => point x=p)) ∧
      ∀i,∀x∈T,∀y∈T,
        heightCell (rho i) (shift i) (height (point x))=
          heightCell (rho i) (shift i) (height (point y)) →
        dist (F (point x)) (F (point y)) < rho i := by
  let w := fun p => (A.filter (fun x => point x=p)).card
  have hmass : mass (A.image point) w=A.card := (card_eq_sum_card_image point A).symm
  obtain ⟨S,hS,hret,hretR,hcoh⟩ := select_above_base K (A.image point) w height F L d hL hd
    rho shift hbase hLip
  rw [hmass,←edgeLift_card A point S] at hret hretR
  refine ⟨S,hS,filter_subset _ _,hret,hretR,fun p hp => edgeLift_fiber A point S p hp,?_⟩
  intro i x hx y hy heq
  exact hcoh i (point x) (mem_filter.mp hx).2 (point y) (mem_filter.mp hy).2 heq

end NativeMatrixHeightWholePoint
