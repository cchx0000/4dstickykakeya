import Theorems.Thm_StickyKakeya4_finite_coarse_y_threshold_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace CanonicalGridRecoding
open Classical Finset
open scoped BigOperators

abbrev Grid (n : ℕ) := Fin n → ℤ
abbrev Label (H : Type*) (k l : ℕ) := H × (Grid k × Grid l)

variable {k l : ℕ}

/-- All coordinates are the canonical OLD fine-cell centers. -/
def center (mu : ℝ) (u : Grid k) : Fin k → ℝ :=
  fun j => mu*((u j:ℝ)+1/2)

def coarseGrid (mu : ℝ) (R : ℕ) (u : Grid k) : Grid k :=
  fun j => ⌊center mu u j/(mu*(R:ℝ))⌋

/-- The recoded normal coordinate uses the old center, not a varying
actual point inside its fine label. -/
def recodedY (mu : ℝ) (R : ℕ) (A : Matrix (Fin l) (Fin k) ℝ)
    (u : Grid k) (v : Grid l) : Grid l :=
  fun i => ⌊(center mu v i+∑j : Fin k,A i j*center mu u j)/(mu*(R:ℝ))⌋

/-- Exact even for negative original grid indices. -/
theorem coarseGrid_eq_ediv (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (u : Grid k) :
    coarseGrid mu R u=fun j => u j/(R:ℤ) := by
  funext j
  have hratio : center mu u j/(mu*(R:ℝ))=((u j:ℝ)+1/2)/(R:ℝ) := by
    dsimp [center]
    exact mul_div_mul_left _ _ hmu.ne'
  change ⌊center mu u j/(mu*(R:ℝ))⌋=_
  rw [hratio,Int.floor_div_natCast,Int.floor_intCast_add]
  norm_num

/-- The full preimage of one coarse X bin has exactly R choices per
coordinate. Its construction includes negative coarse bins. -/
def preimageBox (R : ℕ) (q : Grid k) : Finset (Grid k) :=
  Fintype.piFinset (fun j => Icc ((R:ℤ)*q j) ((R:ℤ)*q j+R-1))

theorem preimageBox_card (R : ℕ) (q : Grid k) : (preimageBox R q).card=R^k := by
  have hc (j : Fin k) : (Icc ((R:ℤ)*q j) ((R:ℤ)*q j+R-1)).card=R := by
    rw [Int.card_Icc]
    omega
  simp [preimageBox,Fintype.card_piFinset,hc]

theorem mem_preimageBox (R : ℕ) (hR : 0 < R) (u q : Grid k)
    (he : ∀j,u j/(R:ℤ)=q j) : u∈preimageBox R q := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hRz : (0:ℤ) < R := by exact_mod_cast hR
  have hlo := Int.emod_nonneg (u j) (ne_of_gt hRz)
  have hhi := Int.emod_lt_of_pos (u j) hRz
  have hd := Int.emod_add_mul_ediv (u j) (R:ℤ)
  rw [he j] at hd
  exact mem_Icc.mpr (by constructor <;> omega)

theorem coarseGrid_fiber_card (S : Finset (Grid k)) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R) (q : Grid k) :
    (S.filter (fun u => coarseGrid mu R u=q)).card≤R^k := by
  calc
    _ ≤ (preimageBox R q).card := by
      apply card_le_card
      intro u hu
      have he := (mem_filter.mp hu).2
      rw [coarseGrid_eq_ediv mu R hmu u] at he
      exact mem_preimageBox R hR u q (congrFun he)
    _ = _ := preimageBox_card R q

/-- Entry control and the actual center box give the complete recoding
error; no displacement or branch-capacity hypothesis is introduced. -/
theorem matrix_displacement (rho : ℝ) (hrho : 0≤rho)
    (A : Matrix (Fin l) (Fin k) ℝ) (x : Fin k → ℝ)
    (hA : ∀i j,|A i j|≤rho) (hx : ∀j,|x j|≤1) (i : Fin l) :
    |∑j : Fin k,A i j*x j|≤(k:ℝ)*rho := by
  calc
    _ ≤ ∑j : Fin k,|A i j*x j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑_j : Fin k,rho := by
      apply sum_le_sum
      intro j _hj
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul (hA i j) (hx j) (abs_nonneg (x j)) hrho
    _ = _ := by simp

lemma floor_displacement (rho a d : ℝ) (hrho : 0 < rho)
    (herror : |d|≤(k:ℝ)*rho) :
    ⌊a/rho⌋-((k:ℤ)+1)≤⌊(a+d)/rho⌋ ∧
      ⌊(a+d)/rho⌋≤⌊a/rho⌋+((k:ℤ)+1) := by
  have hd : |d/rho|≤(k:ℝ) := by
    rw [abs_div,abs_of_pos hrho]
    exact (div_le_iff₀ hrho).2 herror
  obtain ⟨hdlo,hdhi⟩ := abs_le.mp hd
  have hlo := Int.floor_mono (show a/rho-(k:ℝ)≤(a+d)/rho by rw [add_div]; linarith)
  have hhi := Int.floor_mono (show (a+d)/rho≤a/rho+(k:ℝ) by rw [add_div]; linarith)
  rw [Int.floor_sub_natCast] at hlo
  rw [Int.floor_add_natCast] at hhi
  constructor <;> omega

theorem recodedY_near (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (A : Matrix (Fin l) (Fin k) ℝ) (u : Grid k) (v : Grid l)
    (hA : ∀i j,|A i j|≤mu*(R:ℝ)) (hx : ∀j,|center mu u j|≤1) :
    ∀i,coarseGrid mu R v i-((k:ℤ)+1)≤recodedY mu R A u v i ∧
      recodedY mu R A u v i≤coarseGrid mu R v i+((k:ℤ)+1) := by
  have hrho : 0 < mu*(R:ℝ) := mul_pos hmu (by exact_mod_cast hR)
  intro i
  exact floor_displacement (mu*(R:ℝ)) (center mu v i)
    (∑j : Fin k,A i j*center mu u j) hrho
    (matrix_displacement (mu*(R:ℝ)) hrho.le A (center mu u) hA hx i)

def neighborBox (q : Grid l) : Finset (Grid l) :=
  Fintype.piFinset (fun i => Icc (q i-3) (q i+3))

theorem neighborBox_card (q : Grid l) : (neighborBox q).card=7^l := by
  have hc (i : Fin l) : (Icc (q i-3) (q i+3)).card=7 := by
    rw [Int.card_Icc]
    omega
  simp [neighborBox,Fintype.card_piFinset,hc]

theorem recodedY_mem_neighbors (hk : k≤2) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R) (A : Matrix (Fin l) (Fin k) ℝ)
    (u : Grid k) (v : Grid l) (hA : ∀i j,|A i j|≤mu*(R:ℝ))
    (hx : ∀j,|center mu u j|≤1) :
    recodedY mu R A u v∈neighborBox (coarseGrid mu R v) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := recodedY_near mu R hmu hR A u v hA hx i
  exact mem_Icc.mpr (by constructor <;> omega)

/-- The remaining definitions keep the original fine height and both
old grid indices. Target labels include the actual coarse height. -/
def oldIndex {H : Type*} (z : Label H k l) : H × Grid l := (z.1,z.2.2)

def newX {H : Type*} (mu : ℝ) (R : ℕ) (z : Label H k l) : Grid k :=
  coarseGrid mu R z.2.1

def errorMatrix {H Z : Type*} (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (h : H) : Matrix (Fin l) (Fin k) ℝ := F h-Fcfg (height h)

def newY {H Z : Type*} (mu : ℝ) (R : ℕ) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (z : Label H k l) : Z × Grid l :=
  (height z.1,recodedY mu R (errorMatrix height F Fcfg z.1) z.2.1 z.2.2)

def oldY {H Z : Type*} (mu : ℝ) (R : ℕ) (height : H → Z)
    (b : H × Grid l) : Z × Grid l := (height b.1,coarseGrid mu R b.2)

def Neighbor {Z : Type*} (a b : Z × Grid l) : Prop :=
  a.1=b.1 ∧ ∀i,a.2 i-3≤b.2 i ∧ b.2 i≤a.2 i+3

/-- Capacity is on literal fine labels in ONE old height/Y fiber. -/
theorem old_fiber_capacity {H : Type*} [DecidableEq H]
    (L : Finset (Label H k l)) (mu : ℝ) (R : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (b : H × Grid l) (q : Grid k) :
    ((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).filter
      (fun z => newX mu R z=q)).card≤R^k := by
  calc
    _ ≤ (preimageBox R q).card := by
      apply card_le_card_of_injOn (fun z : Label H k l => z.2.1)
      · intro z hz
        have hq := (mem_filter.mp hz).2
        change coarseGrid mu R z.2.1=q at hq
        rw [coarseGrid_eq_ediv mu R hmu z.2.1] at hq
        exact mem_preimageBox R hR z.2.1 q (congrFun hq)
      · intro z hz w hw he
        have hzold := (mem_filter.mp (mem_filter.mp hz).1).2
        have hwold := (mem_filter.mp (mem_filter.mp hw).1).2
        have hzw : oldIndex z=oldIndex w := hzold.trans hwold.symm
        exact Prod.ext (congrArg (fun b : H × Grid l => b.1) hzw)
          (Prod.ext he (congrArg (fun b : H × Grid l => b.2) hzw))
    _ = _ := preimageBox_card R q

/-- Exact source-facing neighboring relation from the actual matrix
difference, with the coarse-height tag retained. -/
theorem actual_neighbor {H Z : Type*} (hk : k≤2) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (z : Label H k l)
    (hF : ∀i j,|F z.1 i j-Fcfg (height z.1) i j|≤mu*(R:ℝ))
    (hx : ∀j,|center mu z.2.1 j|≤1) :
    Neighbor (oldY mu R height (oldIndex z)) (newY mu R height F Fcfg z) := by
  refine ⟨rfl,?_⟩
  have hn := recodedY_mem_neighbors hk mu R hmu hR (errorMatrix height F Fcfg z.1)
    z.2.1 z.2.2 hF hx
  intro i
  exact mem_Icc.mp ((Fintype.mem_piFinset.mp hn) i)

/-- At most 7^l target labels per old height/Y fiber, derived from
entrywise matrix coherence and the actual canonical center bounds. -/
theorem old_fiber_menu {H Z : Type*} [DecidableEq H] [DecidableEq Z]
    (L : Finset (Label H k l)) (hk : k≤2) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (hF : ∀z∈L,∀i j,|F z.1 i j-Fcfg (height z.1) i j|≤mu*(R:ℝ))
    (hx : ∀z∈L,∀j,|center mu z.2.1 j|≤1) (b : H × Grid l) :
    ((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).image
      (newY mu R height F Fcfg)).card≤7^l := by
  let Q := (neighborBox (coarseGrid mu R b.2)).image (fun q => (height b.1,q))
  have hSub : (FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).image
      (newY mu R height F Fcfg)⊆Q := by
    intro q hq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
    obtain ⟨hzL,hzb⟩ := mem_filter.mp hz
    have hh := congrArg Prod.fst hzb
    have hv := congrArg Prod.snd hzb
    change z.1=b.1 at hh
    change z.2.2=b.2 at hv
    have hn := recodedY_mem_neighbors hk mu R hmu hR (errorMatrix height F Fcfg z.1)
      z.2.1 z.2.2 (hF z hzL) (hx z hzL)
    apply mem_image.mpr
    refine ⟨recodedY mu R (errorMatrix height F Fcfg z.1) z.2.1 z.2.2,?_,?_⟩
    · simpa only [hv] using hn
    · exact Prod.ext (congrArg height hh).symm rfl
  calc
    _ ≤ Q.card := card_le_card hSub
    _ ≤ (neighborBox (coarseGrid mu R b.2)).card := card_image_le
    _ = _ := neighborBox_card _

/-- The concrete constants consumed by threshold_original_edges.
No menu-cardinality or coarse-fiber-capacity certificate is an input. -/
theorem threshold_inputs {H Z : Type*} [DecidableEq H] [DecidableEq Z]
    (L : Finset (Label H k l)) (hk : k≤2) (hl : l≤2) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (hF : ∀z∈L,∀i j,|F z.1 i j-Fcfg (height z.1) i j|≤mu*(R:ℝ))
    (hx : ∀z∈L,∀j,|center mu z.2.1 j|≤1) :
    (∀b∈L.image oldIndex,
      ((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).image
        (newY mu R height F Fcfg)).card≤49) ∧
    (∀b∈L.image oldIndex,∀q : Grid k,
      ((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).filter
        (fun z => newX mu R z=q)).card≤R^k) ∧
    (∀z∈L,Neighbor (oldY mu R height (oldIndex z)) (newY mu R height F Fcfg z)) := by
  refine ⟨?_,?_,?_⟩
  · intro b _hb
    apply (old_fiber_menu L hk mu R hmu hR height F Fcfg hF hx b).trans
    calc
      7^l ≤ 7^2 := Nat.pow_le_pow_right (by omega) hl
      _ = 49 := by norm_num
  · intro b _hb q
    exact old_fiber_capacity L mu R hmu hR b q
  · intro z hz
    exact actual_neighbor hk mu R hmu hR height F Fcfg z (hF z hz) (hx z hz)

/-- Apply the proved threshold cut to the actual recoding, retaining both
neighbor-cover directions. Every old fine-height/Y label has a surviving
nearby target label, and every target label has an actual old witness. -/
theorem threshold_support_cover {H Z : Type*} [DecidableEq H] [DecidableEq Z]
    (L : Finset (Label H k l)) (hk : k≤2) (hl : l≤2) (mu : ℝ) (R : ℕ)
    (hmu : 0 < mu) (hR : 0 < R) (height : H → Z)
    (F : H → Matrix (Fin l) (Fin k) ℝ) (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (hF : ∀z∈L,∀i j,|F z.1 i j-Fcfg (height z.1) i j|≤mu*(R:ℝ))
    (hx : ∀z∈L,∀j,|center mu z.2.1 j|≤1) (theta : ℝ) (htheta : 0≤theta)
    (hBudget : ∀b∈L.image oldIndex,2*(49:ℝ)*((R^k:ℕ):ℝ)*theta≤
      ((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).card:ℝ)) :
    let G := FiniteCoarseYThresholdSelection.keepLabels L oldIndex
      (newY mu R height F Fcfg) (newX mu R) theta
    (∀b∈L.image oldIndex,∃q∈G.image (newY mu R height F Fcfg),
      Neighbor (oldY mu R height b) q) ∧
    (∀q∈G.image (newY mu R height F Fcfg),∃b∈L.image oldIndex,
      Neighbor (oldY mu R height b) q) := by
  obtain ⟨hMenu,hCapacity,hNear⟩ := threshold_inputs L hk hl mu R hmu hR height F Fcfg hF hx
  have hHalf := FiniteCoarseYThresholdSelection.each_old_fiber_half L oldIndex
    (newY mu R height F Fcfg) (newX mu R) 49 (R^k) theta htheta hMenu hCapacity hBudget
  have hSupport := FiniteCoarseYThresholdSelection.old_support_eq L oldIndex
    (newY mu R height F Fcfg) (newX mu R) theta hHalf
  exact FiniteCoarseYThresholdSelection.support_cover L oldIndex
    (newY mu R height F Fcfg) (newX mu R) theta (oldY mu R height) Neighbor hSupport hNear

end CanonicalGridRecoding
