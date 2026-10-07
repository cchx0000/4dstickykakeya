/- New draft, 2026-10-06. UNVERIFIED: no Lean check has been run in the restored environment. -/
import Theorems.Thm_StickyKakeya4_fine_point_slab_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace FiniteCoarseYThresholdSelection
open Classical Finset
open scoped BigOperators

variable {A F Y X : Type*} [DecidableEq A] [DecidableEq F] [DecidableEq Y] [DecidableEq X]

/-- F is the old (fine height, fine Y) label. A is the full fineXY label.
Y may include the final coarse height, so different heights are never
silently identified in the target support. All maps are label functions. -/
def oldFiber (L : Finset A) (fiber : A → F) (u : F) : Finset A :=
  L.filter (fun a => fiber a=u)

def branch (L : Finset A) (fiber : A → F) (newY : A → Y) (u : F) (b : Y) : Finset A :=
  (oldFiber L fiber u).filter (fun a => newY a=b)

def coarseCount (L : Finset A) (fiber : A → F) (newY : A → Y) (coarseX : A → X)
    (u : F) (b : Y) : ℕ := ((branch L fiber newY u b).image coarseX).card

/-- Delete every poor branch, rather than retaining one largest branch.
The decision is constant on each complete fineXY label. -/
def keepLabels (L : Finset A) (fiber : A → F) (newY : A → Y) (coarseX : A → X)
    (theta : ℝ) : Finset A :=
  L.filter (fun a => theta≤ (coarseCount L fiber newY coarseX (fiber a) (newY a):ℝ))

def oneFiberKeep (S : Finset A) (newY : A → Y) (coarseX : A → X) (theta : ℝ) : Finset A :=
  S.filter (fun a => theta≤ (((S.filter (fun z => newY z=newY a)).image coarseX).card:ℝ))

lemma keepLabels_subset (L : Finset A) (fiber : A → F) (newY : A → Y) (coarseX : A → X)
    (theta : ℝ) : keepLabels L fiber newY coarseX theta⊆ L := filter_subset _ _

/-- The only geometric input is the actual fine-X capacity in one coarse-X
cell. Exact nested grids give B=R^k; a packing argument may give a larger B. -/
theorem one_fiber_half (S : Finset A) (newY : A → Y) (coarseX : A → X)
    (M B : ℕ) (theta : ℝ) (htheta : 0≤ theta)
    (hMenu : (S.image newY).card≤ M)
    (hCapacity : ∀x : X,(S.filter (fun a => coarseX a=x)).card≤ B)
    (hBudget : 2*(M:ℝ)*(B:ℝ)*theta≤ (S.card:ℝ)) :
    S.card≤ 2*(oneFiberKeep S newY coarseX theta).card := by
  let Bad := S.filter (fun a => ¬theta≤ (((S.filter (fun z => newY z=newY a)).image coarseX).card:ℝ))
  have hBadS : Bad⊆ S := filter_subset _ _
  have hFiber (b : Y) (_hb : b∈S.image newY) :
      ((Bad.filter (fun a => newY a=b)).card:ℝ)≤ theta*(B:ℝ) := by
    by_cases hn : (Bad.filter (fun a => newY a=b)).Nonempty
    · obtain ⟨a,ha⟩ := hn
      have haBad := (mem_filter.mp ha).1
      have hab := (mem_filter.mp ha).2
      have hPoor := (mem_filter.mp haBad).2
      rw [hab] at hPoor
      have hCount : (((S.filter (fun z => newY z=b)).image coarseX).card:ℝ)< theta :=
        lt_of_not_ge hPoor
      have hSub : Bad.filter (fun z => newY z=b)⊆ S.filter (fun z => newY z=b) :=
        filter_subset_filter _ hBadS
      have hCap : ((S.filter (fun z => newY z=b)).card:ℝ)≤
          (((S.filter (fun z => newY z=b)).image coarseX).card:ℝ)*(B:ℝ) := by
        apply FinePointSlabGeometry.card_le_real_mul_of_fibers
          (S.filter (fun z => newY z=b)) ((S.filter (fun z => newY z=b)).image coarseX)
          coarseX (B:ℝ) (fun z hz => mem_image_of_mem _ hz)
        intro x _hx
        have hs : (S.filter (fun z => newY z=b)).filter (fun z => coarseX z=x)⊆
            S.filter (fun z => coarseX z=x) := filter_subset_filter _ (filter_subset _ _)
        exact_mod_cast (card_le_card hs).trans (hCapacity x)
      exact (Nat.cast_le.mpr (card_le_card hSub)).trans
        (hCap.trans (mul_le_mul_of_nonneg_right hCount.le (Nat.cast_nonneg B)))
    · rw [not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero]
      exact mul_nonneg htheta (Nat.cast_nonneg B)
  have hBad := FinePointSlabGeometry.card_le_real_mul_of_fibers Bad (S.image newY) newY
    (theta*(B:ℝ)) (fun a ha => mem_image_of_mem _ (hBadS ha)) hFiber
  have hBadBound : (Bad.card:ℝ)≤ (M:ℝ)*theta*(B:ℝ) := hBad.trans (by
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hMenu)
      (mul_nonneg htheta (Nat.cast_nonneg B))
    simpa only [mul_assoc] using hh)
  have hpart := card_filter_add_card_filter_not (s := S)
    (fun a => theta≤ (((S.filter (fun z => newY z=newY a)).image coarseX).card:ℝ))
  change (oneFiberKeep S newY coarseX theta).card+Bad.card=S.card at hpart
  have hpartR : ((oneFiberKeep S newY coarseX theta).card:ℝ)+(Bad.card:ℝ)=(S.card:ℝ) := by
    exact_mod_cast hpart
  have hh : (S.card:ℝ)≤ 2*((oneFiberKeep S newY coarseX theta).card:ℝ) := by
    nlinarith only [hpartR,hBadBound,hBudget]
  exact_mod_cast hh

lemma kept_fiber_eq (L : Finset A) (fiber : A → F) (newY : A → Y) (coarseX : A → X)
    (theta : ℝ) (u : F) :
    oldFiber (keepLabels L fiber newY coarseX theta) fiber u=
      oneFiberKeep (oldFiber L fiber u) newY coarseX theta := by
  ext a
  simp only [oldFiber,keepLabels,oneFiberKeep,mem_filter]
  constructor
  · rintro ⟨⟨ha,hgood⟩,hfa⟩
    refine ⟨⟨ha,hfa⟩,?_⟩
    simpa only [coarseCount,branch,oldFiber,hfa] using hgood
  · rintro ⟨⟨ha,hfa⟩,hgood⟩
    refine ⟨⟨ha,?_⟩,hfa⟩
    simpa only [coarseCount,branch,oldFiber,hfa] using hgood

/-- At least half the fineXY labels remain in EACH old fine-Y fiber. -/
theorem each_old_fiber_half (L : Finset A) (fiber : A → F) (newY : A → Y)
    (coarseX : A → X) (M B : ℕ) (theta : ℝ) (htheta : 0≤ theta)
    (hMenu : ∀u∈L.image fiber,((oldFiber L fiber u).image newY).card≤ M)
    (hCapacity : ∀u∈L.image fiber,∀x : X,
      ((oldFiber L fiber u).filter (fun a => coarseX a=x)).card≤ B)
    (hBudget : ∀u∈L.image fiber,2*(M:ℝ)*(B:ℝ)*theta≤ ((oldFiber L fiber u).card:ℝ)) :
    ∀u∈L.image fiber,(oldFiber L fiber u).card≤
      2*(oldFiber (keepLabels L fiber newY coarseX theta) fiber u).card := by
  intro u hu
  rw [kept_fiber_eq]
  exact one_fiber_half (oldFiber L fiber u) newY coarseX M B theta htheta
    (hMenu u hu) (hCapacity u hu) (hBudget u hu)

theorem global_half (L : Finset A) (fiber : A → F) (newY : A → Y)
    (coarseX : A → X) (theta : ℝ)
    (H : ∀u∈L.image fiber,(oldFiber L fiber u).card≤
      2*(oldFiber (keepLabels L fiber newY coarseX theta) fiber u).card) :
    L.card≤ 2*(keepLabels L fiber newY coarseX theta).card := by
  have hKeep := keepLabels_subset L fiber newY coarseX theta
  have hL : L.card=∑u∈L.image fiber,(oldFiber L fiber u).card := card_eq_sum_card_image fiber L
  have hK : (keepLabels L fiber newY coarseX theta).card=
      ∑u∈L.image fiber,(oldFiber (keepLabels L fiber newY coarseX theta) fiber u).card :=
    card_eq_sum_card_fiberwise (fun a ha => mem_image_of_mem fiber (hKeep ha))
  calc
    _ = _ := hL
    _ ≤ ∑u∈L.image fiber,2*(oldFiber (keepLabels L fiber newY coarseX theta) fiber u).card :=
      sum_le_sum H
    _ = _ := by rw [←mul_sum,←hK]

/-- No old (fine-height,fine-Y) support label disappears. -/
theorem old_support_eq (L : Finset A) (fiber : A → F) (newY : A → Y)
    (coarseX : A → X) (theta : ℝ)
    (H : ∀u∈L.image fiber,(oldFiber L fiber u).card≤
      2*(oldFiber (keepLabels L fiber newY coarseX theta) fiber u).card) :
    (keepLabels L fiber newY coarseX theta).image fiber=L.image fiber := by
  apply Subset.antisymm (image_subset_image (keepLabels_subset L fiber newY coarseX theta))
  intro u hu
  obtain ⟨a,ha,hfa⟩ := mem_image.mp hu
  have hOld : (oldFiber L fiber u).Nonempty := ⟨a,mem_filter.mpr ⟨ha,hfa⟩⟩
  have hHalf := H u (mem_image.mpr ⟨a,ha,hfa⟩)
  have hNew : (oldFiber (keepLabels L fiber newY coarseX theta) fiber u).Nonempty := by
    apply card_pos.mp
    have ho := hOld.card_pos
    omega
  obtain ⟨b,hb⟩ := hNew
  exact mem_image.mpr ⟨b,(mem_filter.mp hb).1,(mem_filter.mp hb).2⟩

lemma retained_branch_eq (L : Finset A) (fiber : A → F) (newY : A → Y)
    (coarseX : A → X) (theta : ℝ) (u : F) (b : Y)
    (H : theta≤ (coarseCount L fiber newY coarseX u b:ℝ)) :
    branch (keepLabels L fiber newY coarseX theta) fiber newY u b=branch L fiber newY u b := by
  ext a
  simp only [branch,oldFiber,keepLabels,mem_filter]
  constructor
  · exact fun h => ⟨⟨h.1.1.1,h.1.2⟩,h.2⟩
  · rintro ⟨⟨ha,hfa⟩,hya⟩
    exact ⟨⟨⟨ha,by simpa only [hfa,hya] using H⟩,hfa⟩,hya⟩

/-- Every retained new Y label contains a single actual dense old-fiber
branch. Across-height X populations are never added as if disjoint. -/
theorem dense_branch_witness (L : Finset A) (fiber : A → F) (newY : A → Y)
    (coarseX : A → X) (theta : ℝ) :
    ∀b∈(keepLabels L fiber newY coarseX theta).image newY,
      ∃u∈L.image fiber,(branch (keepLabels L fiber newY coarseX theta) fiber newY u b).Nonempty ∧
        theta≤ (((branch (keepLabels L fiber newY coarseX theta) fiber newY u b).image coarseX).card:ℝ) := by
  intro b hb
  obtain ⟨a,ha,hab⟩ := mem_image.mp hb
  have haL := (mem_filter.mp ha).1
  have hRich := (mem_filter.mp ha).2
  rw [hab] at hRich
  refine ⟨fiber a,mem_image_of_mem _ haL,⟨a,mem_filter.mpr ⟨mem_filter.mpr ⟨ha,rfl⟩,hab⟩⟩,?_⟩
  rw [retained_branch_eq L fiber newY coarseX theta (fiber a) b hRich]
  exact hRich

/-- Consequently each retained new-Y fiber itself has the required
coarse-X cardinality, using inclusion of its one dense witness branch. -/
theorem dense_newY_fiber (L : Finset A) (fiber : A → F) (newY : A → Y)
    (coarseX : A → X) (theta : ℝ) :
    ∀b∈(keepLabels L fiber newY coarseX theta).image newY,
      theta≤ ((((keepLabels L fiber newY coarseX theta).filter (fun a => newY a=b)).image
        coarseX).card:ℝ) := by
  intro b hb
  obtain ⟨u,_hu,_hne,hDense⟩ := dense_branch_witness L fiber newY coarseX theta b hb
  have hSub : branch (keepLabels L fiber newY coarseX theta) fiber newY u b⊆
      (keepLabels L fiber newY coarseX theta).filter (fun a => newY a=b) :=
    filter_subset_filter _ (filter_subset _ _)
  exact hDense.trans (Nat.cast_le.mpr (card_le_card (image_subset_image hSub)))

/-- Actual bounded-displacement neighbor relations survive both ways.
The caller can include equality of coarse-height labels in Rel. -/
theorem support_cover {U : Type*} (L : Finset A) (fiber : A → F) (newY : A → Y)
    (coarseX : A → X) (theta : ℝ) (oldY : F → U) (Rel : U → Y → Prop)
    (Hsupport : (keepLabels L fiber newY coarseX theta).image fiber=L.image fiber)
    (Hnear : ∀a∈L,Rel (oldY (fiber a)) (newY a)) :
    (∀u∈L.image fiber,∃b∈(keepLabels L fiber newY coarseX theta).image newY,Rel (oldY u) b) ∧
    (∀b∈(keepLabels L fiber newY coarseX theta).image newY,∃u∈L.image fiber,Rel (oldY u) b) := by
  constructor
  · intro u hu
    rw [←Hsupport] at hu
    obtain ⟨a,ha,hfa⟩ := mem_image.mp hu
    refine ⟨newY a,mem_image_of_mem _ ha,?_⟩
    simpa only [hfa] using Hnear a (keepLabels_subset L fiber newY coarseX theta ha)
  · intro b hb
    obtain ⟨a,ha,hab⟩ := mem_image.mp hb
    have haL := keepLabels_subset L fiber newY coarseX theta ha
    refine ⟨fiber a,mem_image_of_mem _ haL,?_⟩
    simpa only [hab] using Hnear a haL

/-- Half the labels and one already available global weight ratio suffice.
No uniformity is added after the cut. -/
theorem half_labels_weight (L G : Finset A) (hGL : G⊆ L)
    (hhalf : L.card≤ 2*G.card) (w : A → ℕ) (Q : ℕ)
    (Hcomp : ∀a∈L,∀b∈L,w a≤ Q^2*w b) :
    (∑a∈L,w a)≤ 2*Q^2*(∑a∈G,w a) := by
  by_cases hn : L.Nonempty
  · obtain ⟨a0,ha0,hmax⟩ := exists_max_image L w hn
    have hUpper : (∑a∈L,w a)≤ w a0*L.card := by
      calc
        _ ≤ ∑_a∈L,w a0 := sum_le_sum (fun a ha => hmax a ha)
        _ = _ := by simp [mul_comm]
    have hLower : w a0*G.card≤ Q^2*(∑a∈G,w a) := by
      calc
        _ = ∑_a∈G,w a0 := by simp [mul_comm]
        _ ≤ ∑a∈G,Q^2*w a := sum_le_sum (fun a ha => Hcomp a0 ha0 a (hGL ha))
        _ = _ := by rw [mul_sum]
    calc
      _ ≤ w a0*L.card := hUpper
      _ ≤ w a0*(2*G.card) := Nat.mul_le_mul_left _ hhalf
      _ = 2*(w a0*G.card) := by ring
      _ ≤ 2*(Q^2*(∑a∈G,w a)) := Nat.mul_le_mul_left _ hLower
      _ = _ := by ring
  · have hL : L=∅ := not_nonempty_iff_eq_empty.mp hn
    simp only [hL,sum_empty]
    exact Nat.zero_le _

variable {E P : Type*} [DecidableEq E] [DecidableEq P]

/-- The actual original-edge set selected by a set of canonical labels. -/
def liftEdges (I : Finset E) (label : E → A) (G : Finset A) : Finset E :=
  I.filter (fun e => label e∈G)

lemma liftEdges_subset (I : Finset E) (label : E → A) (G : Finset A) :
    liftEdges I label G⊆ I := filter_subset _ _

lemma liftEdges_fiber_eq (I : Finset E) (label : E → A) (G : Finset A)
    (a : A) (ha : a∈G) :
    (liftEdges I label G).filter (fun e => label e=a)=I.filter (fun e => label e=a) := by
  ext e
  simp only [liftEdges,mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨he,hea⟩
    exact ⟨⟨he,by simpa only [hea] using ha⟩,hea⟩

lemma liftEdges_image (I : Finset E) (label : E → A) (G : Finset A)
    (hG : G⊆ I.image label) : (liftEdges I label G).image label=G := by
  apply Subset.antisymm
  · intro a ha
    obtain ⟨e,he,rfl⟩ := mem_image.mp ha
    exact (mem_filter.mp he).2
  · intro a ha
    obtain ⟨e,he,hea⟩ := mem_image.mp (hG ha)
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨he,by simpa only [hea] using ha⟩,hea⟩

lemma liftEdges_card (I : Finset E) (label : E → A) (G : Finset A) :
    (liftEdges I label G).card=∑a∈G,(I.filter (fun e => label e=a)).card := by
  have hpart : (liftEdges I label G).card=
      ∑a∈G,((liftEdges I label G).filter (fun e => label e=a)).card :=
    card_eq_sum_card_fiberwise (fun e he => (mem_filter.mp he).2)
  rw [hpart]
  apply sum_congr rfl
  intro a ha
  rw [liftEdges_fiber_eq I label G a ha]

/-- This is the literal old-edge retention, before any angular trim.
The hypothesis is the existing global fineXY label-fiber ratio. -/
theorem half_labels_original_edges (I : Finset E) (label : E → A) (G : Finset A)
    (hG : G⊆ I.image label) (hhalf : (I.image label).card≤ 2*G.card) (Q : ℕ)
    (Hcomp : ∀a∈I.image label,∀b∈I.image label,
      (I.filter (fun e => label e=a)).card≤ Q^2*(I.filter (fun e => label e=b)).card) :
    I.card≤ 2*Q^2*(liftEdges I label G).card := by
  have h := half_labels_weight (I.image label) G hG hhalf
    (fun a => (I.filter (fun e => label e=a)).card) Q Hcomp
  rw [←card_eq_sum_card_image label I,←liftEdges_card I label G] at h
  exact h

/-- A canonical label depends only on the original point. Therefore every
surviving original point retains its entire current incidence fiber. -/
theorem original_point_fiber_eq (I : Finset E) (point : E → P) (fineLabel : P → A)
    (G : Finset A) (k : P) (hk : fineLabel k∈G) :
    (liftEdges I (fineLabel∘point) G).filter (fun e => point e=k)=
      I.filter (fun e => point e=k) := by
  ext e
  simp only [liftEdges,mem_filter,Function.comp_apply]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨he,hek⟩
    exact ⟨⟨he,by simpa only [hek] using hk⟩,hek⟩

/-- In particular the equality holds for every occupied retained point. -/
theorem surviving_original_point_fiber_eq (I : Finset E) (point : E → P)
    (fineLabel : P → A) (G : Finset A) :
    ∀k∈(liftEdges I (fineLabel∘point) G).image point,
      (liftEdges I (fineLabel∘point) G).filter (fun e => point e=k)=
        I.filter (fun e => point e=k) := by
  intro k hk
  obtain ⟨e,he,hek⟩ := mem_image.mp hk
  apply original_point_fiber_eq
  have hmem := (mem_filter.mp he).2
  simpa only [Function.comp_apply,hek] using hmem

/-- The complete finite-label cut, with the deterministic selected labels
kept visible. Neither AD regularity nor geometric density is assumed as
an output certificate: the conclusion follows from menu size, coarse-X
capacity, the old-fiber population, and the actual label weight ratio. -/
theorem threshold_original_edges {U : Type*}
    (I : Finset E) (point : E → P) (fineLabel : P → A)
    (fiber : A → F) (newY : A → Y) (coarseX : A → X)
    (M B Q : ℕ) (theta : ℝ) (htheta : 0≤ theta)
    (hMenu : ∀u∈(I.image (fineLabel∘point)).image fiber,
      ((oldFiber (I.image (fineLabel∘point)) fiber u).image newY).card≤ M)
    (hCapacity : ∀u∈(I.image (fineLabel∘point)).image fiber,∀x : X,
      ((oldFiber (I.image (fineLabel∘point)) fiber u).filter (fun a => coarseX a=x)).card≤ B)
    (hBudget : ∀u∈(I.image (fineLabel∘point)).image fiber,
      2*(M:ℝ)*(B:ℝ)*theta≤ ((oldFiber (I.image (fineLabel∘point)) fiber u).card:ℝ))
    (Hcomp : ∀a∈I.image (fineLabel∘point),∀b∈I.image (fineLabel∘point),
      (I.filter (fun e => fineLabel (point e)=a)).card≤
        Q^2*(I.filter (fun e => fineLabel (point e)=b)).card)
    (oldY : F → U) (Rel : U → Y → Prop)
    (Hnear : ∀a∈I.image (fineLabel∘point),Rel (oldY (fiber a)) (newY a)) :
    let L := I.image (fineLabel∘point)
    let G := keepLabels L fiber newY coarseX theta
    let J := liftEdges I (fineLabel∘point) G
    J⊆ I ∧ J.image (fineLabel∘point)=G ∧
      I.card≤ 2*Q^2*J.card ∧
      (∀u∈L.image fiber,(oldFiber L fiber u).card≤ 2*(oldFiber G fiber u).card) ∧
      G.image fiber=L.image fiber ∧
      (∀b∈G.image newY,∃u∈L.image fiber,(branch G fiber newY u b).Nonempty ∧
        theta≤ (((branch G fiber newY u b).image coarseX).card:ℝ)) ∧
      ((∀u∈L.image fiber,∃b∈G.image newY,Rel (oldY u) b) ∧
        (∀b∈G.image newY,∃u∈L.image fiber,Rel (oldY u) b)) ∧
      (∀k∈J.image point,J.filter (fun e => point e=k)=I.filter (fun e => point e=k)) := by
  let L := I.image (fineLabel∘point)
  let G := keepLabels L fiber newY coarseX theta
  have hHalf : ∀u∈L.image fiber,(oldFiber L fiber u).card≤ 2*(oldFiber G fiber u).card :=
    each_old_fiber_half L fiber newY coarseX M B theta htheta hMenu hCapacity hBudget
  have hGlobal : L.card≤ 2*G.card := global_half L fiber newY coarseX theta hHalf
  have hSupport : G.image fiber=L.image fiber := old_support_eq L fiber newY coarseX theta hHalf
  have hGL : G⊆ L := keepLabels_subset L fiber newY coarseX theta
  refine ⟨liftEdges_subset I (fineLabel∘point) G,liftEdges_image I (fineLabel∘point) G hGL,
    ?_,hHalf,hSupport,dense_branch_witness L fiber newY coarseX theta,
    support_cover L fiber newY coarseX theta oldY Rel hSupport Hnear,
    surviving_original_point_fiber_eq I point fineLabel G⟩
  exact half_labels_original_edges I (fineLabel∘point) G hGL hGlobal Q Hcomp

end FiniteCoarseYThresholdSelection
