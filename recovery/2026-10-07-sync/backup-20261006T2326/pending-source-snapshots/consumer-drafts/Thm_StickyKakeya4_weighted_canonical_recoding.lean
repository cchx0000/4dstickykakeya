/- New draft, 2026-10-06. Checks are coordinated in the recovered executor. -/
import Theorems.Thm_StickyKakeya4_canonical_grid_recoding

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace WeightedCanonicalRecoding
open Classical Finset CanonicalGridRecoding
open scoped BigOperators

variable {k l : ℕ}

/-- The label is built from maps on ORIGINAL points, so all subsequent
cuts retain complete original point fibers. -/
def pointLabel {P H : Type*} (height : P → H) (x : P → Grid k) (y : P → Grid l)
    (p : P) : Label H k l := (height p,(x p,y p))

def oldPoints {E P H : Type*} [DecidableEq P] [DecidableEq H]
    (I : Finset E) (point : E → P) (height : P → H) (y : P → Grid l)
    (b : H × Grid l) : Finset P :=
  (I.image point).filter (fun p => (height p,y p)=b)

def fineXCells {E P H : Type*} [DecidableEq P] [DecidableEq H]
    (I : Finset E) (point : E → P) (height : P → H) (x : P → Grid k)
    (y : P → Grid l) (b : H × Grid l) : Finset (Grid k) :=
  (oldPoints I point height y b).image x

/-- Exact identification of the old canonical label fiber with DISTINCT
fine X cells of the SAME original-point fiber. Edge multiplicity is absent
from both sides; it is restored separately by the label weights. -/
theorem old_label_fiber_eq {E P H : Type*} [DecidableEq P] [DecidableEq H]
    (I : Finset E) (point : E → P) (height : P → H) (x : P → Grid k)
    (y : P → Grid l) (b : H × Grid l) :
    FiniteCoarseYThresholdSelection.oldFiber (I.image ((pointLabel height x y)∘point)) oldIndex b=
      (fineXCells I point height x y b).image (fun u => (b.1,(u,b.2))) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzL,hzb⟩ := mem_filter.mp hz
    obtain ⟨e,he,rfl⟩ := mem_image.mp hzL
    have hOld : (height (point e),y (point e))=b := hzb
    refine mem_image.mpr ⟨x (point e),?_,?_⟩
    · exact mem_image.mpr ⟨point e,mem_filter.mpr ⟨mem_image_of_mem _ he,hOld⟩,rfl⟩
    · exact Prod.ext (congrArg (fun b : H × Grid l => b.1) hOld).symm
        (Prod.ext rfl (congrArg (fun b : H × Grid l => b.2) hOld).symm)
  · intro hz
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hz
    obtain ⟨p,hp,hxp⟩ := mem_image.mp hu
    obtain ⟨hpI,hpb⟩ := mem_filter.mp hp
    obtain ⟨e,he,hep⟩ := mem_image.mp hpI
    have hh := congrArg (fun b : H × Grid l => b.1) hpb
    have hy := congrArg (fun b : H × Grid l => b.2) hpb
    refine mem_filter.mpr ⟨mem_image.mpr ⟨e,he,?_⟩,?_⟩
    · simp only [Function.comp_apply,pointLabel,hep,hh,hy,hxp]
    · simp only [oldIndex,Prod.mk.eta]

theorem old_label_fiber_card {E P H : Type*} [DecidableEq P] [DecidableEq H]
    (I : Finset E) (point : E → P) (height : P → H) (x : P → Grid k)
    (y : P → Grid l) (b : H × Grid l) :
    (FiniteCoarseYThresholdSelection.oldFiber
      (I.image ((pointLabel height x y)∘point)) oldIndex b).card=
      (fineXCells I point height x y b).card := by
  rw [old_label_fiber_eq]
  apply card_image_of_injective
  intro u v huv
  exact congrArg (fun z : Label H k l => z.2.1) huv

/-- The fine-label weight is the exact sum of original point weights,
not a distinct-point count substituted for original incidences. -/
theorem label_weight_eq_sum_point_weights {E P A : Type*}
    [DecidableEq P] [DecidableEq A] (I : Finset E) (point : E → P)
    (label : P → A) (a : A) :
    (I.filter (fun e => label (point e)=a)).card=
      ∑p∈(I.image point).filter (fun p => label p=a),(I.filter (fun e => point e=p)).card := by
  let S := I.filter (fun e => label (point e)=a)
  let P0 := (I.image point).filter (fun p => label p=a)
  have hmaps : ∀e∈S,point e∈P0 := by
    intro e he
    exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp he).1,(mem_filter.mp he).2⟩
  have hpart : S.card=∑p∈P0,(S.filter (fun e => point e=p)).card :=
    card_eq_sum_card_fiberwise hmaps
  rw [hpart]
  apply sum_congr rfl
  intro p hp
  have hpa := (mem_filter.mp hp).2
  congr 1
  ext e
  simp only [S,mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨he,hep⟩
    exact ⟨⟨he,by simpa only [hep] using hpa⟩,hep⟩

/-- For a whole-original-point cut, the sum of OLD point weights on
surviving points is exactly the retained original edge count. -/
theorem retained_point_weight_mass {E P : Type*} [DecidableEq P]
    (I J : Finset E) (point : E → P)
    (H : ∀p∈J.image point,J.filter (fun e => point e=p)=I.filter (fun e => point e=p)) :
    (∑p∈J.image point,(I.filter (fun e => point e=p)).card)=J.card := by
  calc
    _ = ∑p∈J.image point,(J.filter (fun e => point e=p)).card := by
      apply sum_congr rfl
      intro p hp
      rw [H p hp]
    _ = _ := (card_eq_sum_card_image point J).symm

/-- Explicit threshold for the actual canonical branch capacity. -/
def threshold (Dmin : ℝ) (R k : ℕ) : ℝ := Dmin/(98*(R^k:ℝ))

theorem threshold_nonneg (Dmin : ℝ) (hD : 0≤Dmin) (R k : ℕ) :
    0≤threshold Dmin R k := div_nonneg hD (by positivity)

theorem threshold_budget (Dmin : ℝ) (R k : ℕ) (hR : 0 < R) :
    2*(49:ℝ)*((R^k:ℕ):ℝ)*threshold Dmin R k=Dmin := by
  have hpow : (R:ℝ)^k≠0 := pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hR))
  unfold threshold
  push_cast
  field_simp [hpow]
  <;> ring

lemma real_retention {a b Q : ℕ} (h : a≤2*Q^2*b) :
    (a:ℝ)/(2*(Q:ℝ)^2)≤(b:ℝ) := by
  by_cases hQ : Q=0
  · simp [hQ]
  · have hQpos : (0:ℝ)<Q := by exact_mod_cast (Nat.pos_of_ne_zero hQ)
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(Q:ℝ)^2)).2
    have hh : (a:ℝ)≤2*(Q:ℝ)^2*(b:ℝ) := by exact_mod_cast h
    nlinarith only [hh]

/-- Actual recoding of the same original incidence set. The density input
is the old fine-X image of actual original points, not the desired new-Y
population. Matrix coherence and center bounds derive both capacities.
The existing Q^2 label-weight comparison restores original edge mass. -/
theorem exists_actual_coarse_recoding {E P H Z : Type*}
    [DecidableEq E] [DecidableEq P] [DecidableEq H] [DecidableEq Z]
    (I : Finset E) (point : E → P) (fineHeight : P → H)
    (fineX : P → Grid k) (fineY : P → Grid l)
    (hk : k≤2) (hl : l≤2) (mu : ℝ) (R Q : ℕ) (hmu : 0 < mu) (hR : 0 < R)
    (height : H → Z) (F : H → Matrix (Fin l) (Fin k) ℝ)
    (Fcfg : Z → Matrix (Fin l) (Fin k) ℝ)
    (hF : ∀p∈I.image point,∀i j,|F (fineHeight p) i j-Fcfg (height (fineHeight p)) i j|≤mu*(R:ℝ))
    (hx : ∀p∈I.image point,∀j,|center mu (fineX p) j|≤1)
    (Dmin : ℝ) (hD : 0≤Dmin)
    (hDense : ∀b∈(I.image ((pointLabel fineHeight fineX fineY)∘point)).image oldIndex,
      Dmin≤((fineXCells I point fineHeight fineX fineY b).card:ℝ))
    (hWeight : ∀a∈I.image ((pointLabel fineHeight fineX fineY)∘point),
      ∀b∈I.image ((pointLabel fineHeight fineX fineY)∘point),
      (I.filter (fun e => pointLabel fineHeight fineX fineY (point e)=a)).card≤
        Q^2*(I.filter (fun e => pointLabel fineHeight fineX fineY (point e)=b)).card) :
    ∃J : Finset E,J⊆I ∧
      (I.card:ℝ)/(2*(Q:ℝ)^2)≤(J.card:ℝ) ∧
      (I.card:ℝ)/(2*(Q:ℝ)^2)≤
        ((∑p∈J.image point,(I.filter (fun e => point e=p)).card):ℝ) ∧
      (∀a∈J.image ((pointLabel fineHeight fineX fineY)∘point),
        J.filter (fun e => pointLabel fineHeight fineX fineY (point e)=a)=
          I.filter (fun e => pointLabel fineHeight fineX fineY (point e)=a)) ∧
      (∀p∈J.image point,J.filter (fun e => point e=p)=I.filter (fun e => point e=p)) ∧
      (∀b∈(I.image ((pointLabel fineHeight fineX fineY)∘point)).image oldIndex,
        ∃q∈(J.image ((pointLabel fineHeight fineX fineY)∘point)).image (newY mu R height F Fcfg),
          Neighbor (oldY mu R height b) q) ∧
      (∀q∈(J.image ((pointLabel fineHeight fineX fineY)∘point)).image (newY mu R height F Fcfg),
        ∃b∈(I.image ((pointLabel fineHeight fineX fineY)∘point)).image oldIndex,
          Neighbor (oldY mu R height b) q) ∧
      (∀q∈(J.image ((pointLabel fineHeight fineX fineY)∘point)).image (newY mu R height F Fcfg),
        threshold Dmin R k≤
          ((((J.image ((pointLabel fineHeight fineX fineY)∘point)).filter
            (fun a => newY mu R height F Fcfg a=q)).image (newX mu R)).card:ℝ)) := by
  let label := pointLabel fineHeight fineX fineY
  let L := I.image (label∘point)
  let theta := threshold Dmin R k
  let G := FiniteCoarseYThresholdSelection.keepLabels L oldIndex
    (newY mu R height F Fcfg) (newX mu R) theta
  let J := FiniteCoarseYThresholdSelection.liftEdges I (label∘point) G
  have hFL : ∀z∈L,∀i j,|F z.1 i j-Fcfg (height z.1) i j|≤mu*(R:ℝ) := by
    intro z hz i j
    obtain ⟨e,he,rfl⟩ := mem_image.mp hz
    exact hF (point e) (mem_image_of_mem _ he) i j
  have hxL : ∀z∈L,∀j,|center mu z.2.1 j|≤1 := by
    intro z hz j
    obtain ⟨e,he,rfl⟩ := mem_image.mp hz
    exact hx (point e) (mem_image_of_mem _ he) j
  obtain ⟨hMenu,hCapacity,hNear⟩ := threshold_inputs L hk hl mu R hmu hR height F Fcfg hFL hxL
  have hBudget : ∀b∈L.image oldIndex,2*(49:ℝ)*((R^k:ℕ):ℝ)*theta≤
      ((FiniteCoarseYThresholdSelection.oldFiber L oldIndex b).card:ℝ) := by
    intro b hb
    change 2*(49:ℝ)*((R^k:ℕ):ℝ)*threshold Dmin R k≤_
    rw [threshold_budget Dmin R k hR]
    change Dmin≤((FiniteCoarseYThresholdSelection.oldFiber
      (I.image ((pointLabel fineHeight fineX fineY)∘point)) oldIndex b).card:ℝ)
    rw [old_label_fiber_card]
    exact hDense b hb
  have hAll := FiniteCoarseYThresholdSelection.threshold_original_edges
    I point label oldIndex (newY mu R height F Fcfg) (newX mu R)
    49 (R^k) Q theta (threshold_nonneg Dmin hD R k) hMenu hCapacity hBudget
    hWeight (oldY mu R height) Neighbor hNear
  rcases hAll with ⟨hJI,hImage,hMass,_hHalf,_hSupport,_hDenseBranch,hCover,hPoints⟩
  refine ⟨J,hJI,real_retention hMass,?_,?_,hPoints,?_,?_,?_⟩
  · rw [retained_point_weight_mass I J point hPoints]
    exact real_retention hMass
  · intro a ha
    have haG : a∈G := by rwa [hImage] at ha
    exact FiniteCoarseYThresholdSelection.liftEdges_fiber_eq I (label∘point) G a haG
  · simpa only [hImage] using hCover.1
  · simpa only [hImage] using hCover.2
  · intro q hq
    have hqG : q∈G.image (newY mu R height F Fcfg) := by rwa [hImage] at hq
    have hd := FiniteCoarseYThresholdSelection.dense_newY_fiber L oldIndex
      (newY mu R height F Fcfg) (newX mu R) theta q hqG
    simpa only [hImage] using hd

end WeightedCanonicalRecoding
