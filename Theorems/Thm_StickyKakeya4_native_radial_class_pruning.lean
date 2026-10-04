import Theorems.Thm_StickyKakeya4_original_pair_strip_geometry
import Theorems.Thm_StickyKakeya4_rich_witness_real_core
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeRadialClassPruning
open OriginalPairStripGeometry RichWitnessCore

abbrev ClassLabel := Point×ℤ

def radialAngle (p q : Point) : ℝ := Complex.arg ⟨q.1-p.1,q.2-p.2⟩
def forwardClass (rho : ℝ) (z : Pair) : ClassLabel := (z.1,⌊radialAngle z.1 z.2/rho⌋)
def reverseClass (rho : ℝ) (z : Pair) : ClassLabel := (z.2,⌊radialAngle z.2 z.1/rho⌋)

def leftClass (rho : ℝ) : Pair⊕Pair → ClassLabel⊕ClassLabel
  | Sum.inl z => Sum.inl (forwardClass rho z)
  | Sum.inr z => Sum.inr (reverseClass rho z)

def rightClass (rho : ℝ) : Pair⊕Pair → ClassLabel⊕ClassLabel
  | Sum.inl z => Sum.inr (reverseClass rho z)
  | Sum.inr z => Sum.inl (forwardClass rho z)

/-- Doubled oriented labels retain exactly the same ORIGINAL graph on both sides. -/
theorem retained_oriented_labels
    (G : Finset Pair) (rho : ℝ) (S : Finset (ClassLabel⊕ClassLabel)) :
    retained (G.disjSum G) (leftClass rho) (rightClass rho) S =
      (G.filter (fun z => Sum.inl (forwardClass rho z)∈S ∧
        Sum.inr (reverseClass rho z)∈S)).disjSum
      (G.filter (fun z => Sum.inl (forwardClass rho z)∈S ∧
        Sum.inr (reverseClass rho z)∈S)) := by
  classical
  apply Finset.ext
  intro z
  cases z with
  | inl z =>
    constructor
    · intro hz
      obtain ⟨hzG,hl,hr⟩ := Finset.mem_filter.mp hz
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_filter.mpr
        ⟨Finset.inl_mem_disjSum.mp hzG,hl,hr⟩)
    · intro hz
      obtain ⟨hzG,hl,hr⟩ := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hz)
      exact Finset.mem_filter.mpr ⟨Finset.inl_mem_disjSum.mpr hzG,hl,hr⟩
  | inr z =>
    constructor
    · intro hz
      obtain ⟨hzG,hr,hl⟩ := Finset.mem_filter.mp hz
      exact Finset.inr_mem_disjSum.mpr (Finset.mem_filter.mpr
        ⟨Finset.inr_mem_disjSum.mp hzG,hl,hr⟩)
    · intro hz
      obtain ⟨hzG,hl,hr⟩ := Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hz)
      exact Finset.mem_filter.mpr ⟨Finset.inr_mem_disjSum.mpr hzG,hr,hl⟩

/-- Original class sizes are exactly the canonical engine's outgoing degrees. -/
theorem oriented_degree_counts (H : Finset Pair) (rho : ℝ) (a : ClassLabel) :
    (outgoing (H.disjSum H) (leftClass rho) (Sum.inl a)).card=
      (H.filter (fun z => forwardClass rho z=a)).card ∧
    (outgoing (H.disjSum H) (leftClass rho) (Sum.inr a)).card=
      (H.filter (fun z => reverseClass rho z=a)).card := by
  classical
  have hleft : outgoing (H.disjSum H) (leftClass rho) (Sum.inl a)=
      (H.filter (fun z => forwardClass rho z=a)).disjSum (∅ : Finset Pair) := by
    apply Finset.ext
    intro z
    cases z with
    | inl z =>
      constructor
      · intro hz
        obtain ⟨hzH,hf⟩ := Finset.mem_filter.mp hz
        exact Finset.inl_mem_disjSum.mpr (Finset.mem_filter.mpr
          ⟨Finset.inl_mem_disjSum.mp hzH,Sum.inl.inj hf⟩)
      · intro hz
        obtain ⟨hzH,hf⟩ := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hz)
        exact Finset.mem_filter.mpr ⟨Finset.inl_mem_disjSum.mpr hzH,congrArg Sum.inl hf⟩
    | inr z =>
      constructor
      · intro hz
        have hf := (Finset.mem_filter.mp hz).2
        cases hf
      · intro hz
        exact (Finset.notMem_empty z (Finset.inr_mem_disjSum.mp hz)).elim
  have hright : outgoing (H.disjSum H) (leftClass rho) (Sum.inr a)=
      (∅ : Finset Pair).disjSum (H.filter (fun z => reverseClass rho z=a)) := by
    apply Finset.ext
    intro z
    cases z with
    | inl z =>
      constructor
      · intro hz
        have hf := (Finset.mem_filter.mp hz).2
        cases hf
      · intro hz
        exact (Finset.notMem_empty z (Finset.inl_mem_disjSum.mp hz)).elim
    | inr z =>
      constructor
      · intro hz
        obtain ⟨hzH,hf⟩ := Finset.mem_filter.mp hz
        exact Finset.inr_mem_disjSum.mpr (Finset.mem_filter.mpr
          ⟨Finset.inr_mem_disjSum.mp hzH,Sum.inr.inj hf⟩)
      · intro hz
        obtain ⟨hzH,hf⟩ := Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hz)
        exact Finset.mem_filter.mpr ⟨Finset.inr_mem_disjSum.mpr hzH,congrArg Sum.inr hf⟩
  constructor <;> simp only [hleft,hright,Finset.card_disjSum,Finset.card_empty,add_zero,zero_add]

/-- Native two-sided pruning reuses the canonical real rich-core theorem.
Both degrees concern the same final original H; G need not be symmetric. -/
theorem exists_original_radial_class_core (G : Finset Pair) (rho k : ℝ) (hk : 0≤k) :
    ∃ H : Finset Pair, H⊆G ∧
      (G.card : ℝ)≤H.card+2*k*((G.image (forwardClass rho)).card+
        (G.image (reverseClass rho)).card) ∧
      ∀ z∈H,
        2*k≤((H.filter (fun v => forwardClass rho v=forwardClass rho z)).card : ℝ) ∧
        2*k≤((H.filter (fun v => reverseClass rho v=reverseClass rho z)).card : ℝ) := by
  classical
  let W := G.disjSum G
  let V := (G.image (forwardClass rho)).disjSum (G.image (reverseClass rho))
  have hswap : Function.Involutive (Sum.swap : Pair⊕Pair→Pair⊕Pair) := by
    intro z
    cases z <;> rfl
  have hW : ∀ z∈W, Sum.swap z∈W := by
    intro z hz
    cases z <;> simpa [W] using hz
  have hends : ∀ z∈W, leftClass rho (Sum.swap z)=rightClass rho z ∧
      rightClass rho (Sum.swap z)=leftClass rho z := by
    intro z _
    cases z <;> exact ⟨rfl,rfl⟩
  have hV : ∀ z∈W, leftClass rho z∈V ∧ rightClass rho z∈V := by
    intro z hz
    cases z with
    | inl z =>
      have hzG : z∈G := by simpa only [W,Finset.inl_mem_disjSum] using hz
      exact ⟨Finset.inl_mem_disjSum.mpr (Finset.mem_image.mpr ⟨z,hzG,rfl⟩),
        Finset.inr_mem_disjSum.mpr (Finset.mem_image.mpr ⟨z,hzG,rfl⟩)⟩
    | inr z =>
      have hzG : z∈G := by simpa only [W,Finset.inr_mem_disjSum] using hz
      exact ⟨Finset.inr_mem_disjSum.mpr (Finset.mem_image.mpr ⟨z,hzG,rfl⟩),
        Finset.inl_mem_disjSum.mpr (Finset.mem_image.mpr ⟨z,hzG,rfl⟩)⟩
  obtain ⟨S,_hSV,hdegree,_hstrong,hret,_hret'⟩ := RichWitnessRealCore.exists_rich_core
    W V (leftClass rho) (rightClass rho) Sum.swap hswap hW hends hV (2*k) (by positivity)
  let H := G.filter (fun z => Sum.inl (forwardClass rho z)∈S ∧
    Sum.inr (reverseClass rho z)∈S)
  have hretained : retained W (leftClass rho) (rightClass rho) S=H.disjSum H :=
    retained_oriented_labels G rho S
  rw [hretained] at hret hdegree
  simp only [W,V,Finset.card_disjSum,Nat.cast_add] at hret
  refine ⟨H,Finset.filter_subset _ _,?_,?_⟩
  · nlinarith only [hret]
  · intro z hz
    have hs := (Finset.mem_filter.mp hz).2
    have hf := hdegree (Sum.inl (forwardClass rho z)) hs.1
    have hg := hdegree (Sum.inr (reverseClass rho z)) hs.2
    rw [(oriented_degree_counts H rho (forwardClass rho z)).1] at hf
    rw [(oriented_degree_counts H rho (reverseClass rho z)).2] at hg
    exact ⟨hf,hg⟩

end NativeRadialClassPruning
