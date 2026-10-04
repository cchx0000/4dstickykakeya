import Theorems.Thm_StickyKakeya4_original_macro_printed_w
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalMacroWTupleReadback
open Classical Finset OriginalWWitnessCounts OriginalMacroDirectionCells OriginalMacroPrintedW
variable {P T H : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
/-- The manuscript's original five point labels and four tube labels. -/
structure Tuple (P T : Type*) where
  start : P
  mid₁ : P
  mid₂ : P
  last₁ : P
  last₂ : P
  firstTube₁ : T
  firstTube₂ : T
  lastTube₁ : T
  lastTube₂ : T
  deriving DecidableEq
def encode (w : TwoTubePathCollisionCount.Path P T × TwoTubePathCollisionCount.Path P T) : Tuple P T :=
  ⟨w.1.point₀,w.1.point₁,w.2.point₁,w.1.point₂,w.2.point₂,
    w.1.tube₁,w.2.tube₁,w.1.tube₂,w.2.tube₂⟩
def decode (w : Tuple P T) : TwoTubePathCollisionCount.Path P T × TwoTubePathCollisionCount.Path P T :=
  (⟨w.start,w.firstTube₁,w.mid₁,w.lastTube₁,w.last₁⟩,
    ⟨w.start,w.firstTube₂,w.mid₂,w.lastTube₂,w.last₂⟩)
omit [DecidableEq P] [DecidableEq T] in
private lemma decode_encode (w : TwoTubePathCollisionCount.Path P T × TwoTubePathCollisionCount.Path P T)
    (hp : w.2.point₀=w.1.point₀) : decode (encode w)=w := by
  rcases w with ⟨⟨p0,t1,p1,t1',p1'⟩,⟨p0',t2,p2,t2',p2'⟩⟩
  change p0'=p0 at hp
  subst p0'
  rfl
def tuples (I : Finset (P × T)) (height : P → H) (q : ℝ) (u : T → ℝ) (v : T → ℝ × ℝ) :
    Finset (Tuple P T) := (witnesses I height (directionCell (q/8) u v)).image encode
def OriginalConditions (I : Finset (P × T)) (height : P → H) (q : ℝ)
    (u : T → ℝ) (v : T → ℝ × ℝ) (w : Tuple P T) : Prop :=
  (w.start,w.firstTube₁) ∈ I ∧ (w.mid₁,w.firstTube₁) ∈ I ∧
    (w.mid₁,w.lastTube₁) ∈ I ∧ (w.last₁,w.lastTube₁) ∈ I ∧
    (w.start,w.firstTube₂) ∈ I ∧ (w.mid₂,w.firstTube₂) ∈ I ∧
    (w.mid₂,w.lastTube₂) ∈ I ∧ (w.last₂,w.lastTube₂) ∈ I ∧
    height w.mid₂=height w.mid₁ ∧ height w.last₂=height w.last₁ ∧
    dist (EuclideanAlignmentPatches.euclidean (directionVector u v w.lastTube₂))
      (EuclideanAlignmentPatches.euclidean (directionVector u v w.lastTube₁)) ≤ q
/-- Exact cardinality readback into genuine ORIGINAL nine-tuples. The full
 Euclidean direction restriction and all eight original incidence relations
 are proved for every tuple. No collision multiplicity is lost in encoding. -/
theorem original_nine_tuple_readback (I : Finset (P × T)) (height : P → H)
    (u : T → ℝ) (v : T → ℝ × ℝ) {q : ℝ} (hq : 0 < q) :
    (tuples I height q u v).card=(witnesses I height (directionCell (q/8) u v)).card ∧
      ∀ w ∈ tuples I height q u v, OriginalConditions I height q u v w := by
  constructor
  · apply card_image_of_injOn
    intro w hw z hz he
    have hsw := (witness_conditions I height (directionCell (q/8) u v) hw).2.2.1
    have hsz := (witness_conditions I height (directionCell (q/8) u v) hz).2.2.1
    rw [←decode_encode w hsw,←decode_encode z hsz]
    exact congrArg decode he
  · intro r hr
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hr
    obtain ⟨ha,hb,hp,hm,hl,hgap⟩ := original_full_witness_conditions I height u v hq hw
    have hpa := (TwoTubePathCollisionCount.mem_paths I w.1).mp ha
    have hpb := (TwoTubePathCollisionCount.mem_paths I w.2).mp hb
    refine ⟨hpa.1,hpa.2.1,hpa.2.2.1,hpa.2.2.2,?_,hpb.2.1,hpb.2.2.1,hpb.2.2.2,hm,hl,hgap⟩
    simpa only [encode,hp] using hpb.1
end OriginalMacroWTupleReadback
