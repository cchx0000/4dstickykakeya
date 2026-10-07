import Theorems.Thm_StickyKakeya4_native_lipschitz_height_edge_lift
import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeLipschitzHeightFiberReadback
open Classical Finset NativeMatrixHeightWholePoint NativeLipschitzCoarseHeightSelection
open NativeJointUniformCoarseRelations

/-- Full-bin closure from select_original_edges keeps every exact old
height fiber of its immediate input. This is an identity, not an AD claim. -/
theorem height_fiber_eq {E P : Type*} [DecidableEq P]
    (A : Finset E) (point : E → P) (S : Finset P) (height : P → ℝ)
    (R origin : ℝ) (q : ℕ)
    (hclosed : ∀p∈A.image point,∀v∈S,
      fine R origin q (height p)=fine R origin q (height v) → p∈S)
    (x : E) (hx : x∈edgeLift A point S) :
    (edgeLift A point S).filter (fun y => height (point y)=height (point x))=
      A.filter (fun y => height (point y)=height (point x)) := by
  ext y
  simp only [edgeLift,mem_filter]
  constructor
  · exact fun hy => ⟨hy.1.1,hy.2⟩
  · rintro ⟨hy,he⟩
    refine ⟨⟨hy,?_⟩,he⟩
    exact hclosed (point y) (mem_image_of_mem point hy) (point x)
      (mem_filter.mp hx).2 (congrArg (fine R origin q) he)

/-- Every geometric image of a retained exact-height fiber is unchanged
from the immediate input. An earlier arbitrary cut is not undone. -/
theorem height_image_eq {E P X : Type*} [DecidableEq P] [DecidableEq X]
    (A : Finset E) (point : E → P) (S : Finset P) (height : P → ℝ)
    (R origin : ℝ) (q : ℕ)
    (hclosed : ∀p∈A.image point,∀v∈S,
      fine R origin q (height p)=fine R origin q (height v) → p∈S)
    (x : E) (hx : x∈edgeLift A point S) (imageMap : E → X) :
    ((edgeLift A point S).filter (fun y => height (point y)=height (point x))).image imageMap=
      (A.filter (fun y => height (point y)=height (point x))).image imageMap := by
  rw [height_fiber_eq A point S height R origin q hclosed x hx]

/-- An installed label that determines the original height also keeps
its entire immediate-input equality fiber under the actual bin cut. -/
theorem label_fiber_eq {E P X : Type*} [DecidableEq P] [DecidableEq X]
    (A : Finset E) (point : E → P) (S : Finset P) (height : P → ℝ)
    (R origin : ℝ) (q : ℕ)
    (hclosed : ∀p∈A.image point,∀v∈S,
      fine R origin q (height p)=fine R origin q (height v) → p∈S)
    (label : E → X)
    (hheight : ∀x∈A,∀y∈A,label x=label y → height (point x)=height (point y))
    (x : E) (hx : x∈edgeLift A point S) :
    (edgeLift A point S).filter (fun y => label y=label x)=A.filter (fun y => label y=label x) := by
  ext y
  simp only [edgeLift,mem_filter]
  constructor
  · exact fun hy => ⟨hy.1.1,hy.2⟩
  · rintro ⟨hy,he⟩
    refine ⟨⟨hy,?_⟩,he⟩
    have ht := hheight y hy x (mem_filter.mp hx).1 he
    exact hclosed (point y) (mem_image_of_mem point hy) (point x)
      (mem_filter.mp hx).2 (congrArg (fine R origin q) ht)

/-- Whole old-height fibers restrict the already installed uniformity
with its exact old radix. No uniformity of newly merged labels is asserted. -/
theorem uniformity {E P X : Type*} [DecidableEq E] [DecidableEq P] [DecidableEq X]
    (A : Finset E) (point : E → P) (S : Finset P) (height : P → ℝ)
    (R origin : ℝ) (q Q : ℕ)
    (hclosed : ∀p∈A.image point,∀v∈S,
      fine R origin q (height p)=fine R origin q (height v) → p∈S)
    (label : E → X)
    (hheight : ∀x∈A,∀y∈A,label x=label y → height (point x)=height (point y))
    (HU : HasUniformFibers A Q label) : HasUniformFibers (edgeLift A point S) Q label := by
  intro x hx y hy
  rw [label_fiber_eq A point S height R origin q hclosed label hheight x hx,
    label_fiber_eq A point S height R origin q hclosed label hheight y hy]
  exact HU x (mem_filter.mp hx).1 y (mem_filter.mp hy).1

/-- Direct source-reader form: use the actual coarse-Y height coordinate
or the literal configured point's fourth coordinate as `readHeight`. -/
theorem label_fiber_eq_of_height_readback {E P X : Type*} [DecidableEq P] [DecidableEq X]
    (A : Finset E) (point : E → P) (S : Finset P) (height : P → ℝ)
    (R origin : ℝ) (q : ℕ)
    (hclosed : ∀p∈A.image point,∀v∈S,
      fine R origin q (height p)=fine R origin q (height v) → p∈S)
    (label : E → X) (readHeight : X → ℝ)
    (hread : ∀x∈A,height (point x)=readHeight (label x))
    (x : E) (hx : x∈edgeLift A point S) :
    (edgeLift A point S).filter (fun y => label y=label x)=A.filter (fun y => label y=label x) := by
  apply label_fiber_eq A point S height R origin q hclosed label ?_ x hx
  intro y hy z hz he
  rw [hread y hy,hread z hz,he]

/-- This is the exact same-radix attachment for either existing actual
height reader; it does not require another finite refinement. -/
theorem uniformity_of_height_readback {E P X : Type*} [DecidableEq E] [DecidableEq P] [DecidableEq X]
    (A : Finset E) (point : E → P) (S : Finset P) (height : P → ℝ)
    (R origin : ℝ) (q Q : ℕ)
    (hclosed : ∀p∈A.image point,∀v∈S,
      fine R origin q (height p)=fine R origin q (height v) → p∈S)
    (label : E → X) (readHeight : X → ℝ)
    (hread : ∀x∈A,height (point x)=readHeight (label x))
    (HU : HasUniformFibers A Q label) : HasUniformFibers (edgeLift A point S) Q label := by
  apply uniformity A point S height R origin q Q hclosed label ?_ HU
  intro y hy z hz he
  rw [hread y hy,hread z hz,he]

/-- The actual configured-time sampler. Its argument is the original
translated-height label; it is not the unsnapped physical time. -/
def configuredTime (base : ℝ) (R0 : ℕ) (oldHeight : ℤ) : ℝ :=
  (base/512)*(((oldHeight/((8*R0:ℕ):ℤ):ℤ):ℝ)+1/2)

/-- Explicit source specialization of the height factorization. Thus the
height cut may follow a full planar Y-prime selection without splitting
any surviving original translated-height slice. -/
theorem configured_height_fiber_eq {E P : Type*} [DecidableEq P]
    (A : Finset E) (point : E → P) (S : Finset P) (oldHeight : P → ℤ)
    (base : ℝ) (R0 : ℕ) (R origin : ℝ) (q : ℕ)
    (hclosed : ∀p∈A.image point,∀v∈S,
      fine R origin q (configuredTime base R0 (oldHeight p))=
        fine R origin q (configuredTime base R0 (oldHeight v)) → p∈S)
    (x : E) (hx : x∈edgeLift A point S) :
    (edgeLift A point S).filter (fun y => oldHeight (point y)=oldHeight (point x))=
      A.filter (fun y => oldHeight (point y)=oldHeight (point x)) := by
  exact label_fiber_eq_of_height_readback A point S
    (fun p => configuredTime base R0 (oldHeight p)) R origin q hclosed
    (fun y => oldHeight (point y)) (configuredTime base R0) (fun _ _ => rfl) x hx

/-- The literal geometric Y-prime image on each retained old height is
unchanged from the immediate input of the configured-time cut. -/
theorem configured_height_image_eq {E P X : Type*} [DecidableEq P] [DecidableEq X]
    (A : Finset E) (point : E → P) (S : Finset P) (oldHeight : P → ℤ)
    (base : ℝ) (R0 : ℕ) (R origin : ℝ) (q : ℕ)
    (hclosed : ∀p∈A.image point,∀v∈S,
      fine R origin q (configuredTime base R0 (oldHeight p))=
        fine R origin q (configuredTime base R0 (oldHeight v)) → p∈S)
    (x : E) (hx : x∈edgeLift A point S) (Y : E → X) :
    ((edgeLift A point S).filter (fun y => oldHeight (point y)=oldHeight (point x))).image Y=
      (A.filter (fun y => oldHeight (point y)=oldHeight (point x))).image Y := by
  rw [configured_height_fiber_eq A point S oldHeight base R0 R origin q hclosed x hx]

end NativeLipschitzHeightFiberReadback
