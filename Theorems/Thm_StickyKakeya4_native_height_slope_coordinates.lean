import Theorems.Thm_StickyKakeya4_native_horizontal_graph_coordinates
import Theorems.Thm_StickyKakeya4_native_parent_height_alignment

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeHeightSlopeCoordinates
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCompatibleAngularCandidates
open NativeHorizontalGrainSlice NativeProjectorCellChart NativeProjectorGraphMap
open NativeSelectedHorizontalGraphChart NativeHorizontalGraphCoordinates NativeParentHeightAlignment SelfUniform
open scoped BigOperators Matrix.Norms.Elementwise

def nodeSlope (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (Q : Submodule ℝ E4) (hQ : Q≤heightKernel) : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ :=
  slopeMatrix P hP ell hell hell4 hd (totalGraph P Q) (totalGraph_horizontal P Q hP hQ)

lemma nodeSlope_norm (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (Q : Submodule ℝ E4) (hQ : Q≤heightKernel) : ‖nodeSlope P hP ell hell hell4 hd Q hQ‖ ≤ (1/4:ℝ) :=
  slopeMatrix_norm P hP ell hell hell4 hd (totalGraph P Q) (totalGraph_horizontal P Q hP hQ)
    (1/4) (by norm_num) (totalGraph_norm P Q)

lemma nodeSlope_variation (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (Q R : Submodule ℝ E4) (hQ : Q≤heightKernel) (hR : R≤heightKernel)
    (hdQ : Module.finrank ℝ P=Module.finrank ℝ Q) (hcQ : cell P=cell Q)
    (hdR : Module.finrank ℝ P=Module.finrank ℝ R) (hcR : cell P=cell R)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hgap : ∀v∈Q,Metric.infDist v (R:Set E4) ≤ epsilon*‖v‖) :
    ‖nodeSlope P hP ell hell hell4 hd Q hQ-nodeSlope P hP ell hell hell4 hd R hR‖ ≤ 6*epsilon :=
  slopeMatrix_variation P hP ell hell hell4 hd (totalGraph P Q) (totalGraph P R)
    (totalGraph_horizontal P Q hP hQ) (totalGraph_horizontal P R hP hR)
    (6*epsilon) (by positivity) (totalGraph_variation P Q R hdQ hcQ hdR hcR epsilon he hgap)

/-- The matrix acts on actual Euclidean coordinate vectors. -/
def matrixVector {a b : ℕ} (M : Matrix (Fin b) (Fin a) ℝ) (x : EuclideanSpace ℝ (Fin a)) :
    EuclideanSpace ℝ (Fin b) := WithLp.toLp 2 (M.mulVec (fun j => x j))

lemma nodeSlope_action (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (Q : Submodule ℝ E4) (hQ : Q≤heightKernel) (x : EuclideanSpace ℝ (Fin (ell-1))) :
    matrixVector (nodeSlope P hP ell hell hell4 hd Q hQ) x=
      slopeMap P hP ell hell hell4 hd (totalGraph P Q) (totalGraph_horizontal P Q hP hQ) x := by
  ext i
  exact congrFun (slopeMatrix_action P hP ell hell hell4 hd (totalGraph P Q)
    (totalGraph_horizontal P Q hP hQ) x) i

/-- Exact coordinate readback for the linear node plane; raw thick grains
are not asserted to lie on this graph. -/
lemma nodeSlope_graph (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (Q : Submodule ℝ E4) (hQ : Q≤heightKernel)
    (hdQ : Module.finrank ℝ P=Module.finrank ℝ Q) (hcQ : cell P=cell Q) (v : E4) :
    v∈Q ↔ ∃x : EuclideanSpace ℝ (Fin (ell-1)),
      ((domainBasis P ell hd).repr.symm x:P)+
        (((normalBasis P hP ell hell hell4 hd).repr.symm
          (matrixVector (nodeSlope P hP ell hell hell4 hd Q hQ) x):normalSpace P):E4)=v := by
  have hemb (x : EuclideanSpace ℝ (Fin (ell-1))) :
      (((normalBasis P hP ell hell hell4 hd).repr.symm
          (matrixVector (nodeSlope P hP ell hell hell4 hd Q hQ) x):normalSpace P):E4)=
        (totalGraph P Q ((domainBasis P ell hd).repr.symm x):E4) := by
    rw [nodeSlope_action]
    exact coordinate_graph_readback P hP ell hell hell4 hd (totalGraph P Q)
      (totalGraph_horizontal P Q hP hQ) x
  rw [totalGraph_characterization P Q hdQ hcQ]
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨(domainBasis P ell hd).repr p,?_⟩
    rw [hemb,LinearIsometryEquiv.symm_apply_apply]
    exact hp
  · rintro ⟨x,hx⟩
    exact ⟨(domainBasis P ell hd).repr.symm x,by rwa [hemb] at hx⟩

lemma fine_heightNode_mem (B : Finset Index) (m : ℕ) (t : ℤ)
    (ht : t∈B.image (fun u => u (3:Fin 4))) : heightNode B m m t∈B := by
  obtain ⟨u,hu,he⟩ := mem_image.mp ht
  have hx : ∃u∈B,spatialAncestor m m u (3:Fin 4)=t := by
    exact ⟨u,hu,by simpa only [spatialAncestor_self] using he⟩
  have hh := (heightNode_occupied B m m t hx).1
  have hself : spatialAncestor m m=id := funext (spatialAncestor_self m)
  simpa only [hself,image_id] using hh

/-- A genuine function of literal raw height. It uses the selected actual
node on occupied heights and zero elsewhere. -/
def heightSlope (B : Finset Index) (m : ℕ)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (plane : Index → Submodule ℝ E4) (hplane : ∀u∈B,plane u≤heightKernel)
    (t : ℤ) : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ :=
  if ht : t∈B.image (fun u => u (3:Fin 4)) then
    nodeSlope P hP ell hell hell4 hd (plane (heightNode B m m t))
      (hplane _ (fine_heightNode_mem B m t ht)) else 0

lemma heightSlope_zero_off (B : Finset Index) (m : ℕ)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (plane : Index → Submodule ℝ E4) (hplane : ∀u∈B,plane u≤heightKernel)
    (t : ℤ) (ht : t∉B.image (fun u => u (3:Fin 4))) :
    heightSlope B m P hP ell hell hell4 hd plane hplane t=0 := by
  simp only [heightSlope,dif_neg ht]

lemma heightSlope_norm (B : Finset Index) (m : ℕ)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (plane : Index → Submodule ℝ E4) (hplane : ∀u∈B,plane u≤heightKernel) (t : ℤ) :
    ‖heightSlope B m P hP ell hell hell4 hd plane hplane t‖ ≤ (1/4:ℝ) := by
  unfold heightSlope
  split_ifs with ht
  · exact nodeSlope_norm P hP ell hell hell4 hd _ _
  · norm_num

lemma heightSlope_readback (B : Finset Index) (m : ℕ)
    (Halign : ∀u v,u∈B→v∈B→u (3:Fin 4)=v (3:Fin 4)→u=v)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (plane : Index → Submodule ℝ E4) (hplane : ∀u∈B,plane u≤heightKernel)
    (u : Index) (hu : u∈B) (hQ : plane u≤heightKernel) :
    heightSlope B m P hP ell hell hell4 hd plane hplane (u (3:Fin 4))=
      nodeSlope P hP ell hell hell4 hd (plane u) hQ := by
  have hnode := fine_heightNode_readback B m
    (by simpa only [spatialAncestor_self] using Halign) u hu
  have ht : u (3:Fin 4)∈B.image (fun v => v (3:Fin 4)) := mem_image_of_mem _ hu
  simp only [heightSlope,dif_pos ht]
  congr 1
  exact congrArg plane hnode

/-- The actual height factor preserves the exact incoming plane-gap bound. -/
lemma heightSlope_variation (B : Finset Index) (m : ℕ)
    (Halign : ∀u v,u∈B→v∈B→u (3:Fin 4)=v (3:Fin 4)→u=v)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (plane : Index → Submodule ℝ E4) (hplane : ∀u∈B,plane u≤heightKernel)
    (hrank : ∀u∈B,Module.finrank ℝ P=Module.finrank ℝ (plane u))
    (hcell : ∀u∈B,cell P=cell (plane u))
    (u v : Index) (hu : u∈B) (hv : v∈B) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hgap : ∀x∈plane u,Metric.infDist x (plane v:Set E4) ≤ epsilon*‖x‖) :
    ‖heightSlope B m P hP ell hell hell4 hd plane hplane (u (3:Fin 4))-
      heightSlope B m P hP ell hell hell4 hd plane hplane (v (3:Fin 4))‖ ≤ 6*epsilon := by
  rw [heightSlope_readback B m Halign P hP ell hell hell4 hd plane hplane u hu (hplane u hu),
    heightSlope_readback B m Halign P hP ell hell hell4 hd plane hplane v hv (hplane v hv)]
  exact nodeSlope_variation P hP ell hell hell4 hd (plane u) (plane v) (hplane u hu) (hplane v hv)
    (hrank u hu) (hcell u hu) (hrank v hv) (hcell v hv) epsilon he hgap

/-- Apply the proved whole-node chart selector, then construct the actual
height-indexed coordinate matrices. No common reference chart is a premise. -/
theorem exists_height_slope_chart (S : Finset Index) (hS : S.Nonempty) (w : Index → ℕ)
    (m ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (plane : Index → Submodule ℝ E4)
    (hrank : ∀u∈S,Module.finrank ℝ (plane u)=ell-1)
    (hhorizontal : ∀u∈S,plane u≤heightKernel)
    (Halign : ∀u v,u∈S→v∈S→u (3:Fin 4)=v (3:Fin 4)→u=v) :
    ∃u0∈S,∃B : Finset Index,∃hB : B⊆S,∃hP : plane u0≤heightKernel,
      ∃hd : Module.finrank ℝ (plane u0)=ell-1,
      ∃f : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ,
      B=S.filter (fun u => cell (plane u)=cell (plane u0)) ∧ u0∈B ∧
      mass w S ≤ chartCount*mass w B ∧
      (∀t,t∉B.image (fun u => u (3:Fin 4))→f t=0) ∧
      (∀t,‖f t‖ ≤ (1/4:ℝ)) ∧
      (∀u (hu : u∈B),f (u (3:Fin 4))=nodeSlope (plane u0) hP ell hell hell4 hd (plane u) (hhorizontal u (hB hu))) ∧
      (∀u∈B,∀v : E4,v∈plane u ↔ ∃x : EuclideanSpace ℝ (Fin (ell-1)),
        ((domainBasis (plane u0) ell hd).repr.symm x:plane u0)+
          (((normalBasis (plane u0) hP ell hell hell4 hd).repr.symm (matrixVector (f (u (3:Fin 4))) x):normalSpace (plane u0)):E4)=v) ∧
      (∀u∈B,∀v∈B,∀epsilon : ℝ,0 ≤ epsilon →
        (∀x∈plane u,Metric.infDist x (plane v:Set E4) ≤ epsilon*‖x‖) →
        ‖f (u (3:Fin 4))-f (v (3:Fin 4))‖ ≤ 6*epsilon) := by
  obtain ⟨u0,hu0,B,G,hB,huB,hBS,hmass,_hsat,_hfib,_hrank,_hhoriz,_hnorm,_hGhor,_hgraph,_hvar⟩ :=
    select_horizontal_graph_chart S hS w id plane (ell-1) hrank hhorizontal
  have hP := hhorizontal u0 hu0
  have hd := hrank u0 hu0
  have hplanes : ∀u∈B,plane u≤heightKernel := fun u hu => hhorizontal u (hBS hu)
  have hRanks : ∀u∈B,Module.finrank ℝ (plane u0)=Module.finrank ℝ (plane u) :=
    fun u hu => hd.trans (hrank u (hBS hu)).symm
  have hCells : ∀u∈B,cell (plane u0)=cell (plane u) := by
    intro u hu
    rw [hB] at hu
    exact (mem_filter.mp hu).2.symm
  have hAlign : ∀u v,u∈B→v∈B→u (3:Fin 4)=v (3:Fin 4)→u=v :=
    fun u v hu hv => Halign u v (hBS hu) (hBS hv)
  let f := heightSlope B m (plane u0) hP ell hell hell4 hd plane hplanes
  refine ⟨u0,hu0,B,hBS,hP,hd,f,hB,huB,hmass,?_,?_,?_,?_,?_⟩
  · exact heightSlope_zero_off B m (plane u0) hP ell hell hell4 hd plane hplanes
  · exact heightSlope_norm B m (plane u0) hP ell hell hell4 hd plane hplanes
  · intro u hu
    exact heightSlope_readback B m hAlign (plane u0) hP ell hell hell4 hd plane hplanes u hu (hplanes u hu)
  · intro u hu v
    have hread := heightSlope_readback B m hAlign (plane u0) hP ell hell hell4 hd plane hplanes u hu (hplanes u hu)
    change v∈plane u ↔ _
    dsimp only [f]
    rw [hread]
    exact nodeSlope_graph (plane u0) hP ell hell hell4 hd (plane u) (hplanes u hu) (hRanks u hu) (hCells u hu) v
  · intro u hu v hv epsilon he hgap
    exact heightSlope_variation B m hAlign (plane u0) hP ell hell hell4 hd plane hplanes
      hRanks hCells u v hu hv epsilon he hgap

end NativeHeightSlopeCoordinates
