import Theorems.Thm_StickyKakeya4_native_projector_graph_map

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeSelectedHorizontalGraphChart
open Classical Finset StickyKakeya4 NativeProjectorCellChart NativeProjectorGraphMap
open NativeHorizontalGrainSlice SelfUniform
open scoped BigOperators

/-- A total graph family with a fixed reference domain and codomain.
Off-chart planes receive zero; all selected planes use the actual inverse. -/
def totalGraph (P Q : Submodule ℝ E4) : P →ₗ[ℝ] Pᗮ :=
  if H : Module.finrank ℝ P=Module.finrank ℝ Q ∧ cell P=cell Q then
    graphMap P Q H.1 H.2 else 0

lemma totalGraph_eq (P Q : Submodule ℝ E4)
    (hd : Module.finrank ℝ P=Module.finrank ℝ Q) (hc : cell P=cell Q) :
    totalGraph P Q=graphMap P Q hd hc := by
  have H : Module.finrank ℝ P=Module.finrank ℝ Q ∧ cell P=cell Q := ⟨hd,hc⟩
  simp only [totalGraph,dif_pos H]

lemma totalGraph_norm (P Q : Submodule ℝ E4) (p : P) :
    ‖totalGraph P Q p‖ ≤ (1/4:ℝ)*‖p‖ := by
  unfold totalGraph
  split_ifs with H
  · exact graphMap_norm P Q H.1 H.2 p
  · simp only [LinearMap.zero_apply,norm_zero]
    positivity

lemma totalGraph_horizontal (P Q : Submodule ℝ E4)
    (hP : P≤heightKernel) (hQ : Q≤heightKernel) (p : P) :
    (totalGraph P Q p:E4)∈heightKernel := by
  unfold totalGraph
  split_ifs with H
  · exact graphMap_horizontal P Q H.1 H.2 hP hQ p
  · exact heightKernel.zero_mem

lemma totalGraph_characterization (P Q : Submodule ℝ E4)
    (hd : Module.finrank ℝ P=Module.finrank ℝ Q) (hc : cell P=cell Q) (v : E4) :
    v∈Q ↔ ∃p : P,(p:E4)+(totalGraph P Q p:E4)=v := by
  rw [totalGraph_eq P Q hd hc]
  exact graphMap_characterization P Q hd hc v

lemma totalGraph_variation (P Q R : Submodule ℝ E4)
    (hdQ : Module.finrank ℝ P=Module.finrank ℝ Q) (hcQ : cell P=cell Q)
    (hdR : Module.finrank ℝ P=Module.finrank ℝ R) (hcR : cell P=cell R)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hgap : ∀v∈Q,Metric.infDist v (R:Set E4) ≤ epsilon*‖v‖) (p : P) :
    ‖totalGraph P Q p-totalGraph P R p‖ ≤ 6*epsilon*‖p‖ := by
  rw [totalGraph_eq P Q hdQ hcQ,totalGraph_eq P R hdR hcR]
  exact graphMap_variation P Q R hdQ hcQ hdR hcR epsilon he hgap p

/-- Select actual whole nodes and return one total fixed-chart graph family.
The original weights, node fibers, actual reference plane, horizontal target
and graph variation are all retained explicitly. -/
theorem select_horizontal_graph_chart {A N : Type*} [DecidableEq A] [DecidableEq N]
    (S : Finset A) (hS : S.Nonempty) (w : A → ℕ) (node : A → N)
    (plane : N → Submodule ℝ E4) (k : ℕ)
    (hrank : ∀x∈S,Module.finrank ℝ (plane (node x))=k)
    (hhorizontal : ∀x∈S,plane (node x)≤heightKernel) :
    ∃x0∈S,∃T : Finset A,∃G : N → (plane (node x0) →ₗ[ℝ] (plane (node x0))ᗮ),
      T=S.filter (fun x => cell (plane (node x))=cell (plane (node x0))) ∧
      x0∈T ∧ T⊆S ∧ mass w S ≤ chartCount*mass w T ∧
      (∀x y,x∈S → y∈T → node x=node y → x∈T) ∧
      (∀y∈T,T.filter (fun x => node x=node y)=S.filter (fun x => node x=node y)) ∧
      Module.finrank ℝ (plane (node x0))=k ∧ plane (node x0)≤heightKernel ∧
      (∀n p,‖G n p‖ ≤ (1/4:ℝ)*‖p‖) ∧
      (∀x∈T,∀p,(G (node x) p:E4)∈heightKernel) ∧
      (∀x∈T,∀v : E4,v∈plane (node x) ↔ ∃p : plane (node x0),(p:E4)+(G (node x) p:E4)=v) ∧
      (∀x∈T,∀y∈T,∀epsilon : ℝ,0 ≤ epsilon →
        (∀v∈plane (node x),Metric.infDist v (plane (node y):Set E4) ≤ epsilon*‖v‖) →
        ∀p,‖G (node x) p-G (node y) p‖ ≤ 6*epsilon*‖p‖) := by
  obtain ⟨x0,hx0,T,hT,hxT,hTS,hmass,hsat,_hgap,_hlift⟩ :=
    select_whole_nodes_with_lifts S hS w node plane k hrank
  let P0 := plane (node x0)
  let G := fun n => totalGraph P0 (plane n)
  have hd (x : A) (hx : x∈T) : Module.finrank ℝ P0=Module.finrank ℝ (plane (node x)) :=
    (hrank x0 hx0).trans (hrank x (hTS hx)).symm
  have hc (x : A) (hx : x∈T) : cell P0=cell (plane (node x)) := by
    rw [hT] at hx
    exact (mem_filter.mp hx).2.symm
  refine ⟨x0,hx0,T,G,hT,hxT,hTS,hmass,hsat,?_,hrank x0 hx0,hhorizontal x0 hx0,?_,?_,?_,?_⟩
  · intro y hy
    apply Subset.antisymm
    · exact filter_subset_filter _ hTS
    · intro x hx
      obtain ⟨hxS,hxy⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hsat x y hxS hy hxy,hxy⟩
  · intro n p
    exact totalGraph_norm P0 (plane n) p
  · intro x hx p
    exact totalGraph_horizontal P0 (plane (node x)) (hhorizontal x0 hx0) (hhorizontal x (hTS hx)) p
  · intro x hx v
    exact totalGraph_characterization P0 (plane (node x)) (hd x hx) (hc x hx) v
  · intro x hx y hy epsilon he hforward p
    exact totalGraph_variation P0 (plane (node x)) (plane (node y)) (hd x hx) (hc x hx)
      (hd y hy) (hc y hy) epsilon he hforward p

end NativeSelectedHorizontalGraphChart
