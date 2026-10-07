/- UNVERIFIED staging source. No compiler or imported-axiom check has run.

Scope/manifest (2026-10-06, audit_next_configuration_transfer):
* Literal normal-grid key for ACTUAL output source-cell indices.
* Exact higher-coordinate injectivity and original/output mesh algebra.
* Global ACTUAL incidence mass + actual point-degree upper + constructed
  key uniformity + inherited coarse-cover UPPER => occupied class LOWER.
* Dense higher X and higher Y coarse-class lower are conclusions, not inputs.

This file does NOT construct the remembered output source, admit a pruned
source as native, identify raw edges with a deduplicated output graph, prove
the inherited all-radius halo-cover upper, select a common original height,
or pay its constants. Those obligations remain with the actual-source caller.

For a source of thickness sigma the physical source-cell mesh is sigma/2.
The first planar normalized scalar mesh is rho/tau. With d=8rho,
w=tau/4096, N*w=64, and sigma=N*d/64, the physical parent multiplier
N/512 sends that scalar mesh to sigma/64. Thus the source cells coarsen
the FULL scalar alphabet by a fixed factor; they do not select one strip.

Expected application at output mesh delta (fixed factors absorbed):
  |E| >= a delta^-4, degree(point) <= U delta^-kappa,
  #keys(time,Y_r) <= C delta^-1 r^(-(1-kappa)),
  #global fine X <= CX delta^-2.
The cross inequalities below give Y class lower
  a/(Q^2 C U CX) (r/delta)^(1-kappa)
and X fiber lower a/(Q^2 C U) delta^-2.
At the actual initial exponent t=2-kappa-s, charge delta^(-(1-s))
in BOTH the coarse-cover upper and the resulting lower constant.
Finite scheduled class bounds still need the existing radius-interpolation
and metric/grid readers before calling ADBounds_of_asymmetric_counts.

Declarations: higherXIndex, higherYIndex, higherKey, coarseHigherKey,
higherQuotient, higherYIndex_readback, higher_coordinates_injective,
higherX_fiber_card, aligned_normal_scale, aligned_mesh_in_source,
subset_card_le_point_cap, occupied_class_point_lower,
occupied_class_label_lower, dense_higher_X, higher_Y_class_lower.
-/
import Theorems.Thm_StickyKakeya4_native_finite_slice_homogeneity
import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeActualHigherKeyPopulationDraft1955
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeJointUniformCoarseRelations NativeFiniteSliceHomogeneity
open scoped BigOperators

def higherXIndex (k : Index) : Fin 2 → ℤ :=
  fun j => k j.castSucc.castSucc

/-- Floor of the actual scalar quotient in source-cell mesh units. The
fields are evaluated at the literal source-cell time, never rawHeight. -/
def higherYIndex (C F : ℤ → ℝ) (k : Index) : ℤ :=
  k 2 + ⌊(1/2:ℝ)-C (k 3)*((k 0:ℝ)+1/2)-F (k 3)*((k 1:ℝ)+1/2)⌋

def higherKey (C F : ℤ → ℝ) (k : Index) : ℤ × ℤ :=
  (k 3,higherYIndex C F k)

def coarseHigherKey (C F : ℤ → ℝ) (R : ℕ) (k : Index) : ℤ × ℤ :=
  (k 3,higherYIndex C F k/(R:ℤ))

def higherQuotient (mu : ℝ) (C F : ℤ → ℝ) (k : Index) : ℝ :=
  mu*((k 2:ℝ)+1/2-C (k 3)*((k 0:ℝ)+1/2)-F (k 3)*((k 1:ℝ)+1/2))

theorem higherYIndex_readback (mu : ℝ) (hmu : 0<mu)
    (C F : ℤ → ℝ) (k : Index) :
    ⌊higherQuotient mu C F k/mu⌋=higherYIndex C F k := by
  have he : higherQuotient mu C F k/mu=(k 2:ℝ)+
      ((1/2:ℝ)-C (k 3)*((k 0:ℝ)+1/2)-F (k 3)*((k 1:ℝ)+1/2)) := by
    unfold higherQuotient
    field_simp [hmu.ne']
    <;> ring
  rw [he,Int.floor_intCast_add]
  rfl

theorem higher_coordinates_injective (C F : ℤ → ℝ) {k l : Index}
    (hY : higherKey C F k=higherKey C F l)
    (hX : higherXIndex k=higherXIndex l) : k=l := by
  have h0 : k 0=l 0 := by simpa only [higherXIndex] using congrFun hX 0
  have h1 : k 1=l 1 := by simpa only [higherXIndex] using congrFun hX 1
  have h3 : k 3=l 3 := congrArg Prod.fst hY
  have h2 : k 2=l 2 := by
    have hh := congrArg Prod.snd hY
    change higherYIndex C F k=higherYIndex C F l at hh
    simp only [higherYIndex,h0,h1,h3] at hh
    omega
  funext j
  fin_cases j <;> assumption

/-- Distinct source points in one literal higher-Y fiber are exactly
distinct higher-X indices. There is no point multiplicity hidden here. -/
theorem higherX_fiber_card (P : Finset Index) (C F : ℤ → ℝ) (v : ℤ × ℤ) :
    ((P.filter (fun k => higherKey C F k=v)).image higherXIndex).card=
      (P.filter (fun k => higherKey C F k=v)).card := by
  apply card_image_iff.mpr
  intro k hk l hl he
  exact higher_coordinates_injective C F
    ((mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm) he

theorem aligned_normal_scale (N tau w : ℝ) (hN : N*w=64) (hTau : tau=4096*w) :
    (N/512)*tau=512 := by
  calc
    _ = 8*(N*w) := by rw [hTau]; ring
    _ = 512 := by rw [hN]; norm_num

theorem aligned_mesh_in_source (N rho tau d sigma : ℝ) (hTau : tau≠0)
    (hd : d=8*rho) (hSigma : sigma=N*d/64) :
    (N/512)*tau*(rho/tau)=sigma/64 := by
  rw [hSigma,hd]
  field_simp [hTau]
  <;> ring

/-- Sum the actual point degrees. E and A are literal sets of output
tube/cell incidences, not older antecedent relations. -/
theorem subset_card_le_point_cap {n : ℕ}
    (E A : Finset (Fin n × Index)) (hAE : A⊆E) (U : ℝ)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U) :
    (A.card:ℝ)≤U*(A.image Prod.snd).card := by
  have he : (A.card:ℝ)=∑k∈A.image Prod.snd,
      ((A.filter (fun e => e.2=k)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image Prod.snd A
  rw [he]
  calc
    _ ≤ ∑_k∈A.image Prod.snd,U := by
      apply sum_le_sum
      intro k _hk
      exact (show ((A.filter (fun e => e.2=k)).card:ℝ)≤
        (E.filter (fun e => e.2=k)).card by
          exact_mod_cast card_le_card (filter_subset_filter _ hAE)).trans (hDegree k)
    _ = _ := by simp [mul_comm]

/-- A global occupied-key UPPER bound and actual graph mass force a
LOWER number of actual points in every occupied uniform class. -/
theorem occupied_class_point_lower {n : ℕ} {K : Type*} [DecidableEq K]
    (E : Finset (Fin n × Index)) (key : Index → K) (Q : ℕ)
    (H : HasUniformFibers E Q (fun e => key e.2))
    (mass cover U : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image key).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (v : K) (hv : v∈(E.image Prod.snd).image key) :
    mass≤(Q:ℝ)^2*cover*U*((E.filter (fun e => key e.2=v)).image Prod.snd).card := by
  let A := E.filter (fun e => key e.2=v)
  have hv' : v∈E.image (fun e => key e.2) := by
    simpa only [image_image,Function.comp_def] using hv
  have hAvg := (fiber_card_average_cross E (fun e => key e.2) (Q^2) H v hv').2
  have hAvgR : (E.card:ℝ)≤(Q:ℝ)^2*(A.card:ℝ)*
      (((E.image Prod.snd).image key).card:ℝ) := by
    simpa only [A,image_image,Function.comp_def,Nat.cast_mul,Nat.cast_pow] using
      (show (E.card:ℝ)≤((Q^2*(E.filter (fun e => key e.2=v)).card*
        (E.image (fun e => key e.2)).card:ℕ):ℝ) by exact_mod_cast hAvg)
  have hPoints := subset_card_le_point_cap E A (filter_subset _ _) U hDegree
  calc
    mass≤E.card := hMass
    _ ≤ (Q:ℝ)^2*(A.card:ℝ)*(((E.image Prod.snd).image key).card:ℝ) := hAvgR
    _ ≤ (Q:ℝ)^2*(A.card:ℝ)*cover :=
      mul_le_mul_of_nonneg_left hCover (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    _ ≤ (Q:ℝ)^2*(U*(A.image Prod.snd).card)*cover :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPoints (sq_nonneg _)) hCover0
    _ = _ := by ring

/-- The actual point-to-label capacity is the only extra cost needed to
convert the preceding LOWER to any literal fine-coordinate alphabet. -/
theorem occupied_class_label_lower {n : ℕ} {K Y : Type*}
    [DecidableEq K] [DecidableEq Y]
    (E : Finset (Fin n × Index)) (key : Index → K) (label : Index → Y) (Q : ℕ)
    (H : HasUniformFibers E Q (fun e => key e.2))
    (mass cover U capacity : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image key).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (v : K) (hv : v∈(E.image Prod.snd).image key)
    (hCapacity : ∀y∈((E.filter (fun e => key e.2=v)).image Prod.snd).image label,
      ((((E.filter (fun e => key e.2=v)).image Prod.snd).filter
        (fun k => label k=y)).card:ℝ)≤capacity) :
    mass≤(Q:ℝ)^2*cover*U*capacity*
      (((E.filter (fun e => key e.2=v)).image Prod.snd).image label).card := by
  let P := (E.filter (fun e => key e.2=v)).image Prod.snd
  have hCap : (P.card:ℝ)≤capacity*(P.image label).card := by
    have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images
      P id label capacity (fun y hy => by simpa only [image_id'] using hCapacity y hy)
    simpa only [image_id'] using hh
  have hLower := occupied_class_point_lower E key Q H mass cover U hCover0 hU
    hMass hCover hDegree v hv
  calc
    mass≤(Q:ℝ)^2*cover*U*P.card := hLower
    _ ≤ (Q:ℝ)^2*cover*U*(capacity*(P.image label).card) :=
      mul_le_mul_of_nonneg_left hCap (mul_nonneg (mul_nonneg (sq_nonneg _) hCover0) hU)
    _ = _ := by ring

/-- Higher X density is derived on the actual output cells. -/
theorem dense_higher_X {n : ℕ} (E : Finset (Fin n × Index))
    (C F : ℤ → ℝ) (Q : ℕ)
    (H : HasUniformFibers E Q (fun e => higherKey C F e.2))
    (mass cover U : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image (higherKey C F)).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (v : ℤ × ℤ) (hv : v∈(E.image Prod.snd).image (higherKey C F)) :
    mass≤(Q:ℝ)^2*cover*U*
      (((E.filter (fun e => higherKey C F e.2=v)).image Prod.snd).image higherXIndex).card := by
  have hLower := occupied_class_point_lower E (higherKey C F) Q H mass cover U
    hCover0 hU hMass hCover hDegree v hv
  have hInj : Set.InjOn higherXIndex
      ↑((E.filter (fun e => higherKey C F e.2=v)).image Prod.snd) := by
    intro k hk l hl he
    obtain ⟨e,heE,rfl⟩ := mem_image.mp hk
    obtain ⟨f,hfE,rfl⟩ := mem_image.mp hl
    exact higher_coordinates_injective C F
      ((mem_filter.mp heE).2.trans (mem_filter.mp hfE).2.symm) he
  rw [card_image_iff.mpr hInj]
  exact hLower

/-- Every occupied higher-Y r-class contains many distinct fine higher-Y
labels. The only horizontal input is the GLOBAL trivial X packing upper. -/
theorem higher_Y_class_lower {n : ℕ} (E : Finset (Fin n × Index))
    (C F : ℤ → ℝ) (R Q : ℕ)
    (H : HasUniformFibers E Q (fun e => coarseHigherKey C F R e.2))
    (mass cover U Xcap : ℝ) (hCover0 : 0≤cover) (hU : 0≤U)
    (hMass : mass≤E.card)
    (hCover : (((E.image Prod.snd).image (coarseHigherKey C F R)).card:ℝ)≤cover)
    (hDegree : ∀k,((E.filter (fun e => e.2=k)).card:ℝ)≤U)
    (hXcap : (((E.image Prod.snd).image higherXIndex).card:ℝ)≤Xcap)
    (v : ℤ × ℤ) (hv : v∈(E.image Prod.snd).image (coarseHigherKey C F R)) :
    mass≤(Q:ℝ)^2*cover*U*Xcap*
      (((E.filter (fun e => coarseHigherKey C F R e.2=v)).image Prod.snd).image
        (higherYIndex C F)).card := by
  apply occupied_class_label_lower E (coarseHigherKey C F R) (higherYIndex C F) Q H
    mass cover U Xcap hCover0 hU hMass hCover hDegree v hv
  intro y _hy
  let P := (E.filter (fun e => coarseHigherKey C F R e.2=v)).image Prod.snd
  let W := P.filter (fun k => higherYIndex C F k=y)
  have hTime : ∀k∈P,k 3=v.1 := by
    intro k hk
    obtain ⟨e,he,rfl⟩ := mem_image.mp hk
    exact congrArg Prod.fst (mem_filter.mp he).2
  have hKey : ∀k∈W,higherKey C F k=(v.1,y) := by
    intro k hk
    exact Prod.ext (hTime k (mem_filter.mp hk).1) (mem_filter.mp hk).2
  have hCard : (W.image higherXIndex).card=W.card := by
    apply card_image_iff.mpr
    intro k hk l hl he
    exact higher_coordinates_injective C F ((hKey k hk).trans (hKey l hl).symm) he
  have hSub : W⊆E.image Prod.snd :=
    (filter_subset _ _).trans (image_subset_image (filter_subset _ _))
  change (W.card:ℝ)≤Xcap
  rw [←hCard]
  exact (show ((W.image higherXIndex).card:ℝ)≤((E.image Prod.snd).image higherXIndex).card by
    exact_mod_cast card_le_card (image_subset_image hSub)).trans hXcap

end NativeActualHigherKeyPopulationDraft1955
