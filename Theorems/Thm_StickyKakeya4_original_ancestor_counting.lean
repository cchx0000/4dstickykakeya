import Theorems.Thm_StickyKakeya4_original_tube_ancestor_saturation
import Theorems.Thm_StickyKakeya4_original_height_interval_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalAncestorCounting
open Classical
open scoped BigOperators
open OriginalTubeAncestorSaturation

/-- Choose one ACTUAL original label in each occupied cell, preserving all
 occupied cells and proving injectivity of the cell map on the selected labels. -/
theorem exists_original_cell_representatives {P K : Type*} [DecidableEq P] [DecidableEq K]
    (E : Finset P) (cell : P → K) :
    ∃ S : Finset P, S ⊆ E ∧ S.image cell=E.image cell ∧
      Set.InjOn cell (↑S) ∧ S.card=(E.image cell).card := by
  let lift : {k // k ∈ E.image cell} → P := fun k => Classical.choose (Finset.mem_image.mp k.property)
  have hlift : ∀ k, lift k ∈ E ∧ cell (lift k)=k.val :=
    fun k => Classical.choose_spec (Finset.mem_image.mp k.property)
  let S := (E.image cell).attach.image lift
  have hS : S ⊆ E := by
    intro p hp
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
    exact (hlift k).1
  have himage : S.image cell=E.image cell := by
    apply Finset.Subset.antisymm
    · exact Finset.image_subset_image hS
    · intro k hk
      refine Finset.mem_image.mpr ⟨lift ⟨k,hk⟩,?_,(hlift _).2⟩
      exact Finset.mem_image_of_mem lift (Finset.mem_attach _ _)
  have hinj : Set.InjOn cell (↑S) := by
    intro p hp q hq heq
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
    have hkl : k=l := Subtype.ext (by simpa only [(hlift k).2,(hlift l).2] using heq)
    rw [hkl]
  exact ⟨S,hS,himage,hinj,by rw [← himage,Finset.card_image_iff.mpr hinj]⟩

variable {P T K D U : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K]
  [DecidableEq D] [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- Local labels retain their original identity, point and actual fine direction. -/
def nearDirections (Phi : P → Finset D) (fine : D → U) (center : P → U)
    (rho : ℝ) (p : P) : Finset D :=
  (Phi p).filter (fun d => ‖fine d-center p‖ ≤ rho)

def originalPairs (E : Finset P) (Phi : P → Finset D) (fine : D → U)
    (center : P → U) (rho : ℝ) : Finset (Sigma fun _ : P => D) :=
  E.sigma (nearDirections Phi fine center rho)

def pairAncestor (ancestor : T → K) (realizer : P → D → T)
    (w : Sigma fun _ : P => D) : K := ancestor (realizer w.1 w.2)

def occupiedAncestors (E : Finset P) (Phi : P → Finset D) (fine : D → U)
    (center : P → U) (rho : ℝ) (ancestor : T → K) (realizer : P → D → T) : Finset K :=
  (originalPairs E Phi fine center rho).image (pairAncestor ancestor realizer)

def activePoints (E : Finset P) (Phi : P → Finset D) (fine : D → U)
    (center : P → U) (rho : ℝ) (ancestor : T → K) (realizer : P → D → T) (k : K) : Finset P :=
  E.filter (fun p => ∃ d ∈ nearDirections Phi fine center rho p, ancestor (realizer p d)=k)

omit [DecidableEq T] [DecidableEq D] [NormedSpace ℝ U] in
/-- This finite counting stage exposes two local fiber bounds, to be supplied
 by original incidence and fine-direction geometry below, and constructs the
 actual ancestor image rather than postulating a box population. -/
theorem original_pair_ancestor_count
    (E : Finset P) (Phi : P → Finset D) (fine : D → U) (center : P → U)
    (rho : ℝ) (ancestor : T → K) (realizer : P → D → T)
    {L Cpos Cdir : ℝ} (hCdir : 0 ≤ Cdir)
    (hlower : ∀ p ∈ E, L ≤ ((nearDirections Phi fine center rho p).card : ℝ))
    (hpos : ∀ k ∈ occupiedAncestors E Phi fine center rho ancestor realizer,
      ((activePoints E Phi fine center rho ancestor realizer k).card : ℝ) ≤ Cpos)
    (hdir : ∀ p ∈ E, ∀ k ∈ occupiedAncestors E Phi fine center rho ancestor realizer,
      (((nearDirections Phi fine center rho p).filter (fun d => ancestor (realizer p d)=k)).card : ℝ) ≤ Cdir) :
    (E.card : ℝ)*L ≤
      ((occupiedAncestors E Phi fine center rho ancestor realizer).card : ℝ)*(Cpos*Cdir) := by
  let W := originalPairs E Phi fine center rho
  let A := occupiedAncestors E Phi fine center rho ancestor realizer
  have hlow : (E.card : ℝ)*L ≤ (W.card : ℝ) := by
    calc
      _ = ∑ _p ∈ E, L := by simp
      _ ≤ ∑ p ∈ E, ((nearDirections Phi fine center rho p).card : ℝ) := Finset.sum_le_sum hlower
      _ = (W.card : ℝ) := by simp [W,originalPairs,Finset.card_sigma]
  have hmap : ∀ w ∈ W, pairAncestor ancestor realizer w ∈ A :=
    fun w hw => Finset.mem_image_of_mem _ hw
  have hfiber : ∀ k ∈ A,
      ((W.filter (fun w => pairAncestor ancestor realizer w=k)).card : ℝ) ≤ Cpos*Cdir := by
    intro k hk
    let F := W.filter (fun w => pairAncestor ancestor realizer w=k)
    let Q := activePoints E Phi fine center rho ancestor realizer k
    have hproject : ∀ w ∈ F, w.1 ∈ Q := by
      intro w hw
      obtain ⟨hwW,hwk⟩ := Finset.mem_filter.mp hw
      obtain ⟨hp,hd⟩ := Finset.mem_sigma.mp hwW
      exact Finset.mem_filter.mpr ⟨hp,w.2,hd,hwk⟩
    have hpoint : ∀ p ∈ Q, ((F.filter (fun w => w.1=p)).card : ℝ) ≤ Cdir := by
      intro p hp
      let R := (nearDirections Phi fine center rho p).filter (fun d => ancestor (realizer p d)=k)
      have hmaps : Set.MapsTo (fun w : Sigma fun _ : P => D => w.2)
          (↑(F.filter (fun w => w.1=p))) (↑R) := by
        intro w hw
        obtain ⟨hwF,hwp⟩ := Finset.mem_filter.mp hw
        obtain ⟨hwW,hwk⟩ := Finset.mem_filter.mp hwF
        obtain ⟨_,hd⟩ := Finset.mem_sigma.mp hwW
        exact Finset.mem_filter.mpr ⟨by simpa only [hwp] using hd,by simpa only [pairAncestor,hwp] using hwk⟩
      have hinj : Set.InjOn (fun w : Sigma fun _ : P => D => w.2)
          (↑(F.filter (fun w => w.1=p))) := by
        intro a ha b hb hab
        have hap := (Finset.mem_filter.mp ha).2
        have hbp := (Finset.mem_filter.mp hb).2
        cases a with
        | mk a₁ a₂ =>
          cases b with
          | mk b₁ b₂ =>
            dsimp at hap hbp hab
            subst a₁
            subst b₁
            subst b₂
            rfl
      have hc := Finset.card_le_card_of_injOn (fun w : Sigma fun _ : P => D => w.2) hmaps hinj
      exact (Nat.cast_le.mpr hc).trans (hdir p (Finset.mem_filter.mp hp).1 k hk)
    exact (FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers F Q Sigma.fst Cdir hproject hpoint).trans
      (mul_le_mul_of_nonneg_right (hpos k hk) hCdir)
  exact hlow.trans (FiniteTransverseMenuGrowth.card_le_real_mul_of_fibers W A
    (pairAncestor ancestor realizer) (Cpos*Cdir) hmap hfiber)

omit [NormedSpace ℝ U] in
/-- Fine-label fibers of an actual ancestor lie in one ball at the original
 point. This bound applies to the original fine set, with no coarse-union law. -/
theorem fine_label_in_ancestor_ball (fineDirection slope referenceSlope : U)
    {delta sigma Error : ℝ} (hd : delta ≤ sigma) (hE : 0 ≤ Error)
    (hfine : ‖fineDirection-slope‖ ≤ Error*delta)
    (hslope : ‖slope-referenceSlope‖ ≤ sigma) :
    ‖fineDirection-referenceSlope‖ ≤ (1+Error)*sigma := by
  calc
    _ ≤ ‖fineDirection-slope‖+‖slope-referenceSlope‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Error*delta+sigma := add_le_add hfine hslope
    _ ≤ Error*sigma+sigma := by gcongr
    _ = (1+Error)*sigma := by ring

/-- A same-height original incidence has a fixed tangent location inside its
 actual tube parameter ancestor. No physical overlap hypothesis is involved. -/
theorem same_ancestor_fixed_height_ball (x base referenceBase slope referenceSlope : U)
    {z delta sigma Error : ℝ} (hz : |z| ≤ 1) (hd : delta ≤ sigma) (hE : 0 ≤ Error)
    (hinc : ‖x-base-z • slope‖ ≤ Error*delta)
    (hbase : ‖base-referenceBase‖ ≤ sigma) (hslope : ‖slope-referenceSlope‖ ≤ sigma) :
    ‖x-(referenceBase+z • referenceSlope)‖ ≤ (2+Error)*sigma := by
  have h := ancestor_incidence_residual x base referenceBase slope referenceSlope hz hinc hbase hslope
  calc
    _ = ‖x-referenceBase-z • referenceSlope‖ := by congr 1; abel
    _ ≤ Error*delta+2*sigma := h
    _ ≤ Error*sigma+2*sigma := by gcongr
    _ = (2+Error)*sigma := by ring

omit [DecidableEq T] in
/-- Full original carrier fibers are disjoint because an original tube has
 one literal ancestor label. No count is taken inside the selected W core. -/
theorem original_carrier_saturation_count (Tfull : Finset T) (ancestor : T → K)
    (ancestors : Finset K) {Lcarrier : ℝ}
    (hlower : ∀ k ∈ ancestors,
      Lcarrier ≤ ((Tfull.filter (fun t => ancestor t=k)).card : ℝ)) :
    (ancestors.card : ℝ)*Lcarrier ≤
      ((Tfull.filter (fun t => ancestor t ∈ ancestors)).card : ℝ) := by
  let S := Tfull.filter (fun t => ancestor t ∈ ancestors)
  have hmap : ∀ t ∈ S, ancestor t ∈ ancestors := fun t ht => (Finset.mem_filter.mp ht).2
  have hpart := Finset.card_eq_sum_card_fiberwise hmap
  have hfib : ∀ k ∈ ancestors,
      S.filter (fun t => ancestor t=k)=Tfull.filter (fun t => ancestor t=k) := by
    intro k hk
    ext t
    simp only [S,Finset.mem_filter]
    constructor
    · rintro ⟨⟨ht,_⟩,heq⟩
      exact ⟨ht,heq⟩
    · rintro ⟨ht,heq⟩
      exact ⟨⟨ht,by simpa only [heq] using hk⟩,heq⟩
  calc
    _ = ∑ _k ∈ ancestors, Lcarrier := by simp
    _ ≤ ∑ k ∈ ancestors, ((Tfull.filter (fun t => ancestor t=k)).card : ℝ) :=
      Finset.sum_le_sum hlower
    _ = ∑ k ∈ ancestors, ((S.filter (fun t => ancestor t=k)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hfib k hk]
    _ = (S.card : ℝ) := by exact_mod_cast hpart.symm

omit [DecidableEq T] in
/-- Direct fine-scale convex-Wolff normalization. The physical hypothesis is
 containment of each ORIGINAL carrier fiber; the output count is derived. -/
theorem original_carrier_convex_count {X : Type*} (Tfull : Finset T) (ancestor : T → K)
    (ancestors : Finset K) (tube : T → Set X) (box : Set X)
    {Lcarrier CW volumeBox : ℝ}
    (hlower : ∀ k ∈ ancestors,
      Lcarrier ≤ ((Tfull.filter (fun t => ancestor t=k)).card : ℝ))
    (hcontains : ∀ t ∈ Tfull, ancestor t ∈ ancestors → tube t ⊆ box)
    (hCW : ((Tfull.filter (fun t => tube t ⊆ box)).card : ℝ) ≤ CW*volumeBox*Tfull.card) :
    (ancestors.card : ℝ)*Lcarrier ≤ CW*volumeBox*Tfull.card := by
  have hsub : Tfull.filter (fun t => ancestor t ∈ ancestors) ⊆ Tfull.filter (fun t => tube t ⊆ box) := by
    intro t ht
    obtain ⟨ht,hanc⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨ht,hcontains t ht hanc⟩
  exact (original_carrier_saturation_count Tfull ancestor ancestors hlower).trans
    ((Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hCW)

end OriginalAncestorCounting
