import Theorems.Thm_StickyKakeya4_original_angular_alphabet_translation
import Theorems.Thm_StickyKakeya4_original_core_menu_density
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalReferenceAngleSelection
open Classical OriginalWWitnessCounts OriginalWCoreDynamics OriginalWCoarseEscapeMenus
variable {P T K : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq K]
theorem source_common_angle_near (I : Finset (P × T)) (u : T → ℝ)
    (fine : P → Finset ℝ) (Phi : Finset ℝ) (fineError coarseError : ℝ)
    (hrealize : ∀ p t, (p,t) ∈ I → ∃ phi ∈ fine p, |u t-phi| ≤ fineError)
    (hcover : ∀ p ∈ TwoTubePathCollisionCount.points I, ∀ phi ∈ fine p, ∃ a ∈ Phi, |phi-a| ≤ coarseError) :
    ∀ t ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |u t-a| ≤ fineError+coarseError := by
  intro t ht
  obtain ⟨pt,hpt,hptt⟩ := Finset.mem_image.mp ht
  obtain ⟨phi,hphi,hup⟩ := hrealize pt.1 pt.2 hpt
  obtain ⟨a,ha,hpa⟩ := hcover pt.1 (Finset.mem_image_of_mem Prod.fst hpt) phi hphi
  refine ⟨a,ha,?_⟩
  rw [← hptt]
  calc
    _ = |(u pt.2-phi)+(phi-a)| := by congr 1; ring
    _ ≤ |u pt.2-phi|+|phi-a| := abs_add_le _ _
    _ ≤ _ := add_le_add hup hpa
def angle (I : Finset (P × T)) (u : T → ℝ) (Phi : Finset ℝ) (hPhi : Phi.Nonempty)
    (error : ℝ) (hnear : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |u t-a| ≤ error) (t : T) : ℝ :=
  if ht : t ∈ TwoTubePathCollisionCount.tubes I then Classical.choose (hnear t ht) else Classical.choose hPhi
omit [DecidableEq P] in
lemma angle_spec (I : Finset (P × T)) (u : T → ℝ) (Phi : Finset ℝ) (hPhi : Phi.Nonempty)
    (error : ℝ) (hnear : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |u t-a| ≤ error)
    (t : T) (ht : t ∈ TwoTubePathCollisionCount.tubes I) :
    angle I u Phi hPhi error hnear t ∈ Phi ∧ |u t-angle I u Phi hPhi error hnear t| ≤ error := by
  simpa only [angle,dif_pos ht] using Classical.choose_spec (hnear t ht)
theorem angle_fiber_cap (I : Finset (P × T)) (u : T → ℝ) (Phi : Finset ℝ) (hPhi : Phi.Nonempty)
    (error : ℝ) (hnear : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |u t-a| ≤ error)
    {U : ℝ} (hball : ∀ p a, (((tubesAt I p).filter (fun t => |u t-a| ≤ error)).card : ℝ) ≤ U) :
    ∀ p a, (((tubesAt I p).filter (fun t => angle I u Phi hPhi error hnear t=a)).card : ℝ) ≤ U := by
  intro p a
  have hsub : (tubesAt I p).filter (fun t => angle I u Phi hPhi error hnear t=a) ⊆
      (tubesAt I p).filter (fun t => |u t-a| ≤ error) := by
    intro t ht
    obtain ⟨htI,hta⟩ := Finset.mem_filter.mp ht
    have htT := (Finset.mem_filter.mp htI).1
    exact Finset.mem_filter.mpr ⟨htI,by simpa only [hta] using (angle_spec I u Phi hPhi error hnear t htT).2⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hball p a)
theorem exists_full_reference_rich_core
    (I : Finset (P × T)) (height : P → ℝ) (cell : T → K) (u : T → ℝ)
    (Z Phi : Finset ℝ) (hI : I.Nonempty) (hPhi : Phi.Nonempty)
    (error : ℝ) (hnear : ∀ t ∈ TwoTubePathCollisionCount.tubes I, ∃ a ∈ Phi, |u t-a| ≤ error)
    {C D U alpha beta : ℝ} (hC : 0 < C) (hU : 0 < U) (halpha : 0 ≤ alpha)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (hball : ∀ p a, (((tubesAt I p).filter (fun t => |u t-a| ≤ error)).card : ℝ) ≤ U)
    (hmass : alpha*(C^5*D^2*U*(Z.card : ℝ)^2)*(vertices I height).card ≤ (witnesses I height cell).card)
    (hscale : 4*beta*U^2*(Phi.card : ℝ)^2 ≤ alpha*D^2) :
    ∃ S ⊆ vertices I height, S.Nonempty ∧
      ((witnesses I height cell).card : ℝ) ≤ 2*((RichWitnessCore.retained (witnesses I height cell)
          (fun w => endpoint height w.1) (fun w => endpoint height w.2) S).card : ℝ) ∧
      ∀ s ∈ S, beta*(Z.card : ℝ)^2*(Phi.card : ℝ)^2 ≤
          ((coarseMenus I height cell (angle I u Phi hPhi error hnear) S s).card : ℝ) ∧
        coarseMenus I height cell (angle I u Phi hPhi error hnear) S s ⊆ (Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi) := by
  let a := angle I u Phi hPhi error hnear
  have hfib := angle_fiber_cap I u Phi hPhi error hnear hball
  obtain ⟨S,hSV,hS,hhalf,hrich⟩ := OriginalCoreMenuDensity.exists_original_menu_rich_core
    I height cell a Z hI hC hU halpha hheight hpoints hterminal hfib hmass
  have hsub : angles I a ⊆ Phi := by
    intro phi hphi
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hphi
    exact (angle_spec I u Phi hPhi error hnear t ht).1
  refine ⟨S,hSV,hS,hhalf,?_⟩
  intro s hs
  refine ⟨OriginalCoreMenuDensity.normalize_phase_menu_degree hU hscale (hrich s hs).1,?_⟩
  intro g hg
  obtain ⟨hZ,hPhi'⟩ := Finset.mem_product.mp ((hrich s hs).2 hg)
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hPhi'
  exact Finset.mem_product.mpr ⟨hZ,Finset.mem_product.mpr ⟨hsub ha,hsub hb⟩⟩
end OriginalReferenceAngleSelection
