import Theorems.Thm_StickyKakeya4_native_original_height_vertices
import Theorems.Thm_StickyKakeya4_original_incidence_height_population
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeCoarseOriginalIncidences
open Classical Finset IncidenceBinTransfer NativeOriginalSlicePopulation
variable {T : Type*}
/-- The later point/tube label uses the global physical bin and the SAME
 original tube. It is not a choice of a surrogate incidence representative. -/
def label (P : PhysicalRescalingIncidenceTransfer.Data T) (e : T × Cell) : Cell × T :=
  (P.cellBin e.2,e.1)
def incidences (P : PhysicalRescalingIncidenceTransfer.Data T) (E : Finset (T × Cell)) :
    Finset (Cell × T) := E.image (label P)
def coordinates (P : PhysicalRescalingIncidenceTransfer.Data T) (R : ℝ) (c : Cell) : ShearBinFibers.Point :=
  ShearBinFibers.oldCenter (P.σ/R) c
def height (P : PhysicalRescalingIncidenceTransfer.Data T) (R : ℝ) (c : Cell) : ℝ :=
  (coordinates P R c).2
def heights (P : PhysicalRescalingIncidenceTransfer.Data T) (E : Finset (T × Cell)) (R : ℝ) : Finset ℝ :=
  (incidences P E).image (fun e => height P R e.1)
def pullback (P : PhysicalRescalingIncidenceTransfer.Data T) (E : Finset (T × Cell))
    (I : Finset (Cell × T)) : Finset (T × Cell) := E.filter (fun e => label P e ∈ I)
lemma incidences_eq_swapped_bins (P : PhysicalRescalingIncidenceTransfer.Data T) (E : Finset (T × Cell)) :
    incidences P E=NativeOriginalHeightVertices.pointTube (bins E P.cellBin) := by
  simp only [incidences,NativeOriginalHeightVertices.pointTube,bins,image_image]
  rfl
lemma mem_incidences (P : PhysicalRescalingIncidenceTransfer.Data T) (E : Finset (T × Cell)) (c : Cell) (t : T) :
    (c,t) ∈ incidences P E ↔ ∃ old, (t,old) ∈ E ∧ P.cellBin old=c := by
  simp only [incidences,mem_image,label,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨s,old⟩,he,hc,hs⟩
    change s=t at hs
    subst s
    exact ⟨old,he,hc⟩
  · rintro ⟨old,he,hc⟩
    exact ⟨(t,old),he,hc,rfl⟩
lemma original_tubes_unchanged (P : PhysicalRescalingIncidenceTransfer.Data T) (E : Finset (T × Cell)) :
    TwoTubePathCollisionCount.tubes (incidences P E)=E.image Prod.fst := by
  simp only [TwoTubePathCollisionCount.tubes,incidences,image_image]
  rfl
lemma coarse_card (P : PhysicalRescalingIncidenceTransfer.Data T) (E : Finset (T × Cell)) :
    (incidences P E).card=(bins E P.cellBin).card := by
  rw [incidences_eq_swapped_bins,NativeOriginalHeightVertices.pointTube_card]
/-- The actual old-to-coarse map, written directly on the SAME original E0. -/
theorem original_readback {Old : Type*} [DecidableEq Old]
    (P : PhysicalRescalingIncidenceTransfer.Data T) (E0 : Finset (T × Old))
    (E : Finset (T × Cell)) (chart : Old → Cell)
    (hread : E0.image (fun e => (e.1,chart e.2))=E) :
    incidences P E=E0.image (fun e => (P.cellBin (chart e.2),e.1)) := by
  rw [incidences,←hread,image_image]
  rfl
lemma pullback_image (P : PhysicalRescalingIncidenceTransfer.Data T) (E : Finset (T × Cell))
    (I : Finset (Cell × T)) (hI : I ⊆ incidences P E) :
    incidences P (pullback P E I)=I := by
  ext v
  constructor
  · intro hv
    obtain ⟨e,he,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp he).2
  · intro hv
    obtain ⟨e,he,heq⟩ := mem_image.mp (hI hv)
    exact mem_image.mpr ⟨e,mem_filter.mpr ⟨he,heq ▸ hv⟩,heq⟩
/-- Every actual tube/bin fiber has at most N old labels, by the proven
 affine/floor lattice map. This holds for an arbitrary original subset E. -/
theorem actual_fiber_capacity (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (E : Finset (T × Cell)) (hE : E ⊆ P.incidences) (v : Cell × T) :
    (E.filter (fun e => label P e=v)).card ≤ P.N := by
  apply (card_le_card (show E.filter (fun e => label P e=v) ⊆
      binFiber P.incidences P.cellBin v.swap from ?_)).trans (P.incidence_fiber_bound hP v.swap)
  intro e he
  obtain ⟨he,hv⟩ := mem_filter.mp he
  refine mem_binFiber.mpr ⟨hE he,?_⟩
  have hh := congrArg Prod.swap hv
  exact hh
/-- Total original mass is charged to actual distinct coarse incidences. -/
theorem actual_capacity (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (E : Finset (T × Cell)) (hE : E ⊆ P.incidences) :
    E.card ≤ P.N*(incidences P E).card := by
  apply card_le_mul_card_image_of_maps_to (f := label P)
  · intro e he
    exact mem_image_of_mem _ he
  · intro v _hv
    exact actual_fiber_capacity P hP E hE v
/-- Source density is transported at the actual mesh sigma=N*delta_old;
 the common normalization R is paid explicitly in the retained density. -/
theorem actual_density_transfer (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (E : Finset (T × Cell)) (hE : E ⊆ P.incidences) {density F R : ℝ}
    (hF : 0 < F) (hR : 0 < R)
    (hden : density*(E.image Prod.fst).card ≤ F*P.δ*(E.card:ℝ)) :
    (density/(F*R))*(TwoTubePathCollisionCount.tubes (incidences P E)).card ≤
      (P.σ/R)*(incidences P E).card := by
  rw [original_tubes_unchanged]
  have hc : (E.card:ℝ) ≤ (P.N:ℝ)*(incidences P E).card := by
    exact_mod_cast actual_capacity P hP E hE
  have hh : density*(E.image Prod.fst).card ≤ F*P.σ*(incidences P E).card := by
    calc
      _ ≤ F*P.δ*(E.card:ℝ) := hden
      _ ≤ F*P.δ*((P.N:ℝ)*(incidences P E).card) :=
        mul_le_mul_of_nonneg_left hc (mul_nonneg hF.le hP.delta_pos.le)
      _ = _ := by dsimp [PhysicalRescalingIncidenceTransfer.Data.σ]; ring
  have heq : (F*P.σ*(incidences P E).card)/(F*R)=(P.σ/R)*(incidences P E).card := by
    field_simp
  have hc' : (density*(E.image Prod.fst).card)/(F*R) ≤
      (F*P.σ*(incidences P E).card)/(F*R) := div_le_div_of_nonneg_right hh (mul_pos hF hR).le
  rw [heq] at hc'
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hc'
lemma actual_height_membership (P : PhysicalRescalingIncidenceTransfer.Data T)
    (E : Finset (T × Cell)) (R : ℝ) :
    ∀ c ∈ TwoTubePathCollisionCount.points (incidences P E), height P R c ∈ heights P E R := by
  intro c hc
  obtain ⟨e,he,rfl⟩ := mem_image.mp hc
  exact mem_image_of_mem _ he
end NativeCoarseOriginalIncidences
