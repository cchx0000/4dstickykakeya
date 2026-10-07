import Theorems.Thm_StickyKakeya4_native_window_base_cover

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeWindowKeyReadback
open Classical Finset NativeWindowXYLabels NativeWindowNesting NativeWindowRealInterpolation
open NativeQuotientGridCenters FiniteVoronoiRealADCoarsening

/-- A literal final coarse-Y key slice, retaining its actual source. -/
def keySlice {Ω : Type*} {l : ℕ} (T : Finset Ω)
    (key : Ω → ℤ × (Fin l → ℤ)) (height : ℤ) : Finset (Fin l → ℤ) :=
  (T.filter (fun x => (key x).1=height)).image (fun x => (key x).2)

/-- Exact freezing identifies the actual final key on the retained source
with the old height/normal-grid key. No equality away from T is required. -/
theorem keySlice_eq_atPoint {Ω : Type*} {k l : ℕ} (T : Finset Ω)
    (labels : Ω → XY k l) (key : Ω → ℤ × (Fin l → ℤ)) (R : ℕ)
    (Hkey : ∀x∈T,key x=((labels x).1/((8*R:ℕ):ℤ),gridDiv R (labels x).2.2))
    (p : XY k l) :
    keySlice T key (p.1/((8*R:ℕ):ℤ))=atPoint (T.image labels) R p := by
  rw [atPoint_eq_image]
  ext y
  simp only [keySlice,mem_image,mem_filter]
  constructor
  · rintro ⟨x,⟨hx,hheight⟩,hy⟩
    rw [Hkey x hx] at hheight hy
    exact ⟨labels x,⟨⟨x,hx,rfl⟩,hheight⟩,hy⟩
  · rintro ⟨z,⟨⟨x,hx,rfl⟩,hheight⟩,hy⟩
    refine ⟨x,⟨hx,?_⟩,?_⟩ <;> rw [Hkey x hx]
    · exact hheight
    · exact hy

/-- A larger time window of the already frozen base key. Its normal
labels stay at the original base resolution, and its field is unchanged. -/
def keyWindow {Ω : Type*} {l : ℕ} (T : Finset Ω)
    (key : Ω → ℤ × (Fin l → ℤ)) (D : ℕ) (height : ℤ) : Finset (Fin l → ℤ) :=
  (T.filter (fun x => (key x).1/(D:ℤ)=height)).image (fun x => (key x).2)

/-- Literal base-Y union readback for every larger time window. The key
is frozen only at R0; no field value at a new height scale is introduced. -/
theorem keyWindow_eq_baseUnion {Ω : Type*} {k l : ℕ} (T : Finset Ω)
    (labels : Ω → XY k l) (key : Ω → ℤ × (Fin l → ℤ)) (R0 D : ℕ)
    (Hkey : ∀x∈T,key x=((labels x).1/((8*R0:ℕ):ℤ),gridDiv R0 (labels x).2.2))
    (mu : ℝ) (p : XY k l) :
    (keyWindow T key D (p.1/((8*(R0*D):ℕ):ℤ))).image (center (mu*(R0:ℝ)))=
      NativeWindowBaseCover.baseUnion (T.image labels) mu R0 D p := by
  ext y
  simp only [keyWindow,NativeWindowBaseCover.baseUnion,mem_image,mem_filter]
  constructor
  · rintro ⟨q,⟨x,⟨hx,hheight⟩,rfl⟩,rfl⟩
    rw [Hkey x hx] at hheight ⊢
    rw [height_div_comp] at hheight
    exact ⟨labels x,⟨⟨x,hx,rfl⟩,hheight⟩,rfl⟩
  · rintro ⟨z,⟨⟨x,hx,rfl⟩,hheight⟩,rfl⟩
    refine ⟨(key x).2,⟨x,⟨hx,?_⟩,rfl⟩,?_⟩
    · rw [Hkey x hx,height_div_comp]
      exact hheight
    · rw [Hkey x hx]

/-- The actual source profile and its global count read back to the same
coarse-Y key image used by the higher-grain consumer. -/
theorem keySlice_profile {Ω : Type*} {k l : ℕ} (T : Finset Ω)
    (labels : Ω → XY k l) (key : Ω → ℤ × (Fin l → ℤ)) (R : ℕ)
    (Hkey : ∀x∈T,key x=((labels x).1/((8*R:ℕ):ℤ),gridDiv R (labels x).2.2))
    (p : XY k l) {rho K s : ℝ}
    (H : ADBounds (points (T.image labels) R rho p) rho K s)
    (Hglobal : ((atPoint (T.image labels) R p).card:ℝ) ≤ K*rho^(-s)) :
    ADBounds ((keySlice T key (p.1/((8*R:ℕ):ℤ))).image (center rho)) rho K s ∧
      ((keySlice T key (p.1/((8*R:ℕ):ℤ))).card:ℝ) ≤ K*rho^(-s) := by
  rw [keySlice_eq_atPoint T labels key R Hkey p]
  exact ⟨H,Hglobal⟩

end NativeWindowKeyReadback
