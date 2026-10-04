import Theorems.Thm_StickyKakeya4_native_radial_class_pruning
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeRadialClassGeometry
open OriginalPairStripGeometry NativeRadialClassPruning

theorem forward_class_geometry (rho : ℝ) (hrho : 0<rho) (z v : Pair)
    (heq : forwardClass rho z=forwardClass rho v) :
    z.1=v.1 ∧ |radialAngle z.1 z.2-radialAngle v.1 v.2|<rho := by
  have hroot : z.1=v.1 := congrArg (fun c : ClassLabel => c.1) heq
  have hfloor : ⌊radialAngle z.1 z.2/rho⌋=⌊radialAngle v.1 v.2/rho⌋ :=
    congrArg (fun c : ClassLabel => c.2) heq
  have hzlo := Int.floor_le (radialAngle z.1 z.2/rho)
  have hzhi := Int.lt_floor_add_one (radialAngle z.1 z.2/rho)
  have hvlo := Int.floor_le (radialAngle v.1 v.2/rho)
  have hvhi := Int.lt_floor_add_one (radialAngle v.1 v.2/rho)
  rw [← hfloor] at hvlo hvhi
  have h1 := (le_div_iff₀ hrho).mp hzlo
  have h2 := (div_lt_iff₀ hrho).mp hzhi
  have h3 := (le_div_iff₀ hrho).mp hvlo
  have h4 := (div_lt_iff₀ hrho).mp hvhi
  exact ⟨hroot,abs_lt.mpr ⟨by linarith only [h1,h4],by linarith only [h2,h3]⟩⟩

theorem reverse_class_geometry (rho : ℝ) (hrho : 0<rho) (z v : Pair)
    (heq : reverseClass rho z=reverseClass rho v) :
    z.2=v.2 ∧ |radialAngle z.2 z.1-radialAngle v.2 v.1|<rho :=
  forward_class_geometry rho hrho (z.2,z.1) (v.2,v.1) heq
end NativeRadialClassGeometry
