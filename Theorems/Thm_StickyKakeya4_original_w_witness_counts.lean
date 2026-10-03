import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace OriginalWWitnessCounts
open scoped BigOperators
open Classical
noncomputable section

variable {P T H A L : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
  [DecidableEq A] [DecidableEq L]

abbrev Path (P T : Type*) := TwoTubePathCollisionCount.Path P T

def tubesAt (I : Finset (P × T)) (p : P) : Finset T :=
  (TwoTubePathCollisionCount.tubes I).filter (fun t => (p,t) ∈ I)

def pointsAt (I : Finset (P × T)) (height : P → H) (t : T) (z : H) : Finset P :=
  (TwoTubePathCollisionCount.points I).filter (fun p => (p,t) ∈ I ∧ height p=z)

@[simp] lemma mem_tubesAt (I : Finset (P × T)) (p : P) (t : T) :
    t ∈ tubesAt I p ↔ (p,t) ∈ I := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem Prod.snd h, h⟩

@[simp] lemma mem_pointsAt (I : Finset (P × T)) (height : P → H) (t : T) (z : H) (p : P) :
    p ∈ pointsAt I height t z ↔ (p,t) ∈ I ∧ height p=z := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem Prod.fst h.1, h⟩

lemma card_biUnion_le_real {α β : Type*} [DecidableEq β]
    (S : Finset α) (F : α → Finset β) {K B : ℝ}
    (hB : 0 ≤ B) (hS : (S.card : ℝ) ≤ K)
    (hF : ∀ a ∈ S, ((F a).card : ℝ) ≤ B) :
    ((S.biUnion F).card : ℝ) ≤ K*B := by
  calc
    ((S.biUnion F).card : ℝ) ≤ ∑ a ∈ S, ((F a).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := S) (t := F))
    _ ≤ ∑ _a ∈ S, B := Finset.sum_le_sum hF
    _ = (S.card : ℝ)*B := by simp
    _ ≤ K*B := mul_le_mul_of_nonneg_right hS hB

/-- Enumerate a first branch backwards from its actual terminal tube and
three specified heights. Every choice is an original incidence fiber. -/
def backwardPaths (I : Finset (P × T)) (height : P → H)
    (z₀ z₁ z₂ : H) (t₂ : T) (test : T → Prop) : Finset (Path P T) :=
  (pointsAt I height t₂ z₂).biUnion fun p₂ =>
    (pointsAt I height t₂ z₁).biUnion fun p₁ =>
      ((tubesAt I p₁).filter test).biUnion fun t₁ =>
        (pointsAt I height t₁ z₀).image fun p₀ => ⟨p₀,t₁,p₁,t₂,p₂⟩

lemma path_mem_backward (I : Finset (P × T)) (height : P → H)
    (a : Path P T) (z₀ z₁ z₂ : H) (t₂ : T) (test : T → Prop)
    (ha : a ∈ TwoTubePathCollisionCount.paths I)
    (hz₀ : height a.point₀=z₀) (hz₁ : height a.point₁=z₁)
    (hz₂ : height a.point₂=z₂) (ht₂ : a.tube₂=t₂) (htest : test a.tube₁) :
    a ∈ backwardPaths I height z₀ z₁ z₂ t₂ test := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := (TwoTubePathCollisionCount.mem_paths I a).mp ha
  apply Finset.mem_biUnion.mpr
  refine ⟨a.point₂, ?_, ?_⟩
  · exact (mem_pointsAt _ _ _ _ _).mpr ⟨by simpa only [← ht₂] using h₃, hz₂⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a.point₁, ?_, ?_⟩
  · exact (mem_pointsAt _ _ _ _ _).mpr ⟨by simpa only [← ht₂] using h₂, hz₁⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨a.tube₁, Finset.mem_filter.mpr ⟨(mem_tubesAt _ _ _).mpr h₁, htest⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨a.point₀, (mem_pointsAt _ _ _ _ _).mpr ⟨h₀,hz₀⟩, ?_⟩
  cases a
  cases ht₂
  rfl

/-- Three actual point-at-height choices and one initial tube choice. -/
theorem backwardPaths_card_le (I : Finset (P × T)) (height : P → H)
    (z₀ z₁ z₂ : H) (t₂ : T) (test : T → Prop) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (htubes : ∀ p, (((tubesAt I p).filter test).card : ℝ) ≤ K) :
    ((backwardPaths I height z₀ z₁ z₂ t₂ test).card : ℝ) ≤ C^3*K := by
  calc
    ((backwardPaths I height z₀ z₁ z₂ t₂ test).card : ℝ) ≤ C*(C*(K*C)) := by
      unfold backwardPaths
      apply card_biUnion_le_real _ _ (by positivity) (hpoints t₂ z₂)
      intro p₂ _hp₂
      apply card_biUnion_le_real _ _ (by positivity) (hpoints t₂ z₁)
      intro p₁ _hp₁
      apply card_biUnion_le_real _ _ hC (htubes p₁)
      intro t₁ _ht₁
      exact (Nat.cast_le.mpr (Finset.card_image_le)).trans (hpoints t₁ z₀)
    _ = C^3*K := by ring

/-- Enumerate the second original branch from the shared start point, at the
first branch's actual heights and terminal coarse direction cell. -/
def forwardPaths (I : Finset (P × T)) (height : P → H) (cell : T → L)
    (a : Path P T) (test : T → Prop) : Finset (Path P T) :=
  ((tubesAt I a.point₀).filter test).biUnion fun t₁ =>
    (pointsAt I height t₁ (height a.point₁)).biUnion fun p₁ =>
      ((tubesAt I p₁).filter (fun t₂ => cell t₂=cell a.tube₂)).biUnion fun t₂ =>
        (pointsAt I height t₂ (height a.point₂)).image fun p₂ => ⟨a.point₀,t₁,p₁,t₂,p₂⟩

lemma path_mem_forward (I : Finset (P × T)) (height : P → H) (cell : T → L)
    (a b : Path P T) (test : T → Prop)
    (hb : b ∈ TwoTubePathCollisionCount.paths I) (hp : b.point₀=a.point₀)
    (hz₁ : height b.point₁=height a.point₁) (hz₂ : height b.point₂=height a.point₂)
    (hcell : cell b.tube₂=cell a.tube₂) (htest : test b.tube₁) :
    b ∈ forwardPaths I height cell a test := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := (TwoTubePathCollisionCount.mem_paths I b).mp hb
  apply Finset.mem_biUnion.mpr
  refine ⟨b.tube₁, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨(mem_tubesAt _ _ _).mpr (by simpa only [← hp] using h₀), htest⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨b.point₁, (mem_pointsAt _ _ _ _ _).mpr ⟨h₁,hz₁⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨b.tube₂, Finset.mem_filter.mpr ⟨(mem_tubesAt _ _ _).mpr h₂,hcell⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨b.point₂, (mem_pointsAt _ _ _ _ _).mpr ⟨h₃,hz₂⟩, ?_⟩
  cases b
  cases hp
  rfl

/-- The slab restriction is imposed only on the second initial tube at the
original shared start point. The two later point choices and terminal tube
choices are bounded in the full reference incidence set. -/
theorem forwardPaths_card_le (I : Finset (P × T)) (height : P → H) (cell : T → L)
    (a : Path P T) (test : T → Prop) {C K U : ℝ}
    (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (htubes : (((tubesAt I a.point₀).filter test).card : ℝ) ≤ K)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U) :
    ((forwardPaths I height cell a test).card : ℝ) ≤ C^2*K*U := by
  calc
    ((forwardPaths I height cell a test).card : ℝ) ≤ K*(C*(U*C)) := by
      unfold forwardPaths
      apply card_biUnion_le_real _ _ (by positivity) htubes
      intro t₁ _ht₁
      apply card_biUnion_le_real _ _ (by positivity) (hpoints t₁ (height a.point₁))
      intro p₁ _hp₁
      apply card_biUnion_le_real _ _ hC (hterminal p₁ (cell a.tube₂))
      intro t₂ _ht₂
      exact (Nat.cast_le.mpr (Finset.card_image_le)).trans (hpoints t₂ (height a.point₂))
    _ = C^2*K*U := by ring

def collisionLabel (height : P → H) (cell : T → L) (a : Path P T) : P × H × H × L :=
  (a.point₀,height a.point₁,height a.point₂,cell a.tube₂)

def witnesses (I : Finset (P × T)) (height : P → H) (cell : T → L) :
    Finset (Path P T × Path P T) :=
  TwoTubePathCollisionCount.collisions (TwoTubePathCollisionCount.paths I) (collisionLabel height cell)

def endpoint (height : P → H) (a : Path P T) : H × T := (height a.point₂,a.tube₂)

def menu (height : P → H) (angle : T → A) (w : Path P T × Path P T) :
    (H × H) × (A × A) :=
  ((height w.1.point₀,height w.1.point₁),(angle w.1.tube₁,angle w.2.tube₁))

lemma witness_conditions (I : Finset (P × T)) (height : P → H) (cell : T → L)
    {w : Path P T × Path P T} (hw : w ∈ witnesses I height cell) :
    w.1 ∈ TwoTubePathCollisionCount.paths I ∧ w.2 ∈ TwoTubePathCollisionCount.paths I ∧
    w.2.point₀=w.1.point₀ ∧ height w.2.point₁=height w.1.point₁ ∧
    height w.2.point₂=height w.1.point₂ ∧ cell w.2.tube₂=cell w.1.tube₂ := by
  obtain ⟨ha,hb,heq⟩ := (TwoTubePathCollisionCount.mem_collisions _ _ w).mp hw
  exact ⟨ha,hb,(congrArg Prod.fst heq).symm,
    (congrArg (fun q : P × H × H × L => q.2.1) heq).symm,
    (congrArg (fun q : P × H × H × L => q.2.2.1) heq).symm,
    (congrArg (fun q : P × H × H × L => q.2.2.2) heq).symm⟩

def allBackward (I : Finset (P × T)) (height : P → H) (Z : Finset H)
    (v : H × T) (test : T → Prop) : Finset (Path P T) :=
  Z.biUnion fun z₀ => Z.biUnion fun z₁ => backwardPaths I height z₀ z₁ v.1 v.2 test

theorem allBackward_card_le (I : Finset (P × T)) (height : P → H) (Z : Finset H)
    (v : H × T) (test : T → Prop) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (htubes : ∀ p, (((tubesAt I p).filter test).card : ℝ) ≤ K) :
    ((allBackward I height Z v test).card : ℝ) ≤ C^3*K*(Z.card : ℝ)^2 := by
  calc
    ((allBackward I height Z v test).card : ℝ) ≤
        (Z.card : ℝ)*((Z.card : ℝ)*(C^3*K)) := by
      unfold allBackward
      apply card_biUnion_le_real _ _ (by positivity) (le_refl _)
      intro z₀ _hz₀
      apply card_biUnion_le_real _ _ (by positivity) (le_refl _)
      intro z₁ _hz₁
      exact backwardPaths_card_le I height z₀ z₁ v.1 v.2 test hC hK hpoints htubes
    _ = C^3*K*(Z.card : ℝ)^2 := by ring

def pairedExtensions (F : Finset (Path P T)) (G : Path P T → Finset (Path P T)) :
    Finset (Path P T × Path P T) :=
  F.biUnion fun a => (G a).image (fun b => (a,b))

@[simp] lemma mem_pairedExtensions (F : Finset (Path P T))
    (G : Path P T → Finset (Path P T)) (w : Path P T × Path P T) :
    w ∈ pairedExtensions F G ↔ w.1 ∈ F ∧ w.2 ∈ G w.1 := by
  rcases w with ⟨a,b⟩
  simp [pairedExtensions]

theorem pairedExtensions_card_le (F : Finset (Path P T))
    (G : Path P T → Finset (Path P T)) {K B : ℝ}
    (hB : 0 ≤ B) (hF : (F.card : ℝ) ≤ K)
    (hG : ∀ a ∈ F, ((G a).card : ℝ) ≤ B) :
    ((pairedExtensions F G).card : ℝ) ≤ K*B := by
  unfold pairedExtensions
  apply card_biUnion_le_real _ _ hB hF
  intro a ha
  exact (Nat.cast_le.mpr Finset.card_image_le).trans (hG a ha)

def outgoingTest (I : Finset (P × T)) (height : P → H) (cell : T → L)
    (v : H × T) (test : Path P T → T → Prop) : Finset (Path P T × Path P T) :=
  (witnesses I height cell).filter (fun w => endpoint height w.1=v ∧ test w.1 w.2.tube₁)

/-- An outgoing original witness is injected into actual backward/forward
incidence choices; the second-branch test is imposed at the common start. -/
lemma outgoingTest_subset_extensions (I : Finset (P × T)) (height : P → H)
    (cell : T → L) (Z : Finset H) (v : H × T) (test : Path P T → T → Prop)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z) :
    outgoingTest I height cell v test ⊆
      pairedExtensions (allBackward I height Z v (fun _ => True))
        (fun a => forwardPaths I height cell a (test a)) := by
  intro w hw
  obtain ⟨hwW,hend,htest⟩ := Finset.mem_filter.mp hw
  obtain ⟨ha,hb,hp,hz₁,hz₂,hcell⟩ := witness_conditions I height cell hwW
  have haI := (TwoTubePathCollisionCount.mem_paths I w.1).mp ha
  have hz₀Z : height w.1.point₀ ∈ Z :=
    hheight _ (Finset.mem_image_of_mem Prod.fst haI.1)
  have hz₁Z : height w.1.point₁ ∈ Z :=
    hheight _ (Finset.mem_image_of_mem Prod.fst haI.2.1)
  apply (mem_pairedExtensions _ _ w).mpr
  constructor
  · apply Finset.mem_biUnion.mpr
    refine ⟨height w.1.point₀,hz₀Z,Finset.mem_biUnion.mpr ⟨height w.1.point₁,hz₁Z,?_⟩⟩
    exact path_mem_backward I height w.1 _ _ _ _ _ ha rfl rfl
      (congrArg Prod.fst hend) (congrArg Prod.snd hend) trivial
  · exact path_mem_forward I height cell w.1 w.2 _ hb hp hz₁ hz₂ hcell htest

/-- Native bad-W estimate. Its inputs are only original point-at-height,
point-tube, terminal-cell, and same-start tested-tube bounds. -/
theorem outgoingTest_card_le (I : Finset (P × T)) (height : P → H)
    (cell : T → L) (Z : Finset H) (v : H × T) (test : Path P T → T → Prop)
    {C D K U : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hdegree : ∀ p, ((tubesAt I p).card : ℝ) ≤ D)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (htest : ∀ a : Path P T, (((tubesAt I a.point₀).filter (test a)).card : ℝ) ≤ K) :
    ((outgoingTest I height cell v test).card : ℝ) ≤ C^5*D*K*U*(Z.card : ℝ)^2 := by
  have hfirst := allBackward_card_le I height Z v (fun _ => True) hC hD hpoints
    (by intro p; simpa using hdegree p)
  have hsecond : ∀ a ∈ allBackward I height Z v (fun _ => True),
      ((forwardPaths I height cell a (test a)).card : ℝ) ≤ C^2*K*U := by
    intro a _ha
    exact forwardPaths_card_le I height cell a (test a) hC hU hpoints (htest a) hterminal
  have hcount := pairedExtensions_card_le _ _ (show 0 ≤ C^2*K*U by positivity) hfirst hsecond
  calc
    ((outgoingTest I height cell v test).card : ℝ) ≤ _ := by
      exact_mod_cast Finset.card_le_card
        (outgoingTest_subset_extensions I height cell Z v test hheight)
    _ ≤ (C^3*D*(Z.card : ℝ)^2)*(C^2*K*U) := hcount
    _ = C^5*D*K*U*(Z.card : ℝ)^2 := by ring

/-- The ambient original-witness degree bound, with no selected-W premise. -/
theorem outgoing_card_le (I : Finset (P × T)) (height : P → H)
    (cell : T → L) (Z : Finset H) (v : H × T)
    {C D U : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hdegree : ∀ p, ((tubesAt I p).card : ℝ) ≤ D)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U) :
    (((witnesses I height cell).filter (fun w => endpoint height w.1=v)).card : ℝ)
      ≤ C^5*D^2*U*(Z.card : ℝ)^2 := by
  have h := outgoingTest_card_le I height cell Z v (fun _ _ => True)
    hC hD hD hU hheight hpoints hdegree hterminal
    (by intro a; simpa using hdegree a.point₀)
  simpa only [outgoingTest, and_true, Finset.filter_true, pow_two, mul_assoc] using h

def menuFiber (I : Finset (P × T)) (height : P → H) (cell : T → L)
    (angle : T → A) (v : H × T) (g : (H × H) × (A × A)) :
    Finset (Path P T × Path P T) :=
  (witnesses I height cell).filter (fun w => endpoint height w.1=v ∧ menu height angle w=g)

lemma menuFiber_subset_extensions (I : Finset (P × T)) (height : P → H)
    (cell : T → L) (angle : T → A) (v : H × T) (g : (H × H) × (A × A)) :
    menuFiber I height cell angle v g ⊆
      pairedExtensions (backwardPaths I height g.1.1 g.1.2 v.1 v.2 (fun t => angle t=g.2.1))
        (fun a => forwardPaths I height cell a (fun t => angle t=g.2.2)) := by
  intro w hw
  obtain ⟨hwW,hend,hmenu⟩ := Finset.mem_filter.mp hw
  obtain ⟨ha,hb,hp,hz₁,hz₂,hcell⟩ := witness_conditions I height cell hwW
  have htimes := congrArg Prod.fst hmenu
  have hangles := congrArg Prod.snd hmenu
  apply (mem_pairedExtensions _ _ w).mpr
  constructor
  · exact path_mem_backward I height w.1 _ _ _ _ _ ha
      (congrArg Prod.fst htimes) (congrArg Prod.snd htimes)
      (congrArg Prod.fst hend) (congrArg Prod.snd hend) (congrArg Prod.fst hangles)
  · exact path_mem_forward I height cell w.1 w.2 _ hb hp hz₁ hz₂ hcell
      (congrArg Prod.snd hangles)

/-- The C0^5 U^3 fiber bound is derived from ORIGINAL point/tube incidences
after fixing the two actual projected labels and both actual height labels. -/
theorem menuFiber_card_le (I : Finset (P × T)) (height : P → H)
    (cell : T → L) (angle : T → A) (v : H × T) (g : (H × H) × (A × A))
    {C U : ℝ} (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hpoints : ∀ t z, ((pointsAt I height t z).card : ℝ) ≤ C)
    (hterminal : ∀ p c, (((tubesAt I p).filter (fun t => cell t=c)).card : ℝ) ≤ U)
    (hangular : ∀ p a, (((tubesAt I p).filter (fun t => angle t=a)).card : ℝ) ≤ U) :
    ((menuFiber I height cell angle v g).card : ℝ) ≤ C^5*U^3 := by
  have hfirst := backwardPaths_card_le I height g.1.1 g.1.2 v.1 v.2
    (fun t => angle t=g.2.1) hC hU hpoints (by
      intro p
      convert hangular p g.2.1 using 1
      apply congrArg (fun s : Finset T => (s.card : ℝ))
      exact Finset.filter_congr_decidable _ _ _)
  have hsecond : ∀ a ∈ backwardPaths I height g.1.1 g.1.2 v.1 v.2 (fun t => angle t=g.2.1),
      ((forwardPaths I height cell a (fun t => angle t=g.2.2)).card : ℝ) ≤ C^2*U*U := by
    intro a _ha
    exact forwardPaths_card_le I height cell a _ hC hU hpoints
      (by
        convert hangular a.point₀ g.2.2 using 1
        apply congrArg (fun s : Finset T => (s.card : ℝ))
        exact Finset.filter_congr_decidable _ _ _) hterminal
  have hcount := pairedExtensions_card_le _ _ (show 0 ≤ C^2*U*U by positivity) hfirst hsecond
  calc
    ((menuFiber I height cell angle v g).card : ℝ) ≤ _ := by
      exact_mod_cast Finset.card_le_card
        (menuFiber_subset_extensions I height cell angle v g)
    _ ≤ (C^3*U)*(C^2*U*U) := hcount
    _ = C^5*U^3 := by ring

end
end OriginalWWitnessCounts
