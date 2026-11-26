module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDoubleStair
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.CechDouble

universe u v

namespace Stair

def bdry {R : Type u} [CommRing R] {A : ℕ → Type v} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    (d : ∀ n, A n →ₗ[R] A (n + 1)) : ∀ n, Submodule R (A n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (d n)

abbrev H {R : Type u} [CommRing R] {A : ℕ → Type v} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    (d : ∀ n, A n →ₗ[R] A (n + 1)) (n : ℕ) : Type v :=
  LinearMap.ker (d n) ⧸ (bdry d n).comap (LinearMap.ker (d n)).subtype

structure DblData (R : Type u) [CommRing R] where
  D : ℕ → ℕ → Type v
  [gD : ∀ p q, AddCommGroup (D p q)]
  [mD : ∀ p q, Module R (D p q)]
  v : ∀ p q, D p q →ₗ[R] D (p + 1) q
  h : ∀ p q, D p q →ₗ[R] D p (q + 1)
  comm : ∀ p q, (v p (q + 1)).comp (h p q) = (h (p + 1) q).comp (v p q)
  A : ℕ → Type v
  [gA : ∀ p, AddCommGroup (A p)]
  [mA : ∀ p, Module R (A p)]
  dA : ∀ p, A p →ₗ[R] A (p + 1)
  a : ∀ p, A p →ₗ[R] D p 0
  C : ℕ → Type v
  [gC : ∀ q, AddCommGroup (C q)]
  [mC : ∀ q, Module R (C q)]
  dC : ∀ q, C q →ₗ[R] C (q + 1)
  c : ∀ q, C q →ₗ[R] D 0 q

attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC

variable {R : Type u} [CommRing R]

structure DblData.Good (X : DblData R) : Prop where
  ha : ∀ p, (X.a (p + 1)).comp (X.dA p) = (X.v p 0).comp (X.a p)
  hc : ∀ q, (X.c (q + 1)).comp (X.dC q) = (X.h 0 q).comp (X.c q)
  ka : ∀ p, LinearMap.ker (X.a p) = ⊥
  ra : ∀ p, LinearMap.ker (X.h p 0) = LinearMap.range (X.a p)
  rh : ∀ p q, LinearMap.ker (X.h p (q + 1)) = LinearMap.range (X.h p q)
  kc : ∀ q, LinearMap.ker (X.c q) = ⊥
  rc : ∀ q, LinearMap.ker (X.v 0 q) = LinearMap.range (X.c q)
  rv : ∀ p q, LinearMap.ker (X.v (p + 1) q) = LinearMap.range (X.v p q)

namespace DblData

theorem comm_apply (X : DblData R) (p q : ℕ) (z : X.D p q) :
    X.v p (q + 1) (X.h p q z) = X.h (p + 1) q (X.v p q z) :=
  LinearMap.congr_fun (X.comm p q) z

def shift (X : DblData R) : DblData R where
  D p q := X.D (p + 1) q
  v p q := X.v (p + 1) q
  h p q := X.h (p + 1) q
  comm p q := X.comm (p + 1) q
  A p := X.A (p + 1)
  dA p := X.dA (p + 1)
  a p := X.a (p + 1)
  C q := LinearMap.range (X.v 0 q)
  dC q := (X.h 1 q).restrict (fun x hx => by
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨X.h 0 q z, X.comm_apply 0 q z⟩)
  c q := (LinearMap.range (X.v 0 q)).subtype

def up (X : DblData R) (n : ℕ) : X.D 0 n →ₗ[R] X.shift.C n := (X.v 0 n).rangeRestrict

theorem up_surj (X : DblData R) (n : ℕ) (w : X.shift.C n) : ∃ z, X.up n z = w := by
  have hw : (w : LinearMap.range (X.v 0 n)).1 ∈ LinearMap.range (X.v 0 n) := (w : LinearMap.range (X.v 0 n)).2
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hw
  exact ⟨z, Subtype.ext hz⟩

namespace Good

theorem shift {X : DblData R} (hX : X.Good) : X.shift.Good := by
  refine
    { ha := fun p => hX.ha (p + 1)
      hc := ?_
      ka := fun p => hX.ka (p + 1)
      ra := fun p => hX.ra (p + 1)
      rh := fun p q => hX.rh (p + 1) q
      kc := fun q => Submodule.ker_subtype (LinearMap.range (X.v 0 q))
      rc := ?_
      rv := fun p q => hX.rv (p + 1) q }
  · intro q
    ext z
    rfl
  · intro q
    show LinearMap.ker (X.v 1 q) = LinearMap.range (LinearMap.range (X.v 0 q)).subtype
    rw [Submodule.range_subtype]
    exact hX.rv 0 q

theorem a_d {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) :
    X.a (p + 1) (X.dA p x) = X.v p 0 (X.a p x) :=
  LinearMap.congr_fun (hX.ha p) x

theorem c_d {X : DblData R} (hX : X.Good) (q : ℕ) (y : X.C q) :
    X.c (q + 1) (X.dC q y) = X.h 0 q (X.c q y) :=
  LinearMap.congr_fun (hX.hc q) y

theorem a_injective {X : DblData R} (hX : X.Good) (p : ℕ) : Function.Injective (X.a p) :=
  LinearMap.ker_eq_bot.mp (hX.ka p)

theorem c_injective {X : DblData R} (hX : X.Good) (q : ℕ) : Function.Injective (X.c q) :=
  LinearMap.ker_eq_bot.mp (hX.kc q)

theorem ex_a {X : DblData R} (hX : X.Good) (p : ℕ) {z : X.D p 0} (hz : X.h p 0 z = 0) :
    ∃ x, X.a p x = z := by
  have hm : z ∈ LinearMap.ker (X.h p 0) := LinearMap.mem_ker.mpr hz
  rw [hX.ra p] at hm
  exact LinearMap.mem_range.mp hm

theorem ex_h {X : DblData R} (hX : X.Good) (p q : ℕ) {z : X.D p (q + 1)} (hz : X.h p (q + 1) z = 0) :
    ∃ w, X.h p q w = z := by
  have hm : z ∈ LinearMap.ker (X.h p (q + 1)) := LinearMap.mem_ker.mpr hz
  rw [hX.rh p q] at hm
  exact LinearMap.mem_range.mp hm

theorem ex_c {X : DblData R} (hX : X.Good) (q : ℕ) {z : X.D 0 q} (hz : X.v 0 q z = 0) :
    ∃ y, X.c q y = z := by
  have hm : z ∈ LinearMap.ker (X.v 0 q) := LinearMap.mem_ker.mpr hz
  rw [hX.rc q] at hm
  exact LinearMap.mem_range.mp hm

theorem hh {X : DblData R} (hX : X.Good) (p q : ℕ) (z : X.D p q) : X.h p (q + 1) (X.h p q z) = 0 := by
  have hm : X.h p q z ∈ LinearMap.ker (X.h p (q + 1)) := by
    rw [hX.rh p q]; exact LinearMap.mem_range_self _ z
  exact LinearMap.mem_ker.mp hm

theorem ha0 {X : DblData R} (hX : X.Good) (p : ℕ) (x : X.A p) : X.h p 0 (X.a p x) = 0 := by
  have hm : X.a p x ∈ LinearMap.ker (X.h p 0) := by
    rw [hX.ra p]; exact LinearMap.mem_range_self _ x
  exact LinearMap.mem_ker.mp hm

theorem vc0 {X : DblData R} (hX : X.Good) (q : ℕ) (y : X.C q) : X.v 0 q (X.c q y) = 0 := by
  have hm : X.c q y ∈ LinearMap.ker (X.v 0 q) := by
    rw [hX.rc q]; exact LinearMap.mem_range_self _ y
  exact LinearMap.mem_ker.mp hm

end Good

def Rel : (n : ℕ) → (X : DblData R) → X.A n → X.C n → Prop
  | 0, X => fun x y => X.a 0 x = X.c 0 y
  | n + 1, X => fun x y => ∃ z : X.D 0 n, X.h 0 n z = X.c (n + 1) y ∧ Rel n X.shift x (X.up n z)

theorem rel_zero {X : DblData R} {x : X.A 0} {y : X.C 0} : Rel 0 X x y ↔ X.a 0 x = X.c 0 y := Iff.rfl

theorem rel_succ {n : ℕ} {X : DblData R} {x : X.A (n + 1)} {y : X.C (n + 1)} :
    Rel (n + 1) X x y ↔ ∃ z : X.D 0 n, X.h 0 n z = X.c (n + 1) y ∧ Rel n X.shift x (X.up n z) :=
  Iff.rfl

theorem Rel.zero : ∀ (n : ℕ) (X : DblData R), Rel n X 0 0
  | 0, X => rel_zero.mpr (by rw [map_zero, map_zero])
  | n + 1, X => rel_succ.mpr ⟨0, by rw [map_zero, map_zero], by rw [map_zero]; exact Rel.zero n X.shift⟩

theorem Rel.add : ∀ (n : ℕ) (X : DblData R) {x₁ x₂ : X.A n} {y₁ y₂ : X.C n},
    Rel n X x₁ y₁ → Rel n X x₂ y₂ → Rel n X (x₁ + x₂) (y₁ + y₂) := by
  intro n
  induction n with
  | zero =>
    intro X x₁ x₂ y₁ y₂ h₁ h₂
    exact rel_zero.mpr (by rw [map_add, map_add, rel_zero.mp h₁, rel_zero.mp h₂])
  | succ n ih =>
    intro X x₁ x₂ y₁ y₂ h₁ h₂
    obtain ⟨z₁, e₁, r₁⟩ := rel_succ.mp h₁
    obtain ⟨z₂, e₂, r₂⟩ := rel_succ.mp h₂
    refine rel_succ.mpr ⟨z₁ + z₂, by rw [map_add, map_add, e₁, e₂], ?_⟩
    rw [map_add]
    exact ih X.shift r₁ r₂

theorem Rel.smul : ∀ (n : ℕ) (X : DblData R) (r : R) {x : X.A n} {y : X.C n},
    Rel n X x y → Rel n X (r • x) (r • y) := by
  intro n
  induction n with
  | zero =>
    intro X r x y h₁
    exact rel_zero.mpr (by rw [map_smul, map_smul, rel_zero.mp h₁])
  | succ n ih =>
    intro X r x y h₁
    obtain ⟨z, e, r₁⟩ := rel_succ.mp h₁
    refine rel_succ.mpr ⟨r • z, by rw [map_smul, map_smul, e], ?_⟩
    rw [map_smul]
    exact ih X.shift r r₁

def relSub (n : ℕ) (X : DblData R) : Submodule R (X.A n × X.C n) where
  carrier := {p | Rel n X p.1 p.2}
  add_mem' h₁ h₂ := Rel.add n X h₁ h₂
  zero_mem' := Rel.zero n X
  smul_mem' r _ hp := Rel.smul n X r hp

theorem cocycle : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x y, Rel n X x y → X.dA n x = 0 ∧ X.dC n y = 0 := by
  intro n
  induction n with
  | zero =>
    intro X hX x y hr
    have hr' := rel_zero.mp hr
    refine ⟨hX.a_injective 1 ?_, hX.c_injective 1 ?_⟩
    · rw [hX.a_d, hr', hX.vc0, map_zero]
    · rw [hX.c_d, ← hr', hX.ha0, map_zero]
  | succ n ih =>
    intro X hX x y hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    refine ⟨(ih X.shift hX.shift x (X.up n z) hr).1, hX.c_injective (n + 2) ?_⟩
    rw [hX.c_d, ← hz, hX.hh, map_zero]

theorem exA : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, X.dA n x = 0 → ∃ y, Rel n X x y := by
  intro n
  induction n with
  | zero =>
    intro X hX x hx
    have hv : X.v 0 0 (X.a 0 x) = 0 := by rw [← hX.a_d, hx, map_zero]
    obtain ⟨y, hy⟩ := hX.ex_c 0 hv
    exact ⟨y, rel_zero.mpr hy.symm⟩
  | succ n ih =>
    intro X hX x hx
    obtain ⟨w, hw⟩ := ih X.shift hX.shift x hx
    obtain ⟨z, rfl⟩ := X.up_surj n w
    have hc := (cocycle n X.shift hX.shift x (X.up n z) hw).2
    have h1 : X.h 1 n (X.v 0 n z) = 0 := by
      have := congrArg (X.shift.c (n + 1)) hc
      rw [map_zero] at this
      exact this
    have h2 : X.v 0 (n + 1) (X.h 0 n z) = 0 := by rw [X.comm_apply]; exact h1
    obtain ⟨y, hy⟩ := hX.ex_c (n + 1) h2
    exact ⟨y, rel_succ.mpr ⟨z, hy.symm, hw⟩⟩

theorem exC : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ y, X.dC n y = 0 → ∃ x, Rel n X x y := by
  intro n
  induction n with
  | zero =>
    intro X hX y hy
    have hh0 : X.h 0 0 (X.c 0 y) = 0 := by rw [← hX.c_d, hy, map_zero]
    obtain ⟨x, hx⟩ := hX.ex_a 0 hh0
    exact ⟨x, rel_zero.mpr hx⟩
  | succ n ih =>
    intro X hX y hy
    have hh0 : X.h 0 (n + 1) (X.c (n + 1) y) = 0 := by rw [← hX.c_d, hy, map_zero]
    obtain ⟨z, hz⟩ := hX.ex_h 0 n hh0
    have hd : X.shift.dC n (X.up n z) = 0 := by
      apply hX.shift.c_injective (n + 1)
      rw [map_zero]
      show X.h 1 n (X.v 0 n z) = 0
      rw [← X.comm_apply, hz, hX.vc0]
    obtain ⟨x, hx⟩ := ih X.shift hX.shift (X.up n z) hd
    exact ⟨x, rel_succ.mpr ⟨z, hz, hx⟩⟩

theorem bdA : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x₀ : X.A n, Rel (n + 1) X (X.dA n x₀) 0 := by
  intro n
  induction n with
  | zero =>
    intro X hX x₀
    refine rel_succ.mpr ⟨X.a 0 x₀, by rw [hX.ha0, map_zero], rel_zero.mpr ?_⟩
    exact hX.a_d 0 x₀
  | succ n ih =>
    intro X hX x₀
    refine rel_succ.mpr ⟨0, by rw [map_zero, map_zero], ?_⟩
    rw [map_zero]
    exact ih X.shift hX.shift x₀

theorem bdC (n : ℕ) (X : DblData R) (hX : X.Good) (y₀ : X.C n) : Rel (n + 1) X 0 (X.dC n y₀) := by
  refine rel_succ.mpr ⟨X.c n y₀, (hX.c_d n y₀).symm, ?_⟩
  have hu : X.up n (X.c n y₀) = 0 := by
    apply hX.shift.c_injective n
    rw [map_zero]
    exact hX.vc0 n y₀
  rw [hu]
  exact Rel.zero n X.shift

theorem kerC : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ y, Rel n X 0 y → y ∈ bdry X.dC n := by
  intro n
  induction n with
  | zero =>
    intro X hX y hr
    have hr' := rel_zero.mp hr
    rw [map_zero] at hr'
    exact (Submodule.mem_bot R).mpr (hX.c_injective 0 (by rw [← hr', map_zero]))
  | succ n ih =>
    intro X hX y hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    have hb := ih X.shift hX.shift (X.up n z) hr
    show y ∈ LinearMap.range (X.dC n)
    rcases n with _ | m
    · have hb0 : X.up 0 z = 0 := (Submodule.mem_bot R).mp hb
      have hv : X.v 0 0 z = 0 := by
        have := congrArg (X.shift.c 0) hb0
        rw [map_zero] at this
        exact this
      obtain ⟨y₀, hy₀⟩ := hX.ex_c 0 hv
      refine LinearMap.mem_range.mpr ⟨y₀, hX.c_injective 1 ?_⟩
      rw [hX.c_d, hy₀, hz]
    · have hb' : X.up (m + 1) z ∈ LinearMap.range (X.shift.dC m) := hb
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hb'
      obtain ⟨z', rfl⟩ := X.up_surj m w
      have e : X.v 0 (m + 1) (X.h 0 m z') = X.v 0 (m + 1) z := by
        rw [X.comm_apply]
        exact congrArg (X.shift.c (m + 1)) hw
      obtain ⟨y₀, hy₀⟩ := hX.ex_c (m + 1) (show X.v 0 (m + 1) (z - X.h 0 m z') = 0 by rw [map_sub, e, sub_self])
      refine LinearMap.mem_range.mpr ⟨y₀, hX.c_injective (m + 2) ?_⟩
      rw [hX.c_d, hy₀, map_sub, hX.hh, sub_zero, hz]

theorem kerA : ∀ (n : ℕ) (X : DblData R), X.Good → ∀ x, Rel n X x 0 → x ∈ bdry X.dA n := by
  intro n
  induction n with
  | zero =>
    intro X hX x hr
    have hr' := rel_zero.mp hr
    rw [map_zero] at hr'
    exact (Submodule.mem_bot R).mpr (hX.a_injective 0 (by rw [hr', map_zero]))
  | succ n ih =>
    intro X hX x hr
    obtain ⟨z, hz, hr⟩ := rel_succ.mp hr
    have hz0 : X.h 0 n z = 0 := by rw [hz, map_zero]
    show x ∈ LinearMap.range (X.dA n)
    rcases n with _ | m
    · obtain ⟨x₀, hx₀⟩ := hX.ex_a 0 hz0
      have hr' := rel_zero.mp hr
      refine LinearMap.mem_range.mpr ⟨x₀, hX.a_injective 1 ?_⟩
      rw [hX.a_d, hx₀]
      exact hr'.symm
    · obtain ⟨z', hz'⟩ := hX.ex_h 0 m hz0
      have hu : X.up (m + 1) z = X.shift.dC m (X.up m z') := by
        apply hX.shift.c_injective (m + 1)
        show X.v 0 (m + 1) z = X.h 1 m (X.v 0 m z')
        rw [← hz', X.comm_apply]
      rw [hu] at hr
      have h0 := bdC m X.shift hX.shift (X.up m z')
      have hs : Rel (m + 1) X.shift x 0 := by
        have h1 : (x, X.shift.dC m (X.up m z')) ∈ relSub (m + 1) X.shift := hr
        have h2 : ((0 : X.shift.A (m + 1)), X.shift.dC m (X.up m z')) ∈ relSub (m + 1) X.shift := h0
        have h3 : Rel (m + 1) X.shift (x - (0 : X.A (m + 1 + 1))) (X.shift.dC m (X.up m z') - X.shift.dC m (X.up m z')) :=
          (relSub (m + 1) X.shift).sub_mem h1 h2
        rw [sub_zero, sub_self] at h3
        exact h3
      exact ih X.shift hX.shift x hs

end DblData

theorem graph_equiv {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (dM : M →ₗ[R] M') (dN : N →ₗ[R] N') (BM : Submodule R M) (BN : Submodule R N)
    (G : Submodule R (M × N))
    (hZ : ∀ x y, (x, y) ∈ G → dM x = 0 ∧ dN y = 0)
    (hM : ∀ x, dM x = 0 → ∃ y, (x, y) ∈ G)
    (hN : ∀ y, dN y = 0 → ∃ x, (x, y) ∈ G)
    (hBM : ∀ x ∈ BM, (x, (0 : N)) ∈ G) (hBN : ∀ y ∈ BN, ((0 : M), y) ∈ G)
    (hKM : ∀ x, (x, (0 : N)) ∈ G → x ∈ BM) (hKN : ∀ y, ((0 : M), y) ∈ G → y ∈ BN) :
    Nonempty ((LinearMap.ker dM ⧸ BM.comap (LinearMap.ker dM).subtype) ≃ₗ[R]
      (LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype)) := by
  classical
  choose f hf using fun x : LinearMap.ker dM => hM x.1 (LinearMap.mem_ker.mp x.2)
  have hfz : ∀ x, f x ∈ LinearMap.ker dN := fun x => LinearMap.mem_ker.mpr (hZ _ _ (hf x)).2
  let g : LinearMap.ker dM → LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype :=
    fun x => Submodule.Quotient.mk ⟨f x, hfz x⟩
  have key : ∀ (x : LinearMap.ker dM) (y : LinearMap.ker dN), ((x : M), (y : N)) ∈ G →
      g x = Submodule.Quotient.mk y := by
    intro x y hxy
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [Submodule.mem_comap]
    apply hKN
    have := G.sub_mem (hf x) hxy
    rw [Prod.mk_sub_mk, sub_self] at this
    exact this
  let F : LinearMap.ker dM →ₗ[R] LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype :=
    { toFun := g
      map_add' := fun x₁ x₂ => by
        rw [key (x₁ + x₂) (⟨f x₁, hfz x₁⟩ + ⟨f x₂, hfz x₂⟩) (G.add_mem (hf x₁) (hf x₂))]
        rfl
      map_smul' := fun r x => by
        rw [key (r • x) (r • ⟨f x, hfz x⟩) (G.smul_mem r (hf x))]
        rfl }
  have hQ : BM.comap (LinearMap.ker dM).subtype ≤ LinearMap.ker F := by
    intro x hx
    rw [LinearMap.mem_ker]
    change g x = 0
    rw [key x 0 (hBM x.1 hx)]
    rfl
  let Φ := (BM.comap (LinearMap.ker dM).subtype).liftQ F hQ
  have inj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change g x = 0 at hq
    have hq' : f x ∈ BN := by
      have := (Submodule.Quotient.mk_eq_zero _).mp hq
      exact this
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    apply hKM
    have := G.sub_mem (hf x) (hBN _ hq')
    rw [Prod.mk_sub_mk, sub_zero, sub_self] at this
    exact this
  have surj : Function.Surjective Φ := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx⟩ := hN y.1 (LinearMap.mem_ker.mp y.2)
    refine ⟨Submodule.Quotient.mk ⟨x, LinearMap.mem_ker.mpr (hZ _ _ hx).1⟩, ?_⟩
    exact key _ y hx
  exact ⟨LinearEquiv.ofBijective Φ ⟨inj, surj⟩⟩

namespace DblData

theorem bdryA (X : DblData R) (hX : X.Good) : ∀ (n : ℕ) (x : X.A n), x ∈ bdry X.dA n → Rel n X x 0 := by
  intro n
  cases n with
  | zero =>
    intro x hx
    have hx0 : x = 0 := (Submodule.mem_bot R).mp hx
    subst hx0
    exact Rel.zero 0 X
  | succ n =>
    intro x hx
    obtain ⟨x₀, rfl⟩ := (LinearMap.mem_range (f := X.dA n)).mp hx
    exact bdA n X hX x₀

theorem bdryC (X : DblData R) (hX : X.Good) : ∀ (n : ℕ) (y : X.C n), y ∈ bdry X.dC n → Rel n X 0 y := by
  intro n
  cases n with
  | zero =>
    intro y hy
    have hy0 : y = 0 := (Submodule.mem_bot R).mp hy
    subst hy0
    exact Rel.zero 0 X
  | succ n =>
    intro y hy
    obtain ⟨y₀, rfl⟩ := (LinearMap.mem_range (f := X.dC n)).mp hy
    exact bdC n X hX y₀

theorem equiv (X : DblData R) (hX : X.Good) (n : ℕ) : Nonempty (H X.dA n ≃ₗ[R] H X.dC n) :=
  graph_equiv (X.dA n) (X.dC n) (bdry X.dA n) (bdry X.dC n) (relSub n X)
    (fun x y hr => cocycle n X hX x y hr) (fun x hx => exA n X hX x hx) (fun y hy => exC n X hX y hy)
    (fun x hx => bdryA X hX n x hx) (fun y hy => bdryC X hX n y hy)
    (fun x hr => kerA n X hX x hr) (fun y hr => kerC n X hX y hr)

end DblData

end Stair

end GroundTheory.Heights₂.Heights.Kleiman.CechDouble
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace CechDouble

open Cech

section General

variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {m : ℕ} {U : Finset (Fin m)}


variable (S E U) in
abbrev dE (p : ℕ) : Cochain (fun _ : Cell U => E) p →ₗ[S] Cochain (fun _ : Cell U => E) (p + 1) :=
  Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) p

theorem dE_dE (p : ℕ) (s : Cochain (fun _ : Cell U => E) p) : dE S E U (p + 1) (dE S E U p s) = 0 :=
  CechDSq.proof m U S (fun _ => E) (Cech.idRes S E U) (fun _ _ _ _ _ => rfl) p s

theorem dE_const (e : E) : dE S E U 0 (fun _ => e) = 0 :=
  Cech.d_zero_of_compat (G := fun _ : Cell U => E) (ρ := Cech.idRes S E U) (fun _ => e) (fun _ _ _ => rfl)

theorem d_mem (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (p : ℕ)
    {s : Cochain (fun _ : Cell U => E) p} (hs : s ∈ Cdeg (fun _ : Cell U => E) G p) :
    dE S E U p s ∈ Cdeg (fun _ : Cell U => E) G (p + 1) := fun J _ => by
  rw [Cech.d_apply]
  refine Submodule.sum_mem _ fun j _ => zsmul_mem ?_ _
  exact hG _ _ (face_subset J j) (hs _ (Set.mem_univ _))

def dRes (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (p : ℕ) :
    Cdeg (fun _ : Cell U => E) G p →ₗ[S] Cdeg (fun _ : Cell U => E) G (p + 1) :=
  (dE S E U p).restrict fun _ hs => d_mem G hG p hs

theorem mem_bdry_iff (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) :
    ∀ (n : ℕ) (z : Cdeg (fun _ : Cell U => E) G n),
      z ∈ Stair.bdry (dRes G hG) n ↔ (z : Cochain (fun _ : Cell U => E) n) ∈
        Cech.bdryDeg (fun _ : Cell U => E) G (Cech.idRes S E U) n
  | 0, z => by
      change z ∈ (⊥ : Submodule S _) ↔ (z : Cochain (fun _ : Cell U => E) 0) ∈ (⊥ : Submodule S _)
      rw [Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  | n + 1, z => by
      change z ∈ LinearMap.range (dRes G hG n) ↔
        (z : Cochain (fun _ : Cell U => E) (n + 1)) ∈ (Cdeg (fun _ : Cell U => E) G n).map (dE S E U n)
      rw [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t.1, t.2, rfl⟩
      · rintro ⟨t, ht, hty⟩
        exact ⟨⟨t, ht⟩, Subtype.ext hty⟩

theorem hdeg_equiv (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (n : ℕ) :
    Nonempty (Cech.Hdeg (fun _ : Cell U => E) G (Cech.idRes S E U) n ≃ₗ[S] Stair.H (dRes G hG) n) := by
  let e : LinearMap.ker (dRes G hG n) ≃ₗ[S] Cech.cocyDeg (fun _ : Cell U => E) G (Cech.idRes S E U) n :=
    { toFun := fun z => ⟨z.1.1, LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.mem_ker.mp z.2)), z.1.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.2⟩, LinearMap.mem_ker.mpr (Subtype.ext (LinearMap.mem_ker.mp z.2.1))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨(Submodule.Quotient.equiv _ _ e ?_).symm⟩
  ext z
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
  exact mem_bdry_iff G hG n _

theorem aug_mono {Ω : Type w} [Field Ω] {r : ℕ} {y : Fin (r + 1) → Ω} {ι : Type*}
    (G : ι → Chart y → Submodule S E) (A : ι → Submodule S E) (rel : ι → ι → Prop)
    (hG : ∀ i i' J, rel i i' → G i J ≤ G i' J) (hA : ∀ i, Cech.AugExact S (G i) (A i)) :
    ∀ i i', rel i i' → A i ≤ A i' := by
  intro i i' hii' e he
  by_cases h0 : Nonempty (Cech.Idx (support y) 0)
  · obtain ⟨J₀⟩ := h0
    obtain ⟨b, hb, hbe⟩ := (hA i').2.2.1 (fun _ => e)
      (fun J _ => hG i i' J.1 hii' ((hA i).1 J.1 he)) (dE_const e)
    have h1 : e = b := hbe J₀
    rw [h1]
    exact hb
  · have h1 : e = 0 := (hA i).2.1 e he fun J => (h0 ⟨J⟩).elim
    rw [h1]
    exact zero_mem _

end General

section Double

variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {Ω : Type w} [Field Ω] {N r : ℕ}
  {x : Fin (N + 1) → Ω} {y : Fin (r + 1) → Ω}


variable (E x y) in
abbrev W (p q : ℕ) : Type v := Cochain (fun _ : Chart x => Cochain (fun _ : Chart y => E) q) p


variable (S E x y) in
def vW (p q : ℕ) : W E x y p q →ₗ[S] W E x y (p + 1) q :=
  Cech.d (fun _ : Chart x => Cochain (fun _ : Chart y => E) q) (Cech.idRes S _ (support x)) p


variable (S E x y) in
def hW (p q : ℕ) : W E x y p q →ₗ[S] W E x y p (q + 1) :=
  Cech.mapC (fun _ : Chart x => dE S E (support y) q) p

theorem hW_apply (p q : ℕ) (s : W E x y p q) (I : Idx (support x) p) :
    hW S E x y p q s I = dE S E (support y) q (s I) := rfl

theorem vW_apply (p q : ℕ) (s : W E x y p q) (I' : Idx (support x) (p + 1)) (J : Idx (support y) q) :
    vW S E x y p q s I' J = dE S E (support x) p (fun I => s I J) I' := by
  simp only [vW, dE, Cech.d_apply, Cech.idRes, LinearMap.id_apply, Finset.sum_apply, Pi.smul_apply]

theorem hW_vW (p q : ℕ) (s : W E x y p q) :
    hW S E x y (p + 1) q (vW S E x y p q s) = vW S E x y p (q + 1) (hW S E x y p q s) :=
  Cech.mapC_d (ρ := Cech.idRes S _ (support x)) (ρ' := Cech.idRes S _ (support x))
    (fun _ : Chart x => dE S E (support y) q) (fun _ _ _ _ => rfl) p s

theorem vW_vW (p q : ℕ) (s : W E x y p q) : vW S E x y (p + 1) q (vW S E x y p q s) = 0 :=
  CechDSq.proof _ _ S (fun _ : Chart x => Cochain (fun _ : Chart y => E) q) (Cech.idRes S _ (support x))
    (fun _ _ _ _ _ => rfl) p s

variable (M : Chart x → Chart y → Submodule S E)

def Dsub (p q : ℕ) : Submodule S (W E x y p q) :=
  Submodule.pi Set.univ fun I : Idx (support x) p => Cdeg (fun _ : Chart y => E) (M I.1) q

theorem mem_Dsub {p q : ℕ} {s : W E x y p q} : s ∈ Dsub M p q ↔ ∀ I J, s I J ∈ M I.1 J.1 := by
  simp [Dsub, Cdeg, Submodule.mem_pi]

variable {M}

theorem vW_mem (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J) {p q : ℕ}
    {s : W E x y p q} (hs : s ∈ Dsub M p q) : vW S E x y p q s ∈ Dsub M (p + 1) q := by
  rw [mem_Dsub] at hs ⊢
  intro I' J
  rw [vW_apply]
  exact d_mem (fun I => M I J.1) (fun I I' hI => hM₁ I I' J.1 hI) p (fun I _ => hs I J) I' (Set.mem_univ _)

theorem hW_mem (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J') {p q : ℕ}
    {s : W E x y p q} (hs : s ∈ Dsub M p q) : hW S E x y p q s ∈ Dsub M p (q + 1) := by
  rw [mem_Dsub] at hs ⊢
  intro I J'
  rw [hW_apply]
  exact d_mem (M I.1) (hM₂ I.1) q (fun J _ => hs I J) J' (Set.mem_univ _)

variable (Ax : Chart x → Submodule S E) (Bx : Chart y → Submodule S E)

def dbl (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J)
    (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J')
    (hA : ∀ I, Cech.AugExact S (M I) (Ax I)) (hB : ∀ J, Cech.AugExact S (fun I => M I J) (Bx J)) :
    Stair.DblData.{u, v} S where
  D p q := Dsub M p q
  v p q := (vW S E x y p q).restrict fun _ hs => vW_mem hM₁ hs
  h p q := (hW S E x y p q).restrict fun _ hs => hW_mem hM₂ hs
  comm p q := LinearMap.ext fun s => Subtype.ext (hW_vW p q s.1).symm
  A p := Cdeg (fun _ : Chart x => E) Ax p
  dA := dRes Ax (aug_mono M Ax _ hM₁ hA)
  a _ :=
    { toFun := fun s => ⟨fun I _ => s.1 I, (mem_Dsub M).2 fun I J => (hA I.1).1 J.1 (s.2 I (Set.mem_univ _))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  C q := Cdeg (fun _ : Chart y => E) Bx q
  dC := dRes Bx (aug_mono (fun J I => M I J) Bx _ (fun J J' I hJ => hM₂ I J J' hJ) hB)
  c _ :=
    { toFun := fun t => ⟨fun _ J => t.1 J, (mem_Dsub M).2 fun I J => (hB J.1).1 I.1 (t.2 J (Set.mem_univ _))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem dbl_good (hM₁ : ∀ (I I' : Chart x) (J : Chart y), I.1 ⊆ I'.1 → M I J ≤ M I' J)
    (hM₂ : ∀ (I : Chart x) (J J' : Chart y), J.1 ⊆ J'.1 → M I J ≤ M I J')
    (hA : ∀ I, Cech.AugExact S (M I) (Ax I)) (hB : ∀ J, Cech.AugExact S (fun I => M I J) (Bx J)) :
    (dbl Ax Bx hM₁ hM₂ hA hB).Good := by
  refine { ha := ?ha, hc := ?hc, ka := ?ka, ra := ?ra, rh := ?rh, kc := ?kc, rc := ?rc, rv := ?rv }
  case ha =>
    intro p
    refine LinearMap.ext fun s => Subtype.ext (funext fun I' => funext fun J => ?_)
    change dE S E (support x) p s.1 I' = vW S E x y p 0 (fun I _ => s.1 I) I' J
    rw [vW_apply]
  case hc =>
    intro q
    exact LinearMap.ext fun _ => rfl
  case ka =>
    intro p
    exact LinearMap.ker_eq_bot'.mpr fun s hs => Subtype.ext (funext fun I =>
      (hA I.1).2.1 _ (s.2 I (Set.mem_univ _)) fun J => congrFun (congrFun (congrArg Subtype.val hs) I) J)
  case ra =>
    intro p
    apply Submodule.ext
    intro f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hI : ∀ I : Idx (support x) p, ∃ b ∈ Ax I.1, ∀ J, f.1 I J = b := fun I =>
        (hA I.1).2.2.1 (f.1 I) (fun J _ => (mem_Dsub M).1 f.2 I J) (congrFun (congrArg Subtype.val hf) I)
      choose b hb hbf using hI
      exact ⟨⟨b, fun I _ => hb I⟩, Subtype.ext (funext fun I => funext fun J => (hbf I J).symm)⟩
    · rintro ⟨s, rfl⟩
      exact Subtype.ext (funext fun I => dE_const (s.1 I))
  case rh =>
    intro p q
    apply Submodule.ext
    intro f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hI : ∀ I : Idx (support x) p, ∃ t ∈ Cdeg (fun _ : Chart y => E) (M I.1) q,
          dE S E (support y) q t = f.1 I := fun I =>
        (hA I.1).2.2.2 q (f.1 I) (fun J _ => (mem_Dsub M).1 f.2 I J) (congrFun (congrArg Subtype.val hf) I)
      choose t ht htf using hI
      exact ⟨⟨t, (mem_Dsub M).2 fun I J => ht I J (Set.mem_univ _)⟩, Subtype.ext (funext htf)⟩
    · rintro ⟨s, rfl⟩
      exact Subtype.ext (funext fun I => dE_dE q (s.1 I))
  case kc =>
    intro q
    exact LinearMap.ker_eq_bot'.mpr fun t ht => Subtype.ext (funext fun J =>
      (hB J.1).2.1 _ (t.2 J (Set.mem_univ _)) fun I => congrFun (congrFun (congrArg Subtype.val ht) I) J)
  case rc =>
    intro q
    apply Submodule.ext
    intro f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hJ : ∀ J : Idx (support y) q, ∃ b ∈ Bx J.1, ∀ I, f.1 I J = b := fun J =>
        (hB J.1).2.2.1 (fun I => f.1 I J) (fun I _ => (mem_Dsub M).1 f.2 I J) (funext fun I' => by
          rw [← vW_apply]
          exact congrFun (congrFun (congrArg Subtype.val hf) I') J)
      choose b hb hbf using hJ
      exact ⟨⟨b, fun J _ => hb J⟩, Subtype.ext (funext fun I => funext fun J => (hbf J I).symm)⟩
    · rintro ⟨t, rfl⟩
      refine Subtype.ext (funext fun I' => funext fun J => ?_)
      change vW S E x y 0 q _ I' J = 0
      rw [vW_apply]
      exact congrFun (dE_const (t.1 J)) I'
  case rv =>
    intro p q
    apply Submodule.ext
    intro f
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hf
      have hJ : ∀ J : Idx (support y) q, ∃ t ∈ Cdeg (fun _ : Chart x => E) (fun I => M I J.1) p,
          dE S E (support x) p t = fun I => f.1 I J := fun J =>
        (hB J.1).2.2.2 p (fun I => f.1 I J) (fun I _ => (mem_Dsub M).1 f.2 I J) (funext fun I' => by
          rw [← vW_apply]
          exact congrFun (congrFun (congrArg Subtype.val hf) I') J)
      choose t ht htf using hJ
      refine ⟨⟨fun I J => t J I, (mem_Dsub M).2 fun I J => ht J I (Set.mem_univ _)⟩,
        Subtype.ext (funext fun I' => funext fun J => ?_)⟩
      change vW S E x y p q _ I' J = _
      rw [vW_apply]
      exact congrFun (htf J) I'
    · rintro ⟨s, rfl⟩
      exact Subtype.ext (vW_vW p q s.1)

end Double

end CechDouble

theorem CechDouble.proof : CechDouble.Statement := by
  intro S _ Ω _ N r x y E _ _ A B M hM₁ hM₂ hA hB n
  obtain ⟨e₁⟩ := CechDouble.hdeg_equiv A (CechDouble.aug_mono M A _ hM₁ hA) n
  obtain ⟨e₂⟩ := CechDouble.hdeg_equiv B
    (CechDouble.aug_mono (fun J I => M I J) B _ (fun J J' I hJ => hM₂ I J J' hJ) hB) n
  obtain ⟨e₃⟩ := CechDouble.Stair.DblData.equiv _ (CechDouble.dbl_good A B hM₁ hM₂ hA hB) n
  exact ⟨(e₁.trans e₃).trans e₂.symm⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
