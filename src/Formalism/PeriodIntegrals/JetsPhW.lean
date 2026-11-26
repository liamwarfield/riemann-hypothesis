module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.JetsPhW
noncomputable section

open Classical

namespace PI.JetsPhW

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹

def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n

section Ops

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

def add (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex

def mulBy (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex

def phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a ph

def be (l ex ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

end Ops

def jet {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (i : ℕ) : ℂ_[p] :=
  (i.factorial : ℂ_[p]) * PowerSeries.coeff i (PowerSeries.subst ex ph : PowerSeries ℂ_[p])

def cubeE {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) - phAt ph (add l ex (Xv 0) (Xv 1)) -
    phAt ph (add l ex (Xv 1) (Xv 2)) - phAt ph (add l ex (Xv 2) (Xv 0)) +
    phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)

def High : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    Simeq (cubeE (flog W wq) ex ph) 0 →
    ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (jet ex ph i)

def One : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X → p ≠ 2 →
    Simeq (phAt ph (mulBy (flog W wq) ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ())) →
    IsIntP (jet ex ph 1)

def Two : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    Simeq (be (flog W wq) ex ph (mulBy (flog W wq) ex a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be (flog W wq) ex ph (Xv 0) (mulBy (flog W wq) ex b (Xv 1))) →
    IsIntP ((a - b) * jet ex ph 2)

def Target : Prop := High ∧ One ∧ Two

def LogOk {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) : Prop :=
  PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex l = PowerSeries.X ∧
    ∃ v : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.coeff n v)) ∧ v * dX l = 1

def InvOmega : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    ∃ v : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.coeff n v)) ∧ v * dX (flog W wq) = 1

def HighG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    Simeq (cubeE l ex ph) 0 → ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (jet ex ph i)

def OneG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex → p ≠ 2 →
    Simeq (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ())) →
    IsIntP (jet ex ph 1)

def TwoG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]), LogOk l ex →
    Simeq (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex b (Xv 1))) →
    IsIntP ((a - b) * jet ex ph 2)

def Glue : Prop := InvOmega → HighG → OneG → TwoG → Target

end PI.JetsPhW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitDetRoot
noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI

def UnitDetRootDefs.cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def UnitDetRootDefs.cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := UnitDetRootDefs.cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [UnitDetRootDefs.cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def UnitDetRootDefs.scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc

def UnitDetRootDefs.area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

abbrev UnitDetRootDefs.Sesq (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

def UnitDetRootDefs.altE (H : UnitDetRootDefs.Sesq V) (x y : V) : ℝ := (H x y).im

def UnitDetRootDefs.dualLat (H : UnitDetRootDefs.Sesq V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | ∀ y ∈ Λ, ∃ m : ℤ, UnitDetRootDefs.altE H x y = (m : ℝ)}
  zero_mem' := fun y _ => ⟨0, by simp [UnitDetRootDefs.altE]⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨k, hk⟩ := hb y hy
    exact ⟨m + k, by simp only [UnitDetRootDefs.altE] at hm hk ⊢; simp [hm, hk]⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by simp only [UnitDetRootDefs.altE] at hm ⊢; simp [hm]⟩

def UnitDetRootDefs.IsSelfDual (H : UnitDetRootDefs.Sesq V) (Λ : AddSubgroup V) : Prop := UnitDetRootDefs.dualLat H Λ = Λ

def UnitDetRootDefs.relIdx (Λ₁ Λ₂ : AddSubgroup V) : ℕ := Λ₁.relIndex Λ₂

def UnitDetRootDefs.IsIsom {W : Type*} [AddCommGroup W] [Module ℂ W] (H : UnitDetRootDefs.Sesq V) (H' : UnitDetRootDefs.Sesq W) (g : V →ₗ[ℂ] W) : Prop :=
  ∀ x y, H' (g x) (g y) = H x y

def UnitDetRootDefs.imgLat {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W) (Λ : AddSubgroup V) : AddSubgroup W :=
  Λ.map g.toAddMonoidHom

end General

section Coordinates

variable {n : Type*} [Fintype n]

def UnitDetRootDefs.matH (h : Matrix n n ℂ) : UnitDetRootDefs.Sesq (n → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => ∑ i, ∑ j, z i * h i j * conj (w j))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def UnitDetRootDefs.stdH (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] : UnitDetRootDefs.Sesq (n → ℂ) :=
  UnitDetRootDefs.matH (((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))

def UnitDetRootDefs.stdLat (L : PeriodPair) (n : Type*) : AddSubgroup (n → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => L.lattice.toAddSubgroup

end Coordinates

def UnitDetRootDefs.cmL (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) : PeriodPair :=
  UnitDetRootDefs.scalePair (UnitDetRootDefs.cmPair a b d ha hd) lam hlam

def UnitDetRootDefs.CmOK (a : ℕ) (b c : ℤ) (d : ℕ) : Prop := 4 * (a : ℤ) * c = b ^ 2 + d ∧ Odd a ∧ d % 8 = 7 ∧ d.Prime

def UnitDetRoot : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), UnitDetRootDefs.CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      UnitDetRootDefs.IsSelfDual (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, UnitDetRootDefs.cmTheta b d • x ∈ Λa) →
      UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      UnitDetRootDefs.relIdx Λa (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ : ℂ ≃+* ℂ, ‖σ κ‖ = 1) ∧
        ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
          UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
            (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) →
          UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 →
          ¬ l ∣ UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
          UnitDetRootDefs.relIdx (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0 →
          ‖ι κ‖ ^ 2 * ‖ι (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)))‖ = 1

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.TwChrOne
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwChrOne

section LocS

variable {R : Type*} [CommRing R]

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L

end LocS

abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E

section Red

variable {E : Type} [Field E] [NumberField E]

def redP (P : HeightOneSpectrum (𝓞 E)) (a : E) : 𝓞 E ⧸ P.asIdeal :=
  open Classical in
  if h : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r
  then h.choose else 0

def IntAt (P : HeightOneSpectrum (𝓞 E)) (a : E) : Prop :=
  ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r

end Red

section Deco

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stdLat : Submodule (𝓞 E) (Sp E n) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

end Deco

section Frames

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stabL (M : Submodule (𝓞 E) (Sp E n)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) where
  carrier := {c | ∀ x, c x ∈ M ↔ x ∈ M}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from LinearEquiv.apply_symm_apply a x] at h
    exact h.symm

def stdAt (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E n) := localization₂ P.asIdeal (stdLat E n)

end Frames

namespace Loc

section Groups

variable (k : Type) [CommRing k] (n c : ℕ)

def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0

def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0

def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]

def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}

def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0

def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i

variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 : (r * s) (eN k (n + c) (n + i)) - eN k (n + c) (n + i) =
        r (s (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) + (r (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) := by
      rw [map_sub]
      show r (s _) - _ = _
      abel
    rw [h1]
    exact add_mem (hr.1 i _ (hs.2.2 i)) (hr.2.2 i)

theorem R1cond_one : R1cond k n c 1 :=
  ⟨fun _ _ hv => hv, rfl, fun i => by
    show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
    rw [sub_self]
    exact zero_mem _⟩

def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {k n c}

def n1Arg (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range (c - 1), atN (r (eN k (n + c) (n + i + 1))) (n + i)

def Cbe (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :=
  R1 k n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom

end Groups

end Loc

abbrev HomE (E : Type) [Field E] (a b : ℕ) : Type := Sp E a →ₗ[E] Sp E b

namespace LocE

open Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

variable {P} in
open Classical in
def unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : K := if h : IsUnit (redP P a) then ((χ h.unit : Kˣ) : K) else 0


def sclLat (N : ℕ) (e : ℕ → ℤ) : Submodule (𝓞 E) (Sp E N) :=
  (stdAt E N P).comap
    ((LinearMap.pi fun l : Fin N => ((q : E) ^ e l.1)⁻¹ • (LinearMap.proj l : Sp E N →ₗ[E] E)).restrictScalars (𝓞 E))

section AtQ

variable (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

def parL (kj n c : ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) fun l => if kj ≤ l ∧ l < n then 1 else 0

def JQ (kj n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  stabL E (n + c) (stdAt E (n + c) P) ⊓ stabL E (n + c) (parL P q kj n c)

variable {P}

def lamQB (kj n : ℕ) {N : ℕ} (h : HomE E N N) : K :=
  (unitV ξ (Matrix.det (Matrix.of fun s t : Fin (n - kj) => atN (h (eN E N (kj + t.1))) (kj + s.1))))⁻¹

end AtQ

end LocE

section Target

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def ChiL (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ)
    (h r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : K :=
  (psi (Loc.n1Arg r))⁻¹ * LocE.lamQB ξ kj N ((h⁻¹ * r * h : Sp E (N + c) ≃ₗ[E] Sp E (N + c))).toLinearMap

def ChrOkL (P : HeightOneSpectrum (𝓞 E)) (psi : E → K) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ)
    (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Prop :=
  (∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h, ChiL P psi ξ kj N c h r ≠ 0) ∧
  ∀ r ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h, ∀ r' ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h,
    ∀ r'' ∈ Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) h,
    (∀ x, r'' (Loc.inX E N c x) = r (r' (Loc.inX E N c x))) →
      ChiL P psi ξ kj N c h r'' = ChiL P psi ξ kj N c h r * ChiL P psi ξ kj N c h r'

end Target

def TwChrOne : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (psi : E → K)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj N c : ℕ), (∀ x, IntAt P x → psi x = 1) → ChrOkL P psi ξ kj N c 1

end PI.TwChrOne
end
end

section -- merged from Formalism.PeriodIntegrals.TwNormLat
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwNormLat

section LocS

variable {R : Type*} [CommRing R]

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L

end LocS

abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E

section Red

variable {E : Type} [Field E] [NumberField E]

def IntAt (P : HeightOneSpectrum (𝓞 E)) (a : E) : Prop :=
  ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r

end Red

section Deco

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stdLat : Submodule (𝓞 E) (Sp E n) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

end Deco

section Frames

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stabL (M : Submodule (𝓞 E) (Sp E n)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) where
  carrier := {c | ∀ x, c x ∈ M ↔ x ∈ M}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from LinearEquiv.apply_symm_apply a x] at h
    exact h.symm

def stdAt (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E n) := localization₂ P.asIdeal (stdLat E n)

def GLint (P : HeightOneSpectrum (𝓞 E)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) := stabL E n (stdAt E n P)

end Frames

namespace Loc

section Groups

variable (k : Type) [CommRing k] (n c : ℕ)

def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0

def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0

def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]

def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}

def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0

def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i

variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 : (r * s) (eN k (n + c) (n + i)) - eN k (n + c) (n + i) =
        r (s (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) + (r (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) := by
      rw [map_sub]
      show r (s _) - _ = _
      abel
    rw [h1]
    exact add_mem (hr.1 i _ (hs.2.2 i)) (hr.2.2 i)

theorem R1cond_one : R1cond k n c 1 :=
  ⟨fun _ _ hv => hv, rfl, fun i => by
    show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
    rw [sub_self]
    exact zero_mem _⟩

def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {k n c}

def Cbe (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :=
  R1 k n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom

def prX (C : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : Subgroup ((Fin n → k) ≃ₗ[k] (Fin n → k)) where
  carrier := {g | ∃ r ∈ C, ∀ x, r (inX k n c x) = inX k n c (g x)}
  one_mem' := ⟨1, C.one_mem, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨r, hr, h1⟩ ⟨s, hs, h2⟩
    refine ⟨r * s, C.mul_mem hr hs, fun x => ?_⟩
    show r (s _) = _
    rw [h2, h1]
    rfl
  inv_mem' := by
    rintro a ⟨r, hr, h1⟩
    refine ⟨r⁻¹, C.inv_mem hr, fun x => ?_⟩
    show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h1]
    show _ = inX k n c (a (a.symm x))
    rw [LinearEquiv.apply_symm_apply]

end Groups

end Loc

namespace LocE

open Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)



def sclLat (N : ℕ) (e : ℕ → ℤ) : Submodule (𝓞 E) (Sp E N) :=
  (stdAt E N P).comap
    ((LinearMap.pi fun l : Fin N => ((q : E) ^ e l.1)⁻¹ • (LinearMap.proj l : Sp E N →ₗ[E] E)).restrictScalars (𝓞 E))

def scE (n : ℕ) (ex : ℕ → ℕ) (l : ℕ) : ℤ := if l < n then 0 else (ex (l - n) : ℤ)

def lamY (n c : ℕ) (ex : ℕ → ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) (scE n ex)

section AtQ

variable (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

def parL (kj n c : ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) fun l => if kj ≤ l ∧ l < n then 1 else 0

def JQ (kj n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  stabL E (n + c) (stdAt E (n + c) P) ⊓ stabL E (n + c) (parL P q kj n c)

variable {P}

end AtQ

end LocE

section Target

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def Bdd (P : HeightOneSpectrum (𝓞 E)) (N c j : ℕ) (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Prop :=
  ∀ x ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0, h⁻¹ x ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ∧
    (((Ideal.absNorm P.asIdeal : ℕ) : E) ^ j) • h x ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0

def NF (P : HeightOneSpectrum (𝓞 E)) (N c j : ℕ) (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Prop :=
  ∃ (n : ℕ → ℤ) (z : Sp E N), (∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0) ∧ z ∈ stdAt E N P ∧
    ∀ v : Sp E (N + c), h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔
      (∀ l : Fin N, IntAt P (v (Fin.castAdd _ l) - Loc.atN v N * z l)) ∧
        ∀ i : Fin c, IntAt P ((((Ideal.absNorm P.asIdeal : ℕ) : E) ^ n i.1)⁻¹ * v (Fin.natAdd _ i))

end Target

def TwNormLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (N c kj j : ℕ),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ h : Sp E (N + c) ≃ₗ[E] Sp E (N + c), Bdd P N c j h →
      ∃ r ∈ Loc.R1 E N c, ∃ κ ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
        Bdd P N c j (r * h * κ) ∧ NF P N c j (r * h * κ) ∧
          Loc.prX (Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) (r * h * κ)) ≤ GLint E N P

end PI.TwNormLat
end
end
