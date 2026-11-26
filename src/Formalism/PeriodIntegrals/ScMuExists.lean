module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.FormalDegreeBessel.StatementIO
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.PeriodIntegrals.GTDefs

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.ScMuExists
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct ENNReal
open Matrix

namespace PI.ScMuExists

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

end Real

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

variable {r : ℕ}

def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

abbrev muInf : Measure I.Ginf := Measure.pi fun v => Formalism.REAL.muG (I.ε v)

def IsHaarOnSet (S : Set I.Ginf) (μ : Measure I.Ginf) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ

def IsQuotMeasS (μS ν : Measure I.Ginf) : Prop :=
  ∀ f : I.Ginf → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂(muInf I) = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν

def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}

end Inst

def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) →
    Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0 →
    ∃ muN muH nuQ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) muN ∧
      IsHaarOnSet I (Hset I (Set.range e ∪ Set.range f ∪ {z})) muH ∧
      IsQuotMeasS I ((muN.prod muH).map (fun p => p.1 * p.2)) nuQ

end PI.ScMuExists
end
end

section -- merged from Formalism.PeriodIntegrals.ScRefExists
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open Matrix

namespace PI.ScRefExists

section Fin

variable (I : Formalism.MainNotions.S.AutInst)

abbrev VA : Type := Fin I.n → I.E ⊗[I.F] Af I.F

def incl (x : Fin I.n → I.E) : VA I := fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)

def hA (x y : VA I) : I.E ⊗[I.F] Af I.F :=
  Formalism.UG.hform (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) x y

abbrev sigA : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

def mL (m : ℕ) : Submodule (IntAf I.F I.E) (VA I) :=
  Submodule.span (IntAf I.F I.E) {y | ∃ x ∈ I.Lf, y = (m : I.E ⊗[I.F] Af I.F) • x}

def InMod (m : ℕ) (S : Set (VA I)) (x : VA I) : Prop :=
  x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I m

def ZMod' (m : ℕ) (c : I.E ⊗[I.F] Af I.F) : Prop :=
  ∃ t ∈ IntAf I.F I.E, c = (m : I.E ⊗[I.F] Af I.F) * t

def InAt (g m : ℕ) (x : VA I) : Prop :=
  ∃ c : ℕ, Nat.Coprime c g ∧ (c : I.E ⊗[I.F] Af I.F) • x ∈ mL I m

end Fin

structure RefData (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) where
  e0 : Fin r → VA I
  f0 : Fin r → VA I
  z0 : VA I
  bw : Fin k → VA I
  bwd : Fin k → VA I
  ew : I.E ⊗[I.F] Af I.F
  vectorsInLattice : (∀ a, e0 a ∈ I.Lf ∧ f0 a ∈ I.Lf) ∧ z0 ∈ I.Lf ∧ ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf
  basisApprox : ∀ a, InAt I g g (e0 a - incl I (e a)) ∧ InAt I g g (f0 a - incl I (f a))
  gramIntegral : ∀ a b, ZMod' I g (hA I (e0 a) (e0 b)) ∧ ZMod' I g (hA I (f0 a) (f0 b)) ∧
    ZMod' I g (hA I (e0 a) (f0 b) - if a = b then 1 else 0)
  formsAtZero : ZMod' I g (hA I z0 z0 + 1) ∧
    ∀ a, ZMod' I g (hA I (e0 a) z0) ∧ ZMod' I g (hA I (f0 a) z0)
  weightVectorsIntegral : ∀ i, ZMod' I g (hA I z0 (bw i)) ∧ ZMod' I g (hA I z0 (bwd i)) ∧
    ∀ a, ZMod' I g (hA I (e0 a) (bw i)) ∧ ZMod' I g (hA I (f0 a) (bw i)) ∧
      ZMod' I g (hA I (e0 a) (bwd i)) ∧ ZMod' I g (hA I (f0 a) (bwd i))
  ew_idem : ew * ew = ew
  ew_orth : ew * sigA I ew = 0
  ew_int : ew ∈ IntAf I.F I.E
  ew_full : ∀ y ∈ I.Lf, (1 - ew - sigA I ew) • y ∈ mL I g
  bw_w : ∀ i, bw i = ew • bw i
  bwd_w : ∀ i, bwd i = sigA I ew • bwd i
  bw_dual : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)
  latticeSpan : ∀ y ∈ I.Lf,
    InMod I g (Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd) y

def Target : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E), 1 ≤ g →
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) →
    I.n = 2 * r + k + 1 →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) →
    (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) →
    Nonempty (RefData I g r k e f)

end PI.ScRefExists
end
end

section -- merged from Formalism.PeriodIntegrals.AdelClassFin
noncomputable section

namespace PI.AdelClassFin

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

def GFf (I : Formalism.MainNotions.S.AutInst) : Set I.Gf :=
  {x | ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
    I.fmat x = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))}

def AdelClassFin : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (U : Subgroup I.Gf), IsOpen (U : Set I.Gf) →
    ∃ S : Finset I.Gf, ∀ x : I.Gf, ∃ γ ∈ GFf I, ∃ s ∈ S, ∃ u ∈ U, x = γ * s * u

end PI.AdelClassFin
end
end

section -- merged from Formalism.PeriodIntegrals.CapelliEig
open MeasureTheory Matrix

noncomputable section

namespace PI.CapelliEig

open PI.UpqRep

def capC {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : ℂ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V :=
  Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk k r) (Y + ((2 * r + k : ℕ) : ℂ) / 2) F

def IsKFinCoefH {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (P : H →L[ℂ] Wp) (Q : Wq →L[ℂ] H), (∀ w, IsKFinHpk (k := k) (r := r) σ (Q w)) ∧
    (∀ x, IsKFinHpk (k := k) (r := r) σ (ContinuousLinearMap.adjoint P x)) ∧ ∀ g, f g = P.comp ((σ g).comp Q)

def IsKFinCoefT {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ a ∈ UH (Hpk k r), ∃ b ∈ UH (Hpk k r), IsKFinCoefH σ (fun g => f (a * g * b))

def CapEig : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Hs →L[ℂ] Hs))
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq],
    IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp), IsKFinCoefT σ f →
    ∀ Y : ℂ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      capC (k := k) (r := r) Y f g = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • f g

end PI.CapelliEig

end
end

section -- merged from Formalism.PeriodIntegrals.ScPiExists
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct ENNReal
open Matrix

namespace PI.ScPiExists

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

end Real

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

variable {r : ℕ}

def Sinf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InS (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}

def matW {k : ℕ} (wf : Fin k → Fin I.n → ℂ) (v : InfinitePlace I.F) (s : I.Ginf) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun a b => hJ (I.ε v) (wf a) (uMat (s v) *ᵥ wf b)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def IsRepS (S N : Set I.Ginf) (rho : I.Ginf → (V →L[ℂ] V)) : Prop :=
  rho 1 = 1 ∧ (∀ s ∈ S, ∀ t ∈ S, rho (s * t) = rho s * rho t) ∧
    (∀ s ∈ S, ∀ x y : V, ⟪rho s x, rho s y⟫_ℂ = ⟪x, y⟫_ℂ) ∧ (∀ s ∈ N, rho s = 1) ∧
    ∀ x : V, ContinuousOn (fun s => rho s x) S

end Inst

structure PiData (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (lam : InfinitePlace I.F → Fin k → ℝ) where
  Vpi : Type
  [vN : NormedAddCommGroup Vpi]
  [vI : InnerProductSpace ℂ Vpi]
  [vF : FiniteDimensional ℂ Vpi]
  piU : I.Ginf → (Vpi →L[ℂ] Vpi)
  piU_rep : IsRepS I (Sinf I e z) (Ninf I e z) piU
  Vloc : InfinitePlace I.F → Type
  [lN : ∀ v, NormedAddCommGroup (Vloc v)]
  [lI : ∀ v, InnerProductSpace ℂ (Vloc v)]
  [lF : ∀ v, FiniteDimensional ℂ (Vloc v)]
  piLoc : ∀ v, Matrix (Fin k) (Fin k) ℂ → (Vloc v →L[ℂ] Vloc v)
  piLoc_type : ∀ v, PI.UpqRep.IsHCTypeU k (lam v) (piLoc v)
  wfr : InfinitePlace I.F → Fin k → Fin I.n → ℂ
  wfr_on : ∀ v a b, hJ (I.ε v) (wfr v a) (wfr v b) = if a = b then 1 else 0
  wfr_perp : ∀ v a, (∀ c, hJ (I.ε v) (rv I v (e c)) (wfr v a) = 0 ∧
      hJ (I.ε v) (rv I v (f c)) (wfr v a) = 0) ∧
    hJ (I.ε v) (rv I v z) (wfr v a) = 0
  tensU : (∀ v, Vloc v) → Vpi
  tensU_inner : ∀ x y, ⟪tensU x, tensU y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ
  tensU_span : Submodule.span ℂ (Set.range tensU) = ⊤
  tensU_equiv : ∀ s ∈ Hset I (Set.range e ∪ Set.range f ∪ {z}), ∀ x,
    piU s (tensU x) = tensU (fun v => piLoc v (matW I (wfr v) v s) (x v))

attribute [instance] PiData.vN PiData.vI PiData.vF PiData.lN PiData.lI PiData.lF

def WeylHyp : Prop :=
  ∀ (k : ℕ) (u : Fin k → ℝ), PI.UpqRep.IsHCParam u →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsHCTypeU k u π

def IsFrame (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Prop :=
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0)

def Frame : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    I.n = 2 * r + k + 1 → IsFrame I e f z →
    (∃ t : ℕ, 0 < t ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E)) →
    (∀ v (i : Fin I.n), I.ε v i = if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)) →
    ∀ v, ∃ w : Fin k → Fin I.n → ℂ, (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0

def Build : Prop :=
  WeylHyp →
  ∀ (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (lam : InfinitePlace I.F → Fin k → ℝ),
    I.n = 2 * r + k + 1 → IsFrame I e f z → Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0 →
    (∀ v, PI.UpqRep.IsHCParam (lam v)) →
    (∀ v, ∃ w : Fin k → Fin I.n → ℂ, (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0) →
    Nonempty (PiData I k e f z lam)

end PI.ScPiExists
end
end

section -- merged from Formalism.PeriodIntegrals.GTLower
noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def GTLower : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Interlace h lam sg → Branch h lam sg

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.ScPsiExists
noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScPsiExists

def psiEinf (I : Formalism.MainNotions.S.AutInst) (x : I.E) : ℂ :=
  ∏ v, Complex.exp (2 * Real.pi * Complex.I * (I.φ v x + star (I.φ v x)))

def Target : Prop :=
  ∀ I : Formalism.MainNotions.S.AutInst, ∃ psiEf : I.E ⊗[I.F] Af I.F → ℂ,
    (∀ x y, psiEf (x + y) = psiEf x * psiEf y) ∧
    (∀ x ∈ IntAf I.F I.E, psiEf x = 1) ∧
    ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Af I.F) x) * psiEinf I x = 1

end PI.ScPsiExists
end
end

section -- merged from Formalism.PeriodIntegrals.NMeasInv
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct ENNReal
open Matrix

namespace PI.NMeasInv

section Real

variable {n r : ℕ}

def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)

def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})

def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r

def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r

end Real

section Inst

variable (I : Formalism.MainNotions.S.AutInst)

def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)

variable {r : ℕ}

def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}

def IsHaarOnSet (S : Set I.Ginf) (μ : Measure I.Ginf) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ Sᶜ = 0 ∧ ∀ s ∈ S, μ.map (fun x => s * x) = μ

def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}

def FrameRel (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Prop :=
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) ∧
  Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0

end Inst

def FinCpt : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      ∀ K : Set I.Ginf, IsCompact K → μ K < ⊤

def RightInv : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      ∀ n ∈ Ninf I e z, μ.map (fun x => x * n) = μ

def InvInv : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      μ.map (fun x => x⁻¹) = μ

def ConjInv : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∀ μ : Measure I.Ginf, IsHaarOnSet I (Ninf I e z) μ →
      ∀ h ∈ Hset I (Set.range e ∪ Set.range f ∪ {z}), μ.map (fun x => h * x * h⁻¹) = μ

def Target : Prop := FinCpt ∧ RightInv ∧ InvInv ∧ ConjInv

end PI.NMeasInv
end
end
