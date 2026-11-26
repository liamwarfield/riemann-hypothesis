module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

section OnePlace

variable {P Q R S : ℕ}

def IsLift (x t : ℚ) (M : GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V) : Prop :=
  Function.Surjective pr ∧ (∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f) ∧
    ∀ Y f, M.act Y (pr f) = pr (fockAct2 P Q R S Y f) + ((t : ℂ) * Y.trace) • pr f

def lam (P Q R S : ℕ) (κ : ℤ) : Ix R S → ℚ
  | .inl i => if (i : ℕ) < P then (κ : ℚ) / 2 - cPair R S + cPair P Q else cPair P Q
  | .inr j => if (j : ℕ) < Q then (κ : ℚ) / 2 + cPair R S - cPair P Q else -cPair P Q

def casK (μ : Ix R S → ℚ) : ℚ :=
  ∑ a, μ a ^ 2 + (∑ i : Fin R, μ (.inl i) * ((R : ℚ) - 1 - 2 * (i : ℕ))) + ∑ j : Fin S, μ (.inr j) * ((S : ℚ) - 1 - 2 * (j : ℕ))

def GenBy (M : GKMod R S) (Λ : Ix R S → ℚ) : Prop := ∃ v, IsHW M.act Λ v ∧ genSub M.act {v} = ⊤

def ScalarEnd (M : GKMod R S) : Prop :=
  ∀ T : M.V →ₗ[ℂ] M.V, (∀ Z, T ∘ₗ M.act Z = M.act Z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id

def heisOp (c : Matrix (Ix P Q) (Ix R S) ℂ) : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • ∑ l : Ln P Q R S,
    (c l.1 l.2 • raiB l - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star (c l.1 l.2)) • lowB l)

def IsFrame {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (A : Matrix α (Ix P Q) ℂ) : Prop :=
  Aᵀ * M * A.map star = Jm P Q ∧ ∃ A' : Matrix (Ix P Q) α ℂ, A * A' = 1

end OnePlace

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

def atPl (w : ι) (L : Module.End ℂ (V w)) : Module.End ℂ (⨂[ℂ] i, V i) :=
  PiTensorProduct.map (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L)

def sumPl (L : ∀ w, Module.End ℂ (V w)) : Module.End ℂ (⨂[ℂ] i, V i) := ∑ w, atPl w (L w)

end Tensor

def LocFin {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) : Prop :=
  ∀ v, ∃ N : Submodule ℂ V, FiniteDimensional ℂ N ∧ v ∈ N ∧ ∀ y ∈ N, L y ∈ N

def IsExp {V : Type} [AddCommGroup V] [Module ℂ V] (L U : Module.End ℂ V) : Prop :=
  ∀ (v : V) (l : V →ₗ[ℂ] ℂ), HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) (l (U v))

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}


variable (F) in
abbrev Tens (P Q R S : ℕ) : Type := ⨂[ℂ] _ : InfinitePlace F, Formalism.BasicNotions.TH.Pol P Q R S

def SD (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f f₁ : SInf F κ) : Prop :=
  ∀ g ∈ SB (κ → Af F), ∀ l ∈ (adeleClass F).adm κ, HasDerivAt (fun t => l (T t (pureA F f g))) (l (pureA F f₁ g)) 0

def SA (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f f₁ : SInf F κ) : Prop :=
  ∀ g ∈ SB (κ → Af F), T (pureA F f g) = pureA F f₁ g

def Framed (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ) : Prop :=
  a * b = Complex.I ∧ (∀ w, IsFrame (a • JA.map (piInf (τ w))) (A w)) ∧ ∀ w, IsFrame (b • JB.map (piInf (τ w))) (C w)

def IsFockMap (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) : Prop :=
  Function.Injective Φ ∧ ∀ u : Matrix α β (AE F E), At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      ∀ T, SD (fun t => d.rho ψ (realAd F t • u)) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))


variable (σ) in
def RLines (J : Matrix β β (AE F E)) : Set (Multiplicative ℝ →* UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) J) :=
  {γ | Continuous γ ∧ ∀ t, At (evI F) (((γ t).1 : Matrix β β (AE F E)) - 1)}

def IsGen (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (γ : Multiplicative ℝ →* UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) J) (Y : InfinitePlace F → Mat R S) : Prop :=
  ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w =
    C w * NormedSpace.exp (t • Y w)

def ActsBy (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} {r s : ℕ}
    (C : InfinitePlace F → Matrix β (Ix r s) ℂ) (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) J →* Module.End ℂ ((κ → AF F) → ℂ))
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (act : Mat r s →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (c : InfinitePlace F → ℂ) : Prop :=
  ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGen τ C γ Y → ∀ T, SD (fun t => om (γ (Multiplicative.ofAdd t))) (Φ T)
    (Φ (sumPl (fun w => act (Y w) + (c w * (Y w).trace) • 1) T))

end Adelic

def ActsLaws : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (f f₁ f₂ : SInf F κ),
    (∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, (∀ t, T t 0 = 0) → SD T f f₁ → ActsD (evI F) T f f₁) ∧
    (∀ T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, T 0 = 0 → SA T f f₁ → Acts (evI F) T f f₁) ∧
    (∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, ActsD (evI F) T f f₁ → ActsD (evI F) T f f₂ → f₁ = f₂) ∧
    (∀ T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, Acts (evI F) T f f₁ → Acts (evI F) T f f₂ → f₁ = f₂) ∧
    ∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, SD T f f₁ → SD T f f₂ → f₁ = f₂

def DerEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    ∃ D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ), ∀ u, At (evI F) u → ∀ f,
      SD (fun t => d.rho ψ (realAd F t • u)) f (D u f) ∧ ∀ x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x

def FockEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → Framed τ JA JB a b A C →
    ∃ Φ, IsFockMap ψ τ d A C Φ

def VacLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1)

def GenEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ γ ∈ RLines (σ := σ) J, ∃ Y, (∀ w, Y w ∈ upq R S) ∧ IsGen τ C γ Y

def LineEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : InfinitePlace F → Mat R S, (∀ w, Y w ∈ upq R S) → ∃ γ ∈ RLines (σ := σ) J, IsGen τ C γ Y

def LieScalar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) om →
    ∃ c, ActsBy τ C om Φ (fockAct2 P Q R S) c

def LieSecond : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) JA JB d χ om → HasExp τ χ m →
    ActsBy τ C om Φ (fockAct2 P Q R S) fun w => (m w : ℂ) / 2

def LieFirst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JB JA) κ) (a b : ℂ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)) (χ : Chr F E)
    (m : InfinitePlace F → ℤ), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) JB JA d' χ om → HasExp τ χ m →
    ActsBy τ A om Φ (fockAct1 P Q R S) fun w => (m w : ℂ) / 2

def KLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (θ : InfinitePlace F → Matrix β β ℂ), IsCMExt F E σ →
    (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) → (∀ w, θ w * C w = C w * Jm R S) → ∀ k : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) J,
    At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) → (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) →
    ∃ γ ∈ RLines (σ := σ) J, ∃ Y, IsGen τ C γ Y ∧ (∀ w, IsKC (Y w)) ∧ γ (Multiplicative.ofAdd 1) = k

def FrameEx : Prop :=
  ∀ (n r s : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), HasSig M r s → IsCartan M θ →
    ∃ A : Matrix (Fin n) (Ix r s) ℂ, IsFrame M A ∧ θ * A = A * Jm r s

def PolRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d P Q R S : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    Framed τ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Jm P Q) →
    (∀ w, W.θ w * C w = C w * Jm R S) → IsFockMap ψ τ M.co A C Φ → LinearMap.range Φ = M.Pol ψ τ

def Parity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ w, Even (B.mα w - B.mβ w)

end GlobalTheory.RealLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.SchwartzBox

theorem norm_le_max_comp {V : Type} [NormedAddCommGroup V] {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ ⊕ κ' → V) :
    ‖x‖ ≤ max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun j => ?_
  cases j with
  | inl i => exact le_max_of_le_left (norm_le_pi_norm (x ∘ Sum.inl) i)
  | inr i => exact le_max_of_le_right (norm_le_pi_norm (x ∘ Sum.inr) i)

def restr (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ → ι) :
    (ι → V) →L[ℝ] (κ → V) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => V) (e i)

theorem restr_apply (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) (x : ι → V) : restr V e x = x ∘ e := rfl

theorem norm_restr_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : κ → ι) : ‖restr V e‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => norm_le_pi_norm x (e i)

theorem norm_iteratedFDeriv_restr_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type} [Fintype ι]
    [Fintype κ] (e : κ → ι) (f : SchwartzMap (κ → V) ℂ) (i : ℕ) (x : ι → V) :
    ‖iteratedFDeriv ℝ i (fun y => f (y ∘ e)) x‖ ≤ ‖iteratedFDeriv ℝ i f (x ∘ e)‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (restr V e) (f.smooth ⊤) x (i := i) (by exact_mod_cast le_top)
  have h' : (fun y => f (y ∘ e)) = (f ∘ restr V e) := rfl
  rw [h', h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ i f (restr V e x)‖ * ∏ _j : Fin i, ‖restr V e‖
      ≤ ‖iteratedFDeriv ℝ i f (restr V e x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_restr_le V e
    _ = _ := mul_one _

theorem exists_schwartz_box {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (f₁ : SchwartzMap (κ → V) ℂ) (f₂ : SchwartzMap (κ' → V) ℂ) :
    ∃ f : SchwartzMap (κ ⊕ κ' → V) ℂ, ∀ x, f x = f₁ (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr) := by
  have hs₁ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl)) :=
    (f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff
  have hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₂ (y ∘ Sum.inr)) :=
    (f₂.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff
  refine ⟨⟨fun x => f₁ (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr), hs₁.mul hs₂, fun k n => ?_⟩, fun _ => rfl⟩
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℝ k i f₁ * SchwartzMap.seminorm ℝ 0 (n - i) f₂ +
      SchwartzMap.seminorm ℝ 0 i f₁ * SchwartzMap.seminorm ℝ k (n - i) f₂), fun x => ?_⟩
  have hx : ‖x‖ ^ k ≤ ‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k := by
    have h0 : ‖x‖ ^ k ≤ (max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_max_comp x) k
    refine h0.trans ?_
    have p1 := pow_nonneg (norm_nonneg (x ∘ Sum.inl)) k
    have p2 := pow_nonneg (norm_nonneg (x ∘ Sum.inr)) k
    rcases le_total ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hL := norm_iteratedFDeriv_mul_le hs₁ hs₂ x (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖
      ≤ (‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ := by
        refine mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact norm_iteratedFDeriv_restr_le Sum.inl f₁ i x
        · exact norm_iteratedFDeriv_restr_le Sum.inr f₂ (n - i) x
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ((‖x ∘ Sum.inl‖ ^ k * ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖) *
              ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ +
           ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ *
              (‖x ∘ Sum.inr‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact SchwartzMap.le_seminorm ℝ k i f₁ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₂ _ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₁ _ _
        · exact SchwartzMap.le_seminorm ℝ k (n - i) f₂ _

theorem sb_box {X : Type} [TopologicalSpace X] {κ κ' : Type} {g₁ : (κ → X) → ℂ} {g₂ : (κ' → X) → ℂ}
    (hg₁ : g₁ ∈ SB (κ → X)) (hg₂ : g₂ ∈ SB (κ' → X)) :
    (fun z : κ ⊕ κ' → X => g₁ (z ∘ Sum.inl) * g₂ (z ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → X) := by
  obtain ⟨hl₁, hc₁⟩ := hg₁
  obtain ⟨hl₂, hc₂⟩ := hg₂
  let e : (κ ⊕ κ' → X) ≃ₜ (κ → X) × (κ' → X) := Homeomorph.sumArrowHomeomorphProdArrow
  have he : ∀ z, e z = (z ∘ Sum.inl, z ∘ Sum.inr) := fun _ => rfl
  refine ⟨?_, ?_⟩
  · have c₁ : Continuous fun z : κ ⊕ κ' → X => z ∘ Sum.inl := continuous_pi fun i => continuous_apply _
    have c₂ : Continuous fun z : κ ⊕ κ' → X => z ∘ Sum.inr := continuous_pi fun i => continuous_apply _
    exact (hl₁.comp_continuous c₁).mul (hl₂.comp_continuous c₂)
  · refine HasCompactSupport.intro' (K := e ⁻¹' (tsupport g₁ ×ˢ tsupport g₂))
      (e.isCompact_preimage.2 (hc₁.prod hc₂))
      (((isClosed_tsupport _).prod (isClosed_tsupport _)).preimage e.continuous) fun z hz => ?_
    rw [Set.mem_preimage, he, Set.mem_prod, not_and_or] at hz
    rcases hz with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]

theorem boxFun_zero_left {R κ κ' : Type} (φ : (κ' → R) → ℂ) : boxFun (0 : (κ → R) → ℂ) φ = 0 := by
  funext x; simp [boxFun]

theorem boxFun_add_left {R κ κ' : Type} (a b : (κ → R) → ℂ) (φ : (κ' → R) → ℂ) :
    boxFun (a + b) φ = boxFun a φ + boxFun b φ := by
  funext x; simp [boxFun, add_mul]

theorem boxFun_smul_left {R κ κ' : Type} (c : ℂ) (a : (κ → R) → ℂ) (φ : (κ' → R) → ℂ) :
    boxFun (c • a) φ = c • boxFun a φ := by
  funext x; simp [boxFun, mul_assoc]

theorem boxFun_zero_right {R κ κ' : Type} (φ : (κ → R) → ℂ) : boxFun φ (0 : (κ' → R) → ℂ) = 0 := by
  funext x; simp [boxFun]

theorem boxFun_add_right {R κ κ' : Type} (φ : (κ → R) → ℂ) (a b : (κ' → R) → ℂ) :
    boxFun φ (a + b) = boxFun φ a + boxFun φ b := by
  funext x; simp [boxFun, mul_add]

theorem boxFun_smul_right {R κ κ' : Type} (c : ℂ) (φ : (κ → R) → ℂ) (a : (κ' → R) → ℂ) :
    boxFun φ (c • a) = c • boxFun φ a := by
  funext x; simp [boxFun]; ring


open scoped Classical in
theorem boxFun_mem_schA (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'] :
    ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
  intro φ₁ h₁ φ₂ h₂
  have gen : ∀ Φ₁ ∈ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      ∀ Φ₂ ∈ {Φ | ∃ (f : SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      boxFun Φ₁ Φ₂ ∈ schA F (κ ⊕ κ') := by
    rintro _ ⟨f₁, g₁, hg₁, rfl⟩ _ ⟨f₂, g₂, hg₂, rfl⟩
    obtain ⟨f, hf⟩ := exists_schwartz_box f₁ f₂
    refine Submodule.subset_span ⟨f, fun z => g₁ (z ∘ Sum.inl) * g₂ (z ∘ Sum.inr), sb_box hg₁ hg₂, ?_⟩
    funext x
    simp only [boxFun, pureA, hf]
    simp only [Function.comp_def]
    ring
  have gen₂ : ∀ Φ₁ ∈ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
        (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g},
      boxFun Φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
    intro Φ₁ hΦ₁
    induction h₂ using Submodule.span_induction with
    | mem x hx => exact gen Φ₁ hΦ₁ x hx
    | zero => rw [boxFun_zero_right]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [boxFun_add_right]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [boxFun_smul_right]; exact Submodule.smul_mem _ c hx
  induction h₁ using Submodule.span_induction with
  | mem x hx => exact gen₂ x hx
  | zero => rw [boxFun_zero_left]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [boxFun_add_left]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [boxFun_smul_left]; exact Submodule.smul_mem _ c hx

end GlobalTheory.SchwartzBox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
  first | exact @GlobalTheory.SchwartzBox.boxFun_mem_schA | exact GlobalTheory.SchwartzBox.boxFun_mem_schA | (intros; apply GlobalTheory.SchwartzBox.boxFun_mem_schA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SchANonzero

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

def intPts (F : Type) [Field F] [NumberField F] (κ : Type) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  Set.pi Set.univ fun _ => {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem isOpen_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsOpen (intPts F κ) :=
  isOpen_set_pi Set.finite_univ fun _ _ =>
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)

theorem isCompact_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsCompact (intPts F κ) :=
  isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral F

theorem isClosed_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsClosed (intPts F κ) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  exact (isCompact_intPts F κ).isClosed

theorem indicator_intPts_mem_SB (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (intPts F κ).indicator (1 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_intPts F κ) (isClosed_intPts F κ)
    fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ intPts F κ
  · exact ⟨intPts F κ, isOpen_intPts F κ, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨(intPts F κ)ᶜ, (isClosed_intPts F κ).isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem exists_mem_schA_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ φ ∈ schA F κ, φ 0 ≠ 0 := by
  intro F _ _ κ _
  classical
  obtain ⟨f, hf⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  refine ⟨pureA F f ((intPts F κ).indicator 1), Submodule.subset_span ⟨f, _, indicator_intPts_mem_SB F κ, rfl⟩, ?_⟩
  have h0 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ intPts F κ := fun i _ v => by
    show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem (v.adicCompletionIntegers F)
  simp only [pureA]
  rw [Set.indicator_of_mem h0]
  have hz : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  rw [hz, hf]
  simp

end GlobalTheory.SchANonzero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ φ ∈ schA F κ, φ 0 ≠ 0 := by
  first | exact @GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | exact GlobalTheory.SchANonzero.exists_mem_schA_ne_zero | (intros; apply GlobalTheory.SchANonzero.exists_mem_schA_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AwayOrb

variable {p : ℕ} [Fact p.Prime]

def compL (G : HTGroup p) (w : AwayP p) : G.GAf →* UPts G.star (w.1.adicCompletion ℚ) :=
  ubcMap (AfP.eval w)

def coordL (G : HTGroup p) (w : AwayP p) (a : w.1.adicCompletion ℚ ⊗[ℚ] G.C) :
    Fin (Module.finrank ℚ G.C) → w.1.adicCompletion ℚ :=
  (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) (Module.finBasis ℚ G.C)).repr a

def intPts (G : HTGroup p) (w : AwayP p) : Set (UPts G.star (w.1.adicCompletion ℚ)) :=
  {h | (∀ i, coordL G w (((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 :
          (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) i ∈
        w.1.adicCompletionIntegers ℚ) ∧
      (∀ i, coordL G w ((((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1)⁻¹ :
          (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) i ∈
        w.1.adicCompletionIntegers ℚ) ∧
      (((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2 : (w.1.adicCompletion ℚ)ˣ) :
        w.1.adicCompletion ℚ) ∈ w.1.adicCompletionIntegers ℚ ∧
      ((((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2)⁻¹ : (w.1.adicCompletion ℚ)ˣ) :
        w.1.adicCompletion ℚ) ∈ w.1.adicCompletionIntegers ℚ}

end GlobalTheory.AwayOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct ContDiff

namespace GlobalTheory.HolRead

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SmoothReal (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

def IsUnitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (y : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def unitLie {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) : Set (Frame X.Ψ r) :=
  {Z | ∀ τ : X.Ψ, (mat Z τ)ᴴ * (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) +
    (diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) * mat Z τ = 0}

def expFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) : Frame Ψ r :=
  fun τ => (NormedSpace.exp (mat Z τ) : Matrix (Fin r) (Fin r) ℂ)


open Classical in
def unitFr {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (τ : Ψ) (c d : Fin r) : Frame Ψ r :=
  fun τ' a b => if τ' = τ ∧ a = c ∧ b = d then 1 else 0

def KillPair {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : Prop :=
  (ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a) ∨ (ε a ≠ ε b ∧ b < a)

def wtCol {R : Ranks} (h : HCParam R) (p q c : ℕ) : ℤ :=
  ⌊if c < q then Formalism.L2.NTheta.lamAt h (p + c) - (p : ℚ) / 2 - ((q : ℚ) - 1) / 2 + (c : ℚ)
    else Formalism.L2.NTheta.lamAt h (c - q) + (q : ℚ) / 2 - ((p : ℚ) - 1) / 2 + ((c - q : ℕ) : ℚ)⌋

end GlobalTheory.HolRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField

namespace GlobalTheory.WeilSchrodinger

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def sesq {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) :
    (Fin k → D.host.E) →ₗ⋆[D.host.E] (Fin k → D.host.E) →ₗ[D.host.E] D.host.E :=
  Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) G

def hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm) (nd : (sesq D G).Nondegenerate)
    (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D where
  V := Fin k → D.host.E
  hT := sesq D G
  herm := herm
  nondeg := nd
  rank := k
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := sg
  L0 := L
  standardTuple_isLattice := hL
  baseLattice_isUnimodular := hU

variable {D}

theorem gram_hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm)
    (nd : (sesq D G).Nondegenerate) (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) :
    (hspOf D G herm nd L hL hU sg).gram = G := by
  funext i j
  have e : ∀ m : Fin k, Pi.basisFun D.host.E (Fin k) m = Pi.single m 1 := fun m => Pi.basisFun_apply _ _ m
  simp only [HSpace.gram, hspOf, sesq]
  erw [e i, e j]
  exact Matrix.toLinearMapₛₗ₂'_single (R := D.host.E) (starRingEnd D.host.E) (RingHom.id D.host.E) G i j

end GlobalTheory.WeilSchrodinger

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VStdOfOrthonormalSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdFrame

theorem vStd_of_orthonormal_span : ∀ (D : D7) (i : Fin D.R.m), ((∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧ (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)) → VStd D i := by
  intro D i h
  refine vStd_of_frameChoice D i ⟨h.1, fun a => ?_⟩
  show (Vc D i).frame a ∈ (Vc D i).L0
  rw [h.2]
  exact Submodule.subset_span ⟨a, rfl⟩

end GlobalTheory.StdFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F]

def act {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (g.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_one {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ] [DecidableEq κ]
    (w : (κ → R) × (κ → R)) : act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [act, h, Matrix.one_mulVec]
  rfl

theorem act_mul {R : Type} [CommRing R] [Algebra F R] {κ : Type} [Fintype κ]
    (g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) : act (g * h) w = act g (act h w) := by
  have e : (g * h).map (algebraMap F R) = g.map (algebraMap F R) * h.map (algebraMap F R) :=
    Matrix.map_mul (f := algebraMap F R)
  simp only [act, e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]


variable (F) in
def gens (κ : Type) [Fintype κ] [DecidableEq κ] : Set (Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  {g | ∃ A : Matrix κ κ F, IsUnit A.det ∧ g = Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ} ∪
    {g | ∃ C : Matrix κ κ F, Cᵀ = C ∧ g = Matrix.fromBlocks 1 0 (-C) 1} ∪ {Matrix.fromBlocks 0 1 (-1) 0}

variable [NumberField F]

def Realised (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ,
    (∀ φ ∈ schA F κ, S φ ∈ schA F κ) ∧ (∀ φ ∈ schA F κ, ∃ φ' ∈ schA F κ, S φ' = φ) ∧
    (∀ l ∈ (adeleClass F).adm κ, ∃ l' ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ, l' φ = l (S φ)) ∧
    ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (act g w) (S φ)

theorem realised_one (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    Realised ψ (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :=
  ⟨id, fun φ h => h, fun φ h => ⟨φ, h, rfl⟩, fun l hl => ⟨l, hl, fun _ _ => rfl⟩,
    fun w φ _ => by rw [act_one]; rfl⟩

theorem Realised.mul {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {g h : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (hg : Realised ψ g) (hh : Realised ψ h) : Realised ψ (g * h) := by
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := hg
  obtain ⟨T, hT, hTs, hTa, hTi⟩ := hh
  refine ⟨S ∘ T, fun φ hφ => hS _ (hT φ hφ), fun φ hφ => ?_, fun l hl => ?_, fun w φ hφ => ?_⟩
  · obtain ⟨φ₁, h₁, rfl⟩ := hSs φ hφ
    obtain ⟨φ₂, h₂, rfl⟩ := hTs φ₁ h₁
    exact ⟨φ₂, h₂, rfl⟩
  · obtain ⟨l₁, hl₁, e₁⟩ := hSa l hl
    obtain ⟨l₂, hl₂, e₂⟩ := hTa l₁ hl₁
    exact ⟨l₂, hl₂, fun φ hφ => (e₂ φ hφ).trans (e₁ _ (hT φ hφ))⟩
  · simp only [Function.comp_apply]
    rw [hTi w φ hφ, hSi _ _ (hT φ hφ), act_mul]

end GlobalTheory.AdelicSvN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeAdjoint

theorem unramified_host (D : D7) : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  exact Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv
        (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext ht.symm
    rwa [this]

theorem realUnif (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.SphericalOps.RealUnif P := by
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 (unramified_host D) ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  rw [Ideal.map_le_iff_le_comap, SetLike.not_le_iff_exists] at h2
  obtain ⟨x, hx, hx2⟩ := h2
  exact ⟨x, algebraMap _ _ x, rfl, hx, hx2⟩


open GlobalTheory.SphericalOps in
theorem ipM_heckeOn_dualLab : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M (J : Set (GA D V)) χ μ 𝓕 → ∀ P d R R', Hecke₂ V (J : Set (GA D V)) χ Sb P d R → Hecke₂ V (J : Set (GA D V)) χ Sb P (dualLab d) R' → ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, ∀ T' ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ → heckeOn M R' T' ∈ Mult θ M (J : Set (GA D V)) χ → ipM M μ 𝓕 (heckeOn M R T) T' = ipM M μ 𝓕 T (heckeOn M R' T') := by
  intro D V S θ M J χ Sb μ 𝓕 hθ hμ h𝓕 hS P d R R' h h' T hT T' hT' hRT hRT'
  obtain ⟨R₁, h₁', hcard, K, x, hK, hR, hR₁⟩ := exists_dual (realUnif D P) h
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D V μ hμ
  have hS' := hS hθ hμ h𝓕
  have h₁ := ipM_spec M μ 𝓕 _ _ (hS' _ hRT _ hT')
  have h₂ := ipM_spec M μ 𝓕 _ _ (hS' _ hT _ hRT')
  obtain ⟨c₃, h₃⟩ := hS' _ hT _ hT
  obtain ⟨c₄, h₄⟩ := hS' _ hT' _ hT'
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT hT'
  have hex : ∀ τ, ∃ w : M.sm τ, (w : M.H τ) ≠ 0 := fun τ => by
    obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
    exact ⟨⟨w, hw⟩, h0⟩
  choose v hv using hex
  have hv0 : ∏ τ, inner ℂ (v τ : M.H τ) (v τ : M.H τ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hv τ)
  have e : heckeOn M R' T' v = heckeLin V R₁ (T' v) :=
    labelUnique (realUnif D) P (dualLab d) R' R₁ h' h₁' (T' v) (hT'.lev v)
  have key : ∫ g in 𝓕, star (heckeOn M R T v g) * T' v g ∂μ =
      ∫ g in 𝓕, star (T v g) * heckeOn M R' T' v g ∂μ := by
    rw [e]
    exact integral_adjoint h𝓕 K x R R₁ (hT.aut v).cont (hT'.aut v).cont (hT.aut v).left (hT'.aut v).left
      (fun k hk g => by rw [hT.lev v k (hK k hk).1, (hK k hk).2, one_mul])
      (fun k hk g => by rw [hT'.lev v k (hK k hk).1, (hK k hk).2, one_mul])
      (h₃ v v).1 (h₄ v v).1 hR hR₁ hcard
  exact mul_right_cancel₀ hv0 ((h₁ v v).2.symm.trans (key.trans (h₂ v v).2))

end GlobalTheory.HeckeAdjoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_adjoint_heckeOperator_eq_dualLabel : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (J : Subgroup (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M (J : Set (GA D V)) χ μ 𝓕 → ∀ P d R R', Hecke₂ V (J : Set (GA D V)) χ Sb P d R → Hecke₂ V (J : Set (GA D V)) χ Sb P (dualLab d) R' → ∀ T ∈ Mult θ M (J : Set (GA D V)) χ, ∀ T' ∈ Mult θ M (J : Set (GA D V)) χ, heckeOn M R T ∈ Mult θ M (J : Set (GA D V)) χ → heckeOn M R' T' ∈ Mult θ M (J : Set (GA D V)) χ → ipM M μ 𝓕 (heckeOn M R T) T' = ipM M μ 𝓕 T (heckeOn M R' T') := by
  first | exact @GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab | exact GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab | (intros; apply GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.SchwartzTranslate

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def transl (a : κ → AdeleRing (𝓞 F) F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) where
  toFun φ x := φ (x + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem SB_translate {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] (b : X) {g : X → ℂ}
    (hg : g ∈ SB X) : (fun y => g (y + b)) ∈ SB X :=
  ⟨hg.1.comp_continuous (continuous_add_const b), hg.2.comp_homeomorph (Homeomorph.addRight b)⟩

theorem pureA_translate (a : κ → AdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    transl F a (pureA F f g) = pureA F (f.compSubConstCLM ℂ (-fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1))
      (fun y => g (y + fun i => (a i).2)) := by
  funext x
  simp only [transl, LinearMap.coe_mk, AddHom.coe_mk, pureA, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  congr 2
  funext i
  exact map_add _ _ _

theorem schA_translate (a : κ → AdeleRing (𝓞 F) F) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F κ) :
    (fun x => φ (x + a)) ∈ schA F κ := by
  have key : schA F κ ≤ (schA F κ).comap (transl F a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    show transl F a (pureA F f g) ∈ schA F κ
    rw [pureA_translate]
    exact Submodule.subset_span ⟨_, _, SB_translate _ hg, rfl⟩
  exact key hφ

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : κ → AF F), ∀ φ ∈ schA F κ,
    (fun x => φ (x + a)) ∈ schA F κ :=
  fun F _ _ _ _ a φ hφ => schA_translate F a hφ

end GlobalTheory.SchwartzTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartzSpace_translate_mem : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : κ → AF F), ∀ φ ∈ schA F κ, (fun x => φ (x + a)) ∈ schA F κ := by
  first | exact @GlobalTheory.SchwartzTranslate.main | exact GlobalTheory.SchwartzTranslate.main | (intros; apply GlobalTheory.SchwartzTranslate.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.RedFibreField

noncomputable section



open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite in
open Scheme.IdealSheafData in
theorem _root_.GlobalTheory.RedFibreField.isReduced_nilradical_subscheme (X : Scheme.{0}) : IsReduced X.nilradical.subscheme := by
  have h : X.nilradical = vanishingIdeal (⊥ : X.IdealSheafData).support := by
    rw [Scheme.nilradical, vanishingIdeal_support]
  rw [h]
  exact _root_.GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _

end

end GlobalTheory.RedFibreField

namespace GlobalTheory.RedFibreField

end GlobalTheory.RedFibreField
end
