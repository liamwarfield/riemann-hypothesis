module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsE
public import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsThVEqFK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsThetaFunOFThetaTrK
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
structure Wk_k (B : Base F E) {m n : ℕ} (A : Spc F E m) (Y : Spc F E n) (r s : ℕ) (χ : Chr F E) (κ : Type) [Fintype κ]
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ)
    (μ : Measure (UA σ A.J)) (D : Set (UA σ A.J)) : Prop where
  good : _root_.UpperTheory.TP.W.GoodK σ B
  hm : 1 ≤ m
  hn : 1 ≤ n
  aniso : min r s = 0
  sign : A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j
  hecke : IsHecke F E χ
  res : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m
  dbl : IsDbl (σ := σ) (A := A) (Y := Y) B.ψ dd χ om S l
  frame : IsFrame2 σ Y b
  stdK : IsStdK (σ := σ) (Y := Y) B b K
  hgt : IsHgt K a
  haar : μ.IsHaarMeasure
  dom : IsFundamentalDomain (ratU σ A.J) D μ
structure SD_k (σ : E →ₐ[F] E) : Type 1 where
  B : Base F E
  m : ℕ
  n : ℕ
  A : Spc F E m
  Y : Spc F E n
  r : ℕ
  s : ℕ
  χ : Chr F E
  κ : Type
  [fin : Fintype κ]
  dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ
  om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)
  S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ)
  l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ
  b : GL (Fin n ⊕ Fin n) E
  K : Subgroup (G2 σ Y)
  a : G2 σ Y → ℝ
  μ : Measure (UA σ A.J)
  D : Set (UA σ A.J)
  bs : Module.Basis (Fin 2) F E
  ok : _root_.PositivityTheory.SiegelWeilFormula.Wk_k (σ := σ) B A Y r s χ κ dd om S l b K a μ D
attribute [instance] _root_.PositivityTheory.SiegelWeilFormula.SD_k.fin
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev _root_.PositivityTheory.SiegelWeilFormula.SD_k.G : Type := G2 σ d.Y
abbrev _root_.PositivityTheory.SiegelWeilFormula.SD_k.Fn : Type := (d.κ → AF F) → ℂ
abbrev _root_.PositivityTheory.SiegelWeilFormula.SD_k.sch : Submodule ℂ d.Fn := schA F d.κ
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.KFin (Φ : d.Fn) : Prop :=
  Φ ∈ d.sch ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.T (Φ : d.Fn) (X : Mx F E d.m d.n) : ℂ := d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram (X Z : Mx F E d.m d.n) : Mx F E d.n d.n := Xᵀ * incM F d.A.J * Z.map (cA σ)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt (M : Mx F E d.n d.n) : AF F := Algebra.trace (AF F) (AE F E) M.trace
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb (c : Fin d.m × Fin d.n × Fin 2 → AF F) : Mx F E d.m d.n := fun i j => ∑ k, c (i, j, k) ⊗ₜ[F] d.bs k
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd (X : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : AF F :=
  (Algebra.TensorProduct.basis (AF F) d.bs).repr (X k.1 k.2.1) k.2.2
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.schM : Submodule ℂ (Mx F E d.m d.n → ℂ) := (schA F (Fin d.m × Fin d.n × Fin 2)).comap (LinearMap.funLeft ℂ ℂ d.cmb)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.ratM : AddSubgroup (Mx F E d.m d.n) := AddSubgroup.closure (Set.range fun X : Matrix (Fin d.m) (Fin d.n) E => incM F X)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.IsCov (ν : Measure (Mx F E d.m d.n)) : Prop :=
  ν.IsAddHaarMeasure ∧ ∃ 𝓕, IsAddFundamentalDomain d.ratM 𝓕 ν ∧ ν 𝓕 = 1
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.IsW (ε : ℤˣ) (w : d.G) : Prop := inFrame d.b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht (x : d.G) : ℝ≥0 := (d.a x).toNNReal
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.eis (f : d.G → ℂ) (s₁ z : ℂ) : d.G → ℂ :=
  GlobalTheory.Eis.cosetSum (par2 σ d.Y) (rat2 σ d.Y) fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.Eis (f : d.G → ℂ) (s₁ : ℂ) : Prop := ∀ s₀ : ℂ,
  ∃ (U : Set ℂ) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (t : ℝ), IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ p ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (Ê · g) U) ∧ ContinuousOn (fun y : ℂ × d.G => Ê y.1 y.2) (U ×ˢ Set.univ) ∧
    (∀ z ∈ U, ∀ γ ∈ rat2 σ d.Y, ∀ g, Ê z (γ * g) = Ê z g) ∧
    ∀ z : ℂ, t < z.re → (∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q) ∧
      ∀ g, Ê z g = p.eval z * d.eis f s₁ z g
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.Strong : Prop := ∃ r' s', d.Y.IsHerm σ d.B r' s' ∨ d.Y.IsSkew σ d.B r' s'
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0 (Φ : d.Fn) (x : d.G) : ℂ := d.l (d.om x Φ)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.EisAll : Prop := ∀ Φ, d.KFin Φ → d.Eis (d.sec0 Φ) (s0 d.m d.n)
abbrev _root_.PositivityTheory.SiegelWeilFormula.SD_k.I (Φ : d.Fn) : d.G → ℂ := thetaMean d.om d.S d.μ d.D Φ
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.orb (T : nF σ d.Y d.b) (Φ : d.Fn) : ℂ :=
  ⨍ g in d.D, ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
    d.T Φ (mat g⁻¹ * incM F X.1) ∂d.μ
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.lamSet : Set ((d.G → ℂ) → ℂ) :=
  {L | ∃ nb lam 𝓖 T x, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 ∧ IsND T ∧ L = fun f => fc d.B.ψ d.b nb lam 𝓖 f T x}
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw (w : InfinitePlace F) {α β : Type} (X : Matrix α β (AE F E)) : Matrix α β ℂ := X.map (piInf (d.B.emb w))
end SD
structure RD_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) where
  ε : ℤˣ
  ζ : ℂ
  fr : InfinitePlace F → GL (Fin d.m) ℂ
  sg : InfinitePlace F → ℤˣ
  ι : InfinitePlace F → (GR d.n →* d.G)
  hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0
  hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I
  hfr : ∀ w, ζ • ((fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (fr w).1.map star) = ((sg w : ℤ) : ℂ) • 1
  cont : ∀ w, Continuous (ι w)
  at_w : ∀ w y, dZ d.n ζ * d.cw w (inFrame d.b (ι w y)) = mR y * dZ d.n ζ
  off_w : ∀ w w' y, w' ≠ w → d.cw w' (inFrame d.b (ι w y)) = 1
  off_f : ∀ w y, finOne F • inFrame d.b (ι w y) = finOne F • (1 : Matrix _ _ (AE F E))
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc (w : InfinitePlace F) (X : Mx F E d.m d.n) : Fin d.m → Fin d.n → ℂ := (((R.fr w)⁻¹).1 * d.cw w X).map star
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn (s : Finset (InfinitePlace F)) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ {f | ∃ (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ), g ∈ SB _ ∧
    f = fun X => (∏ w ∈ s, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2}
abbrev _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock : Submodule ℂ (Mx F E d.m d.n → ℂ) := R.fockOn Finset.univ
abbrev _root_.PositivityTheory.SiegelWeilFormula.RD_k.away (w : InfinitePlace F) : Submodule ℂ (Mx F E d.m d.n → ℂ) := R.fockOn (Finset.univ.erase w)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ : Mx F E d.m d.n → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  f (R.loc w X) * Ψ X
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.IsLocOp (w : InfinitePlace F) (L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ) : Prop :=
  ∀ y f, IsSw f → IsSw (L y f) ∧ ∀ Ψ : Mx F E d.m d.n → ℂ,
    (∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) →
    ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om (R.ι w y) Φ) = R.tens w (L y f) Ψ
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.IsLift (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (φ : PX d.m d.n →ₗ[ℂ] d.Fn) : Prop :=
  ∀ P, φ P ∈ d.sch ∧ d.T (φ P) = R.tens w (fP P) Ψ
end RD
def TBij_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
  (∀ Φ ∈ d.sch, d.T Φ ∈ d.schM) ∧ (∀ f ∈ d.schM, ∃ Φ ∈ d.sch, d.T Φ = f) ∧ ∀ Φ ∈ d.sch, d.T Φ = 0 → Φ = 0
def TPar_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch,
  (∀ (x : d.G) (β : Mx F E d.n d.n), inFrame d.b x = Matrix.fromBlocks 1 β 0 1 →
    ∀ X, d.T (d.om x Φ) X = d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * d.T Φ X) ∧
  (∀ (x : d.G) (t u : GL (Fin d.n) (AE F E)), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 →
    ∀ X, d.T (d.om x Φ) X = (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * d.T Φ (X * (u⁻¹).1ᵀ)) ∧
  ∀ g X, d.T (d.S g Φ) X = d.T Φ (mat g⁻¹ * X)
def TWeyl_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ν, d.IsCov ν → ∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch,
  ∀ X, d.T (d.om w Φ) X = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.T Φ Z ∂ν
def TTheta_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch,
  HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Φ (incM F X)) (thetaSum F Φ) ∧
  ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ)
def ThetaAuto_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.μ d.D ≠ 0 ∧ d.μ d.D ≠ ⊤ ∧ ∀ Φ ∈ d.sch,
  (∀ x, IntegrableOn (fun g => thetaSum F (d.om x (d.S g Φ))) d.D d.μ) ∧ Continuous (d.I Φ) ∧
  ∀ γ ∈ rat2 σ d.Y, ∀ x, d.I Φ (γ * x) = d.I Φ x
def ThetaCoef_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch,
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ T x, fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = d.orb T (d.om x Φ)
def TAll_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TBij_k ∧ _root_.PositivityTheory.SiegelWeilFormula.TPar_k ∧ _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k ∧ _root_.PositivityTheory.SiegelWeilFormula.TTheta_k ∧ _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k
def CoefEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∃ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖
def RDEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), Nonempty (_root_.PositivityTheory.SiegelWeilFormula.RD_k d)
def SiegelWeilDatumProperties : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), (∃ ν, d.IsCov ν) ∧ (∃ ε w, d.IsW ε w ∧ w ∈ rat2 σ d.Y) ∧
  IsTopologicalGroup d.G ∧ LocallyCompactSpace d.G ∧ T2Space d.G ∧ SecondCountableTopology d.G
def FockMem_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), R.fock ≤ d.schM ∧
  (∀ w, ∀ Ψ ∈ R.away w, (∀ P, R.tens w (fP P) Ψ ∈ R.fock) ∧
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X) ∧
  ∀ w, ∀ f ∈ R.fock, ∃ (k : ℕ) (P : Fin k → PX d.m d.n) (Ψ : Fin k → Mx F E d.m d.n → ℂ),
    (∀ i, Ψ i ∈ R.away w) ∧ f = ∑ i, R.tens w (fP (P i)) (Ψ i)
def LiftEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w, ∀ Ψ ∈ R.away w, ∃ φ, R.IsLift w Ψ φ
def LocOpEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w, ∃ L, R.IsLocOp w L
def LocInst_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w L, R.IsLocOp w L →
  ∃ (sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)) (ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n) (p q : ℕ) (e : ℤ),
    (d.n ≤ d.m → GoodSig d.n p q) ∧ LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ ∧
    (∀ P y, sL P y = L y (fP P) 0) ∧ ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P)
def GSplit_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w L, R.IsLocOp w L → ∀ Ψ ∈ R.away w, ∀ φ, R.IsLift w Ψ φ →
  ∀ g : d.G, ∃ (x : d.G) (y : GR d.n) (c : ℂ) (r : ℝ), 0 < r ∧ g = x * R.ι w y ∧
    ∀ y' : GR d.n, (d.Ht (x * R.ι w y') : ℝ) = r * hLoc y' ∧ ∀ P, d.sec0 (φ P) (x * R.ι w y') = c * L y' (fP P) 0
def GIinv_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w, ∀ Ψ ∈ R.away w, ∀ φ, R.IsLift w Ψ φ →
  ∀ g a b P, d.I (φ (hOp (fun _ => true) (2 * Real.pi) a b P)) g = 0
def GIdil_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w, ∀ Ψ ∈ R.away w, ∀ φ, R.IsLift w Ψ φ →
  ∀ (g : d.G) (X : Fin d.n → ℝ) (a : ℝ → GR d.n), (∀ t, IsDil X t (a t)) → ∃ (U : Set ℂ) (H : GR d.n → ℂ → ℂ), IsOpen U ∧
    (∀ t : ℝ, (t : ℂ) ∈ U) ∧ ContinuousOn (fun y : GR d.n × ℂ => H y.1 y.2) (Set.univ ×ˢ U) ∧ ∀ y, DifferentiableOn ℂ (H y) U ∧
      (∀ t : ℝ, H y t = d.I (φ 1) (g * R.ι w (y * a t))) ∧
      ∀ r : ℕ, iteratedDeriv r (H y) 0 = d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y)
def KFinPoly_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → d.T Φ ∈ R.fock
def PolyKFin_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ ∈ d.sch, d.T Φ ∈ R.fock → d.KFin Φ
def SecK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ, d.KFin Φ → IsSec d.K d.χ (s0 d.m d.n) (d.sec0 Φ)
def EisStrong_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.Strong → ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁
def LamBd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ L ∈ d.lamSet,
  (∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
    (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) → L (a • f + f') = a * L f + L f') ∧
  ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
    (∀ x ∈ C, ‖f x‖ ≤ M) → ‖L f‖ ≤ M
def FourierZero_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ f : d.G → ℂ, Continuous f →
  (∀ β ∈ nF σ d.Y d.b, ∀ g, f (nb β * g) = f g) → (∀ T g, fc d.B.ψ d.b nb lam 𝓖 f T g = 0) → f = 0
def DenseW_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w (y : GR d.n) (O : Set (GR d.n)), IsOpen O → y ∈ O →
  ∃ γ ∈ rat2 σ d.Y, ∃ y' ∈ O, ∃ x : d.G, γ = x * R.ι w y' ∧ ∀ y'' : GR d.n, x * R.ι w y'' = R.ι w y'' * x
def LamSing_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w (f : d.G → ℂ), Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
  (∀ L ∈ d.lamSet, L f = 0) → ∀ ψ₀, IsSingTest ψ₀ → ∀ nb : (Fin d.n → Fin d.n → ℝ) → GR d.n, (∀ x, mR (nb x) = nU (herm x)) →
    ∀ (g : d.G) (a b : GR d.n), ∫ x, f (g * R.ι w (a * nb x * b)) * ψ₀ x = 0
def Unfold_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ x,
    Integrable (fun β => flat d.a f s₁ z (w * nb β * x)) lam ∧ ∀ T, IsND T →
      fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T x = ∫ β, flat d.a f s₁ z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
def WhitK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.n < d.m → d.EisAll → ∀ Φ, d.KFin Φ →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T → ∀ x,
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (d.orb T (d.om x Φ))
def Main_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.n < d.m → d.EisAll → ∀ Φ, d.KFin Φ → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (d.I Φ x)
def MainOf_k : Prop :=
  AbsThm → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.RDEx_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.GIinv_k → _root_.PositivityTheory.SiegelWeilFormula.GIdil_k → _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k →
    _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.LamSing_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.WhitK_k → _root_.PositivityTheory.SiegelWeilFormula.Main_k
def HeadOf_k : Prop := _root_.GlobalTheory.ThK.Dbl.EisBL_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.EisStrong_k → _root_.PositivityTheory.SiegelWeilFormula.Main_k → _root_.PositivityTheory.SiegelWeilFormula.SWStdLt_k
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseKPair
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
def Stab2Cpt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → IsCompact (K : Set (G2 σ Y))
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} {χ : Chr F E} {z s₀ : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}
theorem kpair_cont_k {B : Base F E} {r s : ℕ} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (h0 : min r s = 0)
    (c : Cpt σ Y.J) (hχ : IsHecke F E χ) (he : ∀ h h', IsEmb h h' (e (h, h'))) (ce : Continuous e)
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) (ca : Continuous a) (a0 : ∀ x, 0 < a x) (cf : Continuous f) (hf : Law χ z f)
    {U Ê} (hE : IsEisCont (flat a f s₀) U Ê) {μ : Measure (UA σ Y.J)} {D : Set (UA σ Y.J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ Y.J) D μ) {t₀ : ℝ} (hi : ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ) :
    (∀ φ, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U) ∧ ∃ t : ℝ, ∀ s : ℂ, t < s.re → s ∈ U ∧
      Integrable (fun g => flat a f s₀ s (e (1, g)) * detInv χ g) μ ∧ ∀ φ, IsRapid φ → kpair χ e μ D (Ê s) φ =
        ∫ g, flat a f s₀ s (e (1, g)) * detInv χ g * pet μ D (fun h => φ (h * g)) φ ∂μ := by
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hB hY h0
  obtain ⟨t₁, half⟩ := hE.half
  haveI := c.sc; haveI := c.lc
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using c.fin _ _ hμ hD⟩
  have bc : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → An.BC φ := fun h => ⟨h.1, c.bdd h.1 h.2.1⟩
  have cE : ∀ s ∈ U, Continuous (Ê s) := fun s hs =>
    hE.cont.comp_continuous (f := fun x => (s, x)) (by fun_prop) fun _ => ⟨hs, trivial⟩
  have iv : ∀ s ∈ U, ∀ γ ∈ ratU σ Y.J, ∀ δ ∈ ratU σ Y.J, ∀ g g', Ê s (e (γ * g, δ * g')) = Ê s (e (g, g')) := fun s hs γ hγ δ hδ g g' =>
    An.ident hE.isOpen hE.conn (hE.hol _) (hE.hol _) (fun s hs => ⟨(half s hs).1, by
      rw [← Prod.mk_mul_mk, map_mul]; exact (hf.flat ha a0 s).eis_inv hχ hJ he (half s hs).2 hγ hδ _⟩) hs
  have ck : ∀ s ∈ U, An.BC fun y : UA σ Y.J × UA σ Y.J => Ê s (e y) * detInv χ y.2 := fun s hs =>
    An.BC.mul ⟨(cE s hs).comp ce, c.bdd₂ c ((cE s hs).comp ce) (iv s hs)⟩
      ⟨(continuous_detInv hχ).comp continuous_snd, 1, fun y => (norm_detInv _ _).le⟩
  have hol : ∀ {φ : UA σ Y.J → ℂ}, IsRapid φ → DifferentiableOn ℂ (fun s => kpair χ e μ D (Ê s) φ) U := fun {φ} h => by
    have b := ((bc h).comp (continuous_snd (X := UA σ Y.J))).mul ((bc h).comp continuous_fst).star
    refine An.diffOn_integral hE.isOpen (fun s hs => ((ck s hs).mul b).1.aestronglyMeasurable)
      (fun y => ((hE.hol _).mul_const _).mul_const _) fun S hS cS => ?_
    obtain ⟨Ω, hΩ, cov⟩ := c.cov
    obtain ⟨C, hC⟩ := (cS.prod ((hΩ.prod hΩ).image ce)).exists_bound_of_continuousOn
      (hE.cont.mono (Set.prod_mono hS (Set.subset_univ _)))
    obtain ⟨C', hC'⟩ := b.2
    refine ⟨C * C', fun s hs y => ?_⟩
    obtain ⟨γ, hγ, h1⟩ := cov y.1
    obtain ⟨δ, hδ, h2⟩ := cov y.2
    have := hC (s, e (γ * y.1, δ * y.2)) ⟨hs, _, ⟨h1, h2⟩, rfl⟩
    rw [iv s (hS hs) γ hγ δ hδ] at this
    rw [norm_mul, norm_mul, norm_detInv, mul_one]
    exact mul_le_mul this (hC' y) (norm_nonneg _) ((norm_nonneg _).trans this)
  refine ⟨fun _ => hol, max t₁ (t₀ + s₀.re - z.re), fun s hs => ?_⟩
  obtain ⟨u, sm⟩ := half s ((le_max_left _ _).trans_lt hs)
  have cs := continuous_flat (s₀ := s₀) cf ca a0 s
  obtain ⟨C, hC⟩ := (hf.flat (s₀ := s₀) ha a0 s).bound cs ha hK
  have i1 : Integrable (fun g => flat a f s₀ s (e (1, g))) μ :=
    ((hi (s - s₀ + z).re (by have := (le_max_right _ _).trans_lt hs; simp; linarith)).const_mul C).mono'
      (cs.comp (ce.comp (Continuous.prodMk_right 1))).aestronglyMeasurable (.of_forall fun g => hC _)
  have i2 := i1.mul_bdd (continuous_detInv hχ).aestronglyMeasurable (.of_forall fun g => (norm_detInv χ g).le)
  exact ⟨u, i2, fun φ h => An.far_right _ μ (ck s u) (bc h) i2
    (_root_.GlobalTheory.ThK.Dbl.unfold0_k F E σ B n Y r _ hB hY h0 χ e hχ he _ _ _ cs (cE s u) sm (hf.flat ha a0 s) μ D hμ hD i1 _ h)⟩
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseCpt
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
def CptAll_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 → Cpt σ Y.J
theorem cptAll_of_k (h1 : PositivityTheory.ThKEst.GrpTop) (h2 : _root_.PositivityTheory.ThKEst.EpsOf_k) (h3 : PositivityTheory.ThKEst.SiegelAll) (h4 : PositivityTheory.ThKEst.FinVolU)
    (h5 : PositivityTheory.ThKF.Unimod) : _root_.GlobalTheory.ThK.Dbl.CptAll_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0
  obtain ⟨e, -, hr⟩ := h2 F E σ B hB n Y r s hY
  obtain ⟨a1, a2, a3, a4, -, -, -, a5⟩ := h1 F E σ hB.cm n Y.J e
  obtain ⟨fr, g, -, ⟨Ω, hΩ, hc⟩, -⟩ := h3 F E σ hB.cm n Y.J e
  have r0 : fr.r = 0 := by have := hr fr g; omega
  have a0 : ∀ t, fr.a t = 1 := fun t => by
    have : t + t = t := funext fun i => absurd i.2 (by omega)
    have e := g.add t t
    rw [this] at e
    exact left_eq_mul.1 e
  have cov : ∀ x, ∃ γ ∈ ratU σ Y.J, γ * x ∈ Ω := fun x => by
    obtain ⟨γ, hγ, t, -, κ, hκ, e⟩ := hc x
    exact ⟨γ, hγ, by rwa [e, a0, one_mul]⟩
  obtain ⟨C, hC⟩ := a5 Ω hΩ
  obtain ⟨-, u1, u2⟩ : Countable (ratU σ Y.J) ∧ _ ∧ _ := e.1.elim
    (fun h => h5 F E σ hB.cm n Y.J 1 (fun i j => by simp [h]) e.2) fun h => h5 F E σ hB.cm n Y.J (-1) (fun i j => by simp [h]) e.2
  refine ⟨a1, a2, a3, a4, ⟨Ω, hΩ, cov⟩, ⟨C, fun x => ?_⟩, u1, h4 F E σ hB.cm n Y.J e, u2⟩
  obtain ⟨γ, hγ, hx⟩ := cov x
  exact (ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ Y.J)).trans (hC _ hx)
section Gen
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] {Γ : Subgroup G} [Countable Γ] {D : Set G}
end Gen
variable {J : Matrix (Fin n) (Fin n) E}
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstEpsOf
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
namespace SignatureOfHermitianForm
end SignatureOfHermitianForm
theorem epsOf_of_k : _root_.PositivityTheory.ThKEst.EpsOf_k := by
  intro F E _ _ _ _ _ σ B hB n X r s hX
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hτ := hB.cm.2.2.2 (B.emb w).1
  rcases hX with hX | hX
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J 1 one_ne_zero (r := r) (s := s) (by rw [one_smul]; exact hX.sig w)
    exact ⟨⟨Or.inl hX.herm, this.1⟩, this.2⟩
  · have := SignatureOfHermitianForm.of_sig σ _ hτ X.J Complex.I Complex.I_ne_zero (hX.sig w)
    exact ⟨⟨Or.inr hX.skew, this.1⟩, this.2⟩
end PositivityTheory.ThKEst
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchrodingerModelIntertwining
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_model_intertwining : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e = f := by
  first | exact @_root_.GlobalTheory.ThetaOntoF.exists_thV_eqF_k | exact _root_.GlobalTheory.ThetaOntoF.exists_thV_eqF_k | (intros; apply _root_.GlobalTheory.ThetaOntoF.exists_thV_eqF_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationPairContinuous
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_pair_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
              ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) := by
  first | exact @_root_.GlobalTheory.TransportHeisF.pres_impl_k | exact _root_.GlobalTheory.TransportHeisF.pres_impl_k | (intros; apply _root_.GlobalTheory.TransportHeisF.pres_impl_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ActsExK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKF0
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK
open PositivityTheory.ThKH.Locrep
theorem actsEx_k : _root_.GlobalTheory.ThK.ActsEx_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v
  obtain ⟨ω, ρ, L⟩ := _root_.PositivityTheory.ThKH.Locrep.locRepEx_k F E σ n d B X W M om ⟨hP.base, ⟨r, s, hP.herm⟩, ⟨r', s', hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  refine ⟨fun g hg h hh φ hφ => ⟨ω (g, h) φ, ⟨L.pres g hg h hh φ hφ, (L.acts g hg h hh φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.acts g hg h hh φ hφ _).1 h₁.2⟩,
    fun u hu φ hφ => ⟨ρ u φ, ⟨L.presH u hu φ hφ, (L.actsH u hu φ hφ _).2 rfl⟩,
      fun φ₁ h₁ => (L.actsH u hu φ hφ _).1 h₁.2⟩, fun φ hφ => ?_⟩
  have hs := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨r₀, x₀, h₀, h₁⟩ := exists_base (Fin n × Fin d) v
  let loc : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v) := fun p => res v x₀ ∘ₗ om p ∘ₗ tensL v r₀
  have hloc : ∀ p : UA σ X.J × UA σ W.J, p.1 ∈ UAt σ X (evFin F v) → p.2 ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _,
      loc p φ = ω p φ := fun p h1 h2 φ hφ =>
    (eq_of_acts v h₁ (h₀ φ hφ) ((L.acts p.1 h1 p.2 h2 φ hφ _).2 rfl)).symm
  obtain ⟨K, hK1, hK2, hK3, hK4⟩ := exists_small_subgroups σ X v
  obtain ⟨K', hK1', hK2', hK3', hK4'⟩ := exists_small_subgroups σ W v
  obtain ⟨m, hm⟩ := smooth_of_weak (SB _) (fun k => (K k).prod (K' k))
    (fun a b hab => Subgroup.prod_mono (hK1 hab) (hK1' hab))
    (fun U hU => by
      obtain ⟨U₁, h1, U₂, h2, h⟩ := mem_nhds_prod_iff.1 hU
      obtain ⟨a, ha⟩ := hK2 U₁ h1
      obtain ⟨b, hb⟩ := hK2' U₂ h2
      exact ⟨max a b, fun p hp => h ⟨ha (hK1 (le_max_left a b) hp.1), hb (hK1' (le_max_right a b) hp.2)⟩⟩)
    loc (fun p hp φ hφ => by
      rw [hloc p (hK3 0 hp.1) (hK3' 0 hp.2) φ hφ]
      exact L.pres p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) φ hφ)
    (fun φ hφ => by
      rw [hloc 1 (one_mem_UAt X v) (one_mem_UAt W v) φ hφ]
      exact L.one φ hφ)
    (fun p hp q hq φ hφ => by
      rw [hloc (p * q) (mul_mem_UAt (hK3 0 hp.1) (hK3 0 hq.1)) (mul_mem_UAt (hK3' 0 hp.2) (hK3' 0 hq.2)) φ hφ,
        hloc q (hK3 0 hq.1) (hK3' 0 hq.2) φ hφ,
        hloc p (hK3 0 hp.1) (hK3' 0 hp.2) _ (L.pres q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)]
      exact L.mul p.1 (hK3 0 hp.1) p.2 (hK3' 0 hp.2) q.1 (hK3 0 hq.1) q.2 (hK3' 0 hq.2) φ hφ)
    (fun l φ hφ => hs.cont _ (res_adm v x₀ l) _ (h₀ φ hφ).2) φ hφ
  obtain ⟨U, hU, hUK⟩ := hK4 m
  obtain ⟨U', hU', hUK'⟩ := hK4' m
  refine ⟨U ×ˢ U', prod_mem_nhds hU hU', fun x hx h1 h2 => ?_⟩
  refine (L.acts x.1 h1 x.2 h2 φ hφ φ).2 ?_
  rw [← hloc x h1 h2 φ hφ]
  exact (hm x ⟨hUK _ hx.1 h1, hUK' _ hx.2 h2⟩).symm
end PositivityTheory.ThKF0
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseFrameConj
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Frame
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling
open Formalism.UG (bc)
section Generic
variable {S R β : Type} [CommRing S] [CommRing R] [Fintype β] [DecidableEq β]
end Generic
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
end GlobalTheory.ThK.Dbl.Frame
namespace GlobalTheory.ThK.Dbl
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Doubling GlobalTheory.ThK.Dbl.Frame
open Formalism.UG (bc)
theorem frameConj_k : _root_.GlobalTheory.ThK.Dbl.FrameConj_k := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY K hK
  have hc := hB.cm
  have hσ := cm_conj_conj hc
  have hL : Y.L.IsLattice E := hY.elim (·.lat.toIsLattice) (·.lat.toIsLattice)
  have hJ := Frame.det_ne hY
  obtain ⟨ε, hε, c, c1, c2⟩ : ∃ ε : ℤˣ, (Y.J.map σ)ᵀ = ((ε : ℤ) : E) • Y.J ∧ ∃ c : ℂ, star c * c = 1 ∧
      ∀ w, (c • Y.J.map (B.emb w).1)ᴴ = c • Y.J.map (B.emb w).1 ∧ IsCartan (c • Y.J.map (B.emb w).1) (Y.θ w) := by
    rcases hY with h | h
    · refine ⟨1, Matrix.ext fun i j => by simpa using h.herm i j, 1, by simp, fun w => ?_⟩
      rw [one_smul]
      exact ⟨Matrix.ext fun i j => (hc.2.2.2 _ _).symm.trans (congrArg _ (h.herm i j)), h.cartan w⟩
    · refine ⟨-1, Matrix.ext fun i j => by simpa using h.skew i j, Complex.I, by simp, fun w => ⟨Matrix.ext fun i j => ?_, h.cartan w⟩⟩
      change star (Complex.I * (B.emb w).1 (Y.J j i)) = Complex.I * (B.emb w).1 (Y.J i j)
      rw [star_mul', ← hc.2.2.2, h.skew]; simp
  have ee : ∀ (S : Type) [CommRing S], ((ε : ℤ) : S) * (ε : ℤ) = 1 := fun S _ => by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  choose gw hw using fun w => Frame.exists_arch c1 (c2 w).1 (Frame.isUnit_of_cartan (c2 w).2) (c2 w).2
  obtain ⟨a, g, ha, hg, hg'⟩ := _root_.GlobalTheory.ThK.Dbl.Frame.exists_ad_k hB hY hJ gw
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  let ι := inclR (F := F) (E := E) (AF F)
  let cc : AE F E →+* AE F E := cA σ
  have hι : ∀ z, ι (σ z) = cc (ι z) := fun z => rfl
  have hcc : ∀ z, cc (cc z) = z := fun z => by
    change cA σ (cA σ z) = z
    rw [cA_eq]; exact sigR_invol hσ z
  have hf : ∀ v z, compFin F E v (cc z) = sigR _ σ (compFin F E v z) := fun v z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hi : ∀ w z, piInf (B.emb w) (cc z) = star (piInf (B.emb w) z) := fun w z => by
    refine Eq.trans (congrArg (infEmb (B.emb w)) ?_) (infEmb_sigR hc (B.emb w) (compInf F E w z)).symm
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have jf : ∀ v, (incM F Y.J).map (compFin F E v) = Y.J.map (inclR (F := F) (Fv F v)) := fun v =>
    Matrix.ext fun i j => congrArg (· ⊗ₜ[F] Y.J i j) (map_one (evFin F v))
  have ii : ∀ w z, piInf (B.emb w) (ι z) = (B.emb w).1 z := fun w z => by
    change InfinitePlace.Completion.extensionEmbedding w 1 * (B.emb w).1 z = _
    rw [map_one, one_mul]
  have ji : ∀ w, (incM F Y.J).map (piInf (B.emb w)) = Y.J.map (B.emb w).1 := fun w => Matrix.ext fun i j => ii w _
  have h2 : (2⁻¹ : E) + σ 2⁻¹ = 1 := by rw [map_inv₀, map_ofNat]; norm_num
  let α : AE F E := ι 2⁻¹ + eF F • ι (t - 2⁻¹)
  have α0 : α + cc α = 1 := by
    have : cc α = ι (σ 2⁻¹) + eF F • ι (σ (t - 2⁻¹)) := by
      rw [hι, hι, map_add (f := _)]; exact congrArg _ (map_smul (cA σ) _ _)
    rw [this, add_add_add_comm, ← smul_add, ← map_add (f := _), ← map_add (f := _), h2, map_sub σ, sub_add_sub_comm, ht, h2, sub_self]
    simp
  have α1 : ∀ v, compFin F E v α ∈ intLoc F E v := fun v => by
    rw [map_add (f := _), comp_eF, ← map_add (f := _), ← map_add (f := _), add_sub_cancel]
    exact tmul_mem_intLoc (a := evFin F v 1) (by rw [map_one]; exact one_mem _) t
  have α2 : ∀ w, piInf (B.emb w) α = 2⁻¹ := fun w => by
    have : piInf (B.emb w) (algebraMap (AF F) (AE F E) (eF F)) = 0 := by
      change InfinitePlace.Completion.extensionEmbedding w 0 * (B.emb w).1 1 = _
      rw [map_zero, zero_mul]
    rw [map_add (f := _), Algebra.smul_def, map_mul, this, zero_mul, add_zero, ii, map_inv₀, map_ofNat]
  have uJ : IsUnit Y.J := (Matrix.isUnit_iff_isUnit_det _).2 hJ.isUnit
  obtain ⟨T₀, hT₀⟩ := exists_dual (σ : E →+* E) hσ uJ 1
  obtain ⟨T, hT⟩ := exists_dual cc hcc (J := incM F Y.J) (uJ.map ι.mapMatrix) g
  have g0 := frame_gram (σ : E →+* E) hσ (ee E) h2 hε 1 T₀ hT₀
  have g1 := frame_gram cc hcc (ee _) α0 (J := incM F Y.J) (Matrix.ext fun i j => by
    have := congrArg ι (congrFun (congrFun hε i) j)
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_intCast] at this
    exact this) g T hT
  have d0 := frame_diag 1 T₀ (2⁻¹ : E)
  set b := two 1 * wit (2⁻¹ : E) T₀
  have d1 := frame_diag g T α
  set b' := two g * wit α T with hb'
  have g2 : (bc ι b).1ᵀ * dbl (incM F Y.J) * (bc ι b).1.map cc = b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc := by
    have := (map_gram ι hι b.1 (dbl Y.J)).symm.trans (congrArg (·.map ι) g0)
    rw [map_dbl] at this
    rw [g1]
    refine this.trans ?_
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, apply_ite ι]
  let p : G2 σ Y := ⟨b' * (bc ι b)⁻¹, by
    change (b'.1 * ((bc ι b)⁻¹).1)ᵀ * _ * (b'.1 * ((bc ι b)⁻¹).1).map cc = _
    calc _ = ((bc ι b)⁻¹).1ᵀ * (b'.1ᵀ * dbl (incM F Y.J) * b'.1.map cc) * ((bc ι b)⁻¹).1.map cc := by
          simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = ((bc ι b).1 * ((bc ι b)⁻¹).1)ᵀ * dbl (incM F Y.J) * ((bc ι b).1 * ((bc ι b)⁻¹).1).map cc := by
          simp only [← g2, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]⟩
  have fr : ∀ k : G2 σ Y, inFrame b k = (b'⁻¹ * (p * k * p⁻¹).1 * b').1 := fun k => by
    rw [show b'⁻¹ * (p * k * p⁻¹).1 * b' = bc ι b⁻¹ * k.1 * bc ι b by
      change b'⁻¹ * (b' * (bc ι b)⁻¹ * k.1 * (b' * (bc ι b)⁻¹)⁻¹) * b' = _
      rw [map_inv]; group]
    rfl
  have fin : ∀ k : G2 σ Y, Keeps (p * k * p⁻¹) ↔ ∀ i j, eF F • inFrame b k i j ∈ intHat F E := fun k => by
    simp only [keeps_iff hL.fg ha, mem_intHat, fr]
    refine (forall_congr' fun v => ?_).trans (forall_comm.trans (forall_congr' fun i => forall_comm))
    obtain ⟨⟨l, hl⟩, u1, G', u2, u3⟩ := hg v
    obtain ⟨q1, q2⟩ := int_dual (T := bc (compFin F E v) T) (sigR_invol hσ) (fun z => sigR_mem_intLoc σ) u1 u2 u3 (by
      have := congrArg (·.map (compFin F E v)) hT
      simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hf v), jf, Matrix.map_one _ (map_zero _) (map_one _)] at this
      rw [← this]
      congr 1
      exact Matrix.ext fun i j => (hf v _).symm)
    obtain ⟨q3, q4⟩ := int_wit (α1 v) q1 q2
    have := int_conj hl q3 q4 (bc (compFin F E v) (p * k * p⁻¹).1)
    simp only [← bc_wit, ← bc_two, ← map_mul (bc (compFin F E v)), ← map_inv (bc (compFin F E v))] at this
    exact this
  refine ⟨b, K.comap (MulAut.conj p).toMonoidHom, p, g, ⟨⟨ε, g0⟩, 1, ?_⟩, fun k => ?_, ?_, fun k => ?_⟩
  · rw [← d0, ← Matrix.fromCols_toCols b.1, Matrix.fromCols_mul_fromRows]; simp
  · refine (hK (p * k * p⁻¹)).trans (and_congr (forall_congr' fun w => ?_) ?_)
    · have := hw w (bc (piInf (B.emb w)) T) (by
        have := congrArg (·.map (piInf (B.emb w))) hT
        simp only [Matrix.map_mul (M := T.1.map cc), map_gram _ (hi w), ji, Matrix.map_one _ (map_zero _) (map_one _)] at this
        rw [← this, ← hg']
        congr 1
        exact Matrix.ext fun i j => (hi w _).symm) (bc (piInf (B.emb w)) (p * k * p⁻¹).1) (by
        have := (map_gram _ (hi w) _ _).symm.trans (congrArg (·.map (piInf (B.emb w))) (show _ = _ from (p * k * p⁻¹).2))
        simp only [map_dbl, ji] at this
        exact this)
      rw [← hg', ← α2 w, ← bc_wit, ← bc_two, ← map_mul, ← map_inv, ← map_mul, ← map_mul] at this
      rw [fr]
      exact this.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, forall_and]
      refine Iff.trans ?_ (and_congr (fin k) (fin k⁻¹))
      rw [show p * k⁻¹ * p⁻¹ = (p * k * p⁻¹)⁻¹ by group]
      simp only [Keeps, forall_and]
      exact and_and_and_comm
  · exact par_of ι (d0.trans (Matrix.mul_one _)) d1
  · change _ ↔ p * (p⁻¹ * k * p) * p⁻¹ ∈ K
    rw [show p * (p⁻¹ * k * p) * p⁻¹ = k by group]
end GlobalTheory.ThK.Dbl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationPairUnitary
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsUnitaryOnTransportFK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledLagrangianThetaCompatible
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HaarFundDomainTransferK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.RatDarbouxTransferF
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem haar_fundDomain_transfer_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
            IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
            ∃ (ν' : @Measure ((κ → AF F) × (κ → AF F)) (borel _)) (𝓕' : Set ((κ → AF F) × (κ → AF F))),
              @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
              @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕' ν' ∧
              ∀ f : (κ → AF F) × (κ → AF F) → ℂ,
                ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  obtain ⟨hfr, hfin, -⟩ := finrank_AEF F E
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI hMT : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  letI mP : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
  haveI : BorelSpace ((κ → AF F) × (κ → AF F)) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let ce : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃L[AF F] (κ → AF F) × (κ → AF F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : WOF F E nS nT ≃ₜ+ (κ → AF F) × (κ → AF F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me : WOF F E nS nT ≃ᵐ (κ → AF F) × (κ → AF F) := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratLF F E nS nT, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, co.e.symm p ∈ ratLF F E nS nT :=
    onto F E nS nT κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : WOF F E nS nT) + x) = co.e g + co.e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS nT := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratLF F E nS nT := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS nT => co.e (t : WOF F E nS nT)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F κ) (k : ratLF F E nS nT),
          (k : WOF F E nS nT) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF F) × (κ → AF F)) + co.e w = co.e ((k : WOF F E nS nT) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl
end GlobalTheory.RatDarbouxTransferF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_lagrangian_theta_compatible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
            IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
            ∃ (ν' : @Measure ((κ → AF F) × (κ → AF F)) (borel _)) (𝓕' : Set ((κ → AF F) × (κ → AF F))),
              @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
              @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕' ν' ∧
              ∀ f : (κ → AF F) × (κ → AF F) → ℂ,
                ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  first | exact @_root_.GlobalTheory.RatDarbouxTransferF.haar_fundDomain_transfer_k | exact _root_.GlobalTheory.RatDarbouxTransferF.haar_fundDomain_transfer_k | (intros; apply _root_.GlobalTheory.RatDarbouxTransferF.haar_fundDomain_transfer_k <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.WeilUnitaryTransportF
theorem isUnitaryOn_transportF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ χS χT hcS hcT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have hψ := hω.std
  rintro μ hμ ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := _root_.GlobalTheory.T.doubled_lagrangian_intertwiner F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm a b
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_rationalMatrices_tower F E nS nT
  obtain ⟨ν', 𝓕', hν', h𝓕', heq⟩ :=
    _root_.GlobalTheory.T.doubled_lagrangian_theta_compatible F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat ν 𝓕 hν h𝓕
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform F B.ψ hψ.1 κ μ hμ ν' hν' 𝓕' h𝓕'
  have hiso : ∀ Ψ ∈ schA F κ, ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂μ =
      c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Ψ w‖ₑ ^ 2 ∂ν := by
    intro Ψ hΨ
    rw [hc Ψ hΨ, ← heq]
    rfl
  have hth : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
    ⟨_root_.GlobalTheory.T.doubled_lagrangian_continuous F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.T.doubled_lagrangian_unitary F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.T.doubled_lagrangian_equivariant F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ,
     _root_.GlobalTheory.T.doubled_lagrangian_invariant_functional F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat Φ hΦ⟩
  have ht := hom a b g h hh hg Φ hΦ
  calc
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ ((om (a, b)) Φ) w‖ₑ ^ 2 ∂ν := hiso _ ht.1
    _ = c * ∫⁻ w in 𝓕, ‖GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w‖ₑ ^ 2 ∂ν := by
      exact (congrArg (fun f => c * ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂ν) ht.2).trans
        (congrArg (c * ·) (hω.om_unit ν 𝓕 hν h𝓕 _ _ hth))
    _ = _ := (hiso _ hΦ).symm
end GlobalTheory.WeilUnitaryTransportF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_pair_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  first | exact @_root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k | exact _root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k | (intros; apply _root_.GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstCoefEq
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKEst
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
theorem coefEq_of_k : _root_.PositivityTheory.ThKEst.CoefEq_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP μ hμ Φ₁ h₁ Φ₂ h₂ g h z
  have hs := IsUWeilPair.isUSplitting hP.weil
  set w := mat g⁻¹ * z * (mat h⁻¹)ᵀ with hw
  have e : actAB (cA σ) (g, h) w = z := by
    have a : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1
    have b : (mat h⁻¹)ᵀ * (mat h)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, show mat h * mat h⁻¹ = 1 from Units.mul_inv h.1, Matrix.transpose_one]
    change mat g * w * (mat h)ᵀ = z
    rw [hw, Matrix.mul_assoc (mat g⁻¹), ← Matrix.mul_assoc (mat g), a, Matrix.one_mul, Matrix.mul_assoc, b,
      Matrix.mul_one]
  have i := hs.impl (g, h) w Φ₁ h₁
  rw [e] at i
  have k := inner_eq_of_unit μ (om (g, h)) (hs.pres _) (hs.unit μ hμ _)
    (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std w Φ₁ h₁) h₂
  rw [i] at k
  exact k
end PositivityTheory.ThKEst
end
end
end
