module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly

section Darboux

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def darbAlg {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      f ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.Pol M ψ τ ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧ Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ}


open Classical in
def liftPure {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F) → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v) :
    ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s :=
  if H : ∃ q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v))
  then H.choose else 0

end Darboux

theorem exists_rtensOp {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i)
    (a : ∀ i, Module.End ℂ (N i)) :
    ∃ T : Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s), ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      T (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (fun i => a i (ξ i)) :=
  GlobalTheory.SmallThetaModules.exists_lift s (GlobalTheory.SmallThetaModules.pureT s)
    (fun l hl => GlobalTheory.SmallThetaModules.pureT_sep s l hl) s a

variable {D : D7}

def vacIm {a a' : ℕ} (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F a a') :
    ∀ v, Rf.Pi v := fun v => Rf.p v (Γ.M.vac v)

abbrev PiT {a a' : ℕ} (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F a a') (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F a a') : Type :=
  R.Pi ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens (vacIm Γ Rf)


open Classical in
def thetaLift {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (S : Submodule ℂ ((Fin m × Fin k → AF D.host.F) → ℂ)) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pD : ((Fin m × Fin k → AF D.host.F) → ℂ) →ₗ[ℂ] P) : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] P :=
  if H : ∃ q : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] P, ∀ Ψ ∈ S, q (GlobalTheory.TripleRead.thO Mo ψ G e Ψ) = pD Ψ
  then H.choose else 0

def mapA (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) :
    (WO W X → ℂ) →ₗ[ℂ] PiT R Γ Rf :=
  thetaLift Γ.M ψ (sgn true W).gram e (darbAlg Γ.M Bs.ψ Bs.emb) (liftPure Γ.M R.p Rf.p (vacIm Γ Rf))

def mapB (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank) :
    (WO W₁ X → ℂ) →ₗ[ℂ] PiT R Γ Rf :=
  thetaLift Γ.M' ψ (sgn false W₁).gram e (darbAlg Γ.M' Bs.ψ Bs.emb) (liftPure Γ.M' R.p' Rf.p' (vacIm Γ Rf))


open Classical in
def opFin {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : (WO M X → ℂ) →ₗ[ℂ] P) (h : GA D X) : Module.End ℂ P :=
  if H : ∃ T : Module.End ℂ P, ∀ Φ ∈ S, p (ω (1, h) Φ) = T (p Φ) then H.choose else 1


open Classical in
def opLie (θ : InfFam D) {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) {P : Type} [AddCommGroup P]
    [Module ℂ P] (p : (WO M X → ℂ) →ₗ[ℂ] P) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) : Module.End ℂ P :=
  if H : ∃ T : Module.End ℂ P, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ X (fun h => ω (1, h)) τ Y Φ Φ' → p Φ' = T (p Φ)
  then H.choose else 0

end GlobalTheory.TripleAssembly

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict

variable {D : D7}

def sgE (ε : Bool) : D.host.E := if ε then 1 else -1

def PublishedHyps (D : D7) {n d : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) : Prop :=
  IsCMExt D.host.F D.host.E D.sp.cm.sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ' ∧
    (∀ i j, D.sp.cm.sig (Xs.J j i) = Xs.J i j) ∧ Xs.J.det ≠ 0 ∧
    (∀ i j, D.sp.cm.sig (Ws.J j i) = -Ws.J i j) ∧ Ws.J.det ≠ 0 ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX n ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW d ∧
    IsHecke D.host.F D.host.E χX ∧ IsHecke D.host.F D.host.E χW ∧ Mo.IsWeil ψ' χX χW om ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Xs.J.map (τ w).1) (Xs.θ w)) ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • Ws.J.map (τ w).1) (Ws.θ w))

structure IsPairReading (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (ω : WRep M X)
    (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws) (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) : Prop where

  psi : ψ' = ψ

  JX : Xs.J = sgE (D := D) ε • M.gram

  JW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))

  cart : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
    Ws.θ w = (B.cart t).map conj

  good : Mo.IsGood ψ'

  transp : GlobalTheory.TripleRead.IsTransp ψ ε Mo om ω (Equiv.refl (Fin X.rank)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (sgE (D := D) ε) JX)
    (GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) JW)

def IsFockMap (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)
    {Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank} {Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws)
    (Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank)) : Prop :=
  ∃ (f₀ : WO (sgn ε M) X → ℂ) (r : (Fin M.rank × Fin X.rank → AF D.host.F) → ℂ),
    IsVacF ψ θ (frSgn ε A) B f₀ ∧ f₀ ≠ 0 ∧
    ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r ∧
      GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram (Equiv.refl (Fin X.rank))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r) = ptF ψ θ (frSgn ε A) B f₀ P

end GlobalTheory.RealDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SquareAgree

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

structure IsThetaSubG (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W)
    (N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop where

  le : N ≤ algD M ψ emb

  fin : ∀ (v : Pl (F := F)) (f : SInf F (Fin n × Fin d)) (φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ), f ∈ M.Pol ψ emb →
    (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) → φ v ∈ augAt om v → pure f φ ∈ N

  lie : ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb,
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ ∈ N

  cpt : ∀ k ∈ KInf σ X emb, ∀ f ∈ M.Pol ψ emb, ∀ f₁ ∈ M.Pol ψ emb, Acts (evI F) (om (k, 1)) f f₁ →
    ∀ φ : ∀ w : Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ, (∀ w, φ w ∈ SB _) → (∀ᶠ w in Filter.cofinite, φ w = M.vac w) →
      pure f₁ φ - pure f φ ∈ N

  stabFin : ∀ (v : Pl (F := F)), ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N

  stabLie : ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ algD M ψ emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

  stabCpt : ∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N

theorem IsDatum.fun_eq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (AE F E) → Z) (hc : Function.Surjective crd) {Φ : (Fin n × Fin d → AF F) → ℂ} {f f' : Z → ℂ}
    (h : IsDatum M ψ crd Φ f) (h' : IsDatum M ψ crd Φ f') : f = f' := by
  funext z
  obtain ⟨u, rfl⟩ := hc z
  rw [← h.2 u, ← h'.2 u]

end GlobalTheory.SquareAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KapXLine

variable {D : D7}

theorem kapX_mul (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g h : GA D X) :
    kapX X e hJ (g * h) = kapX X e hJ g * kapX X e hJ h := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X (g * h)) =
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X g) *
      Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X h)
  rw [map_mul, map_mul]

theorem kapX_one (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : kapX X e hJ 1 = 1 := by
  apply Subtype.ext
  show Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X 1) = 1
  rw [map_one, map_one]

theorem continuous_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) : Continuous (kapX X e hJ) := by
  have h1 : Continuous (matHom X) := continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (Units.continuous_val.comp h1).matrix_reindex e e
  · exact (Units.continuous_coe_inv.comp h1).matrix_reindex e e

theorem smul_eq_zero_of_finTens {u : AF D.host.F} (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0) {z : AE D}
    (hz : GlobalTheory.LFun.finTens D.host.F D.host.E z = 0) : u • z = 0 := by
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective (hu.trans (map_zero _).symm)
  refine GlobalTheory.LFun.tens_ext ?_ ?_
  · rw [Algebra.smul_def, map_mul, map_zero]
    change (u.1 ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = 0
    rw [hu1, TensorProduct.zero_tmul, zero_mul]
  · rw [Algebra.smul_def, map_mul, map_zero, hz, mul_zero]

theorem kapX_mem_UAt (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) {g : GA D X} (hg : g ∈ GinfC X) :
    kapX X e hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) := by
  intro u hu
  have hf : finHom X g = 1 := hg
  have hent : ∀ a b, GlobalTheory.LFun.finTens D.host.F D.host.E (Formalism.L2.Theta.mt X g a b) =
      (1 : Matrix (Fin X.rank) (Fin X.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    have := congrArg (fun k : GL (Fin X.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf
    exact this
  ext i j
  rw [mat_kapX]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, reindex_apply, submatrix_apply]
  apply smul_eq_zero_of_finTens hu
  rw [map_sub, hent, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : e.symm i ≠ e.symm j := fun k => h (e.symm.injective k)
    simp [h, h']

end GlobalTheory.KapXLine

open GlobalTheory.KapXLine in
theorem GlobalTheory.KapXLine.exists_line : ∀ (D : D7) (θ : InfFam D) (X : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ),
    IsInfFam θ → Y ∈ lieAt X τ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ),
    ∃ γ ∈ Lines D.sp.cm.sig Wd, ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  intro D θ X τ Y hθ hY d e Wd hJ
  let γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J :=
    { toFun := fun t => kapX X e hJ (oneP θ X τ Y (Multiplicative.toAdd t))
      map_one' := by
        show kapX X e hJ (oneP θ X τ Y 0) = 1
        rw [GlobalTheory.Mem.Lift.oneP_zero hθ, kapX_one]
      map_mul' := fun s t => by
        show kapX X e hJ (oneP θ X τ Y (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
        rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, kapX_mul] }
  refine ⟨γ, ⟨?_, fun t => ?_⟩, fun t => rfl⟩
  · exact (continuous_kapX X e hJ).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_toAdd)
  · exact kapX_mem_UAt X e Wd hJ (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY _).1

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAtStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oneParamSubgroup_transposeGram_lieAt : ∀ (D : D7) (θ : InfFam D) (X : HSp D) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ),
    IsInfFam θ → Y ∈ lieAt X τ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ),
    ∃ γ ∈ Lines D.sp.cm.sig Wd, ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  first | exact @GlobalTheory.KapXLine.exists_line | exact GlobalTheory.KapXLine.exists_line | (intros; apply GlobalTheory.KapXLine.exists_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinFLin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.FinFockLin

theorem finF_lin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X),
  IsFinF ψ θ ε A B 0 ∧ (∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g)) ∧
  (∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f)) ∧
  (∀ f g P, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g →
    fockF ψ θ ε A B (f + g) P = fockF ψ θ ε A B f P + fockF ψ θ ε A B g P) ∧
  ∀ (c : ℂ) f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B (c • f) P = c • fockF ψ θ ε A B f P := by
  intro D ψ θ hψ hθ ε M X A B
  have hsm : ∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f) := by
    intro c f hf
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c hf.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z c hf.1, hf.2 τ z, smul_zero]
  have hadd : ∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g) := by
    intro f g hf hg
    refine ⟨GlobalTheory.OrientedHeis.theta_add hf.1 hg.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_add hψ hθ τ _ z hf.1 hg.1, hf.2 τ z, hg.2 τ z, add_zero]
  have h0 : IsFinF ψ θ ε A B 0 := by
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, fun τ z => ?_⟩
    have h := GlobalTheory.FockIndep.annih_smul hψ hθ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ)) z 0
      (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε M) (T := X))
    simpa only [zero_smul] using h
  refine ⟨h0, hadd, hsm, fun f g P hf hg => ?_, fun c f P hf => ?_⟩
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb 1 hf.1 hg.1 P
    rw [one_smul, one_smul] at h
    exact h
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb c hf.1
      h0.1 P
    rw [add_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ _ _ hψ hθ, add_zero] at h
    exact h

end GlobalTheory.FinFockLin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleQuotientsIsoOfIntertwinedSemisimple
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleQuotientsIsoOfIntertwinedSemisimple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

theorem simpleQuot_iso_of_intertwined : ∀ (ι Fm Q Q' Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup Pi] [Module ℂ Pi]
  (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (ρ' : ι → Module.End ℂ Q') (C' : Submodule ℂ Q') (σ : ι → Module.End ℂ Pi)
  (β : Fm → Q →ₗ[ℂ] Pi) (β₁ : Q' →ₗ[ℂ] Pi),
  (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ i, β₁ ∘ₗ ρ' i = σ i ∘ₗ β₁) →
  (∀ f, GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker (β f)) → GlobalTheory.RealQuot.rad ρ' C' ≤ LinearMap.ker β₁ → β₁ ≠ 0 →
  (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Q, GlobalTheory.RealQuot.IsStab ρ N → GlobalTheory.RealQuot.rad ρ C ≤ N → N = GlobalTheory.RealQuot.rad ρ C ∨ N = ⊤) →
  (∀ N : Submodule ℂ Q', GlobalTheory.RealQuot.IsStab ρ' N → GlobalTheory.RealQuot.rad ρ' C' ≤ N → N = GlobalTheory.RealQuot.rad ρ' C' ∨ N = ⊤) →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  ∃ e : (Q ⧸ GlobalTheory.RealQuot.rad ρ C) ≃ₗ[ℂ] (Q' ⧸ GlobalTheory.RealQuot.rad ρ' C'),
    ∀ i, e.toLinearMap ∘ₗ GlobalTheory.RealQuot.radAct ρ C i = GlobalTheory.RealQuot.radAct ρ' C' i ∘ₗ e.toLinearMap := by
  intro ι Fm Q Q' Pi _ _ _ _ _ _ ρ C ρ' C' σ β β₁ hβ hβ₁ hkβ hkβ₁ hβ₁0 hspan hQ hQ' hss
  set R := rad ρ C with hRdef
  set R' := rad ρ' C' with hR'def

  have kerStab : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : ι → Module.End ℂ X) (g : X →ₗ[ℂ] Pi),
      (∀ i, g ∘ₗ τ i = σ i ∘ₗ g) → IsStab τ (LinearMap.ker g) := by
    intro X _ _ τ g hg i x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hg i, LinearMap.comp_apply, hx, map_zero]
  set U := LinearMap.range β₁ with hUdef
  have hUs : IsStab σ U := by
    rintro i _ ⟨x, rfl⟩
    exact ⟨ρ' i x, by rw [← LinearMap.comp_apply, hβ₁ i, LinearMap.comp_apply]⟩

  have hUsimple : ∀ Wm : Submodule ℂ Pi, IsStab σ Wm → Wm ≤ U → Wm ≠ ⊥ → Wm = U := by
    intro Wm hW hWU hW0
    have hcs : IsStab ρ' (Wm.comap β₁) := fun i x hx => by
      show β₁ (ρ' i x) ∈ Wm
      rw [← LinearMap.comp_apply, hβ₁ i, LinearMap.comp_apply]
      exact hW i _ hx
    have hcR : R' ≤ Wm.comap β₁ := fun x hx => by
      show β₁ x ∈ Wm
      rw [LinearMap.mem_ker.1 (hkβ₁ hx)]
      exact Wm.zero_mem
    rcases hQ' _ hcs hcR with h | h
    · exfalso
      apply hW0
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨x, rfl⟩ := hWU hw
      have : x ∈ Wm.comap β₁ := hw
      rw [h] at this
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 (hkβ₁ this))
    · refine le_antisymm hWU ?_
      rintro _ ⟨x, rfl⟩
      have : x ∈ Wm.comap β₁ := h ▸ Submodule.mem_top
      exact this
  obtain ⟨N', hN's, hc⟩ := hss U hUs
  let P : Pi →ₗ[ℂ] Pi := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U N' hc
  have hPU : ∀ y ∈ U, P y = y := fun y hy =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨y, hy⟩)
  have hPN : ∀ y ∈ N', P y = 0 := fun y hy => by
    exact (congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨y, hy⟩) :)
  have hPmem : ∀ y, P y ∈ U := fun y => (Submodule.linearProjOfIsCompl U N' hc y).2
  have hdec : ∀ y : Pi, ∃ u ∈ U, ∃ n ∈ N', y = u + n := by
    intro y
    have : y ∈ U ⊔ N' := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨u, hu, n, hn, h⟩ := Submodule.mem_sup.1 this
    exact ⟨u, hu, n, hn, h.symm⟩
  have hPσ : ∀ i y, P (σ i y) = σ i (P y) := by
    intro i y
    obtain ⟨u, hu, n, hn, rfl⟩ := hdec y
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hPU _ (hUs i u hu), hPN _ (hN's i n hn), hPU u hu, hPN n hn, add_zero, add_zero]

  obtain ⟨f, hf⟩ : ∃ f, P ∘ₗ β f ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle : ∀ f, LinearMap.range (β f) ≤ N' := by
      rintro f _ ⟨x, rfl⟩
      obtain ⟨u, hu, n, hn, he⟩ := hdec (β f x)
      have h0 : P (β f x) = 0 := by rw [← LinearMap.comp_apply, hall f, LinearMap.zero_apply]
      rw [he, map_add (f := _), hPU u hu, hPN n hn, add_zero] at h0
      rw [he, h0, zero_add]; exact hn
    have hN'top : N' = ⊤ := eq_top_iff.2 (hspan ▸ iSup_le hle)
    have hU0 : U = ⊥ := by
      have := hc.inf_eq_bot
      rwa [hN'top, inf_top_eq] at this
    apply hβ₁0
    ext x
    have : β₁ x ∈ U := LinearMap.mem_range_self β₁ x
    rw [hU0, Submodule.mem_bot] at this
    exact this
  set γ := P ∘ₗ β f with hγdef
  have hγi : ∀ i, γ ∘ₗ ρ i = σ i ∘ₗ γ := by
    intro i; ext x
    show P (β f (ρ i x)) = σ i (P (β f x))
    have h := LinearMap.congr_fun (hβ f i) x
    simp only [LinearMap.comp_apply] at h
    rw [h, hPσ]
  have hRγ : R ≤ LinearMap.ker γ := fun x hx => by
    rw [LinearMap.mem_ker, hγdef, LinearMap.comp_apply, LinearMap.mem_ker.1 (hkβ f hx), map_zero]
  have hkerγ : LinearMap.ker γ = R := by
    rcases hQ _ (kerStab ρ γ hγi) hRγ with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf
  have hkerβ₁ : LinearMap.ker β₁ = R' := by
    rcases hQ' _ (kerStab ρ' β₁ hβ₁) hkβ₁ with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hβ₁0
  have hrangeγ : LinearMap.range γ = U := by
    apply hUsimple
    · rintro i _ ⟨x, rfl⟩
      exact ⟨ρ i x, by rw [← LinearMap.comp_apply, hγi i, LinearMap.comp_apply]⟩
    · rintro _ ⟨x, rfl⟩; exact hPmem _
    · intro h
      apply hf
      ext x
      have : γ x ∈ LinearMap.range γ := LinearMap.mem_range_self γ x
      rw [h, Submodule.mem_bot] at this
      exact this
  let φ := R.liftQ γ hRγ
  let ψ := R'.liftQ β₁ hkβ₁
  have hφi : Function.Injective φ := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hkerγ.le)
  have hψi : Function.Injective ψ := LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hkerβ₁.le)
  have hrφ : LinearMap.range φ = LinearMap.range ψ := by
    rw [Submodule.range_liftQ, Submodule.range_liftQ, hrangeγ]
  let e : (Q ⧸ R) ≃ₗ[ℂ] (Q' ⧸ R') :=
    (LinearEquiv.ofInjective φ hφi).trans ((LinearEquiv.ofEq _ _ hrφ).trans (LinearEquiv.ofInjective ψ hψi).symm)
  have he : ∀ x, ψ (e x) = φ x := by
    intro x
    have h1 := LinearEquiv.ofInjective_apply (f := ψ) (h := hψi)
      ((LinearEquiv.ofInjective ψ hψi).symm ((LinearEquiv.ofEq _ _ hrφ) (LinearEquiv.ofInjective φ hφi x)))
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨e, fun i => ?_⟩
  apply Submodule.linearMap_qext
  ext q
  apply hψi
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe]
  rw [he, radAct_mk]
  obtain ⟨q', hq'⟩ := Submodule.Quotient.mk_surjective R' (e (Submodule.Quotient.mk q))
  rw [← hq', radAct_mk]
  have h2 := he (Submodule.Quotient.mk q)
  rw [← hq'] at h2
  simp only [φ, ψ, Submodule.liftQ_apply] at h2 ⊢
  have hb := LinearMap.congr_fun (hβ₁ i) q'
  have hg := LinearMap.congr_fun (hγi i) q
  simp only [LinearMap.comp_apply] at hb hg
  rw [hb, h2]
  exact hg

end GlobalTheory.RealQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleQuotientsIsoOfIntertwinedSemisimpleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_quotients_iso_of_intertwined_semisimple : ∀ (ι Fm Q Q' Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup Pi] [Module ℂ Pi]
  (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (ρ' : ι → Module.End ℂ Q') (C' : Submodule ℂ Q') (σ : ι → Module.End ℂ Pi)
  (β : Fm → Q →ₗ[ℂ] Pi) (β₁ : Q' →ₗ[ℂ] Pi),
  (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ i, β₁ ∘ₗ ρ' i = σ i ∘ₗ β₁) →
  (∀ f, GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker (β f)) → GlobalTheory.RealQuot.rad ρ' C' ≤ LinearMap.ker β₁ → β₁ ≠ 0 →
  (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Q, GlobalTheory.RealQuot.IsStab ρ N → GlobalTheory.RealQuot.rad ρ C ≤ N → N = GlobalTheory.RealQuot.rad ρ C ∨ N = ⊤) →
  (∀ N : Submodule ℂ Q', GlobalTheory.RealQuot.IsStab ρ' N → GlobalTheory.RealQuot.rad ρ' C' ≤ N → N = GlobalTheory.RealQuot.rad ρ' C' ∨ N = ⊤) →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  ∃ e : (Q ⧸ GlobalTheory.RealQuot.rad ρ C) ≃ₗ[ℂ] (Q' ⧸ GlobalTheory.RealQuot.rad ρ' C'),
    ∀ i, e.toLinearMap ∘ₗ GlobalTheory.RealQuot.radAct ρ C i = GlobalTheory.RealQuot.radAct ρ' C' i ∘ₗ e.toLinearMap := by
  first | exact @GlobalTheory.RealQuot.simpleQuot_iso_of_intertwined | exact GlobalTheory.RealQuot.simpleQuot_iso_of_intertwined | (intros; apply GlobalTheory.RealQuot.simpleQuot_iso_of_intertwined <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableComplementOfIrreducibleSpanIntertwin
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableComplementOfIrreducibleSpanIntertwin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.RealQuot.SemisimpleSpan

open GlobalTheory.RealQuot

theorem isStab_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] {σ : ι → Module.End ℂ M}
    (W : κ → Submodule ℂ M) (h : ∀ k, IsStab σ (W k)) : IsStab σ (⨆ k, W k) := by
  intro i
  have hle : (⨆ k, W k) ≤ (⨆ k, W k).comap (σ i) :=
    iSup_le fun k x hx => Submodule.mem_iSup_of_mem k (h k i x hx)
  exact fun x hx => hle hx

theorem exists_stab_compl_of_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] (σ : ι → Module.End ℂ M)
    (W : κ → Submodule ℂ M) (hW : ∀ k, IsStab σ (W k))
    (hs : ∀ k (V : Submodule ℂ M), IsStab σ V → V ≤ W k → V = ⊥ ∨ V = W k) (htop : ⨆ k, W k = ⊤) :
    ∀ N : Submodule ℂ M, IsStab σ N → ∃ N' : Submodule ℂ M, IsStab σ N' ∧ IsCompl N N' := by
  letI : Module (FreeAlgebra ℂ ι) M :=
    Module.compHom M (FreeAlgebra.lift ℂ σ : FreeAlgebra ℂ ι →ₐ[ℂ] Module.End ℂ M).toRingHom
  have smul_def : ∀ (a : FreeAlgebra ℂ ι) (x : M), a • x = FreeAlgebra.lift ℂ σ a x := fun _ _ => rfl
  haveI : IsScalarTower ℂ (FreeAlgebra ℂ ι) M := ⟨fun c a x => by
    rw [smul_def, smul_def, map_smul]
    rfl⟩
  have key : ∀ N : Submodule ℂ M, IsStab σ N →
      ∃ W' : Submodule (FreeAlgebra ℂ ι) M, W'.restrictScalars ℂ = N := by
    intro N hN
    have hst : ∀ a : FreeAlgebra ℂ ι, ∀ x ∈ N, FreeAlgebra.lift ℂ σ a x ∈ N := by
      intro a
      induction a using FreeAlgebra.induction with
      | grade0 r =>
        intro x hx
        rw [AlgHom.commutes, Module.algebraMap_end_apply]
        exact N.smul_mem r hx
      | grade1 i =>
        intro x hx
        rw [FreeAlgebra.lift_ι_apply]
        exact hN i x hx
      | mul a b ha hb =>
        intro x hx
        rw [map_mul, Module.End.mul_apply]
        exact ha _ (hb x hx)
      | add a b ha hb =>
        intro x hx
        rw [map_add (f := _), LinearMap.add_apply]
        exact N.add_mem (ha x hx) (hb x hx)
    refine ⟨{ carrier := N
              add_mem' := N.add_mem
              zero_mem' := N.zero_mem
              smul_mem' := fun a x hx => hst a x hx }, ?_⟩
    ext x
    rfl
  have stabR : ∀ W' : Submodule (FreeAlgebra ℂ ι) M, IsStab σ (W'.restrictScalars ℂ) := by
    intro W' i x hx
    have : σ i x = (FreeAlgebra.ι ℂ i) • x := by rw [smul_def, FreeAlgebra.lift_ι_apply]
    rw [this]
    exact W'.smul_mem _ hx
  have hss : IsSemisimpleModule (FreeAlgebra ℂ ι) M := by
    rw [← sSup_simples_eq_top_iff_isSemisimpleModule, ← Submodule.restrictScalars_eq_top_iff ℂ,
      eq_top_iff, ← htop]
    refine iSup_le fun k => ?_
    obtain ⟨Wk, hWk⟩ := key (W k) (hW k)
    rw [← hWk]
    refine Submodule.restrictScalars_mono ℂ ?_
    by_cases h0 : Wk = ⊥
    · rw [h0]
      exact bot_le
    · refine le_sSup (isSimpleModule_iff_isAtom.2 ⟨h0, fun V hV => ?_⟩)
      rcases hs k (V.restrictScalars ℂ) (stabR V) (hWk ▸ Submodule.restrictScalars_mono ℂ hV.le) with h | h
      · exact (Submodule.restrictScalars_eq_bot_iff ℂ _ _).1 h
      · exact absurd ((Submodule.restrictScalars_injective ℂ _ _) (h.trans hWk.symm)) hV.ne
  intro N hN
  obtain ⟨WN, hWN⟩ := key N hN
  obtain ⟨W', hc⟩ := exists_isCompl WN
  refine ⟨W'.restrictScalars ℂ, stabR W', ⟨?_, ?_⟩⟩
  · rw [disjoint_iff, ← hWN, ← Submodule.restrictScalars_inf, hc.inf_eq_bot]
    rfl
  · rw [codisjoint_iff, ← hWN, ← Submodule.restrictScalars_sup, hc.sup_eq_top]
    rfl

theorem exists_stab_compl : ∀ (ι J Fm Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (τ : J → Module.End ℂ Pi) (β : Fm → Q →ₗ[ℂ] Pi),
  GlobalTheory.RealQuot.HoweCond ρ C → (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ f, C ≤ LinearMap.ker (β f)) →
  (∀ j f, ∃ f', τ j ∘ₗ β f = β f') → (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → GlobalTheory.RealQuot.IsStab τ N → N = ⊥ ∨ N = ⊤) →
  ∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N' := by
  intro ι J Fm Q Pi _ _ _ _ ρ C σ τ β hH hint hker hτ hspan hirr
  obtain ⟨⟨L, hL⟩, -⟩ := hH
  have hcomm : ∀ f i x, β f (ρ i x) = σ i (β f x) := fun f i x => by
    rw [← LinearMap.comp_apply (β f) (ρ i), hint f i, LinearMap.comp_apply]
  let K : Submodule ℂ Q := ⨅ f, LinearMap.ker (β f)
  have hKf : ∀ f, K ≤ LinearMap.ker (β f) := fun f => iInf_le _ f
  have hKs : IsStab ρ K := by
    intro i x hx
    refine Submodule.mem_iInf _ |>.2 fun f => ?_
    rw [LinearMap.mem_ker, hcomm, LinearMap.mem_ker.1 (hKf f hx), map_zero]
  have hCK : C ≤ K := le_iInf hker

  have hmapS : ∀ S : Submodule ℂ Q, IsStab ρ S → ∀ f, IsStab σ (S.map (β f)) := by
    rintro S hS f i _ ⟨x, hx, rfl⟩
    exact ⟨ρ i x, hS i x hx, hcomm f i x⟩
  have hNS : ∀ S : Submodule ℂ Q, IsStab ρ S → (⨆ f, S.map (β f)) = ⊥ ∨ (⨆ f, S.map (β f)) = ⊤ := by
    intro S hS
    refine hirr _ (isStab_iSup _ (hmapS S hS)) ?_
    intro j
    have hle : (⨆ f, S.map (β f)) ≤ (⨆ f, S.map (β f)).comap (τ j) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨f', hf'⟩ := hτ j f
      show τ j (β f x) ∈ ⨆ f, S.map (β f)
      rw [← LinearMap.comp_apply, hf']
      exact Submodule.mem_iSup_of_mem f' ⟨x, hx, rfl⟩
    exact fun x hx => hle hx

  obtain ⟨S, hSst, hStop, hsimp⟩ : ∃ S : Submodule ℂ Q, IsStab ρ S ∧ (⨆ f, S.map (β f)) = ⊤ ∧
      ∀ f (V : Submodule ℂ Pi), IsStab σ V → V ≤ S.map (β f) → V = ⊥ ∨ V = S.map (β f) := by
    by_cases hK : K = ⊤
    · refine ⟨⊤, fun i x _ => Submodule.mem_top, by simpa [Submodule.map_top] using hspan, fun f V _ hV => Or.inl ?_⟩
      have h0 : (⊤ : Submodule ℂ Q).map (β f) = ⊥ := by
        rw [Submodule.map_top, LinearMap.range_eq_bot]
        exact LinearMap.ker_eq_top.1 (top_le_iff.1 (hK ▸ hKf f))
      exact le_bot_iff.1 (h0 ▸ hV)
    · let T : Type := {S : Submodule ℂ Q // IsStab ρ S ∧ C ≤ S}
      have wf : WellFounded (fun x y : T => x.1 < y.1) := by
        refine ⟨fun x => ?_⟩
        by_contra hx
        obtain ⟨g, -, hg⟩ := not_acc_iff_exists_descending_chain.1 hx
        have anti : StrictAnti fun n => (g n).1 := strictAnti_nat_of_succ_lt hg
        have mono : StrictMono fun k : Fin (L + 1) => (g (L - k.1)).1 := by
          intro a b hab
          exact anti (by have := a.2; have := b.2; simp only [Fin.lt_def] at hab; omega)
        have := hL (L + 1) _ mono fun k => (g (L - k.1)).2
        omega
      obtain ⟨M, hMK0, hMmin⟩ := wf.has_min {x : T | K < x.1}
        ⟨⟨⊤, fun i x _ => Submodule.mem_top, le_top⟩, lt_top_iff_ne_top.2 hK⟩
      have hMK : K < M.1 := hMK0
      refine ⟨M.1, M.2.1, ?_, ?_⟩
      · rcases hNS M.1 M.2.1 with h | h
        · exfalso
          refine hMK.2 (le_iInf fun f => ?_)
          intro x hx
          have h1 : β f x ∈ M.1.map (β f) := Submodule.mem_map_of_mem hx
          rw [iSup_eq_bot.1 h f] at h1
          exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h1)
        · exact h
      · intro f V hVs hV
        let U : Submodule ℂ Q := M.1 ⊓ V.comap (β f)
        have hUs : IsStab ρ U := by
          rintro i x ⟨hx1, hx2⟩
          refine ⟨M.2.1 i x hx1, ?_⟩
          show β f (ρ i x) ∈ V
          rw [hcomm]
          exact hVs i _ hx2
        have hKU : K ≤ U := fun x hx => ⟨hMK.le hx, by
          show β f x ∈ V
          rw [LinearMap.mem_ker.1 (hKf f hx)]
          exact V.zero_mem⟩
        by_cases hlt : K < U
        · right
          have hUM : U = M.1 := by
            by_contra hne
            exact hMmin ⟨U, hUs, hCK.trans hKU⟩ hlt (lt_of_le_of_ne inf_le_left hne)
          refine le_antisymm hV ?_
          rintro _ ⟨x, hx, rfl⟩
          have : x ∈ U := hUM ▸ hx
          exact this.2
        · left
          have hUK : U = K := (eq_of_le_of_not_lt hKU hlt).symm
          rw [eq_bot_iff]
          intro v hv
          obtain ⟨x, hx, rfl⟩ := hV hv
          have : x ∈ U := ⟨hx, hv⟩
          rw [hUK] at this
          exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 (hKf f this))
  exact exists_stab_compl_of_iSup σ (fun f => S.map (β f)) (hmapS S hSst) hsimp hStop

end GlobalTheory.RealQuot.SemisimpleSpan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableComplementOfIrreducibleSpanIntertwinStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners : ∀ (ι J Fm Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (τ : J → Module.End ℂ Pi) (β : Fm → Q →ₗ[ℂ] Pi),
  GlobalTheory.RealQuot.HoweCond ρ C → (∀ f i, β f ∘ₗ ρ i = σ i ∘ₗ β f) → (∀ f, C ≤ LinearMap.ker (β f)) →
  (∀ j f, ∃ f', τ j ∘ₗ β f = β f') → (⨆ f, LinearMap.range (β f)) = ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → GlobalTheory.RealQuot.IsStab τ N → N = ⊥ ∨ N = ⊤) →
  ∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N' := by
  first | exact @GlobalTheory.RealQuot.SemisimpleSpan.exists_stab_compl | exact GlobalTheory.RealQuot.SemisimpleSpan.exists_stab_compl | (intros; apply GlobalTheory.RealQuot.SemisimpleSpan.exists_stab_compl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def algAt (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ SB _) ∧ (∀ v ∉ T, φ v = M.vac v) ∧ Φ = pure f φ}

variable (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)

theorem algAt_mono {T T' : Finset (Pl F)} (h : T ⊆ T') : algAt M ψ emb T ≤ algAt M ψ emb T' := by
  refine Submodule.span_mono ?_
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨f, φ, hf, hφ, fun v hv' => hv v fun h' => hv' (h h'), rfl⟩

theorem exists_algAt {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb)
    (T₀ : Finset (Pl F)) : ∃ T, T₀ ⊆ T ∧ Φ ∈ algAt M ψ emb T := by
  classical
  induction hΦ using Submodule.span_induction generalizing T₀ with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hco, rfl⟩ := hx
    have hfin : {v | ¬ φ v = M.vac v}.Finite := Filter.eventually_cofinite.1 hco
    refine ⟨T₀ ∪ hfin.toFinset, Finset.subset_union_left, Submodule.subset_span ⟨f, φ, hf, hφ, fun v hv => ?_, rfl⟩⟩
    by_contra hne
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hne))
  | zero => exact ⟨T₀, subset_rfl, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    obtain ⟨T₂, h₂, hy₂⟩ := hy T₁
    exact ⟨T₂, h₁.trans h₂, add_mem (algAt_mono M ψ emb h₂ hx₁) hy₂⟩
  | smul c x _ hx =>
    obtain ⟨T₁, h₁, hx₁⟩ := hx T₀
    exact ⟨T₁, h₁, Submodule.smul_mem _ c hx₁⟩

end GlobalTheory.HoweGlobal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.HeisOrbit

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def archCo {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (d : GlobalTheory.WeilM.Darboux B κ) (w : W) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (fun i => evI F ((d.e w).1 i), fun i => evI F ((d.e w).2 i))

def dOp (P Q : κ → mixedEmbedding.mixedSpace F) (h : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  fderiv ℝ h y P - 2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q i) : ℝ) : ℂ) * h y

end GlobalTheory.HeisOrbit
end
end
