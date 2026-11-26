module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

open Formalism.UG GlobalTheory.PRep GlobalTheory.LGrp GlobalTheory.LFun

def TrivialBound (q n : ℕ) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∀ i, ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2)

def SatakeBoundInert : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GU σ n) V) (α : Fin (n / 2) → ℂˣ),
      IsIrrSmooth π → IsUnitarisable π → HasSatU ϖ q π α → TrivialBound q n α

theorem bound_eq (q n : ℕ) : ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) = (q : ℝ) ^ ((n : ℝ) - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1
  push_cast
  ring

def trivParam (q n : ℕ) (hq : q ≠ 0) : Fin (n / 2) → ℂˣ :=
  fun i => Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem trivial_hyp {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {ϖ : L}
    {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    IsIrrSmooth (charRep (1 : GU σ n →* ℂˣ)) ∧ IsUnitarisable (charRep (1 : GU σ n →* ℂˣ)) ∧
      HasSatU ϖ q (charRep (1 : GU σ n →* ℂˣ)) (trivParam q n hq) := by
  have hc : ∀ b : GU σ n, chiDeltaU q (fun i => (trivParam q n hq i : ℂ)) b = 1 := fun b => by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs with h
    · simp only [trivParam, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero (q : ℂ) using 2
      ring
    · rfl
  refine ⟨⟨fun z => by simp, charRep_irreducible _⟩, charRep_unitarisable _ (by simp), ?_, fun x _ h0 => ?_⟩
  · exact (Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 (by simp), one_ne_zero⟩
  · refine IsSatVecU.of_map hU (ρ' := rightReg ℂ _ ℂ) (LinearMap.pi fun _ => LinearMap.id)
      (fun g y => by funext z; simp [rightReg, LinearMap.funLeft]) (fun a b e => congrFun e 1)
      (isSatVecU_of_isSphericalU hU (fun b g k _ _ => by simp [hc]) fun e => h0 (congrFun e 1))

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def sgn (e : Bool) : ℂ := if e then 1 else -1

def idx {n : ℕ} (ε : Fin n → Bool) : ℚ := ∑ a, if ε a then (1 : ℚ) else -1

def wtS {b : ℕ} (ε' : Fin b → Bool) (aT : ℚ) (e : Bool) : ℚ := (if e then -(idx ε' / 2) else idx ε' / 2) - aT

def wtT {a : ℕ} (ε : Fin a → Bool) (aS : ℚ) (e : Bool) : ℚ := (if e then idx ε / 2 else -(idx ε / 2)) + aS

def signBlockDeterminant {n : ℕ} (ε : Fin n → Bool) (e : Bool) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (g.submatrix (Subtype.val : {a // ε a = e} → Fin n) (Subtype.val : {a // ε a = e} → Fin n)).det

def elt {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)

section Fock

variable {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def raiO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j))
    else -(MvPolynomial.pderiv (τ, i, j)).toLinearMap)

def lowO (i : Fin b) (j : Fin a) : Module.End ℂ (PolF D b a) := by
  classical
  exact sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (τ, i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j)))

def fockS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (raiO τ ε ε' i j * lowO τ ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def fockT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (PolF D b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (raiO τ ε ε' i j * lowO τ ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def subst (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) : PolF D b a →ₐ[ℂ] PolF D b a := by
  classical
  exact MvPolynomial.aeval fun v : FVar D b a =>
    if v.1 = τ then
      ∑ l, ∑ m, (if ε' v.2.1 = ε v.2.2 then k l v.2.1 * g m v.2.2 else star (k l v.2.1 * g m v.2.2)) •
        MvPolynomial.X (τ, l, m)
    else MvPolynomial.X v

end Fock

section Clauses

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
  (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
  (τ : D.what₂.Tau) (aS aT : ℚ)

def TorusVac : Prop :=
  ∀ (t : Fin V.rank → ℝ) (t' : Fin W.rank → ℝ),
    ω (elt θ M τ (diagonal fun j => Complex.exp (Complex.I * t j)),
        elt θ M' τ (diagonal fun i => Complex.exp (Complex.I * t' i))) f =
      Complex.exp (Complex.I * (∑ j, (wtS (M'.ε τ) aT (M.ε τ j) : ℂ) * t j +
        ∑ i, (wtT (M.ε τ) aS (M'.ε τ i) : ℂ) * t' i)) • f

def CompactFock : Prop :=
  ∃ x y : Bool → ℤ, (∀ j, (x (M.ε τ j) : ℚ) = wtS (M'.ε τ) aT (M.ε τ j)) ∧
    (∀ i, (y (M'.ε τ i) : ℚ) = wtT (M.ε τ) aS (M'.ε τ i)) ∧
    ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ k ∈ Formalism.REAL.Kset (M'.ε τ), ∀ P : PolF D W.rank V.rank,
      ω (elt θ M τ h, elt θ M' τ k) (ptOf ψ θ M M' f P) =
        (signBlockDeterminant (M.ε τ) true h ^ x true * signBlockDeterminant (M.ε τ) false h ^ x false *
          (signBlockDeterminant (M'.ε τ) true k ^ y true * signBlockDeterminant (M'.ε τ) false k ^ y false)) •
          ptOf ψ θ M M' f (subst τ (M.ε τ) (M'.ε τ) (h.map (starRingEnd ℂ)) k P)

def LieFock : Prop :=
  (∀ X ∈ lieAt V τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P -
        ((aT : ℂ) * X.trace) • P) z) 0) ∧
  ∀ Y ∈ lieAt W τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptOf ψ θ M M' f P) z)
      (ptOf ψ θ M M' f (fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P +
        ((aS : ℂ) * Y.trace) • P) z) 0

end Clauses

def VacChar (D : D7) : Prop :=
  ∀ (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacVec ψ θ M M' f →
      TorusVac θ M M' ω f τ aS aT ∧ CompactFock ψ θ M M' ω f τ aS aT ∧ LieFock ψ θ M M' ω f τ aS aT

end GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift Formalism.IndefR.Links
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 D.host.E) ∉ w.asIdeal ^ 2

def PsiUnramAt (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ α : Af D.host.F, (∀ v', v' ≠ v → evalV D.host.F v' α = 0) →
    ((∀ β ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * β)) = 1) ↔
      evalV D.host.F v α ∈ v.adicCompletionIntegers D.host.F)

def SideCond (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  IsSplit (E := D.host.E) v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal ∧ PsiUnramAt ψ v ∧
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → w.valuation D.host.E D.host.xi0 = 1

def excluded (q t : ℕ) : Set ℂ :=
  {(((q : ℝ) ^ (((t : ℝ) - 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) - 1) / 2)) : ℝ) : ℂ),
    (((q : ℝ) ^ (((t : ℝ) + 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ)}

section Cusp

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]

variable {V ν} {W : Submodule ℂ (DividedPowerChartLift V ν)}


end Cusp

section Chain

variable (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
  (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ)
  (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
  (𝓕 : ∀ k, Set (GA D (Yc D k))) (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0)))

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Mult Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SignCompat {p q n : ℕ} (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) : Prop := ∀ a, ε (e a) = a.isLeft

def plainMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ := Matrix.reindex e e g

def barMat {p q n : ℕ} (e : Ix p q ≃ Fin n) (g : Mat p q) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (g.map (starRingEnd ℂ))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def toFrame (M : DSModel V S) (τ : D.what₂.Tau) (Y : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹ * Y * M.fr τ


open Classical in
structure Matches {p q : ℕ} {T : GrpData p q} (R : DSRep T) (M : DSModel V S) (τ : D.what₂.Tau)
    (φ : Mat p q → Matrix (Fin V.rank) (Fin V.rank) ℂ) (m : ℤ) (U : M.H τ → R.U.H) : Prop where

  grp : ∀ (g : T.G) (x : M.H τ),
    R.U.π g (U x) = ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (M.σ τ (φ ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)

  kfin : ∀ x : M.H τ, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x ↔ U x ∈ Set.range R.ι

  smooth : ∀ x : M.H τ, U x ∈ Set.range R.ι → SmoothVec (lieAt V τ) (M.rep τ) x

  lie : (fun Z => toFrame M τ (φ Z)) '' upq p q = lieAt V τ

  der : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.H τ), U x = R.ι v →
    U (dRep (M.rep τ) (toFrame M τ (φ Z)) x) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v)

  derT : ∀ Z ∈ upq p q, ∀ (v : R.HK.V) (x : M.Vec) (y : M.sm τ), U (x τ : M.H τ) = R.ι v →
    U (y : M.H τ) = R.ι (R.HK.act Z v + ((m : ℂ) / 2 * Z.trace) • v) →
    DerT M τ (toFrame M τ (φ Z)) (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ (Function.update x τ y))

def HidaSetting (X : ProvA) (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (S : D.what₂.Tau → SPar) (τ : D.what₂.Tau) : Prop :=
  1 ≤ p + q ∧ l₁.length = p ∧ l₂.length = q ∧ IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) ∧
    HasParam (X.ds p q (ofBlocks l₁ l₂)) (ofBlocks l₁ l₂) ∧ S τ = dualPar (GlobalTheory.Chain.signed l₁ l₂ c)

def SourceBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X p q l₁ l₂ c S τ →
    (∃ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ[ℂ] (X.ds p q (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds p q (ofBlocks l₁ l₂)) M τ (barMat e) m U

def TargetBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (τ : D.what₂.Tau)
    (r s : ℕ) (l₁ l₂ : List ℚ) (c : ℚ), HidaSetting X r s l₁ l₂ c S τ →
    (∃ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e) ∧
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix r s ≃ Fin W.rank, SignCompat (M.ε τ) e →
      ∃ U : M.H τ ≃ₗᵢ⋆[ℂ] (X.ds r s (ofBlocks l₁ l₂)).U.H,
        Matches (X.ds r s (ofBlocks l₁ l₂)) M τ (plainMat e) m U

def ModelsAreCoverSeries (D : D7) : Prop := SourceBridge D ∧ TargetBridge D

theorem reindex_form {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq p q) = Formalism.REAL.Jm ε := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  have ha := h a
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp_all

theorem plainMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : plainMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  change (plainMat e g)ᴴ * Formalism.REAL.Jm ε * plainMat e g = Formalism.REAL.Jm ε
  rw [← reindex_form h]
  simp only [plainMat, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]

theorem barMat_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) {g : Mat p q}
    (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q) : barMat e g ∈ Formalism.MainNotions.S.UJset ε := by
  refine plainMat_mem h ?_
  have hJ : (Formalism.UG.Jpq p q).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp [Formalism.UG.Jpq, Matrix.one_apply] <;> split_ifs <;> simp
  have h1 := congrArg (fun A : Mat p q => A.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h1
  exact h1

end GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Filter GlobalTheory.LFun

section Defs

variable {K : Type} [Field K] [NumberField K]

def liftFam (c : Fam K) (m x : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) : Fam K :=
  twist c (x * m⁻¹) + segFam x t

def IsZetaCont (T : Set (HeightOneSpectrum (𝓞 K))) (Z : ℂ → ℂ) : Prop :=
  MeromorphicOn Z Set.univ ∧ ∀ s : ℂ, 1 < s.re → Z s = zetaOff T s

def HasSimplePole (Λ : ℂ → ℂ) (s₀ : ℂ) : Prop :=
  MeromorphicAt Λ s₀ ∧ meromorphicOrderAt Λ s₀ = ((-1 : ℤ) : WithTop ℤ) ∧
    ∃ ρ : ℂ, ρ ≠ 0 ∧ Tendsto (fun s => (s - s₀) * Λ s) (𝓝[≠] s₀) (𝓝 ρ)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rhs (S : Set (HeightOneSpectrum (𝓞 F))) (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ)
    (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)

def Hyp (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) : Prop :=
  S.Finite ∧ r + 5 ≤ t ∧
    ∀ w ∉ above E S, (c w).card = r ∧
      (∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧
      ‖(m w : ℂ)‖ = 1 ∧ ‖(x w : ℂ)‖ = 1 ∧ P w = liftFam c m x t w

def Concl (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) :
    Prop :=
  (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re →
    Converges (above E S) (twist P x⁻¹) s ∧
      (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧
      LSTw S P x s = rhs S c m t (zetaOff (above E S)) s) ∧
  ((∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧
    DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re}) ∧
  (∃ Z, IsZetaCont (above E S) Z) ∧
  ∀ Z, IsZetaCont (above E S) Z →
    MeromorphicOn (rhs S c m t Z) {s | ((r : ℝ) + 1) / 2 < s.re} ∧
      ((r : ℝ) + 1) / 2 < ((1 + (t : ℂ)) / 2).re ∧
      (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → rhs S c m t Z s = LSTw S P x s) ∧
      HasSimplePole (rhs S c m t Z) ((1 + (t : ℂ)) / 2)

def SimplePole : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ),
    Hyp S r t c P m x → Concl S r t c P m x

section Rep

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU

end Rep

theorem twist_liftFam (c : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ) :
    twist (liftFam c m x t) x⁻¹ = twist c m⁻¹ + segFam 1 t := by
  rw [liftFam, twist_add, twist_twist, twist_segFam, inv_mul_cancel_left, inv_mul_cancel]

end GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def signCard (S : SPar) (b : Bool) : ℕ := (S.filter fun x => x.2 = b).card

def SigLowered (S : D.what₂.Tau → SPar) (i : ℕ) (V' : HSp D) : Prop :=
  ∀ τ, ∃ p' q' : ℕ, p' + i = signCard (S τ) true ∧ q' + i = signCard (S τ) false ∧
    Formalism.UG.HasSignature (gramAt D V' τ) p' q'

def LowVanish (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (f' : WO V' W → ℂ),
      IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) = 0

theorem signCard_dualPar (S : SPar) (b : Bool) : signCard (dualPar S) b = signCard S b := by
  unfold signCard dualPar
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro x y h
  simp only [Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.1 h.2

end GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HolomorphicLowestType
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT

namespace GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def LowIrr (M : DSModel V S) : Prop :=
  ∀ τ, IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (lowKSub (M.ε τ) (M.lam τ) (M.σ τ))

end Model

section Base

variable {D : D7}

abbrev pW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).1

abbrev qW (i : Fin D.R.m) (τ : D.what₂.Tau) : ℕ := ((Wc D i).sig (tauE D τ)).2

theorem pW_add_qW (i : Fin D.R.m) (τ : D.what₂.Tau) : pW i τ + qW i τ = (Wc D i).rank :=
  sig_sum _ (D.sp.W_sig _) _

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


end Base

end GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LabelSettingScalars
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ


open Classical in
def badPl (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

def rowPart (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : EigSys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) Sb c ⊓ R.EEat R.triv

def IsLValue (t : T) (B : GlobalTheory.LFun.Fam D.host.E) (j : ℕ) (l : ℝ) : Prop :=
  GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))))
               (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (R.toLevCh.mu t j))⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧
    0 < l ∧ GlobalTheory.LFun.LSD D (badPl R t) B (R.toLevCh.mu t j) ((1 + (D.R.t : ℂ)) / 2) = (l : ℂ)

def IsIP (t : T) (k : ℕ) (u u' : MMap (R.MY k)) (a : ℂ) : Prop :=
  IsMultIP (R.MY k) (R.νY t k) (R.fdY t k) u u' a

def IsUp (t : T) (k : ℕ) (u : MMap (R.MY k)) (x : MMap (R.MY (k + 1))) : Prop :=
  PiTensorProduct.lift x ∈ R.CC t (k + 1) ∧ ∀ y : R.CC t (k + 1), ∃ a : ℂ,
    IsIP R t (k + 1) x (PiTensorProduct.lift.symm y.1) a ∧ IsIP R t k u (PiTensorProduct.lift.symm (R.ioY t k y).1) a

def topStep (t : T) (y : (R.HX t).H) : MMap (R.MY (D.R.m - 1)) :=
  PiTensorProduct.lift.symm (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1

def IsUpTop (t : T) (u : MMap (R.MY (D.R.m - 1))) (x : (R.HX t).H) : Prop :=
  ∀ y : (R.HX t).H, IsIP R t (D.R.m - 1) u (topStep R t y) ⟪x, y⟫_ℂ

def reached (t : T) (c : EigSys D) (k : ℕ) : Set (MMap (R.MY k)) :=
  Nat.rec (motive := fun k => Set (MMap (R.MY k))) (rowPart R (badPl R t) c : Set (MMap (R.MY 0)))
    (fun k P => {x | ∃ u ∈ P, IsUp R t k u x}) k

theorem reached_zero (t : T) (c : EigSys D) : reached R t c 0 = (rowPart R (badPl R t) c : Set (MMap (R.MY 0))) := rfl

theorem reached_succ (t : T) (c : EigSys D) (k : ℕ) :
    reached R t c (k + 1) = {x | ∃ u ∈ reached R t c k, IsUp R t k u x} := rfl

def StepScalar (t : T) (c : EigSys D) (k : ℕ) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c k, ∃ x, IsUp R t k u x) ∧
  ∀ u₁ ∈ reached R t c k, ∀ u₂ ∈ reached R t c k, ∀ x₁ x₂, IsUp R t k u₁ x₁ → IsUp R t k u₂ x₂ →
    ∃ a : ℂ, IsIP R t k u₁ u₂ a ∧ IsIP R t (k + 1) x₁ x₂ ((Λ : ℂ) * a)

def TopScalar (t : T) (c : EigSys D) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c (D.R.m - 1), ∃ x, IsUpTop R t u x) ∧
  ∀ u₁ ∈ reached R t c (D.R.m - 1), ∀ u₂ ∈ reached R t c (D.R.m - 1), ∀ x₁ x₂, IsUpTop R t u₁ x₁ → IsUpTop R t u₂ x₂ →
    ∃ a : ℂ, IsIP R t (D.R.m - 1) u₁ u₂ a ∧ ⟪x₁, x₂⟫_ℂ = (Λ : ℂ) * a

def ScalarsWith (κ : ℕ → ℝ) : Prop :=
  ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ →
    (∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B) ∧
    ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
      (∀ k, k + 1 < D.R.m → ∃ l, IsLValue R t B (k + 1) l ∧ StepScalar R t c k (κ (k + 1) * l)) ∧
      ∃ l, IsLValue R t B D.R.m l ∧ TopScalar R t c (κ D.R.m * l)

def Scalars : Prop := ∃ κ : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < κ j) ∧ ScalarsWith R κ

theorem rowPart_mono {Sb Sb' : Finset (HeightOneSpectrum (𝓞 D.host.F))} (h : Sb ⊆ Sb') (c : EigSys D) :
    rowPart R Sb c ≤ rowPart R Sb' c := by
  refine inf_le_inf_right _ fun u hu => ?_
  rw [partDual, mem_partFull] at hu ⊢
  refine ⟨hu.1, fun P d Rp hR => hu.2 P d Rp ?_⟩
  obtain ⟨e, f, ϖ, α, h1, h2⟩ := hR
  exact ⟨e, f, ϖ, α, fun v hv => h1 v (h hv), h2⟩

theorem IsLValue.unique {R : RealDat D A Ks} {t : T} {B : GlobalTheory.LFun.Fam D.host.E} {j : ℕ} {l l' : ℝ}
    (h : IsLValue R t B j l) (h' : IsLValue R t B j l') : l = l' := by
  exact_mod_cast h.2.2.symm.trans h'.2.2

end GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ContractionTensorModels
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

def IsIsoBilin (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ x x' y y', ⟪Tm x y, Tm x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ

def IsEquivBilin {G₁ G₂ : Type} [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Prop :=
  ∀ g h x y, Tm (π₁ g x) (π₂ h y) = ρ (g, h) (Tm x y)

def IsContr (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) (It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁) : Prop :=
  ∀ φ y x, ⟪x, It φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ

def HasWeakDer {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (c : ℝ → H) (v' : H) : Prop :=
  ∀ w : H, HasDerivAt (fun t : ℝ => ⟪w, c t⟫_ℂ) ⟪w, v'⟫_ℂ 0

def IsFiniteVec {G H : Type} [Group G] [AddCommGroup H] [Module ℂ H] (K : Subgroup G) (π : G → H → H) (v : H) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => π k v))

def imSpan (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF) : Submodule ℂ FF :=
  Submodule.span ℂ (Set.range fun p : H₁ × H₂ => Tm p.1 p.2)

structure ContrProps {G₁ G₂ : Type} [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁))
    (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂)) (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF)
    (It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁) : Prop where

  norm_le : ∀ φ y, ‖It φ y‖ ≤ ‖φ‖ * ‖y‖

  equiv : ∀ g φ y, It (ρ (g, 1) φ) y = π₁ g (It φ y)

  inv : ∀ h φ y, It (ρ (1, h) φ) (π₂ h y) = It φ y

  der₁ : ∀ (c : Multiplicative ℝ →* G₁) φ φ' y,
    HasDerivAt (fun t : ℝ => ρ (c (Multiplicative.ofAdd t), 1) φ) φ' 0 →
      HasDerivAt (fun t : ℝ => π₁ (c (Multiplicative.ofAdd t)) (It φ y)) (It φ' y) 0

  weakDer₁ : ∀ (c : Multiplicative ℝ →* G₁) φ φ' y,
    HasWeakDer (fun t : ℝ => ρ (c (Multiplicative.ofAdd t), 1) φ) φ' →
      HasWeakDer (fun t : ℝ => π₁ (c (Multiplicative.ofAdd t)) (It φ y)) (It φ' y)

  der₂ : ∀ (c : Multiplicative ℝ →* G₂) φ φ' y y',
    HasWeakDer (fun t : ℝ => ρ (1, c (Multiplicative.ofAdd t)) φ) φ' →
      HasWeakDer (fun t : ℝ => π₂ (c (Multiplicative.ofAdd t)) y) y' → It φ' y + It φ y' = 0

  ne : ∀ φ, φ ∉ (imSpan Tm)ᗮ → ∀ Y : Set H₂, Dense Y → ∃ y ∈ Y, It φ y ≠ 0

  fin : ∀ (K : Subgroup G₁) φ y, IsFiniteVec K (fun g => ρ (g, 1)) φ → IsFiniteVec K (fun g => π₁ g) (It φ y)

end Hilbert

def ContrHilbert : Prop :=
  ∀ (H₁ H₂ FF : Type)
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]
    (G₁ G₂ : Type) [Group G₁] [Group G₂] (π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)) (π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂))
    (ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)) (Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF),
    IsIsoBilin Tm → IsEquivBilin π₁ π₂ ρ Tm →
      (∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It) ∧
      ∀ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It → ContrProps π₁ π₂ ρ Tm It

def IsTensorIt {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var) {A B : ι → Type}
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ)
    (It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ) : Prop :=
  ∀ (P : ∀ τ, MvPolynomial (σ τ) ℂ) (v : ∀ τ, A τ),
    It (∏ τ, MvPolynomial.rename (fun s => e ⟨τ, s⟩) (P τ)) (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ fun τ => Itl τ (P τ) (v τ)

def ContrTensor : Prop :=
  ∀ (ι : Type) [Fintype ι] (σ : ι → Type) (Var : Type) (e : (Σ τ, σ τ) ≃ Var) (A B : ι → Type)
    [∀ τ, AddCommGroup (A τ)] [∀ τ, Module ℂ (A τ)] [∀ τ, AddCommGroup (B τ)] [∀ τ, Module ℂ (B τ)]
    (Itl : ∀ τ, MvPolynomial (σ τ) ℂ →ₗ[ℂ] A τ →ₗ[ℂ] B τ),
    ∃ It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ,
      IsTensorIt e Itl It ∧ ((∀ τ, Itl τ ≠ 0) → It ≠ 0)

def Contraction : Prop := ContrHilbert ∧ ContrTensor

section Models

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Models

theorem contrProps_of {H₁ H₂ FF : Type}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]
    {G₁ G₂ : Type} [Group G₁] [Group G₂] {π₁ : G₁ →* (H₁ ≃ₗᵢ[ℂ] H₁)} {π₂ : G₂ →* (H₂ ≃ₗᵢ[ℂ] H₂)}
    {ρ : G₁ × G₂ →* (FF ≃ₗᵢ[ℂ] FF)} {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm)
    (hE : IsEquivBilin π₁ π₂ ρ Tm) {It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁} (hC : IsContr Tm It) :
    ContrProps π₁ π₂ ρ Tm It := by
  have hn : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hI x x y y
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hb : ∀ φ y, ‖It φ y‖ ≤ ‖φ‖ * ‖y‖ := by
    intro φ y
    have h := hC φ y (It φ y)
    have h1 : ‖It φ y‖ * ‖It φ y‖ ≤ ‖It φ y‖ * (‖φ‖ * ‖y‖) := by
      have := norm_inner_le_norm (𝕜 := ℂ) (Tm (It φ y) y) φ
      rw [← h, hn, inner_self_eq_norm_sq_to_K] at this
      simp at this
      nlinarith
    rcases (norm_nonneg (It φ y)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exact le_of_mul_le_mul_left h1 h0
  have hall : ∀ g h φ y, It (ρ (g, h) φ) (π₂ h y) = π₁ g (It φ y) := by
    intro g h φ y
    apply ext_inner_left ℂ
    intro x
    obtain ⟨x, rfl⟩ := (π₁ g).surjective x
    rw [hC, hE, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map, hC]
  have he : ∀ g φ y, It (ρ (g, 1) φ) y = π₁ g (It φ y) := fun g φ y => by simpa using hall g 1 φ y
  have hi : ∀ h φ y, It (ρ (1, h) φ) (π₂ h y) = It φ y := fun h φ y => by simpa using hall 1 h φ y
  refine ⟨hb, he, hi, ?_, ?_, ?_, ?_, ?_⟩
  · intro c φ φ' y hd
    let L : FF →L[ℂ] H₁ := (It.flip y).mkContinuous ‖y‖ fun φ => by simpa [mul_comm] using hb φ y
    have := ((L.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hd
    simpa [L, Function.comp_def, he] using this
  · intro c φ φ' y hd w
    simpa only [← he, hC _ _ _] using hd (Tm w y)
  · intro c φ φ' y y' hd hd'
    apply ext_inner_left ℂ
    intro x
    let ℓ : H₂ →L[ℂ] ℂ := ((innerₛₗ ℂ φ) ∘ₗ Tm x).mkContinuous (‖φ‖ * ‖x‖) fun y => by
      simpa [hn, mul_assoc] using norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)
    obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ H₂).surjective ℓ
    have hw' : ∀ z, ⟪w, z⟫_ℂ = ⟪φ, Tm x z⟫_ℂ := fun z => by
      have := congrArg (fun f : H₂ →L[ℂ] ℂ => f z) hw
      simpa [ℓ] using this
    have h1 := hd (Tm x y)
    have h2 := ((hd' w).scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)).star
    have h3 : (fun t : ℝ => ⟪Tm x y, ρ (1, c (Multiplicative.ofAdd t)) φ⟫_ℂ) =
        fun t : ℝ => star (((fun t : ℝ => ⟪w, π₂ (c (Multiplicative.ofAdd t)) y⟫_ℂ) ∘ Neg.neg) t) := by
      funext t
      have hy : y = π₂ (c (Multiplicative.ofAdd t)) (π₂ (c (Multiplicative.ofAdd (-t))) y) := by
        change y = (π₂ _ * π₂ _) y
        rw [← map_mul, ← map_mul, ← ofAdd_add]; simp
      simp only [Function.comp, hw']
      rw [← hC, Complex.star_def, inner_conj_symm, ← hC]
      conv_lhs => rw [hy, hi]
    rw [h3] at h1
    have h4 := h1.unique h2
    rw [inner_add_right, hC, hC, h4, hw']
    simp
  · intro φ hφ Y hY
    by_contra hcon
    push_neg at hcon
    apply hφ
    let L : H₂ →SL[starRingEnd ℂ] H₁ := (It φ).mkContinuous ‖φ‖ (hb φ)
    have h0 : ∀ y, It φ y = 0 := fun y =>
      congrFun (Continuous.ext_on hY L.continuous (continuous_const (y := (0 : H₁))) hcon) y
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨p, rfl⟩ := hu; simp [← hC φ, h0]
    | zero => simp
    | add a b _ _ ha hb => simp [inner_add_left, ha, hb]
    | smul a b _ hb => simp [inner_smul_left, hb]
  · intro K φ y hf
    unfold IsFiniteVec at *
    have : (Set.range fun k : K => π₁ k (It φ y)) = It.flip y '' Set.range fun k : K => ρ (k, 1) φ := by
      rw [← Set.range_comp]; congr 1; funext k; simp [he]
    rw [this, ← Submodule.map_span]
    infer_instance

end GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

end
end
