module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def nbar (c : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks 1 0 c 1

def mM (a : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks a 0 0 (aᴴ)⁻¹

def IsSch {m : ℕ} (f : (Fin m → Fin n → ℂ) → ℂ) : Prop := ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑S = f

def AwayCls {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (Ψ : Mx D m n → ℂ) : Prop :=
  (∀ x x' : Mx D m n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') → x.map (finPart D) = x'.map (finPart D) →
    Ψ x = Ψ x') ∧ ∀ f, IsSch f → tens θ τ fr f Ψ ∈ schwartzA θ m n

def Decomp : Prop :=
  ∀ (n : ℕ) (y : GR n), ∃ y₁ y₂ y₃ y₄ : GR n, y = y₁ * y₂ * y₃ * y₄ ∧
    (∃ t : ℝ, mR y₁ = nU ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) ∧ (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y₂ = nbar c) ∧
    (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y₃ = mM a) ∧ (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y₄ = nU b)

def LNe : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ →
    HasRealPar ψ θ l → ∀ τ, l τ ≠ 0

def AwayIn : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → IsTauFrame V τ s ε fr → (∀ τ', l τ' ≠ 0) → ∀ Ψ ∈ awayA θ V n l s τ,
      AwayCls θ τ fr Ψ

def SchFP : Prop := ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, IsSch (fP c P)

def OpGen : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ y : GR n,
    ((∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y = nU b) ∨ (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y = mM a)) →
    ∃ L : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ), (∀ f, IsSch f → IsSch (L f)) ∧
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L f) Ψ

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ConvRight
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def ConvRight : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n →
    ∃ σ : ℝ, ∀ z : ℂ, σ < z.re → ∀ g, GlobalTheory.Eis.CosetConv (P D n) (GF D n) (sect ω H Φ z) g

def ThLin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ Φ', PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ →
    PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ' → PositivityTheory.PfSWUS.InRange V n →
    ∀ g, thetaInt ω ν (Φ + Φ') g = thetaInt ω ν Φ g + thetaInt ω ν Φ' g

def GLamBd : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ L ∈ lamSet (n := n) ψ,
    (∀ (a : ℂ) (F F' : G D n → ℂ), Continuous F → Continuous F' → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ γ ∈ GF D n, ∀ g, F' (γ * g) = F' g) → L (a • F + F') = a * L F + L F') ∧
    ∃ C : Set (G D n), IsCompact C ∧ ∀ (F : G D n → ℂ) (M : ℝ), Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
      (∀ x ∈ C, ‖F x‖ ≤ M) → ‖L F‖ ≤ M

def GLsing : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsCharAF D.host.F ψ →
    IsInfFam θ → IsPlaceEmb θ τ ι → ∀ F : G D n → ℂ, Continuous F → (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
    (∀ L ∈ lamSet (n := n) ψ, L F = 0) → ∀ ψ₀, IsSingTest ψ₀ → ∀ (nb : (Fin n → Fin n → ℝ) → GR n), (∀ x, mR (nb x) = nU (herm x)) →
      ∀ (g : G D n) (a b : GR n), ∫ x, F (g * ι (a * nb x * b)) * ψ₀ x = 0

def LNZ : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ →
    HasRealPar ψ θ l → ∀ τ, l τ ≠ 0

def MainSt : Prop :=
  AbsThm → SFrame → SEmb → SigOK → SplitFock → TensMem → LocOpEx → LocInst → LinSec → GSplit → GIauto → GIk → GIinv →
    GIdil → EisStrong → GLamBd → GLsing → PositivityTheory.PfSWUS.CoefND → ConvRight → ThLin → LNZ →
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (s0 V n) (thetaInt ω ν Φ g)

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def CompInj : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (x y : Mx D m n), (∀ τ, compAt θ τ x = compAt θ τ y) →
    x.map (finPart D) = y.map (finPart D) → x = y

def WEx : Prop := ∀ (D : D7) (n : ℕ), ∃ W : G D n, mat W = blk4 0 1 (-1) 0

def UnipTau : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∀ (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b → mR y = nU b → ∀ (Φ : schwartzA θ V.rank n) (x : Mx D V.rank n),
      (ω (ι y) Φ).1 x = Complex.exp (Complex.I * tLoc l τ * (b * gramX ε (fr⁻¹ * compAt θ τ x)).trace) * Φ.1 x

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def sLd {m : ℕ} (L : GR n → ((Fin m → Fin n → ℂ) → ℂ) → ((Fin m → Fin n → ℂ) → ℂ)) (c : ℝ) (P : PX m n) (y : GR n) : ℂ :=
  L y (fP c P) 0

def pqOf {m : ℕ} (ε : Fin m → Bool) (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : ℕ × ℕ :=
  if 0 < l τ then (cnt ε true, cnt ε false) else (cnt ε false, cnt ε true)

def LIl : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → l τ ≠ 0

def LIlin : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    (∀ (y : GR n) (a : ℂ) (P Q : PX V.rank n), L y (fP (cLoc l τ) (a • P + Q)) = a • L y (fP (cLoc l τ) P) + L y (fP (cLoc l τ) Q)) ∧
    ∀ P : PX V.rank n, L 1 (fP (cLoc l τ) P) = fP (cLoc l τ) P

def LIlaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ e : ℤ, ∀ (P : PX V.rank n) (y g : GR n), (mR y).toBlocks₂₁ = 0 →
      sLd L (cLoc l τ) P (y * g) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e y * sLd L (cLoc l τ) P g

def LIcell : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ (P : PX V.rank n) (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b →
      sLd L (cLoc l τ) P g = C * secN ε (cLoc l τ) (tLoc l τ) P b

def LIcont : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ P : PX V.rank n, Continuous (sLd L (cLoc l τ) P)

def LIrho : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∃ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) ∧
      ∀ P, ∃ W : Submodule ℂ (PX V.rank n), FiniteDimensional ℂ W ∧ P ∈ W ∧ (∀ k : GR n, InK (mR k) → ∀ Q ∈ W, ρ k Q ∈ W) ∧
        ∀ Q ∈ W, ∀ l' : PX V.rank n →ₗ[ℂ] ℂ, ContinuousOn (fun k : GR n => l' (ρ k Q)) {k | InK (mR k)}

def LIkact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ ρ : GR n → PX V.rank n →ₗ[ℂ] PX V.rank n, (∀ (k : GR n) P, InK (mR k) → L k (fP (cLoc l τ) P) = fP (cLoc l τ) (ρ k P)) →
      ∀ P (g k : GR n), InK (mR k) → sLd L (cLoc l τ) P (g * k) = sLd L (cLoc l τ) (ρ k P) g

def LIvac : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ), 0 < c →
    ((t = c ∧ p = cnt ε true ∧ q = cnt ε false) ∨ (t = -c ∧ p = cnt ε false ∧ q = cnt ε true)) →
    ∀ (S : GR n → ℂ) (C : ℂ), Continuous S → S 1 = 1 →
      (∀ (y g : GR n), (mR y).toBlocks₂₁ = 0 → S (y * g) = F0 p q e y * S g) →
      (∀ (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → mR g = JJ n * nU b → S g = C * secN ε c t (1 : PX m n) b) →
      ∀ g, S g = F0 p q e g

def LIkvac : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → TensMem → ∀ L, IsLocOp ω l s τ fr ι L →
    ∀ e : ℤ, (∀ g : GR n, sLd L (cLoc l τ) 1 g = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e g) →
    ∀ k : GR n, InK (mR k) → L k (fP (cLoc l τ) 1) = F0 (pqOf ε l τ).1 (pqOf ε l τ).2 e k • fP (cLoc l τ) 1

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

namespace PlaceFactsH

theorem compAt_eq_psiT {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (w : Mx D a b) :
    compAt θ τ w = w.map (Formalism.IndefR.Eqv.psiT D τ) := by
  have hθτ : θ τ = Formalism.IndefR.Eqv.thetaC D τ :=
    Formalism.IndefR.Eqv.infEmb_unique (hθ τ) (Formalism.IndefR.Eqv.isInfFam_thetaC D τ)
  ext i j
  change (θ τ) (Formalism.L2.Theta.infPart D (w i j)) = Formalism.IndefR.Eqv.psiT D τ (w i j)
  rw [hθτ]
  rfl

theorem mat_mul' (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' : mat (1 : G D n) = 1 := rfl

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  delta GlobalTheory.StdUnn.mat at e
  exact Subtype.ext (Units.ext e)

theorem compAt_mul' {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a : ℕ} (A B : Mx D a a) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B := by
  rw [compAt_eq_psiT hθ, compAt_eq_psiT hθ, compAt_eq_psiT hθ, Matrix.map_mul]

theorem compAt_one' {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a : ℕ} :
    compAt θ τ (1 : Mx D a a) = 1 := by
  rw [compAt_eq_psiT hθ, Matrix.map_one _ (map_zero _) (map_one _)]

section GlobalTheory

variable {R S : Type} [CommRing R] [CommRing S]

def bOf (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

theorem upper_right_entry_block_matrix (a b c d : Matrix (Fin n) (Fin n) R) : bOf (blk4 a b c d) = b := by
  unfold bOf
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bOf_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bOf (M.map f) = (bOf M).map f := by
  ext i j
  rfl

theorem block_matrix_map (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  delta GlobalTheory.StdUnn.blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem submatrix_fromBlocks_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' = blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem reidx_nU (b : Matrix (Fin n) (Fin n) ℂ) : reidx (nU b) = blk4 1 b 0 1 := rfl

end GlobalTheory

theorem commute_of_tau {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    (z : G D n) (hz : compAt θ τ (mat z) = 1) (y' : GR n) : z * ι y' = ι y' * z := by
  obtain ⟨-, hι'⟩ := hι
  obtain ⟨-, h2, h3⟩ := hι' y'
  apply mat_inj
  rw [mat_mul', mat_mul']
  apply Formalism.IndefR.Eqv.mat_ext
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases ht : τ' = τ
    · subst ht
      rw [← compAt_eq_psiT hθ τ' (mat z), hz, one_mul, mul_one]
    · rw [← compAt_eq_psiT hθ τ' (mat (ι y')), h2 τ' ht, one_mul, mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, h3, one_mul, mul_one]

theorem herm_conjTranspose (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  change star ((↑(x j i + x i j) : ℂ) / 2 + Complex.I * ↑(x j i - x i j) / 2) =
    (↑(x i j + x j i) : ℂ) / 2 + Complex.I * ↑(x i j - x j i) / 2
  apply Complex.ext <;> simp <;> ring

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  change (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) *
    Matrix.fromBlocks 0 1 (-1) 0 = -1
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem cT_map_psiT' (τ : D.what₂.Tau) {a : ℕ} (M : Mx D a a) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (Formalism.IndefR.Eqv.psiT D τ) = (M.map (Formalism.IndefR.Eqv.psiT D τ))ᴴ := by
  ext i j
  rw [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
  exact Formalism.IndefR.Eqv.psiT_sigR D τ (M j i)

theorem Jst_map_psiT (τ : D.what₂.Tau) :
    (JR (AF D.host.F) (Jst D n)).map (Formalism.IndefR.Eqv.psiT D τ) = blk4 0 1 (-1) 0 := by
  change ((GlobalTheory.StdUnn.blk4 (0 : Matrix (Fin n) (Fin n) D.host.E) 1 (-1) 0).map
    (inclR (AF D.host.F))).map (Formalism.IndefR.Eqv.psiT D τ) = _
  rw [block_matrix_map, Matrix.map_neg _ (map_neg _), Matrix.map_zero _ (map_zero _),
    Matrix.map_one _ (map_zero _) (map_one _), block_matrix_map, Matrix.map_neg _ (map_neg _),
    Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem tauComp {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : G D n) :
    ∃ y : GR n, reidx (mR y) = compAt θ τ (mat g) := by
  have hU : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat g) * JR (AF D.host.F) (Jst D n) * mat g =
      JR (AF D.host.F) (Jst D n) := g.2
  have hUψ := congrArg (fun X => X.map (Formalism.IndefR.Eqv.psiT D τ)) hU
  simp only [Matrix.map_mul, cT_map_psiT', Jst_map_psiT] at hUψ
  rw [← compAt_eq_psiT hθ] at hUψ
  have hB : (GlobalTheory.StdUnn.blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0).submatrix finSumFinEquiv
      finSumFinEquiv = JJ n := by
    delta GlobalTheory.StdUnn.blk4
    rw [Matrix.submatrix_submatrix]
    simp only [Equiv.symm_comp_self, Matrix.submatrix_id_id]
    rfl
  have hY : ((compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv)ᴴ * JJ n *
      (compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv = JJ n := by
    rw [← hB, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hUψ]
  have hL : (-(JJ n * ((compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv)ᴴ * JJ n)) *
      (compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv = 1 := by
    rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (JJ n), hY, JJ_mul_self, neg_neg]
  refine ⟨⟨⟨_, _, (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hL, hL⟩, hY⟩, ?_⟩
  change ((compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv).submatrix finSumFinEquiv.symm
    finSumFinEquiv.symm = _
  rw [Matrix.submatrix_submatrix]
  simp only [Equiv.self_comp_symm, Matrix.submatrix_id_id]

end PlaceFactsH

open PlaceFactsH

theorem splitTau {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    (g : G D n) : ∃ (y : GR n) (x : G D n), g = ι y * x ∧ ∀ y' : GR n, x * ι y' = ι y' * x := by
  obtain ⟨y, hy⟩ := tauComp hθ τ g
  have h1 : compAt θ τ (mat (ι y)) = compAt θ τ (mat g) := by
    obtain ⟨-, hι'⟩ := hι
    rw [(hι' y).1, hy]
  refine ⟨y, (ι y)⁻¹ * g, (mul_inv_cancel_left _ _).symm, ?_⟩
  apply commute_of_tau hθ hι
  rw [mat_mul', compAt_mul' hθ, ← h1, ← compAt_mul' hθ, ← mat_mul', inv_mul_cancel, mat_one',
    compAt_one' hθ]

namespace PlaceFactsH

theorem nb_mat (nb : hermA D n → G D n) (hnb : PositivityTheory.PfSWUS.IsNMap nb) (b b' : hermA D n) :
    mat (nb b * nb b') = blk4 1 (b.1 + b'.1) 0 1 := by
  rw [mat_mul', hnb b, hnb b', submatrix_fromBlocks_mul]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [add_comm (b'.1 : Mx D n n)]

theorem nb_mul_comm (nb : hermA D n → G D n) (hnb : PositivityTheory.PfSWUS.IsNMap nb) (b b' : hermA D n) :
    nb b * nb b' = nb b' * nb b := by
  apply mat_inj
  rw [nb_mat nb hnb, nb_mat nb hnb, add_comm (b.1 : Mx D n n)]

end PlaceFactsH

open PlaceFactsH

theorem nbTau {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    (nb : hermA D n → G D n) (hnb : PositivityTheory.PfSWUS.IsNMap nb) (nb' : (Fin n → Fin n → ℝ) → GR n)
    (hnb' : ∀ x, mR (nb' x) = nU (herm x)) (x : Fin n → Fin n → ℝ) :
    ∃ b : hermA D n, ι (nb' x) = nb b ∧ b.1.map (finPart D) = 0 ∧ compAt θ τ b.1 = herm x ∧
      (∀ τ', τ' ≠ τ → compAt θ τ' b.1 = 0) ∧ ∀ b' : hermA D n, nb b' * ι (nb' x) = ι (nb' x) * nb b' := by
  classical
  obtain ⟨-, hι'⟩ := hι
  obtain ⟨h1y, h2y, h3y⟩ := hι' (nb' x)
  obtain ⟨β, hβ⟩ : ∃ β : Mx D n n, β = bOf (mat (ι (nb' x))) := ⟨_, rfl⟩
  have hψβ : ∀ τ', β.map (Formalism.IndefR.Eqv.psiT D τ') = if τ' = τ then herm x else 0 := by
    intro τ'
    rw [hβ, ← bOf_map, ← compAt_eq_psiT hθ]
    split_ifs with ht
    · subst ht
      rw [h1y, hnb', reidx_nU, upper_right_entry_block_matrix]
    · rw [h2y τ' ht, ← block_matrix_one, upper_right_entry_block_matrix]
  have hfβ : β.map (Formalism.L2.Theta.finPart D) = 0 := by
    rw [hβ, ← bOf_map, h3y, ← block_matrix_one, upper_right_entry_block_matrix]
  have hmat : mat (ι (nb' x)) = blk4 1 β 0 1 := by
    apply Formalism.IndefR.Eqv.mat_ext
    · intro τ'
      rw [block_matrix_map, hψβ τ', ← compAt_eq_psiT hθ, Matrix.map_zero _ (map_zero _),
        Matrix.map_one _ (map_zero _) (map_one _)]
      split_ifs with ht
      · subst ht
        rw [h1y, hnb', reidx_nU]
      · rw [h2y τ' ht, block_matrix_one]
    · rw [block_matrix_map, hfβ, h3y, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _),
        block_matrix_one]
  have hherm : GlobalTheory.MixModel.adj β = β := by
    apply Formalism.IndefR.Eqv.mat_ext
    · intro τ'
      rw [show GlobalTheory.MixModel.adj β = Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) β from rfl, cT_map_psiT',
        hψβ τ']
      split_ifs
      · exact herm_conjTranspose x
      · exact Matrix.conjTranspose_zero
    · rw [hfβ]
      ext i j
      change Formalism.L2.Theta.finPart D (Formalism.L2.Theta.cA D (β j i)) = 0
      have h0 : Formalism.L2.Theta.finPart D (β j i) = 0 := congrFun (congrFun hfβ j) i
      exact (Formalism.IndefR.Eqv.finPart_sigR D (β j i)).trans (by rw [h0, map_zero])
  have e : ι (nb' x) = nb ⟨β, hherm⟩ := by
    apply mat_inj
    rw [hmat, hnb ⟨β, hherm⟩]
  refine ⟨⟨β, hherm⟩, e, hfβ, ?_, ?_, ?_⟩
  · show compAt θ τ β = herm x
    rw [compAt_eq_psiT hθ, hψβ τ, if_pos rfl]
  · intro τ' ht
    show compAt θ τ' β = 0
    rw [compAt_eq_psiT hθ, hψβ τ', if_neg ht]
  · intro b'
    rw [e, nb_mul_comm nb hnb]

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitSt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def GIwasawa : Prop := ∀ (D : D7) (n : ℕ) (g : G D n), ∃ p ∈ P D n, ∃ k ∈ K D n, g = p * k

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigAtLeast
noncomputable section

open scoped Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

def SigAtLeast (D : D7) (V : HSp D) (k : ℕ) : Prop :=
  ∀ τ : D.what₂.Tau, ∃ (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    IsUnit fr.det ∧ frᴴ * gramAt D V τ * fr = Matrix.diagonal (sgn ε) ∧ k ≤ cnt ε true ∧ k ≤ cnt ε false

def WittLBlt : Prop :=
  ∀ (D : D7) (V : HSp D) (k : ℕ), 2 * k < V.rank → SigAtLeast D V k → k ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V

def WittLBeq : Prop :=
  ∀ (D : D7) (V : HSp D) (k : ℕ), 2 * k = V.rank → SigAtLeast D V k → k ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseD
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem isUnit_det_of_inG {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have hJ : JJ n * JJ n = -1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp [JJ, Matrix.fromBlocks_multiply]
  have h1 : (JJ n).det * (JJ n).det = (-1 : ℂ) ^ (Fintype.card (Fin n ⊕ Fin n)) := by
    rw [← Matrix.det_mul, hJ, Matrix.det_neg, Matrix.det_one, mul_one]
  have hJd : (JJ n).det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h1; exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1.symm
  have e := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul] at e
  refine isUnit_iff_ne_zero.2 fun h0 => hJd ?_
  rw [h0, mul_zero] at e
  exact e.symm

def mkGR (g : M2 n) (hg : InG g) : GR n :=
  ⟨⟨g, g⁻¹, Matrix.mul_nonsing_inv g (isUnit_det_of_inG hg), Matrix.nonsing_inv_mul g (isUnit_det_of_inG hg)⟩, hg⟩

def IsNElt (g : GR n) : Prop := ∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR g = nU b

def IsMElt (g : GR n) : Prop :=
  ∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR g = fromBlocks a 0 0 (a⁻¹)ᴴ

def IsWElt (g : GR n) : Prop := mR g = JJ n

def GenSt : Prop :=
  ∀ n : ℕ, ∀ g : GR n, g ∈ Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h}

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousAtMN
noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.EmbP

open Formalism.IndefR.Eqv (glueA splitInv psiT psiT_glueA finPart_glueA mat_ext psiT_sigR finPart_sigR psiT_inclR
  finPart_inclR continuous_glueA continuous_splitInv thetaC eq_thetaC)

variable (D : D7) {N : ℕ}

open Classical

def atMN (τ : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) (AE D) :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then g i j else (1 : Matrix (Fin N) (Fin N) ℂ) i j)
    ((1 : Matrix (Fin N) (Fin N) (Af D.host.F ⊗[D.host.F] D.host.E)) i j)

theorem psi_atMN (τ τ' : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) :
    (atMN D τ g).map (psiT D τ') = if τ' = τ then g else 1 := by
  classical
  ext i j
  rw [Matrix.map_apply, atMN, Matrix.of_apply, psiT_glueA]
  split_ifs <;> rfl

theorem fin_atMN (τ : D.what₂.Tau) (g : Matrix (Fin N) (Fin N) ℂ) : (atMN D τ g).map (finPart D) = 1 := by
  ext i j
  rw [Matrix.map_apply, atMN, Matrix.of_apply, finPart_glueA]

theorem atMN_mul (τ : D.what₂.Tau) (g g' : Matrix (Fin N) (Fin N) ℂ) :
    atMN D τ (g * g') = atMN D τ g * atMN D τ g' := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, psi_atMN, psi_atMN, psi_atMN]
    split_ifs <;> simp
  · rw [Matrix.map_mul, fin_atMN, fin_atMN, fin_atMN, Matrix.one_mul]

theorem atMN_one (τ : D.what₂.Tau) : atMN D τ (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  apply mat_ext D
  · intro τ'
    rw [psi_atMN, Matrix.map_one _ (map_zero _) (map_one _)]
    split_ifs <;> rfl
  · rw [fin_atMN, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cT_map_psiT (τ : D.what₂.Tau) (M : Matrix (Fin N) (Fin N) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (psiT D τ) = (M.map (psiT D τ))ᴴ := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply, psiT_sigR]

theorem cT_map_fin (M : Matrix (Fin N) (Fin N) (AE D)) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (finPart D) =
      Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (M.map (finPart D)) := by
  ext i j; simp [Formalism.UG.cT, finPart_sigR]

theorem JR_map_psiT (τ : D.what₂.Tau) (J : Matrix (Fin N) (Fin N) D.host.E) :
    (JR (AF D.host.F) J).map (psiT D τ) = J.map (tauE D τ) := by
  ext i j; simp [JR, psiT_inclR]

theorem JR_map_fin (J : Matrix (Fin N) (Fin N) D.host.E) :
    (JR (AF D.host.F) J).map (finPart D) = JR (Af D.host.F) J := by
  ext i j; simp [JR, finPart_inclR]

theorem atMN_unitary (τ : D.what₂.Tau) (J : Matrix (Fin N) (Fin N) D.host.E) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : gᴴ * J.map (tauE D τ) * g = J.map (tauE D τ)) :
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (atMN D τ g) * JR (AF D.host.F) J * atMN D τ g = JR (AF D.host.F) J := by
  apply mat_ext D
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul, cT_map_psiT, JR_map_psiT, psi_atMN]
    split_ifs with h
    · subst h; exact hg
    · simp
  · rw [Matrix.map_mul, Matrix.map_mul, cT_map_fin, JR_map_fin, fin_atMN, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem continuous_atMN (τ : D.what₂.Tau) : Continuous (atMN D (N := N) τ) := by
  classical
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D _).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  by_cases h : τ' = τ
  · simp only [h, if_true]; exact (continuous_apply j).comp (continuous_apply i)
  · simp only [h, if_false]; exact continuous_const

end PositivityTheory.Rg.Sw.Glob.EmbP
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ExistsUnitaryDiag
noncomputable section

open scoped Matrix ComplexOrder
open Matrix Formalism.IndefR.Datum

namespace PositivityTheory.Rg.Sw.Glob

theorem exists_unitary_diag {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ} (hT : T.IsHermitian) :
    ∃ (W : Matrix (Fin k) (Fin k) ℂ) (lam : Fin k → ℝ), Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      Wᴴ * T * W = diagonal (fun i => (lam i : ℂ)) := by
  refine ⟨(hT.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ), hT.eigenvalues, ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have := hT.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this

theorem exists_normal {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} (hM : M.PosDef) : ∃ C : Matrix (Fin k) (Fin k) ℂ,
    Cᴴ * M * C = 1 := by
  have hpos := hM.eigenvalues_pos
  have hUU : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hd : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * M * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) =
      diagonal (fun i => (hM.1.eigenvalues i : ℂ)) := by
    have := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this
  generalize (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = U at hUU hd
  generalize hM.1.eigenvalues = μ at hpos hd
  refine ⟨U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)), ?_⟩
  have hCd : (diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))ᴴ = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp [Complex.conj_ofReal]
  rw [conjTranspose_mul, hCd]
  calc diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * Uᴴ * M * (U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))
      = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * (Uᴴ * M * U) * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hd, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        have hp := hpos i
        have hs : (Real.sqrt (μ i)) ^ 2 = μ i := Real.sq_sqrt hp.le
        have hs0 : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
        have hc : ((Real.sqrt (μ i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
        field_simp
        rw [← Complex.ofReal_pow, hs]

theorem frame_of_cartan {k : ℕ} (G S : Matrix (Fin k) (Fin k) ℂ) (h : IsCartanInv G S) :
    ∃ (ε : Fin k → Bool) (fr : Matrix (Fin k) (Fin k) ℂ), IsUnit fr.det ∧ frᴴ * G * fr = diagonal (sgn ε) ∧
      frᴴ * (G * S) * fr = 1 := by
  obtain ⟨hSS, hSG, hM⟩ := h
  have hMh : (G * S)ᴴ = G * S := hM.1
  have hGh : Gᴴ = G := by
    have h1 : Sᴴ * Sᴴ = 1 := by rw [← conjTranspose_mul, hSS, conjTranspose_one]
    have h2 : Sᴴ * Gᴴ = G * S := by rw [← conjTranspose_mul]; exact hMh
    calc Gᴴ = Sᴴ * Sᴴ * Gᴴ := by rw [h1, Matrix.one_mul]
      _ = Sᴴ * (Sᴴ * Gᴴ) := by rw [Matrix.mul_assoc]
      _ = Sᴴ * (G * S) := by rw [h2]
      _ = Sᴴ * G * S := by rw [Matrix.mul_assoc]
      _ = G := hSG
  obtain ⟨C, hCMC⟩ := exists_normal hM
  have hCCM : C * (Cᴴ * (G * S)) = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin k))).mp hCMC
  have hTh : (Cᴴ * G * C).IsHermitian := by
    show (Cᴴ * G * C)ᴴ = Cᴴ * G * C
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, Matrix.mul_assoc]
  have hTT : (Cᴴ * G * C) * (Cᴴ * G * C) = 1 := by
    have e1 : C * Cᴴ * G = S := by
      have : G = G * S * S := by rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      calc C * Cᴴ * G = C * (Cᴴ * (G * S)) * S := by
            conv_lhs => rw [this]
            simp only [Matrix.mul_assoc]
        _ = S := by rw [hCCM, Matrix.one_mul]
    calc (Cᴴ * G * C) * (Cᴴ * G * C) = Cᴴ * G * (C * Cᴴ * G) * C := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * (G * S) * C := by rw [e1]; simp only [Matrix.mul_assoc]
      _ = 1 := hCMC
  obtain ⟨W, lam, hWW, hWW', hTd⟩ := exists_unitary_diag hTh
  have hsq : ∀ i, lam i = 1 ∨ lam i = -1 := by
    have hD : diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ)) = 1 := by
      rw [← hTd]
      calc Wᴴ * (Cᴴ * G * C) * W * (Wᴴ * (Cᴴ * G * C) * W)
          = Wᴴ * (Cᴴ * G * C) * (W * Wᴴ) * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hWW', Matrix.mul_one, Matrix.mul_assoc Wᴴ (Cᴴ * G * C) (Cᴴ * G * C), hTT, Matrix.mul_one, hWW]
    intro i
    have := congrFun (congrFun hD i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at this
    have h2 : (lam i) * (lam i) = 1 := by exact_mod_cast this
    have h3 : (lam i - 1) * (lam i + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h3 with h | h
    · left; linarith
    · right; linarith
  refine ⟨fun i => decide (lam i = 1), C * W, ?_, ?_, ?_⟩
  · have hinv : ((C * W)ᴴ * (G * S)) * (C * W) = 1 := by
      rw [conjTranspose_mul]
      calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]
    exact isUnit_det_of_left_inverse hinv
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * G * (C * W) = Wᴴ * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => (lam i : ℂ)) := hTd
      _ = diagonal (sgn fun i => decide (lam i = 1)) := by
          congr 1; funext i
          simp only [sgn]
          rcases hsq i with h | h
          · simp [h]
          · simp [h] <;> norm_num
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]

theorem sFrame : SFrame := by
  intro D V τ s h
  exact frame_of_cartan _ _ h

end PositivityTheory.Rg.Sw.Glob
end
end
