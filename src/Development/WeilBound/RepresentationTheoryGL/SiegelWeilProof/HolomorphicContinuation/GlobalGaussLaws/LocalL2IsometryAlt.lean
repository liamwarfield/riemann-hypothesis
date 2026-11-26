module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def ftLoc {m : ℕ} (ε : Fin m → Bool) (t : ℝ) (f : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  ∫ y : Fin m → Fin n → ℂ, f y *
    Complex.exp (Complex.I * ((2 * t : ℝ) : ℂ) * (((Matrix.of u)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of y).trace.re : ℂ))

def FTfact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 →
    ∃ (κ : ℂ) (A A' : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ)), κ ≠ 0 ∧ ∀ Ψ (hΨ : AwayCls θ τ fr Ψ),
      AwayCls θ τ fr (A Ψ) ∧ AwayCls θ τ fr (A' Ψ) ∧ ∀ f (hf : IsSch f),
        IsSch (fun u => κ * ftLoc ε (tLoc l τ) f u) ∧ IsSch (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) ∧
        (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ) f u) (A Ψ) ∧
        (ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ)

def GenA : Prop :=
  ∀ (D : D7) (n : ℕ), Subgroup.closure {g : G D n | (∃ b, mat g = blk4 1 b 0 1) ∨ (∃ a d, mat g = blk4 a 0 0 d) ∨
    (∃ c, mat g = blk4 1 0 c 1)} = ⊤

def LocalL2Isometry : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∀ y : GR n, ∃ κ : ℝ, 0 < κ ∧ ∀ f, IsSch f → ∫ u, ‖L y f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def DX (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (Φ : Mx D V.rank n → ℂ)
    (x : Mx D V.rank n) : ℂ :=
  deriv (fun t : ℝ => Φ (HMul.hMul (mt V (atTau θ V τ (fr * NormedSpace.exp ((t : ℂ) • X) * fr⁻¹))) x)) 0

def LieComm : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ Ψ ∈ awayA θ V n l s τ,
    ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUe ε X → ∀ (P : PX V.rank n) (g : G D n) (x : Mx D V.rank n),
      (ω g (phiS θ τ fr (cLoc l τ) Ψ (vfX (cLoc l τ) X P))).1 x = DX θ V τ fr X (ω g (phiS θ τ fr (cLoc l τ) Ψ P)).1 x

def DerivOne : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι →
    ∀ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUe ε X → ∀ Θ Θ' : schwartzA θ V.rank n,
      (∀ x, Θ'.1 x = DX θ V τ fr X Θ.1 x) → thetaInt ω ν Θ' 1 = 0

end PositivityTheory.Rg.Sw.Glob
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HermSmulOne
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

theorem phiS_eq' {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ}
    {Ψ : Mx D m n → ℂ} {P : PX m n} (h : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : phiS θ τ fr c Ψ P = ⟨_, h⟩ := by
  unfold phiS
  rw [dite_eq_left h]

theorem herm_smul_one (t : ℝ) : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

end PositivityTheory.Rg.Sw.Glob
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem locFact_of (hD : Decomp) (hG : OpGen) : LocFact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  have hop : ∀ y : GR n, ((∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y = mM a)) →
    ∃ L : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ), (∀ f, IsSch f → IsSch (L f)) ∧
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L f) Ψ :=
    fun y hy => hG D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y hy
  choose! large₂ hLgS hLg using hop
  have hdec := fun y : GR n => hD n y
  choose y1 y2 y3 y4 hy h1 h2 h3 h4 using hdec
  have g1 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y1 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y1 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y1 y) = mM a) := fun y => by
    obtain ⟨t, ht⟩ := h1 y
    exact Or.inl ⟨_, herm_smul_one t, ht⟩
  have g2 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y2 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y2 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y2 y) = mM a) := fun y => Or.inr (Or.inl (h2 y))
  have g3 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y3 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y3 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y3 y) = mM a) := fun y => Or.inr (Or.inr (h3 y))
  have g4 : ∀ y, (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR (y4 y) = nU b) ∨
      (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR (y4 y) = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR (y4 y) = mM a) := fun y => Or.inl (h4 y)
  refine ⟨fun y f => large₂ (y1 y) (large₂ (y2 y) (large₂ (y3 y) (large₂ (y4 y) f))), fun y f hf => ?_, fun y Ψ hΨ f hf => ?_⟩
  · exact hLgS _ (g1 y) _ (hLgS _ (g2 y) _ (hLgS _ (g3 y) _ (hLgS _ (g4 y) _ hf)))
  · have step : ∀ (z : GR n) (hz : (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR z = nU b) ∨
        (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR z = nbar c) ∨
        (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR z = mM a)), ∀ f (hf : IsSch f)
        (h : tens θ τ fr f Ψ ∈ schwartzA θ V.rank n),
        ω (ι z) ⟨tens θ τ fr f Ψ, h⟩ = ⟨tens θ τ fr (large₂ z f) Ψ, hΨ.2 _ (hLgS z hz f hf)⟩ := by
      intro z hz f hf h
      exact Subtype.ext (hLg z hz Ψ hΨ f hf)
    have hprod : ω (ι y) = ω (ι (y1 y)) * ω (ι (y2 y)) * ω (ι (y3 y)) * ω (ι (y4 y)) := by
      conv_lhs => rw [hy y]
      simp only [map_mul]
    rw [hprod]
    simp only [Module.End.mul_apply]
    have s4 := hLgS (y4 y) (g4 y) _ hf
    have s3 := hLgS (y3 y) (g3 y) _ s4
    have s2 := hLgS (y2 y) (g2 y) _ s3
    rw [step (y4 y) (g4 y) _ hf, step (y3 y) (g3 y) _ s4, step (y2 y) (g2 y) _ s3, step (y1 y) (g1 y) _ s2]

theorem locOpEx_of_fact (hF : LocFact) (hA : AwayIn) (hS : SchFP) (hL : LNe) : LocOpEx := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨L, -, hL2⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  refine ⟨L, ?_⟩
  intro y Ψ hΨ P
  have hAw : AwayCls θ τ fr Ψ :=
    hA D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr (fun τ' => hL D ψ θ l hC.hψ hC.hθ hC.hl τ') Ψ hΨ
  have hc : 0 < cLoc l τ := by
    have hne := hL D ψ θ l hC.hψ hC.hθ hC.hl τ
    unfold cLoc
    have : 0 < |l τ| := abs_pos.mpr hne
    positivity
  have hf0 : IsSch (fP (cLoc l τ) P) := hS _ _ _ hc P
  rw [phiS_eq' (hAw.2 _ hf0)]
  exact hL2 y Ψ hAw _ hf0

end PositivityTheory.Rg.Sw.Glob
end
end
