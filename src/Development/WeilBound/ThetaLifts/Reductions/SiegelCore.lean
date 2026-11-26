module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.Reductions.SiegelCore
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace PositivityTheory.ThKR

open GlobalTheory.SiegelSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def minPar (X : Matrix (Fin n) (Fin r) E) : Set (GAd σ J) :=
  {p | ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular id ∧
    (matHom _ σ J p).1 * adMat F X = adMat F X * B}

def leviMin (X Y : Matrix (Fin n) (Fin r) E) : Set (GAd σ J) :=
  {m | ∃ d d' : Fin r → AF F ⊗[F] E, (matHom _ σ J m).1 * adMat F X = adMat F X * diagonal d ∧
    (matHom _ σ J m).1 * adMat F Y = adMat F Y * diagonal d'}

def unipMin (X : Matrix (Fin n) (Fin r) E) : Set (GAd σ J) :=
  {u | ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular id ∧ (∀ i, B i i = 1) ∧
    (matHom _ σ J u).1 * adMat F X = adMat F X * B ∧
    ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 →
      ∃ a : Fin r → AF F ⊗[F] E,
        ((matHom _ σ J u).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (z i)) = adMat F X *ᵥ a}

def GoodPosition (X Y : Matrix (Fin n) (Fin r) E) (K : Subgroup (GAd σ J)) : Prop :=
  ∀ p ∈ minPar σ J X, p ∈ K →
    ∃ m ∈ leviMin σ J X Y, m ∈ K ∧ ∃ u ∈ unipMin σ J X, u ∈ K ∧ p = m * u

def SiegelCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
        ∃ (K : Subgroup (GAd σ J)) (Ω : Set (GAd σ J)) (c : ℝ),
          IsCompact (K : Set (GAd σ J)) ∧ IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ 0 < c ∧
          (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) ∧
          GoodPosition σ J X Y K ∧
          (∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ siegelSet σ J X Y Ω c K, g = γ * s) ∧
          (∃ C : Set (GAd σ J), IsCompact C ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → a⁻¹ * p * a ∈ C) ∧
          (∃ (C : ℝ≥0) (A : ℕ), ∀ g ∈ siegelSet σ J X Y Ω c K, ∀ γ ∈ ratPts σ J,
            height σ J g ≤ C * height σ J (γ * g) ^ A) ∧
          ∀ φ : GAd σ J → ℂ, IsSmoothModerate σ J φ → IsCuspidal σ J φ →
            ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ siegelSet σ J X Y Ω c K, ‖φ g‖ * (height σ J g : ℝ) ^ N ≤ C

theorem one_mem_minPar (X : Matrix (Fin n) (Fin r) E) : (1 : GAd σ J) ∈ minPar σ J X :=
  ⟨1, Matrix.blockTriangular_one, by simp⟩

theorem one_mem_leviMin (X Y : Matrix (Fin n) (Fin r) E) : (1 : GAd σ J) ∈ leviMin σ J X Y :=
  ⟨1, 1, by simp, by simp⟩

end PositivityTheory.ThKR

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.JoinDef
noncomputable section

namespace PositivityTheory.ThKR

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def JoinAt (B : Base F E) (M : Model σ X W) (om : Rep σ X W) : Prop :=
  ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb om N' →
    N ≠ M.Pol B.ψ B.emb → N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb

def JoinTri : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    JoinAt B G.M om ∧ JoinAt B G.M' om'

end PositivityTheory.ThKR

end
end
