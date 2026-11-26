module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.GoodLifts.OfIsGood
noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.TP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

structure GoodNG (B : Base F E) : Prop where
  cm : IsCMExt F E σ
  unram : Algebra.Unramified (𝓞 F) (𝓞 E)
  std : IsStd B.ψ
  inert : ∀ v w, Formalism.UG.IsInertAt F E v w → (2 : 𝓞 F) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal ∧ PsiUnr B.ψ v
  psiP : ∀ v ∈ B.P, PsiUnr B.ψ v

end UpperTheory.TP

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CoreAtIffRowAt
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP

open Sub

theorem map_wtJumps {a : ℕ} (lam : DomWeight a) :
    (wtJumps lam).map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map fun z => ((a : ℂ) - 1) / 2 - z := by
  simp only [wtJumps, infOfWeight, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

theorem sphG_iff_cl (hS : SatPol) {a : ℕ} (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E))
    (B : Multiset ℂˣ) (lam : (E →+* ℂ) → DomWeight a) :
    (∀ c, GlobalTheory.Row9.SphG c ι r w B fun τ => infOfWeight (lam τ)) ↔
      Cl ι r w (algSat a (normV w) B) (GlobalTheory.GalDef.jumpsOf ι lam) := by
  constructor
  · intro h
    refine ⟨h .unr, fun P AI hT A hA O _ _ _ Bw hj => ⟨h .crys P AI hT A hA O Bw hj, (h .dR P AI hT A hA O Bw hj).1,
      fun τ LL' τ' hi => (h .dR P AI hT A hA O Bw hj).2 τ LL' τ' hi _ (map_wtJumps _), fun g => ?_⟩⟩
    rw [← hS E Ω A w hA a B g]
    exact h .phi P AI hT A hA O Bw hj g
  · rintro ⟨h1, h2⟩ c
    cases c with
    | unr => exact h1
    | dR =>
      intro P AI hT A hA O _ _ _ Bw hj
      refine ⟨(h2 P AI hT A hA O Bw hj).2.1, fun τ LL' τ' hi J hJ => ?_⟩
      have e : J = wtJumps (lam (ι.toRingHom.comp τ)) :=
        Multiset.map_injective Int.cast_injective (hJ.trans (map_wtJumps _).symm)
      rw [e]
      exact (h2 P AI hT A hA O Bw hj).2.2.1 τ LL' τ' hi
    | crys => exact fun P AI hT A hA O _ _ _ Bw hj => (h2 P AI hT A hA O Bw hj).1
    | phi =>
      intro P AI hT A hA O _ _ _ Bw hj g
      rw [hS E Ω A w hA a B g]
      exact (h2 P AI hT A hA O Bw hj).2.2.2 g


end UpperTheory.Gal.TP

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.TP

def InertOK (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w →
    (2 : 𝓞 (maximalRealSubfield E)) ∉ (w.under (𝓞 (maximalRealSubfield E))).asIdeal ∧
      3 < Ideal.absNorm (w.under (𝓞 (maximalRealSubfield E))).asIdeal ∧
      ¬ differentIdeal ℤ (𝓞 (maximalRealSubfield E)) ≤ (w.under (𝓞 (maximalRealSubfield E))).asIdeal

def TwoUpOK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) → Even (Module.finrank ℚ (maximalRealSubfield E)) → InertOK E →
    ∀ n : ℕ, 1 ≤ n → Even n → Sub.TwoUp E n

end UpperTheory.Gal.TP

end
