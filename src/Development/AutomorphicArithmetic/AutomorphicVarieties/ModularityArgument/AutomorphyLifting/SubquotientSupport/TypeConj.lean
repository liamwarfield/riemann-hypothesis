module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeConj

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Win.T2.TypeConj

open GlobalTheory.PRep

section General

variable {G V V' W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private def Cj (γ : ℂ ≃+* ℂ) (π : Representation ℂ G V) (π' : Representation ℂ G V') (f : V ≃+ V') : Prop :=
  (∀ (z : ℂ) v, f (z • v) = γ z • f v) ∧ ∀ g v, f (π g v) = π' g (f v)

private theorem Cj.symm {γ : ℂ ≃+* ℂ} {π : Representation ℂ G V} {π' : Representation ℂ G V'} {f : V ≃+ V'}
    (h : Cj γ π π' f) : Cj γ.symm π' π f.symm :=
  ⟨fun z v => f.injective (by rw [h.1]; simp), fun g v => f.injective (by rw [h.2]; simp)⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

end General

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

section Loc2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

end Loc2

section Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {n : ℕ}

private theorem sumList_chars : ∀ (n : ℕ) (ξ : Fin n → Weil h →* ℂˣ) (hξ : ∀ j, GlobalTheory.WeilDeligne.IsSmooth (ξ j)),
    sumList (List.ofFn fun i => WD.lpOfChar h (ξ i) (hξ i)) = WD.mk (WDRep.ofChars h ξ hξ)
  | 0, ξ, hξ => by
    rw [List.ofFn_zero]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | n + 1, ξ, hξ => by
    rw [List.ofFn_succ, SatakeLaw.sumList_cons, sumList_chars n (fun i => ξ i.succ), WD.lpOfChar, WD.lpSum_mk]
    refine WD.sound ⟨SatakeLaw.consEquiv n, fun σ v => funext fun i => ?_, fun v => funext fun i => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp [SatakeLaw.consEquiv]
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp [SatakeLaw.consEquiv]

end Gal

end UpperTheory.V.Z.Win.T2.TypeConj
