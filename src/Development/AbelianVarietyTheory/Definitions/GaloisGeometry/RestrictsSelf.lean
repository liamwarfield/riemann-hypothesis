module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
noncomputable section

open Neutral.B1 hiding G IsPlaceOver
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL

def resTo {K Ω : Type} (L : Type) [Field K] [Field L] [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
    {M : Type} [Monoid M] (r : G K Ω →* M) : G L Ω →* M :=
  r.comp (AlgEquiv.restrictScalarsHom K)

def Restricts {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}
    (x : WD h) (x' : WD h') : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h' (Fin n → ℂ)), WD.mk a = x ∧ WD.mk b = x' ∧ b.N = a.N ∧
    ∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → b.ρ σ' = a.ρ σ

def IneTriv {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x : WD h) : Prop :=
  ∀ τ : Ine (F := K) A, x.charPol (ineIncl h τ) = (Polynomial.X - 1) ^ x.lpDim

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

end GlobalTheory.AboveL

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedGLOfHasSatGL
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CuspRep ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem mem_integer_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov (F := E) w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← Valuation.vle_iff_le, Valuation.vle_iff_le Valued.v, map_one]
  rfl

theorem range_eq {K : Type} [Field K] {A B : Subring K} (h : A = B) (n : ℕ) :
    (Formalism.UG.bc (n := Fin n) B.subtype).range = (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap A K)).range := by
  subst h; rfl

theorem kgl_eq_ko (n : ℕ) : GlobalTheory.LFun.KGL w (n := n) = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) :=
  range_eq (SetLike.ext fun x => mem_integer_iff w x) n

theorem isSpherical_of_hasSatGL (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w ρ B) :
    GlobalTheory.SmGL.IsSpherical ρ := by
  have h1 := h.1
  unfold GlobalTheory.LGrp.IsSpherical at h1
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rwa [← kgl_eq_ko]

end GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel
end
end
