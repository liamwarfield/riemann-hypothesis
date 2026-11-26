module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreFibreIdeal.Statement : Prop :=
  ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (F : Type) [Field F] (φ : O →+* F)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω),
    segreRels ι F ⊆ ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) : Set _) ∧
    (mIdealOver O y).map (MvPolynomial.map φ) ≤
      ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ)).comap (segreIncl ι F) ∧
    ∀ W : Ideal (MRing ι F), (mIdealOver O y).map (MvPolynomial.map φ) ≤ W →
      (mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) ≤ segreLift ι F W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime intNum)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreLiftComap.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W' : Ideal (MRing (segreIdx ι) F)), IsMultiProjPrime W' →
      segreRels ι F ⊆ W' →
      IsMultiProjPrime (W'.comap (segreIncl ι F)) ∧ W' = segreLift ι F (W'.comap (segreIncl ι F))

theorem SegreLiftComap.hyps :
    IsMultiProjPrime (⊥ : Ideal (MRing (segreIdx (fun _ : Unit => Fin 1)) ℚ)) ∧
      segreRels (fun _ : Unit => Fin 1) ℚ ⊆
        ((⊥ : Ideal (MRing (segreIdx (fun _ : Unit => Fin 1)) ℚ)) : Set _) := by
  have : ∀ k, Nonempty (segreIdx (fun _ : Unit => Fin 1) k) := fun k => by
    rcases k with _ | _
    · exact ⟨fun _ => (0 : Fin 1)⟩
    · exact ⟨(0 : Fin 1)⟩
  refine ⟨NumbersDVR.isMultiProjPrime_bot, ?_⟩
  rintro g ⟨c, d, rfl⟩
  obtain rfl : c = d := Subsingleton.elim _ _
  simp

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
