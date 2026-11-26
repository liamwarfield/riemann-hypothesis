module

public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.FnDefB
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CBaseYPDef
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def colR (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (j : Fin r) : ℝ :=
  ‖dmin X.Gm x τ j.succ / dmin X.Gm x τ j.castSucc‖


def IsIdOrConj {σ σ' : c.F →+* ℂ} (φ : CAt σ →ₐ[c.F] CAt σ') : Prop :=
  (∀ z : CAt σ, toC (φ z) = toC z) ∨ ∀ z : CAt σ, toC (φ z) = starRingEnd ℂ (toC z)

def RdAt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ))
    (q : Σ k : (U (goodOf c σ)).Comp, ((U (goodOf c σ)).X k).dom × (Ix Dw → (CAt (goodOf c σ))ˣ)) : Prop :=
  ∃ (y' : FrPt Xo c (CAt (goodOf c σ))) (φ : CAt σ →ₐ[c.F] CAt (goodOf c σ)),
    IsIdOrConj φ ∧ FrMap φ y y' ∧ FrBor q.2.2 ((U (goodOf c σ)).un q.1 q.2.1) y'



variable (Xo c) in
def CBaseEx (h : GenFrEx Xo c) : Prop :=
  ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ y : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) y

def yPDef (h : GenFrEx Xo c) (hb : CBaseEx Xo c h) (Z : Comp Xo c) (P : Om Z →+* ℂ) : FrPt Xo c (CAt (sgOf P)) :=
  (hb Z P).choose

end Formalism.L2.Pj
end
end

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


open Classical in
def toGoodR (c : Coeff l) (σ : c.F →+* ℂ) : ℂ →+* ℂ := if GoodEmb c σ then RingHom.id ℂ else starRingEnd ℂ

theorem toGoodR_apply (c : Coeff l) (σ : c.F →+* ℂ) (x : c.F) : toGoodR c σ (σ x) = goodOf c σ x := by
  unfold toGoodR goodOf
  split_ifs <;> rfl

def toGood (c : Coeff l) (σ : c.F →+* ℂ) : CAt σ →ₐ[c.F] CAt (goodOf c σ) :=
  { (toGoodR c σ : ℂ →+* ℂ) with commutes' := fun x => toGoodR_apply c σ x }

theorem isIdOrConj_toGood (c : Coeff l) (σ : c.F →+* ℂ) : IsIdOrConj (toGood c σ) := by
  by_cases h : GoodEmb c σ
  · left; intro z
    show toGoodR c σ (toC z) = toC z
    unfold toGoodR; rw [if_pos h]; rfl
  · right; intro z
    show toGoodR c σ (toC z) = _
    unfold toGoodR; rw [if_neg h]

theorem rdEx_of (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hA : AllTest Xo c)
    (hB : ∀ σ, GoodEmb c σ → BCEx Xo c σ) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) : ∃ q, RdAt U σ y q := by
  have : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  obtain ⟨p, ψ, y0, hy0⟩ := hA (CAt σ) y
  have hg := goodEmb_goodOf c σ
  obtain ⟨z, hz⟩ := hB _ hg p y0 ((toGood c σ).comp ψ)
  have hm : FrMap (toGood c σ) y z := frMap_cancel _ _ _ ψ (toGood c σ) y0 y z hy0 hz
  obtain ⟨k, x, t, ht⟩ := (hU _ hg).2.2.1 z
  exact ⟨⟨k, x, t⟩, z, toGood c σ, isIdOrConj_toGood c σ, hm, ht⟩


end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.UnifFrDet
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.UnifGam
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem smul_coord (x : 𝓞 E) (w : Fin r → E) (a : Fin r) : (x • w) a = (x : E) * w a := by
  simp [Algebra.smul_def]

end Lat

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G (c • u) w = (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, mul_assoc]

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G u (c • w) = cc (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, cc, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end Herm

section Gam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {r : ℕ}

end Gam

end Formalism.L2.Pj
end
end

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_pos (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (ρ : X.Ψ) (i : ℕ)
    (hi : X.p0 + i < r) :
    perFr X x v ρ.1 i = ((mat x ρ)⁻¹ *ᵥ ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 v) ⟨X.p0 + i, hi⟩ := by
  unfold perFr
  rw [dite_eq_left ρ.2, dite_eq_left hi]

theorem perFr_neg (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : E →+* ℂ)
    (hτ : τ ∉ X.Ψ) (ρ : X.Ψ) (hρ : ρ.1 = conjEmb τ) (i : ℕ) (hi : X.p0 - 1 - i < r) :
    perFr X x v τ i = hermC ρ.1 X.Gm (col (mat x ρ) ⟨X.p0 - 1 - i, hi⟩) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb ρ.1 v) := by
  obtain ⟨ρ1, hρ1⟩ := ρ
  simp only at hρ
  subst hρ
  unfold perFr
  rw [dite_eq_right hτ, dite_eq_left hρ1, dite_eq_left hi]

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb]

theorem conjEmb_eq (τ : E →+* ℂ) : conjEmb τ = ComplexEmbedding.conjugate τ := by
  ext x
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]

end Mat

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Fam

section Final

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Final

section Rows

variable {D : D7}

end Rows

end Formalism.L2.Pj
end
end
