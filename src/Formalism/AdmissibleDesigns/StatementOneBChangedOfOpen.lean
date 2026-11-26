module

public import Formalism.SharpRestriction.LevelLetterCocycles.JumpAndLengthOfAdmitted
public import Formalism.AdmissibleDesigns.MemIntegralSpanIffImage
public import Formalism.AdmissibleDesigns.UnramifiedInputOfAdmitted

@[expose] public section

section -- merged from Formalism.AdmissibleDesigns.ColLx
section -- merged from Formalism.AdmissibleDesigns.ColumnUnramifiedCharacter
section -- merged from Formalism.AdmissibleDesigns.ContWRec
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem contW_rec (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l :=
  contW_of i dc ρ π (K.Norm.rhoCont_of i r ρ π hd hc) l

end Formalism.MainNotions.N.KOrb

end
end

section -- merged from Formalism.AdmissibleDesigns.ExistsLx
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KHf

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem exists_Lx {Pe : Type} [AddCommGroup Pe] [Module R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass R' (D.nd.O i) Pe]
    {PE : Type} [AddCommGroup PE] [Module R' PE] [Module (D.nd.O i) PE] [SMulCommClass R' (D.nd.O i) PE]
    (hPe : ∀ (c : D.nd.O i) (m : Pe), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (hPE : ∀ (c : D.nd.O i) (m : PE), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (j : ℕ → ℕ) (x' : X') (l : K.Col i dc)
    (hO : letI := evalModO i (R' := R') x'
      haveI := evalTower i (R' := R') x'
      OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)))
    (hdim : DimLx i dc r χ j x' l) :
    ∃ Lx : Submodule (FractionRing (D.nd.O i)) (↥(Γn i dc (K.colIdx i dc l)) → EvalSp (D.nd.O i) d R' x'),
      LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
        (Γn i dc (K.colIdx i dc l))) ≤ Lx ∧
      (∀ (f : Pe →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := Pe) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := Pe) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → Pe) g)) ∈ Lx) ∧
      (∀ (f : PE →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := PE) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := PE) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → PE) g)) ∈ Lx) ∧
      Module.rank (FractionRing (D.nd.O i))
          (Lx ⧸ (LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))).comap Lx.subtype) ≤
        (j (K.colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
          (LinearMap.ker (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))) : ℕ) := by
  refine ⟨Lx i dc r χ x' l, ?_, ?_, ?_, hdim⟩
  · apply colD_le_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption

end Formalism.MainNotions.N.KHf

end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StA

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1
  omega

theorem card_pos (D : D7) : 0 < Fintype.card (Fin D.R.nV) := by
  rw [Fintype.card_fin]
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1 + D.R.t
  omega

theorem jN_eq {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (dc : TruncatedSeriesCountingIdentities.Decl D i) : jN i ρ π dc = KHf.jK i dc ρ π := rfl

theorem leftId_alg {O : Type} [CommRing O] {A : Type} [Ring A] [Algebra O A] (x : A) (c : O) (m : LeftId O x) :
    c • m = (algebraMap O A c) • m := by
  exact Subtype.ext (Algebra.smul_def c m.1)

section Cols

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem colUz : ∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
    (((KFin.uz i dc Dd.δO l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g :
      ↥(Ideal.span {Dd.δO})) : D.nd.O i) = Dd.δO * KFin.u i dc l g := by
  intro l g
  first
  | (show Dd.δO * KFin.uCol i dc l g = Dd.δO * KFin.u i dc l g
     rw [KFin.u, dite_eq_left (show ((g : GE D.nd)) ∈ KFin.Γc i dc l from g.2)])
  | (simp [KFin.uz, KFin.uzOf, KFin.u, g.2])

theorem column_unramified_character : (∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), KFin.u i dc l (g : GE D.nd) = 0) ∧
    (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), KFin.u i dc l g = 1) :=
  ⟨fun l => KFin.u_I i dc l (KUnr.unrHom i dc l), fun l => KFin.u_one i dc l (KUnr.unrHom i dc l)⟩

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem colLx_of_ringDef
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCr : ∀ x' l, KDim.CrysX i dc Dd.r Dd.χ x' l) (hNeg : ∀ x' l, KDim.NegX i dc Dd.r Dd.χ ρ π x' l)
    (hFin : ∀ x' l, KDim.FinX i dc Dd.r Dd.χ x' l) (hCrW : ∀ l, KDim.CrysW i dc ρ π l) :
    ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ) := by
  intro x' _ l
  have hO := KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (colIdx i dc l)
  have hdim : KHf.DimLx i dc Dd.r Dd.χ (KHf.jK i dc ρ π) x' l :=
    KDim.dimLx_of_font i dc Dd.r Dd.χ ρ π r x' l (card_pos D) (r_pos D) hBK hG2 hFont
      (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l hO) (hCr x' l) (hNeg x' l) (hFin x' l) (hCrW l)
      (KOrb.contW_rec i dc r ρ π hDec hc l)
  rw [jN_eq]
  exact KHf.exists_Lx i dc Dd.r Dd.χ (leftId_alg Dd.e₁) (leftId_alg Dd.E) (KHf.jK i dc ρ π) x' l hO hdim

end Cols

end Formalism.MainNotions.N.K.StA

end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StA

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Cols2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem colLx
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) :
    ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ) := by
  have hρ := K.Norm.rhoCont_of i r ρ π hDec hc
  refine colLx_of_ringDef i r ρ π dc g0 eB e₁ s Dd hD hc hBK hG2 hFont hDec
    (fun x' l => K.Font.crysX_of (i := i) (dc := dc) (r := r) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁) (s := s)
      (Dd := Dd) ρ hG2 hD x' l)
    (fun x' l => K.Font.negX_of (i := i) (dc := dc) (r := r) (ρ := ρ) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁)
      (s := s) (Dd := Dd) hFont hG2 hDec hc hρ hD x' l)
    (fun x' l => KTate.finX (i := i) (dc := dc) (r := Dd.r) (χ := Dd.χ) hFin x' l
      (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l (KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (colIdx i dc l))))
    (fun l => K.Font.crysW_of (i := i) (dc := dc) (r := r) (ρ := ρ) (π := π) hFont hG2 hDec hc hρ l)

end Cols2

end Formalism.MainNotions.N.K.StA

end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.Final

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Open

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (cB : ℕ)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def ColOpen : Prop :=
  ∃ (κ : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) → GE D.nd → Lr i Dd)
      (κz : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) →
      coZ1s (resRep (uRep (D.nd.O i) (M := Lr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) (colIdx i dc l))))
      (u : Col i dc → GE D.nd → D.nd.O i)
      (uz : ∀ l : Col i dc,
      coZ1s (Representation.trivial (D.nd.O i) ↥(decs D.host.E (Aw i dc) (colIdx i dc l)) ↥(Ideal.span {Dd.δO}))),
      (∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
      (((uz l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g : ↥(Ideal.span {Dd.δO})) :
        D.nd.O i) = Dd.δO * u l g) ∧
      (KHf.UnrFin i dc Dd.δO uz) ∧
      (∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ)) ∧
      (InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk) κ
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) κz (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk)) ∧
      ((∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), u l (g : GE D.nd) = 0) ∧
      (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), u l g = 1))


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def TBOpen : Prop :=
      (∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → ∀ w ∈ rowsN i dc,
      (∀ ψ : Ymod Dd.r Dd.χ Dd.E →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c,
        (∀ g ∈ (decs D.host.E (Aw i dc)) w, ∀ y, ψ (uElt Dd.r Dd.χ g • y) = uElt Dd.r Dd.χ g • ψ y) →
        ∀ z : coZ1s (QS.resU i dc Dd c w),
          (∀ g : (decs D.host.E (Aw i dc)) w, (z : (decs D.host.E (Aw i dc)) w → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) g =
            ψ (yY Dd.r Dd.χ Dd.E (g : GE D.nd))) →
          (((D.nd.l i : ℕ) : D.nd.O i) ^ cB) • (Submodule.mkQ _ z : H1z (QS.resU i dc Dd c w)) ∈ FS i r π dc g0 eB e₁ s Dd hD hc c w) ∧
      Module.length (D.nd.O i) (↥(lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
        (FS i r π dc g0 eB e₁ s Dd hD hc c w).comap (lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype) ≤
        eON i * (cB : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 1))


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def ChiOpen : Prop :=
      (∀ c : Fin (D.R.t + 1), 2 ≤ (c : ℕ) →
      InChiFixReal (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ Dd.E (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
        (qsN i dc) (ShaN i ((c : ℕ) - 1)) (FS i r π dc g0 eB e₁ s Dd hD hc c) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd)
        (QS.ζO i dc) (QS.nQ i dc))


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def FirstLocalConditionOpen : Prop :=
      (InChiLoc (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk QS.c1) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc)
      (FS i r π dc g0 eB e₁ s Dd hD hc QS.c1) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc))

end Open

section Final

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem row_bound_normalized_lattice (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (cB : ℕ) (h : EmbeddingTypes.admTB i r π dc cB) :
    EmbeddingTypes.admTB i (Norm.rN i r ρ π) π dc cB := by
  intro w hw hrow C hC
  have ht : Norm.IsConjM ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π)) ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (Norm.rN i r ρ π) π)) :=
    Norm.conj_locC i C (Norm.conj_twistM _ (Norm.conjK i r ρ π hd π) _)
  have hset : (fun τ => {a | Formalism.WeaklyAdmissibleFiltrations.IsJumpV (Br.PD D.loc D.nbr i w hw)
      (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (Norm.rN i r ρ π) π))) τ a}) =
      (fun τ => {a | Formalism.WeaklyAdmissibleFiltrations.IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a}) :=
    funext fun τ => Set.ext fun a => ((Norm.jd _ ht).2.2 τ a).symm
  have := h w hw hrow C hC
  rw [← hset] at this
  exact this

variable (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def OnRing (Q : ∀ (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
      (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
      [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
      (_hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i)
        g0 eB e₁ s Dd)
      (_hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π)) (_hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
      (_hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1), Prop) : Prop :=
  TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (Norm.rN i r ρ π) ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i (Norm.rN i r ρ π) dc e' →
    EmbeddingTypes.admTB i (Norm.rN i r ρ π) π dc cB → π ∈ D.nd.Z i →
    ∀ (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
      (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
      [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
      (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i)
        g0 eB e₁ s Dd)
      (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π)) (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
      (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1),
      Q g0 eB e₁ s Dd hD hc hT hrk


end Final

section Stmts

end Stmts

section EmbeddingTypes

end EmbeddingTypes

section Land

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)

end Land

section WithCols

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (cB : ℕ)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def RhoOpenA : Prop :=
      (InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk) (KFin.κ i dc Dd ρ π)
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) (KFin.κz i dc Dd ρ π) (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk))

end WithCols

section FinalA

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)



set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem theorem_n5_of_ring_inputs (g1 : TruncatedSeriesCountingIdentities.admG1 i r) (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g3 : TruncatedSeriesCountingIdentities.admG3 i r ρ π) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (g6 : TruncatedSeriesCountingIdentities.admG6 i r) (ct : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (dcm : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (a51 : LargeLevelLemmas.adm51 i r ρ π) (hG : K.SelfGood i)
    (hP : OnRing i r ρ π dc lenRow e' cB (fun g0 eB e₁ s Dd _ hD hc hT hrk =>
      SelmerInequalityThree i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk lenRow cB)) :
    TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB →
      TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hR hL hTB
  have hR' := Norm.row_normalized i r ρ π dcm dc lenRow hR
  have hL' := Norm.lift_normalized i r ρ π dcm dc e' hL
  have hT' := row_bound_normalized_lattice i r ρ π dc dcm cB hTB
  refine H0.theorem_of_display_and_g2 i r ρ π dc lenRow e' cB (fun _ _ hπ _ _ => ?_) g2 g5x
  have hN := Norm.normAt_rN i r ρ π
  have hG1 := Norm.admG1_rN i r ρ π dcm g1
  obtain ⟨g0, -, ⟨u0, hcyc⟩, eB, e₁, s, hI, hX⟩ := Norm.design_normalized_of_admitted i r ρ π a51 hπ
  obtain ⟨Dd, hD, -, i1, i2, i3, i4, i5, hTop, hK⟩ :=
    normalized_ring_data i (Norm.rN i r ρ π) ρ π hN hG1 g3.2.2 g0 eB e₁ s hI hX
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
  have hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π) := Norm.continuity_normalized i r ρ π (Norm.rhoCont_of i r ρ π dcm ct) ct
  exact selmer_inequality_three i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hTop (rank_reduction_idempotent_one Dd hI hD) lenRow e' cB hN
    (RepresentationBoundsCohomology.primHyp_of D.nd (Norm.rN i r ρ π) ρ π hN hG1) u0 hcyc hK (Norm.admG6_rN i r ρ π dcm g6) hL' hG
    (hP hR' hL' hT' hπ g0 eB e₁ s Dd hD hc hTop (rank_reduction_idempotent_one Dd hI hD))

end FinalA

section StmtsA

end StmtsA

section FinalB

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (cB : ℕ)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem plugOpen3_B (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (hUn : StD.UnrIn i dc) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (bka : LargeLevelLemmas.BlochKatoAnnihilators i) (hG : K.SelfGood i) (hR : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow)
    (hRho : RhoOpenA i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk) (hTB : TBOpen i r π dc g0 eB e₁ s Dd hD hc cB)
    (hChi : ChiOpen i r π dc g0 eB e₁ s Dd hD hc) (hLoc1 : FirstLocalConditionOpen i r π dc g0 eB e₁ s Dd hD hc)
    (hRT : StD.RowTieIn i r ρ π dc g0 eB e₁ s Dd hD hc) :
    SelmerInequalityThree i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk lenRow cB :=
  ⟨KFin.κ i dc Dd ρ π, KFin.κz i dc Dd ρ π, KFin.u i dc, KFin.uz i dc Dd.δO, StA.colUz i dc Dd,
    StD.unrFin_of i dc Dd.δO hUn, StA.colLx i r ρ π dc g0 eB e₁ s Dd hD hc hBK hG2 hFont hDec hFin, hRho,
    StD.bKa_clause i r π dc g0 eB e₁ s Dd hD hc bka hG (StD.rowDR_of_fontaine i r ρ π dc g0 eB e₁ s Dd hD hc hFont hG2 hDec hN),
    hTB, hChi, StA.column_unramified_character i dc, hLoc1,
    StD.tie_clause i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk lenRow hG hR (StD.row_match_from_comparison i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk hRT)⟩

end FinalB

section FinalB2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
def RemainingInputsLastLayer : Prop :=
  OnRing i r ρ π dc lenRow e' cB (fun g0 eB e₁ s Dd _ hD hc hT hrk =>
    RhoOpenA i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk ∧
    TBOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc cB ∧
    ChiOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    FirstLocalConditionOpen i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc ∧
    StD.RowTieIn i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem theorem_n5_of_open_b (g1 : TruncatedSeriesCountingIdentities.admG1 i r) (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g3 : TruncatedSeriesCountingIdentities.admG3 i r ρ π) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (g6 : TruncatedSeriesCountingIdentities.admG6 i r) (bk : TruncatedSeriesCountingIdentities.admBK i) (bka : LargeLevelLemmas.BlochKatoAnnihilators i) (ct : TruncatedSeriesCountingIdentities.FamilyContinuous i r)
    (dcm : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (font : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (a51 : LargeLevelLemmas.adm51 i r ρ π)
    (unr : StD.UnrIn i dc) (hG : K.SelfGood i) (hO : RemainingInputsLastLayer i r ρ π dc lenRow e' cB) :
    TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' → EmbeddingTypes.admTB i r π dc cB →
      TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  intro hR hL hTB
  refine theorem_n5_of_ring_inputs i r ρ π dc lenRow e' cB g1 g2 g3 g5x g6 ct dcm a51 hG ?_ hR hL hTB
  intro hR' hL' hTB' hZ g0 eB e₁ s Dd _ hD hc hT hrk
  obtain ⟨hRho, hTBo, hChi, hLoc1, hRT⟩ := hO hR' hL' hTB' hZ g0 eB e₁ s Dd hD hc hT hrk
  exact plugOpen3_B i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk lenRow cB bk
    (Norm.admG2_rN (hd := dcm) (h := g2)) font (Norm.decomposes_normalized (i := i) (r := r) (ρ := ρ) (π := π)) fin unr
    (Norm.normAt_rN (i := i) (r := r) (ρ := ρ) (π := π)) bka hG hR' hRho hTBo hChi hLoc1 hRT

end FinalB2

section StmtsB

end StmtsB

end Formalism.MainNotions.N.K.Final

end
