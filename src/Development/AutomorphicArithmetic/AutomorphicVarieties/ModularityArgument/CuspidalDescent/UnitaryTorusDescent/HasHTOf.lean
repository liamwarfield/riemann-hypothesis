module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.GalUnitaryO
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PlainTorOfPs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocDataT

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.UnitaryTorusDescent.TypeTor
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.WeilDeligne UpperTheory.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Desc.P.typeTor :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω) (h : IsPlaceOver A w) (χ : Fin n → G E Ω →* ℂˣ) (y : WD h),
    Hi.IsTypeWD h (fun i => (χ i).comp (Ine (F := E) A).subtype) y → Z.Win.Gd y := by
  intro E Ω _ _ _ _ _ n w A h χ y hy
  obtain ⟨b, rfl, hN, hρ⟩ := hy
  have key : ∀ c : Weil h, (hc : deg c = 0) → (∀ k, χ k c.1 = 1) → LocalGlobalAboveLAlt.Triv (WD.mk b) c := by
    intro c hc hk
    have hmem : (c : G E Ω) ∈ Ine A := deg_eq_zero_iff.1 hc
    have hρ1 : b.ρ c = 1 := by
      have := hρ ⟨c, hmem⟩
      have hinc : ineIncl h ⟨c, hmem⟩ = c := rfl
      rw [hinc] at this
      rw [this]
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hk, Units.val_one,
        Matrix.diagonal_one, Matrix.toLin'_one]
      rfl
    show (WD.mk b).charPol c = (Polynomial.X - 1) ^ (WD.mk b).lpDim
    rw [WD.charPol_mk, WD.lpDim_mk, hρ1, LinearMap.charpoly_one, Module.finrank_fin_fun]
  refine ⟨fun s t => key _ ?_ (fun k => ?_), (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN⟩
  · rw [commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]
    ring
  · have := map_commutatorElement ((χ k).comp (Weil h).subtype) s t
    exact this.trans (commutatorElement_eq_one_iff_mul_comm.2 (mul_comm (((χ k).comp (Weil h).subtype) s) _))
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Desc.P

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G L Ω →* GL (Fin n) (Qbar l)} {w : Plc L} {τ : SmIrr (GLw n w)} {A : ValuationSubring Ω}
  {HT : (L →+* Qbar l) → Multiset ℤ}

theorem lgAwayT (k : LocGlobT ι r w τ) (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion L) → WD h) (hrc : IsRecT h rc) : WOT ι r (rc (algNorm τ)) := (k A h rc hrc).1 hw

theorem woTypeT {h : IsPlaceOver A w} {y : WD h} (k : WOT ι r y) (χ : Fin n → G L Ω →* ℂˣ)
    (t : IsTypeWD h (fun i => (χ i).comp (Ine (F := L) A).subtype) y) : IsWDOf ι r y :=
  WDT.isWDOf k (typeTor L Ω n w A h χ y t)


end UpperTheory.V.Z.Desc.P
