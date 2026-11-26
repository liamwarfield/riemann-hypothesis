module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PotOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf

@[expose] public section

open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

section CongLemmas

variable {l : ℕ} [Fact l.Prime]

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

end CongLemmas

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem algClosure (K : Type) [Field K] [NumberField K] [Algebra K Ω] : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩

private theorem exists_alg (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K Ω] [Algebra L Ω]
    (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) : ∃ _ : Algebra K L, IsScalarTower K L Ω := by
  haveI := algClosure (Ω := Ω) L
  have h1 : ∀ x : K, ∃ y : L, algebraMap L Ω y = algebraMap K Ω x := fun x =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) _).2 fun f => h (galEmb_mem ℚ L Ω f) x
  choose f hf using h1
  have hi := (algebraMap L Ω).injective
  let g : K →+* L :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun a b => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun a b => hi (by simp [hf]) }
  letI := g.toAlgebra
  exact ⟨_, IsScalarTower.of_algebraMap_eq fun x => (hf x).symm⟩

end Gal

section Shape

variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem cont_tw {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {n : ℕ}
    {r : Γ →* GL (Fin n) (Qbar l)} {δ : Γ →* (Qbar l)ˣ} (h : Continuous r) (hδ : Continuous δ) : Continuous (tw r δ) := by
  refine cont_units _ ?_
  simp only [tw_val]
  exact (Units.continuous_val.comp hδ).smul (Units.continuous_val.comp h)

end Shape

section Up

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem irr_down {k : Type} [Field k] {n : ℕ} (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (r : G K Ω →* GL (Fin n) k)
    (hi : IsIrr (r.comp (galEmb K L Ω))) : IsIrr r :=
  ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W hW hI => hi.2.2 W hW fun g v hv => hI (galEmb K L Ω g) v hv⟩

private theorem up (hP : Z.Bc.HypothesesZ) (K L : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L]
    [IsCMField L] [Algebra K Ω] [Algebra L Ω] [IsAbelianGalois ℚ L] (hK : Module.finrank ℚ K = 2)
    (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)] (hn : 1 ≤ n)
    (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (hc : Continuous r) (ha : IsAutR ι r)
    (hL' : IsIrr (r.comp (galEmb ℚ L Ω))) (κ : G K Ω →* (Qbar l)ˣ) (hκ : IsAlgChar ι κ) (ka : G L Ω →* (Qbar l)ˣ)
    (hka : ∀ (s : G L Ω) (s' : G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s') :
    IsAutC ι (tw (r.comp (galEmb ℚ L Ω)) ka) := by
  haveI := algClosure (Ω := Ω) L
  haveI := algClosure (Ω := Ω) K
  obtain ⟨_, _⟩ := exists_alg K L h
  haveI : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := isSolvable_of_comm fun a b => mul_comm' a b
  have e : (r.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω) = r.comp (galEmb ℚ L Ω) := MonoidHom.ext fun s => rfl
  have h1 := upQuad hP.af ℚ K Ω l ι hK n hn r hc ha (irr_down K L _ (e ▸ hL'))
  have h1' := twC hP.af K Ω l ι n _ κ hκ h1
  have e1 : ka = κ.comp (galEmb K L Ω) := MonoidHom.ext fun s => hka s _ rfl
  have e2 : (tw (r.comp (galEmb ℚ K Ω)) κ).comp (galEmb K L Ω) = tw (r.comp (galEmb ℚ L Ω)) ka := by
    rw [e1]; rfl
  have h2 := hP.up K L Ω l ι n hn _ (cont_tw (hc.comp (resFacts ℚ K Ω l n r).1) hκ.1) h1'
    (e2 ▸ (shapeFacts l _ n _ _).2.2.2.2.2 hL')
  rwa [e2] at h2

end Up

end UpperTheory.V.Sd
