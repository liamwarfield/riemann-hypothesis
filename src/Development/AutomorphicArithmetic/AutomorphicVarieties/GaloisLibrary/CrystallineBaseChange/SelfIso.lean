module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SelfIso
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

theorem UpperTheory.V.Br.selfIso :
    UpperTheory.V.Br.SelfIso := by
  intro H F _ _ _ a ha π η h2 h
  have hd : ∀ z, TR.dchi η z = 0 := fun z => by
    have e := TR.dchi_mul η η z
    rw [← pow_two, h2, TR.dchi_one] at e
    linear_combination (-1 / 2 : ℂ) * e
  obtain ⟨S, hS⟩ : π.Iso (π.twist η) := H F a ha _ _ (by
    filter_upwards [h] with w ⟨hu, B, hB, hE⟩
    exact ⟨B, hB, hE ▸ hB.twist hu⟩)
  have key : ∀ o φ, (S.trans (π.toTwist η).symm) (π.op o φ) =
      ((TR.opMul η o : ℂˣ) : ℂ) • π.op o ((S.trans (π.toTwist η).symm) φ) +
        TR.opAdd η o • (S.trans (π.toTwist η).symm) φ := fun o φ => by
    apply (π.toTwist η).injective
    rw [← TR.CuspSub.op_toTwist]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hS]
  refine ⟨S.trans (π.toTwist η).symm, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  all_goals rw [key]; simp [TR.opMul, TR.opAdd, hd]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormQuad
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Imports
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.V.Br.intP :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.IntP := by
  intro hP K _ _ _ n hn m hm M _ π hπ p w hp hw _ hd B hB
  obtain ⟨hinf, ⟨χ, hpol⟩, -⟩ := hπ
  have hic : ∀ τ, (CG.mk π).infChar τ = infOf m := fun τ => CG.HasInfChar.infChar_eq (hinf τ)
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hic]
    refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel e
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompC hP K n π w
  have hBσ := ((satLoc hP K n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  refine slopesOf hP m hp w hw hd σ B hBσ fun l _ ι => ?_
  obtain ⟨r, wt, HT, H⟩ := hP.litN.aut.gal K (AlgebraicClosure K) l ι n (by omega) π _ hreg hpol
  have hHT : ∀ τ, HT τ = Finset.univ.val.map fun i => -m i := fun τ => by
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [H.weights τ, hic, infOf, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => by simp
  refine ⟨r, H.cont, fun hl A h rc hrc => H.away w hl A h rc hrc σ hσ, fun A h O _ _ _ Bw hj => ?_⟩
  have a := H.above _ _ (UpperTheory.V.Loc.tiedP l) w A h O Bw hj
  exact ⟨a.crys σ hσ, fun τ LL' τ' hτ => hHT τ ▸ a.jumps τ LL' τ' hτ, fun hi => (a.iwahori σ hσ hi).2⟩
end
