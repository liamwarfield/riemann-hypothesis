module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResInjective
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.BadFinite
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.ExistsQuadraticCMExtSplitAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.FirstQuadraticSquareHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.TwoUpOKOfSteps

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.toIsNoetherian UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.LimOddOfLimFinOdd
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.JoinAll
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core
open UpperTheory.Gal.TP

namespace UpperTheory.Gal.Int.Core

theorem goodGuard_usPl (h1 : OneUs) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (d : ℕ) (hd : ImQ E d) : GoodGuard Ω l (UsPl (E := E) d) := by
  refine ⟨fun _ h => h.1, fun S hS => ?_⟩
  have hT := hS.union (Filter.eventually_cofinite.1 ((h1 E d hd).and (GlobalTheory.CongEx.eventually_not_mem_l E l)))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hT
  refine (hD.preimage (Homeomorph.inv (G E Ω)).isOpenMap).mono ?_
  rintro g ⟨v, hv, hdeg, A, hA, hσ⟩
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  have hp : (normV v).Prime := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      (((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hdeg)
  exact ⟨v, hv.1, hv.2.1 hp, hv.2.2, A, hA, hσ⟩

theorem joinAll_of (h1 : OneUs) (hS : SubtractQ) : JoinAll := by
  intro hT hU E Ω _ _ _ _ _ _ l _ ι hF hI d hd hsq n hn
  exact allCoreQ_of hS hT E Ω l ι hF hI _ (goodGuard_usPl h1 E Ω l d hd) (fun m hm => hU m hm E Ω l ι hF d hd hsq) n hn

end UpperTheory.Gal.Int.Core
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneTower
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

private theorem normV_under_eq_of_normV_prime {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) (hp : (normV w).Prime) : normV (w.under (𝓞 K)) = normV w := by
  let f : 𝓞 K ⧸ (w.under (𝓞 K)).asIdeal →+* 𝓞 M ⧸ w.asIdeal :=
    Ideal.quotientMap w.asIdeal (algebraMap (𝓞 K) (𝓞 M)) le_rfl
  have hf : Function.Injective f := Ideal.quotientMap_injective' le_rfl
  have hd : normV (w.under (𝓞 K)) ∣ normV w := by
    have h1 := AddSubgroup.card_addSubgroup_dvd_card f.toAddMonoidHom.range
    rwa [← Nat.card_congr (AddMonoidHom.ofInjective (f := f.toAddMonoidHom) hf).toEquiv] at h1
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · exfalso
    haveI : (w.under (𝓞 K)).asIdeal.IsPrime := (w.under (𝓞 K)).isPrime
    have h2 := (Nat.card_eq_one_iff_unique.1 h).1
    exact not_subsingleton (𝓞 K ⧸ (w.under (𝓞 K)).asIdeal) h2
  · exact h

theorem UpperTheory.Gal.Int.Core.oneTower_holds :
    OneTower := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ l _ ι a sat r hK
  unfold AttOne at hK ⊢
  have hT : Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
      Filter.cofinite Filter.cofinite := by
    refine ((Filter.tendstoCofinite_iff_finite_preimage_singleton _).2 ?_).tendsto_cofinite
    intro v
    refine (Ideal.finite_factors (I := v.asIdeal.map (algebraMap (𝓞 K) (𝓞 M))) ?_).subset ?_
    · exact Ideal.map_ne_bot_of_ne_bot v.ne_bot
    · intro w hw
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      show w.asIdeal ∣ _
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hw]
      exact le_rfl
  filter_upwards [hT.eventually hK] with w hw hp
  have hn := normV_under_eq_of_normV_prime (K := K) w hp
  obtain ⟨B, hB, hF⟩ := hw (hn ▸ hp)
  refine ⟨B, ?_, ?_⟩
  · convert hB using 2
    ext x
    show algebraMap (𝓞 F) (𝓞 M) x ∈ w.asIdeal ↔ algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 F) (𝓞 K) x) ∈ w.asIdeal
    rw [show algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 M) x from
      Subtype.ext (IsScalarTower.algebraMap_apply F K M (x : F)).symm]
  · rw [hn] at hF
    intro A hA
    have hA' : IsPlaceOver A (w.under (𝓞 K)) := by
      intro x
      rw [show algebraMap K Ω (x : K) = algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) from
        IsScalarTower.algebraMap_apply K M Ω (x : K)]
      exact hA _
    obtain ⟨hI, hFr⟩ := hF A hA'
    refine ⟨fun s hs => hI _ ?_, fun σ hσ => ?_⟩
    · obtain ⟨hs1, hs2⟩ := hs
      exact ⟨hs1, fun x hx => hs2 x hx⟩
    · have h3 := hFr (res K Ω M σ) ⟨hσ.1, fun x hx => by rw [hn]; exact hσ.2 x hx⟩
      rw [MonoidHom.comp_apply, map_inv]
      exact h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOne
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut

namespace UpperTheory.Gal.Int.Core

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
open scoped Pointwise

private theorem uniq (hI : IsoOne) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (r r' : G K Ω →* GL (Fin a) (Qbar l)) (hc : Continuous r) (hc' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r') (h : AttOne sat ι K r) (h' : AttOne sat ι K r') : RepIso r r' := by
  refine hI K Ω l ι a r r' hc hc' hs hs' ?_
  filter_upwards [h, h'] with w hw hw' hp
  obtain ⟨B, hB, hr⟩ := hw hp
  obtain ⟨B', hB', hr'⟩ := hw' hp
  obtain rfl := hu _ _ _ hB hB'
  exact ⟨_, hr, hr'⟩


open GlobalTheory.RealGal.TrInv in
private theorem trace_conj (hI : IsoOne) (hC : OneConj) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (h2 : Module.finrank F K = 2) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (r : G K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) (hss : IsSSRep r) (hatt : AttOne sat ι K r) (g : G F Ω) (s s' : G K Ω) (hs : res F Ω K s' = g * res F Ω K s * g⁻¹) : ((r s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  haveI : Algebra.IsQuadraticExtension F K := ⟨h2⟩
  haveI : Normal F K := Algebra.IsQuadraticExtension.normal F K
  have hsur := conj_surjective (F := F) (Ω := Ω) K g
  have hatt' : AttOne sat ι K (r.comp (conj K g)) :=
    hC F Ω K l ι a sat r g (conj K g) (res_conj K g) hsur hatt
  obtain ⟨h, hh⟩ := uniq hI F Ω K l ι a sat hu r (r.comp (conj K g)) hr (hr.comp (continuous_conj K g)) hss
    (isSSRep_comp r _ hsur hss) hatt hatt'
  have hs' : s' = conj K g s := GlobalTheory.SatSysPatch.res_injective (F := F) (Ω := Ω) K (by rw [hs, res_conj])
  subst hs'
  rw [← MonoidHom.comp_apply, hh s]
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle]
  simp


open GlobalTheory.RealGalCompat in
private theorem trace_eq (hI : IsoOne) (hT : OneTower) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Q Q' : QCM F Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (hu : ∀ v B B', sat v B → sat v B' → B = B') (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)) (r' : G ↥Q'.K Ω →* GL (Fin a) (Qbar l)) (hr : Continuous r) (hr' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r') (ha : AttOne sat ι ↥Q.K r) (ha' : AttOne sat ι ↥Q'.K r') (s : G ↥Q.K Ω) (s' : G ↥Q'.K Ω) (hss : res F Ω ↥Q.K s = res F Ω ↥Q'.K s') : ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r' s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  let M : IntermediateField F Ω := Q.K ⊔ Q'.K
  haveI : FiniteDimensional F Q.K := Module.finite_of_finrank_pos (by rw [Q.two]; norm_num)
  haveI : FiniteDimensional F Q'.K := Module.finite_of_finrank_pos (by rw [Q'.two]; norm_num)
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed F,
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := F) _⟩
  haveI : Algebra.IsQuadraticExtension F Q.K := { finrank_eq_two' := Q.two }
  haveI : Algebra.IsQuadraticExtension F Q'.K := { finrank_eq_two' := Q'.two }
  haveI : Normal F M := IntermediateField.normal_sup F Ω Q.K Q'.K
  letI : Algebra Q.K M := (IntermediateField.inclusion (le_sup_left : Q.K ≤ M)).toRingHom.toAlgebra
  letI : Algebra Q'.K M := (IntermediateField.inclusion (le_sup_right : Q'.K ≤ M)).toRingHom.toAlgebra
  haveI : IsScalarTower F Q.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower F Q'.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower Q.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower Q'.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hA := hT F Ω Q.K M l ι a sat r ha
  have hA' := hT F Ω Q'.K M l ι a sat r' ha'
  have hS := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r (res Q.K Ω M) (range_res_normal (F := F)) hs
  have hS' := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r' (res Q'.K Ω M) (range_res_normal (F := F)) hs'
  have hC := hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q.K M Ω)
  have hC' := hr'.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q'.K M Ω)
  obtain ⟨g, hg⟩ := uniq hI F Ω M l ι a sat hu _ _ hC hC' hS hS' hA hA'
  set σ : G F Ω := res F Ω Q.K s with hσ
  have hfix : σ ∈ M.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact s.commutes x
    · rw [hss]; exact s'.commutes x
  let t : G M Ω := IntermediateField.fixingSubgroupEquiv M ⟨σ, hfix⟩
  have ht : res Q.K Ω M t = s := by ext z; rfl
  have ht' : res Q'.K Ω M t = s' := by
    ext z
    exact congrArg (fun u : G F Ω => u z) hss
  have e := hg t
  simp only [MonoidHom.comp_apply, ht, ht'] at e
  rw [e, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem patchOne_holds : IsoOne → OneTower → OneConj → PatchOne := by
  intro hI hT hC F Ω _ _ _ _ _ l _ ι a sat hu S hS r hr
  classical
  haveI : Infinite ↥S := hS.to_subtype
  haveI : Algebra.IsIntegral F Ω := (IsAlgClosure.isAlgebraic (R := F) (K := Ω)).isIntegral
  obtain ⟨η, hηinj, hη⟩ := GlobalTheory.RealGal.SignChar.main F Ω
  let e : ∀ Q : ↥S, G ↥Q.1.K Ω ≃* (η Q.1).ker := fun Q =>
    (MonoidHom.ofInjective (GlobalTheory.SatSysPatch.res_injective F Ω ↥Q.1.K)).trans (MulEquiv.subgroupCongr (hη Q.1).1.symm)
  have he : ∀ Q : ↥S, ∀ (s : G ↥Q.1.K Ω), ((e Q s : (η Q.1).ker) : G F Ω) = res F Ω ↥Q.1.K s := fun Q s => rfl
  have hes : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), res F Ω ↥Q.1.K ((e Q).symm h) = h := by
    intro Q h; rw [← he, MulEquiv.apply_symm_apply]
  let r' : ∀ Q : ↥S, (η Q.1).ker →* GL (Fin a) (Qbar l) := fun Q => (r Q).comp (e Q).symm.toMonoidHom
  have hr' : ∀ Q : ↥S, ∀ (h : (η Q.1).ker), r' Q h = r Q ((e Q).symm h) := fun Q h => rfl
  have hcont : ∀ Q : ↥S, Continuous (r' Q) := by
    intro Q
    haveI : CompactSpace (G ↥Q.1.K Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[↥Q.1.K] Ω))
    have hc : Continuous (e Q) := (UpperTheory.V.Af.continuous_restrictScalarsHom F ↥Q.1.K Ω).subtype_mk _
    let hm := hc.homeoOfEquivCompactToT2 (f := (e Q).toEquiv)
    exact (hr Q).1.comp hm.symm.continuous
  have hss : ∀ Q : ↥S, IsSSRep (r' Q) := by
    intro Q
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a (r Q) (e Q).symm.toMonoidHom ?_ (hr Q).2.1
    rw [MonoidHom.range_eq_top.mpr (e Q).symm.surjective]
    infer_instance
  obtain ⟨ρ, hρc, hρs, hev⟩ := GlobalTheory.IndexTwoPatch.main (G F Ω) (Qbar l) a ↥S (fun Q => η Q.1)
    (hηinj.comp Subtype.val_injective) (fun Q => (hη Q.1).2) r' (fun Q => ⟨hcont Q, hss Q⟩)
    (by
      intro Q g h h' hh
      rw [hr', hr']
      exact trace_conj hI hC F Ω ↥Q.1.K Q.1.two l ι a sat hu (r Q) (hr Q).1 (hr Q).2.1 (hr Q).2.2 g
        ((e Q).symm h) ((e Q).symm h') (by rw [hes, hes]; exact hh))
    (by
      intro Q Q' h h' hh
      rw [hr', hr']
      exact trace_eq hI hT F Ω Q.1 Q'.1 l ι a sat hu (r Q) (r Q') (hr Q).1 (hr Q').1 (hr Q).2.1 (hr Q').2.1
        (hr Q).2.2 (hr Q').2.2 _ _ (by rw [hes, hes]; exact hh))
  refine ⟨ρ, hρc, hρs, hev.mono fun Q hQ => ?_⟩
  have hres : IsSSRep (ρ.comp (res F Ω ↥Q.1.K)) := by
    refine UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a ρ (res F Ω ↥Q.1.K) ?_ hρs
    rw [← (hη Q.1).1]
    infer_instance
  refine GlobalTheory.TraceConj.main (G ↥Q.1.K Ω) (Qbar l) a (r Q) (ρ.comp (res F Ω ↥Q.1.K)) (hr Q).2.1 hres fun s => ?_
  have h1 := hQ (e Q s)
  rw [hr', MulEquiv.symm_apply_apply, he] at h1
  exact h1.symm

end UpperTheory.Gal.Int.Core

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneConj
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open UpperTheory.Gal.Int.Core
open scoped Pointwise


open GlobalTheory.RealGal.AttConj in
theorem UpperTheory.Gal.Int.Core.oneConj_holds :
    OneConj := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ ι a sat r g c hc hsurj h
  have hcs : ∀ s y, c s y = g (s ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) y)) := fun s y => DFunLike.congr_fun (hc s) y
  have hfwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = g (algebraMap K Ω x) := fun x => by
    apply exists_of_fixed
    intro t
    obtain ⟨s, rfl⟩ := hsurj t
    rw [hcs, inv_apply_apply, s.commutes]
  have hbwd : ∀ x : K, ∃ y : K, algebraMap K Ω y = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := fun x => by
    apply exists_of_fixed
    intro t
    have h1 := hcs t (algebraMap K Ω x)
    rw [(c t).commutes] at h1
    calc t ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x))
        = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (g (t ((g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x)))) := (inv_apply_apply _ _).symm
      _ = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := by rw [← h1]
  obtain ⟨γ, hγ⟩ := exists_ringEquiv g hfwd hbwd
  have hγinv : ∀ x : K, algebraMap K Ω (γ.symm x) = (g⁻¹ : Formalism.ConjugateSelfDual.G F Ω) (algebraMap K Ω x) := fun x => by
    have h1 := hγ (γ.symm x)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [h1, inv_apply_apply]
  have hγF : ∀ x : F, γ.symm (algebraMap F K x) = algebraMap F K x := fun x => by
    apply (algebraMap K Ω).injective
    rw [hγinv, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  set e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv γ with he
  have heγ : ∀ y : 𝓞 K, ((e.symm y : 𝓞 K) : K) = γ.symm (y : K) := fun y => rfl
  let P : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K) :=
    fun w => w.comap (e.symm : 𝓞 K →+* 𝓞 K) e.symm.surjective
  have hPmem : ∀ w y, y ∈ (P w).asIdeal ↔ e.symm y ∈ w.asIdeal := fun _ _ => Iff.rfl
  have hPinj : Function.Injective P := by
    intro w1 w2 h12
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    have h3 := congrArg (fun w : HeightOneSpectrum (𝓞 K) => e x ∈ w.asIdeal) h12
    simp only [hPmem, RingEquiv.symm_apply_apply] at h3
    exact Iff.of_eq h3
  have hPunder : ∀ w, (P w).under (𝓞 F) = w.under (𝓞 F) := by
    intro w
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    show algebraMap (𝓞 F) (𝓞 K) x ∈ (P w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
    rw [hPmem]
    have h4 : e.symm (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x :=
      RingOfIntegers.ext (by rw [heγ]; exact hγF x)
    rw [h4]
  have hPnorm : ∀ w, normV (P w) = normV w := by
    intro w
    unfold normV
    refine Nat.card_congr (Ideal.quotientEquiv (P w).asIdeal w.asIdeal e.symm ?_).toEquiv
    exact (Ideal.map_comap_of_surjective _ e.symm.surjective w.asIdeal).symm
  have hPplace : ∀ w (A : ValuationSubring Ω), IsPlaceOver A w → IsPlaceOver (g • A) (P w) := by
    intro w A hA y
    rw [val_lt_one_smul, hPmem, ← hA (e.symm y), heγ, hγinv]
  unfold AttOne at h ⊢
  filter_upwards [hPinj.tendsto_cofinite.eventually h] with w hw hp
  obtain ⟨B, hB, hE⟩ := hw (by rw [hPnorm]; exact hp)
  rw [hPunder] at hB
  rw [hPnorm] at hE
  refine ⟨B, hB, fun A hA => ?_⟩
  obtain ⟨hI, hF⟩ := hE (g • A) (hPplace w A hA)
  refine ⟨fun s hs => hI (c s) (ine_conj g c hc A s hs), fun σ hσ => ?_⟩
  have h5 := hF (c σ) (by rw [hPnorm]; exact frob_conj g c hc A _ σ hσ)
  rw [MonoidHom.comp_apply, map_inv]
  exact h5
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.CsdLift
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.csdLift_holds :
    CsdLift := by
  intro hJ hG E M _ _ _ _ _ _ _ l a ha π P hL hS
  obtain ⟨hreg, hpol, -⟩ := hS
  have hreg' : (CG.mk P).IsRegAlg := (CG.isRegAlg_iff _).2 fun τ => by
    rw [hL.inf τ]
    exact (CG.isRegAlg_iff _).1 hreg (τ.comp (algebraMap E M))
  have hF := GlobalTheory.automorphicFormsFiniteGL
  refine ⟨hreg', ⟨fun v => by rw [locInf_pow, quadChar_locInf], ?_⟩, trivial⟩
  rw [GlobalTheory.CsdLift.compNorm_quadChar_pow]
  refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha P 1 ?_
  have hsd := GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace hF E a π _ hpol
  have hun := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π
  filter_upwards [(GlobalTheory.LiftPolar.tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hs, B, hB⟩
  rw [GlobalTheory.CsdLift.compNorm_quadChar_pow] at hs
  have e1 := GlobalTheory.LiftPolar.cPl_under (E := E) w
  have e2 := GlobalTheory.LiftPolar.normV_cPl w
  have e3 := GlobalTheory.LiftPolar.normV_cPl (w.under (𝓞 E))
  have hf := GlobalTheory.LiftPolar.normV_under (K := E) w
  set f := w.asIdeal.inertiaDeg (𝓞 E)
  have hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B := (CG.hasSat_mk _ _ _).2 hB
  have h1 := hL.sat w f B hf hB0
  have h2 := hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)
  refine ⟨GlobalTheory.CsdLift.unrAt_one w, _, _, h1, h2, ?_⟩
  simp only [GlobalTheory.CsdLift.val_one, Multiset.map_map, Function.comp_def, mul_one, inv_one, inv_pow, inv_inv]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownPhi
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open GlobalTheory.GLq GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.AboveL
open UpperTheory.Gal.Int.Core
open GlobalTheory.RoadU GlobalTheory.RoadU.PhiDescent in
theorem UpperTheory.Gal.Int.Core.downPhi_holds : SphDown .phi := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP r w B hB hQdec hyp Pr AI hT A h O _ _ _ Bw hj g
  have hdec := hQdec A h
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A h hdec
  have hunder : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver h h'
    ext1
    exact this.over.symm
  obtain ⟨c, hc, hdegc, hq, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  obtain ⟨S, hS, -, -, -, -, hTw, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk P).HasSat w' B := by
    have := hP.sat w' 1 B (by rw [pow_one, hunder, hq]) (by rw [hunder]; exact hB)
    simpa using this
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  have hrel : WDRel (RingEquiv.refl Ω) (wdAt Pr ι Bw h hj (r.comp (Dec (F := E) A).subtype))
      (wdAt Pr ι Bw' h' hj' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype)) := by
    by_cases hp : IsPstAt Pr Bw (r.comp (Dec (F := E) A).subtype)
    · exact GlobalTheory.RealGal.wdRelRes_gen E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r hp ι w w' h h' hj hj' i hi
    · have hp' : ¬ IsPstAt Pr Bw' ((r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)).comp (Dec (F := Q.K) A).subtype) :=
        fun H => hp (D.2.2.2.1 H)
      rw [wdAt_of_not_isPstAt _ _ _ _ hp, wdAt_of_not_isPstAt _ _ _ _ hp']
      exact wdRel_trivWD h h' _ a
  have hsat : WDRel (RingEquiv.refl Ω) (satWD h a B) (satWD h' a B) := by
    have h0 := GlobalTheory.RSGam.Transport.wdRel_lpUnr c hc hdegc (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))
    unfold satWD
    rw [hS, hTw, (hS _ _).mp h0]
  have hgc : WeilRel (RingEquiv.refl Ω) g (c g) := (hc g (c g)).2 rfl
  have hcl := hyp w' hunder hB' Pr AI hT A h' O Bw' hj' (c g)
  rw [charPol_eq hrel hgc, charPol_eq hsat hgc]
  exact hcl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownUnr
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.downUnr_holds :
    SphDown .unr := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP ρ w B hB hQdec hyp hl A h
  obtain ⟨w', hunder, h', hN⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A h (hQdec A h)
  have hB' : (CG.mk P).HasSat w' B := by
    have e := hP.sat w' 1 B (by rw [pow_one, hunder, hN]) (hunder ▸ hB)
    simpa using e
  have hlw : ((l : ℕ) : 𝓞 Q.K) ∉ w'.asIdeal := by
    intro hw
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 E))
    have e2 := (h' ((l : ℕ) : 𝓞 Q.K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have hcl := hyp w' hunder hB' hlw A h'
  rw [hN] at hcl
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨s', rfl⟩ := hQdec A h (Ine_le_Dec A hs)
    exact hcl.1 s' hs
  · obtain ⟨σ', rfl⟩ := hQdec A h hσ.1
    have e := hcl.2 σ' hσ
    rw [← map_inv]
    exact e
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownDR
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

set_option maxHeartbeats 1000000 in
theorem UpperTheory.Gal.Int.Core.downDR_holds :
    SphDown .dR := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hP r w B hB hdec hS
  show ClauseAt .dR π ι r w
  intro Pr AI hT A hA O _ _ _ Bw hj
  have hdA := hdec A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdA
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', hu, hw', hn⟩ := GlobalTheory.PlaceNormDec.exists_place_normV_eq E Ω Q w A hA hdA
  have hBP : (CG.mk P).HasSat w' (B.map (· ^ 1)) :=
    hP.sat w' 1 B (by rw [hu, pow_one]; exact hn) (by rw [hu]; exact hB)
  have hc : ClauseAt .dR P ι _ w' := hS w' hu (by simpa using hBP)
  have hc' := hc Pr AI hT A hw' O Bw' hj'
  have D := GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r
  refine ⟨D.1 hc'.1, fun τ LL' τ' hτ J hJ => ?_⟩
  obtain ⟨τK, τ'', hτK, hind⟩ := GlobalTheory.induced_embedding_extends E Ω Q.K l A O Bw Bw' e1 e2 τ LL' τ' hτ
  have hJK : J.map (fun n : ℤ => (n : ℂ)) =
      ((CG.mk P).infChar (ι.toRingHom.comp τK)).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
    rw [hP.inf, RingHom.comp_assoc, hτK]
    exact hJ
  have hres := D.2.2.2.2 τK J (hc'.2 τK LL' τ'' hind J hJK)
  rwa [hτK] at hres
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.DownCrys
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.downCrys_holds :
    SphDown .crys := by
  intro E Ω _ _ _ _ _ _ l _ ι a π Q P hPc r w B hB hQ1 hyp
  have hAF := GlobalTheory.automorphicFormsFiniteGL
  intro Pr AI hT A hA O _ _ _ Bw hj σ hσ hsph
  have hdec := hQ1 A hA
  have hjK := GlobalTheory.RealGal.bridge_j_mem_Kw_of_dec_le E Ω Q.K l A O Bw hdec
  obtain ⟨Bw', e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge E Q.K Ω l A O Bw hjK
  have hj' : Induces Bw' := fun x => by rw [e2]; exact hj x
  obtain ⟨w', h', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω Q.K w A hA hdec
  have hund : w'.under (𝓞 E) = w := by
    have := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA h'
    ext1
    exact this.over.symm
  obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA Q.K Ω A w' h' (RingEquiv.refl Ω) (algebraMap E Q.K) i hi
  have hB' : (CG.mk P).HasSat w' B := by
    have := hPc.sat w' 1 B (by rw [pow_one, hund, hq]) (by rw [hund]; exact hB)
    simpa using this
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp hAF Q.K a P w'
  obtain ⟨e, he⟩ := hPc.loc w w' i hi.cont hi.loc σ σ' hσ hσ'
  have hsph' := (GlobalTheory.CompletionIso.iwahori_spherical_transfer E Q.K w w' i hi.cont a σ σ' e he).2 hsph
  have hcr : ClauseAt .crys P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω Q.K)) w' := hyp w' hund hB'
  exact (GlobalTheory.RealGal.dRSstCrysPstJumps_descend E Ω Q.K l Pr A O Bw Bw' e1 e2 e3 a r).2.2.1
    (hcr Pr AI hT A h' O Bw' hj' σ' hσ' hsph')
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.IsoOne
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.isoOne_holds :
    IsoOne := by
  intro F Ω _ _ _ _ _ l _ ι a r r' hr hr' hs hs' hev
  rw [Filter.eventually_cofinite] at hev
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hev
  refine GlobalTheory.SplitAttUniq.repIso_of_dense r r' hr hr' hs hs' _ (hD.preimage (Homeomorph.inv (G F Ω)).isOpenMap) ?_
  intro g hg
  obtain ⟨v, hv, hdeg, B, hB, hfr⟩ := hg
  have hprime : Nat.Prime (normV v) := by
    have h := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hdeg
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h
  have hv' : ¬¬(Nat.Prime (normV v) → ∃ S, FrobEig ι r v S ∧ FrobEig ι r' v S) := hv
  obtain ⟨S, h1, h2⟩ := (not_not.1 hv') hprime
  have e1 := (h1 B hB).2 _ hfr
  have e2 := (h2 B hB).2 _ hfr
  simp only [Homeomorph.coe_inv, inv_inv] at e1 e2
  exact Polynomial.map_injective _ ι.injective (e1.trans e2.symm)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.OneUsHolds
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

private theorem exists_intCast_eq_of_card_prime (k : Type) [Ring k] (p : ℕ) (hp : Nat.Prime p) (hk : Nat.card k = p)
    (y : k) : ∃ n : ℤ, (n : k) = y := by
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact hp.ne_zero)
  haveI : Nontrivial k := by
    rw [← Finite.one_lt_card_iff_nontrivial, hk]; exact hp.one_lt
  have htop : AddSubgroup.zmultiples (1 : k) = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    have hdvd := AddSubgroup.card_addSubgroup_dvd_card (AddSubgroup.zmultiples (1 : k))
    rw [hk] at hdvd ⊢
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exfalso
      rw [AddSubgroup.card_eq_one] at h
      have : (1 : k) ∈ AddSubgroup.zmultiples (1 : k) := AddSubgroup.mem_zmultiples 1
      rw [h] at this
      exact one_ne_zero this
    · exact h
  have hy : y ∈ AddSubgroup.zmultiples (1 : k) := by rw [htop]; trivial
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  exact ⟨n, by simpa using hn⟩

private theorem complexConj_eq_neg_of_sq_eq_neg_natCast (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (hd0 : 0 < d)
    (x : E) (hx : x ^ 2 = -(d : E)) : IsCMField.complexConj E x = -x := by
  obtain ⟨φ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  have h2 : (φ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx]; simp
  have hre : (φ x).re = 0 := by
    have him := congrArg Complex.im h2
    have hre2 := congrArg Complex.re h2
    simp [pow_two] at him hre2
    have hm : (φ x).re * (φ x).im = 0 := by linarith
    rcases mul_eq_zero.mp hm with h | h
    · exact h
    · rw [h] at hre2
      have : (0:ℝ) < d := by exact_mod_cast hd0
      nlinarith [sq_nonneg (φ x).re]
  apply Complex.ext <;> simp [hre]

private theorem prime_dvd_of_intCast_mem_of_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] (q : ℕ)
    (hq : Nat.Prime q) (hqP : (q : R) ∈ P) (m : ℤ) (hm : (m : R) ∈ P) : (q : ℤ) ∣ m := by
  by_contra h
  have hirr : Irreducible (q : ℤ) := (Nat.prime_iff_prime_int.mp hq).irreducible
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hirr).mpr h
  have h1 : ((a * q + b * m : ℤ) : R) ∈ P := by
    push_cast
    exact P.add_mem (P.mul_mem_left _ hqP) (P.mul_mem_left _ hm)
  rw [hab, Int.cast_one] at h1
  exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one P).mpr h1)

private theorem isSquare_neg_padic_of_dvd_sq_add_of_not_dvd (q : ℕ) [Fact q.Prime] (d n : ℤ) (h1 : (q : ℤ) ∣ n ^ 2 + d)
    (h2 : ¬ (q : ℤ) ∣ 2 * n) : IsSquare (-(d : ℚ_[q])) := by
  have hnorm : ‖(Polynomial.X ^ 2 + Polynomial.C d : Polynomial ℤ).aeval (n : ℤ_[q])‖ <
      ‖(Polynomial.X ^ 2 + Polynomial.C d : Polynomial ℤ).derivative.aeval (n : ℤ_[q])‖ ^ 2 := by
    have e1 : (Polynomial.X ^ 2 + Polynomial.C d : Polynomial ℤ).aeval (n : ℤ_[q]) =
        ((n ^ 2 + d : ℤ) : ℤ_[q]) := by
      simp
    have e2 : (Polynomial.X ^ 2 + Polynomial.C d : Polynomial ℤ).derivative.aeval (n : ℤ_[q]) =
        ((2 * n : ℤ) : ℤ_[q]) := by
      simp [Polynomial.derivative_X_pow]
      left
      exact map_ofNat _ 2
    rw [e1, e2]
    have a1 : ‖((n ^ 2 + d : ℤ) : ℤ_[q])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).mpr h1
    have a2 : ‖((2 * n : ℤ) : ℤ_[q])‖ = 1 := by
      have hle : ‖((2 * n : ℤ) : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
      have hnlt : ¬ ‖((2 * n : ℤ) : ℤ_[q])‖ < 1 :=
        fun h => h2 ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
      linarith [not_lt.mp hnlt]
    rw [a2]
    simpa using a1
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨(z : ℚ_[q]), ?_⟩
  have hz' : z ^ 2 + (d : ℤ_[q]) = 0 := by simpa using hz
  have hz'' : ((z ^ 2 + (d : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz']; simp
  push_cast at hz''
  linear_combination -hz''

theorem UpperTheory.Gal.Int.Core.oneUs_holds :
    OneUs := by
  unfold OneUs
  intro E _ _ _ d hd
  obtain ⟨hd0, x, hx⟩ := hd
  have hint : IsIntegral ℤ x := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hx]
    apply IsIntegral.neg
    have := isIntegral_algebraMap (R := ℤ) (A := E) (x := (d:ℤ))
    simpa using this
  let xo : 𝓞 E := ⟨x, hint⟩
  have hxo : xo ^ 2 = -(d : 𝓞 E) := by
    apply RingOfIntegers.ext
    push_cast
    exact hx
  let cO := RingOfIntegers.mapAlgEquiv (IsCMField.complexConj E)
  have hcxo : cO xo = -xo := by
    apply RingOfIntegers.ext
    change IsCMField.complexConj E x = -x
    exact complexConj_eq_neg_of_sq_eq_neg_natCast E d hd0 x hx
  have hne : Ideal.span {((2 * d : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (by omega : 2 * d ≠ 0)
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors hne).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra h2d
  apply hw
  intro hprime
  obtain ⟨n, hn⟩ := exists_intCast_eq_of_card_prime (𝓞 E ⧸ w.asIdeal) (normV w) hprime rfl
    (Ideal.Quotient.mk _ xo)
  have hxn : xo - n ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hn]
    simp
  unfold UsPl
  refine ⟨?_, ?_⟩
  · unfold IsSplitAt
    let u : HeightOneSpectrum (𝓞 E) :=
      { asIdeal := w.asIdeal.comap (cO.toRingEquiv : 𝓞 E →+* 𝓞 E)
        isPrime := Ideal.comap_isPrime _ _
        ne_bot := by
          intro h
          apply w.ne_bot
          have := Ideal.map_comap_of_surjective (cO.toRingEquiv : 𝓞 E →+* 𝓞 E)
            cO.surjective w.asIdeal
          rw [h, Ideal.map_bot] at this
          exact this.symm }
    refine ⟨u, ?_, ?_⟩
    · intro huw
      have hmem : ∀ a, a ∈ w.asIdeal → cO a ∈ w.asIdeal := by
        intro a ha
        have : a ∈ u.asIdeal := by rw [huw]; exact ha
        exact this
      have h1 := hmem _ hxn
      rw [map_sub, hcxo, map_intCast] at h1
      have h2 : 2 * xo ∈ w.asIdeal := by
        have := w.asIdeal.sub_mem hxn h1
        convert this using 1
        ring
      apply h2d
      have h3 := w.asIdeal.mul_mem_right (-xo) h2
      convert h3 using 1
      have : ((2 * d : ℕ) : 𝓞 E) = -2 * (-(d : 𝓞 E)) := by push_cast; ring
      rw [this, ← hxo]
      ring
    · apply HeightOneSpectrum.ext
      change Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
          (Ideal.comap (cO.toRingEquiv : 𝓞 E →+* 𝓞 E) w.asIdeal) =
        Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) w.asIdeal
      rw [Ideal.comap_comap]
      congr 1
      ext y
      exact congrArg Subtype.val (cO.commutes y)
  · intro q hq hqw
    haveI := Fact.mk hq
    unfold SqAt
    have hm : ((n ^ 2 + d : ℤ) : 𝓞 E) ∈ w.asIdeal := by
      have : ((n ^ 2 + d : ℤ) : 𝓞 E) = (xo - n) * (-(xo + n)) := by
        push_cast
        linear_combination hxo
      rw [this]
      exact w.asIdeal.mul_mem_right _ hxn
    have hdiv := prime_dvd_of_intCast_mem_of_natCast_mem w.asIdeal q hq hqw _ hm
    have hq2d : ¬ (q : ℤ) ∣ 2 * d := by
      rintro ⟨k, hk⟩
      apply h2d
      have : ((2 * d : ℕ) : 𝓞 E) = (q : 𝓞 E) * (k : 𝓞 E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 E)) hk
        push_cast at this ⊢
        exact this
      rw [this]
      exact w.asIdeal.mul_mem_right _ hqw
    have h2n : ¬ (q : ℤ) ∣ 2 * n := by
      intro h
      apply hq2d
      have e : (2 * d : ℤ) = 2 * (n ^ 2 + d) - (2 * n) * n := by ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_right hdiv 2) (dvd_mul_of_dvd_left h n)
    exact isSquare_neg_padic_of_dvd_sq_add_of_not_dvd q (d : ℤ) n hdiv h2n
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.RamUnr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Int.Core

theorem ramUnr_holds : RamUnr := by
  intro F Ω _ _ _ _ _ T Q hQ
  obtain ⟨u, huT, A, hA, τ, hτ, hfix⟩ := hQ
  haveI : Algebra.IsQuadraticExtension F ↥Q.K := ⟨Q.two⟩
  haveI : IsGalois F ↥Q.K := inferInstance
  obtain ⟨w, hw, hwu⟩ := CompanionTheory.FamInh.exists_place_between (K := F) (L := ↥Q.K) hA
  have hunder : w.under (𝓞 F) = u :=
    ReciprocityTheory.Gal.eq_of_isPlaceOver (fun x => by
      rw [IsScalarTower.algebraMap_apply F ↥Q.K Ω]
      exact hw (algebraMap (𝓞 F) (𝓞 ↥Q.K) x)) hA
  refine ⟨w, fun hun => hfix fun x => ?_, hunder ▸ huT⟩
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hs := CompanionTheory.FamInh.res_mem_inertia (L := ↥Q.K) hw hτ
  rw [(CompanionTheory.FamInh.inertia_eq_bot_iff u w).2 he, Subgroup.mem_bot] at hs
  have hc := AlgEquiv.restrictNormal_commutes τ ↥Q.K x
  have h1 : AlgEquiv.restrictNormal τ ↥Q.K x = x := DFunLike.congr_fun hs x
  rw [h1] at hc
  exact hc.symm

end UpperTheory.Gal.Int.Core
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PhiPol
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

theorem UpperTheory.Gal.Int.Core.phiPol_holds :
    PhiPol := by
  intro F Ω _ _ _ _ _ A w h x y σ hs
  have split : ∀ z : WD h, ((z.charPol σ).roots.map fun a => X - C a).prod = z.charPol σ := by
    intro z
    induction z using WD.ind with
    | hP n a =>
      rw [WD.charPol_mk]
      exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (LinearMap.charpoly_monic _)
        (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have hc : Multiset.card (x.charPol σ).roots = Multiset.card (y.charPol σ).roots := by
    have h0 := hs 0
    simp only [GlobalTheory.CongPhi.phiSum, pow_zero, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one] at h0
    exact_mod_cast h0
  rw [← split x, ← split y]
  exact GlobalTheory.CharpolyNewton.prod_eq_of_psum_eq _ _ hc hs
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.AutTHolds
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open GlobalTheory.PRep Formalism.UG GlobalTheory.BCT

theorem UpperTheory.Gal.Int.Core.autT_holds : UpperTheory.Gal.Int.Core.AutT := by
  classical
  intro E _ _ _ a U hU
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU (E := E) (n := a))) := (hU.aut φ hφ).level
  have hunr : ∀ᶠ w in Filter.cofinite, IsUnramU U w := by
    filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E a L hLo] with w hw
    exact ⟨φ, hφ, hφ0, fun x hx hxK => hw x hx hxK hx.1⟩
  have hfin : {w | ¬ IsUnramU U w}.Finite := hunr
  refine ⟨hfin.toFinset.filter (fun w => ¬ IsSplitAt w), fun w hw => (Finset.mem_filter.1 hw).2, hU, fun w hs hT => ?_⟩
  by_contra hn
  exact hT (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hn, hs⟩)
end

namespace UpperTheory.Gal.Int.Core

open UpperTheory.Gal.TP

theorem joinU_holds : JoinU :=
  joinU_of oneUs_holds isoOne_holds phiPol_holds autT_holds Sub.satAE_holds Sub.clConj Sub.satPol_holds Sub.clAway_holds

theorem subtractQ_holds : SubtractQ :=
  subtractQ_of Sub.charEx Sub.satAE_holds (Sub.denseId_holds Sub.cpFacts_holds Sub.dgFacts_holds) Sub.cpFacts_holds Sub.peelAll
    Sub.clTw Sub.contLeft_holds Sub.sSLeft_holds Sub.satPol_holds Sub.clConj

theorem joinAll_holds : JoinAll := joinAll_of oneUs_holds subtractQ_holds

theorem sphDown_holds : ∀ c, SphDown c
  | .unr => downUnr_holds
  | .dR => downDR_holds
  | .crys => downCrys_holds
  | .phi => downPhi_holds

theorem stepDown_holds : StepDown :=
  stepDown_of isoOne_holds (patchOne_holds isoOne_holds oneTower_holds oneConj_holds) sphDown_holds

theorem joinUp_holds : JoinUp :=
  joinUp_of' stepDown_holds csdLift_holds ramUnr_holds oneUs_holds exists_quadratic_CM_ext_split_at

theorem rowCsd_of (hT : TwoUpOK) (hD : GlobalTheory.Cong.DescOffT) (hL : LimU) : RowCsd :=
  joinUp_holds PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity UpperTheory.Gal.AbelianGaloisNormality.gk_holds
    (GlobalTheory.QuadLiftBridge.quadLift UpperTheory.Gal.AbelianGaloisNormality.strongTC_holds PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity)
    (joinGL_holds hD (joinAll_holds hT (joinU_holds hL)))

theorem core_of_limU (hT : TwoUpOK) (hD : GlobalTheory.Cong.DescOffT) (hL : LimU) : GlobalTheory.RoadU.Core :=
  GlobalTheory.RoadW.core_of_rowStarCore (joinEnd_holds (rowCsd_of hT hD hL))

theorem core_of_limOdd (hT : TwoUpOK) (hC : GlobalTheory.CongPhi.ClosedPhi) (hD : GlobalTheory.Cong.DescOffT) (hL : LimOdd) : GlobalTheory.RoadU.Core :=
  core_of_limU hT hD (limU_of_limOdd hC hL)

theorem limOdd_of_limFinOdd (h : GlobalTheory.CongL.LimFinOdd) : LimOdd := fun E Ω _ _ _ _ _ _ l _ ι a ha => h E Ω l ι a ha.pos ha

theorem toCore (hT : TwoUpOK) : GlobalTheory.CongPhi.ClosedPhi → GlobalTheory.Cong.DescOffT → GlobalTheory.CongL.LimFinOdd → GlobalTheory.RoadU.Core :=
  fun hC hD hL => core_of_limOdd hT hC hD (limOdd_of_limFinOdd hL)

end UpperTheory.Gal.Int.Core
end

namespace UpperTheory.Gal.Int.Core

theorem toCoreK (hT : UpperTheory.TP.TLiftK) :
    GlobalTheory.CongPhi.ClosedPhi → GlobalTheory.Cong.DescOffT → GlobalTheory.CongL.LimFinOdd → GlobalTheory.RoadU.Core :=
  toCore (UpperTheory.Gal.TP.twoUpOK_of_k hT)

end UpperTheory.Gal.Int.Core
