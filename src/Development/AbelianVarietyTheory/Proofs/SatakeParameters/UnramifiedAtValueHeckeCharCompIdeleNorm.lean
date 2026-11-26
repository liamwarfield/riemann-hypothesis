module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.NormValGen

theorem valuation_eq_pow_of_norm_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [toAdd_pow, nsmul_eq_mul, WithZero.toAdd_unzero_eq_log,
    WithZero.toAdd_unzero_eq_log, h2]

theorem loc_eq_of_comp_norm {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (ψ : HChar K) (ψ' : HChar M) (hψ : ∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x))
    (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion M)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      ψ'.loc w x = ψ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion M) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, (hψ _).trans (congrArg ψ.1 h), valuation_eq_pow_of_norm_eq _ w _ x hm' f hf⟩

theorem unrAt_val_of_comp_norm : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (ψ : HChar K) (ψ' : HChar M), (∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x)) → ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f → ψ.UnrAt (w.under (𝓞 K)) → ψ'.UnrAt w ∧ ψ'.val w = ψ.val (w.under (𝓞 K)) ^ f := by
  intro K M _ _ _ _ _ ψ ψ' hψ w f hf hu
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := loc_eq_of_comp_norm ψ ψ' hψ w f hf x
    rw [hy]
    apply hu
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := loc_eq_of_comp_norm ψ ψ' hψ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hunit : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hu _ hunit
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3

end GlobalTheory.NormValGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNormStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedAt_value_heckeChar_comp_ideleNorm : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (ψ : HChar K) (ψ' : HChar M), (∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x)) → ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f → ψ.UnrAt (w.under (𝓞 K)) → ψ'.UnrAt w ∧ ψ'.val w = ψ.val (w.under (𝓞 K)) ^ f := by
  first | exact @GlobalTheory.NormValGen.unrAt_val_of_comp_norm | exact GlobalTheory.NormValGen.unrAt_val_of_comp_norm | (intros; apply GlobalTheory.NormValGen.unrAt_val_of_comp_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointOfConditions
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowPointLoc

theorem continuous_of_adic {A B : Type} [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [IsLocalRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (f : A ≃+* B) :
    Continuous f := by
  have hm : Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A) ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have := hu.map (f.symm : B →+* A)
    simpa using this
  refine continuous_of_continuousAt_zero (f : A →+ B) ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := ((isAdic_iff.1 hB).2 s hs)
  have hopen := (isAdic_iff.1 hA).1 n
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds (Ideal.zero_mem _)) ?_)
  intro x hx
  apply hn
  have h1 : f x ∈ Ideal.map (f : A →+* B) (IsLocalRing.maximalIdeal A ^ n) := Ideal.mem_map_of_mem _ hx
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono hm n h1

end GlobalTheory.RowPointLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem GlobalTheory.Cong.satake_locComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ → (∀ B, (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ ↔ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥) := by
  intro E _ _ _ a π w σ hσ
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := E) w a
  refine ⟨fun B => ⟨fun hB => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ h⟩, ?_⟩
  · have hB' : GlobalTheory.LFun.HasSatGL w (π.locRep w) B := hB
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
    obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred
      (fun f : LocSph.Maps π w σ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL w (n := a) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
      (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
      (by rw [LocSph.iSup_range_eq π w σ hσ]; exact x.2)
    obtain ⟨B', hB''⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
      ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
    exact (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hB'').unique hB' ▸ hB''
  · unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
    rw [hK]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_satake_iff_localComponent_satake : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ → (∀ B, (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ ↔ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥) := by
  first | (exact @GlobalTheory.Cong.satake_locComp) | (exact GlobalTheory.Cong.satake_locComp) | (intros; apply GlobalTheory.Cong.satake_locComp  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.SatBC

theorem normV_under_pow (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have norm_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [norm_eq, norm_eq]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem tendsto_under (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  haveI := v.isMaximal
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_) (fun _ _ _ _ h => HeightOneSpectrum.ext h)
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨by rw [← Set.mem_singleton_iff.1 hw, HeightOneSpectrum.under_asIdeal]⟩⟩

theorem isPlaceOver_under {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K Ω]
    [Algebra M Ω] [Algebra K M] [IsScalarTower K M Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 M)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
  rw [IsScalarTower.algebraMap_apply K M Ω]
  exact h (algebraMap (𝓞 K) (𝓞 M) x)

end GlobalTheory.AboveL.SatBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitary
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.SplitComp

theorem exists_comp_and_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → (∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ) ∧ ∀ σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ'.ρ → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  intro E _ _ _ a U hU w hw
  let π : GlobalTheory.DefU.AutSub E a := ⟨U, hU⟩
  refine ⟨?_, fun σ σ' hσ hσ' => ?_⟩
  · obtain ⟨σ, -, h, -⟩ := GlobalTheory.DefU.exists_locComp_split E a π w hw
    exact ⟨σ, h⟩
  · obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E a w hw
    obtain ⟨r, -, -, hr2⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E a w
    set p : locU a w →* GL (Fin a) (w.adicCompletion E) := (cLoc w).comp (locU a w).subtype with hpdef
    have hp : p = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
    have hsurj : ∀ g, p (e.symm g) = g := fun g => by
      rw [hp]; exact e.apply_symm_apply g
    have hirr : ∀ τ : SmIrr (GL (Fin a) (w.adicCompletion E)), Representation.IsIrreducible (τ.ρ.comp p) := fun τ => by
      rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv τ.ρ e.toMulEquiv τ.irred
    have hmap : ∀ τ : SmIrr (GL (Fin a) (w.adicCompletion E)),
        IsCompAlong U (locU a w) p τ.ρ → ∃ F : Representation.IntertwiningMap (τ.ρ.comp p) (π.rep.comp (locU a w).subtype), F ≠ 0 := by
      rintro τ ⟨-, f, hf0, hfm, hf⟩
      refine ⟨⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩, fun h => hf0 ?_⟩
      exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v)
    obtain ⟨F, hF⟩ := hmap σ hσ
    obtain ⟨F', hF'⟩ := hmap σ' hσ'
    obtain ⟨T⟩ := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E a) (locU a w) π.V σ.V σ'.V π.rep (locU a w).subtype
      (σ.ρ.comp p) (σ'.ρ.comp p) π.isIrreducible_rep (hirr σ) (hirr σ')
      (fun g => ⟨r g, fun y => hr2 g y⟩) F hF).2 F' hF'
    refine ⟨Representation.Equiv.mk' ⟨T.toLinearEquiv.toLinearMap, fun g => ?_⟩ T.toLinearEquiv.invFun
      T.toLinearEquiv.left_inv T.toLinearEquiv.right_inv⟩
    have := T.isIntertwining' (e.symm g)
    rw [← hsurj g]
    exact this

end GlobalTheory.SplitComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitaryStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → (∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ) ∧ ∀ σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ'.ρ → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  first | (exact @GlobalTheory.SplitComp.exists_comp_and_unique) | (exact GlobalTheory.SplitComp.exists_comp_and_unique) | (intros; apply GlobalTheory.SplitComp.exists_comp_and_unique  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRep
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRep
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.Cong

theorem exists_weight_of_isAutRepU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ)
    (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∃ lam : (E →+* ℂ) → DomWeight a, ∀ τ, HasWeightAt U τ (lam τ) := by
  intro E _ _ _ a U hU
  choose lam hlam using fun τ : E →+* ℂ => (GlobalTheory.DefU.AU.existsUnique_hasWt E a (GlobalTheory.DefU.AU.mk ⟨U, hU⟩) τ).exists
  exact ⟨lam, hlam⟩

end GlobalTheory.Cong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRepStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
theorem _root_.GlobalTheory.T.exists_algebraicWeight_definiteUnitaryAutRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∃ lam : (E →+* ℂ) → DomWeight a, ∀ τ, HasWeightAt U τ (lam τ) := by
  first | exact @GlobalTheory.Cong.exists_weight_of_isAutRepU | exact GlobalTheory.Cong.exists_weight_of_isAutRepU | (intros; apply GlobalTheory.Cong.exists_weight_of_isAutRepU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepConjInvariant
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open TensorProduct Module GlobalTheory.CoeffExt
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL.RepConj

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_iff : IsSst P ρ ↔ finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] ↥(K0 K) * finrank ℚ_[l] V := by
  have := L.2
  rw [IsSst, ← finrank_mul_finrank ℚ_[l] ↥L.1 V, ← finrank_mul_finrank ℚ_[l] ↥L.1 ↥(Dst P ρ), mul_left_comm]
  exact (Nat.mul_right_inj finrank_pos.ne').symm

theorem finrank_pi_card {k M ι : Type} [Field k] [AddCommGroup M] [Module k M] [Fintype ι] :
    finrank k (ι → M) = Fintype.card ι * finrank k M := by
  rw [finrank, rank_fun, Cardinal.toNat_mul, Cardinal.toNat_natCast, finrank]

theorem isSst_of_coord (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ) : IsSst P ρ' := by
  have hm : ∀ x : V' ⊗[ℚ_[l]] Bst P, x ∈ Dst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dst P ρ := fun x => by
    simp only [mem_Dst]
    refine ⟨fun hx i g => by rw [← GlobalTheory.PstExt.tensCoord_stRep P hE, hx g], fun hx g => ?_⟩
    exact (tensCoord E (Bst P)).injective (funext fun i => by rw [GlobalTheory.PstExt.tensCoord_stRep P hE, hx i g])
  let e : ↥(Dst P ρ') ≃ₗ[ℚ_[l]] (ι → ↥(Dst P ρ)) :=
    { toFun := fun x i => ⟨tensCoord E (Bst P) x.1 i, (hm _).1 x.2 i⟩
      invFun := fun y => ⟨(tensCoord E (Bst P)).symm fun i => (y i).1, (hm _).2 fun i => by
        rw [LinearEquiv.apply_symm_apply]; exact (y i).2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
      map_smul' := fun c x => funext fun i =>
        Subtype.ext (congrFun (((tensCoord E (Bst P)).restrictScalars ℚ_[l]).map_smul c x.1) i)
      left_inv := fun x => Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
      right_inv := fun y => funext fun i =>
        Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i) }
  rw [isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, finrank_pi_card, finrank_pi_card, h, mul_left_comm]

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1)
    (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1) (h : IsSst P (Bw.repE L₁ r₁)) :
    IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsSstAt P Bw r) : IsSstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  refine ⟨L₂, r₂, hm, isSst_of_coord P (ι := Unit) (E := e.symm.trans (LinearEquiv.funUnique Unit _ _).symm)
    (fun g x _ => ?_) (isSst_enlarge P Bw hL r₁ hp)⟩
  change e.symm _ = Bw.repE L₂ _ g (e.symm x)
  rw [e.symm_apply_eq, he, e.apply_symm_apply]

theorem isPstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsPstAt P Bw r) : IsPstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩

theorem wdAt_conj [NumberField E] [IsAlgClosure E Ω] (ι : Om l ≃+* ℂ) {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
    {r r' : ↥(Dec (F := E) A) →* GL (Fin m) (Om l)} (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) :
    wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  by_cases hr : IsPstAt P Bw r
  · exact GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr (isPstAt_conj P Bw p hc hr)
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, wdAt_of_not_isPstAt ι Bw h hj fun hr' =>
      hr (isPstAt_conj P Bw p⁻¹ (fun g => by rw [hc]; group) hr')]

end GlobalTheory.AboveL.RepConj

namespace GlobalTheory.AboveL

open GlobalTheory.AboveL.RepConj

end GlobalTheory.AboveL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCMFieldOfForallIsConj
open NumberField NumberField.ComplexEmbedding

namespace GlobalTheory.CMFieldCriterion

theorem isTotallyReal_fixedField (K : Type) [Field K] [NumberField K] {σ : Gal(K/ℚ)}
    (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) :
    IsTotallyReal (IntermediateField.fixedField (Subgroup.zpowers σ)) := by
  refine ⟨fun w => ?_⟩
  obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
  dsimp only
  rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
    ComplexEmbedding.isReal_iff]
  ext x
  have hx : σ (x : K) = x :=
    (IntermediateField.mem_fixedField_iff _ _).mp x.2 σ (Subgroup.mem_zpowers σ)
  have h := (hσ W.embedding).eq (x : K)
  rw [hx] at h
  rw [conjugate_coe_eq]
  exact h.symm

theorem isCMField_of_forall_isConj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    {σ : Gal(K/ℚ)} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : σ ≠ 1 :=
    (isConj_ne_one_iff (hσ φ)).mpr (IsTotallyComplex.complexEmbedding_not_isReal φ)
  have hcard : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ hne
    ext x
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact isConj_apply_apply (hσ φ) x
  have hreal := isTotallyReal_fixedField K hσ
  have hquad :
      Algebra.IsQuadraticExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K :=
    { finrank_eq_two' := by rw [IntermediateField.finrank_fixedField_eq_card, hcard] }
  exact IsCMField.ofCMExtension (IntermediateField.fixedField (Subgroup.zpowers σ)) K

end GlobalTheory.CMFieldCriterion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosed
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.CMSub

section Crit

open ComplexEmbedding InfinitePlace IntermediateField

theorem isCMField_of_forall_isConj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    {σ : K ≃ₐ[ℚ] K} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  first
  | exact @_root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj
  | exact _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj
  | (apply _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj ..)

end Crit

def conjStable (Ω : Type) [Field Ω] : Subfield Ω where
  carrier := {x | ∃ y : Ω, ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x)}
  mul_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y * z, fun φ => by simp [hy, hz]⟩
  one_mem' := ⟨1, fun φ => by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, fun φ => by simp [hy, hz]⟩
  zero_mem' := ⟨0, fun φ => by simp⟩
  neg_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨-y, fun φ => by simp [hy]⟩
  inv_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨y⁻¹, fun φ => by simp [hy]⟩

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]

theorem nonempty_ringHom_complex (E Ω : Type) [Field Ω] [Field E] [NumberField E] [Algebra E Ω]
    [IsAlgClosure E Ω] : Nonempty (Ω →+* ℂ) := by
  let ψ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  letI : Algebra E ℂ := ψ.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact ⟨(IsAlgClosed.lift : Ω →ₐ[E] ℂ).toRingHom⟩

theorem exists_extend (M : IntermediateField E Ω) (ψ : M →+* ℂ) :
    ∃ φ : Ω →+* ℂ, ∀ x : M, φ x = ψ x := by
  letI : Algebra M ℂ := ψ.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := E) M
  let f : Ω →ₐ[M] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem mem_of_conj {L : IntermediateField E Ω} {x y : Ω} (hx : x ∈ L)
    (hy : ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x)) : y ∈ L := by
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨φ₀⟩ := nonempty_ringHom_complex E Ω
  rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  have hτx : τ x = x := (mem_fixingSubgroup_iff _).mp hτ x hx
  apply φ₀.injective
  have h1 : φ₀ (τ y) = starRingEnd ℂ (φ₀ (τ x)) := hy (φ₀.comp τ.toRingHom)
  rw [h1, hτx, hy φ₀]

theorem algebraMap_mem_conjStable [IsCMField E] (e : E) : algebraMap E Ω e ∈ conjStable Ω :=
  ⟨algebraMap E Ω (IsCMField.complexConj E e), fun φ =>
    IsCMField.complexEmbedding_complexConj E (φ.comp (algebraMap E Ω)) e⟩

def conjField (E Ω : Type) [Field Ω] [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] :
    IntermediateField E Ω :=
  (conjStable Ω).toIntermediateField algebraMap_mem_conjStable

theorem le_conjField [IsCMField E] (M : IntermediateField E Ω) [NumberField M] [IsCMField M] :
    M ≤ conjField E Ω := fun x hx =>
  ⟨(IsCMField.complexConj M ⟨x, hx⟩ : M), fun φ =>
    IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M Ω)) ⟨x, hx⟩⟩

theorem isCMField_of_le [IsCMField E] (M : IntermediateField E Ω) [NumberField M]
    (h : M ≤ conjField E Ω) : IsCMField M := by
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra E M
  have hc : ∀ x : M, ∃ y : M, ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x) := fun x => by
    obtain ⟨y, hy⟩ := h x.2
    exact ⟨⟨y, mem_of_conj x.2 hy⟩, hy⟩
  choose c hc using hc
  obtain ⟨φ₀⟩ := nonempty_ringHom_complex E Ω
  have inj : ∀ a b : M, φ₀ a = φ₀ b → a = b := fun a b hab => Subtype.ext (φ₀.injective hab)
  let f : M →+* M :=
    { toFun := c
      map_one' := inj _ _ (by simp [hc])
      map_mul' := fun a b => inj _ _ (by simp [hc])
      map_zero' := inj _ _ (by simp [hc])
      map_add' := fun a b => inj _ _ (by simp [hc]) }
  have hff : ∀ x, c (c x) = x := fun x => inj _ _ (by simp [hc])
  let g : M ≃+* M := RingEquiv.ofRingHom f f (by ext x; exact congrArg Subtype.val (hff x))
    (by ext x; exact congrArg Subtype.val (hff x))
  let σ : M ≃ₐ[ℚ] M := AlgEquiv.ofRingEquiv (f := g) (fun q => by
    rw [eq_ratCast (algebraMap ℚ M) q, map_ratCast])
  refine isCMField_of_forall_isConj M (σ := σ) fun ψ => ?_
  obtain ⟨φ, hφ⟩ := exists_extend M ψ
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  have e1 : ((σ : M →+* M) x) = c x := rfl
  rw [e1, ← hφ, ← hφ, hc]

theorem isCMField_sup_le_adjoin : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω], (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N] [NumberField ↥(M ⊔ N)], IsCMField M → IsCMField N → IsCMField ↥(M ⊔ N)) ∧ (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N], N ≤ M → IsCMField M → IsCMField N) ∧ ∀ (M : IntermediateField E Ω) [NumberField M] (S : Set Ω), (∀ x ∈ S, ∀ φ : Ω →+* ℂ, (φ x).im = 0) → M = IntermediateField.adjoin E S → IsCMField M := by
  intro Ω _ E _ _ _ _ _
  refine ⟨fun M N _ _ _ hM hN => isCMField_of_le _ (sup_le (le_conjField M) (le_conjField N)),
    fun M N _ _ hNM hM => isCMField_of_le _ (hNM.trans (le_conjField M)),
    fun M _ S hS hMS => isCMField_of_le _ ?_⟩
  rw [hMS, IntermediateField.adjoin_le_iff]
  intro x hx
  exact ⟨x, fun φ => (Complex.conj_eq_iff_im.mpr (hS x hx φ)).symm⟩

end GlobalTheory.CMSub

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosedStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_subfields_compositum_closed : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω], (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N] [NumberField ↥(M ⊔ N)], IsCMField M → IsCMField N → IsCMField ↥(M ⊔ N)) ∧ (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N], N ≤ M → IsCMField M → IsCMField N) ∧ ∀ (M : IntermediateField E Ω) [NumberField M] (S : Set Ω), (∀ x ∈ S, ∀ φ : Ω →+* ℂ, (φ x).im = 0) → M = IntermediateField.adjoin E S → IsCMField M := by
  first | exact @GlobalTheory.CMSub.isCMField_sup_le_adjoin | exact GlobalTheory.CMSub.isCMField_sup_le_adjoin | (intros; apply GlobalTheory.CMSub.isCMField_sup_le_adjoin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.Published

namespace GlobalTheory.QuadLiftBridge

theorem quadLift : ArthurClozelStrongTC → JacquetShalikaRigidity → GlobalTheory.GalCut.QuadLift := by
  intro hAC hJS K M _ _ _ _ _ _ _ h2 a ha π ⟨w, hw, B, hB⟩
  haveI : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  haveI : IsGalois K M := inferInstance
  refine hAC K M (h2 ▸ Nat.prime_two) a ha π fun η hη hST => ?_
  have hsm : CG.mk π = (CG.mk π).twist η := by
    refine JacquetShalikaRigidity.strong_multiplicity_one hJS ha _ _ (hST.mono fun v ⟨hu, B', h1, h3⟩ => ⟨B', h1, ?_⟩)
    have := h1.twist hu
    rwa [h3] at this
  exact GlobalTheory.T.cuspidal_twist_ramified_char_ne_self K a ha (CG.mk π) η _ B hB (GlobalTheory.T.quadratic_norm_hecke_char_ramified_below_ramified_prime K M h2 η hη w hw) hsm.symm

end GlobalTheory.QuadLiftBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUnique
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem cg_hasSat_unique : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : ℕ) (π : CG K a) (w : HeightOneSpectrum (𝓞 K)) (B B' : Multiset ℂˣ), π.HasSat w B → π.HasSat w B' → B = B' :=
  fun _ _ _ _ _ _ _ _ _ h h' => CG.HasSat.unique h h'

end GlobalTheory.AboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUniqueStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspRep_satakeParameters_unique : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : ℕ) (π : CG K a) (w : HeightOneSpectrum (𝓞 K)) (B B' : Multiset ℂˣ), π.HasSat w B → π.HasSat w B' → B = B' := by
  first | exact @GlobalTheory.AboveL.cg_hasSat_unique | exact GlobalTheory.AboveL.cg_hasSat_unique | (intros; apply GlobalTheory.AboveL.cg_hasSat_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPow
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPow
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.ResDeg

theorem normV_eq_under_pow : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f := by
  intro K M _ _ _ _ _ w
  refine ⟨w.asIdeal.inertiaDeg (𝓞 K), ?_⟩
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

end GlobalTheory.AboveL.ResDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPowStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normV_eq_normV_under_pow : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f := by
  first | exact @GlobalTheory.AboveL.ResDeg.normV_eq_under_pow | exact GlobalTheory.AboveL.ResDeg.normV_eq_under_pow | (intros; apply GlobalTheory.AboveL.ResDeg.normV_eq_under_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnder
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnder
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.ConjUnder

theorem complexConj_algebraMap {K M : Type} [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : K) :
    IsCMField.complexConj M (algebraMap K M x) = algebraMap K M (IsCMField.complexConj K x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K M)) x).symm

theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

theorem cPl_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (w : HeightOneSpectrum (𝓞 M)),
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ _ _ w
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact complexConj_algebraMap (x : K)

end GlobalTheory.ConjUnder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnderStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.under_conjugatePlace_eq_conjugatePlace_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.ConjUnder.cPl_under | exact GlobalTheory.ConjUnder.cPl_under | (intros; apply GlobalTheory.ConjUnder.cPl_under <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroup
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.OpenNormal

theorem exists_open_normal_le : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → ∃ N : Subgroup (G F Ω), N.Normal ∧ IsOpen (N : Set (G F Ω)) ∧ N.FiniteIndex ∧ N ≤ U := by
  intro Ω _ F _ _ _ _ U hU
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  haveI : CompactSpace (G F Ω) := inferInstanceAs (CompactSpace Gal(Ω/F))
  haveI : Finite (G F Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨U.normalCore, U.normalCore_normal, ?_, inferInstance, U.normalCore_le⟩
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (U.normalCore_isClosed (U.isClosed_of_isOpen hU))

end GlobalTheory.OpenNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroupStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openNormal_finiteIndex_le_absGaloisGroup : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → ∃ N : Subgroup (G F Ω), N.Normal ∧ IsOpen (N : Set (G F Ω)) ∧ N.FiniteIndex ∧ N ≤ U := by
  first | exact @GlobalTheory.OpenNormal.exists_open_normal_le | exact GlobalTheory.OpenNormal.exists_open_normal_le | (intros; apply GlobalTheory.OpenNormal.exists_open_normal_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlace
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
namespace GlobalTheory

theorem eventually_cofinite_under_of_eventually_cofinite :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      (P : HeightOneSpectrum (𝓞 K) → Prop), (∀ᶠ v in Filter.cofinite, P v) →
      ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, P (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  have hfib : ∀ v : HeightOneSpectrum (𝓞 K),
      ((fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) ⁻¹' {v}).Finite := by
    intro v
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
    refine ⟨w.isPrime, ⟨?_⟩⟩
    rw [← hw]
    rfl
  exact (hP.preimage' fun v _ => hfib v).subset fun w hw => hw

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlaceStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_cofinite_under_of_eventually_cofinite_places : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (P : HeightOneSpectrum (𝓞 K) → Prop), (∀ᶠ v in Filter.cofinite, P v) → ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, P (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.eventually_cofinite_under_of_eventually_cofinite | exact GlobalTheory.eventually_cofinite_under_of_eventually_cofinite | (intros; apply GlobalTheory.eventually_cofinite_under_of_eventually_cofinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapNormEqOfMapPowEq
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem eig_pow_of_rep {K Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v} (x : WD h) (σ : Weil h) (k : ℕ) :
    x.eig (σ ^ k) = (x.eig σ).map (· ^ k) := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.eig_mk, WD.eig_mk, map_pow]
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow ℂ n k
    (LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) (a.ρ σ))
  rw [LinearMap.toMatrix_pow, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at h2
  exact h2

end GlobalTheory.AboveL

namespace GlobalTheory.AboveL

open Pointwise

end GlobalTheory.AboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorp
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorp
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem GlobalTheory.Cong.cLoc_locU_bijective_open_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Function.Bijective ((cLoc w).comp (locU a w).subtype) ∧ IsOpenMap ((cLoc w).comp (locU a w).subtype) ∧ Continuous ((cLoc w).comp (locU a w).subtype) := by
  intro E _ _ _ a w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hf : ((cLoc w).comp (locU a w).subtype : locU a w → GL (Fin a) (w.adicCompletion E)) = (fun x => e x) := by
    funext x
    exact (he x).symm
  rw [hf]
  exact ⟨e.bijective, e.toHomeomorph.isOpenMap, e.continuous⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorpStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Function.Bijective ((cLoc w).comp (locU a w).subtype) ∧ IsOpenMap ((cLoc w).comp (locU a w).subtype) ∧ Continuous ((cLoc w).comp (locU a w).subtype) := by
  first | (exact @GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (exact GlobalTheory.Cong.cLoc_locU_bijective_open_continuous) | (intros; apply GlobalTheory.Cong.cLoc_locU_bijective_open_continuous  <;> assumption)
end
end
