module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnlSph
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStableAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Unlinked
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.CbcSph
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.CoreId
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TorusCharComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.VarTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.VarEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJHolds

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.LocGal
open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open PositivityTheory.Rg.Tf.Geo
open scoped Classical NNReal ENNReal Pointwise

section Local

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k'] [FiniteDimensional k k']
  [IsModuleTopology k k']

private theorem cont_norm : Continuous (Algebra.norm k : k' → k) := by
  let b := Module.finBasis k k'
  have e : (Algebra.norm k : k' → k) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [e]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  have hl : Continuous ((b.coord i).comp (LinearMap.mulRight k (b j))) :=
    IsModuleTopology.continuous_of_linearMap _
  refine hl.congr fun x => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul]

private theorem nabs_norm [CharZero k] (x : k'ˣ) :
    GlobalTheory.SplitWeil.nabs k (Units.map (Algebra.norm k : k' →* k) x) = GlobalTheory.SplitWeil.nabs k' x := by
  borelize k'
  unfold GlobalTheory.SplitWeil.nabs
  congr 1
  symm
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : k')
  let μ : Measure k' := Measure.addHaar
  have h0 : μ K ≠ 0 :=
    (μ.measure_pos_of_nonempty_interior ⟨0, mem_interior_iff_mem_nhds.mpr hK0⟩).ne'
  have hf : μ K ≠ ∞ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) h0 hf ?_
  let T : k' ≃ₗ[k] k' := DistribMulAction.toLinearEquiv k k' x⁻¹
  have hT := GlobalTheory.T.map_linearEquiv_addHaar_localField k k' μ T
  have hdet : LinearEquiv.det T = (Units.map (Algebra.norm k : k' →* k) x)⁻¹ := by
    ext
    simp only [LinearEquiv.coe_det, T, Units.coe_map, MonoidHom.coe_coe, Algebra.norm_apply,
      Units.val_inv_eq_inv_val, map_inv₀]
    have hl : (↑(DistribMulAction.toLinearEquiv k k' x⁻¹) : k' →ₗ[k] k') =
        LinearMap.mul k k' ↑x⁻¹ := by
      ext y
      simp [Units.smul_def]
    rw [hl]
    apply eq_inv_of_mul_eq_one_left
    rw [← LinearMap.det_comp]
    have hc : (LinearMap.mul k k' ↑x⁻¹).comp (Algebra.lmul k k' ↑x) = LinearMap.id := by
      ext y
      simp
    rw [hc, LinearMap.det_id]
  have hm : MeasurableSet K := hK.isClosed.measurableSet
  have hTc : Continuous T := IsModuleTopology.continuous_of_linearMap (T : k' →ₗ[k] k')
  have e : Measure.map T μ K = (((distribHaarChar k) (LinearEquiv.det T))⁻¹ • μ) K := by
    rw [hT]
  rw [Measure.map_apply hTc.measurable hm, hdet, map_inv, inv_inv] at e
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  rw [← e]
  congr 1
  ext y
  simp [T, Set.mem_smul_set_iff_inv_smul_mem]

private theorem prod_aut [IsGalois k k'] {M : Type*} [CommMonoid M] (s : k' ≃ₐ[k] k') (hs : ∀ τ, τ ∈ Subgroup.zpowers s)
    (f : (k' ≃ₐ[k] k') → M) : ∏ τ, f τ = ∏ i ∈ Finset.range (Module.finrank k k'), f (s ^ i) := by
  have ho : orderOf s = Module.finrank k k' :=
    (orderOf_eq_card_of_forall_mem_zpowers hs).trans (IsGalois.card_aut_eq_finrank k k')
  calc ∏ τ, f τ = ∏ τ ∈ (Finset.range (orderOf s)).image (fun i => s ^ i), f τ := by
        rw [IsCyclic.image_range_orderOf hs]
    _ = ∏ i ∈ Finset.range (orderOf s), f (s ^ i) :=
        Finset.prod_image (fun i hi j hj h =>
          pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) h)
    _ = _ := by rw [ho]

private theorem iter_aut (s : k' ≃ₐ[k] k') (i : ℕ) (x : k') :
    (⇑(s : k' ≃+* k'))^[i] x = (s ^ i) x := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', AlgEquiv.mul_apply]
    rfl

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem val_gal (v : HeightOneSpectrum (𝓞 F)) (σ : E ≃ₐ[F] E) (w u : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver v.asIdeal] (h : u = σ • w) (y : w.adicCompletion E) :
    Valued.v (galEquiv v σ w u h y) = Valued.v y := by
  subst h
  have ev : ∀ (u : HeightOneSpectrum (𝓞 E)) (x : E),
      Valued.v (algebraMap E (u.adicCompletion E) x) = u.valuation E x :=
    fun u x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u x
  have key : ∀ x : E, Valued.v (galEquiv v σ w (σ • w) rfl (algebraMap E _ x)) =
      Valued.v (algebraMap E (w.adicCompletion E) x) := by
    intro x
    rw [galEquiv_algebraMap, ev, ev]
    exact valuation_smul σ w x
  by_cases hy : y = 0
  · simp [hy]
  have hy' : galEquiv v σ w (σ • w) rfl y ≠ 0 := by simpa using hy
  have h1 := Valued.locally_const ((Valuation.ne_zero_iff _).mpr hy)
  have h2 := (continuous_galEquiv v σ w (σ • w) rfl).continuousAt.preimage_mem_nhds
    (Valued.locally_const ((Valuation.ne_zero_iff _).mpr hy'))
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ :=
    (HeightOneSpectrum.denseRange_algebraMap E w).inter_nhds_nonempty (Filter.inter_mem h1 h2)
  have e1 : Valued.v (algebraMap E (w.adicCompletion E) x) = Valued.v y := hx.1
  have e2 : Valued.v (galEquiv v σ w (σ • w) rfl (algebraMap E _ x)) =
      Valued.v (galEquiv v σ w (σ • w) rfl y) := hx.2
  rw [← e2, key, e1]

private theorem galFin_eq (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hfix : w.1 = σ • w.1)
    (y : CompletionsOver E v) : galFin σ v y w = galEquiv v σ w.1 w.1 hfix (y w) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x a =>
    simp only [galFin, galOf, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe,
      AlgEquiv.symm_apply_apply]
    rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul]
    simp only [Pi.mul_apply, map_mul, Pi.algebraMap_apply, AlgHom.id_apply, AlgEquiv.commutes,
      galEquiv_algebraMap]
    rfl
  | add a b ha hb =>
    simp only [map_add (f := _), Pi.add_apply] at ha hb ⊢
    rw [ha, hb]

end Global

open scoped Valued in
theorem UpperTheory.Gal.Join.locGal :
    UpperTheory.Gal.Join.LocGal := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp v w hns
  obtain ⟨-, -, -, huniq, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  have hw : ∀ u : PlacesOver E v, u = w := huniq v hns w
  obtain ⟨A, hval, hfin, hgal, s, hs, hrk, hinc, hgf, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData F E σ hσ v w hw
  have hA : A = algebraCompletion v w.1 := Algebra.algebra_ext _ _ fun x => (hinc x).symm
  subst hA
  have hfix : w.1 = σ • w.1 := (congrArg Subtype.val (hw (σ • w))).symm
  have hse : ∀ z, s z = galEquiv v σ w.1 w.1 hfix z := fun z => by
    have h1 := hgf (Pi.single w z)
    rw [galFin_eq σ w hfix, Pi.single_eq_same] at h1
    exact h1.symm
  have hvs : ∀ z, Valued.v (s z) = Valued.v z := fun z => by
    rw [hse]
    exact val_gal v σ w.1 w.1 hfix z
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : IsModuleTopology (v.adicCompletion F) (w.1.adicCompletion E) := isModuleTopologyOfFiniteDimensional
  refine ⟨(s : _ ≃+* _), Units.map (Algebra.norm (v.adicCompletion F) : w.1.adicCompletion E →* _), fun n g => ?_,
    ⟨⟨fun x => ?_, ?_, fun x => ?_⟩, fun x => ?_, ?_, fun x => ?_⟩, fun x => rfl⟩
  · exact Units.ext (Matrix.ext fun a b => hgf _)
  · exact le_antisymm ((ValuativeRel.isEquiv (valuation _) Valued.v _ _).2 (hvs x).le)
      ((ValuativeRel.isEquiv (valuation _) Valued.v _ _).2 (hvs x).ge)
  · exact hp.pos
  · rw [iter_aut, ← hrk, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one']
    rfl
  · change algebraMap _ _ (Algebra.norm (v.adicCompletion F) (x : w.1.adicCompletion E)) = _
    rw [Algebra.norm_eq_prod_automorphisms, prod_aut s hs, hrk]
    exact Finset.prod_congr rfl fun i _ => (iter_aut s i _).symm
  · exact Continuous.units_map _ cont_norm
  · exact nabs_norm x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLiftOf
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.QuadLiftUnr
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftUnr
open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem UpperTheory.ConvolutionTheory.Sph.liftUnr :
    UpperTheory.ConvolutionTheory.Sph.LiftUnr := by
  intro K M _ _ _ _ _ _ _ _ hp a ha π hη
  obtain ⟨L, -, -⟩ := UpperTheory.ConvolutionTheory.cbcc K M hp inferInstance a ha
  rcases L (.cx π) with ⟨η, hη', e⟩ | ⟨P, hW, hinf, hS⟩
  · exact (hη η hη' (Quotient.sound e)).elim
  rcases P with @⟨_, P⟩ | @⟨hR, P⟩
  swap
  · exact (not_both M hR inferInstance).elim
  refine ⟨P, hW, fun w f B hu hf hB => ?_, fun τ => ?_, hS⟩
  · have hall : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) →
        Algebra.IsUnramifiedAt (𝓞 K) w'.asIdeal := by
      intro w' hw'
      by_contra hr
      obtain ⟨-, h2, -⟩ := UpperTheory.ConvolutionTheory.Sph.normRam K M hp w' hr
      have e' : w = w' := h2 w hw'.symm
      exact hr (e' ▸ hu)
    exact (UpperTheory.ConvolutionTheory.Sph.cbcSph K M hp inferInstance a ha (.cx π) (.cx P) hW (w.under (𝓞 K)) hall).1 B hB w rfl f hf
  · have h := hinf τ _ (ParLaws.hasInfChar_infChar (CG.mk π) (τ.comp (algebraMap K M)))
    exact CG.HasInfChar.infChar_eq (π := CG.mk P) h
end

open NumberField IsDedekindDomain

theorem UpperTheory.ConvolutionTheory.Sph.quadLiftUnr :
    UpperTheory.ConvolutionTheory.Sph.QuadLiftUnr := by
  intro K M _ _ _ _ _ _ _ h2 a ha π ⟨w, hram, B, hB⟩
  haveI : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  haveI : IsGalois K M := inferInstance
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  exact UpperTheory.ConvolutionTheory.Sph.liftUnr K M hp a ha π fun η hη =>
    GlobalTheory.T.cuspidal_twist_ramified_char_ne_self K a ha _ η (w.under (𝓞 K)) B hB ((UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hram).2.2 η hη)
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

private theorem normV_two_le {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  have e : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [e]
  have a := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have b := Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top
  omega

theorem UpperTheory.ConvolutionTheory.Sph.quadLiftOf :
    UpperTheory.ConvolutionTheory.Sph.RamSph → GlobalTheory.GalCut.QuadLift := by
  intro hR K M _ _ _ _ _ _ _ h2 a ha π hw
  obtain ⟨P, hP⟩ := UpperTheory.ConvolutionTheory.Sph.quadLiftUnr K M h2 a ha π hw
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  haveI : Algebra.IsQuadraticExtension K M := { finrank_eq_two' := h2 }
  haveI : IsGalois K M := Algebra.IsQuadraticExtension.isGalois K M
  refine ⟨P, ⟨fun w f B hf hB => ?_, hP.inf, hP.loc⟩⟩
  by_cases hu : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal
  · exact hP.sat w f B hu hf hB
  · have h1 := (UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hu).1
    have hf1 : f = 1 := by
      have h3 : normV (w.under (𝓞 K)) ^ 1 = normV (w.under (𝓞 K)) ^ f := by rw [pow_one, ← hf, h1]
      exact (Nat.pow_right_injective (normV_two_le _) h3).symm
    subst hf1
    have e : B.map (· ^ 1) = B := by simp
    rw [e]
    exact hR K M hp a ha π P hP.weak w hu B hB
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamSphOf
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SatDict
noncomputable section

open NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory.C GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

private theorem hasSat_iff {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (π : CuspSub K n)
    (v : HeightOneSpectrum (𝓞 K)) (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (hτ : π.IsLocComp v τ)
    (B : Multiset ℂˣ) : (Cusp.cx π).sat v B ↔ GlobalTheory.LFun.HasSatGL v τ.ρ B := by
  refine ⟨fun hB => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  have hB' : GlobalTheory.LFun.HasSatGL v (π.locRep v) B := hB
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep K n).comp (locGL K n v)) τ.ρ τ.irred
    (fun f : LocSph.Maps π v τ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL v (n := n) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
    (by rw [LocSph.iSup_range_eq π v τ hτ]; exact x.2)
  obtain ⟨B', hB''⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred
    ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
  exact (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ hB'').unique hB' ▸ hB''

private theorem isSpherical_iff {K : Type} [Field K] [NumberField K] {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) :
    IsSpherical τ.ρ ↔ GlobalTheory.PRep.fixed τ.ρ (GlobalTheory.LFun.KGL v (n := n)) ≠ ⊥ := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := K) v n
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [hK]

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
theorem UpperTheory.ConvolutionTheory.Sph.satDict :
    UpperTheory.ConvolutionTheory.Sph.SatDict := by
  refine ⟨1, Or.inl rfl, ?_⟩
  intro K _ _ _ n π v τ hτ
  have hτ' : π.IsLocComp v τ := hτ
  refine ⟨?_, fun hs => ?_, fun α hs hα => ?_⟩
  · rintro ⟨B, hB⟩
    exact (isSpherical_iff v τ).2 ((hasSat_iff π v τ hτ' B).1 hB).1
  · refine GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries
      ((GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness _).1 (Fin n) τ.V τ.ρ τ.smooth τ.irred) τ.irred ?_
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
    exact (Submodule.ne_bot_iff _).2 ⟨x, fun h => hx ⟨h.1, iwahori_le_KO _ _ h.2⟩, hx0⟩
  · have h := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake K v n τ.V τ.ρ α ⟨τ.irred, hs, hα⟩
    have e : (Finset.univ.val.map fun i => α i ^ (1 : ℤ)) = Finset.univ.val.map α := by simp
    rw [e]
    exact (hasSat_iff π v τ hτ' _).2 h
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnrNorm
namespace UpperTheory.ConvolutionTheory.Sph

private theorem zpow_inj_of_absNorm {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {a b : ℤ}
    (h : (Ideal.absNorm v.asIdeal : ℝ) ^ a = (Ideal.absNorm v.asIdeal : ℝ) ^ b) : a = b := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun e => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 e)
  have h2 : 1 < Ideal.absNorm v.asIdeal := by omega
  have h3 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast h2
  exact zpow_right_injective₀ (by linarith) h3.ne' h

theorem unrNorm : UnrNorm := by
  intro F E _ _ _ _ _ v w σw l N hN hq a
  refine MonoidHom.ext fun x => ?_
  have h := hN.abs x
  rw [GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.T.residue_card_eq_abs_norm F v, GlobalTheory.T.residue_card_eq_abs_norm E w.1, hq] at h
  have h' := zpow_inj_of_absNorm v h
  have h'' := neg_injective h'
  simp only [MonoidHom.comp_apply, GlobalTheory.SmGL.unrChar_apply, h'']

end UpperTheory.ConvolutionTheory.Sph
end

noncomputable section

open NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LocGL Formalism.BasicNotions UpperTheory.CBC PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.Sph

private theorem not_split_of_ramified {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (v : Pl K) (u : PlacesOver M v) (hram : ¬ Algebra.IsUnramifiedAt (𝓞 K) u.1.asIdeal) : ¬ GM.Split M v := by
  intro hs
  haveI := u.2
  have hb : Function.Bijective (Algebra.linearMap (v.adicCompletion K) (u.1.adicCompletion M)) :=
    ⟨(completionMap v u.1).injective, hs u⟩
  have h : u.1.asIdeal.ramificationIdx (𝓞 K) * u.1.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M v u.1, ← (LinearEquiv.ofBijective _ hb).finrank_eq,
      Module.finrank_self]
  exact hram (Ideal.ramificationIdx_eq_one_iff.1 (Nat.eq_one_of_mul_eq_one_right h))

private theorem unlinked_of {q : ℂ} {n : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (α : Fin n → ℂˣ)
    (h : ∀ a ∈ (Finset.univ.val.map fun i => α i ^ ε), ∀ b ∈ (Finset.univ.val.map fun i => α i ^ ε), (a : ℂ) ≠ q * b)
    (i j : Fin n) : (α i : ℂ) ≠ q * α j := by
  have hm : ∀ k, α k ^ ε ∈ (Finset.univ.val.map fun i => α i ^ ε) := fun k =>
    Multiset.mem_map_of_mem _ (Finset.mem_univ k)
  rcases hε with rfl | rfl
  · simpa using h _ (hm i) _ (hm j)
  · intro e
    apply h _ (hm j) _ (hm i)
    have hi : (α i : ℂ) ≠ 0 := (α i).ne_zero
    have hj : (α j : ℂ) ≠ 0 := (α j).ne_zero
    simp only [zpow_neg, zpow_one, Units.val_inv_eq_inv_val]
    rw [e]
    have hq : q ≠ 0 := fun h0 => hi (by rw [e, h0, zero_mul])
    field_simp

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
theorem UpperTheory.ConvolutionTheory.Sph.ramSphOf :
    UpperTheory.Gal.Join.LocGal → UpperTheory.Gal.Join.LiftGood → UpperTheory.ConvolutionTheory.Sph.RamSph := by
  intro hLG hLift K M _ _ _ _ _ _ _ _ hp n hn π P hW w hram B hB
  let v : Pl K := w.under (𝓞 K)
  have hlies : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  let u : PlacesOver M v := ⟨w, hlies⟩
  have hns : ¬ GM.Split M v := not_split_of_ramified v u hram
  obtain ⟨hN, -, -⟩ := UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hram
  have habs : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := by
    simpa [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply, v] using hN
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (p := Module.finrank K M) (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  obtain ⟨σw, N, hloc, hNorm, -⟩ := hLG K M σ hσ hp v u hns
  obtain ⟨ε, hε, hsd⟩ : SatDict := UpperTheory.ConvolutionTheory.Sph.satDict
  obtain ⟨hconj, hex, hex'⟩ := UpperTheory.ConvolutionTheory.Sph.weakStable K M hp n hn π P hW
  obtain ⟨τ, hτ⟩ := hex v
  obtain ⟨τ', hτ'⟩ := hex' w
  obtain ⟨d1, d2, d3⟩ := hsd K n π v τ hτ
  have hsph : IsSpherical τ.ρ := d1 ⟨B, hB⟩
  obtain ⟨α, hα⟩ := d2 hsph
  have hsat := d3 α hsph hα
  obtain rfl := SSatUniq_holds K n (.cx π) v _ _ hB hsat
  have hsub := hLift K M σ hσ hp n hn v u hns σw N (hloc n) hNorm π P hconj hW τ τ' hτ hτ'
    (fun i => unrChar (v.adicCompletion K) (α i)) (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ _)) hα
  have hcomp : ∀ i, (unrChar (v.adicCompletion K) (α i)).comp N = unrChar (w.adicCompletion M) (α i) := fun i =>
    UpperTheory.ConvolutionTheory.Sph.unrNorm K M v u σw _ N hNorm habs (α i)
  beta_reduce at hsub
  rw [funext hcomp] at hsub
  have hun := unlinked_of (q := (Ideal.absNorm w.asIdeal : ℂ)) hε α (by
    rw [habs]
    exact UpperTheory.ConvolutionTheory.Sph.unlinked K n hn π v _ hsat)
  have hsph' : IsSpherical τ'.ρ := UpperTheory.ConvolutionTheory.Sph.unlSph M n w τ' α hun hsub
  exact (hsd M n P w τ' hτ').2.2 α hsph' hsub
end
end

theorem UpperTheory.ConvolutionTheory.Sph.ramSph : UpperTheory.ConvolutionTheory.Sph.RamSph :=
  UpperTheory.ConvolutionTheory.Sph.ramSphOf UpperTheory.Gal.Join.locGal (UpperTheory.Gal.Join.liftGood
    (UpperTheory.Gal.Join.coreId UpperTheory.Gal.InertialTypesAlt.G.varEx UpperTheory.Gal.InertialTypesAlt.G.varTrace UpperTheory.Gal.InertialTypesAlt.L.elemPairJ_holds))

theorem UpperTheory.ConvolutionTheory.Sph.quadLift : GlobalTheory.GalCut.QuadLift := UpperTheory.ConvolutionTheory.Sph.quadLiftOf UpperTheory.ConvolutionTheory.Sph.ramSph
