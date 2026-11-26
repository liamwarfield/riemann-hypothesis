module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.LiftPolar

theorem conj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E M)) x).symm

theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

theorem cPl_under {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (w : HeightOneSpectrum (𝓞 M)) :
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 E) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 E)) := by
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 E) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact conj_algebraMap (x : E)

theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (UpperTheory.V.Af.Bc.cPl w) = normV w := by
  show Nat.card (𝓞 E ⧸ (UpperTheory.V.Af.Bc.cPl w).asIdeal) = Nat.card (𝓞 E ⧸ w.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) ?_).toEquiv
  rw [cPl_asIdeal]
  exact (Ideal.map_comap_of_surjective
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E)
    (RingOfIntegers.mapRingEquiv _).surjective w.asIdeal).symm

theorem tendsto_under {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem normV_under {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Ideal.absNorm_eq_natCard]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem val_of_norm {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := by
    simpa only [normV, ← Ideal.absNorm_eq_natCard] using hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [toAdd_pow, WithZero.toAdd_unzero_eq_log, WithZero.toAdd_unzero_eq_log, nsmul_eq_mul, h2]

def normChar {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) :
    HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩

theorem normChar_loc {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion L)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      (normChar L χ).loc w x = χ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, congrArg χ.1 h, val_of_norm _ w _ x hm' f hf⟩

theorem normChar_val {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (w : HeightOneSpectrum (𝓞 L)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (hχ : χ.UnrAt (w.under (𝓞 K))) : (normChar L χ).UnrAt w ∧ (normChar L χ).val w = χ.val (w.under (𝓞 K)) ^ f := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := normChar_loc χ w f hf x
    rw [hy]
    apply hχ
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := normChar_loc χ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hu : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hχ _ hu
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3

theorem infIdele_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K w x = GroundTheory.Global.IdeleGroup.infiniteEmbedding w x := by
  classical
  refine Units.ext (Prod.ext (funext fun u => ?_) rfl)
  change Pi.mulSingle w (x : w.Completion) u = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (x : w.Completion) u
  rw [GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply]

theorem normChar_locInf {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (u : InfinitePlace L) (hu : u.IsReal) :
    (normChar L χ).locInf u (-1) = χ.locInf (u.comap (algebraMap K L)) (-1) := by
  have hv := hu.comap (algebraMap K L)
  show χ.1 (GroundTheory.Global.ideleNorm K L (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L u (-1))) =
    χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K (u.comap (algebraMap K L)) (-1))
  rw [infIdele_eq, infIdele_eq, GroundTheory.Global.ideleNorm_infiniteEmbedding]
  congr 2
  apply Units.ext
  apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
  have := GroundTheory.Global.extensionEmbeddingOfIsReal_normUnits (K := K) u hu (-1)
  rw [this]
  simp

theorem normCharGen : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) (s : ℂˣ), (∀ v : InfinitePlace K, v.IsReal → χ.locInf v (-1) = s) → ∃ χ' : HChar L, (∀ u : InfinitePlace L, u.IsReal → χ'.locInf u (-1) = s) ∧ ∀ u : HeightOneSpectrum (𝓞 L), χ.UnrAt (u.under (𝓞 K)) → χ'.UnrAt u ∧ ∀ f : ℕ, normV u = normV (u.under (𝓞 K)) ^ f → χ'.val u = χ.val (u.under (𝓞 K)) ^ f := by
  intro K L _ _ _ _ _ χ s hs
  refine ⟨normChar L χ, fun u hu => (normChar_locInf χ u hu).trans (hs _ (hu.comap _)), fun u hu => ?_⟩
  refine ⟨(normChar_val χ u _ (normV_under u) hu).1, fun f hf => (normChar_val χ u f hf hu).2⟩

theorem one_lt_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 1 < normV v := by
  have h := HeightOneSpectrum.one_lt_absNorm_nnreal v
  simp only [normV, ← Ideal.absNorm_eq_natCard]
  exact_mod_cast h

theorem algebraMap_mem_real {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : maximalRealSubfield E) : algebraMap E M x ∈ maximalRealSubfield M := by
  refine (IsCMField.complexConj_eq_self_iff M _).1 ?_
  rw [conj_algebraMap, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def realHom (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] : maximalRealSubfield E →+* maximalRealSubfield M :=
  ((algebraMap E M).comp (maximalRealSubfield E).subtype).codRestrict _ algebraMap_mem_real

theorem charLift : ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (a : ℕ) (χ : HChar (maximalRealSubfield E)), (∀ v : InfinitePlace (maximalRealSubfield E), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, (compNorm M χ').UnrAt w ∧ ∀ f : ℕ, normV w = normV (w.under (𝓞 E)) ^ f → (compNorm M χ').val w = (compNorm E χ).val (w.under (𝓞 E)) ^ f := by
  intro E M _ _ _ _ _ _ _ a χ hsign
  letI : Algebra (maximalRealSubfield E) (maximalRealSubfield M) := (realHom E M).toAlgebra
  obtain ⟨χ', hs, hv⟩ := normCharGen (maximalRealSubfield E) (maximalRealSubfield M) χ ((-1) ^ a) (fun v _ => hsign v)
  refine ⟨χ', fun u => hs u (IsTotallyReal.isReal u), ?_⟩
  have hNV := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility
  have hfin : ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite,
      χ.UnrAt ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E))) :=
    (tendsto_under (K := E) (L := M)).eventually ((tendsto_under (K := maximalRealSubfield E) (L := E)).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)))
  filter_upwards [hfin] with w hw
  have key : (w.under (𝓞 (maximalRealSubfield M))).under (𝓞 (maximalRealSubfield E)) =
      (w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)) := by
    apply HeightOneSpectrum.ext
    change (w.asIdeal.comap _).comap _ = (w.asIdeal.comap _).comap _
    rw [Ideal.comap_comap, Ideal.comap_comap]
    congr 1
  obtain ⟨hu1, hu2⟩ := hv (w.under (𝓞 (maximalRealSubfield M))) (by rw [key]; exact hw)
  obtain ⟨hw1, hw2⟩ := hNV M χ' w _ (normV_under w) hu1
  obtain ⟨-, hv2⟩ := hNV E χ (w.under (𝓞 E)) _ (normV_under _) hw
  refine ⟨hw1, fun f hf => ?_⟩
  rw [hw2, hu2 _ (normV_under _), hv2, key, ← pow_mul, ← pow_mul]
  congr 1
  refine Nat.pow_right_injective (one_lt_normV ((w.under (𝓞 E)).under (𝓞 (maximalRealSubfield E)))) ?_
  simp only
  rw [pow_mul, pow_mul, ← key, ← normV_under, ← normV_under, key, ← normV_under, ← hf]

theorem main : AutomorphicFormsFiniteGL → JacquetShalikaRigidity → GelfandKazhdanDual → ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (P : CuspSub M a), IsLift π P → InScope .all l π χ → (∃ χ' : HChar (maximalRealSubfield M), InScope .all l P χ') ∧ ∀ wt : ℤ, IsWeight π wt → IsWeight P wt := by
  intro hF hJ hG E M _ _ _ _ _ _ _ l a ha π χ P hL hS
  obtain ⟨hreg, hpol, -⟩ := hS
  refine ⟨?_, fun wt hw τ => ?_⟩
  · obtain ⟨χ', hsign, hev⟩ := charLift E M a χ hpol.sign
    refine ⟨χ', (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ⟨hsign, ?_⟩, trivial⟩
    · rw [hL.inf τ]
      exact (GlobalTheory.CuspRep.CG.isRegAlg_iff _).1 hreg _
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hJ hG M a ha P (compNorm M χ') ?_
    have hsd := GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace hF E a π χ hpol
    have hun := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep hF E a π
    filter_upwards [hev, (tendsto_under (K := E) (L := M)).eventually (hsd.and hun)] with w ⟨hu, hval⟩ ⟨hs, B, hB⟩
    have e1 := cPl_under (E := E) w
    have e2 := normV_cPl w
    have e3 := normV_cPl (w.under (𝓞 E))
    have hf := normV_under (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    have hB0 : (CG.mk π).HasSat (w.under (𝓞 E)) B := (CG.hasSat_mk _ _ _).2 hB
    have h1 := hL.sat w f B hf hB0
    have h2 := hL.sat (UpperTheory.V.Af.Bc.cPl w) f _ (by rw [e1, e2, e3]; exact hf) (e1 ▸ hs B hB0)
    refine ⟨hu, _, _, h1, h2, ?_⟩
    rw [hval f hf]
    simp only [Multiset.map_map, Function.comp_def, mul_pow, inv_pow, mul_inv, inv_inv]
  · rw [hL.inf, hL.inf]
    have e : (τ.comp (IsCMField.complexConj M).toRingEquiv.toRingHom).comp (algebraMap E M) =
        (τ.comp (algebraMap E M)).comp (IsCMField.complexConj E).toRingEquiv.toRingHom :=
      RingHom.ext fun x => congrArg τ (conj_algebraMap x)
    rw [e]
    exact hw _

end GlobalTheory.LiftPolar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeightStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarizedPair_baseChange_polarized_same_weight : AutomorphicFormsFiniteGL → JacquetShalikaRigidity → GelfandKazhdanDual → ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (P : CuspSub M a), IsLift π P → InScope .all l π χ → (∃ χ' : HChar (maximalRealSubfield M), InScope .all l P χ') ∧ ∀ wt : ℤ, IsWeight π wt → IsWeight P wt := by
  first | exact @GlobalTheory.LiftPolar.main | exact GlobalTheory.LiftPolar.main | (intros; apply GlobalTheory.LiftPolar.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameEqCoordMulInvMulBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameEqCoordMulInvMulBasis
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

section SlopeTestRemainingChoices
variable {E : Type} [Field E]
theorem toMatrix'_stdCo_reindex {n N : ℕ} (h : N = n) (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) :
    LinearMap.toMatrix' (stdCo σ (G.reindex (finCongr h) (finCongr h))).toLinearMap =
      (LinearMap.toMatrix' (stdCo σ G).toLinearMap).submatrix (Fin.cast h.symm) (Fin.cast h.symm) := by
  subst h
  simp

theorem toMatrix'_linEquiv_symm_mul {n : ℕ} (e : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  simp

theorem toMatrix'_toLE_eq {n : ℕ} (g : GL (Fin n) E) : LinearMap.toMatrix' (toLE g).toLinearMap = (g : Matrix (Fin n) (Fin n) E) := by
  simp only [toLE, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  exact LinearMap.toMatrix'_toLin' (g : Matrix (Fin n) (Fin n) E)

theorem toMatrix'_toLE_symm_eq {n : ℕ} (g : GL (Fin n) E) :
    LinearMap.toMatrix' (toLE g).symm.toLinearMap = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
  rw [Matrix.coe_units_inv, ← toMatrix'_toLE_eq]
  exact (Matrix.inv_eq_left_inv (toMatrix'_linEquiv_symm_mul _)).symm
end SlopeTestRemainingChoices

section Site
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)

theorem Joint.cp_iw_eq_rho (j : ℕ) (La : (sysS H X std).Lt j) (v : (sysS H X std).Pl) : (J.cp std).iw j La v = J.rho std v := by
  cases j with
  | zero => rfl
  | succ i =>
    simp only [Joint.cp, cpAt, chAt]
    split_ifs with hi
    · exact J.iw i hi _ v
    · rfl

theorem Joint.stdCo_cpJ_mat (j : ℕ) (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) :
    LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap =
      (LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap).submatrix (Fin.cast hr) (Fin.cast hr) := by
  cases j with
  | zero =>
    simp only [Joint.cp, cpAt, chAt]
    exact toMatrix'_stdCo_reindex _ _ _
  | succ i =>
    simp only [Joint.cp, cpAt, chAt, dif_pos hj]
    exact toMatrix'_stdCo_reindex _ _ _

theorem gMat_eq_mul (j : ℕ) (hj : j ≤ D.R.m) (γ : GL (Fin (D.R.N j)) D.host.E) :
    gMat J j hj γ = LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
      ((γ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) * (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)) := by
  unfold gMat toStdCo stdG
  simp only [LinearEquiv.coe_trans, LinearMap.toMatrix'_comp]
  rw [toMatrix'_toLE_eq, toMatrix'_toLE_symm_eq, mul_assoc (_ * _), ← mul_assoc (LinearMap.toMatrix' _), toMatrix'_linEquiv_symm_mul, one_mul,
    mul_assoc]
end Site

theorem changedFrame_eq_coord_mul_inv_mul_basis : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) La v, d.fd2.frM j La v = (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr) * ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La))).map (J.rho std v)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj hr La v
  have hU' : star (d.eM j La) * d.eM j La = 1 := mul_eq_one_comm.mp (GlobalTheory.T.decomposition_unitary_mul_star_eq_one S d j La)
  have hE : d.eM j La = (LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
      (((d.gam j hj La : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) *
        (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E))).submatrix
        (finCongr hr) (finCongr hr) := by
    rw [Dec.eM, dif_pos ⟨hj, hr⟩, gMat_eq_mul]
    rfl
  have hC : LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap =
      d.eM j La * (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix
        (finCongr hr) (finCongr hr)) := by
    rw [Joint.stdCo_cpJ_mat J std j hj hr La, hE, Matrix.submatrix_mul_equiv]
    have h1 : LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
        (((d.gam j hj La : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) *
          (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)) *
        (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E)) =
        LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap := by
      rw [Units.val_mul, mul_assoc, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
    rw [h1]
    rfl
  show (star (d.eM j La)).map (J.rho std v) * ((((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap) *
      ((J.cp std).B j La).1).map ((J.cp std).iw j La v)).submatrix (finCongr ((J.cp std).hk j La)) (finCongr ((J.cp std).hk j La))) = _
  rw [Joint.cp_iw_eq_rho, hC]
  change (star (d.eM j La)).map (J.rho std v) * (d.eM j La * (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) :
      Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)) * (show Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) D.host.E from ((J.cp std).B j La).1)).map (J.rho std v) =
    ((((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) :
      Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)) * (show Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) D.host.E from ((J.cp std).B j La).1)).map (J.rho std v)
  rw [← Matrix.map_mul, ← mul_assoc, ← mul_assoc, hU', one_mul]

end GlobalTheory.TwV.DelB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameEqCoordMulInvMulBasisStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frM_eq_map_crd_mul_gam_inv_mul_basis : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) La v, d.fd2.frM j La v = (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr) * ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La))).map (J.rho std v)) := by
  first | exact @GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis | exact GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis | (intros; apply GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitary
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem sigD_eq_star' (D : D7) (x : D.host.E) : (sigD D : D.host.E →+* D.host.E) x = star x := rfl

theorem cpB_eq_bAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)
  (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) :
    ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La)) =
      (bAt J j hj La.1).1.submatrix (Fin.cast h) (Fin.cast h) := by
  cases j with
  | zero => rfl
  | succ i =>
    show (chAt _ _ _ _ _ _ _ _ _ I _ _ _ _ (i + 1) La).B.1.submatrix _ _ = _
    simp only [chAt, dif_pos hj]
    rfl

theorem unitary_product_of_hermitian_relations {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ}
    (J c g B : Matrix (Fin N) (Fin N) E) (hc : cT σ c * c = J) (hg : cT σ g * J * g = J) (hB : cT σ B * J * B = 1) :
    star (c * g * B) * (c * g * B) = 1 := by
  have hs : star (c * g * B) = cT σ (c * g * B) := by
    ext i k
    simp only [cT, Matrix.star_apply, Matrix.transpose_apply, Matrix.map_apply, hσ]
  rw [hs, cT_mul, cT_mul]
  calc cT σ B * (cT σ g * cT σ c) * (c * g * B) = cT σ B * (cT σ g * (cT σ c * c) * g) * B := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hc, hg, hB]

theorem changed_frame_unitary : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j), StdU D (mM d j hj La) ∧ FrIs d.fd2 (J.rho std) j La h (mM d j hj La) ∧ (mM d j hj La).1.det * (d.gam j hj La).1.det = (uB J j hj La.1).1.det) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj h La
  have hB := (GlobalTheory.T.kernelSite_chartBasis_orthonormal_levelIndependent S j hj La.1).1
  have hc := J.pins.crd_orth j hj
  have hg' : (d.gam j hj La)⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D j hj) := inv_mem (d.mem j hj La)
  have hval : (mM d j hj La).1 = (J.A.crd j hj).1 * ((d.gam j hj La)⁻¹).1 * (bAt J j hj La.1).1 := by
    simp only [mM, Units.val_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold StdU
    rw [hval]
    exact unitary_product_of_hermitian_relations _ (sigD_eq_star' D) _ _ _ _ hc hg' hB
  · intro v
    rw [GlobalTheory.T.frM_eq_map_crd_mul_gam_inv_mul_basis S d j hj h La v, cpB_eq_bAt J std j hj h La,
      show ((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast h) (Fin.cast h) =
        ((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast h) (finCongr h) from rfl,
      show (bAt J j hj La.1).1.submatrix (Fin.cast h) (Fin.cast h) = (bAt J j hj La.1).1.submatrix (finCongr h) (Fin.cast h) from rfl,
      Matrix.submatrix_mul_equiv, ← Units.val_mul]
    rfl
  · have hdet : ((d.gam j hj La)⁻¹).1.det * (d.gam j hj La).1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [hval, uB, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    linear_combination ((J.A.crd j hj).1.det * (bAt J j hj La.1).1.det) * hdet

end GlobalTheory.TwV.DelA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitaryStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.changedFrame_rational_unitary : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j), StdU D (mM d j hj La) ∧ FrIs d.fd2 (J.rho std) j La h (mM d j hj La) ∧ (mM d j hj La).1.det * (d.gam j hj La).1.det = (uB J j hj La.1).1.det) := by
  first | exact @GlobalTheory.TwV.DelA.changed_frame_unitary | exact GlobalTheory.TwV.DelA.changed_frame_unitary | (intros; apply GlobalTheory.TwV.DelA.changed_frame_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SolvableAscentInduction
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.SolvUp

theorem exists_normal_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ H : Subgroup Γ, H.Normal ∧ H.index.Prime := by
  obtain ⟨H, hH, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : H.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H :=
      hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using H.mul_mem h1 hn⟩
  refine ⟨H, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ H)) (mt Subgroup.index_eq_one.1 hH.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' H) = ⊤ := by
    refine hH.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H g
      have hx : x ∈ H := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective H) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp

theorem isCMField_of_ringEquiv {A B : Type} [Field A] [NumberField A] [Field B] [NumberField B] [IsCMField A]
    (e : A ≃+* B) : IsCMField B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsTotallyComplex B := isTotallyComplex_of_algebra A B
  letI : Algebra (maximalRealSubfield A) B :=
    ((e : A →+* B).comp (algebraMap (maximalRealSubfield A) A)).toAlgebra
  let f : A ≃ₐ[maximalRealSubfield A] B := { e with commutes' := fun _ => rfl }
  haveI : Module.Free (maximalRealSubfield A) B := Module.Free.of_equiv f.toLinearEquiv
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield A) B :=
    ⟨by rw [← f.toLinearEquiv.finrank_eq]; exact Algebra.IsQuadraticExtension.finrank_eq_two _ _⟩
  exact IsCMField.ofCMExtension (maximalRealSubfield A) B

end GlobalTheory.SolvUp

namespace GlobalTheory.SolvUp

theorem isCMField_intermediate (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [Algebra K M]
    [IsScalarTower K M Ω] (L : IntermediateField K M) : IsCMField L := by
  let f := IsScalarTower.toAlgHom K M Ω
  haveI : NumberField f.fieldRange := NumberField.of_ringEquiv M _ (AlgEquiv.ofInjectiveField f).toRingEquiv
  haveI : NumberField (L.map f) := NumberField.of_ringEquiv L _ (IntermediateField.equivMap L f).toRingEquiv
  haveI : IsCMField f.fieldRange := isCMField_of_ringEquiv (AlgEquiv.ofInjectiveField f).toRingEquiv
  have hle : L.map f ≤ f.fieldRange := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (IntermediateField.mem_map L).1 hy
    exact AlgHom.mem_fieldRange.2 ⟨x, rfl⟩
  haveI : IsCMField (L.map f) := (GlobalTheory.T.cm_subfields_compositum_closed Ω K).2.1 f.fieldRange (L.map f) hle inferInstance
  exact isCMField_of_ringEquiv (IntermediateField.equivMap L f).symm.toRingEquiv

end GlobalTheory.SolvUp
end
end
