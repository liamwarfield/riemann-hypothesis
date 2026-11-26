module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralIffSpectralNormLeOne
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ClosureIso

open Polynomial

section localPart

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 F)}

theorem exists_ne_zero_valued_lt_one (v : HeightOneSpectrum (𝓞 K)) :
    ∃ c : v.adicCompletion K, c ≠ 0 ∧ Valued.v c < 1 := by
  obtain ⟨x, hx⟩ := v.valuation_surjective K (WithZero.exp (-1))
  have hxv : Valued.v (algebraMap K (v.adicCompletion K) x) = WithZero.exp (-1) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans hx
  refine ⟨algebraMap K _ x, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero] at hxv
    exact WithZero.exp_ne_zero hxv.symm
  · rw [hxv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num

theorem valued_map_le_one (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f)
    {x : v.adicCompletion K} (hx : Valued.v x ≤ 1) : Valued.v (f x) ≤ 1 := by
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_valued_lt_one v
  have hN : ∀ N : ℕ, ‖f c‖ * ‖f x‖ ^ N < 1 := by
    intro N
    have h1 : Valued.v (c * x ^ N) < 1 := by
      rw [Valuation.map_mul, Valuation.map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one₀ zero_le hx)) hc1
    have h2 := GlobalTheory.ConjParahoric.val_lt_one_map f hf h1
    rw [← Valued.toNormedField.norm_lt_one_iff] at h2
    simpa [map_mul, map_pow, norm_mul, norm_pow] using h2
  by_contra hgt
  rw [← Valued.toNormedField.norm_le_one_iff, not_le] at hgt
  have hfc : 0 < ‖f c‖ := norm_pos_iff.2 ((map_ne_zero f).2 hc0)
  obtain ⟨N, hN'⟩ := pow_unbounded_of_one_lt (‖f c‖⁻¹) hgt
  have := hN N
  have h3 : 1 < ‖f c‖ * ‖f x‖ ^ N := by
    calc (1 : ℝ) = ‖f c‖ * ‖f c‖⁻¹ := (mul_inv_cancel₀ hfc.ne').symm
      _ < ‖f c‖ * ‖f x‖ ^ N := mul_lt_mul_of_pos_left hN' hfc
  linarith

def intMap (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f) :
    v.adicCompletionIntegers K →+* v'.adicCompletionIntegers F :=
  (f.comp (v.adicCompletionIntegers K).subtype).codRestrict (v'.adicCompletionIntegers F).toSubring
    (fun x => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (valued_map_le_one f hf ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2)))

theorem isIntegral_map (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f)
    (b : Kbar v ≃+* Kbar v') (hb : ∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) {y : Kbar v}
    (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    IsIntegral (v'.adicCompletionIntegers F) (b y) := by
  refine IsIntegral.map_of_comp_eq (intMap f hf) b.toRingHom ?_ hy
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v),
    IsScalarTower.algebraMap_apply (v'.adicCompletionIntegers F) (v'.adicCompletion F) (Kbar v'), hb]
  rfl

theorem valued_le_one_of_isIntegral {x : v'.adicCompletion F}
    (hx : IsIntegral (v'.adicCompletionIntegers F) (algebraMap (v'.adicCompletion F) (Kbar v') x)) :
    Valued.v x ≤ 1 := by
  rw [isIntegral_algebraMap_iff ] at hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2

end localPart

section spectral

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 F)}

theorem isIntegral_iff_spectralNorm_le_one (y : Kbar v) :
    IsIntegral (v.adicCompletionIntegers K) y ↔ spectralNorm (v.adicCompletion K) (Kbar v) y ≤ 1 := by
  have hyK : IsIntegral (v.adicCompletion K) y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyK)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' (v.adicCompletion K) hy, coeff_map]
    exact Valued.toNormedField.norm_le_one_iff.2
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((minpoly (v.adicCompletionIntegers K) y).coeff n).2)
  · intro h
    have hl : minpoly (v.adicCompletion K) y ∈
        lifts (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        (Valued.toNormedField.norm_le_one_iff.1 (h n))⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyK)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap (v.adicCompletion K), hq, minpoly.aeval]

theorem exists_isIntegral_mul_inv_pow {y : Kbar v} (hy : ¬ IsIntegral (v.adicCompletionIntegers K) y)
    {c : v.adicCompletion K} (hc : c ≠ 0) :
    ∃ N : ℕ, IsIntegral (v.adicCompletionIntegers K) (algebraMap _ (Kbar v) c⁻¹ * y⁻¹ ^ N) := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_ne_zero_valued_lt_one v
  letI : NontriviallyNormedField (v.adicCompletion K) :=
    NontriviallyNormedField.ofNormNeOne ⟨ϖ, hϖ0, (Valued.toNormedField.norm_lt_one_iff.2 hϖ1).ne⟩
  have hmul : ∀ a b : Kbar v, spectralNorm (v.adicCompletion K) (Kbar v) (a * b) =
      spectralNorm (v.adicCompletion K) (Kbar v) a * spectralNorm (v.adicCompletion K) (Kbar v) b :=
    fun a b => spectralAlgNorm_mul a b
  have hy1 : 1 < spectralNorm (v.adicCompletion K) (Kbar v) y := by
    rw [isIntegral_iff_spectralNorm_le_one, not_le] at hy
    exact hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy isIntegral_zero
  have hinv : spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ *
      spectralNorm (v.adicCompletion K) (Kbar v) y = 1 := by
    rw [← hmul, inv_mul_cancel₀ hy0, spectralNorm_one]
  have hlt : spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ < 1 := by
    rw [eq_inv_of_mul_eq_one_left hinv]
    exact inv_lt_one_of_one_lt₀ hy1
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc' hlt
  refine ⟨n + 1, ?_⟩
  have hs0 : 0 ≤ spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ := spectralNorm_nonneg _
  rw [isIntegral_iff_spectralNorm_le_one, hmul, spectralNorm_extends,
    isPowMul_spectralNorm _ (by omega : 1 ≤ n + 1)]
  calc ‖c⁻¹‖ * spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ ^ (n + 1)
      ≤ ‖c⁻¹‖ * spectralNorm (v.adicCompletion K) (Kbar v) y⁻¹ ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs0 hlt.le (by omega)) (norm_nonneg _)
    _ ≤ ‖c⁻¹‖ * ‖c‖ := mul_le_mul_of_nonneg_left hn.le (norm_nonneg _)
    _ = 1 := by rw [norm_inv, inv_mul_cancel₀ hc'.ne']

theorem isIntegral_map_iff (f : v.adicCompletion K →+* v'.adicCompletion F) (hf : Continuous f)
    (b : Kbar v ≃+* Kbar v') (hb : ∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) (y : Kbar v) :
    IsIntegral (v'.adicCompletionIntegers F) (b y) ↔ IsIntegral (v.adicCompletionIntegers K) y := by
  refine ⟨fun h => ?_, isIntegral_map f hf b hb⟩
  by_contra hy
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_valued_lt_one v
  obtain ⟨N, hN⟩ := exists_isIntegral_mul_inv_pow hy hc0
  have h1 := isIntegral_map f hf b hb hN
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy isIntegral_zero
  have hby0 : b y ≠ 0 := (map_ne_zero b).2 hy0
  have h2 : IsIntegral (v'.adicCompletionIntegers F)
      (algebraMap (v'.adicCompletion F) (Kbar v') (f c)⁻¹) := by
    have e : algebraMap (v'.adicCompletion F) (Kbar v') (f c)⁻¹ =
        b y ^ N * b (algebraMap (v.adicCompletion K) (Kbar v) c⁻¹ * y⁻¹ ^ N) := by
      rw [map_mul, map_pow, map_inv₀ b y, hb, map_inv₀ f, inv_pow, mul_left_comm,
        mul_inv_cancel₀ (pow_ne_zero _ hby0), mul_one]
    rw [e]
    exact (h.pow N).mul h1
  have h3 := valued_le_one_of_isIntegral h2
  have h4 := GlobalTheory.ConjParahoric.val_lt_one_map f hf hc1
  have hfc : f c ≠ 0 := (map_ne_zero f).2 hc0
  have h5 : Valued.v (f c * (f c)⁻¹) < 1 := by
    rw [Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h3) h4
  rw [mul_inv_cancel₀ hfc, Valuation.map_one] at h5
  exact lt_irrefl _ h5

end spectral

end GlobalTheory.ClosureIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompat
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.Global.AdicLiesOver

namespace GlobalTheory.ArtinNormU

theorem localArtin_normU : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') [v'.asIdeal.LiesOver v.asIdeal] (a : Weil h →* (v.adicCompletion K)ˣ) (a' : Weil h' →* (v'.adicCompletion L)ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ (g : Weil h) (g' : Weil h'), (∀ z : Ω, (g : G K Ω) z = (g' : G L Ω) z) → a g = GlobalTheory.BCChar.normU v v' (a' g') := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' _ a a' ha ha' g g' hgg
  classical
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero (v'.adicCompletion L) :=
    charZero_of_injective_algebraMap (algebraMap L (v'.adicCompletion L)).injective
  haveI : IsSepClosure (v'.adicCompletion L) (Kbar v') := ⟨inferInstance, inferInstance⟩
  haveI : Algebra.IsSeparable (v.adicCompletion K) (v'.adicCompletion L) := inferInstance
  haveI : IsSepClosure (v.adicCompletion K) (Kbar v') :=
    isSepClosure_of_isSeparable (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (v'.adicCompletion L) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (v.adicCompletion K) (Kbar v') :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')
  haveI : IsAlgClosure (v.adicCompletion K) (Kbar v') := ⟨inferInstance, inferInstance⟩
  obtain ⟨ι', hι'⟩ := GlobalTheory.LocDict.exists_isLocEmb L Ω A v' h'
  obtain ⟨θ, -, -, hθ⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc L Ω A v' h' ι' hι'
  let gL : GalLoc v' := θ ⟨g', Weil_le_Dec h' g'.2⟩
  have hgL : Lifts ι' gL (g' : G L Ω) := hθ _
  let gK : Kbar v' ≃ₐ[v.adicCompletion K] Kbar v' := gL.restrictScalars (v.adicCompletion K)
  have hgK : ∀ z : Ω, gK (ι'.toRingHom z) = ι'.toRingHom ((g : G K Ω) z) := fun z => by
    change gL (ι' z) = ι' _
    rw [hgL z, hgg z]
  have hj : ∀ x : K, ι'.toRingHom (algebraMap K Ω x) =
      algebraMap (v.adicCompletion K) (Kbar v') (algebraMap K (v.adicCompletion K) x) := fun x => by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    change ι' (algebraMap L Ω _) = _
    rw [ι'.commutes, IsScalarTower.algebraMap_apply (v.adicCompletion K) (v'.adicCompletion L) (Kbar v'),
      GroundTheory.Global.AdicLiesOver.algebraMap_eq, GroundTheory.Global.adicCompletionMap_algebraMap,
      ← IsScalarTower.algebraMap_apply L (v'.adicCompletion L) (Kbar v')]
  let b : Kbar v ≃ₐ[v.adicCompletion K] Kbar v' := IsAlgClosure.equiv (v.adicCompletion K) (Kbar v) (Kbar v')
  have hb : ∀ x, (b : Kbar v ≃+* Kbar v') (algebraMap _ (Kbar v) x) =
      algebraMap (v'.adicCompletion L) (Kbar v') (GroundTheory.Global.adicCompletionMap v v' x) := fun x => by
    change b _ = _
    rw [b.commutes, IsScalarTower.algebraMap_apply (v.adicCompletion K) (v'.adicCompletion L) (Kbar v')]
    rfl
  have hc : (algebraMap (v.adicCompletion K) (Kbar v')).comp
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      (b : Kbar v →+* Kbar v').comp (algebraMap (v.adicCompletionIntegers K) (Kbar v)) := RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v)]
    exact (b.commutes _).symm
  have hA : ∀ z : Ω, z ∈ A ↔ ((algebraMap (v.adicCompletion K) (Kbar v')).comp
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).IsIntegralElem (ι'.toRingHom z) := fun z => by
    have e := GlobalTheory.ClosureIso.isIntegral_map_iff (GroundTheory.Global.adicCompletionMap v v')
      (GroundTheory.Global.continuous_adicCompletionMap v v') (b : Kbar v ≃+* Kbar v') hb (b.symm (ι' z))
    have e2 : (b : Kbar v ≃+* Kbar v') (b.symm (ι' z)) = ι' z := b.apply_symm_apply _
    rw [e2] at e
    rw [hι' z, e, hc]
    change _ ↔ ((b : Kbar v →+* Kbar v').comp (algebraMap (v.adicCompletionIntegers K) (Kbar v))).IsIntegralElem (ι' z)
    constructor
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, ?_⟩
      have := congrArg (b : Kbar v →+* Kbar v') hp'
      rw [Polynomial.hom_eval₂, map_zero] at this
      rwa [show (b : Kbar v →+* Kbar v') (b.symm (ι' z)) = ι' z from b.apply_symm_apply _] at this
    · rintro ⟨p, hp, hp'⟩
      refine ⟨p, hp, (b : Kbar v →+* Kbar v').injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, show (b : Kbar v →+* Kbar v') (b.symm (ι' z)) = ι' z from b.apply_symm_apply _]
      exact hp'
  have restrict_local : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
      [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
      (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a →
      ∀ [IsSepClosure (w.adicCompletion E) (Kbar w)] (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
        AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w)) g =
          (localArtinMap (w.adicCompletion E) (Kbar w) (a σ))⁻¹ := by
    intro E Ω _ _ _ _ _ A w h ι hι a ha _ σ g hg
    have hN := GlobalTheory.LocNormGrp.hasNormGroups_of_isLocalArtin GlobalTheory.globalArtinReciprocity_holds
      GlobalTheory.Published.chevalleyUnits' E Ω A w h ι a hι ha
    obtain ⟨θ, -, -, hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc E Ω A w h ι hι
    let ψ : Weil h →* GalLoc w := θ.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))
    have hψ : ∀ τ : Weil h, Lifts ι (ψ τ) τ := fun τ => hl ⟨τ, Weil_le_Dec h τ.2⟩
    have e2 : ψ σ = g := by
      have e : θ.symm g = Subgroup.inclusion (Weil_le_Dec h) σ := by
        have := hl (θ.symm g)
        rw [θ.apply_symm_apply] at this
        exact Subtype.ext (this.eq hg)
      show θ _ = g
      rw [← e, θ.apply_symm_apply]
    let r := (AlgEquiv.restrictNormalHom (maximalAbelianExtension (w.adicCompletion E) (Kbar w))).comp ψ
    have hr : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w)) [Normal (w.adicCompletion E) L]
        (hL : L ≤ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
        restrictAb L hL (r τ) = AlgEquiv.restrictNormalHom L (ψ τ) := fun τ L _ hL =>
      restrictAb_topologicalAbelianizationEquiv L hL (ψ τ)
    have hnorm : ∀ (τ : Weil h) (L : IntermediateField (w.adicCompletion E) (Kbar w))
        [FiniteDimensional (w.adicCompletion E) L] [IsAbelianGalois (w.adicCompletion E) L],
        a τ ∈ (normUnits (w.adicCompletion E) L).range →
          restrictAb L (le_maximalAbelianExtension L) (r τ) = 1 := fun τ L _ hL hx => by
      have := (hN L ⟨inferInstance, inferInstance, hL.is_comm.comm⟩ τ _ (hψ τ)).2 hx
      rw [hr, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
      exact this
    let a' : Weil h →* (w.adicCompletion E)ˣ := invMonoidHom.comp a
    have ha' : Function.Surjective a' := inv_surjective.comp ha.surj
    have hker : a'.ker ≤ r.ker := fun τ hτ => by
      have h1 : a τ = 1 := inv_eq_one.1 (MonoidHom.mem_ker.1 hτ)
      refine MonoidHom.mem_ker.2 (ext_restrictAb fun L _ _ => ?_)
      rw [map_one]
      exact hnorm τ L (h1 ▸ Subgroup.one_mem _)
    let b := a'.liftOfSurjective ha' ⟨r, hker⟩
    have hb : ∀ τ, b (a τ)⁻¹ = r τ := fun τ =>
      MonoidHom.liftOfRightInverse_comp_apply a' _ (Function.rightInverse_surjInv ha') ⟨r, hker⟩ τ
    have hbφ : b = localArtinMap (w.adicCompletion E) (Kbar w) := by
      refine eq_localArtinMap_of (fun π hπ => ?_) (fun L _ _ x hx => ?_)
      · obtain ⟨τ, rfl⟩ := ha' π
        have h1 : GlobalTheory.SmGL.ord (w.adicCompletion E) (a τ⁻¹) = 1 := by rw [map_inv]; exact hπ
        rw [ha.ord_eq, deg_inv, neg_neg] at h1
        have hF := (GlobalTheory.WeilDict.isFrob_iff_of_lifts h (Weil_le_Dec h τ.2) (hψ τ)).1 (deg_eq_one_iff.1 h1)
        change restrictAb _ _ (b (a τ)⁻¹) = _
        rw [hb, hr]
        refine (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (ψ τ)).2 ?_
        rw [unramifiedDegree_eq_ofAdd_one_iff]
        rintro ξ ⟨n, hn, hξ⟩
        have hq : Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation (w.adicCompletion E)).integer) = normV w := resCard_eq_normV w
        rw [hq] at hξ ⊢
        refine hF ξ n (Nat.pos_of_ne_zero hn) ?_
        have h2 : normV w ^ n = normV w ^ n - 1 + 1 :=
          (Nat.sub_add_cancel (Nat.one_le_pow _ _ (zero_lt_one.trans (ReciprocityTheory.Gal.one_lt_normV w)))).symm
        rw [h2, pow_succ, hξ, one_mul]
      · obtain ⟨τ, rfl⟩ := ha' x
        change restrictAb _ _ (b (a τ)⁻¹) = _
        rw [hb]
        exact hnorm τ L (Subgroup.inv_mem_iff _ |>.1 hx)
    rw [← map_inv, ← hbφ, hb, ← e2]
    rfl
  
  have HK : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK =
      (localArtinMap (v.adicCompletion K) (Kbar v') (a g))⁻¹ := by
    have : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    have : IsSepClosure (v.adicCompletion K) (Kbar v) := ⟨inferInstance, inferInstance⟩
    let ε : (Kbar v') ≃ₐ[v.adicCompletion K] Kbar v := IsSepClosure.equiv (v.adicCompletion K) (Kbar v') (Kbar v)
    let ι : Ω →ₐ[K] Kbar v :=
      { (ε : (Kbar v') →+* Kbar v).comp ι'.toRingHom with
        commutes' := fun x => by
          change ε (ι'.toRingHom (algebraMap K Ω x)) = _
          rw [hj, ε.commutes, IsScalarTower.algebraMap_apply K (v.adicCompletion K) (Kbar v)] }
    have hιz : ∀ z, ι z = ε (ι'.toRingHom z) := fun _ => rfl
    have hc : (ε : (Kbar v') →+* Kbar v).comp ((algebraMap (v.adicCompletion K) (Kbar v')).comp
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))) =
        algebraMap (v.adicCompletionIntegers K) (Kbar v) := RingHom.ext fun x => by
      rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v)]
      exact ε.commutes _
    have hι : IsLocEmb A v ι := fun z => by
      rw [hA, hιz]
      constructor
      · rintro ⟨p, hp, hp'⟩
        refine ⟨p, hp, ?_⟩
        rw [← hc]
        have := congrArg (ε : (Kbar v') →+* Kbar v) hp'
        rwa [Polynomial.hom_eval₂, map_zero] at this
      · rintro ⟨p, hp, hp'⟩
        refine ⟨p, hp, (ε : (Kbar v') →+* Kbar v).injective ?_⟩
        rw [Polynomial.hom_eval₂, map_zero, hc]
        exact hp'
    let gK' : GalLoc v := ε.symm.trans (gK.trans ε)
    have hg' : Lifts ι gK' g := fun z => by
      change ε (gK (ε.symm (ε (ι'.toRingHom z)))) = ε (ι'.toRingHom _)
      rw [ε.symm_apply_apply, hgK]
    have H := restrict_local K Ω A v h ι hι a ha g gK' hg'
    have H1 : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK =
        (localArtinMap (v.adicCompletion K) (Kbar v') (a g))⁻¹ := by
      rw [← map_inv] at H ⊢
      ext y
      have h1 := localArtinMap_transport (RingEquiv.refl (v.adicCompletion K)) (fun _ _ => Iff.rfl)
        (ε : (Kbar v') ≃+* Kbar v) (fun x => ε.commutes x) (a g)⁻¹ y.2
      have h2 : Units.map (RingEquiv.refl (v.adicCompletion K)).toRingHom.toMonoidHom (a g)⁻¹ = (a g)⁻¹ :=
        Units.ext rfl
      rw [h2, ← H, AlgEquiv.restrictNormalHom_apply] at h1
      rw [AlgEquiv.restrictNormalHom_apply]
      apply ε.injective
      refine Eq.trans ?_ h1.symm
      change _ = ε (gK (ε.symm (ε y)))
      rw [ε.symm_apply_apply]
    exact H1
  have HL : ∀ (z : Kbar v') (hz : z ∈ maximalAbelianExtension (v'.adicCompletion L) (Kbar v')),
      gL ((localArtinMap (v'.adicCompletion L) (Kbar v') (a' g') ⟨z, hz⟩ :
        maximalAbelianExtension (v'.adicCompletion L) (Kbar v')) : Kbar v') = z := by
    intro z hz
    have H := restrict_local L Ω A v' h' ι' hι' a' ha' g' gL hgL
    have e : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v'.adicCompletion L) (Kbar v')) gL
        (localArtinMap (v'.adicCompletion L) (Kbar v') (a' g') ⟨z, hz⟩) = ⟨z, hz⟩ := by
      rw [H, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have e2 := congrArg (fun y : maximalAbelianExtension (v'.adicCompletion L) (Kbar v') => (y : Kbar v')) e
    simpa only [AlgEquiv.restrictNormalHom_apply] using e2
  have kK : ∀ (y : Kbar v') (hy : y ∈ maximalAbelianExtension (v.adicCompletion K) (Kbar v')),
      gK ((localArtinMap (v.adicCompletion K) (Kbar v') (a g) ⟨y, hy⟩ :
        maximalAbelianExtension (v.adicCompletion K) (Kbar v')) : Kbar v') = y := fun y hy => by
    have e : AlgEquiv.restrictNormalHom (maximalAbelianExtension (v.adicCompletion K) (Kbar v')) gK
        (localArtinMap (v.adicCompletion K) (Kbar v') (a g) ⟨y, hy⟩) = ⟨y, hy⟩ := by
      rw [HK, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have e2 := congrArg (fun y : maximalAbelianExtension (v.adicCompletion K) (Kbar v') => (y : Kbar v')) e
    simp only [AlgEquiv.restrictNormalHom_apply] at e2
    exact e2
  have key : localArtinMap (v.adicCompletion K) (Kbar v') (a g) =
      localArtinMap (v.adicCompletion K) (Kbar v') (normUnits (v.adicCompletion K) (v'.adicCompletion L) (a' g')) := by
    refine AlgEquiv.ext fun y => Subtype.ext ?_
    have hN := localArtinMap_norm (K := v.adicCompletion K) (K' := v'.adicCompletion L) (Ω := Kbar v') (a' g') y.2
    apply gK.injective
    rw [kK y y.2]
    change (y : Kbar v') = gL _
    rw [← hN, HL]
  exact injective_localArtinMap key

end GlobalTheory.ArtinNormU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompatStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localArtin_comp_norm_compat : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') [v'.asIdeal.LiesOver v.asIdeal] (a : Weil h →* (v.adicCompletion K)ˣ) (a' : Weil h' →* (v'.adicCompletion L)ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ (g : Weil h) (g' : Weil h'), (∀ z : Ω, (g : G K Ω) z = (g' : G L Ω) z) → a g = GlobalTheory.BCChar.normU v v' (a' g') := by
  first | (exact @GlobalTheory.ArtinNormU.localArtin_normU) | (exact GlobalTheory.ArtinNormU.localArtin_normU) | (intros; apply GlobalTheory.ArtinNormU.localArtin_normU  <;> assumption)
end
