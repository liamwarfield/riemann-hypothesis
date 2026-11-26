module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSepClosureOfRangeEq
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSepClosureOfRangeEq
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

theorem GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [Algebra F (Om l)] (K : FinExt l),
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) → IsSepClosure F (Om l) := by
  intro l _ F _ _ K hK
  have hmem : ∀ q : ℚ_[l], algebraMap ℚ_[l] (Om l) q ∈ (algebraMap F (Om l)).fieldRange := by
    intro q
    have h : algebraMap ℚ_[l] (Om l) q ∈ Set.range (algebraMap F (Om l)) := by
      rw [hK]
      exact K.1.algebraMap_mem q
    obtain ⟨y, hy⟩ := h
    exact ⟨y, hy⟩
  let e := (algebraMap F (Om l)).rangeRestrictFieldEquiv
  let φ : ℚ_[l] →+* F :=
    e.symm.toRingHom.comp ((algebraMap ℚ_[l] (Om l)).codRestrict (algebraMap F (Om l)).fieldRange hmem)
  have hφ : ∀ q, algebraMap F (Om l) (φ q) = algebraMap ℚ_[l] (Om l) q := by
    intro q
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨algebraMap ℚ_[l] (Om l) q, hmem q⟩)
    exact h
  have hcomp : (algebraMap F (Om l)).comp φ = algebraMap ℚ_[l] (Om l) := RingHom.ext hφ
  haveI : CharZero F := (algebraMap F (Om l)).charZero
  haveI halg : Algebra.IsAlgebraic F (Om l) := by
    constructor
    intro x
    obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x
    refine ⟨p.map φ, (Polynomial.map_ne_zero_iff φ.injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
    exact hpx
  exact IsSepClosure.mk inferInstance (Algebra.IsAlgebraic.isSeparable_of_perfectField)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSepClosureOfRangeEqStatement
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_sep_closure_of_range_eq : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [Algebra F (Om l)] (K : FinExt l),
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) → IsSepClosure F (Om l) := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range | exact GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range | (intros; apply GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalArtinCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalArtinCompatible
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink


open GroundTheory.Global GroundTheory.Global.SemiLocal in
theorem local_restriction_abelianization_artin : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) {Ωv : Type} [Field Ωv] [Algebra (w.adicCompletion E) Ωv]
    [IsSepClosure (w.adicCompletion E) Ωv] (j : Ω →+* Ωv),
    (∀ y : E, j (algebraMap E Ω y) = algebraMap (w.adicCompletion E) Ωv (algebraMap E (w.adicCompletion E) y)) →
    ∀ (a : (w.adicCompletion E)ˣ) (σ : G E Ω) (g : Ωv ≃ₐ[w.adicCompletion E] Ωv),
    (∀ x : Ω, g (j x) = j (σ x)) →
    (∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension (w.adicCompletion E) Ωv),
      ((localArtinMap (w.adicCompletion E) Ωv a ⟨y, hy⟩ : maximalAbelianExtension (w.adicCompletion E) Ωv) : Ωv) = g y) →
    ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
    PositivityTheory.FamInh.res L (toAb E Ω σ) = PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) := by
  intro E Ω _ _ _ _ _ w Ωv _ _ _ j hj a σ g hgj hloc L _ _
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨w'⟩ := GroundTheory.Global.IdeleGroup.nonempty_placesOver_of_finite (K := E) (L := L) w
  haveI : IsSepClosed Ωv := IsSepClosure.sep_closed (w.adicCompletion E)
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  haveI : Algebra.IsSeparable (w.adicCompletion E) (w'.1.adicCompletion L) := inferInstance
  let ι : w'.1.adicCompletion L →ₐ[w.adicCompletion E] Ωv := IsSepClosed.lift
  set s := restrictAb L (le_maximalAbelianExtension L)
    (artinMap E Ω (GroundTheory.Global.IdeleClassGroup.mk E (IdeleGroup.finiteEmbedding w a))) with hs
  have hres : PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) = s :=
    congrArg (restrictAb L (le_maximalAbelianExtension L))
      ((topologicalAbelianizationEquiv E Ω).apply_symm_apply _)
  have h1 : ∀ l : L, ι (algebraMap L (w'.1.adicCompletion L) (s l)) =
      g (ι (algebraMap L (w'.1.adicCompletion L) l)) := fun l => by
    rw [hs, artinMap_finiteEmbedding_apply L w w' ι a l]
    exact hloc _ _
  rw [hres, PositivityTheory.FamInh.res_toAb]
  letI : Algebra E Ωv := ((algebraMap (w.adicCompletion E) Ωv).comp (algebraMap E (w.adicCompletion E))).toAlgebra
  let m₂ : L →ₐ[E] Ωv :=
    { toRingHom := j.comp (algebraMap L Ω)
      commutes' := fun y => by
        show j (algebraMap L Ω (algebraMap E L y)) = _
        rw [← IsScalarTower.algebraMap_apply]
        exact hj y }
  have hcomp : ∀ y : E, algebraMap L (w'.1.adicCompletion L) (algebraMap E L y) =
      algebraMap (w.adicCompletion E) (w'.1.adicCompletion L) (algebraMap E (w.adicCompletion E) y) := by
    intro y
    rw [← IsScalarTower.algebraMap_apply E L (w'.1.adicCompletion L),
      ← IsScalarTower.algebraMap_apply E (w.adicCompletion E) (w'.1.adicCompletion L)]
  let m₁ : L →ₐ[E] Ωv :=
    { toRingHom := (ι : w'.1.adicCompletion L →+* Ωv).comp (algebraMap L (w'.1.adicCompletion L))
      commutes' := fun y => by
        show ι (algebraMap L (w'.1.adicCompletion L) (algebraMap E L y)) = _
        rw [hcomp, ι.commutes]
        rfl }
  letI : Algebra L Ωv := m₂.toRingHom.toAlgebra
  haveI : IsScalarTower E L Ωv := IsScalarTower.of_algebraMap_eq fun y => (m₂.commutes y).symm
  let τ : L ≃ₐ[E] L := Normal.algHomEquivAut E Ωv L m₁
  have hτ : ∀ l : L, m₂ (τ l) = m₁ l := fun l =>
    DFunLike.congr_fun ((Normal.algHomEquivAut E Ωv L).symm_apply_apply m₁) l
  have h2 : ∀ l : L, τ (s l) = AlgEquiv.restrictNormalHom L σ (τ l) := fun l => by
    apply m₂.toRingHom.injective
    show m₂ (τ (s l)) = j (algebraMap L Ω (AlgEquiv.restrictNormalHom L σ (τ l)))
    have hρ : algebraMap L Ω (AlgEquiv.restrictNormalHom L σ (τ l)) = σ (algebraMap L Ω (τ l)) :=
      AlgEquiv.restrictNormal_commutes σ L (τ l)
    rw [hρ, ← hgj, hτ]
    have hj₂ : j (algebraMap L Ω (τ l)) = m₁ l := hτ l
    rw [hj₂]
    exact h1 l
  have h3 : τ * s = AlgEquiv.restrictNormalHom L σ * τ := AlgEquiv.ext h2
  have h4 : τ * s = τ * AlgEquiv.restrictNormalHom L σ := by
    rw [h3]
    exact IsMulCommutative.is_comm.comm _ _
  exact (mul_left_cancel h4).symm

end GlobalTheory.CompanionTheory.LTLink
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalArtinCompatibleStatement
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_artin_compatible : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) {Ωv : Type} [Field Ωv] [Algebra (w.adicCompletion E) Ωv]
    [IsSepClosure (w.adicCompletion E) Ωv] (j : Ω →+* Ωv),
    (∀ y : E, j (algebraMap E Ω y) = algebraMap (w.adicCompletion E) Ωv (algebraMap E (w.adicCompletion E) y)) →
    ∀ (a : (w.adicCompletion E)ˣ) (σ : G E Ω) (g : Ωv ≃ₐ[w.adicCompletion E] Ωv),
    (∀ x : Ω, g (j x) = j (σ x)) →
    (∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension (w.adicCompletion E) Ωv),
      ((localArtinMap (w.adicCompletion E) Ωv a ⟨y, hy⟩ : maximalAbelianExtension (w.adicCompletion E) Ωv) : Ωv) = g y) →
    ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
    PositivityTheory.FamInh.res L (toAb E Ω σ) = PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin | exact GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin | (intros; apply GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLeIffNormEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLeIffNormEmbedding
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LocalNorm

theorem tendsto_pow_zero_of_val_lt_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {x : F} (hx : valuation F x < 1) :
    Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0) := by
  intro s hs
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx γ
  refine Filter.mem_atTop_sets.2 ⟨n, fun m hm => hγ ?_⟩
  show valuation F (x ^ m) < γ
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hx.le hm) hn

private theorem norm_lt_one_of_valuation_lt_one' {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l) (hφ : Continuous φ)
    {c : F} (hc : valuation F c < 1) : ‖φ c‖ < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => φ c ^ n) Filter.atTop (nhds 0) := by
    have h2 := ((hφ.tendsto 0).comp (tendsto_pow_zero_of_val_lt_one hc))
    simpa [Function.comp_def, map_pow, map_zero] using h2
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 h1

theorem norm_le_one_of_val_le_one {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l) (hφ : Continuous φ)
    {c : F} (hc : valuation F c ≤ 1) : ‖φ c‖ ≤ 1 := by
  obtain ⟨p, hp, hp1⟩ := (Valuation.IsNontrivial.exists_lt_one (v := valuation F))
  have hpos : 0 < ‖φ p‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hp)
  have key : ∀ n : ℕ, ‖φ p‖ * ‖φ c‖ ^ n < 1 := by
    intro n
    have hv : valuation F (p * c ^ n) < 1 := by
      rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hc n)) hp1
    have h3 := norm_lt_one_of_valuation_lt_one' φ hφ hv
    rwa [map_mul, map_pow, norm_mul, norm_pow] at h3
  refine not_lt.1 fun h => ?_
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖φ p‖⁻¹) h
  have h4 := mul_lt_mul_of_pos_left hn hpos
  rw [mul_inv_cancel₀ hpos.ne'] at h4
  exact lt_asymm h4 (key n)

theorem one_lt_norm_of_one_lt_val {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l) (hφ : Continuous φ)
    {c : F} (hc : 1 < valuation F c) : 1 < ‖φ c‖ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact not_lt_zero hc
  have h1 : valuation F c⁻¹ < 1 := by
    rw [Valuation.map_inv]
    exact inv_lt_one_of_one_lt₀ hc
  have h2 := norm_lt_one_of_valuation_lt_one' φ hφ h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖φ c‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hc0)
  exact (inv_lt_one₀ hpos).1 h2

end GlobalTheory.CompanionTheory.LocalNorm

theorem GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l), Continuous φ → ∀ a b : F, a ≤ᵥ b ↔ ‖φ a‖ ≤ ‖φ b‖ := by
  intro l _ F _ _ _ _ φ hφ a b
  rw [Valuation.Compatible.vle_iff_le (v := valuation F) a b]
  by_cases hb : b = 0
  · subst hb
    simp
  · have hbn : 0 < ‖φ b‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hb)
    have hvb : 0 < valuation F b := by
      rw [zero_lt_iff]
      exact (Valuation.ne_zero_iff _).2 hb
    constructor
    · intro h
      have hv : valuation F (a / b) ≤ 1 := by
        rw [map_div₀]
        exact (div_le_one₀ hvb).2 h
      have h3 := GlobalTheory.CompanionTheory.LocalNorm.norm_le_one_of_val_le_one φ hφ hv
      rwa [map_div₀, norm_div, div_le_one hbn] at h3
    · intro h
      refine not_lt.1 fun h' => ?_
      have hv : 1 < valuation F (a / b) := by
        rw [map_div₀]
        exact (one_lt_div₀ hvb).2 h'
      have h3 := GlobalTheory.CompanionTheory.LocalNorm.one_lt_norm_of_one_lt_val φ hφ hv
      rw [map_div₀, norm_div, one_lt_div hbn] at h3
      exact absurd h (not_le.2 h3)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLeIffNormEmbeddingStatement
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_le_iff_norm_embedding : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l), Continuous φ → ∀ a b : F, a ≤ᵥ b ↔ ‖φ a‖ ≤ ‖φ b‖ := by
  first | exact @GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le | exact GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le | (intros; apply GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalArtinMapUnique
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalArtinMapUnique
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.ArtinMapUniq

open PositivityTheory.FamInh

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_ideal_ramificationIdx (L : Type) [Field L] [NumberField L] [Algebra E L] :
    ∃ 𝔡 : Ideal (𝓞 E), 𝔡 ≠ ⊥ ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 L)),
      ¬ v.asIdeal ∣ 𝔡 → w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 E) = 1 := by
  refine ⟨(differentIdeal (𝓞 E) (𝓞 L)).under (𝓞 E), ?_, fun v w hv hl => ?_⟩
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (differentIdeal_ne_bot (A := 𝓞 E) (B := 𝓞 L))
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)
  · have hnd : ¬ w.asIdeal ∣ differentIdeal (𝓞 E) (𝓞 L) := fun hd => hv (Ideal.dvd_iff_le.2 (by
      rw [hl.over]
      exact Ideal.comap_mono (Ideal.dvd_iff_le.1 hd)))
    exact Ideal.ramificationIdx_eq_one_iff.2 (not_dvd_differentIdeal_iff.1 hnd)

theorem res_unif_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (L : IntermediateField E Ω) [FiniteDimensional E L]
    [IsAbelianGalois E L] (v : HeightOneSpectrum (𝓞 E)) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) (w : HeightOneSpectrum (𝓞 L)) (hw : IsPlaceOver A w)
    [w.asIdeal.LiesOver v.asIdeal] (hr : w.asIdeal.ramificationIdx (𝓞 E) = 1)
    {x : (v.adicCompletion E)ˣ} (hx : IsUnifAt v x) :
    res L (art (localIdele E v x)) = res L (art' (localIdele E v x)) := by
  obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
  obtain ⟨σ', hσ', e'⟩ := (ha'.frob v A hA _).mp ⟨x, hx, rfl⟩
  have h := (res_isArithFrobAt hw hσ).mul_inv_mem_inertia (res_isArithFrobAt hw hσ')
  rw [(inertia_eq_bot_iff v w).2 hr, Subgroup.mem_bot, mul_inv_eq_one] at h
  rw [← e, ← e', map_inv, map_inv, map_inv, map_inv, res_toAb, res_toAb, h]

theorem res_eq {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') (L : IntermediateField E Ω) [FiniteDimensional E L]
    [IsAbelianGalois E L] (x : Ideles E) : res L (art x) = res L (art' x) := by
  have := isAlgClosure_top L
  letI : CommGroup (L ≃ₐ[E] L) :=
    { (inferInstance : Group (L ≃ₐ[E] L)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := L ≃ₐ[E] L)).comm a b }
  have : T2Space (L ≃ₐ[E] L) := krullTopology_t2
  have : IsTopologicalGroup (L ≃ₐ[E] L) := inferInstance
  let f : Ideles E →* (L ≃ₐ[E] L) := (res L).comp art
  let f' : Ideles E →* (L ≃ₐ[E] L) := (res L).comp art'
  have hf : Continuous f := (continuous_res L).comp ha.quot.continuous
  have hf' : Continuous f' := (continuous_res L).comp ha'.quot.continuous
  have hk : ∀ b : Ideles E →* Gab E Ω, IsGlobalArtin b → ∀ k, b (diagUnits E k) = 1 := fun b hb k => by
    have hk : diagUnits E k ∈ b.ker := by
      rw [hb.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact MonoidHom.mem_ker.mp hk
  obtain ⟨𝔡, h𝔡, hun⟩ := exists_ideal_ramificationIdx (E := E) L
  have hψ := GlobalTheory.FrobDense.eq_one_of_away (f * f'⁻¹) (hf.mul hf'.inv) (fun k => by
      simp [f, f', hk _ ha k, hk _ ha' k]) (Ideal.finite_factors (I := 𝔡) h𝔡).toFinset fun v hv => by
    refine GlobalTheory.FrobDense.eq_one_of_unif ((f * f'⁻¹).comp (localIdele E v)) fun y hy => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨w, hw, hwv⟩ := exists_place_between (L := L) hA
    have hv' : ¬ v.asIdeal ∣ 𝔡 := by simpa using hv
    have e := res_unif_eq ha ha' L v hA w hw (hun v w hv' hwv) hy
    simp [f, f', e]
  have := DFunLike.congr_fun hψ x
  simpa [f, f', mul_inv_eq_one] using this

theorem eq_inv_arithmetic_artin_map : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → art = (PositivityTheory.FamInh.art0 E Ω)⁻¹ := by
  intro E Ω _ _ _ _ _ art ha
  ext x
  have ha0 : IsGlobalArtin (art0 E Ω)⁻¹ := by
    refine ⟨(Homeomorph.inv (Gab E Ω)).isOpenQuotientMap.comp (isOpenQuotientMap_art0 E Ω),
      ?_, ?_, ?_, ?_⟩
    · rw [← ker_art0 E Ω]
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
    · intro v A hA g
      simp only [MonoidHom.inv_apply, inv_eq_iff_eq_inv]
      rw [art0_unit_iff hA, Subgroup.inv_mem_iff]
      rfl
    · intro v A hA g
      simp only [MonoidHom.inv_apply, map_inv, inv_eq_iff_eq_inv]
      exact art0_unif_iff hA _
    · intro v A hA
      rw [← closure_range_eq hA]
      congr 1
      ext g
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x⁻¹, by simp⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x⁻¹, by simp⟩
  have h : art x * ((art0 E Ω)⁻¹ x)⁻¹ ∈ (⊥ : Subgroup (Gab E Ω)) :=
    mem_of_forall_res (H := ⊥) isClosed_singleton fun L _ _ _ => by
      rw [map_mul, map_inv, res_eq ha ha0 L x, mul_inv_cancel]
  rwa [Subgroup.mem_bot, mul_inv_eq_one] at h

end GlobalTheory.CompanionTheory.ArtinMapUniq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalArtinMapUniqueStatement
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_artin_map_unique : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → art = (PositivityTheory.FamInh.art0 E Ω)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map | exact GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map | (intros; apply GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map <;> assumption)
end
end
end

noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem link : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (χ : ↥(GK Bw.Kw) →* (↥Bw.Kw.1)ˣ), IsLTChar Bw.Kw χ →
    ∀ (φ : w.adicCompletion E →+* Om l), Continuous φ →
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    ∀ (x : (w.adicCompletion E)ˣ) (σ : ↥(Dec (F := E) A)), IsUnitAt w x → (σ : G E Ω) ∈ Ine (F := E) A →
      art (localIdele E w x) = toAb E Ω σ →
      (((χ (Bw.e σ) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) : Om l) = φ (x : w.adicCompletion E) := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hI art hart χ hχ φ hφ hφj x σ hx hσ hxσ
  letI algF : Algebra (w.adicCompletion E) (Om l) := φ.toAlgebra
  have hmap : ∀ y, algebraMap (w.adicCompletion E) (Om l) y = φ y := fun _ => rfl
  have hr : Set.range (algebraMap (w.adicCompletion E) (Om l)) = (Bw.Kw.1 : Set (Om l)) :=
    GlobalTheory.T.local_embedding_range_eq_field Bw w φ hφ hφj
  haveI hsep : IsSepClosure (w.adicCompletion E) (Om l) := GlobalTheory.T.is_sep_closure_of_range_eq Bw.Kw hr
  haveI hext : ValuativeExtension (w.adicCompletion E) (Om l) := ⟨fun {a b} => by
    rw [GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le]
    exact (GlobalTheory.T.valuation_le_iff_norm_embedding φ hφ a b).symm⟩
  haveI hclosed : IsSepClosed (Om l) := IsSepClosure.sep_closed (w.adicCompletion E)
  haveI halg : Algebra.IsAlgebraic (w.adicCompletion E) (Om l) := hsep.separable.isAlgebraic
  obtain ⟨π, hπ, H⟩ := GlobalTheory.T.exists_uniformizer_galois_action hχ hr
  let g' := Bw.e σ
  have hfix : ∀ y, (g' : GQ l) (algebraMap (w.adicCompletion E) (Om l) y) = algebraMap (w.adicCompletion E) (Om l) y := by
    intro y
    have hy : algebraMap (w.adicCompletion E) (Om l) y ∈ Bw.Kw.1 := by
      have : algebraMap (w.adicCompletion E) (Om l) y ∈ (Bw.Kw.1 : Set (Om l)) := hr ▸ ⟨y, rfl⟩
      exact this
    exact g'.2 ⟨_, hy⟩
  let g : Om l ≃ₐ[w.adicCompletion E] Om l := { (g' : GQ l).toRingEquiv with commutes' := hfix }
  have hg : ∀ y, g y = (g' : GQ l) y := fun _ => rfl
  obtain ⟨u, hu, hact⟩ := H g g' hg
  have hdeg : unramifiedDegree (w.adicCompletion E) (Om l) g = 1 := GlobalTheory.T.local_bridge_lubin_tate_field Bw hI σ hσ g hg
  have hloc := GlobalTheory.T.lubin_tate_unramified_degree_one hπ (isLubinTateSeries_ltPoly π) u g hdeg hact
  have hres := fun (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L] =>
    GlobalTheory.T.local_global_artin_compatible w Bw.j (fun y => (hφj y).symm) (unitsIncl _ u⁻¹) (σ : G E Ω) g
      (fun z => by rw [hg]; exact Bw.e_comm σ z) hloc L
  have h1 : art (localIdele E w (unitsIncl _ u)) = toAb E Ω σ := by
    rw [GlobalTheory.T.global_artin_map_unique art hart]
    have hb : ∀ a b : Gab E Ω, (∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
        PositivityTheory.FamInh.res L a = PositivityTheory.FamInh.res L b) → a = b := by
      intro a b h
      have := PositivityTheory.FamInh.mem_of_forall_res (H := ⊥) (g := a * b⁻¹) (by simpa using isClosed_singleton)
        fun L _ _ _ => by rw [map_mul, map_inv, h L, mul_inv_cancel]
      exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 this)
    refine hb _ _ fun L _ _ => ?_
    rw [hres L, MonoidHom.inv_apply, map_inv, map_inv]
    simp
  have h2 : unitsIncl _ u = x :=
    GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art hart w (h1.trans hxσ.symm)
  rw [← hu, ← h2]
  rfl

end GlobalTheory.CompanionTheory.LTLink
