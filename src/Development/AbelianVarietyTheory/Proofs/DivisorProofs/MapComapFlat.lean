module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FlatBaseChangeIdeal

theorem toImage_std {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ ?_
  · have := f.imageι.preimage_iSup (fun U : Y.affineOpens ↦ U.1)
    rw [← this, iSup_affineOpens_eq_top]
    simp
  · intro U
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      ← RingHom.injective_iff_ker_eq_bot]
    exact f.toImage_app_injective U

theorem ker_comap_flat {X Y V : Scheme.{0}} (h : X ⟶ Y) [QuasiCompact h] (g : V ⟶ Y) [Flat g] :
    h.ker.comap g = (pullback.fst g h).ker := by
  have := toImage_std h
  let m : pullback g h ⟶ pullback g h.imageι :=
    pullback.map g h g h.imageι (𝟙 _) h.toImage (𝟙 _) (by simp) (by simp)
  have hm1 : m ≫ pullback.fst g h.imageι = pullback.fst g h := by
    simp only [m, pullback.lift_fst, Category.comp_id]
  have hm2 : m ≫ pullback.snd g h.imageι = pullback.snd g h ≫ h.toImage := by
    simp only [m, pullback.lift_snd]
  have big : IsPullback (pullback.snd g h) (m ≫ pullback.fst g h.imageι)
      (h.toImage ≫ h.imageι) g := by
    rw [hm1, h.toImage_imageι]; exact (IsPullback.of_hasPullback g h).flip
  have hsq : IsPullback (pullback.snd g h) m h.toImage (pullback.snd g h.imageι) :=
    IsPullback.of_bot big hm2.symm (IsPullback.of_hasPullback g h.imageι).flip
  have hd : IsSchemeTheoreticallyDominant m := IsSchemeTheoreticallyDominant.of_isPullback hsq
  rw [← hm1, Scheme.Hom.ker_comp, hd.ker_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  congr 1
  exact (Scheme.IdealSheafData.ker_subschemeι _).symm

end GlobalTheory.FlatBaseChangeIdeal

namespace GlobalTheory.FlatBaseChangeIdeal

theorem map_comap_flat : ∀ (W W' V V' : Scheme.{0}) (π : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W')
    (π' : V' ⟶ V), IsPullback g' π' π g → Flat g → QuasiCompact π →
    ∀ T : W'.IdealSheafData, (T.map π).comap g = (T.comap g').map π' := by
  intro W W' V V' π g g' π' H hg hπ T
  have big : IsPullback (pullback.snd g' T.subschemeι) (pullback.fst g' T.subschemeι ≫ π')
      (T.subschemeι ≫ π) g :=
    (IsPullback.of_hasPullback g' T.subschemeι).flip.paste_vert H
  rw [Scheme.IdealSheafData.map, ker_comap_flat, Scheme.IdealSheafData.comap,
    Scheme.IdealSheafData.map_ker, ← big.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end GlobalTheory.FlatBaseChangeIdeal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlatStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_comap_eq_comap_map_of_flat : ∀ (W W' V V' : Scheme.{0}) (π : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W') (π' : V' ⟶ V), IsPullback g' π' π g → Flat g → QuasiCompact π → ∀ T : W'.IdealSheafData, (T.map π).comap g = (T.comap g').map π' := by
  first | exact @GlobalTheory.FlatBaseChangeIdeal.map_comap_flat | exact GlobalTheory.FlatBaseChangeIdeal.map_comap_flat | (intros; apply GlobalTheory.FlatBaseChangeIdeal.map_comap_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedProductDerivativeTermNormLeUniform
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedProductDerivativeTermNormLeUniform
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DeformedSum.Bound

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem defCoord_lower (φ : I → E →+* ℂ) (z : I → ℂ) (x : E) (i : I) {r : ℝ} (hz : ‖z i‖ ≤ r) :
    (1 - r) * ‖φ i x‖ ≤ ‖defCoord φ z x i‖ := by
  have h1 : ‖z i * starRingEnd ℂ (φ i x)‖ = ‖z i‖ * ‖φ i x‖ := by rw [norm_mul, Complex.norm_conj]
  have h2 := norm_sub_norm_le (φ i x) (-(z i * starRingEnd ℂ (φ i x)))
  rw [norm_neg, h1, sub_neg_eq_add] at h2
  unfold defCoord
  nlinarith [norm_nonneg (φ i x)]

theorem factor_le (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) (hx : x ≠ 0) (i : I) {r : ℝ} (hr : r < 1)
    (hz : ‖z i‖ ≤ r) :
    ‖((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
        (defCoord φ z x i)⁻¹ ^ (k + m i)‖ ≤
      ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)‖ * ((1 - r)⁻¹) ^ (k + m i) * (‖φ i x‖⁻¹) ^ k := by
  have hp : 0 < ‖φ i x‖ := by simpa using hx
  have hr' : 0 < 1 - r := by linarith
  have hl := defCoord_lower φ z x i hz
  have hd : 0 < ‖defCoord φ z x i‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
  have hinv : ‖defCoord φ z x i‖⁻¹ ≤ (1 - r)⁻¹ * ‖φ i x‖⁻¹ := by
    rw [← mul_inv]; exact inv_anti₀ (mul_pos hr' hp) hl
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_inv]
  rw [mul_assoc, mul_assoc]
  gcongr ‖_‖ * ?_
  calc ‖φ i x‖ ^ m i * ‖defCoord φ z x i‖⁻¹ ^ (k + m i)
      ≤ ‖φ i x‖ ^ m i * ((1 - r)⁻¹ * ‖φ i x‖⁻¹) ^ (k + m i) := by gcongr
    _ = (1 - r)⁻¹ ^ (k + m i) * ‖φ i x‖⁻¹ ^ k := by
      rw [mul_pow, pow_add ‖φ i x‖⁻¹]
      have : ‖φ i x‖ ^ m i * ‖φ i x‖⁻¹ ^ m i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow]
      calc ‖φ i x‖ ^ m i * ((1 - r)⁻¹ ^ (k + m i) * (‖φ i x‖⁻¹ ^ k * ‖φ i x‖⁻¹ ^ m i))
          = (1 - r)⁻¹ ^ (k + m i) * ‖φ i x‖⁻¹ ^ k * (‖φ i x‖ ^ m i * ‖φ i x‖⁻¹ ^ m i) := by ring
        _ = _ := by rw [this, mul_one]

theorem dTerm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (s : ℕ) (m : I → ℕ) (r : ℝ), r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 →
      ‖dTerm φ (2 * s) m z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) := by
  intro E _ _ _ I _ φ hφ s m r hr
  refine ⟨∏ i, (‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (((2 * s : ℕ) : ℂ) + j)‖ * ((1 - r)⁻¹) ^ (2 * s + m i)),
    fun z hz x hx => ?_⟩
  have hN : |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) = ∏ i, (‖φ i x‖⁻¹) ^ (2 * s) := by
    rw [← TermUnit.prod_norm_sq hφ x, Real.rpow_neg (Finset.prod_nonneg fun i _ => by positivity), Real.rpow_natCast,
      ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_mul, inv_pow, inv_pow]
  rw [hN, ← Finset.prod_mul_distrib, dTerm, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  exact factor_le φ (2 * s) m z x hx i hr (hz i)

end GlobalTheory.DeformedSum.Bound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedProductDerivativeTermNormLeUniformStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformedProductDerivativeTerm_norm_le_uniform : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (m : I → ℕ) (r : ℝ), r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 → ‖dTerm φ (2 * s) m z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) := by
  first | exact @GlobalTheory.DeformedSum.Bound.dTerm_bound | exact GlobalTheory.DeformedSum.Bound.dTerm_bound | (intros; apply GlobalTheory.DeformedSum.Bound.dTerm_bound <;> assumption)
end
end
