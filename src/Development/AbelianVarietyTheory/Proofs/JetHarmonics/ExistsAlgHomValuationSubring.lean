module

public import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitsZpowSurjective
namespace GlobalTheory.DivisibleUnits

theorem units_zpow_surjective {F : Type} [Field F] [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Fˣ => a ^ n) := by
  have nat_root : ∀ (m : ℕ), 0 < m → ∀ x : Fˣ, ∃ y : Fˣ, y ^ m = x := by
    intro m hm x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) hm
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact x.ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    ext
    simp [hz]
  intro x
  rcases Int.lt_or_gt_of_ne hn with h | h
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x⁻¹
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = -(n.natAbs : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, hy, inv_inv]
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = (n.natAbs : ℤ) := by omega
    rw [this, zpow_natCast, hy]

noncomputable def divisibleUnits (F : Type) [Field F] [IsAlgClosed F] :
    DivisibleBy (Additive Fˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Fˣ) ℤ (fun {n} hn x => by
    obtain ⟨y, hy⟩ := units_zpow_surjective (F := F) hn (Additive.toMul x)
    exact ⟨Additive.ofMul y, by simpa using congrArg Additive.ofMul hy⟩)

theorem exists_extension {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) :
    ∃ κ : M →* Fˣ, ∀ x : H, κ (Φ x) = χ x := by
  letI := divisibleUnits F
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

theorem target : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M] [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) → ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x :=
  fun Φ hΦ χ => exists_extension Φ hΦ χ

end GlobalTheory.DivisibleUnits
end

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

theorem exists_extend_character {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  first
  | exact @_root_.GlobalTheory.DivisibleUnits.target
  | exact _root_.GlobalTheory.DivisibleUnits.target
  | (apply _root_.GlobalTheory.DivisibleUnits.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.DivisibleUnits.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DivisibleUnits.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DivisibleUnits.target ..)

variable {O : Type} [CommRing O]

theorem exists_ptMap {A R : Type} [CommRing A] [Algebra O A] [CommRing R] [Algebra O R]
    (c : specO O R ⟶ specO O A) : ∃ φ : A →ₐ[O] R, c = ptMap φ := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of A) (S := CommRingCat.of R) c.left
  have w := Over.w c
  change c.left ≫ Spec.map _ = Spec.map _ at w
  rw [← hψ, ← Spec.map_comp] at w
  have w' := congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  exact ⟨⟨ψ.hom, fun r => RingHom.congr_fun w' r⟩, Over.OverMorphism.ext hψ.symm⟩

theorem exists_finite_free [IsLocalRing O] (Z : Over (Spec (CommRingCat.of O))) [IsFinite Z.hom] [Flat Z.hom] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A), Module.Finite O A ∧ Module.Free O A ∧
      Nonempty (specO O A ≅ Z) := by
  haveI : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let g : CommRingCat.of O ⟶ Γ(Z.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ Z.hom.appTop
  letI : Algebra O Γ(Z.left, ⊤) := g.hom.toAlgebra
  have hw : Z.left.isoSpec.inv ≫ Z.hom = Spec.map g := by
    rw [Iso.inv_comp_eq, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      ← Scheme.isoSpec_Spec_inv, Iso.hom_inv_id, Category.comp_id]
  haveI h1 : IsFinite (Spec.map g) := hw ▸ inferInstance
  haveI h2 : Flat (Spec.map g) := hw ▸ inferInstance
  have h3 : g.hom.Finite := (IsFinite.SpecMap_iff g).1 h1
  have h4 : g.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h2
  haveI : Module.Finite O Γ(Z.left, ⊤) := h3
  haveI : Module.Flat O Γ(Z.left, ⊤) := h4
  exact ⟨Γ(Z.left, ⊤), inferInstance, inferInstance, inferInstance, Module.free_of_flat_of_isLocalRing,
    ⟨Over.isoMk Z.left.isoSpec.symm hw⟩⟩

theorem exists_algHom_valuationSubring {F : Type} [Field F] (W : ValuationSubring F) {A : Type} [CommRing A]
    [Algebra W A] [Module.Finite W A] (φ : A →ₐ[W] F) : ∃ ψ : A →ₐ[W] W, φ = (Algebra.ofId W F).comp ψ := by
  have h : ∀ a, φ a ∈ (⊥ : Subalgebra W F) := fun a => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 ((Algebra.IsIntegral.isIntegral (R := W) a).map φ)
    exact Algebra.mem_bot.2 ⟨y, hy⟩
  let e := Algebra.botEquivOfInjective (R := W) (A := F) Subtype.val_injective
  refine ⟨(e : (⊥ : Subalgebra W F) →ₐ[W] W).comp (φ.codRestrict ⊥ h), AlgHom.ext fun a => ?_⟩
  obtain ⟨y, hy⟩ := e.symm.surjective (φ.codRestrict ⊥ h a)
  show φ a = algebraMap W F (e (φ.codRestrict ⊥ h a))
  rw [← hy, e.apply_symm_apply]
  exact (congrArg Subtype.val hy).symm.trans ((e.symm.commutes y ▸ rfl : ((e.symm y : (⊥ : Subalgebra W F)) : F) = _))

theorem isAdicComplete_of_pow_le {I J : Ideal O} [IsAdicComplete I O] {a b : ℕ} (h₁ : I ^ a ≤ J) (h₂ : J ^ b ≤ I) :
    IsAdicComplete J O := by
  letI : TopologicalSpace O := I.adicTopology
  haveI : IsTopologicalRing O := (I.ringFilterBasis).isTopologicalRing
  letI : UniformSpace O := IsTopologicalAddGroup.rightUniformSpace O
  haveI : IsUniformAddGroup O := isUniformAddGroup_of_addCommGroup
  have hI : IsAdic I := rfl
  have hJ : IsAdic J := by
    rw [isAdic_iff] at hI ⊢
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · refine AddSubgroup.isOpen_mono (H₁ := (I ^ (a * n)).toAddSubgroup) (H₂ := (J ^ n).toAddSubgroup) ?_ (hI.1 _)
      intro x hx
      rw [pow_mul] at hx
      exact Ideal.pow_right_mono h₁ n hx
    · obtain ⟨n, hn⟩ := hI.2 s hs
      refine ⟨b * n, fun x hx => hn ?_⟩
      rw [pow_mul] at hx
      exact Ideal.pow_right_mono h₂ n hx
  exact hJ.isAdicComplete_iff.2 (hI.isAdicComplete_iff.1 inferInstance)

section Val
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem exists_pow_mem_span (a b : TWO.Ov v) (ha : ¬ IsUnit a) (hb : b ≠ 0) :
    ∃ n : ℕ, a ^ n ∈ Ideal.span {b} := by
  by_cases ha0 : a = 0
  · exact ⟨1, by simp [ha0]⟩
  have hbF : (b : F) ≠ 0 := fun h => hb (Subtype.ext h)
  have haF : (a : F) ≠ 0 := fun h => ha0 (Subtype.ext h)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff v).2 haF)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff v).2 hbF)
  have hr0 : 0 < r := by
    have h0 : (0 : ℚ) ≤ r := by have := TWO.v_nonneg v a; rw [← hr] at this; exact_mod_cast this
    refine lt_of_le_of_ne h0 fun h => ha ?_
    have hi : (a : F)⁻¹ ∈ TWO.Ov v := by
      refine TWO.exists_weight_basis_filtration (a := v a) ?_ (by rw [← hr, ← h]; rfl)
      rw [← AddValuation.map_mul, mul_inv_cancel₀ haF, AddValuation.map_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ haF))
  obtain ⟨n, hn⟩ := Archimedean.arch s hr0
  have hq : (a : F) ^ n / b ∈ TWO.Ov v := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
      ((AddValuation.ne_top_iff v).2 (div_ne_zero (pow_ne_zero n haF) hbF))
    have e : v ((a : F) ^ n / b * b) = v ((a : F) ^ n) := by rw [div_mul_cancel₀ _ hbF]
    rw [AddValuation.map_mul, AddValuation.map_pow, ← ht, ← hs, ← hr] at e
    have e' : t + s = n • r := by exact_mod_cast e
    rw [TWO.mem_Ov, ← ht]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ t)
  exact ⟨n, Ideal.mem_span_singleton'.2 ⟨⟨_, hq⟩, Subtype.ext (by
    show (a : F) ^ n / b * b = ((a ^ n : TWO.Ov v) : F)
    rw [div_mul_cancel₀ _ hbF]; rfl)⟩⟩

end Val

end GlobalTheory.TorsionCharacter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem comp_eq_sum_inner_smul_rankOne {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ Wp) (c : OrthonormalBasis κ ℂ Wq)
    (P : H →L[ℂ] Wp) (A : H →L[ℂ] H) (Q : Wq →L[ℂ] H) :
    P.comp (A.comp Q) = ∑ p : ι × κ, ⟪ContinuousLinearMap.adjoint P (b p.1), A (Q (c p.2))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (b p.1) := by
  ext x
  simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, Fintype.sum_prod_type, smul_smul]
  conv_lhs => rw [← c.sum_repr' x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [← b.sum_repr' (P (A (Q (c j))))]
  simp only [Finset.smul_sum, smul_smul, mul_comm]

theorem isCoef_of_translate_smul_exists : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → (∀ f : Mx k r → (Wq →L[ℂ] Wp), PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f → ∃ s, IsCoef R l l' f s) ∧ (∀ F s (t : ℂ), IsCoef R l l' F s → IsCoef R l l' (fun g => t • F g) (t * s)) ∧ ((∃ x ∈ R.TK, l x ≠ 0) → (∃ y ∈ R.TK, l' y ≠ 0) → ∀ s : ℂ, ∃ F, IsCoef R l l' F s) := by
  intro hK k r ε mu R Wp _ _ _ _ Wq _ _ _ _ l l' hR
  obtain ⟨hmul, hone, hinner, -, -, hTK, hKF, -, -⟩ := rep_basic_of_isDS hK k r ε mu R hR
  refine ⟨?_, ?_, ?_⟩
  · rintro f ⟨a, ha, b, hb, P, Q, hQ, hP, h⟩
    obtain ⟨hai, ha1, -⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv ha
    obtain ⟨hbi, -, hb2⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hb
    let e := stdOrthonormalBasis ℂ Wp
    let c := stdOrthonormalBasis ℂ Wq
    let φ := (finProdFinEquiv (m := Module.finrank ℂ Wp) (n := Module.finrank ℂ Wq)).symm
    refine ⟨_, _, fun i => R.σ a (ContinuousLinearMap.adjoint P (e (φ i).1)),
      fun i => R.σ b⁻¹ (Q (c (φ i).2)), fun i => (innerSL ℂ (c (φ i).2)).smulRight (e (φ i).1),
      fun i => ⟨hTK a ha _ (hKF _ (hP _)), hTK _ hbi _ (hKF _ (hQ _))⟩, fun g hg => ?_, rfl⟩
    have hc : a * (a⁻¹ * g * b⁻¹) * b = g := by
      calc a * (a⁻¹ * g * b⁻¹) * b = (a * a⁻¹) * g * (b⁻¹ * b) := by simp only [Matrix.mul_assoc]
        _ = g := by rw [ha1, hb2, Matrix.one_mul, Matrix.mul_one]
    have h1 : f g = P.comp ((R.σ (a⁻¹ * g * b⁻¹)).comp Q) := by
      have := h (a⁻¹ * g * b⁻¹)
      simpa only [hc] using this
    have hm : a⁻¹ * g * b⁻¹ ∈ GG k r :=
      Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hai hg) hbi
    have h2 : ∀ u v, ⟪u, R.σ (a⁻¹ * g * b⁻¹) v⟫_ℂ = ⟪R.σ a u, R.σ g (R.σ b⁻¹ v)⟫_ℂ := by
      intro u v
      rw [← hinner a ha, ← hmul a ha _ hm, ← hmul g hg _ hbi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ha1,
        Matrix.one_mul]
    rw [h1, comp_eq_sum_inner_smul_rankOne e c]
    simp only [h2]
    exact (φ.sum_comp (fun p => ⟪R.σ a (ContinuousLinearMap.adjoint P (e p.1)), R.σ g (R.σ b⁻¹ (Q (c p.2)))⟫_ℂ •
      (innerSL ℂ (c p.2)).smulRight (e p.1))).symm
  · rintro F s t ⟨m, x, y, X, hxy, hF, hs⟩
    refine ⟨m, x, y, fun i => t • X i, hxy, fun g hg => ?_, ?_⟩
    · simp only [hF g hg, Finset.smul_sum, smul_smul, mul_comm]
    · simp only [hs, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_right]
  · rintro ⟨x, hx, hx0⟩ ⟨y, hy, hy0⟩ s
    have h1 : ⟪l x, l x⟫_ℂ ≠ 0 := fun h => hx0 (inner_self_eq_zero.mp h)
    have h2 : ⟪l' y, l' y⟫_ℂ ≠ 0 := fun h => hy0 (inner_self_eq_zero.mp h)
    refine ⟨fun g => ∑ _i : Fin 1, ⟪x, R.σ g y⟫_ℂ •
        ((s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x)),
      1, fun _ => x, fun _ => y,
      fun _ => (s / (⟪l' y, l' y⟫_ℂ * ⟪l x, l x⟫_ℂ)) • (innerSL ℂ (l' y)).smulRight (l x),
      fun _ => ⟨hx, hy⟩, fun g _ => rfl, ?_⟩
    rw [Fin.sum_univ_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, inner_smul_right, inner_smul_right, div_mul_cancel₀ _ (mul_ne_zero h2 h1)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
open Matrix

noncomputable section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma deriv_smul_const_vec (φ : ℝ → ℂ) (v : E) (t : ℝ) :
    deriv (fun s => φ s • v) t = deriv φ t • v := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hφ : DifferentiableAt ℝ φ t
  · exact deriv_smul_const hφ v
  · have hn : ¬ DifferentiableAt ℝ (fun s => φ s • v) t := by
      intro h
      obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
      apply hφ
      have hv' : ℓ v ≠ 0 := by rw [hℓ]; simpa using hv
      have h2 := (((ℓ.restrictScalars ℝ).differentiableAt).comp t h).const_mul (ℓ v)⁻¹
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show φ s = (ℓ v)⁻¹ * ℓ (φ s • v)
      rw [map_smul, smul_eq_mul, mul_comm (φ s), ← mul_assoc, inv_mul_cancel₀ hv', one_mul]
    rw [deriv_zero_of_not_differentiableAt hφ, deriv_zero_of_not_differentiableAt hn, zero_smul]

private lemma Dx_smul_const (x : Bool × B.Mat k r) (f : B.Mat k r → ℂ) (v : E) :
    Dx x (fun g => f g • v) = fun g => Dx x f g • v := by
  funext g
  unfold Dx
  split_ifs
  · exact deriv_smul_const_vec _ v 0
  · exact deriv_smul_const_vec _ v 0

private lemma Dw_smul_const (w : List (Bool × B.Mat k r)) (f : B.Mat k r → ℂ) (v : E) :
    Dw w (fun g => f g • v) = fun g => Dw w f g • v := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w (fun g => f g • v)) = fun g => Dx x (Dw w f) g • v
    rw [ih]
    exact Dx_smul_const x _ v

theorem polyOK_star {N a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : IsPolyDeg a P) :
    IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hPq⟩ := h

  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_rename_le _ _).trans (le_trans ?_ hq)
    exact MvPolynomial.totalDegree_le_of_support_subset (MvPolynomial.support_map_subset (f := starRingEnd ℂ) q)
  · intro g

    have key : ∀ (p : MvPolynomial ((Fin N × Fin N) ⊕ (Fin N × Fin N)) ℂ) (y : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℂ),
        star (MvPolynomial.eval y p) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun i => star (y i)) p := by
      intro p y
      induction p using MvPolynomial.induction_on with
      | C c => rw [MvPolynomial.eval_C, MvPolynomial.eval₂_C, Complex.star_def]
      | add p p' hp hp' => rw [map_add (f := _), star_add, hp, hp', MvPolynomial.eval₂_add]
      | mul_X p i hp =>
        rw [map_mul, star_mul', hp, MvPolynomial.eval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    show star (P g) = _
    rw [MvPolynomial.eval_rename, MvPolynomial.eval_map, hPq g, key]
    congr 1
    funext i
    rcases i with ⟨a, b⟩ | ⟨a, b⟩ <;> simp

theorem polyOK_ck {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) (v : E) (UU : Set (B.Mat k r)) :
    B.CkOn ⊤ UU (fun g => P g • v) := by
  obtain ⟨hs, -⟩ := polynomial_bound k r κ P hP
  intro g₀ _
  exact ⟨Set.univ, fun g => P g • v, isOpen_univ, Set.mem_univ _,
    (hs.smul contDiff_const).contDiffOn, fun _ _ _ => rfl⟩

theorem polyOK_bound {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) (v : E) {d : ℝ} (hd : (κ : ℝ) ≤ d) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r, ‖B.dLR u w (fun g => P g • v) g‖ ≤ C * B.gN g ^ d := by
  obtain ⟨-, hB⟩ := polynomial_bound k r κ P hP
  obtain ⟨C₀, hC₀⟩ := hB m
  refine ⟨max C₀ 0 * ‖v‖, mul_nonneg (le_max_right _ _) (norm_nonneg _), ?_⟩
  intro u w hu hw hl g hg
  have h1 := hC₀ u w hu hw hl g hg
  have hs : ((u ++ w).map (fun _ : B.Mat k r => (0 : ℕ))).sum = 0 := by simp
  rw [hs, Nat.cast_zero, add_zero, dLR_eq] at h1

  have hg1 : 1 ≤ B.gN g := gN_ge_one hg
  have e0 : 0 ≤ B.gN g ^ (κ : ℝ) := Real.rpow_nonneg (zero_le_one.trans hg1) _
  have hpow : B.gN g ^ (κ : ℝ) ≤ B.gN g ^ d := Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hC : ‖Dw (wL u ++ wR w) P g‖ ≤ max C₀ 0 * B.gN g ^ d :=
    h1.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) e0).trans
      (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
  rw [dLR_eq, Dw_smul_const, norm_smul]
  calc ‖Dw (wL u ++ wR w) P g‖ * ‖v‖ ≤ max C₀ 0 * B.gN g ^ d * ‖v‖ :=
        mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    _ = max C₀ 0 * ‖v‖ * B.gN g ^ d := by ring

end aux

private lemma foldr_max_zero_le_of_forall_le {o : ℕ} (l : List ℕ) (h : ∀ a ∈ l, a ≤ o) : l.foldr max 0 ≤ o := by

  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih => exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem polyOp_ok : Formalism.FourierDecayAlt.P.CutMP.JDPolyOK := by
  intro k r Wp Wq _ _ _ _ _ o κ Θ hΘ
  refine ⟨fun UU T hT => ?_, fun d hd T hT => ?_, ?_⟩
  · obtain ⟨-, P, hP, hc, hca⟩ := hΘ T hT
    rw [show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc,
      show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]
    exact ⟨polyOK_ck hP _ UU, polyOK_ck (polyOK_star hP) _ UU⟩
  · obtain ⟨-, P, hP, hc, hca⟩ := hΘ T hT
    rw [show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc,
      show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]
    refine ⟨polyOK_ck hP _ _, polyOK_ck (polyOK_star hP) _ _, fun m => ?_⟩
    obtain ⟨C₁, -, h₁⟩ := polyOK_bound hP (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m
    obtain ⟨C₂, -, h₂⟩ := polyOK_bound (polyOK_star hP) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m
    refine ⟨max C₁ C₂, fun u w hu hw hl g hg => ?_⟩
    have hx : 0 ≤ B.gN g ^ d := Real.rpow_nonneg (zero_le_one.trans (gN_ge_one hg)) d
    exact ⟨(h₁ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx),
      (h₂ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)⟩
  · show (Θ.map fun T => T.word.length).foldr max 0 ≤ o
    refine foldr_max_zero_le_of_forall_le _ fun a ha => ?_
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp ha
    exact (hΘ T hT).1

end GlobalTheory.HatNF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionInjectiveParameters
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensOrth

variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem hh_smul (Γ : Matrix ι ι ℂ) (R : Rep k r) (a b : ℂ) (x y : ι → R.H) :
    hh Γ R (fun c => a • x c) (fun c => b • y c) = a * star b * hh Γ R x y := by
  simp only [hh, inner_smul_left, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (x : ι → R.H) (y : κ → ι → R.H) :
    hh Γ R x (fun c => ∑ J, y J c) = ∑ J, hh Γ R x (y J) := by
  simp only [hh, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem hh_star (Γ : Matrix ι ι ℂ) (hΓ : Γᴴ = Γ) (R : Rep k r) (x y : ι → R.H) :
    star (hh Γ R x y) = hh Γ R y x := by
  simp only [hh, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : star (Γ j i) = Γ i j := by
    have := congrFun (congrFun hΓ i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [h]
  congr 1
  exact inner_conj_symm _ _

theorem eq_zero_of_hh (Γ : Matrix ι ι ℂ) (hΓ : Γ * Γ = 1) (R : Rep k r) (x : ι → R.H)
    (h : hh Γ R x (fun c => ∑ j, Γ c j • x j) = 0) (c : ι) : x c = 0 := by
  set z : ι → R.H := fun c => ∑ j, Γ c j • x j with hz
  have h1 : hh Γ R x z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    unfold hh
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ⟪z i, z i⟫_ℂ = ∑ j, Γ i j * ⟪z i, x j⟫_ℂ := by
      conv_lhs => enter [3]; rw [hz]
      simp only [inner_sum, inner_smul_right]
    rw [← this, inner_self_eq_norm_sq_to_K]
    rfl
  rw [h1, Complex.ofReal_eq_zero] at h
  have h2 : ∀ i, z i = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖z i‖)).1 h i (mem_univ _)
    simpa using this
  have h3 : ∑ i, Γ c i • z i = x c := by
    simp only [hz, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, hΓ, Matrix.one_apply]
    simp
  rw [← h3]
  simp [h2]

theorem SmMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have := hT.smul 0 0 R.smSub.zero_mem
  simpa using this

omit [DecidableEq ι] [DecidableEq κ] in
theorem raw_scale {ρ : Mx k r → Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
    {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} (h : TensRaw ρ R RI io pr)
    (a : κ → ℂ) (ha : ∀ I, a I ≠ 0)
    (h1 : ∀ I c, SmMap (RI I) R (fun v => a I • io I c v))
    (h2 : ∀ I c, SmMap R (RI I) (fun v => (a I)⁻¹ • pr I c v)) :
    TensRaw ρ R RI (fun I c v => a I • io I c v) (fun I c v => (a I)⁻¹ • pr I c v) := by
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · intro I g hg y hy
    funext c
    have := congrFun (h.io_eq I g hg y hy) c
    simp only [act] at this ⊢
    rw [this, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_comm]
  · intro I g hg x hx
    rw [← Finset.smul_sum, ← Finset.smul_sum, map_smul, h.pr_eq I g hg x hx]
  · intro x hx c
    rw [← h.sum_io_pr x hx c]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hm : ∑ d, pr I d (x d) ∈ (RI I).smSub :=
      Submodule.sum_mem _ fun d _ => (h.pr_sm I d).mem _ (hx d)
    rw [← Finset.smul_sum, (h.io_sm I c).smul _ _ hm, smul_smul, mul_inv_cancel₀ (ha I), one_smul]
  · intro I y hy
    conv_rhs => rw [← h.pr_io I y hy]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [(h.pr_sm I c).smul _ _ ((h.io_sm I c).mem _ hy), smul_smul, inv_mul_cancel₀ (ha I), one_smul]
  · intro I J hIJ y hy
    have : ∀ c, (a I)⁻¹ • pr I c (a J • io J c y) = ((a I)⁻¹ * a J) • pr I c (io J c y) := fun c => by
      rw [(h.pr_sm I c).smul _ _ ((h.io_sm J c).mem _ hy), smul_smul]
    simp only [this]
    rw [← Finset.smul_sum, h.pr_io_ne I J hIJ y hy, smul_zero]

theorem tensH_of_raw : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∃ io' pr' ep, TensH ρ Γ R RI io' pr' ep := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hinj hF hT
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hP : Poulsen := hH.2.2.2.2.2.1
  have hform := GlobalTheory.TensForm.pulledBack_isInvForm hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  have horth : ∀ I J, I ≠ J → ∀ y ∈ (RI I).sm, ∀ y' ∈ (RI J).sm,
      hh Γ R (fun c => io I c y) (fun c => io J c y') = 0 := by
    intro I J hIJ
    rcases (hP k r ε _ _ _ _ (hRI I) (hRI J)).2 _ (hform I J) with h | ⟨U, hU⟩
    · exact h
    · exact absurd (hinj (GlobalTheory.DSInequiv.param_eq_of_equiv hH k r ε _ _ _ _ (hRI I) (hRI J) U hU)) hIJ
  choose cI hc using fun I => (hP k r ε _ _ _ _ (hRI I) (hRI I)).1 _ (hform I I)
  have hunit : ∀ I, ∃ w ∈ (RI I).sm, ‖w‖ = 1 := fun I => by
    obtain ⟨-, -, -, -, h5, -, h7, ⟨w, hw, hwK, -⟩, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε _ _ (hRI I)
    exact ⟨w, h5 w (h7 w hwK), hw⟩
  have hreal : ∀ I, ((cI I).re : ℂ) = cI I := fun I => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have h1 := hc I w hw w hw
    have h2 := hh_star Γ hF.1 R (fun c => io I c w) (fun c => io I c w)
    rw [inner_self_eq_norm_sq_to_K, hn] at h1
    simp only [map_one, one_pow, mul_one] at h1
    rw [h1] at h2
    exact Complex.conj_eq_iff_re.1 h2
  have hne : ∀ I, cI I ≠ 0 := fun I h0 => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have hx : ∀ c, (∑ j, Γ c j • io I j w) ∈ R.smSub := fun c =>
      Submodule.sum_mem _ fun j _ => R.smSub.smul_mem _ ((hT.io_sm I j).mem _ hw)
    have hz : hh Γ R (fun c => io I c w) (fun c => ∑ j, Γ c j • io I j w) = 0 := by
      have e : (fun c => ∑ j, Γ c j • io I j w) =
          fun c => ∑ J, io J c (∑ e, pr J e (∑ j, Γ e j • io I j w)) :=
        funext fun c => (hT.sum_io_pr _ hx c).symm
      rw [e, hh_sum_right]
      refine Finset.sum_eq_zero fun J _ => ?_
      have hm : ∑ e, pr J e (∑ j, Γ e j • io I j w) ∈ (RI J).smSub :=
        Submodule.sum_mem _ fun e _ => (hT.pr_sm J e).mem _ (hx e)
      by_cases hIJ : I = J
      · subst hIJ
        have := hc I w hw _ hm
        rw [h0, zero_mul] at this
        exact this
      · exact horth I J hIJ w hw _ hm
    have h0' := eq_zero_of_hh Γ hF.2.1 R _ hz
    have h1 := hT.pr_io I w hw
    simp only [h0', SmMap_zero (hT.pr_sm I _), Finset.sum_const_zero] at h1
    rw [← h1, norm_zero] at hn
    exact zero_ne_one hn
  have hre : ∀ I, (cI I).re ≠ 0 := fun I h => hne I (by rw [← hreal I, h]; simp)
  have hsc : ∀ (m m' : Fin (2 * r + k + 1) → ℝ) (S S' : Rep k r), S.IsDS ε m → S'.IsDS ε m' →
      ∀ (T : S.H → S'.H) (a : ℂ), SmMap S S' T → SmMap S S' (fun v => a • T v) := by
    intro m m' S S' hS hS' T a h
    have := (GlobalTheory.T.smooth_maps_closure hK k r ε _ _ _ S S' S' hS hS' hS').2.2.1 T T (a - 1) h h
    simpa only [sub_smul, one_smul, sub_add_cancel] using this
  set a : κ → ℂ := fun I => (((Real.sqrt |(cI I).re|)⁻¹ : ℝ) : ℂ) with ha
  have hane : ∀ I, a I ≠ 0 := fun I => by
    simp only [ha, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (abs_pos.2 (hre I))).ne'
  refine ⟨fun I c v => a I • io I c v, fun I c v => (a I)⁻¹ • pr I c v,
    fun I => (cI I).re / |(cI I).re|, ⟨raw_scale hT a hane
      (fun I c => hsc _ _ _ _ (hRI I) hR _ _ (hT.io_sm I c))
      (fun I c => hsc _ _ _ _ hR (hRI I) _ _ (hT.pr_sm I c)), fun I => ?_, fun I y hy y' hy' => ?_,
      fun I J hIJ y hy y' hy' => ?_⟩⟩
  · rcases lt_or_gt_of_ne (hre I) with h | h
    · right
      rw [abs_of_neg h, div_neg, div_self (hre I)]
    · left
      rw [abs_of_pos h, div_self (hre I)]
  · have h1 := hc I y hy y' hy'
    rw [hh_smul, h1, ← mul_assoc]
    congr 1
    have h2 : (Real.sqrt |(cI I).re|)⁻¹ * (Real.sqrt |(cI I).re|)⁻¹ * (cI I).re = (cI I).re / |(cI I).re| := by
      rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_inv_mul]
    rw [← h2]
    simp only [ha, RCLike.star_def, Complex.conj_ofReal]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, hreal I]
  · rw [hh_smul, horth I J hIJ y hy y' hy', mul_zero]

end GlobalTheory.TensOrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.KStableFiniteDimSmoothCompactRootStable
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompactStable

open PI.UpqRep

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    {f : ℝ → H} {f' : H} (hf : HasDerivAt f f' 0) (hS : ∀ t, f t ∈ S) : f' ∈ S := by
  have hcl : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  have hsl := hasDerivAt_iff_tendsto_slope_zero.mp hf
  refine hcl.mem_of_tendsto hsl (Filter.Eventually.of_forall fun t => ?_)
  exact S.smul_of_tower_mem t⁻¹ (S.sub_mem (hS _) (hS _))

variable {k r : ℕ}

private lemma real_smul_skew_and_commute {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (hc : M * X = X * M)
    (t : ℝ) : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) ∧ M * ((t : ℂ) • X) = ((t : ℂ) • X) * M := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, hX, Complex.star_def, Complex.conj_ofReal, smul_neg]
  · rw [Matrix.mul_smul, hc, Matrix.smul_mul]

private lemma exp_real_smul_mem_UJset_of_inG {n : ℕ} (M Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ = -Y) (hc : M * Y = Y * M) :
    NormedSpace.exp Y ∈ UH M ∩ (Matrix.unitaryGroup (Fin n) ℂ : Set _) := by
  have hu : (NormedSpace.exp Y)ᴴ * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_conjTranspose, hY, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  have hcm : Commute M (NormedSpace.exp Y) := Commute.exp_right hc
  refine ⟨?_, ?_⟩
  · show (NormedSpace.exp Y)ᴴ * M * NormedSpace.exp Y = M
    rw [Matrix.mul_assoc, hcm.eq, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hu

theorem dsig_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    {X : Mx k r} (hX : Xᴴ = -X) (hc : Hpk k r * X = X * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X v ∈ S := by
  have hmem : ∀ t : ℝ, R.σ (NormedSpace.exp ((t : ℂ) • X)) v ∈ S := fun t =>
    hS _ (exp_real_smul_mem_UJset_of_inG _ _ (real_smul_skew_and_commute _ _ hX hc t).1 (real_smul_skew_and_commute _ _ hX hc t).2) v hv
  show deriv (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0 ∈ S
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0
  · exact deriv_mem S hd.hasDerivAt hmem
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact S.zero_mem

private lemma herm_eq_sum_star_mul_mulVec {n : ℕ} (M Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Mᴴ = M) (h2 : M * M = 1)
    (hc : M * Y = Y * M) : M * Yᴴ * M = Yᴴ ∧ M * Yᴴ = Yᴴ * M := by
  have hs : Yᴴ * M = M * Yᴴ := by
    have h0 := congrArg Matrix.conjTranspose hc
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1] at h0
  refine ⟨?_, hs.symm⟩
  rw [← hs, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem dC_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1)
    {Y : Mx k r} (hc : Hpk k r * Y = Y * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    R.dC Y v ∈ S := by
  have hH : Formalism.QuantumDeterminants.Hpk k r = Hpk k r := rfl
  obtain ⟨hθ, hcs⟩ := herm_eq_sum_star_mul_mulVec _ Y h1 h2 hc
  have e1 : ((1 / 2 : ℂ) • (Y + -Yᴴ))ᴴ = -((1 / 2 : ℂ) • (Y + -Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, ← smul_neg]
    congr 1
    · simp
    · abel
  have hI : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have e2 : ((1 / (2 * Complex.I)) • (Y - -Yᴴ))ᴴ = -((1 / (2 * Complex.I)) • (Y - -Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, hI, neg_smul]
    congr 2
    abel
  have c1 : Hpk k r * ((1 / 2 : ℂ) • (Y + -Yᴴ)) = ((1 / 2 : ℂ) • (Y + -Yᴴ)) * Hpk k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_neg, neg_mul, hc, hcs]
  have c2 : Hpk k r * ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) =
      ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) * Hpk k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_neg, neg_mul, hc, hcs]
  unfold BranchingSupport.Rep.dC
  rw [hH, hθ]
  exact S.add_mem (dsig_mem R S hS e1 c1 hv hsm) (S.smul_mem _ (dsig_mem R S hS e2 c2 hv hsm))

theorem Jm_single {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    Jm ε * Matrix.single a b (1 : ℂ) = Matrix.single a b 1 * Jm ε := by
  ext i j
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs <;> simp_all

private lemma unitary_conj_mem_and_commute_Jmat {n : ℕ} (Jmat M Q g : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hcay : Qᴴ * Jmat * Q = M)
    (hg : g ∈ UH M ∩ (Matrix.unitaryGroup (Fin n) ℂ : Set _)) :
    Q * g * Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Q * g * Qᴴ * Jmat = Jmat * (Q * g * Qᴴ) ∧
      Qᴴ * (Q * g * Qᴴ) * Q = g := by
  obtain ⟨hgM, hgU⟩ := hg
  have hgM' : gᴴ * M * g = M := hgM
  have q1 : Qᴴ * Q = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp hQ
    rwa [Matrix.star_eq_conjTranspose] at h0
  have q2 : Q * Qᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hQ
    rwa [Matrix.star_eq_conjTranspose] at h0
  have g2 : g * gᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hgU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hJ : Jmat = Q * M * Qᴴ := by
    rw [← hcay]
    calc Jmat = (Q * Qᴴ) * Jmat * (Q * Qᴴ) := by rw [q2, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (Qᴴ * Jmat * Q) * Qᴴ := by simp only [Matrix.mul_assoc]
  have hgc : M * g = g * M := by
    calc M * g = (g * gᴴ) * M * g := by rw [g2, Matrix.one_mul]
      _ = g * (gᴴ * M * g) := by simp only [Matrix.mul_assoc]
      _ = g * M := by rw [hgM']
  refine ⟨?_, ?_, ?_⟩
  · have hs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact q1
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hQ hgU) hs
  · rw [hJ]
    calc Q * g * Qᴴ * (Q * M * Qᴴ) = Q * g * (Qᴴ * Q) * M * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = Q * (M * g) * Qᴴ := by
          rw [q1, Matrix.mul_one, hgc]
          simp only [Matrix.mul_assoc]
      _ = Q * M * (Qᴴ * Q) * g * Qᴴ := by
          rw [q1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Q * M * Qᴴ * (Q * g * Qᴴ) := by simp only [Matrix.mul_assoc]
  · calc Qᴴ * (Q * g * Qᴴ) * Q = (Qᴴ * Q) * g * (Qᴴ * Q) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [q1, Matrix.one_mul, Matrix.mul_one]

theorem kStable_smooth_and_stable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → ∀ S : Submodule ℂ R.H, FiniteDimensional ℂ S → PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S → (∀ v ∈ S, R.KFin v ∧ v ∈ R.sm) ∧ ∀ a b, ε a = ε b → ∀ v ∈ S, R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v ∈ S := by
  intro hK k r ε mu R hR Q hQ S hfin hKS
  obtain ⟨⟨-, hcay⟩, hQU⟩ := hQ
  obtain ⟨-, -, -, -, hTKsm, -, hKTK, -, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have q1 : Qᴴ * Q = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp hQU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have q2 : Q * Qᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hQU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have hS' : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S,
      R.σ g x ∈ S := by
    intro g hg x hx
    obtain ⟨hu, hc, he⟩ := unitary_conj_mem_and_commute_Jmat _ _ Q g hQU hcay hg
    have hk : Q * g * Qᴴ ∈ Kset ε := by
      simp only [Kset, Set.mem_ofPred_eq]
      exact ⟨hu, hc⟩
    have h0 := hKS (Q * g * Qᴴ) hk x hx
    simp only [hinv, he] at h0
    exact h0
  have hsm : ∀ v ∈ S, R.KFin v ∧ v ∈ R.sm := by
    intro v hv
    have hkf : R.KFin v := by
      simp only [BranchingSupport.Rep.KFin, PI.UpqRep.IsKFinHpk]
      exact ⟨S, hfin, hv, hS'⟩
    exact ⟨hkf, hTKsm v (hKTK v hkf)⟩
  refine ⟨hsm, fun a b hab v hv => ?_⟩
  have h1 : (Hpk k r)ᴴ = Hpk k r := by
    rw [← hcay, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
    simp only [Matrix.mul_assoc]
  have h2 : Hpk k r * Hpk k r = 1 := by
    rw [← hcay]
    calc Qᴴ * Jm ε * Q * (Qᴴ * Jm ε * Q) = Qᴴ * Jm ε * (Q * Qᴴ) * Jm ε * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [q2, Matrix.mul_one, Matrix.mul_assoc (Qᴴ) (Jm ε), Jm_mul_self, Matrix.mul_one, q1]
  have hc : Hpk k r * (Q⁻¹ * Matrix.single a b 1 * Q) = (Q⁻¹ * Matrix.single a b 1 * Q) * Hpk k r := by
    rw [hinv, ← hcay]
    calc Qᴴ * Jm ε * Q * (Qᴴ * Matrix.single a b 1 * Q)
        = Qᴴ * Jm ε * (Q * Qᴴ) * Matrix.single a b 1 * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (Jm ε * Matrix.single a b 1) * Q := by
          rw [q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * (Matrix.single a b 1 * Jm ε) * Q := by rw [Jm_single ε hab]
      _ = Qᴴ * Matrix.single a b 1 * (Q * Qᴴ) * Jm ε * Q := by
          rw [q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * Matrix.single a b 1 * Q * (Qᴴ * Jm ε * Q) := by simp only [Matrix.mul_assoc]
  exact dC_mem R S hS' h1 h2 hc hv (hsm v hv).2

end GlobalTheory.CompactStable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDeterminantEigenvalue
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDeterminantEigenvalue
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliSmooth

lemma entry_conj {n : ℕ} (P P' : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (P * Matrix.single a b (1 : ℂ) * P') c d = P c a * P' b d := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hx, mul_zero]
  · simp

theorem qdet_smooth : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → ∀ (Y : ℂ) (w : R.smSub), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  intro hyp k r ε mu R hR Q E hQ hE Y w
  have hK : PI.KFinSmooth := hyp.1.2.2.1
  have hC := hyp.2.2.1
  obtain ⟨hmu, Q0, hQ0, hDS⟩ := id hR
  have hU0 : IsUnit Q0 := hQ0.1.1
  obtain ⟨E0, hE0, hgl⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR Q0 hU0
  obtain ⟨hsm, hd⟩ := GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport k r ε R Q0 hQ0
  obtain ⟨-, hexp, -⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q0 E0 hU0 hE0
  have hdQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hdQ0 : IsUnit Q0.det := (Matrix.isUnit_iff_isUnit_det Q0).1 hU0
  have hEE : E = Formalism.FourierDecayAlt.Q.Econj E0 (Q0 * Q⁻¹) (Q * Q0⁻¹) := by
    funext a b
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [hE a b v, hexp]
    have h1 : Q0 * (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * Q0⁻¹ =
        (Q0 * Q⁻¹) * Matrix.single a b (1 : ℂ) * (Q * Q0⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [h1]
    simp only [entry_conj, Formalism.FourierDecayAlt.Q.Econj, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have h2 : (Q * Q0⁻¹) * (Q0 * Q⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ0, Matrix.mul_nonsing_inv _ hdQ]
  have h3 : (Q0 * Q⁻¹) * (Q * Q0⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ, Matrix.mul_nonsing_inv _ hdQ0]
  rw [hEE, covariant_det_of_lin covariant_linear _ _ E0 _ _ hgl h2 h3]
  apply Subtype.ext
  have h4 := GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator _ ε R.H (fun g => R.σ (Q0⁻¹ * g * Q0)) R.smSub E0
    (fun a b v => by rw [hd, hE0 a b v]; rfl) (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w
  rw [← h4, hC _ ε mu R.H _ hmu hDS w (hsm w w.2) Y]
  rfl

end GlobalTheory.CapelliSmooth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDeterminantEigenvalueStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_eigenvalue : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → ∀ (Y : ℂ) (w : R.smSub), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  first | exact @GlobalTheory.CapelliSmooth.qdet_smooth | exact GlobalTheory.CapelliSmooth.qdet_smooth | (intros; apply GlobalTheory.CapelliSmooth.qdet_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureBesselPeriodSubgroupUnitary
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_isQuotMeas_bessel_subgroup : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    PI.BesselPeriodGGP.IsHaarOn (GG k r) μG →
    ∃ νq, PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq := by
  intro k r z μW μN μG hz hT hW hN hG
  obtain ⟨hGgrp, hGinv⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  obtain ⟨hGhaar, _⟩ := hGinv μG hG
  obtain ⟨hSgrp, hSsub, hShaar, hSright⟩ := GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN
  exact GlobalTheory.T.exists_quotientMeasure_weil (2 * r + k + 1) (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN)
    hGgrp hSgrp hSsub hGhaar hShaar hSright

end GlobalTheory
end
