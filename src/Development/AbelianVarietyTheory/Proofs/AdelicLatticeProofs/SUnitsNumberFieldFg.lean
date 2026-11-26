module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

noncomputable section

namespace GlobalTheory.QNorm

private lemma valuation_algebraMap_unit_eq_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (u : (𝓞 F)ˣ) : v.valuation F (algebraMap (𝓞 F) F u) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun h => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)

private lemma exists_unit_of_valuation_eq_one {F : Type} [Field F] [NumberField F] (y : Fˣ)
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y = 1) :
    ∃ u : (𝓞 F)ˣ, algebraMap (𝓞 F) F u = y := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (y : F)
    fun v => (hy v).le
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((y⁻¹ : Fˣ) : F)
    fun v => by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hy v, inv_one]
  have hab : a * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ha⟩

theorem _root_.GlobalTheory.QNorm.sUnits_fg :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
      Group.FG (_root_.GlobalTheory.QNorm.sUnits F S) := by
  intro F _ _ S
  set G := _root_.GlobalTheory.QNorm.sUnits F S
  let val : HeightOneSpectrum (𝓞 F) → G →* Multiplicative ℤ := fun v =>
    (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
      (Units.map (v.valuation F : F →* ℤᵐ⁰))).comp G.subtype
  have hval : ∀ v x, val v x = 1 ↔ v.valuation F ((x : Fˣ) : F) = 1 := by
    intro v x
    simp only [val, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, Units.ext_iff, Units.coe_map, Units.val_one]
    rfl
  let f : Additive G →+ (S → ℤ) :=
    { toFun := fun x v => Multiplicative.toAdd (val v.1 x.toMul)
      map_zero' := by ext v; simp
      map_add' := fun x y => by ext v; simp }
  let ψ : (𝓞 F)ˣ →* G :=
    { toFun := fun u => ⟨Units.map (algebraMap (𝓞 F) F : (𝓞 F) →* F) u, by
        rw [_root_.GlobalTheory.QNorm.mem_sUnits]
        intro v _
        exact valuation_algebraMap_unit_eq_one v u⟩
      map_one' := by ext; simp
      map_mul' := fun u w => by ext; simp }
  let g : Additive (𝓞 F)ˣ →+ Additive G := MonoidHom.toAdditive ψ
  have hker : f.toIntLinearMap.ker = LinearMap.range g.toIntLinearMap := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, AddMonoidHom.coe_toIntLinearMap]
    constructor
    · intro hx
      obtain ⟨u, hu⟩ := exists_unit_of_valuation_eq_one ((x.toMul : G) : Fˣ) fun v => by
        by_cases hv : v ∈ S
        · rw [← hval]
          have := congrFun hx ⟨v, hv⟩
          simpa [f] using this
        · exact (_root_.GlobalTheory.QNorm.mem_sUnits F S _).mp x.toMul.2 v hv
      refine ⟨Additive.ofMul u, ?_⟩
      apply Additive.toMul.injective
      ext
      simpa [g, ψ] using hu
    · rintro ⟨u, rfl⟩
      ext v
      have : val v.1 (ψ u.toMul) = 1 :=
        (hval _ _).mpr (valuation_algebraMap_unit_eq_one v.1 u.toMul)
      simpa [f, g] using this
  have htop : (⊤ : Submodule ℤ (Additive G)).FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker f.toIntLinearMap (IsNoetherian.noetherian _) ?_
    rw [top_inf_eq, hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  have : Module.Finite ℤ (Additive G) := ⟨htop⟩
  rw [Group.fg_iff_monoid_fg, Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg]
  exact Module.Finite.iff_addGroup_fg.mp this

end GlobalTheory.QNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFgStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sUnitsNumberField_fg : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), Group.FG (sUnits F S) := by
  first | exact @GlobalTheory.QNorm.sUnits_fg | exact GlobalTheory.QNorm.sUnits_fg | (intros; apply GlobalTheory.QNorm.sUnits_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFacts
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}

theorem _root_.GlobalTheory.QNorm.IsQuad.coord_indep
    (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (a b : F)
    (hab : algebraMap F E a + algebraMap F E b * θ = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply h.nonsq
    refine ⟨-a / b, (algebraMap F E).injective ?_⟩
    have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
    have hθ : θ = -algebraMap F E a / algebraMap F E b := by
      field_simp
      linear_combination hab
    rw [← h.sq, hθ]
    simp [map_div₀, map_neg]
    ring
  subst hb
  refine ⟨(algebraMap F E).injective ?_, rfl⟩
  simpa using hab

theorem _root_.GlobalTheory.QNorm.IsQuad.root_ne_zero (h : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) :
    θ ≠ 0 := by
  intro hθ
  apply h.nonsq
  refine ⟨0, (algebraMap F E).injective ?_⟩
  rw [← h.sq, hθ]
  simp

end

theorem _root_.GlobalTheory.QNorm.isQuad_basic : ∀ (F E : Type) [Field F] [CharZero F] [Field E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ a : F, x = algebraMap F E a) ∧
    (∀ a b : F, algebraMap F E a + algebraMap F E b * θ = 0 → a = 0 ∧ b = 0) ∧
    (∀ x : E, ∃ a b : F, x * σ x = algebraMap F E (a ^ 2 - δ * b ^ 2)) ∧
    (∀ x : E, x * σ x = 1 → ∃ y : E, y ≠ 0 ∧ x = y / σ y) ∧
    (∀ u : F, IsSquare (algebraMap F E u) → IsSquare u ∨ IsSquare (u * δ)) ∧
    Module.finrank F E = 2 := by
  intro F E _ _ _ _ δ θ σ h
  have t1 := h.coord_indep
  have hθ := h.root_ne_zero
  have hc := h.conj
  have hs := h.sq
  refine ⟨?_, ?_, t1, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    simp [AlgEquiv.commutes, hc]
  · intro x hx
    obtain ⟨a, b, rfl⟩ := h.span x
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hc] at hx
    have := t1 0 (2 * b) (by simp only [map_zero, map_mul, map_ofNat]; linear_combination -hx)
    have hb : b = 0 := by simpa using this.2
    exact ⟨a, by simp [hb]⟩
  · intro x
    obtain ⟨a, b, rfl⟩ := h.span x
    refine ⟨a, b, ?_⟩
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hc, map_sub, map_pow]
    linear_combination (-(algebraMap F E b) ^ 2) * hs
  · intro x hx
    by_cases h1 : x = -1
    · refine ⟨θ, hθ, ?_⟩
      rw [hc, h1, div_neg, div_self hθ]
    · have hy : (1 + x) ≠ 0 := fun h0 => h1 (by linear_combination h0)
      have hσy : σ (1 + x) ≠ 0 := by
        rwa [ne_eq, map_eq_zero_iff _ σ.injective]
      refine ⟨1 + x, hy, ?_⟩
      rw [eq_div_iff hσy, map_add (f := _), map_one]
      linear_combination hx
  · rintro u ⟨y, hy⟩
    obtain ⟨a, b, rfl⟩ := h.span y
    have := t1 (u - a ^ 2 - b ^ 2 * δ) (-(2 * a * b)) (by
      simp only [map_sub, map_mul, map_pow, map_neg, map_ofNat]
      linear_combination hy + (algebraMap F E b) ^ 2 * hs)
    have h2 : a * b = 0 := by
      have h3 := this.2
      have h4 : (2 : F) * (a * b) = 0 := by linear_combination -h3
      simpa using h4
    have hu : u = a ^ 2 + b ^ 2 * δ := by linear_combination this.1
    rcases mul_eq_zero.1 h2 with ha | hb
    · right; exact ⟨b * δ, by rw [hu, ha]; ring⟩
    · left; exact ⟨a, by rw [hu, hb]; ring⟩
  · have hli : LinearIndependent F ![(1 : E), θ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      apply t1
      simpa [Algebra.smul_def] using hst
    have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), θ]) := by
      intro x _
      obtain ⟨a, b, rfl⟩ := h.span x
      rw [Matrix.range_cons_cons_empty]
      refine Submodule.mem_span_pair.2 ⟨a, b, ?_⟩
      simp [Algebra.smul_def]
    simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFactsStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuadraticSqrtExtension_basic_facts : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → (∀ x, σ (σ x) = x) ∧ (∀ x, σ x = x → ∃ a : F, x = algebraMap F E a) ∧ (∀ a b : F, algebraMap F E a + algebraMap F E b * θ = 0 → a = 0 ∧ b = 0) ∧ (∀ x : E, ∃ a b : F, x * σ x = algebraMap F E (a ^ 2 - δ * b ^ 2)) ∧ (∀ x : E, x * σ x = 1 → ∃ y : E, y ≠ 0 ∧ x = y / σ y) ∧ (∀ u : F, IsSquare (algebraMap F E u) → IsSquare u ∨ IsSquare (u * δ)) ∧ Module.finrank F E = 2 := by
  first | exact @GlobalTheory.QNorm.isQuad_basic | exact GlobalTheory.QNorm.isQuad_basic | (intros; apply GlobalTheory.QNorm.isQuad_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquare
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_isQuad : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E),
      IsQuad δ θ σ := by
  intro F _ _ δ hδ
  have hroot : ∀ b : F, b ^ 2 ≠ δ := fun b hb => hδ ⟨b, by rw [← hb, sq]⟩
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C δ) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hroot
  have hmon : (Polynomial.X ^ 2 - Polynomial.C δ).Monic := Polynomial.monic_X_pow_sub_C δ two_ne_zero
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C δ).natDegree = 2 := Polynomial.natDegree_X_pow_sub_C _
  have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C δ)) := ⟨hirr⟩
  set p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C δ with hp
  have hsq : AdjoinRoot.root p ^ 2 = AdjoinRoot.of p δ := by
    have h := AdjoinRoot.eval₂_root p
    rw [hp, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    exact sub_eq_zero.mp h
  have hneg : Polynomial.eval₂ (↑(Algebra.ofId F (AdjoinRoot p)) : F →+* AdjoinRoot p)
      (-AdjoinRoot.root p) (Polynomial.X ^ 2 - Polynomial.C δ) = 0 := by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, neg_sq, hsq, sub_eq_zero]
    rfl
  let τ : AdjoinRoot p →ₐ[F] AdjoinRoot p :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId F (AdjoinRoot p)) (-AdjoinRoot.root p) hneg
  have hτ : τ (AdjoinRoot.root p) = -AdjoinRoot.root p := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hττ : τ.comp τ = AlgHom.id F (AdjoinRoot p) := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hτ, map_neg, neg_neg]
  have hp0 : p ≠ 0 := hmon.ne_zero
  have : Module.Finite F (AdjoinRoot p) := (AdjoinRoot.powerBasis hp0).finite
  have : CharZero (AdjoinRoot p) :=
    charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p)).injective
  have : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans F (AdjoinRoot p)
  refine ⟨AdjoinRoot p, inferInstance, { }, inferInstance, AdjoinRoot.root p,
    AlgEquiv.ofAlgHom τ τ hττ hττ, ⟨hδ, ?_, hτ, ?_⟩⟩
  · rw [AdjoinRoot.algebraMap_eq]; exact hsq
  · intro x
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    have hp1 : p ≠ 1 := fun h => by
      rw [h, Polynomial.natDegree_one] at hdeg; exact absurd hdeg (by norm_num)
    have hlt := Polynomial.natDegree_modByMonic_lt g hmon hp1
    rw [hdeg] at hlt
    have hr := Polynomial.eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hlt)
    refine ⟨(g %ₘ p).coeff 0, (g %ₘ p).coeff 1, ?_⟩
    have hmk : AdjoinRoot.mk p g = AdjoinRoot.mk p (g %ₘ p) := by
      conv_lhs => rw [← Polynomial.modByMonic_add_div g p]
      rw [map_add (f := _), map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    conv_lhs => rw [hr]
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      AdjoinRoot.algebraMap_eq, add_comm]

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquareStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ := by
  first | exact @GlobalTheory.QNorm.exists_isQuad | exact GlobalTheory.QNorm.exists_isQuad | (intros; apply GlobalTheory.QNorm.exists_isQuad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BlockDiagPartOfRatIdempotentOneAndMulOfTriangula
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BlockDiagPartOfRatIdempotentOneAndMulOfTriangula
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem peirce_block_decomposition {A : Type*} [Ring A] (E F : A) (hE : E * E = E) (hF : F * F = F) (hEF : E * F = 0)
    (hFE : F * E = 0) (h1 : E + F = 1) :
    E * 1 * E + F * 1 * F = 1 ∧
    (∀ x y : A, F * x * E = 0 → F * y * E = 0 →
      E * (x * y) * E + F * (x * y) * F = (E * x * E + F * x * F) * (E * y * E + F * y * F) ∧
        F * (x * y) * E = 0) ∧
    (∀ x : A, F * x * E = 0 → x = (E * x * E + F * x * F) + E * x * F) ∧
    (∀ x : A, E * (E * x * E + F * x * F) * E + F * (E * x * E + F * x * F) * F = E * x * E + F * x * F) := by
  have hE' : ∀ z, E * (E * z) = E * z := fun z => by rw [← mul_assoc, hE]
  have hF' : ∀ z, F * (F * z) = F * z := fun z => by rw [← mul_assoc, hF]
  have hEF' : ∀ z, E * (F * z) = 0 := fun z => by rw [← mul_assoc, hEF, zero_mul]
  have hFE' : ∀ z, F * (E * z) = 0 := fun z => by rw [← mul_assoc, hFE, zero_mul]
  refine ⟨by rw [mul_one, mul_one, hE, hF, h1], ?_, ?_, ?_⟩
  · intro x y hx hy
    have hxy : x * y = x * (E + F) * y := by rw [h1, mul_one]
    have hx' : ∀ z, F * (x * (E * z)) = 0 := fun z => by
      rw [← mul_assoc, ← mul_assoc, hx, zero_mul]
    have hy' : F * (y * E) = 0 := by rw [← mul_assoc, hy]
    rw [hxy]
    constructor
    · simp only [mul_add, add_mul, mul_assoc, hE', hF', hEF', hFE', hx', hy', mul_zero, add_zero, zero_add]
    · simp only [mul_add, add_mul, mul_assoc, hx', hy', mul_zero, zero_mul, add_zero]
  · intro x hx
    calc x = (E + F) * x * (E + F) := by rw [h1, one_mul, mul_one]
      _ = E * x * E + F * x * F + E * x * F + F * x * E := by noncomm_ring
      _ = _ := by rw [hx, add_zero]
  · intro x
    simp only [mul_add, add_mul, mul_assoc, hE', hF', hEF', hFE', hE, hF, add_zero, zero_add]

theorem blk_mul_of_triangular : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R], e * e = e → blk e (1 : Matrix ι ι R) = 1 ∧ (∀ x y : Matrix ι ι R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 → (1 - e.map (algebraMap ℚ R)) * y * e.map (algebraMap ℚ R) = 0 → blk e (x * y) = blk e x * blk e y ∧ (1 - e.map (algebraMap ℚ R)) * (x * y) * e.map (algebraMap ℚ R) = 0) ∧ (∀ x : Matrix ι ι R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 → x = blk e x + e.map (algebraMap ℚ R) * x * (1 - e.map (algebraMap ℚ R))) ∧ (∀ x : Matrix ι ι R, blk e (blk e x) = blk e x) ∧ ∀ γ : Matrix ι ι ℚ, blk e (γ.map (algebraMap ℚ R)) = (blk e γ).map (algebraMap ℚ R) := by
  intro ι _ _ e R _ _ he
  have hE : e.map (algebraMap ℚ R) * e.map (algebraMap ℚ R) = e.map (algebraMap ℚ R) := by
    rw [← Matrix.map_mul, he]
  obtain ⟨h1, h2, h3, h4⟩ := peirce_block_decomposition (e.map (algebraMap ℚ R)) (1 - e.map (algebraMap ℚ R)) hE
    (by rw [sub_mul, mul_sub, mul_sub, hE]; simp) (by rw [mul_sub, hE]; simp)
    (by rw [sub_mul, hE]; simp) (by simp)
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro γ
  have hid : e.map (algebraMap ℚ ℚ) = e := by
    ext i j
    simp
  change _ = (algebraMap ℚ R).mapMatrix (blk e γ)
  unfold blk
  rw [hid]
  simp only [map_add (f := _), map_mul, map_sub, map_one, RingHom.mapMatrix_apply]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BlockDiagPartOfRatIdempotentOneAndMulOfTriangulaStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDiagPartOfRatIdempotent_one_and_mul_of_triangular : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (e : Matrix ι ι ℚ) (R : Type) [CommRing R] [Algebra ℚ R], e * e = e → blk e (1 : Matrix ι ι R) = 1 ∧ (∀ x y : Matrix ι ι R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 → (1 - e.map (algebraMap ℚ R)) * y * e.map (algebraMap ℚ R) = 0 → blk e (x * y) = blk e x * blk e y ∧ (1 - e.map (algebraMap ℚ R)) * (x * y) * e.map (algebraMap ℚ R) = 0) ∧ (∀ x : Matrix ι ι R, (1 - e.map (algebraMap ℚ R)) * x * e.map (algebraMap ℚ R) = 0 → x = blk e x + e.map (algebraMap ℚ R) * x * (1 - e.map (algebraMap ℚ R))) ∧ (∀ x : Matrix ι ι R, blk e (blk e x) = blk e x) ∧ ∀ γ : Matrix ι ι ℚ, blk e (γ.map (algebraMap ℚ R)) = (blk e γ).map (algebraMap ℚ R) := by
  first | exact @GlobalTheory.ClassFin.blk_mul_of_triangular | exact GlobalTheory.ClassFin.blk_mul_of_triangular | (intros; apply GlobalTheory.ClassFin.blk_mul_of_triangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleToMatrixIffIsSemisimpleRepres
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleToMatrixIffIsSemisimpleRepres
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private theorem subrepresentation_isCompl_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (p q : Subrepresentation ρ) :
    IsCompl p q ↔ IsCompl p.toSubmodule q.toSubmodule := by
  rw [isCompl_iff, isCompl_iff, disjoint_iff, disjoint_iff, codisjoint_iff, codisjoint_iff,
    Subrepresentation.ext_iff, Subrepresentation.ext_iff, Subrepresentation.toSubmodule_inf,
    Subrepresentation.toSubmodule_sup]
  rfl

theorem _root_.GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V), _root_.GlobalTheory.ClassFin.SS (Set.range fun g => LinearMap.toMatrix b b (ρ g)) ↔ ρ.IsSemisimpleRepresentation := by
  intro ι _ _ G _ V _ _ ρ b
  set e := b.equivFun
  have he : ∀ (g : G) (v : V), (LinearMap.toMatrix b b (ρ g)).mulVec (e v) = e (ρ g v) := fun g v =>
    LinearMap.toMatrix_mulVec_repr b b (ρ g) v

  have hmap : ∀ p : Submodule ℂ V, (∀ (g : G) ⦃v : V⦄, v ∈ p → ρ g v ∈ p) →
      ∀ M ∈ Set.range (fun g => LinearMap.toMatrix b b (ρ g)), ∀ w ∈ p.map (e : V →ₗ[ℂ] (ι → ℂ)),
        M.mulVec w ∈ p.map (e : V →ₗ[ℂ] (ι → ℂ)) := by
    rintro p hp _ ⟨g, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hp g hv, (he g v).symm⟩
  have hcomap : ∀ W : Submodule ℂ (ι → ℂ),
      (∀ M ∈ Set.range (fun g => LinearMap.toMatrix b b (ρ g)), ∀ w ∈ W, M.mulVec w ∈ W) →
        ∀ (g : G) ⦃v : V⦄, v ∈ W.comap (e : V →ₗ[ℂ] (ι → ℂ)) → ρ g v ∈ W.comap (e : V →ₗ[ℂ] (ι → ℂ)) := by
    intro W hW g v hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
    rw [← he]
    exact hW _ ⟨g, rfl⟩ _ hv
  let Φ := Submodule.orderIsoMapComap e
  constructor
  · intro hS
    refine ⟨fun p => ?_⟩
    obtain ⟨W', hW', hc⟩ := hS _ (hmap p.toSubmodule p.apply_mem_toSubmodule)
    refine ⟨⟨W'.comap (e : V →ₗ[ℂ] (ι → ℂ)), hcomap W' hW'⟩, ?_⟩
    rw [subrepresentation_isCompl_iff]
    have := (Φ.symm.isCompl_iff).1 hc
    simpa [Φ, Submodule.comap_map_eq_of_injective e.injective] using this
  · intro hC W hW
    obtain ⟨q, hq⟩ := hC.exists_isCompl ⟨W.comap (e : V →ₗ[ℂ] (ι → ℂ)), hcomap W hW⟩
    refine ⟨q.toSubmodule.map (e : V →ₗ[ℂ] (ι → ℂ)), hmap _ q.apply_mem_toSubmodule, ?_⟩
    rw [subrepresentation_isCompl_iff] at hq
    have := (Φ.isCompl_iff).1 hq
    simpa [Φ, Submodule.map_comap_eq_of_surjective e.surjective] using this

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleToMatrixIffIsSemisimpleRepresStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V), SS (Set.range fun g => LinearMap.toMatrix b b (ρ g)) ↔ ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation | exact GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation | (intros; apply GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnits
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

namespace DeepSquares

end DeepSquares

private lemma exp_neg_two_mul_le_mul_of_lt {e : ℕ} {a b : ℤᵐ⁰}
    (ha : WithZero.exp (-((e : ℤ) + 1)) < a) (hb : WithZero.exp (-((e : ℤ) + 1)) < b) :
    WithZero.exp (-(2 * (e : ℤ))) ≤ a * b := by
  obtain ⟨k, rfl⟩ : ∃ k, WithZero.exp k = a := ⟨_, WithZero.exp_log (ne_bot_of_gt ha)⟩
  obtain ⟨l, rfl⟩ : ∃ l, WithZero.exp l = b := ⟨_, WithZero.exp_log (ne_bot_of_gt hb)⟩
  rw [WithZero.exp_lt_exp] at ha hb
  rw [← WithZero.exp_add, WithZero.exp_le_exp]
  omega

theorem _root_.GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ),
    Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) →
    _root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤
      _root_.GlobalTheory.QNorm.sqs
        (_root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by
  intro F _ _ v e h2 x hx
  unfold _root_.GlobalTheory.QNorm.hiUnits at hx
  unfold _root_.GlobalTheory.QNorm.sqs _root_.GlobalTheory.QNorm.hiUnits
  obtain ⟨-, hx1⟩ := hx
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have h4 : w 4 = WithZero.exp (-(2 * e : ℤ)) := by
    have : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
    rw [this, map_mul, h2, ← WithZero.exp_add]; congr 1; ring
  have hlt : w ((x : v.adicCompletion F) - 1) < w 4 := by
    refine lt_of_le_of_lt hx1 ?_
    rw [h4, WithZero.exp_lt_exp]; push_cast; omega
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v _ hlt
  have hprod : w (r - 1) * w (r + 1) ≤ WithZero.exp (-((2 * e + 1 : ℕ) : ℤ)) := by
    rw [← map_mul, show (r - 1) * (r + 1) = r * r - 1 by ring, ← hr]; exact hx1
  obtain ⟨s, hs, hs1⟩ : ∃ s : v.adicCompletion F, s * s = x ∧
      w (s - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ)) := by
    by_cases hm : w (r - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · exact ⟨r, hr.symm, hm⟩
    by_cases hp : w (r + 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · refine ⟨-r, by rw [neg_mul_neg, hr], ?_⟩
      rwa [show -r - 1 = -(r + 1) by ring, Valuation.map_neg]
    exfalso
    push_cast at hm hp hprod
    have := (exp_neg_two_mul_le_mul_of_lt (not_le.mp hm) (not_le.mp hp)).trans hprod
    rw [WithZero.exp_le_exp] at this
    omega
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact x.ne_zero hs.symm
  have hsv : w s = 1 := by
    have hlt1 : w (s - 1) < 1 :=
      hs1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using Valuation.map_one_add_of_lt w hlt1
  refine ⟨Units.mk0 s hs0, ⟨hsv, hs1⟩, ?_⟩
  ext
  simp [pow_two, hs]

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnitsStatement
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherUnits_le_squares_higherUnits : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) → hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤ sqs (hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by
  first | exact @GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits | exact GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits | (intros; apply GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmCharacterConjugateInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeAlgebraMapOfConjFixed
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem mem_range_algebraMap_of_conj_fixed (F E : Type) [Field F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (e : E) (he : σ e = e) :
    ∃ c : F, algebraMap F E c = e := by
  have := Subalgebra.isSimpleOrder_of_finrank h2
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
  · have hm : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := by
      rw [AlgHom.mem_equalizer]; simpa using he
    rw [h] at hm
    exact Algebra.mem_bot.mp hm
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hm : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
    rw [AlgHom.mem_equalizer] at hm
    have h1 := hσ τ x
    rw [hm] at h1
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact h1.symm

theorem exists_mul_conj_eq_algebraMap (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (R : Type) [CommRing R] [Algebra F R]
    (y : R ⊗[F] E) :
    ∃ n : R, y * Algebra.TensorProduct.map (AlgHom.id F R) σ y = algebraMap R (R ⊗[F] E) n := by
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hσ, hσ, star_star]
  set φ := Algebra.TensorProduct.map (AlgHom.id F R) σ with hφ
  have key : ∀ y z : R ⊗[F] E, ∃ n : R, y * φ z + z * φ y = algebraMap R (R ⊗[F] E) n := by
    intro y z
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨n₁, h₁⟩ := h₁
      obtain ⟨n₂, h₂⟩ := h₂
      exact ⟨n₁ + n₂, by rw [map_add (f := _), map_add (f := _), ← h₁, ← h₂]; ring⟩
    | tmul a e =>
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add z₁ z₂ h₁ h₂ =>
        obtain ⟨n₁, h₁⟩ := h₁
        obtain ⟨n₂, h₂⟩ := h₂
        exact ⟨n₁ + n₂, by rw [map_add (f := _), map_add (f := _), ← h₁, ← h₂]; ring⟩
      | tmul b f =>
        obtain ⟨c, hc⟩ := mem_range_algebraMap_of_conj_fixed F E σ hE h2 hσ
          (e * σ f + f * σ e) (by rw [map_add (f := _), map_mul, map_mul, hinv, hinv]; ring)
        refine ⟨c • (a * b), ?_⟩
        rw [hφ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          AlgHom.id_apply, AlgHom.id_apply, mul_comm b a, ← TensorProduct.tmul_add, ← hc,
          Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  obtain ⟨n, hn⟩ := key y y
  refine ⟨algebraMap F R (1 / 2) * n, ?_⟩
  have h : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
  have h' : algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap R (R ⊗[F] E)) 2, ← map_mul, h, map_one]
  rw [map_mul, ← hn, ← two_mul, ← mul_assoc, h', one_mul]

theorem exists_unit_mul_conj_eq_algebraMap :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → ∀ (R : Type) [CommRing R] [Algebra F R] (x : (R ⊗[F] E)ˣ), ∃ n : Rˣ, (x : R ⊗[F] E) * Algebra.TensorProduct.map (AlgHom.id F R) σ (x : R ⊗[F] E) = algebraMap R (R ⊗[F] E) n := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ R _ _ x
  obtain ⟨n, hn⟩ := exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R (x : R ⊗[F] E)
  obtain ⟨m, hm⟩ := exists_mul_conj_eq_algebraMap F E σ hE h2 hσ R ((x⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap F E).injective
  have hnm : n * m = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hn, ← hm, mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, mul_one]
  exact ⟨⟨n, m, hnm, by rw [mul_comm, hnm]⟩, hn⟩

end GlobalTheory
end

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem ideleChar_conj_eq_inv_of_trivial_on_base :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ χ : (AE F E)ˣ →* Circle, (∀ a : (AF F)ˣ, χ (idF F E a) = 1) → ∀ x y : (AE F E)ˣ, (y : AE F E) = cA σ x → χ y = (χ x)⁻¹ := by
  intro F E _ _ _ _ _ σ h χ hχ x y hy
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨n, hn⟩ := exists_unit_mul_conj_eq_algebraMap F E σ h1 h2 h3 h4 (AF F) x
  have hxy : x * y = idF F E n := by
    apply Units.ext
    rw [Units.val_mul, hy]
    exact hn
  have h5 : χ x * χ y = 1 := by rw [← map_mul, hxy, hχ]
  exact eq_inv_of_mul_eq_one_right h5

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPart
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPart
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private lemma idempotent_corner_part_mul {A : Type} [Ring A] (E g h : A) (hE : E * E = E)
    (hg : (1 - E) * g * E = 0) (hh : (1 - E) * h * E = 0) :
    (E * g * E + (1 - E) * g * (1 - E)) * (E * h * E + (1 - E) * h * (1 - E)) =
      E * (g * h) * E + (1 - E) * (g * h) * (1 - E) := by
  have h1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have h3 : (1 - E) * (1 - E) = 1 - E := by rw [mul_sub, mul_one, h2, sub_zero]
  set F := 1 - E with hF
  have hs : E + F = 1 := by rw [hF]; abel
  have a1 : E * (g * h) * E = E * g * E * h * E := by
    calc E * (g * h) * E = E * g * (E + F) * h * E := by rw [hs]; noncomm_ring
      _ = E * g * E * h * E + E * g * (F * h * E) := by noncomm_ring
      _ = _ := by rw [hh, mul_zero, add_zero]
  have a2 : F * (g * h) * F = F * g * F * h * F := by
    calc F * (g * h) * F = F * g * (E + F) * h * F := by rw [hs]; noncomm_ring
      _ = (F * g * E) * h * F + F * g * F * h * F := by noncomm_ring
      _ = _ := by rw [hg, zero_mul, zero_mul, zero_add]
  rw [a1, a2]
  calc _ = E * g * (E * E) * h * E + E * g * (E * F) * h * F + F * g * (F * E) * h * E
        + F * g * (F * F) * h * F := by noncomm_ring
    _ = _ := by rw [hE, h1, h2, h3]; noncomm_ring

private lemma idempotent_corner_sum_one {A : Type} [Ring A] (E : A) (hE : E * E = E) :
    E * 1 * E + (1 - E) * 1 * (1 - E) = 1 := by
  have : E * 1 * E + (1 - E) * 1 * (1 - E) = 1 + 2 * (E * E - E) := by noncomm_ring
  rw [this, hE, sub_self, mul_zero, add_zero]

private lemma idempotent_corner_part_inv {A : Type} [Ring A] (E g h : A) (hE : E * E = E)
    (hg : (1 - E) * g * E = 0) (hh : (1 - E) * h * E = 0) (hgh : g * h = 1) :
    g * (E * h * E + (1 - E) * h * (1 - E)) = 1 + E * (-(g * E * h) * (1 - E)) := by
  have h2 : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  set F := 1 - E with hF
  have hs : E + F = 1 := by rw [hF]; abel
  have a1 : E * g * E = g * E := by
    calc E * g * E = E * g * E + F * g * E := by rw [hg, add_zero]
      _ = (E + F) * g * E := by noncomm_ring
      _ = _ := by rw [hs, one_mul]
  have a2 : h = (E * h * E + F * h * F) + E * h * F := by
    calc h = (E + F) * h * (E + F) := by rw [hs, one_mul, mul_one]
      _ = (E * h * E + F * h * F) + E * h * F + F * h * E := by noncomm_ring
      _ = _ := by rw [hh, add_zero]
  have a3 : g * (E * h * E + F * h * F) + g * (E * h * F) = 1 := by
    rw [← mul_add, ← a2, hgh]
  calc g * (E * h * E + F * h * F) = 1 - g * E * h * F := by
        rw [← a3]; noncomm_ring
    _ = 1 - E * g * E * h * F := by rw [a1]
    _ = _ := by noncomm_ring

theorem isPre_blk_image :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsPre Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → IsPre (blk e '' Γ) := by
  intro ι _ _ Γ e hΓ he htri
  have hE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, he]
  have hmul : ∀ g ∈ Γ, ∀ h ∈ Γ, blk e g * blk e h = blk e (g * h) := fun g hg h hh =>
    idempotent_corner_part_mul _ g h hE (htri g hg) (htri h hh)
  have hone : blk e (1 : Matrix ι ι ℂ) = 1 := idempotent_corner_sum_one _ hE
  have hga : ∀ g ∈ Γ, g * g.adjugate = 1 := fun g hg => by
    rw [Matrix.mul_adjugate, hΓ.det_eq g hg, one_smul]
  have hinv : ∀ g ∈ Γ, blk e g * blk e g.adjugate = 1 := fun g hg => by
    rw [hmul g hg _ (hΓ.adj_mem g hg), hga g hg, hone]
  have hdet : ∀ g ∈ Γ, (blk e g).det = 1 := fun g hg => by
    have h1 := idempotent_corner_part_inv _ g g.adjugate hE (htri g hg) (htri _ (hΓ.adj_mem g hg)) (hga g hg)
    have h2 : (g * blk e g.adjugate).det = 1 := by
      unfold blk
      rw [h1, Matrix.det_one_add_mul_comm, mul_assoc, sub_mul, one_mul, hE, sub_self, mul_zero,
        add_zero, Matrix.det_one]
    rw [Matrix.det_mul, hΓ.det_eq g hg, one_mul] at h2
    have h3 := congrArg Matrix.det (hinv g hg)
    rwa [Matrix.det_mul, h2, mul_one, Matrix.det_one] at h3
  refine ⟨⟨1, hΓ.one_mem, hone⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact ⟨g * h, hΓ.mul_mem g hg h hh, (hmul g hg h hh).symm⟩
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨g.adjugate, hΓ.adj_mem g hg, ?_⟩
    calc blk e g.adjugate = ((blk e g).adjugate * blk e g) * blk e g.adjugate := by
          rw [Matrix.adjugate_mul, hdet g hg, one_smul, one_mul]
      _ = _ := by rw [mul_assoc, hinv g hg, mul_one]
  · rintro _ ⟨g, hg, rfl⟩
    exact hdet g hg
  · rintro σ _ ⟨g, hg, rfl⟩
    refine ⟨g.map σ, hΓ.aut_mem σ g hg, ?_⟩
    have hσ : (σ : ℂ →+* ℂ).mapMatrix (e.map (algebraMap ℚ ℂ)) = e.map (algebraMap ℚ ℂ) := by
      ext i j
      simp
    change _ = (σ : ℂ →+* ℂ).mapMatrix (blk e g)
    unfold blk
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_mul, map_sub, map_one, hσ]
    rfl

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPartStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsPre Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → IsPre (blk e '' Γ) := by
  first | exact @GlobalTheory.ClassFin.isPre_blk_image | exact GlobalTheory.ClassFin.isPre_blk_image | (intros; apply GlobalTheory.ClassFin.isPre_blk_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CardRingHomRealEqNrRealPlaces
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem card_ringHom_real_eq_nrRealPlaces :
    ∀ (F : Type) [Field F] [NumberField F], Nat.card (F →+* ℝ) = InfinitePlace.nrRealPlaces F := by
  intro F _ _
  let e : (F →+* ℝ) ≃ {φ : F →+* ℂ // ComplexEmbedding.IsReal φ} :=
    { toFun := fun ψ => ⟨Complex.ofRealHom.comp ψ, by
        rw [ComplexEmbedding.isReal_iff]
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]⟩
      invFun := fun φ => φ.2.embedding
      left_inv := fun ψ => by
        ext x
        simp [ComplexEmbedding.IsReal.embedding]
      right_inv := fun φ => by
        apply Subtype.ext
        ext x
        simp }
  classical
  rw [Nat.card_congr (e.trans InfinitePlace.mkReal), Nat.card_eq_fintype_card]

end GlobalTheory.QNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatPolyEvalEqTensorPowerSumRightAction
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatPolyEvalEqTensorPowerSumRightAction
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_mvPolynomial_ev_eq_act : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), ∃ Φ : TIdx ι d → MvPolynomial (ι × ι) ℚ, ∀ (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) (k : TIdx ι d), ev (Φ k) y = act d (fun k => algebraMap ℚ R (t k)) y k := by
  intro ι _ _ m d t
  refine ⟨fun k => ∑ a : Fin (d k.1) → ι,
    MvPolynomial.C (t ⟨k.1, a⟩) * ∏ i, MvPolynomial.X (a i, k.2 i), ?_⟩
  intro R _ _ y k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ev, act, tpow, Matrix.vecMul, dotProduct, map_sum, map_prod,
    MvPolynomial.aeval_X]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatPolyEvalEqTensorPowerSumRightActionStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratPoly_eval_eq_tensorPowerSumRightAction : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), ∃ Φ : TIdx ι d → MvPolynomial (ι × ι) ℚ, ∀ (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R) (k : TIdx ι d), ev (Φ k) y = act d (fun k => algebraMap ℚ R (t k)) y k := by
  first | exact @GlobalTheory.ClassFin.exists_mvPolynomial_ev_eq_act | exact GlobalTheory.ClassFin.exists_mvPolynomial_ev_eq_act | (intros; apply GlobalTheory.ClassFin.exists_mvPolynomial_ev_eq_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsHermitianLogOfPosDefGram
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsHermitianLogOfPosDefGram
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_isLog_gram : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι ℂ), IsUnit x.det → ∃ H : Matrix ι ι ℂ, IsLog H (xᴴ * x) := by
  intro ι _ _ x hx
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hx
  have hp : (xᴴ * x).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self x (Matrix.mulVec_injective_iff_isUnit.2 hu)
  have hs := hp.1.spectral_theorem
  refine ⟨_, (hp.1.eigenvectorUnitary : Matrix ι ι ℂ), fun i => Real.log (hp.1.eigenvalues i), ?_, rfl, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff).1 hp.1.eigenvectorUnitary.2
  · have he : (fun i => ((Real.exp (Real.log (hp.1.eigenvalues i)) : ℝ) : ℂ)) = RCLike.ofReal ∘ hp.1.eigenvalues := by
      funext i
      rw [Real.exp_log (hp.eigenvalues_pos i)]
      rfl
    rw [he]
    exact hs

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsHermitianLogOfPosDefGramStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHermitianLogOfPosDef_gram : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι ℂ), IsUnit x.det → ∃ H : Matrix ι ι ℂ, IsLog H (xᴴ * x) := by
  first | exact @GlobalTheory.ClassFin.exists_isLog_gram | exact GlobalTheory.ClassFin.exists_isLog_gram | (intros; apply GlobalTheory.ClassFin.exists_isLog_gram <;> assumption)
end
end
