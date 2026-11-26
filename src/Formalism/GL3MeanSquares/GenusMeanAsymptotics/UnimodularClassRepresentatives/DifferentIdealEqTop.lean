module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFilterResCharLe
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFiberMulCardRange

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop
open NumberField Module Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ a : K, star a ≠ a := by
  obtain ⟨hTC, hconj, -⟩ := hK
  by_contra h
  push_neg at h
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace K) := inferInstance
  have hc := hTC.isComplex w
  rw [NumberField.InfinitePlace.isComplex_iff] at hc
  apply hc
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext a
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hconj, h]

theorem star_algebraMap (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (u : F) :
    star (algebraMap F K u) = algebraMap F K u :=
  (hF _).2 ⟨u, rfl⟩

theorem exists_decomp (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {a : K}
    (ha : star a ≠ a) (x : K) : ∃ u v : F, x = algebraMap F K u + algebraMap F K v * a := by
  have hb : a - star a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  obtain ⟨w, hw⟩ : ∃ w : K, w * (a - star a) = x - star x :=
    ⟨(x - star x) / (a - star a), div_mul_cancel₀ _ hb⟩
  have hsw : star w = w := by
    have h1 := congrArg star hw
    rw [star_mul', star_sub, star_sub, star_star, star_star] at h1
    apply mul_right_cancel₀ hb
    linear_combination -h1 - hw
  obtain ⟨v, hv⟩ := (hF w).1 hsw
  have hz : star (x - w * a) = x - w * a := by
    rw [star_sub, star_mul', hsw]
    linear_combination hw
  obtain ⟨u, hu⟩ := (hF _).1 hz
  exact ⟨u, v, by rw [hu, hv]; ring⟩

theorem finrank_eq_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : finrank F K = 2 := by
  obtain ⟨a, ha⟩ := exists_star_ne hK
  have hli : LinearIndependent F ![(1 : K), a] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply ha
      have htK : algebraMap F K t ≠ 0 := (_root_.map_ne_zero _).mpr ht
      have hA : a = algebraMap F K (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_div₀, map_neg, eq_div_iff htK]
        linear_combination hst
      exact (hF a).2 ⟨_, hA.symm⟩
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), a]) := by
    intro x _
    obtain ⟨u, v, rfl⟩ := exists_decomp hF ha x
    apply Submodule.add_mem
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩)
  rw [Module.finrank_eq_card_basis (Basis.mk hli hsp)]
  simp

theorem adjoin_eq_top (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {a : K}
    (ha : star a ≠ a) : Algebra.adjoin F {a} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨u, v, rfl⟩ := exists_decomp hF ha x
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ u)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ v) (Algebra.subset_adjoin (Set.mem_singleton a)))

theorem coe_algebraMap (z : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) z) = algebraMap F K (algebraMap (𝓞 F) F z) := by
  rfl

theorem exists_int_of_star_eq (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))
    (y : 𝓞 K) (hy : star (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) K y) :
    ∃ z : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) z = y := by
  obtain ⟨u, hu⟩ := (hF _).1 hy
  have hint : IsIntegral ℤ u := by
    have h1 : IsIntegral ℤ (algebraMap F K u) := by
      rw [hu]; exact RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algebraMap_iff ).mp h1
  refine ⟨⟨u, hint⟩, ?_⟩
  apply RingOfIntegers.ext
  exact (coe_algebraMap (F := F) (K := K) ⟨u, hint⟩).trans hu

theorem isTotallyReal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : IsTotallyReal F := by
  obtain ⟨-, hconj, -⟩ := hK
  refine ⟨fun w => ?_⟩
  obtain ⟨v, rfl⟩ := NumberField.InfinitePlace.comap_surjective (k := F) (K := K) w
  try dsimp only
  rw [← NumberField.InfinitePlace.mk_embedding v, NumberField.InfinitePlace.comap_mk]
  by_contra h
  rw [NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isComplex_mk_iff] at h
  apply h
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext u
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hconj, star_algebraMap hF]

theorem minpoly_eq (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (θ t : 𝓞 K)
    (ht : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ)) (hne : θ ≠ t) :
    aeval θ (derivative (minpoly (𝓞 F) θ)) = θ - t := by
  have ht' : star (algebraMap (𝓞 K) K t) = algebraMap (𝓞 K) K θ := by rw [ht, star_star]
  obtain ⟨s, hs⟩ := exists_int_of_star_eq hF (θ + t) (by rw [map_add (f := _), star_add, ht', ← ht, add_comm])
  obtain ⟨p, hp⟩ := exists_int_of_star_eq hF (θ * t) (by rw [map_mul, star_mul', ht', ← ht, mul_comm])
  obtain ⟨q, hq⟩ : ∃ q : Polynomial (𝓞 F), q = X ^ 2 - C s * X + C p := ⟨_, rfl⟩
  have hqdeg : q.natDegree = 2 := by rw [hq]; compute_degree!
  have hqm : q.Monic := by rw [hq]; monicity!
  have hroot : aeval θ q = 0 := by
    rw [hq]
    simp only [map_add (f := _), map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hp]
    ring
  have hint : IsIntegral (𝓞 F) θ := by
    first
      | exact Algebra.IsIntegral.isIntegral θ
      | exact IsIntegral.tower_top (A := 𝓞 F) (RingOfIntegers.isIntegral θ)
      | exact (Algebra.IsIntegral.isIntegral (R := ℤ) θ).tower_top
  have hdvd : minpoly (𝓞 F) θ ∣ q := minpoly.isIntegrallyClosed_dvd hint hroot
  have hdeg2 : 2 ≤ (minpoly (𝓞 F) θ).natDegree := by
    by_contra hlt
    push_neg at hlt
    have h1 : (minpoly (𝓞 F) θ).natDegree = 1 := by
      have := minpoly.natDegree_pos hint
      omega
    have hd1 : (minpoly (𝓞 F) θ).degree = 1 := by
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), h1]
      rfl
    have hr : θ ∈ (algebraMap (𝓞 F) (𝓞 K)).range := by
      first
        | exact minpoly.mem_range_of_degree_eq_one (𝓞 F) θ hd1
        | exact minpoly.mem_range_of_degree_eq_one hd1
        | exact minpoly.mem_range_of_degree_eq_one (𝓞 F) hd1
    obtain ⟨z, hz⟩ := hr
    apply hne
    apply RingOfIntegers.ext
    have hfx : star (algebraMap (𝓞 K) K θ) = algebraMap (𝓞 K) K θ := by
      rw [← hz, coe_algebraMap]
      exact star_algebraMap hF _
    exact (ht.trans hfx).symm
  have heq : q = minpoly (𝓞 F) θ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqm hdvd (by rw [hqdeg]; exact hdeg2)
  rw [← heq, hq]
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow, derivative_C,
    derivative_X, zero_mul, mul_one, zero_add, add_zero, map_add, map_sub, map_mul, map_pow,
    aeval_X, aeval_C, map_natCast, hs]
  first
    | ring
    | (norm_num; ring)
    | norm_num
    | (push_cast; ring)

theorem differentIdeal_eq_top (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) :
    differentIdeal (𝓞 F) (𝓞 K) = ⊤ := by
  obtain ⟨-, -, hmax⟩ := hK
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hmax P hP
  have hne' : θ ≠ t := fun h => hθt (by rw [h, sub_self]; exact P.zero_mem)
  have hstar : star (algebraMap (𝓞 K) K θ) ≠ algebraMap (𝓞 K) K θ := by
    rw [← ht]; exact fun h => hne' (RingOfIntegers.ext h.symm)
  apply hθt
  apply hle
  rw [← minpoly_eq hF θ t ht hne']
  exact aeval_derivative_mem_differentIdeal (A := 𝓞 F) (K := F) (L := K) θ (adjoin_eq_top hF hstar)

theorem natAbs_discr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) :
    (discr K).natAbs = (discr F).natAbs ^ 2 := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) K (𝓞 K),
    differentIdeal_eq_top hK hF, Ideal.absNorm_top, one_mul, finrank_eq_two hK hF]

theorem discr_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : 0 < discr F := by
  haveI := isTotallyReal hK hF
  first
    | exact NumberField.discr_pos_of_isTotallyReal F
    | (have h := NumberField.sign_discr F
       rw [IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero] at h
       exact Int.sign_eq_one_iff_pos.mp h)

end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation

namespace Formalism.HermitianLattices.Ext.L3

theorem discrTower : DiscrTower := by
  intro K F _ _ _ _ _ _ hK hF
  have hpos := QuadraticExtensionConjugation.discr_pos hK hF
  have h1 := QuadraticExtensionConjugation.natAbs_discr hK hF
  have hTC : IsTotallyComplex K := by
    obtain ⟨h, -, -⟩ := hK
    exact h
  have hA : |(discr K : ℝ)| = (discr F : ℝ) ^ 2 := by
    have h2 := congrArg (fun n : ℕ => (n : ℝ)) h1
    simp only [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at h2
    rw [h2, sq_abs]
  have hdeg : finrank ℚ F = Formalism.HermitianLatticesTheory.fDeg K := by
    have e1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    have e2 := Module.finrank_mul_finrank ℚ F K
    have e3 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    have e4 : NumberField.InfinitePlace.nrRealPlaces K = 0 := by
      first
        | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero
        | exact IsTotallyComplex.nrRealPlaces_eq_zero
        | exact NumberField.InfinitePlace.nrRealPlaces_eq_zero_iff.mpr hTC
        | exact NumberField.nrRealPlaces_eq_zero_iff.mpr hTC
        | (haveI : IsEmpty {w : NumberField.InfinitePlace K // w.IsReal} :=
             ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩
           simp [NumberField.InfinitePlace.nrRealPlaces])
        | (unfold NumberField.InfinitePlace.nrRealPlaces
           rw [Fintype.card_eq_zero_iff]
           exact ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩)
    rw [QuadraticExtensionConjugation.finrank_eq_two hK hF] at e2
    unfold Formalism.HermitianLatticesTheory.fDeg
    omega
  refine ⟨hA, hdeg, ?_⟩
  have hF0 : (0 : ℝ) < discr F := by exact_mod_cast hpos
  have hd : 0 < Formalism.HermitianLatticesTheory.fDeg K := by
    unfold Formalism.HermitianLatticesTheory.fDeg
    exact Fintype.card_pos
  have hd0 : ((Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [show ∀ x : ℝ, 2 * (x / 2) = x from fun x => by ring, hA, ← Real.rpow_natCast (discr F : ℝ) 2,
    ← Real.rpow_mul hF0.le, ← Real.rpow_natCast _ (Formalism.HermitianLatticesTheory.fDeg K), ← Real.rpow_mul hF0.le]
  conv_lhs => rw [← Real.rpow_one (discr F : ℝ)]
  congr 1
  first
    | (push_cast; field_simp)
    | (push_cast; field_simp; ring)
    | field_simp
    | (field_simp; ring)

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandA
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def conjAlg : K ≃ₐ[ℚ] K := (starRingAut : RingAut K).toRatAlgEquiv

abbrev cmF : IntermediateField ℚ K := IntermediateField.fixedField (Subgroup.zpowers (conjAlg K))

theorem conjAlg_apply (x : K) : conjAlg K x = star x := rfl

theorem mem_cmF_iff (x : K) : x ∈ cmF K ↔ star x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h _ (Subgroup.mem_zpowers _)
  · intro h f hf
    have hs : conjAlg K ∈ MulAction.stabilizer (K ≃ₐ[ℚ] K) x :=
      MulAction.mem_stabilizer_iff.2 (by rw [AlgEquiv.smul_def, conjAlg_apply, h])
    have := MulAction.mem_stabilizer_iff.1 ((Subgroup.zpowers_le.2 hs) hf)
    rwa [AlgEquiv.smul_def] at this

theorem star_coe_cmF (x : cmF K) : star (x : K) = x := (mem_cmF_iff K x).1 x.2

variable {K}

theorem exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ a : K, star a ≠ a := by
  by_contra h
  push_neg at h
  let φ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  have hφ : ComplexEmbedding.IsReal φ := by
    rw [ComplexEmbedding.isReal_iff]
    ext a
    rw [ComplexEmbedding.conjugate_coe_eq, ← hK.2.1 φ a, h a]
  have hc := hK.1.isComplex (InfinitePlace.mk φ)
  rw [InfinitePlace.isComplex_mk_iff] at hc
  exact hc hφ

theorem exists_skew (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ w : K, w ≠ 0 ∧ star w = -w := by
  obtain ⟨a, ha⟩ := exists_star_ne hK
  refine ⟨a - star a, sub_ne_zero.2 (Ne.symm ha), ?_⟩
  rw [star_sub, star_star]
  ring

theorem isReal_embedding_cmF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (ψ : K →+* ℂ) :
    ComplexEmbedding.IsReal (ψ.comp (algebraMap (cmF K) K)) := by
  rw [ComplexEmbedding.isReal_iff]
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hK.2.1 ψ]
  exact congrArg ψ (star_coe_cmF K a)

theorem isReal_cmF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (v : InfinitePlace (cmF K)) : v.IsReal := by
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := K) v
  show (w.comap (algebraMap (cmF K) K)).IsReal
  have e : w.comap (algebraMap (cmF K) K) = InfinitePlace.mk (w.embedding.comp (algebraMap (cmF K) K)) := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  rw [e, InfinitePlace.isReal_mk_iff]
  exact isReal_embedding_cmF hK _

theorem totPos_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (a : cmF K) :
    TotPos (a : K) ↔ ∀ φ : cmF K →+* ℝ, 0 < φ a := by
  constructor
  · intro h φ
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := K) (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have hr := isReal_embedding_cmF hK w.embedding
    have hw' : InfinitePlace.mk (w.embedding.comp (algebraMap (cmF K) K)) =
        InfinitePlace.mk (Complex.ofRealHom.comp φ) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
      exact hw
    rw [InfinitePlace.mk_eq_iff] at hw'
    have e : w.embedding.comp (algebraMap (cmF K) K) = Complex.ofRealHom.comp φ := by
      rcases hw' with e | e
      · exact e
      · rwa [ComplexEmbedding.isReal_iff.1 hr] at e
    have h1 := h w.embedding
    have e2 : w.embedding (a : K) = (φ a : ℂ) := RingHom.congr_fun e a
    rw [e2, Complex.ofReal_re] at h1
    exact h1
  · intro h ψ
    have hr := isReal_embedding_cmF hK ψ
    have e : ((hr.embedding a : ℝ) : ℂ) = ψ (a : K) := hr.coe_embedding_apply a
    rw [← e, Complex.ofReal_re]
    exact h _

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EulerFacMulConjInvSplit
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace IdealNormInequalities

theorem zpow_neg_lt_one {x : ℝ} (hx : 1 < x) {M : ℕ} (hM : 1 ≤ M) : x ^ (-(M : ℤ)) < 1 := by
  rw [zpow_neg, zpow_natCast]
  exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by omega))

theorem zpow_neg_le {x p : ℝ} (hp : 1 ≤ p) (hx : p ≤ x) {M : ℕ} (hM : 2 ≤ M) :
    x ^ (-(M : ℤ)) ≤ (p ^ 2)⁻¹ := by
  rw [zpow_neg, zpow_natCast]
  refine inv_anti₀ (by positivity) ?_
  calc p ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hx 2
    _ ≤ x ^ M := pow_le_pow_right₀ (by linarith) hM

theorem two_le_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : 2 ≤ Ideal.absNorm P :=
  (resChar_prime hP).two_le.trans (resChar_le_absNorm hP)

theorem one_lt_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (1 : ℝ) < (Ideal.absNorm P : ℝ) := by
  exact_mod_cast (two_le_absNorm hP)

theorem one_lt_sqrt_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (1 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) := by
  rw [Real.lt_sqrt (by norm_num)]
  simpa using one_lt_absNorm hP

def smallTerm (M : ℕ) (P : Ideal (𝓞 K)) : ℝ :=
  if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then
    -((-1 : ℝ) ^ M * Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)))
  else -((Ideal.absNorm P : ℝ) ^ (-(M : ℤ)))

theorem abs_smallTerm_lt_one {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    |smallTerm M P| < 1 := by
  unfold smallTerm
  split_ifs with hc
  · rw [abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (zpow_nonneg (Real.sqrt_nonneg _) _)]
    exact zpow_neg_lt_one (one_lt_sqrt_absNorm hP) hM
  · rw [abs_neg, abs_of_nonneg (zpow_nonneg (Nat.cast_nonneg _) _)]
    exact zpow_neg_lt_one (one_lt_absNorm hP) hM

theorem one_add_smallTerm_pos {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    0 < 1 + smallTerm M P := by
  have := (abs_lt.mp (abs_smallTerm_lt_one hP hM)).1
  linarith

theorem abs_smallTerm_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ}
    (hM : 2 ≤ M) : |smallTerm M P| ≤ ((resChar P : ℝ) ^ 2)⁻¹ := by
  have hp1 : (1 : ℝ) ≤ (resChar P : ℝ) := by exact_mod_cast (resChar_prime hP).one_lt.le
  unfold smallTerm
  split_ifs with hc
  · rw [abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (zpow_nonneg (Real.sqrt_nonneg _) _)]
    obtain ⟨q, hq⟩ := exists_sq_absNorm_of_inert hK hP hc
    have hs : Real.sqrt (Ideal.absNorm P : ℝ) = q := by
      rw [hq]; push_cast; exact Real.sqrt_sq (Nat.cast_nonneg q)
    rw [hs]
    exact zpow_neg_le hp1 (by exact_mod_cast resChar_le_of_sq hP hq) hM
  · rw [abs_neg, abs_of_nonneg (zpow_nonneg (Nat.cast_nonneg _) _)]
    exact zpow_neg_le hp1 (by exact_mod_cast resChar_le_absNorm hP) hM

theorem eulerFac_eq (M : ℕ) (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.eulerFac K M P = if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then (1 + smallTerm M P)⁻¹
      else (1 + smallTerm M P) ^ (-(1 : ℝ) / 2) := by
  unfold Formalism.HermitianLatticesTheory.eulerFac smallTerm
  split_ifs with hc <;> simp only [← sub_eq_add_neg]

theorem abs_log_eulerFac_le {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {M : ℕ} (hM : 1 ≤ M) :
    |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P)| ≤ |Real.log (1 + smallTerm M P)| := by
  rw [eulerFac_eq]
  split_ifs with hc
  · rw [Real.log_inv, abs_neg]
  · rw [Real.log_rpow (one_add_smallTerm_pos hP hM), abs_mul]
    have : |(-(1 : ℝ) / 2)| = 1 / 2 := by rw [abs_of_nonpos (by norm_num)]; norm_num
    rw [this]
    nlinarith [abs_nonneg (Real.log (1 + smallTerm M P))]

theorem summable_log_eulerFac (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {M : ℕ} (hM : 2 ≤ M) :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) := by
  have h1 : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => smallTerm M P.1) :=
    Summable.of_norm_bounded summable_resChar_sq (fun P => abs_smallTerm_le hK P.2 hM)
  have h2 := (Real.summable_log_one_add_of_summable h1).abs
  exact Summable.of_norm_bounded h2 (fun P => abs_log_eulerFac_le P.2 (by omega))

end IdealNormInequalities

open IdealNormInequalities

theorem eulerFac_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (M : ℕ)
    (hM : 1 ≤ M) : 0 < Formalism.HermitianLatticesTheory.eulerFac K M P := by
  rw [eulerFac_eq]
  split_ifs with hc
  · exact inv_pos.mpr (one_add_smallTerm_pos hP hM)
  · exact Real.rpow_pos_of_pos (one_add_smallTerm_pos hP hM) _

theorem eulerFac_inv_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M : ℕ) :
    (Formalism.HermitianLatticesTheory.eulerFac K M P)⁻¹ =
      1 - (-1 : ℝ) ^ M * Real.sqrt (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by
  unfold Formalism.HermitianLatticesTheory.eulerFac
  rw [if_pos hc, inv_inv]

theorem eulerFac_mul_conj_inv_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M : ℕ) (hM : 1 ≤ M) :
    (Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P))⁻¹ =
      1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by
  have hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠
      Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [conjIdeal_conjIdeal hK]; exact hc.symm
  have hx : 0 < 1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) :=
    sub_pos.mpr (zpow_neg_lt_one (one_lt_absNorm hP) hM)
  unfold Formalism.HermitianLatticesTheory.eulerFac
  rw [if_neg hc, if_neg hc', absNorm_conjIdeal hK, ← Real.rpow_add hx]
  norm_num [Real.rpow_neg_one]

theorem multipliable_eulerFac (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1) :=
  Real.multipliable_of_summable_log (fun P => eulerFac_pos hK P.2 M (by omega))
    (summable_log_eulerFac hK hM)

theorem lValEta_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.lValEta K M := by
  unfold Formalism.HermitianLatticesTheory.lValEta
  rw [← Real.rexp_tsum_eq_tprod (fun P => eulerFac_pos hK P.2 M (by omega))
    (summable_log_eulerFac hK hM)]
  exact Real.exp_pos _

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountPowSuccInert
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.NormLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  first
  | exact RingOfIntegers.ext (star_star (x : K))
  | (apply RingOfIntegers.ext; simp [conjO])
  | (apply RingOfIntegers.ext; unfold conjO; simp)

theorem eq_conjO_of {θ t : 𝓞 K} (h : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ)) :
    t = conjO K θ := by
  apply RingOfIntegers.ext
  have h' : (t : K) = star (θ : K) := h
  rw [h']
  first
  | rfl
  | simp [conjO]
  | (unfold conjO; simp)

def conjQ (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) : (𝓞 K ⧸ J) →+* (𝓞 K ⧸ J) :=
  Ideal.quotientMap J (conjO K) (fun a ha => hJ a ha)

theorem conjQ_mk (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) (a : 𝓞 K) :
    conjQ J hJ (Ideal.Quotient.mk J a) = Ideal.Quotient.mk J (conjO K a) := by
  first
  | rfl
  | exact Ideal.quotientMap_mk
  | simp [conjQ]

theorem normRepCount_eq (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) (M : ℕ) (n : 𝓞 K) :
    normRepCount K J M n =
      Nat.card {x : Fin M → 𝓞 K ⧸ J // ∑ i, conjQ J hJ (x i) * x i = Ideal.Quotient.mk J n} := by
  unfold normRepCount
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  have key : ∀ y : Fin M → 𝓞 K, (∀ i, Ideal.Quotient.mk J (y i) = x i) →
      Ideal.Quotient.mk J (∑ i, conjO K (y i) * y i) = ∑ i, conjQ J hJ (x i) * x i := by
    intro y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hy i, conjQ_mk]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [← key y hy, h]
  · intro h
    refine ⟨fun i => (Ideal.Quotient.mk_surjective (x i)).choose,
      fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec, ?_⟩
    rw [key _ (fun i => (Ideal.Quotient.mk_surjective (x i)).choose_spec), h]

theorem exists_inv_mod {J : Ideal (𝓞 K)} {a : 𝓞 K} (h : IsCoprime (Ideal.span {a}) J) :
    ∃ b : 𝓞 K, Ideal.Quotient.mk J a * Ideal.Quotient.mk J b = 1 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  refine ⟨b, ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq, ← hij]
  have e : a * b - (b * a + j) = -j := by ring
  rw [e]
  exact J.neg_mem hj

theorem stable_pow {Q : Ideal (𝓞 K)} (hQ : Q.map (conjO K) = Q) (k : ℕ) :
    ∀ a ∈ Q ^ k, conjO K a ∈ Q ^ k := by
  intro a ha
  have h1 := Ideal.mem_map_of_mem (conjO K) ha
  rwa [Ideal.map_pow, hQ] at h1

theorem normRepCount_pow_succ_of {Q : Ideal (𝓞 K)} (hQ0 : Q ≠ ⊥) (hQ : Q.map (conjO K) = Q)
    (θ n : 𝓞 K) (hθ : IsCoprime (Ideal.span {θ - conjO K θ}) Q)
    (hnQ : IsCoprime (Ideal.span {n}) Q) (hn : conjO K n = n) (q : ℕ)
    (hq : Ideal.absNorm Q = q ^ 2) (M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k) :
    normRepCount K (Q ^ (k + 1)) M n = q ^ (2 * M - 1) * normRepCount K (Q ^ k) M n := by
  rw [normRepCount_eq _ (stable_pow hQ (k + 1)), normRepCount_eq _ (stable_pow hQ k)]
  have hle : Q ^ (k + 1) ≤ Q ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
  have : Finite (𝓞 K ⧸ Q ^ (k + 1)) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ hQ0)
  obtain ⟨e, he⟩ := exists_inv_mod (hθ.pow_right (n := k + 1))
  obtain ⟨m, hm⟩ := exists_inv_mod (hnQ.pow_right (n := k + 1))
  have h := card_lift (σ := conjQ _ (stable_pow hQ (k + 1))) (τ := conjQ _ (stable_pow hQ k))
    (π := Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [conjQ_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, conjQ_mk])
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [conjQ_mk, conjQ_mk, conjO_conjO])
    (by
      intro a b ha hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at ha hb
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have h2 : a * b ∈ Q ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul ha hb
      exact Ideal.pow_le_pow_right (by omega) h2)
    (θ := Ideal.Quotient.mk _ θ) (e := Ideal.Quotient.mk _ e)
    (by rw [conjQ_mk, ← map_sub]; exact he)
    (n := Ideal.Quotient.mk _ n) (m := Ideal.Quotient.mk _ m) hm
    (by rw [conjQ_mk, hn]) q
    (by
      have h1 : ∀ J : Ideal (𝓞 K), Nat.card (𝓞 K ⧸ J) = Ideal.absNorm J := fun J => by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [h1, h1, map_pow, map_pow, hq]; ring) M hM
  rw [Ideal.Quotient.factor_mk] at h
  exact h

theorem isCoprime_span_of_notMem {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {a : 𝓞 K} (ha : a ∉ P) :
    IsCoprime (Ideal.span {a}) P := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  have h2 := hP.eq_of_le h le_sup_right
  exact ha (by rw [h2]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))

end Formalism.HermitianLattices.Ext.L3.NormLifting

namespace Formalism.HermitianLattices.Ext.L3

open NormLifting

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private lemma map_conjO_eq_conjIdeal (P : Ideal (𝓞 K)) :
    P.map (conjO K) = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal Ideal.map
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    show ((conjO K s : 𝓞 K) : K) = star ((s : 𝓞 K) : K)
    first
    | rfl
    | (symm; simp [conjO])
    | simp [conjO]
    | (unfold conjO; simp)
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, (eq_conjO_of h).symm⟩

theorem normRepCount_pow_succ_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) (q : ℕ)
    (hq : Ideal.absNorm P = q ^ 2) :
    normRepCount K (P ^ (k + 1)) M n = q ^ (2 * M - 1) * normRepCount K (P ^ k) M n := by
  obtain ⟨θ, t, ht, hθP⟩ := hK.2.2 P hP
  rw [eq_conjO_of ht] at hθP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hmap : P.map (conjO K) = P := by rw [map_conjO_eq_conjIdeal]; exact hc
  exact normRepCount_pow_succ_of hP0 hmap θ n (isCoprime_span_of_notMem hP hθP)
    (isCoprime_span_of_notMem hP hnP) hn q hq M k hM hk

theorem normRepCount_pow_succ_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ (k + 1)) M n =
      Ideal.absNorm P ^ (2 * M - 1) *
        normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) M n := by
  obtain ⟨θ, t, ht, hθP⟩ := hK.2.2 P hP
  rw [eq_conjO_of ht] at hθP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  generalize hPbdef : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = Pb
  have hm : P.map (conjO K) = Pb := by rw [← hPbdef]; exact map_conjO_eq_conjIdeal P
  have hcc : (conjO K).comp (conjO K) = RingHom.id _ := RingHom.ext conjO_conjO
  have hmm : ∀ I : Ideal (𝓞 K), (I.map (conjO K)).map (conjO K) = I := fun I => by
    rw [Ideal.map_map, hcc, Ideal.map_id]
  have hPb0 : Pb ≠ ⊥ := by
    intro h
    apply hP0
    rw [← hmm P, hm, h, Ideal.map_bot]
  have hQ0 : P * Pb ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨hP0, hPb0⟩
  have hQ : (P * Pb).map (conjO K) = P * Pb := by
    rw [Ideal.map_mul, ← hm, hmm, mul_comm]
  have hcop : ∀ a, IsCoprime (Ideal.span {a}) P → IsCoprime (Ideal.span {conjO K a}) Pb := by
    intro a ha
    rw [Ideal.isCoprime_iff_sup_eq] at ha ⊢
    have h3 := congrArg (Ideal.map (conjO K)) ha
    rwa [Ideal.map_sup, Ideal.map_top, hm, Ideal.map_span, Set.image_singleton] at h3
  have h1 := isCoprime_span_of_notMem hP hθP
  have h4 := hcop _ h1
  rw [map_sub, conjO_conjO, ← Ideal.span_singleton_neg (conjO K θ - θ), neg_sub] at h4
  have hθ : IsCoprime (Ideal.span {θ - conjO K θ}) (P * Pb) := IsCoprime.mul_right h1 h4
  have h5 := isCoprime_span_of_notMem hP hnP
  have h6 := hcop _ h5
  rw [hn] at h6
  have hnQ : IsCoprime (Ideal.span {n}) (P * Pb) := IsCoprime.mul_right h5 h6
  have hnorm : Ideal.absNorm Pb = Ideal.absNorm P := by
    have hbij : Function.Bijective (conjO K) :=
      ⟨Function.LeftInverse.injective (g := conjO K) (fun x => conjO_conjO x),
        Function.RightInverse.surjective (g := conjO K) (fun x => conjO_conjO x)⟩
    let f : 𝓞 K ≃+* 𝓞 K := RingEquiv.ofBijective (conjO K) hbij
    have e := Ideal.quotientEquiv P Pb f (by rw [← hm]; rfl)
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr e.toEquiv).symm
  have hq : Ideal.absNorm (P * Pb) = Ideal.absNorm P ^ 2 := by rw [map_mul, hnorm, sq]
  have hQ' : (P * Pb).map (conjO K) = P * Pb := hQ
  exact normRepCount_pow_succ_of hQ0 hQ' θ n hθ hnQ hn (Ideal.absNorm P) hq M k hM hk

end Formalism.HermitianLattices.Ext.L3
end
end
