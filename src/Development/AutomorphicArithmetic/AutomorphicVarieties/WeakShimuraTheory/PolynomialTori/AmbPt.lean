module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AlLoc
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsValuationExtensionIntegral
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralExtensionAlgClosed
theorem UpperTheory.Reformulated.B.IntegralExtensionAlgClosed.exists_ringHom_extension_of_integral :
    ∀ (R S K : Type) [inst : CommRing R] [inst_1 : CommRing S]
    [inst_2 : Algebra R S] [Algebra.IsIntegral R S] [inst_4 : Field K] [IsAlgClosed K],
    Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
      ∀ (b : R →+* K), ∃ (Φ : S →+* K), Φ.comp (Algebra.algebraMap R S) = b := by
  intro R S K _ _ _ _ _ _ hinj b
  haveI hp : (RingHom.ker b).IsPrime := RingHom.ker_isPrime b
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker b) ⊥ (by
      intro x hx
      have hx0 : algebraMap R S x = 0 := by simpa using hx
      have : x = 0 := hinj (by simpa using hx0)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker b) := ⟨hQp.symm⟩
  letI : Algebra (R ⧸ RingHom.ker b) K := (RingHom.kerLift b).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective b)
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : FaithfulSMul (R ⧸ RingHom.ker b) (S ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker b) K :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker b) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ : (S ⧸ Q) →ₐ[R ⧸ RingHom.ker b] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext x
  exact ψ.commutes (Ideal.Quotient.mk (RingHom.ker b) x)
end

private theorem UpperTheory.exists_ringHom_extension_of_integral (R S K : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Field K] [IsAlgClosed K]
    (hinj : Function.Injective (algebraMap R S)) (b : R →+* K) :
    ∃ Φ : S →+* K, Φ.comp (algebraMap R S) = b :=
  _root_.UpperTheory.Reformulated.B.IntegralExtensionAlgClosed.exists_ringHom_extension_of_integral R S K hinj b

theorem UpperTheory.exists_valuation_extension_integral :
    ∀ (R S K : Type) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] [Field K] [IsAlgClosed K] (V : ValuationSubring K), Function.Injective (algebraMap R S) → ∀ b : R →+* V, ∃ Φ : S →+* V, Φ.comp (algebraMap R S) = b := by
  intro R S K _ _ _ _ _ _ V hinj b
  obtain ⟨Φ, hΦ⟩ := UpperTheory.exists_ringHom_extension_of_integral R S K hinj ((algebraMap V K).comp b)
  have hmem : ∀ s : S, Φ s ∈ V := by
    intro s
    have hs : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    have h2 : IsIntegral V (Φ s) := hs.map_of_comp_eq b Φ hΦ.symm
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := K)).1 h2
    rw [← hy]; exact y.2
  refine ⟨Φ.codRestrict V hmem, ?_⟩
  ext r
  exact RingHom.congr_fun hΦ r
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralClosurePreimageOfIsIntegral
open Polynomial in
theorem UpperTheory.exists_integralClosure_preimage_of_isIntegral :
    ∀ (R E k : Type) [CommRing R] [Field E] [IsAlgClosed E] [Algebra R E] [CommRing k] [IsDomain k] (ψ : integralClosure R E →+* k) (x : k), IsIntegral ℤ x → ∃ y, ψ y = x := by
  intro R E k _ _ _ _ _ _ ψ x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := hx
  set q : E[X] := p.map (algebraMap ℤ E) with hq
  have hqm : q.Monic := hpm.map _
  have hqs : q.Splits := IsAlgClosed.splits q
  let lift : E → integralClosure R E := fun a => if h : IsIntegral R a then ⟨a, h⟩ else 0
  have hlift : ∀ a ∈ q.roots, ((lift a : integralClosure R E) : E) = a := by
    intro a ha
    have hr : q.IsRoot a := (mem_roots hqm.ne_zero).1 ha
    have hi : IsIntegral ℤ a := ⟨p, hpm, by
      rw [eval₂_eq_eval_map]
      exact hr⟩
    have hiR : IsIntegral R a := hi.tower_top
    simp [lift, hiR]
  have hfac : p.map (algebraMap ℤ (integralClosure R E)) = (q.roots.map fun a => X - C (lift a)).prod := by
    apply Polynomial.map_injective (algebraMap (integralClosure R E) E) Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
    have e : (algebraMap (integralClosure R E) E).comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ E :=
      RingHom.ext_int _ _
    rw [e, ← hq]
    conv_lhs => rw [hqs.eq_prod_roots_of_monic hqm]
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
    congr 2
    exact (hlift a ha).symm
  have hk : p.map (algebraMap ℤ k) = (q.roots.map fun a => X - C (ψ (lift a))).prod := by
    have e : ψ.comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ k := RingHom.ext_int _ _
    rw [← e, ← Polynomial.map_map, hfac, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have h0 : (p.map (algebraMap ℤ k)).eval x = 0 := by
    rw [eval_map]
    exact hpx
  rw [hk, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff] at h0
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.1 h0
  refine ⟨lift a, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at ha
  exact (sub_eq_zero.1 ha).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ResidueIsIntegralOfAlgebraicOverDvr
private theorem UpperTheory.algebraic_over_finite_field_integral (k L : Type) [Field k] [Finite k] [Field L] [Algebra k L]
    (y : L) (h : IsAlgebraic k y) : IsIntegral ℤ y := by
  have hi : IsIntegral k y := h.isIntegral
  haveI : FiniteDimensional k (IntermediateField.adjoin k {y}) := IntermediateField.adjoin.finiteDimensional hi
  haveI : Finite (IntermediateField.adjoin k {y}) := Module.finite_of_finite k
  let g : ℕ → IntermediateField.adjoin k {y} := fun n =>
    ⟨y ^ (n + 1), pow_mem (IntermediateField.mem_adjoin_simple_self k y) _⟩
  obtain ⟨m, n, hmn, hg⟩ := Finite.exists_ne_map_eq_of_infinite g
  have hpow : y ^ (m + 1) = y ^ (n + 1) := congrArg Subtype.val hg
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · refine ⟨Polynomial.X ^ (n + 1) - Polynomial.X ^ (m + 1), Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X_pow]
      exact_mod_cast Nat.succ_lt_succ hlt
    · simp [hpow]
  · refine ⟨Polynomial.X ^ (m + 1) - Polynomial.X ^ (n + 1), Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X_pow]
      exact_mod_cast Nat.succ_lt_succ hlt
    · simp [hpow]

open Polynomial in
theorem UpperTheory.residue_isIntegral_of_algebraic_over_dvr :
    ∀ (A K : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] [Field K] (V : ValuationSubring K) (f : A →+* V), Function.Injective f → IsLocalHom f → ∀ x : V, (∃ p : Polynomial A, p ≠ 0 ∧ p.eval₂ (V.subtype.comp f) x = 0) → IsIntegral ℤ (IsLocalRing.residue V x) := by
  intro A K _ _ _ _ _ V f hf _ x hx
  classical
  obtain ⟨p, hp0, hpx⟩ := hx
  letI : NormalizationMonoid A := UniqueFactorizationMonoid.normalizationMonoid.toNormalizationMonoid
  letI : NormalizedGCDMonoid A := UniqueFactorizationMonoid.toNormalizedGCDMonoid A
  have hV : Polynomial.eval₂ f x p = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero]
    exact (Polynomial.hom_eval₂ p f V.subtype x).trans hpx
  set q := p.primPart with hq
  have hcont : f p.content ≠ 0 := by
    intro h0
    apply hp0
    rw [← Polynomial.content_eq_zero_iff]
    exact hf (h0.trans (map_zero f).symm)
  have hqx : Polynomial.eval₂ f x q = 0 := by
    have e := Polynomial.eq_C_content_mul_primPart p
    rw [e, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hV
    exact (mul_eq_zero.1 hV).resolve_left hcont
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hqbar : q.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C π ∣ q := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi : IsLocalRing.residue A (q.coeff i) = 0 := by
        rw [← Polynomial.coeff_map, h0, Polynomial.coeff_zero]
      rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hi
      exact hi
    exact hπ.not_isUnit (Polynomial.isPrimitive_primPart p π hdvd)
  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) :=
    (IsLocalRing.ResidueField.map f).toAlgebra
  have halg : IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.residue V x) := by
    refine ⟨q.map (IsLocalRing.residue A), hqbar, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have e : (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue A) =
        (IsLocalRing.residue V).comp f := by
      ext a
      exact IsLocalRing.ResidueField.map_residue f a
    rw [e, ← Polynomial.hom_eval₂, hqx, map_zero]
  exact UpperTheory.algebraic_over_finite_field_integral (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField V) _ halg
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem al_loc {l : ℕ} [Fact l.Prime] (c : Coef l) {B : Type} [CommRing B] [IsDomain B] [CharP B l] (g : c.O →+* B) :
    IsLocalHom g := by
  have hl : (l : c.O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hk : RingHom.ker g ≠ ⊥ := fun h => hl (by
    have : (l : c.O) ∈ RingHom.ker g := by rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    rwa [h, Ideal.mem_bot] at this)
  have hm : RingHom.ker g = maximalIdeal c.O := eq_maximalIdeal ((RingHom.ker_isPrime g).isMaximal hk)
  refine ⟨fun x hx => by_contra fun h => hx.ne_zero ?_⟩
  have : x ∈ RingHom.ker g := hm ▸ (mem_maximalIdeal x).2 h
  exact this

private theorem al_le {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O ≤ integralClosure ℤ_[l] (PadicAlgCl l) := fun x hx =>
  (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val

theorem UpperTheory.V.Ws.ambL :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      [Finite (ResidueField A)] [CharP A l] (a : c.O →+* A), ∃ (𝔞 : Amb l) (f : A →+* 𝔞.V), CharP 𝔞.K l ∧ 𝔞.IsDvr f ∧ f.comp a = 𝔞.a c := by
  intro l _ c A _ _ _ _ _ _ a
  haveI := c.dvr
  haveI := c.fin
  let K := AlgebraicClosure (FractionRing A)
  let g0 : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hg0 : Function.Injective g0 :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing g0
  let f : A →+* V := g0.codRestrict V hV
  have hfinj : Function.Injective f := fun x y h => hg0 (congrArg Subtype.val h)
  have hfloc : IsLocalHom f := hloc
  haveI hK : CharP K l := charP_of_injective_ringHom hg0 l
  haveI : CharP V l := charP_of_injective_ringHom hfinj l
  have heq : V.subtype.comp f = g0 := RingHom.ext fun _ => rfl
  have halg : ∀ z : K, ∃ p : A[X], p ≠ 0 ∧ eval₂ (V.subtype.comp f) z p = 0 := by
    intro z
    obtain ⟨q, hq0, hq⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing A) z
    refine ⟨IsLocalization.integerNormalization (nonZeroDivisors A) q, ?_, ?_⟩
    · rwa [Ne, IsFractionRing.integerNormalization_eq_zero_iff]
    · rw [Polynomial.aeval_def] at hq
      rw [heq]
      exact IsLocalization.integerNormalization_eval₂_eq_zero (nonZeroDivisors A)
        (algebraMap (FractionRing A) K) q hq
  let S := integralClosure c.O (PadicAlgCl l)
  have hinj : Function.Injective (algebraMap c.O S) := by
    intro x y h
    apply Subtype.ext
    have h2 := congrArg Subtype.val h
    exact h2
  obtain ⟨Φ, hΦ⟩ := UpperTheory.exists_valuation_extension_integral c.O S K V hinj (f.comp a)
  have hS : ∀ c' : Coef l, ∀ x : c'.O, (x : PadicAlgCl l) ∈ S := fun c' x =>
    IsIntegral.tower_top (A := c.O) (al_le c' x.2)
  let ι : ∀ c' : Coef l, c'.O →+* S := fun c' => c'.O.val.toRingHom.codRestrict S (hS c')
  refine ⟨Amb.mk K V (fun c' => Φ.comp (ι c')) ?_ ?_ ?_, f, hK, ⟨hfinj, hfloc, inferInstance, inferInstance, halg⟩, ?_⟩
  · intro c1 c2 h x
    exact congrArg Φ (Subtype.ext rfl)
  · intro c'
    exact al_loc c' _
  · intro x
    obtain ⟨p, hp0, hp⟩ := halg x
    have hint := UpperTheory.residue_isIntegral_of_algebraic_over_dvr A K V f hfinj hfloc x ⟨p, hp0, hp⟩
    obtain ⟨y, hy⟩ := UpperTheory.exists_integralClosure_preimage_of_isIntegral c.O (PadicAlgCl l) (ResidueField V)
      ((IsLocalRing.residue V).comp Φ) (IsLocalRing.residue V x) hint
    have hyl : IsIntegral ℤ_[l] (y : PadicAlgCl l) := isIntegral_trans (A := c.O) _ y.2
    obtain ⟨c', -, hc'⟩ := (coefSup l).2.2.1 c y.1 hyl
    refine ⟨c', ⟨y.1, hc'⟩, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hy]
    rfl
  · exact hΦ.symm.trans (congrArg Φ.comp (RingHom.ext fun x => Subtype.ext rfl))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinPow
open IsLocalRing

private theorem exists_fg_sup_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n

theorem UpperTheory.V.Ws.Po.finPow {O A : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing A] [IsLocalRing A] [Algebra O A] [IsNoetherianRing A]
    (hloc : (maximalIdeal O).map (algebraMap O A) ≤ maximalIdeal A)
    (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ maximalIdeal A) (n : ℕ)
    (hn : maximalIdeal A ^ n ≤ (maximalIdeal O).map (algebraMap O A)) : Module.Finite O A := by
  haveI : IsHausdorff (maximalIdeal A) A := IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal A).ne_top
  haveI : IsHausdorff (maximalIdeal O) A := IsHausdorff.of_map hloc
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) A).2 ?_
  obtain ⟨N, hN, hx⟩ := exists_fg_sup_pow (maximalIdeal A) hres n
  have : N.map (maximalIdeal O • (⊤ : Submodule O A)).mkQ = ⊤ := by
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := hx x
    have h2 : x - y ∈ maximalIdeal O • (⊤ : Submodule O A) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    have := Submodule.add_mem_sup h2 hy
    rwa [sub_add_cancel] at this
  exact ⟨this ▸ hN.map _⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.DimOne
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

private theorem pow_le_of_primes {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (I : Ideal B)
    (h : ∀ Q : Ideal B, Q.IsPrime → I ≤ Q → Q = maximalIdeal B) : ∃ n, maximalIdeal B ^ n ≤ I := by
  have hle : maximalIdeal B ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro Q ⟨hIQ, hQ⟩
    rw [h Q hQ hIQ]
  exact Ideal.exists_pow_le_of_le_radical_of_fg hle (IsNoetherian.noetherian _)

theorem UpperTheory.V.Ws.Po.dimOne :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B], ¬ Module.Finite O B →
      ∃ (P : Ideal B) (t : B) (n : ℕ), P.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ P ∧ t ∈ maximalIdeal B ∧ t ∉ P ∧
        maximalIdeal B ^ n ≤ P ⊔ Ideal.span {t} := by
  intro O _ _ _ B _ _ _ hnf
  haveI : IsLocalHom (algebraMap O B) := IsCO.isLocalHom
  have hIm : (maximalIdeal O).map (algebraMap O B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (algebraMap O B) x hx
  have hex : ∃ Q : Ideal B, Q.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ Q ∧
      Q ≠ maximalIdeal B := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨n, hn⟩ := pow_le_of_primes _ (fun Q hQ hIQ => hcon Q hQ hIQ)
    exact hnf (UpperTheory.V.Ws.Po.finPow hIm IsCO.res_surj n hn)
  obtain ⟨P, ⟨hP, hIP, hPm⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian B B)
      {Q : Ideal B | Q.IsPrime ∧ (maximalIdeal O).map (algebraMap O B) ≤ Q ∧ Q ≠ maximalIdeal B} hex
  have hPle : P ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal hP.ne_top
  obtain ⟨t, htm, htP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPle hPm)
  obtain ⟨n, hn⟩ := pow_le_of_primes (P ⊔ Ideal.span {t}) (by
    intro Q hQ hPQ
    by_contra hQm
    have hPQ' : P ≤ Q := le_trans le_sup_left hPQ
    have htQ : t ∈ Q := hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
    exact hmax Q ⟨hQ, hIP.trans hPQ', hQm⟩
      (lt_of_le_of_ne hPQ' (fun e => htP (by rw [e]; exact htQ))))
  exact ⟨P, t, n, hP, hIP, htm, htP, hn⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.PsFinEv
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.Ws.Po.psFin :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsDomain B], (∀ a ∈ maximalIdeal O, algebraMap O B a = 0) →
      ∀ t ∈ maximalIdeal B, t ≠ 0 → ∀ n : ℕ, maximalIdeal B ^ n ≤ Ideal.span {t} →
      ∃ φ : PowerSeries (ResidueField O) →+* B, Function.Injective φ ∧ φ.Finite ∧ φ PowerSeries.X = t ∧
        ∀ a : O, φ (PowerSeries.C (residue O a)) = algebraMap O B a := by
  intro O _ _ B _ _ _ _ h0 t ht ht0 n hn
  classical
  let ι : ResidueField O →+* B := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O B) h0
  letI : UniformSpace (ResidueField O) := ⊥
  letI : WithIdeal B := ⟨maximalIdeal B⟩
  have hadic : IsAdic (maximalIdeal B) := rfl
  have hc : CompleteSpace B ∧ T2Space B := hadic.isAdicComplete_iff.mp (IsCO.complete (O := O))
  haveI := hc.1
  haveI := hc.2
  have hcont : Continuous ι := continuous_of_discreteTopology
  have hte : PowerSeries.HasEval t := by
    show Filter.Tendsto (fun m => t ^ m) Filter.atTop (nhds 0)
    rw [hadic.hasBasis_nhds_zero.tendsto_right_iff]
    intro i _
    filter_upwards [Filter.eventually_ge_atTop i] with m hm
    exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow ht m)
  let φ := PowerSeries.eval₂Hom hcont hte
  have hφX : φ PowerSeries.X = t := by simp [φ, PowerSeries.coe_eval₂Hom]
  have hφC : ∀ r, φ (PowerSeries.C r) = ι r := by
    intro r
    simp [φ, PowerSeries.coe_eval₂Hom]
  refine ⟨φ, ?_, ?_, hφX, fun a => by rw [hφC]; rfl⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have hu : IsUnit (PowerSeries.divXPowOrder f) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      exact Ne.isUnit (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hne)
    have h1 := congrArg φ (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
    rw [map_mul, map_pow, hφX, hf] at h1
    exact mul_ne_zero (pow_ne_zero _ ht0) (hu.map φ).ne_zero h1
  · letI : Algebra (PowerSeries (ResidueField O)) B := φ.toAlgebra
    haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField O))) (PowerSeries (ResidueField O)) := by
      rw [PowerSeries.maximalIdeal_eq_span_X]
      infer_instance
    have hmap : Ideal.map (algebraMap (PowerSeries (ResidueField O)) B)
        (maximalIdeal (PowerSeries (ResidueField O))) = Ideal.span {t} := by
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton,
        RingHom.algebraMap_toAlgebra, hφX]
    show Module.Finite _ _
    refine UpperTheory.V.Ws.Po.finPow ?_ ?_ n ?_
    · rw [hmap, Ideal.span_le, Set.singleton_subset_iff]
      exact ht
    · intro x
      obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
      exact ⟨PowerSeries.C (residue O a), by rw [RingHom.algebraMap_toAlgebra, hφC]; exact ha⟩
    · rw [hmap]
      exact hn
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinExt
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.Ws.Po.finExt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (V : ValuationSubring K) (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
      (φ : A →+* B) (f : A →+* V), Function.Injective φ → φ.Finite → Function.Injective f →
      ∃ (y : B →+* V) (s : Finset K), y.comp φ = f ∧ ∀ b, (y b : K) ∈ Subfield.closure (Set.range (V.subtype.comp f) ∪ s) := by
  intro K _ _ V A B _ _ _ _ φ f hφ hfin hf
  classical
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A K := (V.subtype.comp f).toAlgebra
  letI : Algebra A V := f.toAlgebra
  haveI : Module.Finite A B := hfin
  have hfK : Function.Injective (V.subtype.comp f) := Subtype.val_injective.comp hf
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hφ
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hfK
  haveI : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  let y₀ : B →ₐ[A] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hmem : ∀ b, y₀ b ∈ V := by
    intro b
    have h1 : IsIntegral A (y₀ b) := (Algebra.IsIntegral.isIntegral b).map y₀
    have h2 : IsIntegral V (y₀ b) := h1.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    rw [← hz]
    exact z.2
  let y : B →+* V := y₀.toRingHom.codRestrict V hmem
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := B)
  refine ⟨y, Finset.univ.image (fun i => y₀ (g i)), ?_, ?_⟩
  · ext a
    exact y₀.commutes a
  · intro b
    show y₀ b ∈ _
    have hb : b ∈ Submodule.span A (Set.range g) := by
      rw [hg]
      exact Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      apply Subfield.subset_closure
      right
      simp
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x z _ _ hx hz =>
      rw [map_add (f := _)]
      exact add_mem hx hz
    | smul a x _ hx =>
      rw [map_smul, Algebra.smul_def]
      refine mul_mem (Subfield.subset_closure ?_) hx
      left
      exact ⟨a, rfl⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Po.ambPt :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B], ¬ Module.Finite c.O B →
      ∃ (𝔞 : Amb l) (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (f : A →+* 𝔞.V) (s : Finset 𝔞.K)
        (y : B →+* 𝔞.V), CharP 𝔞.K l ∧ 𝔞.IsDvr f ∧ y.comp (algebraMap c.O B) = 𝔞.a c ∧ (∀ b ∈ maximalIdeal B, y b ∈ maximalIdeal 𝔞.V) ∧
        (∃ b ∈ maximalIdeal B, y b ≠ 0) ∧ (∀ a ∈ maximalIdeal c.O, 𝔞.a c a = 0) ∧
        ∀ b, (y b : 𝔞.K) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ s) := by
  intro l _ c B _ _ _ hB
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (dvrFacts l c.O).2.2.2.1
  obtain ⟨P, t, n, hP, hmP, ht, htP, hn⟩ := Po.dimOne c.O B hB
  haveI : IsDomain (B ⧸ P) := Ideal.Quotient.isDomain P
  haveI : IsCO c.O (B ⧸ P) := co_quot c.O B _ (Ideal.Quotient.mkₐ c.O P) (Ideal.Quotient.mkₐ_surjective c.O P)
  have hq : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hm : (maximalIdeal B).map (Ideal.Quotient.mk P) = maximalIdeal (B ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hq
  have h0 : ∀ a ∈ maximalIdeal c.O, algebraMap c.O (B ⧸ P) a = 0 := fun a ha =>
    (Ideal.Quotient.eq_zero_iff_mem (a := algebraMap c.O B a)).2 (hmP (Ideal.mem_map_of_mem _ ha))
  have hn' : maximalIdeal (B ⧸ P) ^ n ≤ Ideal.span {Ideal.Quotient.mk P t} := by
    rw [← hm, ← Ideal.map_pow]
    refine (Ideal.map_mono hn).trans ?_
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨φ, hφi, hφf, hφX, hφC⟩ := Po.psFin c.O (B ⧸ P) h0 (Ideal.Quotient.mk P t)
    (hm ▸ Ideal.mem_map_of_mem _ ht) (fun h => htP (Ideal.Quotient.eq_zero_iff_mem.1 h)) n hn'
  obtain ⟨hfin, hch⟩ := Po.fin_res c
  haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField c.O))) (PowerSeries (ResidueField c.O)) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  haveI : Finite (ResidueField (PowerSeries (ResidueField c.O))) :=
    Finite.of_equiv _ (PowerSeries.residueFieldOfPowerSeries (k := ResidueField c.O)).symm.toEquiv
  haveI : CharP (PowerSeries (ResidueField c.O)) l :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := ResidueField c.O)) l
  obtain ⟨𝔞, f, hK, hf, hfa⟩ := ambL c (PowerSeries (ResidueField c.O)) (PowerSeries.C.comp (residue c.O))
  obtain ⟨y, s, hy, hs⟩ := Po.finExt 𝔞.K 𝔞.V _ _ φ f hφi hφf hf.inj
  have hyφ : ∀ x, y (φ x) = f x := fun x => RingHom.congr_fun hy x
  have hya : ∀ a, y (algebraMap c.O (B ⧸ P) a) = 𝔞.a c a := fun a => by
    rw [← hφC, hyφ, ← hfa]
    rfl
  have hX : f PowerSeries.X ∈ maximalIdeal 𝔞.V := by
    haveI := hf.loc
    refine map_nonunit f _ ?_
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  refine ⟨𝔞, _, inferInstance, inferInstance, inferInstance, f, s, y.comp (Ideal.Quotient.mk P), hK, hf,
    RingHom.ext hya, fun b hb => ?_, ⟨t, ht, ?_⟩, fun a ha => ?_, fun b => hs _⟩
  · have hb' : Ideal.Quotient.mk P b ∈ maximalIdeal (B ⧸ P) := hm ▸ Ideal.mem_map_of_mem _ hb
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (hn' (Ideal.pow_mem_pow hb' n))
    refine (maximalIdeal.isMaximal 𝔞.V).isPrime.mem_of_pow_mem n ?_
    rw [RingHom.comp_apply, ← map_pow, ← hu, map_mul, ← hφX, hyφ]
    exact Ideal.mul_mem_left _ _ hX
  · rw [RingHom.comp_apply, ← hφX, hyφ]
    exact fun h => PowerSeries.X_ne_zero (hf.inj (h.trans (map_zero f).symm))
  · rw [← hya, h0 a ha, map_zero]
