module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLoc

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfB
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.SatGramLoc

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev rcIntAlg (v : HeightOneSpectrum (𝓞 F)) :
    Algebra (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) :=
  ((algebraMap (v.adicCompletion F) (E ⊗[F] v.adicCompletion F)).comp
    (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra

theorem rc_isIntegral (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F)
    (hx : x ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
      (v.adicCompletionIntegers F).toSubring) :
    @IsIntegral (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) _ _
      (rcIntAlg (E := E) v) x := by
  letI := rcIntAlg (E := E) v
  unfold Formalism.UG.tensInt Formalism.UG.intOE at hx
  refine (Subring.closure_le (t := (integralClosure (v.adicCompletionIntegers F)
    (E ⊗[F] v.adicCompletion F)).toSubring).2 ?_) hx
  rintro _ (⟨a, rfl⟩ | ⟨y, rfl⟩)
  · have ha : IsIntegral ℤ (a : E) := by
      obtain ⟨b, hb⟩ := a.2
      rw [← hb]
      first
      | exact b.isIntegral_coe
      | exact b.2
      | exact NumberField.RingOfIntegers.isIntegral_coe b
    exact IsIntegral.map_of_comp_eq (Int.castRingHom (v.adicCompletionIntegers F))
      (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F))
      (RingHom.ext_int _ _) ha
  · show IsIntegral _ (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) y)
    exact isIntegral_algebraMap

theorem rc_idem_zero (v : HeightOneSpectrum (𝓞 F)) (f t : E ⊗[F] v.adicCompletion F)
    (c : v.adicCompletion F) (hc : Valued.v c < 1) (hf : f * f = f)
    (hft : f = ((1 : E) ⊗ₜ[F] c) * t)
    (ht : letI := rcIntAlg (E := E) v; IsIntegral (v.adicCompletionIntegers F) t) : f = 0 := by
  letI := rcIntAlg (E := E) v
  obtain ⟨p, hpm, hp⟩ := ht
  have hc1 : Valued.v c ≤ 1 := le_of_lt hc
  obtain ⟨c', hc'⟩ : ∃ c' : v.adicCompletionIntegers F, (c' : v.adicCompletion F) = c :=
    ⟨⟨c, by
      first
      | exact hc1
      | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hc1
      | simpa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] using hc1⟩, rfl⟩
  subst hc'
  have hC : algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) c' =
      (1 : E) ⊗ₜ[F] (c' : v.adicCompletion F) := rfl

  have hq0 : (p.scaleRoots c').eval₂ (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)) f = 0 := by
    rw [hft, ← hC, Polynomial.scaleRoots_eval₂_mul, hp, mul_zero]
  have hidem : ∀ i : ℕ, f * f ^ i = f := fun i => by
    rw [← pow_succ']; exact IsIdempotentElem.pow_succ_eq i hf

  have key : f * algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) ((p.scaleRoots c').eval 1) = 0 := by
    have h := congrArg (f * ·) hq0
    simp only [mul_zero] at h
    rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.eval_eq_sum_range, map_sum, Finset.mul_sum, ← h]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_pow, mul_one, mul_left_comm, hidem, mul_comm]
  have hsplit : (p.scaleRoots c').eval 1 =
      (∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i)) + 1 := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.natDegree_scaleRoots, Finset.sum_range_succ]
    simp [Polynomial.coeff_scaleRoots, hpm.coeff_natDegree]

  have hlt : Valued.v ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) :
      v.adicCompletionIntegers F) : v.adicCompletion F) < 1 := by
    push_cast
    refine Valuation.map_sum_lt _ one_ne_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have h1 : Valued.v ((p.coeff i : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 := by
      first
      | exact (p.coeff i).2
      | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (p.coeff i).2
    have hm : p.natDegree - i = (p.natDegree - i - 1) + 1 := by omega
    rw [Valuation.map_mul, Valuation.map_pow, hm, pow_succ]
    calc Valued.v ((p.coeff i : v.adicCompletionIntegers F) : v.adicCompletion F) *
          (Valued.v (c' : v.adicCompletion F) ^ (p.natDegree - i - 1) * Valued.v (c' : v.adicCompletion F))
        ≤ 1 * (1 * Valued.v (c' : v.adicCompletion F)) :=
          mul_le_mul' h1 (mul_le_mul' (pow_le_one' hc1 _) le_rfl)
      _ < 1 := by rw [one_mul, one_mul]; exact hc
  have hU : (((p.scaleRoots c').eval 1 : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    rw [hsplit]
    intro h0
    have h0' : ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) :
        v.adicCompletionIntegers F) : v.adicCompletion F) = -1 := by
      have : ((∑ i ∈ Finset.range p.natDegree, p.coeff i * c' ^ (p.natDegree - i) :
          v.adicCompletionIntegers F) : v.adicCompletion F) + 1 = 0 := by
        rw [← h0]; push_cast; ring
      exact eq_neg_of_add_eq_zero_left this
    have hv := hlt
    rw [h0', Valuation.map_neg, Valuation.map_one] at hv
    exact lt_irrefl _ hv
  have hunit : IsUnit (algebraMap (v.adicCompletion F) (E ⊗[F] v.adicCompletion F)
      (((p.scaleRoots c').eval 1 : v.adicCompletionIntegers F) : v.adicCompletion F)) :=
    (Ne.isUnit hU).map _
  exact hunit.mul_left_eq_zero.mp key

theorem rc_finrank (v : HeightOneSpectrum (𝓞 F)) :
    Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) = Module.finrank F E := by
  let e : (v.adicCompletion F ⊗[F] E) ≃ₗ[v.adicCompletion F] (E ⊗[F] v.adicCompletion F) :=
    { TensorProduct.comm F (v.adicCompletion F) E with
      map_smul' := fun a x => by
        show TensorProduct.comm F _ _ (a • x) = a • TensorProduct.comm F _ _ x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b y =>
          rw [TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul]
          first
          | (show y ⊗ₜ[F] (a • b) = (1 ⊗ₜ[F] a) * (y ⊗ₜ[F] b)
             rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul])
          | (rw [Algebra.smul_def]
             show y ⊗ₜ[F] (a • b) = (1 ⊗ₜ[F] a) * (y ⊗ₜ[F] b)
             rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul])
          | (simp [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]; done)
        | add x y hx hy =>
          rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add] }
  rw [← e.finrank_eq, Module.finrank_baseChange]

end

theorem reduction_structure_holds : RedCore := by
  intro F E _ _ _ _ _ σ hσ h2 v e he hee hes hct
  obtain ⟨c, hc, t, ht, hft⟩ := hct
  set e' := Formalism.UG.sigR σ (v.adicCompletion F) e with he'
  have he'e' : e' * e' = e' := by rw [he', ← map_mul, hee]
  have hee' : e * e' = 0 := hes
  have he'e : e' * e = 0 := by rw [mul_comm]; exact hee'

  have hidem : (1 - e - e') * (1 - e - e') = 1 - e - e' := by
    linear_combination hee + he'e' + 2 * hee'
  have hf0 : 1 - e - e' = 0 := rc_idem_zero v (1 - e - e') t c hc hidem hft (rc_isIntegral v t ht)
  have hsum : e + e' = 1 := by linear_combination -hf0
  have hfr : Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) = 2 := by
    rw [rc_finrank, h2]
  haveI : Nontrivial (E ⊗[F] v.adicCompletion F) := by
    have hpos : 0 < Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := by
      rw [hfr]; norm_num
    exact Module.nontrivial_of_finrank_pos hpos
  have he0 : e ≠ 0 := by
    intro h0
    have h3 : e' = 0 := by rw [he', h0, map_zero]
    have h1 : (1 : E ⊗[F] v.adicCompletion F) = 0 := by rw [← hsum, h0, h3, add_zero]
    exact one_ne_zero h1

  have hli : LinearIndependent (v.adicCompletion F) ![e, e'] := by
    rw [LinearIndependent.pair_iff]
    intro s s' hst
    have h1 : s • e = 0 := by
      have h := congrArg (e * ·) hst
      simpa only [mul_add, mul_smul_comm, hee, hee', smul_zero, add_zero, mul_zero] using h
    have h3 : s' • e' = 0 := by
      have h := congrArg (e' * ·) hst
      simpa only [mul_add, mul_smul_comm, he'e, he'e', smul_zero, zero_add, mul_zero] using h
    have he'0 : e' ≠ 0 := by
      intro h0
      have h4 : e = 1 := by rw [← hsum, h0, add_zero]
      have h5 : e' = 1 := by rw [he', h4, map_one]
      rw [h0] at h5
      exact zero_ne_one h5
    exact ⟨(smul_eq_zero.mp h1).resolve_right he0, (smul_eq_zero.mp h3).resolve_right he'0⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank (v.adicCompletion F) (E ⊗[F] v.adicCompletion F) := by
    rw [hfr]; rfl
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = e := by simp [b]
  have hb1 : b 1 = e' := by simp [b]
  let r0 : E ⊗[F] v.adicCompletion F → v.adicCompletion F := fun x => b.repr x 0
  have hr : ∀ x, e * x = r0 x • e := by
    intro x
    have hx := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at hx
    conv_lhs => rw [← hx]
    rw [mul_add, mul_smul_comm, mul_smul_comm, hee, hee', smul_zero, add_zero]
  have huniq : ∀ α β : v.adicCompletion F, α • e = β • e → α = β :=
    fun α β h => smul_left_injective (v.adicCompletion F) he0 h
  have halg : ∀ a : v.adicCompletion F, ((1 : E) ⊗ₜ[F] a) * e = a • e := by
    intro a; rw [Algebra.smul_def]; rfl
  have hr1 : r0 1 = 1 := huniq _ _ (by rw [← hr, mul_one, one_smul])
  have hr0 : r0 0 = 0 := huniq _ _ (by rw [← hr, mul_zero, zero_smul])
  have hra : ∀ x y, r0 (x + y) = r0 x + r0 y := fun x y =>
    huniq _ _ (by rw [← hr, mul_add, hr, hr, add_smul])
  have hrm : ∀ x y, r0 (x * y) = r0 x * r0 y := fun x y =>
    huniq _ _ (calc r0 (x * y) • e = e * (x * y) := (hr _).symm
      _ = (e * x) * y := (mul_assoc _ _ _).symm
      _ = (r0 x • e) * y := by rw [hr]
      _ = r0 x • (e * y) := smul_mul_assoc _ _ _
      _ = r0 x • (r0 y • e) := by rw [hr]
      _ = (r0 x * r0 y) • e := (mul_smul _ _ _).symm)
  have hr2 : ∀ a : v.adicCompletion F, r0 ((1 : E) ⊗ₜ[F] a) = a := fun a =>
    huniq _ _ (by rw [← hr, mul_comm, halg])
  let r : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F :=
    { toFun := r0, map_one' := hr1, map_mul' := hrm, map_zero' := hr0, map_add' := hra }
  refine ⟨r, ?_, hr2, ?_, ?_⟩
  · show r0 e = 1
    exact huniq _ _ (by rw [← hr, hee, one_smul])
  · intro x hx
    have hint := rc_isIntegral v x hx
    letI := rcIntAlg (E := E) v
    have hint' : IsIntegral (v.adicCompletionIntegers F) (r x) := by
      refine IsIntegral.map_of_comp_eq (RingHom.id _) r ?_ hint
      refine RingHom.ext fun y => ?_
      show ((y : v.adicCompletionIntegers F) : v.adicCompletion F) =
        r0 ((1 : E) ⊗ₜ[F] ((y : v.adicCompletionIntegers F) : v.adicCompletion F))
      exact (hr2 _).symm
    first
    | (obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'; rw [← hy]; exact y.2)
    | exact ValuationSubring.mem_of_isIntegral _ hint'
    | exact (Valuation.integer.integers _).mem_of_integral hint'
  · intro x hx
    show x = ((1 : E) ⊗ₜ[F] r0 x) * e
    rw [halg, ← hr, hx]

end Formalism.L2.SG.Pf.SatGramLoc
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfA
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.SatGramLoc

section Deg

variable {K : Type} [Field K] [NumberField K]

theorem liesOver_natCast (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hne : Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal ≠ ⊤ := Ideal.comap_ne_top _ v.isPrime.ne_top
  have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hv
  constructor
  exact hmax.eq_of_le hne hle

theorem image_places_primesOver (p : ℕ) (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_natCast p hp v hv⟩
  · rintro ⟨hP, hPo⟩
    have h' : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
    rw [hPo.over] at h'
    have h'' : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := h'
    have hmem : ((p : ℕ) : 𝓞 K) ∈ P := by simpa using h''
    have hne : P ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hmem
      exact hp.ne_zero (by exact_mod_cast hmem)
    exact ⟨⟨P, hP, hne⟩, hmem, rfl⟩

theorem ram_inertia_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [RingOfIntegers.rank, ← hs, ← Set.ncard_image_of_injective _
    (fun v w h => HeightOneSpectrum.ext h), image_places_primesOver p hp,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones] at hsum
  have hle : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rintro ⟨q, hq, hql⟩
    exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) q) (Ideal.inertiaDeg_pos q ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le (fun q _ => hle q)).1 hsum.symm
    ⟨v.asIdeal, v.isPrime, liesOver_natCast p hp v hv⟩ (Finset.mem_univ _)
  exact ⟨Nat.dvd_one.1 ⟨_, hall⟩, Nat.dvd_one.1 ⟨_, hall.trans (mul_comm _ _)⟩⟩

theorem card_quot_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  haveI := liesOver_natCast p hp v hv
  have h := Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp
  have hf := (ram_inertia_split p hp hs v hv).2
  have h2 : (Ideal.span {((p : ℕ) : ℤ)}).inertiaDeg' v.asIdeal = 1 := by
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    rw [Ideal.inertiaDeg'_eq_inertiaDeg, hf]
  rw [h2, pow_one] at h
  rw [← h, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem intValuation_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.intValuation ((p : ℕ) : 𝓞 K) = WithZero.exp (-1 : ℤ) := by
  have := v.isPrime
  have hr : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hmap : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hne : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hr
  have := liesOver_natCast p hp v hv
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {((p : ℕ) : ℤ)})
    v.asIdeal hne
  rw [hmap, (ram_inertia_split p hp hs v hv).1] at he
  rw [v.intValuation_eq_exp_neg_multiplicity hr, ← he]
  rfl

end Deg

theorem ram_inertia_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hvp := v.isPrime
  have hvl : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_natCast p hp v hv
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (v.asIdeal.primesOver (𝓞 E)) := inferInstance
  have hPZ : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
      rw [hPZ.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))
    exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
  have hPmem : ((p : ℕ) : 𝓞 E) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [← hPZ.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  obtain ⟨he, hf⟩ := ram_inertia_split (K := E) p hp hs ⟨P, hPp, hP0⟩ hPmem
  change P.ramificationIdx ℤ = 1 at he
  change P.inertiaDeg ℤ = 1 at hf
  rw [Ideal.ramificationIdx_tower (R := ℤ) v.asIdeal P] at he
  rw [Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P] at hf
  exact ⟨Nat.eq_one_of_mul_eq_one_right he, Nat.eq_one_of_mul_eq_one_right hf⟩

theorem split_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E) :
    {v : HeightOneSpectrum (𝓞 F) | ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 F)
  have hone : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 F),
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    rintro ⟨q, hq, hql⟩
    have hq0 : q ≠ ⊥ := by
      rintro rfl
      have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
        rw [hql.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 F))
      exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
    have hqmem : ((p : ℕ) : 𝓞 F) ∈ q := by
      have : (p : ℤ) ∈ q.under ℤ := by rw [← hql.over]; exact Ideal.mem_span_singleton_self _
      simpa using this
    obtain ⟨h1, h2⟩ := ram_inertia_sub (E := E) p hp hs ⟨q, hq, hq0⟩ hqmem
    change q.ramificationIdx ℤ * q.inertiaDeg ℤ = 1
    rw [h1, h2]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  rw [RingOfIntegers.rank] at hsum
  rw [← hsum, ← Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h),
    image_places_primesOver p hp, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

theorem split_prime_local_holds : SplitPrimeLoc := by
  intro F E _ _ _ _ _ p hp hs
  have hF := split_sub (F := F) (E := E) p hp hs
  refine ⟨fun v hv => ⟨card_quot_split p hp hF v hv, ?_⟩, hF⟩
  have h1 := intValuation_split p hp hF v hv
  first
  | exact h1
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; exact (map_natCast (algebraMap F (v.adicCompletion F)) p).symm)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; simp; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; congr 1; norm_cast; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; simp; done)
  | (rw [← h1, ← HeightOneSpectrum.valuation_of_algebraMap (K := F),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; rfl)

end Formalism.L2.SG.Pf.SatGramLoc

end
end
