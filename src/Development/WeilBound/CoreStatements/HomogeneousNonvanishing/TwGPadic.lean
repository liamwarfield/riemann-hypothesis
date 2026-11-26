module

public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGFree
public import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RealOfFixedByConjugations
open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.UnimodularBaseChange

theorem bijective_baseChange :
    ∀ (Z : Type) [CommRing Z] (L : Type) [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
      (B : LinearMap.BilinForm ℤ L), Function.Bijective B →
      Function.Bijective (B.baseChange Z) := by
  intro Z _ L _ _ _ B hB
  classical
  let b := Module.Free.chooseBasis ℤ L
  let c := b.baseChange Z
  have h1 : IsUnit (LinearMap.toMatrix b b.dualBasis B).det :=
    LinearEquiv.isUnit_det (LinearEquiv.ofBijective B hB) b b.dualBasis
  have h2 : LinearMap.toMatrix c c.dualBasis (B.baseChange Z) =
      (algebraMap ℤ Z).mapMatrix (LinearMap.toMatrix b b.dualBasis B) := by
    ext i j
    simp [c, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply]
  have h3 : IsUnit (LinearMap.toMatrix c c.dualBasis (B.baseChange Z)).det := by
    rw [h2, ← RingHom.map_det]
    exact h1.map _
  exact (LinearEquiv.ofIsUnitDet h3).bijective

end GlobalTheory.CompanionTheory.UnimodularBaseChange
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGLam
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGXi
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem xi_den (E : Type) [Field E] [NumberField E] : ∃ c : 𝓞 E, c ≠ 0 ∧ ∀ η : E,
    (∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (η * a) = z) → ∃ b : 𝓞 E, (b : E) = c * η := by
  obtain ⟨c, hc, h⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)).prop
  refine ⟨c, nonZeroDivisors.ne_zero hc, fun η hη => ?_⟩
  have hm : η ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨z, hz⟩ := hη b
    exact ⟨z, hz.symm⟩
  obtain ⟨b, hb⟩ := h η hm
  exact ⟨b, by rw [Algebra.smul_def] at hb; exact hb⟩

theorem xi_rep (E : Type) [Field E] [NumberField E] (lam : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ η : E, ∀ a : 𝓞 E, Algebra.trace ℚ E (η * a) = lam a := by
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ fun i => (lam (RingOfIntegers.basis E i) : ℚ)
  refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm f, fun a => ?_⟩
  rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  have h : (f.restrictScalars ℤ).comp (IsScalarTower.toAlgHom ℤ (𝓞 E) E).toLinearMap
      = (Algebra.linearMap ℤ ℚ).comp lam := by
    refine (RingOfIntegers.basis E).ext fun i => ?_
    show f (algebraMap (𝓞 E) E (RingOfIntegers.basis E i)) = _
    rw [← integralBasis_apply]
    exact (integralBasis E).constr_basis ℚ _ i
  exact LinearMap.congr_fun h a

theorem tw_g_xi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : ℕ, p.Prime → ∃ ξ : E, IsCMField.complexConj E ξ = -ξ ∧ (∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (ξ * a) = z) ∧ ∀ lam : 𝓞 E →ₗ[ℤ] ℤ, ∃ (m : ℤ) (b : 𝓞 E), ¬ (p : ℤ) ∣ m ∧ ∀ a : 𝓞 E, ((m * lam a : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * b * a) := by
  intro E _ _ _ bar hbar hun p hp
  obtain ⟨c0, hc0, hden⟩ := xi_den E
  have hbb := bar_bar bar hbar
  have htr : ∀ x : E, Algebra.trace ℚ E (IsCMField.complexConj E x) = Algebra.trace ℚ E x := fun x =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
  set c : 𝓞 E := c0 * bar c0 with hc
  have hc' : c ≠ 0 := mul_ne_zero hc0 (by simpa using hc0)
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc'
  have hcb : IsCMField.complexConj E (c : E) = c := by
    rw [← hbar, hc, map_mul, hbb, mul_comm]
  let I : Ideal (𝓞 E) :=
    { carrier := {y | ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E ((y : E) / c * a) = z}
      add_mem' := fun {x y} hx hy a => by
        obtain ⟨z, hz⟩ := hx a
        obtain ⟨w, hw⟩ := hy a
        exact ⟨z + w, by push_cast; rw [add_div, add_mul, map_add (f := _), hz, hw]⟩
      zero_mem' := fun a => ⟨0, by simp⟩
      smul_mem' := fun r y hy a => by
        obtain ⟨z, hz⟩ := hy (r * a)
        refine ⟨z, ?_⟩
        rw [← hz]
        congr 1
        rw [smul_eq_mul]
        push_cast
        ring }
  have hmem : ∀ y : 𝓞 E, y ∈ I ↔ ∀ a : 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E ((y : E) / c * a) = z :=
    fun _ => Iff.rfl
  have hI0 : I ≠ ⊥ := by
    intro h
    have : c ∈ I := (hmem c).2 fun a => ⟨Algebra.trace ℤ (𝓞 E) a, by
      rw [div_self hcE, one_mul, Algebra.coe_trace_int]⟩
    rw [h] at this
    exact hc' this
  have hI : ∀ y ∈ I, bar y ∈ I := by
    intro y hy
    refine (hmem _).2 fun a => ?_
    obtain ⟨z, hz⟩ := (hmem y).1 hy (bar a)
    refine ⟨z, ?_⟩
    rw [← hz, ← htr ((y : E) / c * _), map_mul (IsCMField.complexConj E), map_div₀, hcb, ← hbar, ← hbar, hbb]
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨x, hxI, hx⟩ := anti_ded bar hbb I hI0 hI (tw_g_diff E bar hbar hun) (p : 𝓞 E) hp0
  have hxI' : x - bar x ∈ I := sub_mem hxI (hI x hxI)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {x - bar x} := Ideal.dvd_span_singleton.2 hxI'
  have hm : ∃ m : ℤ, ¬ (p : ℤ) ∣ m ∧ (m : 𝓞 E) ∈ J := by
    by_contra hne
    push Not at hne
    have : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
    obtain ⟨Q, hJQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E)
      (Ideal.span {(p : ℤ)}) J (by
        intro m hm
        rw [Ideal.mem_span_singleton]
        by_contra h
        exact hne m h (by simpa using hm))
    have hpQ : (p : 𝓞 E) ∈ Q := by
      have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
        change (p : ℤ) ∈ Ideal.under ℤ Q
        rw [hQp]
        exact Ideal.mem_span_singleton_self _
      simpa using this
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact hp0 hpQ
    refine hx Q (hQ.isMaximal hQ0) hpQ ?_
    have : x - bar x ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self _
    rw [mul_comm Q]
    exact Ideal.mul_mono_right hJQ this
  obtain ⟨m, hmp, hmJ⟩ := hm
  refine ⟨((x - bar x : 𝓞 E) : E) / c, ?_, (hmem _).1 hxI', fun lam => ?_⟩
  · rw [map_div₀, hcb, ← hbar, map_sub, hbb]
    push_cast
    ring
  · obtain ⟨η, hη⟩ := xi_rep E lam
    obtain ⟨b, hb⟩ := hden η fun a => ⟨lam a, hη a⟩
    have hy : ((bar c0 * b : 𝓞 E) : E) / c = η := by
      rw [div_eq_iff hcE, hc]
      have e1 : ((bar c0 * b : 𝓞 E) : E) = (bar c0 : 𝓞 E) * (b : E) := rfl
      have e2 : ((c0 * bar c0 : 𝓞 E) : E) = (c0 : E) * (bar c0 : 𝓞 E) := rfl
      rw [e1, e2, hb]
      ring
    have hyI : bar c0 * b ∈ I := (hmem _).2 fun a => ⟨lam a, by rw [hy, hη]⟩
    have h2 : bar c0 * b * m ∈ Ideal.span {x - bar x} := hJ ▸ Ideal.mul_mem_mul hyI hmJ
    obtain ⟨β, hβ⟩ := Ideal.mem_span_singleton.1 h2
    refine ⟨m, β, hmp, fun a => ?_⟩
    have h3 : ((x - bar x : 𝓞 E) : E) / c * β * a = (m : ℚ) • (η * a) := by
      have h4 : ((bar c0 * b : 𝓞 E) : E) * m = ((x - bar x : 𝓞 E) : E) * β := by
        have := congrArg (algebraMap (𝓞 E) E) hβ
        rw [map_mul _ (bar c0 * b), map_intCast, map_mul _ _ β] at this
        exact this
      rw [← hy, Int.cast_smul_eq_zsmul, zsmul_eq_mul, div_mul_eq_mul_div, ← h4]
      ring
    rw [h3, map_smul, hη]
    simp

end PositivityTheory.UnitarySelfGeneration
end

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem trace_form_mulLeft_bijective (B Z : Type) [CommRing B] [Module.Finite ℤ B] [Module.Free ℤ B] [CommRing Z]
    (l : B →ₗ[ℤ] ℤ) (h : ∀ f : B →ₗ[ℤ] ℤ, ∃ (m : ℤ) (b : B), IsUnit (m : Z) ∧ ∀ a, m * f a = l (b * a))
    (L : Z ⊗[ℤ] B →ₗ[Z] Z) (hL : ∀ z a, L (z ⊗ₜ a) = z * l a) :
    Function.Bijective (fun r : Z ⊗[ℤ] B => L.comp (LinearMap.mulLeft Z r)) := by
  classical
  let T : Z ⊗[ℤ] B →ₗ[Z] Module.Dual Z (Z ⊗[ℤ] B) := (LinearMap.mul Z (Z ⊗[ℤ] B)).compr₂ L
  show Function.Bijective T
  let b := Module.Free.chooseBasis ℤ B
  let bZ := Algebra.TensorProduct.basis Z b
  have hs : Function.Surjective T := by
    intro f
    choose m β hu hm using fun i => h (b.coord i)
    refine ⟨∑ i, (f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i, bZ.ext fun j => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    have h1 : ∀ i, T ((f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i) (bZ j) = if j = i then f (bZ i) else 0 := by
      intro i
      have h2 : bZ j = 1 ⊗ₜ b j := Algebra.TensorProduct.basis_apply _ _
      show L (_ * bZ j) = _
      rw [h2, Algebra.TensorProduct.tmul_mul_tmul, hL, ← hm, mul_one, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · rw [mul_one, mul_assoc, IsUnit.val_inv_mul, mul_one]
      · simp
    simp [h1]
  refine ⟨?_, hs⟩
  have := OrzechProperty.injective_of_surjective_endomorphism (bZ.toDualEquiv.symm.toLinearMap.comp T)
    (bZ.toDualEquiv.symm.surjective.comp hs)
  exact Function.Injective.of_comp this

theorem tw_g_lam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime], ∃ lam : (ℤ_[p] ⊗[ℤ] 𝓞 E) →ₗ[ℤ_[p]] ℤ_[p], (∀ r, lam (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom r) = -lam r) ∧ Function.Bijective (fun r : ℤ_[p] ⊗[ℤ] 𝓞 E => lam.comp (LinearMap.mulLeft ℤ_[p] r)) := by
  intro E _ _ _ bar hbar hun p hp
  obtain ⟨ξ, h1, h2, h3⟩ := tw_g_xi E bar hbar hun p hp.out
  choose l0 hl0 using h2
  let l : 𝓞 E →ₗ[ℤ] ℤ := (AddMonoidHom.mk' l0 fun a b => by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← hl0, ← hl0, ← hl0, ← map_add (f := _), ← mul_add]
    rfl).toIntLinearMap
  have hl : ∀ a, (l a : ℚ) = Algebra.trace ℚ E (ξ * a) := fun a => (hl0 a).symm
  let L : ℤ_[p] ⊗[ℤ] 𝓞 E →ₗ[ℤ_[p]] ℤ_[p] :=
    (TensorProduct.AlgebraTensorModule.rid ℤ ℤ_[p] ℤ_[p]).toLinearMap.comp (l.baseChange ℤ_[p])
  have hL : ∀ z a, L (z ⊗ₜ a) = z * l a := by
    intro z a
    simp [L, mul_comm]
  have htr : ∀ x : E, Algebra.trace ℚ E (IsCMField.complexConj E x) = Algebra.trace ℚ E x := fun x =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
  have hlb : ∀ a, l (bar a) = -l a := by
    intro a
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hl, hl, ← htr, map_mul, h1, hbar, IsCMField.complexConj_apply_apply, neg_mul, map_neg]
  refine ⟨L, fun r => ?_, trace_form_mulLeft_bijective _ _ l (fun f => ?_) L hL⟩
  · induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [Algebra.TensorProduct.map_tmul, hL, hL]
      show z * (l (bar a) : ℤ_[p]) = _
      rw [hlb]
      push_cast
      ring
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, neg_add]
  · obtain ⟨m, b, hm, hb⟩ := h3 f
    refine ⟨m, b, ?_, fun a => ?_⟩
    · rw [PadicInt.isUnit_iff]
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hm ((PadicInt.norm_int_lt_one_iff_dvd m).1 h))
    · apply Int.cast_injective (α := ℚ)
      rw [hb, hl, mul_assoc]
      rfl

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGSemi
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

open IsLocalRing Polynomial

theorem semi_complete {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    IsAdicComplete (maximalIdeal A) M := by
  refine
    { toIsHausdorff := inferInstance
      toIsPrecomplete := AdicCompletion.of_surjective_iff.mp ?_ }
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite (maximalIdeal A) M y
  induction t using TensorProduct.inductionOn with
  | tmul r x =>
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective (maximalIdeal A) A r
    refine ⟨r • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion (maximalIdeal A) A) r _).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem semi_unit_or_nil {Q : Type} [CommRing Q] [Finite Q] (h : ∀ e : Q, e * e = e → e = 0 ∨ e = 1) (x : Q) :
    IsUnit x ∨ IsNilpotent x := by
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : Q)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at hy
  have h1 : ∀ k : ℕ, x ^ (n + 1) * (x * y) ^ k = x ^ (n + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => linear_combination (x * y) * ih + x * hy
  have h2 : (x * y) ^ (n + 1) * (x * y) ^ (n + 1) = (x * y) ^ (n + 1) := by
    have := h1 (n + 1)
    rw [mul_pow] at this ⊢
    linear_combination y ^ (n + 1) * this
  rcases h _ h2 with h0 | h0
  · right
    exact ⟨n + 1, by rw [← h1 (n + 1), h0, mul_zero]⟩
  · left
    exact IsUnit.of_mul_eq_one (y * (x * y) ^ n) (by rw [← h0]; ring)

theorem semi_hensel {S : Type} [CommRing S] [Nontrivial S] (I : Ideal S) [hI : HenselianRing S I] [Finite (S ⧸ I)]
    (h : ∀ e : S, e * e = e → e = 0 ∨ e = 1) :
    ∃ _ : HenselianLocalRing S, Finite (ResidueField S) := by
  have hloc : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson hI.jac
  have hQ : ∀ e : S ⧸ I, e * e = e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e
    have hm : (X ^ 2 - X : S[X]).Monic := by monicity!
    obtain ⟨a, ha, hae⟩ := hI.is_henselian (X ^ 2 - X) hm e
      (by rw [← Ideal.Quotient.eq_zero_iff_mem]; simp [pow_two, he])
      (by
        refine IsUnit.of_mul_eq_one (2 * Ideal.Quotient.mk I e - 1) ?_
        have : (derivative (X ^ 2 - X : S[X])).eval e = 2 * e - 1 := by
          simp; norm_num
        rw [this, map_sub, map_mul, map_ofNat, map_one]
        linear_combination 4 * he)
    have ha' : a * a = a := by
      have : a ^ 2 - a = 0 := by simpa using ha
      linear_combination this
    have hae' : Ideal.Quotient.mk I a = Ideal.Quotient.mk I e := Ideal.Quotient.eq.2 hae
    rcases h a ha' with h0 | h0
    · left; rw [← hae', h0, map_zero]
    · right; rw [← hae', h0, map_one]
  have hun : ∀ x : S, IsUnit x ∨ IsNilpotent (Ideal.Quotient.mk I x) := fun x =>
    (semi_unit_or_nil hQ _).imp_left (IsUnit.of_map _ x)
  have hL : IsLocalRing S := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (hun a).imp_right fun hn => IsUnit.of_map (Ideal.Quotient.mk I) _ (by
      rw [map_sub, map_one]; exact hn.isUnit_one_sub)
  have hle : I ≤ maximalIdeal S := by
    rw [← IsLocalRing.ringJacobson_eq_maximalIdeal S]; exact hI.jac
  have hnt : Nontrivial (S ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.2 fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hle))
  have hnil : ∀ x : S, IsNilpotent (Ideal.Quotient.mk I x) → x ∈ maximalIdeal S := fun x hx hu =>
    hx.not_isUnit (hu.map _)
  refine ⟨{ hL with is_henselian := ?_ }, Finite.of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)⟩
  intro f hf a₀ h1 h2
  have hev : ∀ (g : S[X]) (a : S), aeval (Ideal.Quotient.mk I a) g = Ideal.Quotient.mk I (g.eval a) := fun g a =>
    aeval_algebraMap_apply_eq_algebraMap_eval a g
  obtain ⟨r, ⟨hr1, hr2⟩, -⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
    (P := f) (x := Ideal.Quotient.mk I a₀) (by rw [hev]; exact (hun _).resolve_left h1) (by rw [hev]; exact h2.map _)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hr : a₀ - r ∈ maximalIdeal S := hnil _ (by rw [map_sub]; exact hr1)
  have hu : IsUnit (f.derivative.eval r) := by
    by_contra hn
    have hn' : f.derivative.eval r ∈ maximalIdeal S := hn
    have h3 : f.derivative.eval a₀ - f.derivative.eval r ∈ maximalIdeal S :=
      Ideal.mem_of_dvd _ (Polynomial.sub_dvd_eval_sub _ _ _) hr
    have h4 : f.derivative.eval a₀ ∈ maximalIdeal S := by simpa using add_mem h3 hn'
    exact h4 h2
  obtain ⟨a, ha, har⟩ := hI.is_henselian f hf r (by rw [← Ideal.Quotient.eq_zero_iff_mem, ← hev, hr2]) (hu.map _)
  refine ⟨a, ha, ?_⟩
  simpa using sub_mem (hle har) hr

theorem semi_hensel_padic (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [Nontrivial S] [Algebra ℤ_[p] S]
    [Module.Finite ℤ_[p] S] (h : ∀ e : S, e * e = e → e = 0 ∨ e = 1) :
    ∃ _ : HenselianLocalRing S, Finite (ResidueField S) := by
  have h1 := semi_complete (A := ℤ_[p]) S
  have h2 : IsAdicComplete ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) S :=
    (IsAdicComplete.map_algebraMap_iff _ _).2 h1
  have h3 : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  have h4 : Module.Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (S ⧸ (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[p] _ _
  have h5 : Finite (S ⧸ (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) :=
    Module.finite_of_finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p])
  exact semi_hensel ((maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) h

theorem semi_local (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Nontrivial R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] (σ : R →ₐ[ℤ_[p]] R) (hσ : ∀ r, σ (σ r) = r) (hθ : ∃ θ : R, IsUnit (θ - σ θ))
    (h : ∀ e : R, e * e = e → σ e = e → e = 0 ∨ e = 1) (n : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (hA : (A.map σ).transpose = A) (hd : IsUnit A.det) :
    ∃ g : Matrix (Fin n) (Fin n) R, (g.map σ).transpose * A * g = 1 := by
  let S : Subalgebra ℤ_[p] R := AlgHom.equalizer σ (AlgHom.id _ _)
  have hfin : Module.Finite ℤ_[p] S := Module.Finite.of_injective S.val.toLinearMap Subtype.val_injective
  obtain ⟨hH, hF⟩ := semi_hensel_padic p S fun e he =>
    (h e.1 (congrArg Subtype.val he) e.2).imp Subtype.ext Subtype.ext
  let τ : R ≃+* R := RingEquiv.ofBijective σ.toRingHom (Function.Involutive.bijective hσ)
  obtain ⟨g, -, hg⟩ := @Formalism.HermitianLatticesTheory.unimodUnramUnique R _ τ hσ S.toSubring (fun _ => Iff.rfl) hH hF hθ n A hA hd
  exact ⟨g, hg⟩

theorem semi_congr {Z R : Type} [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R) (J : Ideal R)
    (hJ : ∀ x ∈ J, σ x ∈ J) {n : ℕ} (A g g' : Matrix (Fin n) (Fin n) R) (h : ∀ i j, g i j - g' i j ∈ J) (i j : Fin n) :
    ((g.map σ).transpose * A * g) i j - ((g'.map σ).transpose * A * g') i j ∈ J := by
  have h1 : ∀ i j, Ideal.Quotient.mk J (g i j) = Ideal.Quotient.mk J (g' i j) := fun i j => Ideal.Quotient.eq.2 (h i j)
  have h2 : ∀ i j, Ideal.Quotient.mk J (σ (g i j)) = Ideal.Quotient.mk J (σ (g' i j)) := fun i j =>
    Ideal.Quotient.eq.2 (by rw [← map_sub]; exact hJ _ (h i j))
  rw [← Ideal.Quotient.eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, h1, h2]

theorem semi_main (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] (σ : R →ₐ[ℤ_[p]] R) (hσ : ∀ r, σ (σ r) = r) (hθ : ∃ θ : R, IsUnit (θ - σ θ))
    (n : ℕ) (A : Matrix (Fin n) (Fin n) R) (hA : (A.map σ).transpose = A) (hd : IsUnit A.det) (I : Ideal R) :
    (∀ x ∈ I, σ x ∈ I) → ∃ g : Matrix (Fin n) (Fin n) R, ∀ i j,
      ((g.map σ).transpose * A * g) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
  have hN : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[p] R
  induction I using IsNoetherian.induction with
  | hgt I ih =>
  intro hI
  by_cases htop : I = ⊤
  · exact ⟨1, fun i j => htop ▸ Submodule.mem_top⟩
  by_cases he : ∃ e : R, e * e - e ∈ I ∧ σ e - e ∈ I ∧ e ∉ I ∧ 1 - e ∉ I
  · obtain ⟨e, he1, he2, he3, he4⟩ := he
    have hst : ∀ u : R, σ u - u ∈ I → ∀ x ∈ I ⊔ Ideal.span {u}, σ x ∈ I ⊔ Ideal.span {u} := by
      intro u hu x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      have : σ (a + r * u) = (σ a + σ r * (σ u - u)) + σ r * u := by rw [map_add (f := _), map_mul]; ring
      rw [this]
      exact Submodule.add_mem_sup (add_mem (hI a ha) (Ideal.mul_mem_left I _ hu)) (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩)
    have hgt : ∀ u : R, u ∉ I → I < I ⊔ Ideal.span {u} := fun u hu =>
      lt_of_le_of_ne le_sup_left fun h => hu (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self u))
    have he2' : σ (1 - e) - (1 - e) ∈ I := by
      have := neg_mem he2
      rw [map_sub, map_one]
      convert this using 1
      ring
    obtain ⟨g₁, hg₁⟩ := ih _ (hgt e he3) (hst e he2)
    obtain ⟨g₂, hg₂⟩ := ih _ (hgt (1 - e) he4) (hst _ he2')
    let g : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (1 - e) * g₁ i j + e * g₂ i j
    refine ⟨g, fun i j => ?_⟩
    have k₁ := add_mem (semi_congr σ _ (hst e he2) A g g₁ (fun i j =>
      Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨g₂ i j - g₁ i j, by simp only [g, Matrix.of_apply]; ring⟩)) i j) (hg₁ i j)
    have k₂ := add_mem (semi_congr σ _ (hst _ he2') A g g₂ (fun i j =>
      Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨g₁ i j - g₂ i j, by simp only [g, Matrix.of_apply]; ring⟩)) i j) (hg₂ i j)
    rw [sub_add_sub_cancel] at k₁ k₂
    generalize ((g.map σ).transpose * A * g) i j - (1 : Matrix (Fin n) (Fin n) R) i j = x at k₁ k₂ ⊢
    obtain ⟨a, ha, b, hb, h1⟩ := Submodule.mem_sup.1 k₁
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨a', ha', b', hb', h2⟩ := Submodule.mem_sup.1 k₂
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hb'
    have : x = (1 - e) * a + e * a' - (r + s) * (e * e - e) := by
      linear_combination (-(1 - e)) * h1 - e * h2
    rw [this]
    exact sub_mem (add_mem (Ideal.mul_mem_left I _ ha) (Ideal.mul_mem_left I _ ha')) (Ideal.mul_mem_left I _ he1)
  · have hnt : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
    let τ : (R ⧸ I) →ₐ[ℤ_[p]] (R ⧸ I) := Ideal.quotientMapₐ I σ hI
    have hτ : ∀ x, τ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (σ x) := fun x => rfl
    obtain ⟨g, hg⟩ := semi_local p (R ⧸ I) τ
      (fun r => by obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r; rw [hτ, hτ, hσ])
      (by
        obtain ⟨θ, h⟩ := hθ
        exact ⟨Ideal.Quotient.mk I θ, by rw [hτ, ← map_sub]; exact h.map _⟩)
      (fun e h1 h2 => by
        obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e
        by_contra hc
        rw [not_or] at hc
        refine he ⟨e, Ideal.Quotient.eq.1 h1, Ideal.Quotient.eq.1 h2, fun h => hc.1 ?_, fun h => hc.2 ?_⟩
        · exact Ideal.Quotient.eq_zero_iff_mem.2 h
        · exact (Ideal.Quotient.eq.2 h).symm)
      n (A.map (Ideal.Quotient.mk I))
      (by
        ext i j
        have := congrFun (congrFun hA i) j
        simp only [Matrix.transpose_apply, Matrix.map_apply] at this ⊢
        rw [hτ, this])
      (by
        have := hd.map (Ideal.Quotient.mk I)
        rwa [RingHom.map_det] at this)
    choose G hG using fun i j => Ideal.Quotient.mk_surjective (g i j)
    refine ⟨Matrix.of G, fun i j => ?_⟩
    have := congrFun (congrFun hg i) j
    rw [← Ideal.Quotient.eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      ← hG, hτ] at this ⊢
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem tw_g_semi : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] (σ : R →ₐ[ℤ_[p]] R), (∀ r, σ (σ r) = r) → (∃ θ : R, IsUnit (θ - σ θ)) → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), (A.map σ).transpose = A → IsUnit A.det → ∃ g : Matrix (Fin n) (Fin n) R, IsUnit g.det ∧ (g.map σ).transpose * A * g = 1 := by
  intro p _ R _ _ _ σ hσ hθ n A hA hd
  obtain ⟨g, hg⟩ := semi_main p R σ hσ hθ n A hA hd ⊥ (fun x hx => by rw [Ideal.mem_bot.1 hx, map_zero]; rfl)
  have h : (g.map σ).transpose * A * g = 1 := by
    ext i j
    exact sub_eq_zero.1 (Ideal.mem_bot.1 (hg i j))
  exact ⟨g, Matrix.isUnit_det_of_left_inverse h, h⟩

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGStd
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGHerm
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_g_herm : ∀ (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R), (∀ r, σ (σ r) = r) → ∀ lam : R →ₗ[Z] Z, (∀ r, lam (σ r) = -lam r) → Function.Bijective (fun r : R => lam.comp (LinearMap.mulLeft Z r)) → ∀ (N : ℕ) (ψ : LinearMap.BilinForm Z (Fin N → R)), (∀ x, ψ x x = 0) → Function.Bijective ψ → (∀ (a : R) x y, ψ (a • x) y = ψ x (σ a • y)) → ∃ A : Matrix (Fin N) (Fin N) R, (A.map σ).transpose = A ∧ IsUnit A.det ∧ ∀ x y, ψ x y = lam (∑ i, ∑ j, x i * A i j * σ (y j)) := by
  intro Z R _ _ _ σ hσ lam hlam hbij N ψ halt hψ hadj
  have hskew : ∀ x y, ψ x y = -ψ y x := fun x y => by
    have := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt] at this
    linear_combination this
  have hinj : ∀ a b : R, (∀ r, lam (a * r) = lam (b * r)) → a = b := fun a b h =>
    hbij.1 (LinearMap.ext fun r => h r)
  have hex : ∀ i j : Fin N, ∃ a : R, ∀ r : R, lam (a * r) = ψ (r • Pi.single i 1) (Pi.single j 1) := by
    intro i j
    obtain ⟨a, ha⟩ := hbij.2 ((ψ.flip (Pi.single j 1)).comp
      ((LinearMap.toSpanSingleton R (Fin N → R) (Pi.single i 1)).restrictScalars Z))
    exact ⟨a, fun r => LinearMap.congr_fun ha r⟩
  choose A hA using hex
  have hform : ∀ x y, ψ x y = lam (∑ i, ∑ j, x i * A i j * σ (y j)) := by
    intro x y
    conv_lhs => rw [pi_eq_sum_univ' x, pi_eq_sum_univ' y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h1 := hadj (σ (y j)) (x i • Pi.single i 1) (Pi.single j 1)
    rw [hσ, smul_smul, ← hA] at h1
    rw [← h1]
    congr 1; ring
  refine ⟨Matrix.of A, ?_, ?_, hform⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    refine hinj _ _ fun r => ?_
    have h1 := hlam (A j i * σ r)
    rw [map_mul, hσ] at h1
    rw [h1, hA, hA, hadj r, hskew (Pi.single i 1)]
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
    intro w
    let F : (Fin N → R) →ₗ[Z] Z := ∑ j, lam.comp ((LinearMap.mulLeft Z (w j)).comp
      (σ.toLinearMap.comp ((LinearMap.proj j : (Fin N → R) →ₗ[R] R).restrictScalars Z)))
    obtain ⟨x, hx⟩ := hψ.2 F
    refine ⟨x, funext fun j => hinj _ _ fun r => ?_⟩
    have h1 := LinearMap.congr_fun hx (Pi.single j (σ r))
    rw [hform] at h1
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.proj_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply] at h1
    have h2 : ∑ d, lam (w d * σ (Pi.single (M := fun _ => R) j (σ r) d)) = lam (w j * r) := by
      rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp),
        Pi.single_eq_same, hσ]
    rw [← h2, ← h1]
    congr 1
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp),
      Pi.single_eq_same, hσ]

end PositivityTheory.UnitarySelfGeneration
end

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem hermitian_form_standard_basis (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R) (hσ : ∀ r, σ (σ r) = r)
    (N : ℕ) (A g : Matrix (Fin N) (Fin N) R) (hg : IsUnit g.det) (h : (g.map σ).transpose * A * g = 1) :
    ∃ φ : (Fin N → R) ≃ₗ[R] (Fin N → R), ∀ x y,
      ∑ i, ∑ j, φ x i * A i j * σ (φ y j) = ∑ i, x i * σ (y i) := by
  have hM : IsUnit (g.map σ).det := by
    have e : σ g.det = (g.map σ).det := AlgHom.map_det σ g
    rw [← e]
    exact hg.map σ
  refine ⟨Matrix.toLinearEquiv' (g.map σ) (Matrix.invertibleOfIsUnitDet (g.map σ) hM), fun x y => ?_⟩
  have hs : (fun j => σ (Matrix.mulVec (g.map σ) y j)) = Matrix.mulVec g (fun k => σ (y k)) := by
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ]
  have key : ∀ u w : Fin N → R, ∑ i, ∑ j, u i * A i j * w j = dotProduct u (Matrix.mulVec A w) := by
    intro u w
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hT : (A * g).transpose * g.map σ = 1 := by
    rw [← Matrix.transpose_transpose (g.map σ), ← Matrix.transpose_mul, ← Matrix.mul_assoc, h,
      Matrix.transpose_one]
  change ∑ i, ∑ j, Matrix.mulVec (g.map σ) x i * A i j * σ (Matrix.mulVec (g.map σ) y j) = _
  rw [key _ (fun j => σ (Matrix.mulVec (g.map σ) y j)), hs, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  simp [dotProduct]

theorem tw_g_std : ∀ (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R), (∀ r, σ (σ r) = r) → ∀ lam : R →ₗ[Z] Z, (∀ r, lam (σ r) = -lam r) → Function.Bijective (fun r : R => lam.comp (LinearMap.mulLeft Z r)) → ∀ (N : ℕ), (∀ A : Matrix (Fin N) (Fin N) R, (A.map σ).transpose = A → IsUnit A.det → ∃ g : Matrix (Fin N) (Fin N) R, IsUnit g.det ∧ (g.map σ).transpose * A * g = 1) → ∀ ψ ψ' : LinearMap.BilinForm Z (Fin N → R), (∀ x, ψ x x = 0) → Function.Bijective ψ → (∀ (a : R) x y, ψ (a • x) y = ψ x (σ a • y)) → (∀ x, ψ' x x = 0) → Function.Bijective ψ' → (∀ (a : R) x y, ψ' (a • x) y = ψ' x (σ a • y)) → ∃ φ : (Fin N → R) ≃ₗ[R] (Fin N → R), ∀ x y, ψ' (φ x) (φ y) = ψ x y := by
  intro Z R _ _ _ σ hσ lam hlam hbij N hstd ψ ψ' hψ0 hψb hψs hψ'0 hψ'b hψ's
  obtain ⟨A, hAh, hAu, hAψ⟩ := tw_g_herm Z R σ hσ lam hlam hbij N ψ hψ0 hψb hψs
  obtain ⟨A', hA'h, hA'u, hA'ψ⟩ := tw_g_herm Z R σ hσ lam hlam hbij N ψ' hψ'0 hψ'b hψ's
  obtain ⟨g, hg, hgA⟩ := hstd A hAh hAu
  obtain ⟨g', hg', hgA'⟩ := hstd A' hA'h hA'u
  obtain ⟨φ, hφ⟩ := hermitian_form_standard_basis Z R σ hσ N A g hg hgA
  obtain ⟨φ', hφ'⟩ := hermitian_form_standard_basis Z R σ hσ N A' g' hg' hgA'
  refine ⟨φ.symm.trans φ', fun x y => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hA'ψ, hφ', ← hφ, φ.apply_symm_apply,
    φ.apply_symm_apply, ← hAψ]

end PositivityTheory.UnitarySelfGeneration
end

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

section

variable {Z O L : Type} [CommRing Z] [CommRing O] [AddCommGroup L] [Module O L]

theorem padic_act {N : ℕ} (φ : (Z ⊗[ℤ] L) ≃ₗ[Z] (Fin N → Z ⊗[ℤ] O))
    (hφ : ∀ (z : Z) (a : O) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ (z ⊗ₜ x)) (a : O)
    (u : Z ⊗[ℤ] L) :
    φ (LinearMap.baseChange Z (LinearMap.lsmul O L a).toAddMonoidHom.toIntLinearMap u) =
      ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    rw [LinearMap.baseChange_tmul]
    exact hφ z a x
  | add u v hu hv => simp only [map_add (f := _), hu, hv, smul_add]

private theorem baseChange_antisymm_of_self_eq_zero (B : LinearMap.BilinForm ℤ L) (hB : ∀ x, B x x = 0) (u v : Z ⊗[ℤ] L) :
    B.baseChange Z u v = - B.baseChange Z v u := by
  have hs : ∀ x y, B x y = - B y x := by
    intro x y
    have h := hB (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, hB, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul w y =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hs x y, neg_smul, mul_comm]
    | add v w hv hw => simp only [map_add (f := _), LinearMap.add_apply, hv, hw, neg_add]
  | add u u' hu hu' => simp only [map_add (f := _), LinearMap.add_apply, hu, hu', neg_add]

theorem padic_alt (B : LinearMap.BilinForm ℤ L) (hB : ∀ x, B x x = 0) (u : Z ⊗[ℤ] L) :
    B.baseChange Z u u = 0 := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x => rw [LinearMap.BilinForm.baseChange_tmul, hB, zero_smul]
  | add u v hu hv =>
    simp only [map_add (f := _), LinearMap.add_apply, hu, hv]
    rw [baseChange_antisymm_of_self_eq_zero B hB u v]
    abel

theorem padic_adj (bar : O ≃+* O) (B : LinearMap.BilinForm ℤ L) (hB : ∀ (a : O) x y, B (a • x) y = B x (bar a • y))
    (a : O) (u v : Z ⊗[ℤ] L) :
    B.baseChange Z (LinearMap.baseChange Z (LinearMap.lsmul O L a).toAddMonoidHom.toIntLinearMap u) v =
      B.baseChange Z u (LinearMap.baseChange Z (LinearMap.lsmul O L (bar a)).toAddMonoidHom.toIntLinearMap v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul w y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
      simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply,
        LinearMap.BilinForm.baseChange_tmul]
      rw [hB]
    | add v w hv hw => simp only [map_add (f := _), hv, hw]
  | add u u' hu hu' => simp only [map_add (f := _), LinearMap.add_apply, hu, hu']

theorem padic_form {N : ℕ} (bar : O ≃+* O) (φ : (Z ⊗[ℤ] L) ≃ₗ[Z] (Fin N → Z ⊗[ℤ] O))
    (hφ : ∀ (z : Z) (a : O) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ (z ⊗ₜ x))
    (B : LinearMap.BilinForm ℤ L) (h1 : ∀ x, B x x = 0) (h2 : Function.Bijective (B.baseChange Z))
    (h3 : ∀ (a : O) x y, B (a • x) y = B x (bar a • y)) :
    ∃ ψ : LinearMap.BilinForm Z (Fin N → Z ⊗[ℤ] O), (∀ u v, ψ (φ u) (φ v) = B.baseChange Z u v) ∧
      (∀ x, ψ x x = 0) ∧ Function.Bijective ψ ∧ ∀ (a : Z ⊗[ℤ] O) x y, ψ (a • x) y =
        ψ x (Algebra.TensorProduct.map (AlgHom.id Z Z) bar.toRingHom.toIntAlgHom a • y) := by
  refine ⟨(B.baseChange Z).compl₁₂ φ.symm.toLinearMap φ.symm.toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro u v
    simp
  · intro x
    simp [padic_alt B h1]
  · constructor
    · intro x y hxy
      apply φ.symm.injective
      apply h2.1
      refine LinearMap.ext fun w => ?_
      have := LinearMap.congr_fun hxy (φ w)
      simpa using this
    · intro f
      obtain ⟨u, hu⟩ := h2.2 (f.comp φ.toLinearMap)
      refine ⟨φ u, LinearMap.ext fun y => ?_⟩
      have := LinearMap.congr_fun hu (φ.symm y)
      simpa using this
  · intro a x y
    obtain ⟨u, rfl⟩ := φ.surjective x
    obtain ⟨v, rfl⟩ := φ.surjective y
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul z c =>
      have hz : ∀ (c' : O) (w : Z ⊗[ℤ] L), (z ⊗ₜ[ℤ] c' : Z ⊗[ℤ] O) • φ w =
          z • φ (LinearMap.baseChange Z (LinearMap.lsmul O L c').toAddMonoidHom.toIntLinearMap w) := by
        intro c' w
        rw [padic_act φ hφ c' w, ← smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul]
      have e1 : (AlgHom.id Z Z) z = z := rfl
      have e2 : bar.toRingHom.toIntAlgHom c = bar c := rfl
      rw [e1, e2, hz, hz]
      simp only [LinearMap.map_smul, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.smul_apply, padic_adj bar B h3]
    | add a a' ha ha' => simp only [add_smul, map_add (f := _), LinearMap.add_apply, ha, ha']

end

theorem padic_unit (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] (d : R)
    (h : IsCoprime d (p : R)) : IsUnit d := by
  obtain ⟨a, b, hab⟩ := h
  have hp : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hN : (⊤ : Submodule ℤ_[p] R) ≤ (Ideal.span {a * d}).restrictScalars ℤ_[p] := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[p])
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    intro x _
    have hx : x = a * d * x + (p : ℤ_[p]) • (b * x) := by
      rw [Algebra.smul_def, map_natCast]
      linear_combination (-x) * hab
    rw [hx]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Submodule.smul_mem_smul hp Submodule.mem_top)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hN Submodule.mem_top : (1 : R) ∈ _)
  have hu : IsUnit (a * d) := IsUnit.of_mul_eq_one y (by rw [mul_comm]; exact hy)
  exact isUnit_of_mul_isUnit_right hu

theorem padic_freeZ (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L] [Module (𝓞 E) L]
    [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] : Module.Finite ℤ L ∧ Module.Free ℤ L := by
  have h1 : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have h2 : Module.Flat ℤ L := Module.Flat.trans ℤ (𝓞 E) L
  exact ⟨h1, inferInstance⟩

theorem tw_g_padic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime] (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L'), (∀ (a : 𝓞 E) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul (𝓞 E) L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) ∧ ∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v := by
  intro E _ _ _ bar hbar hunr p _ L L' _ _ _ _ _ _ _ _ B B' hrk h1 h2 h3 k1 k2 k3
  obtain ⟨_, _⟩ := padic_freeZ E L
  obtain ⟨_, _⟩ := padic_freeZ E L'
  obtain ⟨φ, hφ⟩ := tw_g_free E p L
  have hL' := tw_g_free E p L'
  rw [← hrk] at hL'
  obtain ⟨φ', hφ'⟩ := hL'
  obtain ⟨ψ, hψ, a1, a2, a3⟩ := padic_form bar φ hφ B h1 (GlobalTheory.CompanionTheory.UnimodularBaseChange.bijective_baseChange ℤ_[p] L B h2) h3
  obtain ⟨ψ', hψ', b1, b2, b3⟩ := padic_form bar φ' hφ' B' k1 (GlobalTheory.CompanionTheory.UnimodularBaseChange.bijective_baseChange ℤ_[p] L' B' k2) k3
  obtain ⟨lam, l1, l2⟩ := tw_g_lam E bar hbar hunr p
  obtain ⟨θ, hθ⟩ := tw_g_theta E bar hbar hunr p Fact.out
  have hbb : ∀ a, bar (bar a) = a := fun a => RingOfIntegers.ext (by
    rw [hbar, hbar, IsCMField.complexConj_apply_apply])
  have hσ : ∀ r : ℤ_[p] ⊗[ℤ] 𝓞 E, Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom
      (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom r) = r := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      exact congrArg (z ⊗ₜ[ℤ] ·) (hbb a)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hu : ∃ t : ℤ_[p] ⊗[ℤ] 𝓞 E,
      IsUnit (t - Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom t) := by
    refine ⟨1 ⊗ₜ θ, padic_unit p _ _ ?_⟩
    have := hθ.map (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := 𝓞 E)).toRingHom
    rw [map_natCast, map_sub] at this
    exact this
  obtain ⟨e, he⟩ := tw_g_std ℤ_[p] _ _ hσ lam l1 l2 _ (tw_g_semi p _ _ hσ hu _) ψ ψ' a1 a2 a3 b1 b2 b3
  refine ⟨φ ≪≫ₗ e.restrictScalars ℤ_[p] ≪≫ₗ φ'.symm, fun a x => ?_, fun u v => ?_⟩
  · apply φ'.injective
    rw [padic_act φ' hφ']
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]
    rw [hφ, map_smul]
  · rw [← hψ', ← hψ]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]
    exact he _ _

end PositivityTheory.UnitarySelfGeneration
