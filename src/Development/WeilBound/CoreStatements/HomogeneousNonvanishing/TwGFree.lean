module

public import Mathlib

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGFree
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem free_semilocal (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R] [Module.Finite A R] :
    Finite (MaximalSpectrum R) := by
  haveI := (Algebra.QuasiFinite.finite_primesOver (R := A) (S := R)
    (IsLocalRing.maximalIdeal A)).to_subtype
  have hover : ∀ P : MaximalSpectrum R, IsLocalRing.maximalIdeal A = Ideal.under A P.asIdeal :=
    fun P =>
      haveI := P.isMaximal
      (IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) P.asIdeal)).symm
  exact Finite.of_injective (β := ↥((IsLocalRing.maximalIdeal A).primesOver R))
    (fun P => ⟨P.asIdeal, P.isMaximal.isPrime, Ideal.LiesOver.mk (hover P)⟩)
    (fun P Q h => MaximalSpectrum.ext (congrArg Subtype.val h))

theorem free_rank (B K L : Type) [CommRing B] [IsDomain B] [Field K] [Algebra B K] [AddCommGroup L] [Module B L]
    [Module.Finite B L] [Module.Projective B L] : Module.finrank K (K ⊗[B] L) = Module.finrank B L := by
  haveI : Module.Flat B L := Module.Flat.of_projective
  haveI : Module.Free K (K ⊗[B] L) := Module.Free.of_divisionRing K _
  have hstalk : ∀ q : PrimeSpectrum B, Module.rankAtStalk L q = Module.finrank B L := by
    intro q
    have hle := Ideal.primeCompl_le_nonZeroDivisors q.asIdeal
    show Module.finrank (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl L) = _
    rw [IsLocalization.finrank_eq (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl hle,
      IsLocalizedModule.finrank_eq q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl L) hle]
  have hK := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := K ⊗[B] L))
    (IsLocalRing.closedPoint K)
  rw [Module.rankAtStalk_baseChange, hstalk] at hK
  simp only [Pi.natCast_apply, Nat.cast_id] at hK
  exact hK.symm

theorem tw_g_free : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (L : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L], ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (Fin (Module.finrank (𝓞 E) L) → ℤ_[p] ⊗[ℤ] 𝓞 E), ∀ (z : ℤ_[p]) (a : 𝓞 E) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : ℤ_[p]) ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] 𝓞 E) • φ (z ⊗ₜ x) := by
  intro E _ _ p _ L _ _ _ _
  haveI : Module.Flat (𝓞 E) L := Module.Flat.of_projective
  haveI : Module.Finite ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := Module.Finite.base_change ℤ ℤ_[p] (𝓞 E)
  haveI : Finite (MaximalSpectrum (ℤ_[p] ⊗[ℤ] 𝓞 E)) :=
    PositivityTheory.UnitarySelfGeneration.free_semilocal ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)
  haveI : Module.Flat (ℤ_[p] ⊗[ℤ] 𝓞 E) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L) :=
    Module.Flat.baseChange (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) L
  haveI : Module.Finite (ℤ_[p] ⊗[ℤ] 𝓞 E) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L) :=
    Module.Finite.base_change (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) L
  haveI : Algebra.IsPushout ℤ ℤ_[p] (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) := TensorProduct.isPushout
  have hrank : ∀ P : MaximalSpectrum (ℤ_[p] ⊗[ℤ] 𝓞 E),
      Module.finrank ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal)
        (((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) ⊗[ℤ_[p] ⊗[ℤ] 𝓞 E] ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L)) =
        Module.finrank (𝓞 E) L := by
    intro P
    haveI := P.isMaximal
    letI : Field ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E)
      ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) L).finrank_eq.trans
      (PositivityTheory.UnitarySelfGeneration.free_rank (𝓞 E) ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⧸ P.asIdeal) L)
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (ℤ_[p] ⊗[ℤ] 𝓞 E)
    ((ℤ_[p] ⊗[ℤ] 𝓞 E) ⊗[𝓞 E] L) _ hrank
  refine ⟨(Algebra.IsPushout.cancelBaseChange ℤ ℤ_[p] (𝓞 E) (ℤ_[p] ⊗[ℤ] 𝓞 E) L).symm.trans
    (b.equivFun.restrictScalars ℤ_[p]), ?_⟩
  intro z a x
  have key : (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) z) ⊗ₜ[𝓞 E] (a • x) =
      ((1 : ℤ_[p]) ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] 𝓞 E) • ((algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) z) ⊗ₜ[𝓞 E] x) := by
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul,
      Algebra.TensorProduct.right_algebraMap_apply]
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, key, map_smul]

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGTheta
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGDiff
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem differentiable_schwartz_translate {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.Unramified A B]
    (σ : B →ₐ[A] B) (hσ : ∃ s, σ s ≠ s) : Ideal.span (Set.range fun x : B => x - σ x) = ⊤ := by
  obtain ⟨t, ht1, ht2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := B)).1 inferInstance
  let φ : B ⊗[A] B →ₐ[A] B := Algebra.TensorProduct.lift (AlgHom.id A B) σ fun _ _ => Commute.all _ _
  obtain ⟨s, hs⟩ := hσ
  have h0 : φ t = 0 := by
    have := congrArg φ (ht1 s)
    rw [map_mul, map_zero, map_sub] at this
    simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, AlgHom.id_apply, one_mul, mul_one] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hs)
  have h1 : ∀ u : B ⊗[A] B, Algebra.TensorProduct.lmul' A u - φ u ∈
      Ideal.span (Set.range fun x : B => x - σ x) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [φ, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, Algebra.TensorProduct.lmul'_apply_tmul]
      rw [← mul_sub]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, rfl⟩)
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact add_mem hx hy
  have := h1 t
  rw [ht2, h0, sub_zero] at this
  exact (Ideal.eq_top_iff_one _).2 this

theorem tw_g_diff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → Ideal.span (Set.range fun x : 𝓞 E => x - bar x) = ⊤ := by
  intro E _ _ _ bar hbar hun
  let σ : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E :=
    { bar.toRingHom with
      commutes' := fun r => by
        apply RingOfIntegers.ext
        show ((bar _ : 𝓞 E) : E) = _
        rw [hbar]
        exact IsCMField.complexConj_apply_eq_self E (r : maximalRealSubfield E) }
  refine differentiable_schwartz_translate σ ?_
  by_contra hne
  push Not at hne
  apply IsCMField.complexConj_ne_one E
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have h : ∀ a : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a := fun a => by
    have h1 : bar a = a := hne a
    have := hbar a
    rw [h1] at this
    exact this.symm
  rw [map_div₀, h, h]; rfl

end PositivityTheory.UnitarySelfGeneration
end

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem anti_one {B : Type} [CommRing B] (σ : B ≃+* B) (I : Ideal B)
    (hspan : Ideal.span (Set.range fun x : B => x - σ x) = ⊤) (P : Ideal B) (hP : ¬ I ≤ P * I) :
    ∃ x ∈ I, x - σ x ∉ P * I := by
  by_contra hcon
  push_neg at hcon
  apply hP
  intro i hi
  have hJ : Ideal.span (Set.range fun x : B => x - σ x) ≤
      Submodule.comap (LinearMap.toSpanSingleton B B i) (P * I) := by
    rw [Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, smul_eq_mul]
    have h1 := hcon (b * i) (I.mul_mem_left b hi)
    have h2 := hcon i hi
    have e : (b - σ b) * i = (b * i - σ (b * i)) - σ b * (i - σ i) := by
      rw [map_mul]
      ring
    rw [e]
    exact sub_mem h1 (Ideal.mul_mem_left _ _ h2)
  rw [hspan] at hJ
  have h1 : (1 : B) ∈ Submodule.comap (LinearMap.toSpanSingleton B B i) (P * I) :=
    hJ Submodule.mem_top
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul] at h1
  exact h1

theorem anti_avoid {B : Type} [CommRing B] (σ : B ≃+* B) (hσ : ∀ x, σ (σ x) = x) (I : Ideal B)
    (hI : ∀ x ∈ I, σ x ∈ I) (hspan : Ideal.span (Set.range fun x : B => x - σ x) = ⊤)
    (S : Finset (Ideal B)) (hS : ∀ P ∈ S, P.IsMaximal ∧ ¬ I ≤ P * I) :
    ∃ x ∈ I, ∀ P ∈ S, x - σ x ∉ P * I := by
  classical
  have hmap : ∀ P : Ideal B, P * I ≤ (P.comap σ * I).comap σ := by
    intro P
    rw [Ideal.mul_le]
    intro r hr s hs
    rw [Ideal.mem_comap, map_mul]
    refine Ideal.mul_mem_mul ?_ (hI s hs)
    rw [Ideal.mem_comap, hσ]
    exact hr
  have hneg : ∀ x : B, σ (x - σ x) = -(x - σ x) := by
    intro x
    rw [map_sub, hσ, neg_sub]
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _
    exact ⟨0, I.zero_mem, fun P hP => by simp at hP⟩
  intro P S hPS ih hS
  obtain ⟨x, hxI, hx⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
  obtain ⟨hPmax, hPI⟩ := hS P (Finset.mem_insert_self P S)
  by_cases hxP : x - σ x ∈ P * I
  swap
  · refine ⟨x, hxI, fun Q hQ => ?_⟩
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · exact hxP
    · exact hx Q hQ
  by_cases hσP : P.comap σ ∈ S
  · exfalso
    apply hx _ hσP
    have h1 := Ideal.mem_comap.mp (hmap P hxP)
    rw [hneg] at h1
    exact neg_mem_iff.mp h1
  have hPc : (P.comap σ).IsPrime := Ideal.comap_isPrime σ P
  have hnot : ¬ ((S.inf fun Q => Q ⊓ Q.comap σ : Ideal B) : Set B) ⊆
      (P : Set B) ∪ (P.comap σ : Set B) := by
    rw [Ideal.subset_union]
    rintro (hle | hle)
    · obtain ⟨Q, hQ, hQle⟩ := (Ideal.IsPrime.inf_le' hPmax.isPrime).mp hle
      have hQmax := (hS Q (Finset.mem_insert_of_mem hQ)).1
      rcases hPmax.isPrime.inf_le.mp hQle with h | h
      · exact hPS (by rw [← hQmax.eq_of_le hPmax.ne_top h]; exact hQ)
      · apply hσP
        have hQle' : Q ≤ P.comap σ := fun q hq => by
          rw [Ideal.mem_comap]
          apply h
          rw [Ideal.mem_comap, hσ]
          exact hq
        rw [← hQmax.eq_of_le hPc.ne_top hQle']
        exact hQ
    · obtain ⟨Q, hQ, hQle⟩ := (Ideal.IsPrime.inf_le' hPc).mp hle
      have hQmax := (hS Q (Finset.mem_insert_of_mem hQ)).1
      rcases hPc.inf_le.mp hQle with h | h
      · exact hσP (by rw [← hQmax.eq_of_le hPc.ne_top h]; exact hQ)
      · apply hPS
        have hQle' : Q ≤ P := fun q hq => by
          have h2 := h (show σ q ∈ Q.comap σ by rw [Ideal.mem_comap, hσ]; exact hq)
          rw [Ideal.mem_comap, hσ] at h2
          exact h2
        rw [← hQmax.eq_of_le hPmax.ne_top hQle']
        exact hQ
  obtain ⟨a, haK, haP⟩ := Set.not_subset.mp hnot
  rw [Set.mem_union, not_or] at haP
  obtain ⟨haP1, haP2⟩ := haP
  have hσa : σ a ∉ P := fun h => haP2 (Ideal.mem_comap.mpr h)
  have haQ : ∀ Q ∈ S, a ∈ Q := by
    intro Q hQ
    have h := Finset.inf_le (f := fun Q : Ideal B => Q ⊓ Q.comap σ) hQ haK
    exact (Submodule.mem_inf.mp h).1
  have hc : σ (a * σ a) = a * σ a := by
    rw [map_mul, hσ, mul_comm]
  have hcP : a * σ a ∉ P := fun h => (hPmax.isPrime.mem_or_mem h).elim haP1 hσa
  obtain ⟨y, hyI, hy⟩ := PositivityTheory.UnitarySelfGeneration.anti_one σ I hspan P hPI
  have hyD : y - σ y ∈ I := I.sub_mem hyI (hI y hyI)
  refine ⟨x + a * σ a * y, I.add_mem hxI (I.mul_mem_left _ hyI), fun Q hQ => ?_⟩
  have hD : x + a * σ a * y - σ (x + a * σ a * y) = (x - σ x) + a * σ a * (y - σ y) := by
    rw [map_add (f := _), map_mul, hc]
    ring
  rw [hD]
  rcases Finset.mem_insert.mp hQ with rfl | hQ
  · intro hmem
    apply hy
    rw [Submodule.add_mem_iff_right _ hxP] at hmem
    obtain ⟨d, e, he, hde⟩ := hPmax.exists_inv hcP
    have hyz : y - σ y = d * (a * σ a * (y - σ y)) + e * (y - σ y) := by
      calc y - σ y = (d * (a * σ a) + e) * (y - σ y) := by rw [hde, one_mul]
        _ = d * (a * σ a * (y - σ y)) + e * (y - σ y) := by ring
    rw [hyz]
    exact add_mem (Ideal.mul_mem_left _ d hmem) (Ideal.mul_mem_mul he hyD)
  · intro hmem
    apply hx Q hQ
    have hcQ : a * σ a * (y - σ y) ∈ Q * I :=
      Ideal.mul_mem_mul (Ideal.mul_mem_right _ Q (haQ Q hQ)) hyD
    exact (Submodule.add_mem_iff_left _ hcQ).mp hmem

theorem anti_ded {B : Type} [CommRing B] [IsDedekindDomain B] (σ : B ≃+* B) (hσ : ∀ x, σ (σ x) = x)
    (I : Ideal B) (hI0 : I ≠ ⊥)
    (hI : ∀ x ∈ I, σ x ∈ I) (hspan : Ideal.span (Set.range fun x : B => x - σ x) = ⊤)
    (p : B) (hp : p ≠ 0) : ∃ x ∈ I, ∀ P : Ideal B, P.IsMaximal → p ∈ P → x - σ x ∉ P * I := by
  classical
  have hspan0 : Ideal.span {p} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp
  have hI0' : I ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot]
    exact hI0
  have hT : ∀ P ∈ (Ideal.finite_factors hspan0).toFinset.image
      (fun v : IsDedekindDomain.HeightOneSpectrum B => v.asIdeal), P.IsMaximal ∧ ¬ I ≤ P * I := by
    intro P hP
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hP
    refine ⟨v.isMaximal, fun hle => ?_⟩
    have heq : v.asIdeal * I = ⊤ * I := by
      rw [Ideal.top_mul]
      exact le_antisymm (Ideal.mul_le.mpr fun r _ s hs => I.mul_mem_left r hs) hle
    exact v.isMaximal.ne_top (mul_right_cancel₀ hI0' heq)
  obtain ⟨x, hxI, hx⟩ :=
    PositivityTheory.UnitarySelfGeneration.anti_avoid σ hσ I hI hspan _ hT
  refine ⟨x, hxI, fun P hPmax hpP => hx P ?_⟩
  have hPbot : P ≠ ⊥ := fun h => hp (by rw [h] at hpP; exact Ideal.mem_bot.mp hpP)
  refine Finset.mem_image.mpr ⟨⟨P, hPmax.isPrime, hPbot⟩, ?_, rfl⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  exact hpP

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) (a : 𝓞 E) : bar (bar a) = a := by
  apply RingOfIntegers.ext
  rw [hbar, hbar, IsCMField.complexConj_apply_apply]

theorem tw_g_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ p : ℕ, p.Prime → ∃ θ : 𝓞 E, IsCoprime (θ - bar θ) (p : 𝓞 E) := by
  intro E _ _ _ bar hbar hunr p hp
  have hspan := PositivityTheory.UnitarySelfGeneration.tw_g_diff E bar hbar hunr
  have hinv : ∀ a, bar (bar a) = a := PositivityTheory.UnitarySelfGeneration.bar_bar bar hbar
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨x, -, hx⟩ := PositivityTheory.UnitarySelfGeneration.anti_ded bar hinv ⊤
    top_ne_bot (fun _ _ => Submodule.mem_top) hspan (p : 𝓞 E) hp0
  refine ⟨x, ?_⟩
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  apply hx P hPmax (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  rw [Ideal.mul_top]
  exact hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))

end PositivityTheory.UnitarySelfGeneration
end
