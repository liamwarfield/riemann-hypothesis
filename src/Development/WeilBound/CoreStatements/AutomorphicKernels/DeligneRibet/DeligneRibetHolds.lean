module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLargePrimeInRayClass
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLargePrimeInRayClass
open NumberField IsDedekindDomain Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.DegOneRay

variable {F : Type} [Field F] [NumberField F]

theorem finite_realEmb : Finite (F →+* ℝ) :=
  Finite.of_injective (fun σ : F →+* ℝ => (Complex.ofRealHom.comp σ : F →+* ℂ)) fun σ τ h => by
    ext x
    exact Complex.ofReal_injective (congrArg (fun f : F →+* ℂ => f x) h)

theorem exists_totPos_inv {𝔣 : Ideal (𝓞 F)} (hf : 𝔣 ≠ ⊥) {u : 𝓞 F} (hu : IsCoprime (Ideal.span {u}) 𝔣) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ d * u - 1 ∈ 𝔣 ∧ ∀ σ : F →+* ℝ, 0 < σ (d : F) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 hu
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  have hc : c * u - 1 ∈ 𝔣 := by
    have : c * u - 1 = -j := by rw [← hij]; ring
    rw [this]; exact 𝔣.neg_mem hj
  set N : ℕ := Ideal.absNorm 𝔣 with hN
  have hN0 : 0 < N := Nat.pos_of_ne_zero (by simpa [hN, Ideal.absNorm_eq_zero_iff] using hf)
  have hNm : ((N : ℕ) : 𝓞 F) ∈ 𝔣 := Ideal.absNorm_mem 𝔣
  have : Finite (F →+* ℝ) := finite_realEmb
  obtain ⟨b, hb⟩ := (Set.finite_range fun σ : F →+* ℝ => -σ (c : F)).bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt b
  have key : ∀ m : ℕ, M ≤ m → ((c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 ∈ 𝔣 ∧
      ∀ σ : F →+* ℝ, 0 < σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F)) := by
    intro m hm
    refine ⟨?_, fun σ => ?_⟩
    · have : (c + (m : 𝓞 F) * (N : 𝓞 F)) * u - 1 = (c * u - 1) + (N : 𝓞 F) * ((m : 𝓞 F) * u) := by ring
      rw [this]
      exact 𝔣.add_mem hc (𝔣.mul_mem_right _ hNm)
    · have h1 : -σ (c : F) ≤ b := hb ⟨σ, rfl⟩
      have h2 : (M : ℝ) ≤ m := by exact_mod_cast hm
      have h3 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      have h4 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have e : σ ((c + (m : 𝓞 F) * (N : 𝓞 F) : 𝓞 F) : F) = σ (c : F) + (m : ℝ) * (N : ℝ) := by
        push_cast
        simp
      rw [e]
      nlinarith
  by_cases h0 : c + (M : 𝓞 F) * (N : 𝓞 F) = 0
  · refine ⟨c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F), ?_, (key _ (Nat.le_succ M)).1, (key _ (Nat.le_succ M)).2⟩
    have : c + ((M + 1 : ℕ) : 𝓞 F) * (N : 𝓞 F) = (N : 𝓞 F) := by
      push_cast
      linear_combination h0
    rw [this]
    exact_mod_cast hN0.ne'
  · exact ⟨_, h0, (key M le_rfl).1, (key M le_rfl).2⟩

theorem rayRel_of_rayPair {𝔣 𝔠 𝔞 : Ideal (𝓞 F)} (hf : 𝔣 ≠ ⊥) {α β : 𝓞 F} (hr : GlobalTheory.NT.RayPair 𝔣 α β)
    (h : Ideal.span {β} * 𝔠 = Ideal.span {α} * 𝔞) : RayRel F 𝔣 𝔠 𝔞 := by
  obtain ⟨ha, hb, ha', hb', hab, hpos⟩ := hr
  have hb2 : IsCoprime (Ideal.span {β * β}) 𝔣 := by
    rw [← Ideal.span_singleton_mul_span_singleton]; exact hb'.mul_left hb'
  obtain ⟨d, hd0, hd, hdp⟩ := exists_totPos_inv hf hb2
  refine ⟨d * (β * β), d * (α * β), mul_ne_zero hd0 (mul_ne_zero hb hb),
    mul_ne_zero hd0 (mul_ne_zero ha hb), hd, ?_, fun σ => ?_, ?_⟩
  · have : d * (α * β) - 1 = (d * β) * (α - β) + (d * (β * β) - 1) := by ring
    rw [this]
    exact 𝔣.add_mem (𝔣.mul_mem_left _ hab) hd
  · have hbK : (β : F) ≠ 0 := by exact_mod_cast hb
    have hσb : σ (β : F) ≠ 0 := (map_ne_zero σ).2 hbK
    have e1 : σ ((d * (β * β) : 𝓞 F) : F) = σ (d : F) * (σ (β : F) * σ (β : F)) := by
      push_cast; simp
    have e2 : σ ((d * (α * β) : 𝓞 F) : F) = σ (d : F) * (σ (α : F) * σ (β : F)) := by
      push_cast; simp
    rw [e1, e2]
    exact ⟨mul_pos (hdp σ) (mul_self_pos.2 hσb), mul_pos (hdp σ) (hpos σ)⟩
  · calc Ideal.span {d * (β * β)} * 𝔠 = Ideal.span {d * β} * (Ideal.span {β} * 𝔠) := by
          rw [← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton, mul_assoc d]
      _ = Ideal.span {d * β} * (Ideal.span {α} * 𝔞) := by rw [h]
      _ = Ideal.span {d * (α * β)} * 𝔞 := by
          rw [← mul_assoc (Ideal.span {d * β}), Ideal.span_singleton_mul_span_singleton,
            show d * β * α = d * (α * β) by ring]

theorem finite_excluded (𝔣 : Ideal (𝓞 F)) (hf : 𝔣 ≠ ⊥) (W : Finset (𝓞 F)) (B : ℕ) (hW : ∀ x ∈ W, x ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣 ∨ Ideal.absNorm v.asIdeal ≤ B ∨ ∃ x ∈ W, x ∈ v.asIdeal}.Finite := by
  have h1 : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ 𝔣}.Finite := Ideal.finite_factors hf
  have h2 : {v : HeightOneSpectrum (𝓞 F) | Ideal.absNorm v.asIdeal ≤ B}.Finite := by
    have h : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B}.Finite := by
      have : {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ B} =
          ⋃ n ∈ Finset.range (B + 1), {I : Ideal (𝓞 F) | Ideal.absNorm I = n} := by
        ext I; simp [Nat.lt_succ_iff]
      rw [this]
      exact Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => Ideal.finite_setOfPred_absNorm_eq n
    exact (h.preimage (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
      (fun v _ w _ e => HeightOneSpectrum.ext e))
  have h3 : {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal}.Finite := by
    have : {v : HeightOneSpectrum (𝓞 F) | ∃ x ∈ W, x ∈ v.asIdeal} =
        ⋃ x ∈ W, {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {x}} := by
      ext v
      simp [Ideal.dvd_span_singleton]
    rw [this]
    refine Set.Finite.biUnion W.finite_toSet fun x hx => Ideal.finite_factors ?_
    simpa using hW x hx
  exact (h1.union (h2.union h3)).subset fun v hv => by
    rcases hv with h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)]

theorem exists_degree_one_frobenius_prime {Ω : Type} [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω)
    [FiniteDimensional F L] [IsGalois F L] (g : L ≃ₐ[F] L) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g := by
  obtain ⟨v, hv, hd, A, hA, -, σ, hσ, hg⟩ := GlobalTheory.Published.chebotarevDegreeOne' F Ω L g S hS
  refine ⟨v, hv, hd, ?_⟩
  have h := GlobalTheory.RayFromArtin.isFrob_restrict (K := F) (Ω := Ω) L hA hσ
  rwa [hg] at h

theorem exists_degOne_isFrob_of_closure (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {L : Type} [Field L]
    [NumberField L] [Algebra F L] [IsGalois F L] (g : L ≃ₐ[F] L) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite ℚ F L
  let i : L →ₐ[F] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : L ≃ₐ[F] i.fieldRange := AlgEquiv.ofInjectiveField i
  have : IsGalois F i.fieldRange := IsGalois.of_algEquiv e
  have : FiniteDimensional F i.fieldRange := e.toLinearEquiv.finiteDimensional
  obtain ⟨v, hv, hd, h⟩ := exists_degree_one_frobenius_prime i.fieldRange (e.autCongr g) S hS
  exact ⟨v, hv, hd, (GlobalTheory.Mem.Fld.isFrob_congr e v g).1 h⟩

theorem exists_degOne_isFrob {L : Type} [Field L] [NumberField L] [Algebra F L] [IsGalois F L] (g : L ≃ₐ[F] L)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ GlobalTheory.NT.IsFrob L v g :=
  exists_degOne_isFrob_of_closure (AlgebraicClosure F) g S hS

theorem exists_degOne_prime_in_rayClass : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    CoprimeTo F 𝔣 𝔞 → ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
    ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ CoprimeTo F 𝔣 𝔠 ∧
      RayRel F 𝔣 𝔠 𝔞 ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  intro F _ _ 𝔣 𝔞 hf ha W B hW
  obtain ⟨ha0, hac⟩ := ha
  obtain ⟨L, _, _, _, hab, Art, hArt⟩ := (GlobalTheory.Published.rayClassFieldSt_iff_artinIso.1
    (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt GlobalTheory.CompanionTheory.Hypotheses₂.globalArtinReciprocity)) F 𝔣 hf
  have hc : IsCoprime 𝔞 𝔣 := Ideal.isCoprime_iff_sup_eq.2 hac
  obtain ⟨J, hJ⟩ := GlobalTheory.RayFieldCompare.exists_integral 𝔣 𝔞 ha0 hc
  obtain ⟨v, hv, hd, hfr⟩ := exists_degOne_isFrob (Art (QuotientGroup.mk J)) _ (finite_excluded 𝔣 hf W B hW)
  simp only [Set.mem_setOf_eq, not_or, not_exists, not_and] at hv
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have heq : (QuotientGroup.mk J : GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.RayClassGroup 𝔣) = GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeClass 𝔣 v hv1 :=
    Art.injective (GlobalTheory.RayFieldCompare.isFrob_unique L (hArt v hv1).1 hfr (hArt v hv1).2)
  obtain ⟨x, ⟨α, β, hr, hx⟩, hxJ⟩ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 heq)
  have e1 : J.1 * toPrincipalIdeal (𝓞 F) F x = (GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeElt 𝔣 v hv1).1 := by
    rw [hxJ, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  have e2 : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) =
      (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) := by
    have h := congrArg Units.val e1
    rw [Units.val_mul, hJ, coe_toPrincipalIdeal] at h
    exact h
  have hα : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) * FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hx]
  have e3 : Ideal.span {β} * v.asIdeal = Ideal.span {α} * 𝔞 := by
    refine FractionalIdeal.coeIdeal_injective (K := F) ?_
    change ((Ideal.span {β} * v.asIdeal : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      ((Ideal.span {α} * 𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, ← e2]
    change FractionalIdeal.spanSingleton (𝓞 F)⁰ ((β : 𝓞 F) : F) * _ =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((α : 𝓞 F) : F) * _
    rw [hα]
    ring
  refine ⟨v.asIdeal, v.isPrime, ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd,
    not_le.1 hv2, ⟨v.ne_bot, ?_⟩, rayRel_of_rayPair hf hr e3, fun y hy hy' => hv3 y hy hy'⟩
  by_contra hne
  exact hv1 (Ideal.dvd_iff_le.2 ((v.isMaximal.eq_of_le hne le_sup_left).symm ▸ le_sup_right))

end GlobalTheory.CompanionTheory.DegOneRay
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLargePrimeInRayClassStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_prime_in_ray_class : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → CoprimeTo F 𝔣 𝔞 → ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) → ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ CoprimeTo F 𝔣 𝔠 ∧ RayRel F 𝔣 𝔠 𝔞 ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  first | exact @GlobalTheory.CompanionTheory.DegOneRay.exists_degOne_prime_in_rayClass | exact GlobalTheory.CompanionTheory.DegOneRay.exists_degOne_prime_in_rayClass | (intros; apply GlobalTheory.CompanionTheory.DegOneRay.exists_degOne_prime_in_rayClass <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassPartialZetaIntegrality
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassPartialZetaIntegrality
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality

theorem eqOn_compl_one {H R : ℂ → ℂ} (hH : DifferentiableOn ℂ H {1}ᶜ) (hR : DifferentiableOn ℂ R {1}ᶜ)
    (h : ∀ s : ℂ, 1 < s.re → H s = R s) : Set.EqOn H R {1}ᶜ := by
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; first | exact Cardinal.one_lt_two | norm_num | exact_mod_cast (show (1:ℕ) < 2 by norm_num)) 1).isPreconnected
  have hmem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff]; norm_num
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hnhds : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) := hopen.mem_nhds (by norm_num)
  exact (hH.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd isOpen_compl_singleton) hconn hmem (Filter.eventually_of_mem hnhds fun s hs => h s hs)

theorem coneWeight_int {F : Type} [Field F] [NumberField F] {r : ℕ} (l : ℕ) (A : Ideal (𝓞 F)) (y : 𝓞 F)
    (v : Fin r → 𝓞 F) (m : Fin r → ℕ) : ∃ z : ℤ, coneWeight l A y v m = z := by
  unfold coneWeight
  split_ifs
  · exact ⟨(l : ℤ) - 1, by push_cast; ring⟩
  · exact ⟨-1, by push_cast; ring⟩

theorem exists_pow_mul_sum {J : Type} (S : Finset J) (l : ℕ) (q : J → ℚ) (K : J → ℕ) (z : J → ℤ)
    (h : ∀ j, (l : ℚ) ^ K j * q j = z j) : ∃ (K' : ℕ) (Z : ℤ), (l : ℚ) ^ K' * ∑ j ∈ S, q j = Z := by
  refine ⟨∑ j ∈ S, K j, ∑ j ∈ S, (l : ℤ) ^ (∑ i ∈ S, K i - K j) * z j, ?_⟩
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hle : K j ≤ ∑ i ∈ S, K i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
  rw [← h j, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem padicValRat_int_div_nonneg (l : ℕ) [Fact l.Prime] (Z : ℤ) (D : ℕ) (hD : D ≠ 0) (h : ¬ l ∣ D) :
    0 ≤ padicValRat l ((Z : ℚ) / (D : ℚ)) := by
  rcases eq_or_ne Z 0 with rfl | hZ
  · simp
  have hZ' : (Z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hZ
  have hD' : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  rw [padicValRat.div hZ' hD', padicValRat.of_int, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  simp

theorem classTwist_value_int : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J] (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) → ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧ ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := by
  intro F _ _ _ 𝔣 𝔞 𝔟 𝔠 J _ r y v hP h𝔠 hN hv T hT hS k hk
  obtain ⟨hb, hy, hvv, hr, e, he⟩ := hP
  letI : Fintype (F →+* ℝ) := Fintype.ofEquiv (F →+* ℂ) (realEmbeddingsEquiv F).symm
  set l := Ideal.absNorm 𝔠 with hl_def
  have hl0 : 0 < l := hN.pos
  have hcard : Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
    rw [Fintype.card_congr (realEmbeddingsEquiv F)]
    convert NumberField.Embeddings.card F ℂ
  have hNb : Ideal.absNorm 𝔟 ≠ 0 := fun h => hb (Ideal.absNorm_eq_zero_iff.mp h)
  have hNbC : ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hNb
  have hw : ∀ j, GoodWeight l (coneWeight l (𝔠 * 𝔟) (y j) (v j)) := fun j =>
    goodWeight_coneWeight hb hN (hy j).1 (fun i => (hvv j i).1) (hv j)
  have hcont : ∀ j, ∃ Tj : ℂ → ℂ, Differentiable ℂ Tj ∧
      (∀ s : ℂ, 1 < s.re → HasSum (fun m => (coneWeight l (𝔠 * 𝔟) (y j) (v j) m : ℂ) *
        coneTerm (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) s m) (Tj s)) := by
    intro j
    obtain ⟨Tj, hd, hs, -⟩ := abelContinuation (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F))
      (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F)) (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0
      (fun σ i => (hvv j i).2 σ) (fun σ => (hy j).2 σ) (hw j)
    exact ⟨Tj, hd, hs⟩
  choose Tc hTcd hTcs using hcont
  have key : ∀ (s : ℂ) (p : (j : J) × (Fin (r j) → ℕ)),
      (classWeight l 𝔠 (e p).1 : ℂ) * ((Ideal.absNorm (e p).1 : ℕ) : ℂ) ^ (-s) =
        ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2) := by
    rintro s ⟨j, m⟩
    dsimp only
    have hx : (e ⟨j, m⟩).1 * 𝔟 = Ideal.span {conePt (y j) (v j) m} := he ⟨j, m⟩
    have hwt : classWeight l 𝔠 (e ⟨j, m⟩).1 = coneWeight l (𝔠 * 𝔟) (y j) (v j) m := by
      unfold classWeight coneWeight
      rw [le_iff_mem_mul_of_span (𝔠 := 𝔠) hb hx]
    have hnorm : Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) =
        Ideal.absNorm (e ⟨j, m⟩).1 * Ideal.absNorm 𝔟 := by rw [← hx, map_mul]
    rw [hwt, coneTerm_eq_absNorm_cpow (hy j).2 (fun i => (hvv j i).2) s m, hnorm, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s),
      mul_left_comm (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s), ← Complex.cpow_add _ _ hNbC, add_neg_cancel,
      Complex.cpow_zero, mul_one]
  have hRs : ∀ s : ℂ, 1 < s.re → T s = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s := by
    intro s hs
    have h1 := (e.hasSum_iff.mpr (hS s hs))
    have h2 : HasSum (fun p : (j : J) × (Fin (r j) → ℕ) => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s *
        ((coneWeight l (𝔠 * 𝔟) (y p.1) (v p.1) p.2 : ℂ) *
          coneTerm (fun (σ : F →+* ℝ) i => σ ((v p.1 i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y p.1 : 𝓞 F) : F)) s p.2)) (T s) := by
      convert h1 using 1
      funext p
      exact (key s p).symm
    have h3 := h2.sigma (fun j => (hTcs j s hs).mul_left (((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s))
    rw [Finset.mul_sum]
    exact h3.unique (hasSum_fintype _)
  have hRd : DifferentiableOn ℂ (fun s => ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ s * ∑ j, Tc j s) {1}ᶜ := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul
    · exact differentiableAt_id.const_cpow (Or.inl hNbC)
    · have hsd := DifferentiableAt.sum (u := Finset.univ) (fun j _ => hTcd j s)
      have hfun : (fun t => ∑ j, Tc j t) = ∑ j, Tc j := by
        funext t
        simp [Finset.sum_apply]
      rw [hfun]
      exact hsd
  have heq := eqOn_compl_one hT hRd (fun s hs => hRs s hs)
  have hint : ∀ j, ∃ (qj : ℚ) (K : ℕ) (z : ℤ), Tc j (-((k - 1 : ℕ) : ℂ)) = qj ∧ (l : ℚ) ^ K * qj = z := by
    intro j
    refine GlobalTheory.T.cone_zeta_special_value_denominator_bound (F →+* ℝ) (r j) l (fun (σ : F →+* ℝ) i => σ ((v j i : 𝓞 F) : F)) (fun (σ : F →+* ℝ) => σ ((y j : 𝓞 F) : F))
      (coneWeight l (𝔠 * 𝔟) (y j) (v j)) (by rw [hcard]; exact hr j) hl0 (fun σ i => (hvv j i).2 σ)
      (fun σ => (hy j).2 σ) (hw j) (fun m => coneWeight_int l _ _ _ m) (Tc j) (hTcd j).differentiableOn
      (hTcs j) (k - 1) (fun m => ?_)
    have h1 : ∏ σ : F →+* ℝ, (σ ((y j : 𝓞 F) : F) + ∑ i, σ ((v j i : 𝓞 F) : F) * (m i : ℝ)) =
        ((Ideal.absNorm (Ideal.span {conePt (y j) (v j) m}) : ℕ) : ℝ) := by
      rw [← prod_real_embeddings_eq_absNorm _ (totPos_conePt (hy j).2 (fun i => (hvv j i).2) m)]
      exact Finset.prod_congr rfl fun σ _ => (embedding_conePt σ (y j) (v j) m).symm
    refine ⟨(Ideal.absNorm (Ideal.span {conePt (y j) (v j) m})) ^ (k - 1), ?_⟩
    try beta_reduce
    rw [Finset.prod_pow, h1]
    first | norm_cast | (push_cast; ring) | simp
  choose qj Kj zj hqj hzj using hint
  obtain ⟨K', Z, hZ⟩ := exists_pow_mul_sum Finset.univ l qj Kj zj hzj
  have hs0 : (1 - (k : ℂ)) = -(((k - 1 : ℕ)) : ℂ) := by rw [Nat.cast_sub hk]; push_cast; ring
  have hmem : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_singleton_iff, Ne, sub_eq_self]; exact_mod_cast (by omega : k ≠ 0)
  have hval : T (1 - (k : ℂ)) = ((Ideal.absNorm 𝔟 : ℕ) : ℂ) ^ (1 - (k : ℂ)) * ∑ j, (qj j : ℂ) := by
    rw [heq hmem]
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs0]; exact hqj j
  have hlK : (l : ℚ) ^ K' ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl0.ne')
  have hsum : ∑ j, qj j = (Z : ℚ) / (l : ℚ) ^ K' := by
    rw [eq_div_iff hlK, mul_comm]; exact hZ
  have hD : l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hl0.ne') (pow_ne_zero _ hNb)
  refine ⟨(Z : ℚ) / ((l ^ K' * Ideal.absNorm 𝔟 ^ (k - 1) : ℕ) : ℚ), ?_, ?_⟩
  · rw [hval, hs0, Complex.cpow_neg, Complex.cpow_natCast, ← Rat.cast_sum, hsum]
    push_cast
    ring
  · intro l' hl' hne hndvd
    haveI := Fact.mk hl'
    apply padicValRat_int_div_nonneg l' Z _ hD
    intro hdvd
    rcases (Nat.Prime.dvd_mul hl').mp hdvd with h | h
    · exact hne ((Nat.prime_dvd_prime_iff_eq hl' hN).mp (hl'.dvd_of_dvd_pow h))
    · exact hndvd (hl'.dvd_of_dvd_pow h)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassPartialZetaIntegralityStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_partial_zeta_integrality : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J] (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) → ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧ ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormModEqOfRayRelPowMod
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormModEqOfRayRelPowMod
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.RayFacts

theorem absNorm_span_modEq_one {F : Type} [Field F] [NumberField F] (l m : ℕ) {a : 𝓞 F} (ha : a ≠ 0)
    (ha1 : a - 1 ∈ powMod F l m) (hpos : ∀ σ : F →+* ℝ, 0 < σ (a : F)) :
    Ideal.absNorm (Ideal.span {a}) ≡ 1 [MOD l ^ m] := by
  have hn : 0 < Algebra.norm ℤ a := by
    have h := GlobalTheory.RayRootOfUnity.norm_pos_of_pos_real (x := (a : F)) (by simpa using ha) hpos
    rw [← Algebra.coe_norm_int] at h
    exact_mod_cast h
  have hc := GlobalTheory.Mem.RayNorm.norm_cast_eq F (l ^ m) (x := a) (y := 1) (by
    have e : ((l ^ m : ℕ) : 𝓞 F) = (l : 𝓞 F) ^ m := by push_cast; rfl
    rw [e]
    exact ha1)
  rw [map_one, Int.cast_one] at hc
  have h2 := congrArg (Int.cast : ℤ → ZMod (l ^ m)) (Int.natAbs_of_nonneg hn.le)
  rw [Int.cast_natCast] at h2
  rw [← ZMod.natCast_eq_natCast_iff, Ideal.absNorm_span_singleton, h2, hc, Nat.cast_one]

theorem absNorm_modEq_of_rayRel_powMod : ∀ (F : Type) [Field F] [NumberField F] (l m : ℕ) (I J : Ideal (𝓞 F)),
    RayRel F (powMod F l m) I J → Ideal.absNorm I ≡ Ideal.absNorm J [MOD l ^ m] := by
  intro F _ _ l m I J h
  obtain ⟨a, b, ha, hb, ha1, hb1, hσ, he⟩ := h
  have h1 := absNorm_span_modEq_one l m ha ha1 fun σ => (hσ σ).1
  have h2 := absNorm_span_modEq_one l m hb hb1 fun σ => (hσ σ).2
  have h3 := congrArg Ideal.absNorm he
  rw [map_mul, map_mul] at h3
  calc Ideal.absNorm I = 1 * Ideal.absNorm I := (one_mul _).symm
    _ ≡ Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm I [MOD l ^ m] := h1.symm.mul_right _
    _ = Ideal.absNorm (Ideal.span {b}) * Ideal.absNorm J := h3
    _ ≡ 1 * Ideal.absNorm J [MOD l ^ m] := h2.mul_right _
    _ = Ideal.absNorm J := one_mul _

end GlobalTheory.CompanionTheory.RayFacts
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormModEqOfRayRelPowModStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_modEq_pow_of_rayRel_powMod : ∀ (F : Type) [Field F] [NumberField F] (l m : ℕ) (I J : Ideal (𝓞 F)), RayRel F (powMod F l m) I J → Ideal.absNorm I ≡ Ideal.absNorm J [MOD l ^ m] := by
  first | exact @GlobalTheory.CompanionTheory.RayFacts.absNorm_modEq_of_rayRel_powMod | exact GlobalTheory.CompanionTheory.RayFacts.absNorm_modEq_of_rayRel_powMod | (intros; apply GlobalTheory.CompanionTheory.RayFacts.absNorm_modEq_of_rayRel_powMod <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.DeligneRibet.WeightedSummability.WeightedSummable
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace PositivityTheory.PfDR.h_smooth

private theorem rayRel_of_mul_left' {F : Type} [Field F] [NumberField F] {𝔣 𝔠 I J : Ideal (𝓞 F)}
    (h𝔠 : 𝔠 ≠ 0) (h : RayRel F 𝔣 (𝔠 * I) (𝔠 * J)) : RayRel F 𝔣 I J := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hpos, heq⟩ := h
  refine ⟨a, b, ha, hb, ha1, hb1, hpos, ?_⟩
  apply mul_left_cancel₀ h𝔠
  calc 𝔠 * (Ideal.span {a} * I) = Ideal.span {a} * (𝔠 * I) := by ring
    _ = Ideal.span {b} * (𝔠 * J) := heq
    _ = 𝔠 * (Ideal.span {b} * J) := by ring

private theorem ne_zero_of_totPos' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {x : F}
    (hx : TotPos F x) : x ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h := hx (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
  intro h0
  rw [h0, map_zero] at h
  exact lt_irrefl _ h

theorem smoothed_of
    (hcv : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
      (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
      (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ →
        (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
          (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) →
        ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧
          ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q)
    (hcp : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
      ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
        ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
          ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤)
    (hnd : ∀ {F : Type} [Field F] [NumberField F] {l : ℕ}, l.Prime → ∀ {𝔟 : Ideal (𝓞 F)},
      𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟) :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ (S : Finset (Ideal (𝓞 F))), (∀ a ∈ S, CoprimeTo F 𝔣 a) → (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) →
      (∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) → ∀ Z : S → ℂ → ℂ, (∀ c, IsRayZeta 𝔣 c.1 (Z c)) →
      ∃ W : Finset (𝓞 F), (∀ x ∈ W, x ≠ 0) ∧ ∀ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → 𝔠 ⊔ 𝔣 = ⊤ →
        (∀ x ∈ W, x ∉ 𝔠) → ∃ τ : Equiv.Perm S, (∀ c, RayRel F 𝔣 (𝔠 * (τ c).1) c.1) ∧
          ∀ k : ℕ, 1 ≤ k → ∀ c, ∃ q : ℚ,
            ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ k * Z (τ c) (1 - (k : ℂ)) - Z c (1 - (k : ℂ)) = (q : ℂ) ∧
            ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → 𝔣 ≤ Ideal.span {(l : 𝓞 F)} → 0 ≤ padicValRat l q := by
  intro F _ _ _ 𝔣 h𝔣 S hSc hSinj hScov Z hZ
  classical
  have hdat := fun c : S => hcp F 𝔣 h𝔣 c.1 (hSc c.1 c.2)
  choose 𝔟 J hJ r y v hP hb using hdat
  have vne : ∀ c j i, v c j i ≠ 0 := fun c j i h =>
    ne_zero_of_totPos' ((hP c).2.2.1 j i).2 (by simp [h])
  let W : Finset (𝓞 F) := Finset.univ.biUnion
    (fun c : S => (Finset.univ : Finset (Σ j : J c, Fin (r c j))).image (fun p => v c p.1 p.2))
  have memW : ∀ c j i, v c j i ∈ W := fun c j i =>
    Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_image.2 ⟨⟨j, i⟩, Finset.mem_univ _, rfl⟩⟩
  refine ⟨W, ?_, ?_⟩
  · intro x hx
    simp only [W, Finset.mem_biUnion, Finset.mem_image] at hx
    obtain ⟨c, -, ⟨j, i⟩, -, rfl⟩ := hx
    exact vne c j i
  intro 𝔠 h𝔠p h𝔠N h𝔠f hW
  have h𝔠ne : 𝔠 ≠ ⊥ := fun h => by
    rw [h, ← Submodule.zero_eq_bot, map_zero] at h𝔠N
    exact Nat.not_prime_zero h𝔠N
  have h𝔠0 : 𝔠 ≠ 0 := by rw [Ne, Submodule.zero_eq_bot]; exact h𝔠ne
  have hN0 : ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h𝔠N.ne_zero
  have hcopI : ∀ I, CoprimeTo F 𝔣 I → CoprimeTo F 𝔣 (𝔠 * I) := by
    intro I hI
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.mul_eq_bot]
      push_neg
      exact ⟨h𝔠ne, hI.1⟩
    · rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (by rw [sup_comm]; exact h𝔠f), sup_comm]
      exact hI.2
  have hσ : ∀ c : S, ∃ a : S, RayRel F 𝔣 (𝔠 * c.1) a.1 := fun c => by
    obtain ⟨a, ha, h⟩ := hScov _ (hcopI _ (hSc _ c.2))
    exact ⟨⟨a, ha⟩, h⟩
  choose σ hσ using hσ
  have σinj : Function.Injective σ := by
    intro c d h
    have h1 := hσ c
    have h2 := hσ d
    rw [h] at h1
    have h3 := rayRel_of_mul_left' h𝔠0 (GlobalTheory.RayZeta.rayRel_trans h1 (GlobalTheory.RayZeta.rayRel_symm h2))
    exact Subtype.ext (hSinj _ c.2 _ d.2 h3)
  have σbij := Finite.injective_iff_bijective.mp σinj
  set τ : Equiv.Perm S := (Equiv.ofBijective σ σbij).symm with hτdef
  have hτ : ∀ c : S, RayRel F 𝔣 (𝔠 * (τ c).1) c.1 := by
    intro c
    have h := hσ (τ c)
    have e : σ (τ c) = c := Equiv.ofBijective_apply_symm_apply σ σbij c
    rw [e] at h
    exact h
  refine ⟨τ, hτ, ?_⟩
  intro k hk c
  have hd1 : Differentiable ℂ (fun s : ℂ => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s)) :=
    Differentiable.const_cpow differentiable_neg (Or.inl hN0)
  have hdiff : DifferentiableOn ℂ (fun s => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s)
      * Z (τ c) s - Z c s) {1}ᶜ :=
    (((differentiableOn_const _).mul hd1.differentiableOn).mul (hZ (τ c)).1).sub (hZ c).1
  have hsum : ∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))
      (((Ideal.absNorm 𝔠 : ℕ) : ℂ) * ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * Z (τ c) s - Z c s) := by
    intro s hs
    have hA := (hZ c).2 s hs
    have hB := (hZ (τ c)).2 s hs
    let m : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I (τ c).1} →
        {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} := fun I' =>
      ⟨𝔠 * I'.1, hcopI _ I'.2.1,
        GlobalTheory.RayZeta.rayRel_trans (GlobalTheory.RayZeta.rayRel_mul_left 𝔠 I'.2.2) (hτ c)⟩
    have minj : Function.Injective m := fun a b h =>
      Subtype.ext (mul_left_cancel₀ h𝔠0 (Subtype.ext_iff.1 h))
    let f : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} → ℂ := fun I =>
      if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0
    have hf : HasSum f (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * Z (τ c) s) := by
      rw [← minj.hasSum_iff]
      · have e : f ∘ m = fun I' => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * ((Ideal.absNorm I'.1 : ℕ) : ℂ) ^ (-s) := by
          funext I'
          simp only [Function.comp, f, m]
          rw [if_pos Ideal.mul_le_left, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        rw [e]
        exact hB.mul_left _
      · intro I hI
        simp only [f]
        rw [if_neg]
        intro hle
        apply hI
        obtain ⟨I', hI'⟩ := Ideal.dvd_iff_le.2 hle
        have h1 : RayRel F 𝔣 (𝔠 * I') c.1 := by
          rw [← hI']
          exact I.2.2
        have hle' : I.1 ≤ I' := by
          rw [hI']
          exact Ideal.mul_le_right
        refine ⟨⟨I', ⟨fun h => I.2.1.1 (by rw [hI', h, Ideal.mul_bot]), ?_⟩, ?_⟩, Subtype.ext hI'.symm⟩
        · exact top_le_iff.1 (I.2.1.2.ge.trans (sup_le_sup_right hle' _))
        · exact rayRel_of_mul_left' h𝔠0 (GlobalTheory.RayZeta.rayRel_trans h1 (GlobalTheory.RayZeta.rayRel_symm (hτ c)))
    have hC := (hf.mul_left ((Ideal.absNorm 𝔠 : ℕ) : ℂ)).sub hA
    have e2 : (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I c.1} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))
        = fun I => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * f I - ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
      funext I
      simp only [f, classWeight]
      split_ifs <;> push_cast <;> ring
    rw [e2, show ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * Z (τ c) s - Z c s
      = ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * Z (τ c) s) - Z c s by ring]
    exact hC
  obtain ⟨q, hq, hql⟩ := hcv F 𝔣 c.1 (𝔟 c) 𝔠 (J c) (r c) (y c) (v c) (hP c) h𝔠p h𝔠N
    (fun j i hv => hW (v c j i) (memW c j i) (Ideal.mul_le_left hv)) _ hdiff hsum k hk
  refine ⟨q, ?_, fun l hl hlc hfl => hql l hl hlc (hnd hl ?_)⟩
  · have hpow : ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-(1 - (k : ℂ)))
        = ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ k := by
      have he : -(1 - (k : ℂ)) = ((k - 1 : ℕ) : ℂ) := by
        push_cast [Nat.cast_sub hk]
        ring
      rw [he, Complex.cpow_natCast, ← pow_succ', Nat.sub_add_cancel hk]
    rw [← hpow]
    exact hq
  · exact top_le_iff.1 ((hb c).ge.trans (sup_le_sup_left hfl _))

end PositivityTheory.PfDR.h_smooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayRelAntitoneModulusAndPowMod
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayRelAntitoneModulusAndPowMod
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.RayFacts

theorem rayRel_mono_powMod_anti (F : Type) [Field F] [NumberField F] :
    (∀ 𝔣 𝔣' I J : Ideal (𝓞 F), 𝔣' ≤ 𝔣 → RayRel F 𝔣' I J → RayRel F 𝔣 I J) ∧
    (∀ l n m : ℕ, n ≤ m → powMod F l m ≤ powMod F l n) := by
  refine ⟨?_, ?_⟩
  · rintro 𝔣 𝔣' I J hle ⟨a, b, ha, hb, ha1, hb1, hσ, h⟩
    exact ⟨a, b, ha, hb, hle ha1, hle hb1, hσ, h⟩
  · intro l n m hnm
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hnm)

end GlobalTheory.CompanionTheory.RayFacts
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayRelAntitoneModulusAndPowModStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayRel_antitone_modulus_and_powMod : ∀ (F : Type) [Field F] [NumberField F], (∀ 𝔣 𝔣' I J : Ideal (𝓞 F), 𝔣' ≤ 𝔣 → RayRel F 𝔣' I J → RayRel F 𝔣 I J) ∧ (∀ l n m : ℕ, n ≤ m → powMod F l m ≤ powMod F l n) := by
  first | exact @GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti | exact GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti | (intros; apply GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassParametrizationExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassParametrizationExists
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_classParam_sup_eq_top : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  intro F _ _ _ 𝔣 h𝔣 𝔞 h𝔞
  obtain ⟨ι, _, r, v, hdom⟩ := exists_coneDomain F 𝔣 h𝔣
  obtain ⟨𝔟, x₀, hb, hx0, hx1, hxp, hab⟩ := exists_complement h𝔣 h𝔞
  obtain ⟨N, w, hN, hw⟩ := exists_scaled (𝔪 := 𝔟 * 𝔣) (mul_ne_zero hb.1 h𝔣) r v
  have hd := hdom.scale hN (u := fun c i => (w c i : F)) (fun c i => (hw c i).2)
  obtain ⟨J, a, b, c, d, e⟩ := classParam_of_scaled hb.1 hx0 hx1 hxp hab hd
    (fun c i => (Ideal.mul_le_left : 𝔟 * 𝔣 ≤ 𝔟) (hw c i).1)
    (fun c i => (Ideal.mul_le_right : 𝔟 * 𝔣 ≤ 𝔣) (hw c i).1)
  exact ⟨𝔟, J, a, b, c, d, e, hb.2⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassParametrizationExistsStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_parametrization_exists : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 → ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_classParam_sup_eq_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimeNotDividingCoprimeIdealNorm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimeNotDividingCoprimeIdealNorm
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.DeligneRibet

theorem absNorm_not_dvd_of_sup_span_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ), l.Prime → ∀ 𝔟 : Ideal (𝓞 F),
      𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟 := by
  intro F _ _ l hl 𝔟 h hdvd
  have h1 : (1 : 𝓞 F) ∈ 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  by_cases h𝔟 : 𝔟 = ⊥
  · subst h𝔟
    rw [bot_sup_eq] at h
    have hnorm := Ideal.absNorm_span_singleton (l : 𝓞 F)
    rw [h, Ideal.absNorm_top] at hnorm
    have hcast : (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) := by simp
    rw [hcast, Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at hnorm
    have hpos : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp hnorm.symm with h' | h'
    · exact hl.one_lt.ne' h'
    · omega
  · haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔟 h𝔟
    haveI := Fact.mk hl
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hdvd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hdvd
    have hlx : (l : 𝓞 F ⧸ 𝔟) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hunit : Ideal.Quotient.mk 𝔟 a * (l : 𝓞 F ⧸ 𝔟) = 1 := by
      have key := congrArg (Ideal.Quotient.mk 𝔟) hbc
      rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add, map_mul, map_natCast,
        map_one] at key
      exact key
    have hx0 : x = 0 := by
      rw [← one_mul x, ← hunit, mul_assoc, hlx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hl.one_lt.ne hx

end GlobalTheory.CompanionTheory.DeligneRibet
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimeNotDividingCoprimeIdealNormStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_not_dividing_coprime_ideal_norm : ∀ (F : Type) [Field F] [NumberField F] (l : ℕ), l.Prime → ∀ 𝔟 : Ideal (𝓞 F), 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤ → ¬ l ∣ Ideal.absNorm 𝔟 := by
  first | exact @GlobalTheory.CompanionTheory.DeligneRibet.absNorm_not_dvd_of_sup_span_eq_top | exact GlobalTheory.CompanionTheory.DeligneRibet.absNorm_not_dvd_of_sup_span_eq_top | (intros; apply GlobalTheory.CompanionTheory.DeligneRibet.absNorm_not_dvd_of_sup_span_eq_top <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.DeligneRibet.NotDvdAbsNorm
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace PositivityTheory.PfDRL

theorem classValueZ : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J]
    (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime →
    (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ →
      (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} =>
        (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) →
      ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧
        ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := GlobalTheory.T.ray_class_partial_zeta_integrality

theorem classParamCop : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
      ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
        ClassParam 𝔣 𝔞 𝔟 r' y v' ∧ 𝔟 ⊔ 𝔣 = ⊤ := GlobalTheory.T.ray_class_parametrization_exists

theorem not_dvd_absNorm {F : Type} [Field F] [NumberField F] {l : ℕ} (hl : l.Prime) {𝔟 : Ideal (𝓞 F)}
    (h : 𝔟 ⊔ Ideal.span {(l : 𝓞 F)} = ⊤) : ¬ l ∣ Ideal.absNorm 𝔟 := GlobalTheory.T.prime_not_dividing_coprime_ideal_norm F l hl 𝔟 h

theorem deg1Ray : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → CoprimeTo F 𝔣 𝔞 →
    ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) →
      ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ CoprimeTo F 𝔣 𝔠 ∧
        RayRel F 𝔣 𝔠 𝔞 ∧ ∀ x ∈ W, x ∉ 𝔠 := GlobalTheory.T.exists_large_prime_in_ray_class

theorem absNorm_modEq (F : Type) [Field F] [NumberField F] (l m : ℕ) {I J : Ideal (𝓞 F)}
    (h : RayRel F (powMod F l m) I J) : Ideal.absNorm I ≡ Ideal.absNorm J [MOD l ^ m] := GlobalTheory.T.absNorm_modEq_pow_of_rayRel_powMod F l m I J h

theorem rayRel_mono {F : Type} [Field F] [NumberField F] {𝔣 𝔣' I J : Ideal (𝓞 F)} (h : 𝔣' ≤ 𝔣) (hr : RayRel F 𝔣' I J) :
    RayRel F 𝔣 I J := (GlobalTheory.T.rayRel_antitone_modulus_and_powMod F).1 𝔣 𝔣' I J h hr

theorem powMod_le {F : Type} [Field F] [NumberField F] (l : ℕ) {n m : ℕ} (h : n ≤ m) : powMod F l m ≤ powMod F l n := (GlobalTheory.T.rayRel_antitone_modulus_and_powMod F).2 l n m h

theorem smoothed : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ (S : Finset (Ideal (𝓞 F))), (∀ a ∈ S, CoprimeTo F 𝔣 a) → (∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b) →
      (∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) → ∀ Z : S → ℂ → ℂ, (∀ c, IsRayZeta 𝔣 c.1 (Z c)) →
      ∃ W : Finset (𝓞 F), (∀ x ∈ W, x ≠ 0) ∧ ∀ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → 𝔠 ⊔ 𝔣 = ⊤ →
        (∀ x ∈ W, x ∉ 𝔠) → ∃ τ : Equiv.Perm S, (∀ c, RayRel F 𝔣 (𝔠 * (τ c).1) c.1) ∧
          ∀ k : ℕ, 1 ≤ k → ∀ c, ∃ q : ℚ,
            ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ k * Z (τ c) (1 - (k : ℂ)) - Z c (1 - (k : ℂ)) = (q : ℂ) ∧
            ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → 𝔣 ≤ Ideal.span {(l : 𝓞 F)} → 0 ≤ padicValRat l q := PositivityTheory.PfDR.h_smooth.smoothed_of classValueZ classParamCop not_dvd_absNorm

theorem val_add_nonneg {l : ℕ} [Fact l.Prime] {x y : ℚ} (hx : 0 ≤ padicValRat l x)
    (hy : 0 ≤ padicValRat l y) : 0 ≤ padicValRat l (x + y) := by
  by_cases h : x + y = 0
  · simp [h]
  · exact le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add h)

theorem val_mul_nonneg {l : ℕ} [Fact l.Prime] {x y : ℚ} (hx : 0 ≤ padicValRat l x)
    (hy : 0 ≤ padicValRat l y) : 0 ≤ padicValRat l (x * y) := by
  by_cases h0 : x = 0
  · simp [h0]
  by_cases h1 : y = 0
  · simp [h1]
  rw [padicValRat.mul h0 h1]
  exact add_nonneg hx hy

theorem val_sum_nonneg {l : ℕ} [Fact l.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, 0 ≤ padicValRat l (f i)) : 0 ≤ padicValRat l (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact val_add_nonneg (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isRayL_sum {F : Type} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)} {S : Finset (Ideal (𝓞 F))}
    (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a) (hd : ∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b)
    (hc : ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) {Z : S → ℂ → ℂ} (hZ : ∀ c, IsRayZeta 𝔣 c.1 (Z c))
    {ε : Ideal (𝓞 F) → ℚ} (hε : IsRayFun 𝔣 ε) :
    IsRayL 𝔣 ε (fun s => ∑ c : S, (ε c.1 : ℂ) * Z c s) := by
  classical
  have hZ' : ∀ c : S, IsRayL 𝔣 (rayIndicator 𝔣 c.1) (Z c) := fun c => isRayZeta_iff.1 (hZ c)
  have hind : ∀ I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I},
      ∑ c : S, (ε c.1 : ℂ) * ((rayIndicator 𝔣 c.1 I.1 : ℚ) : ℂ) = (ε I.1 : ℂ) := by
    intro I
    obtain ⟨a, ha, hIa⟩ := hc I.1 I.2
    rw [Finset.sum_eq_single (⟨a, ha⟩ : S)]
    · have : ε a = ε I.1 := hε _ _ (hS a ha) I.2 (rayRel_symm hIa)
      simp [rayIndicator, hIa, this]
    · intro b _ hb
      have : ¬ RayRel F 𝔣 I.1 b.1 := fun h =>
        hb (Subtype.ext (hd _ b.2 _ ha (rayRel_trans (rayRel_symm h) hIa)))
      simp [rayIndicator, this]
    · simp
  refine ⟨?_, fun s hs => ?_⟩
  · intro s hs
    refine DifferentiableWithinAt.fun_sum fun c _ => ?_
    exact (differentiableWithinAt_const _).mul ((hZ' c).1 s hs)
  · have h1 := hasSum_sum (s := Finset.univ) fun c (_ : c ∈ (Finset.univ : Finset S)) =>
      ((hZ' c).2 s hs).mul_left (ε c.1 : ℂ)
    have he : (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} => (ε I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) =
        fun I => ∑ c : S, (ε c.1 : ℂ) * (((rayIndicator 𝔣 c.1 I.1 : ℚ) : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
      funext I
      rw [← hind I, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [he]
    exact h1

theorem value_eq {F : Type} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)} {S : Finset (Ideal (𝓞 F))}
    (hS : ∀ a ∈ S, CoprimeTo F 𝔣 a) (hd : ∀ a ∈ S, ∀ b ∈ S, RayRel F 𝔣 a b → a = b)
    (hc : ∀ I, CoprimeTo F 𝔣 I → ∃ a ∈ S, RayRel F 𝔣 I a) {Z : S → ℂ → ℂ} (hZ : ∀ c, IsRayZeta 𝔣 c.1 (Z c))
    {ε : Ideal (𝓞 F) → ℚ} (hε : IsRayFun 𝔣 ε) {k : ℕ} (hk : 1 ≤ k) {z : S → ℚ}
    (hz : ∀ c, Z c (1 - (k : ℂ)) = (z c : ℂ)) {r : ℚ} (hr : IsRayValue 𝔣 ε k r) :
    r = ∑ c : S, ε c.1 * z c := by
  have h := hr.eq hk (isRayL_sum hS hd hc hZ hε)
  simp only [hz] at h
  have h' : ((∑ c : S, ε c.1 * z c : ℚ) : ℂ) = (r : ℂ) := by push_cast; exact h
  exact_mod_cast h'.symm

theorem deligneRibet : GlobalTheory.Published.DeligneRibet := by
  classical
  intro F _ _ _ l _ n hn ε hε hint 𝔠 h𝔠 k hk r r' hr hr'
  have hl : l.Prime := Fact.out
  have h𝔣 : powMod F l n ≠ ⊥ := powMod_ne_bot hl.ne_zero n
  obtain ⟨S, hS, hd, hc⟩ := GlobalTheory.T.ray_class_group_finite_representatives F (powMod F l n) h𝔣
  obtain ⟨Z, hZ⟩ := exists_classZeta F (powMod F l n) h𝔣 S hS hd hc
  choose z hz using fun c : S => (hZ c).2 k hk
  have hZ1 : ∀ c : S, IsRayZeta (powMod F l n) c.1 (Z c) := fun c => (hZ c).1
  have hrv : r = ∑ c : S, ε c.1 * z c := value_eq hS hd hc hZ1 hε hk hz hr
  have hrv' : r' = ∑ c : S, ε (𝔠 * c.1) * z c := value_eq hS hd hc hZ1 (hε.translate h𝔠) hk hz hr'
  set m : ℕ := n + (padicValRat l r').natAbs with hm
  have hnm : n ≤ m := Nat.le_add_right _ _
  have hm1 : 1 ≤ m := le_trans hn hnm
  have h𝔣' : powMod F l m ≠ ⊥ := powMod_ne_bot hl.ne_zero m
  obtain ⟨W, hW0, hW⟩ := smoothed F (powMod F l n) h𝔣 S hS hd hc Z hZ1
  have h𝔠m : CoprimeTo F (powMod F l m) 𝔠 := (coprimeTo_powMod_iff hm1).2 ((coprimeTo_powMod_iff hn).1 h𝔠)
  obtain ⟨𝔠', hpr, hNp, hB, h𝔠'm, hrel, hav⟩ := deg1Ray F (powMod F l m) 𝔠 h𝔣' h𝔠m W l hW0
  have h𝔠'n : CoprimeTo F (powMod F l n) 𝔠' := (coprimeTo_powMod_iff hn).2 ((coprimeTo_powMod_iff hm1).1 h𝔠'm)
  obtain ⟨τ, hτ, hq⟩ := hW 𝔠' hpr hNp h𝔠'n.2 hav
  have hlN : l ≠ Ideal.absNorm 𝔠' := hB.ne
  have hfl : powMod F l n ≤ Ideal.span {(l : 𝓞 F)} := by
    unfold powMod
    rw [Ideal.span_singleton_le_span_singleton]
    exact dvd_pow_self _ (by omega)
  choose q hqv hqval using fun c => hq k hk c
  have hqeq : ∀ c, (Ideal.absNorm 𝔠' : ℚ) ^ k * z (τ c) - z c = q c := by
    intro c
    have h := hqv c
    rw [hz (τ c), hz c] at h
    exact_mod_cast h
  have heq : ∀ c : S, ε (𝔠 * (τ c).1) = ε c.1 := by
    intro c
    have h1 : RayRel F (powMod F l n) 𝔠 𝔠' := rayRel_symm (rayRel_mono (powMod_le l hnm) hrel)
    have h2 : RayRel F (powMod F l n) ((τ c).1 * 𝔠) ((τ c).1 * 𝔠') := rayRel_mul_left _ h1
    rw [mul_comm (τ c).1 𝔠, mul_comm (τ c).1 𝔠'] at h2
    exact hε _ _ (coprimeTo_mul h𝔠 (hS _ (τ c).2)) (hS _ c.2) (rayRel_trans h2 (hτ c))
  have hr'τ : r' = ∑ c : S, ε c.1 * z (τ c) := by
    rw [hrv']
    refine (Fintype.sum_equiv τ _ _ fun c => ?_).symm
    show ε c.1 * z (τ c) = ε (𝔠 * (τ c).1) * z (τ c)
    rw [heq c]
  have hA : r - (Ideal.absNorm 𝔠' : ℚ) ^ k * r' = -∑ c : S, ε c.1 * q c := by
    rw [hrv, hr'τ, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hqeq c]
    ring
  have hAval : 0 ≤ padicValRat l (r - (Ideal.absNorm 𝔠' : ℚ) ^ k * r') := by
    rw [hA, padicValRat.neg]
    refine val_sum_nonneg _ _ fun c _ => val_mul_nonneg ?_ ?_
    · exact inZl_iff.1 (hint _ (hS _ c.2))
    · exact hqval c l hl hlN hfl
  have hmod : Ideal.absNorm 𝔠' ^ k ≡ Ideal.absNorm 𝔠 ^ k [MOD l ^ m] := (absNorm_modEq F l m hrel).pow k
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd.1 hmod.symm)
  have hB' : 0 ≤ padicValRat l (((Ideal.absNorm 𝔠' : ℚ) ^ k - (Ideal.absNorm 𝔠 : ℚ) ^ k) * r') := by
    have hcast : (Ideal.absNorm 𝔠' : ℚ) ^ k - (Ideal.absNorm 𝔠 : ℚ) ^ k = (l : ℚ) ^ m * (t : ℚ) := by
      have h := congrArg (fun x : ℤ => (x : ℚ)) ht
      push_cast at h
      exact h
    rw [hcast]
    by_cases ht0 : t = 0
    · simp [ht0]
    by_cases hr0 : r' = 0
    · simp [hr0]
    have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne_zero
    have ht0' : (t : ℚ) ≠ 0 := by exact_mod_cast ht0
    have hlm : padicValRat l ((l : ℚ) ^ m) = m := by
      rw [show ((l : ℚ) ^ m) = ((l ^ m : ℕ) : ℚ) by push_cast; rfl, padicValRat.of_nat, padicValNat.prime_pow]
    rw [mul_assoc, padicValRat.mul (pow_ne_zero _ hl0) (mul_ne_zero ht0' hr0), padicValRat.mul ht0' hr0, hlm]
    have hv : 0 ≤ padicValRat l (t : ℚ) := by
      rw [padicValRat.of_int]
      exact Nat.cast_nonneg _
    have key : -(padicValRat l r') ≤ ((padicValRat l r').natAbs : ℤ) := by
      rw [← Int.natAbs_neg]
      exact Int.le_natAbs
    have hmz : (m : ℤ) = (n : ℤ) + ((padicValRat l r').natAbs : ℤ) := by
      rw [hm]
      push_cast
      ring
    rw [hmz]
    have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg _
    linarith
  rw [inZl_iff]
  have hsplit : r - (Ideal.absNorm 𝔠 : ℚ) ^ k * r' = (r - (Ideal.absNorm 𝔠' : ℚ) ^ k * r') +
      ((Ideal.absNorm 𝔠' : ℚ) ^ k - (Ideal.absNorm 𝔠 : ℚ) ^ k) * r' := by ring
  rw [hsplit]
  exact val_add_nonneg hAval hB'

end PositivityTheory.PfDRL
end
end

theorem PositivityTheory.PfDR.deligneRibet_holds : GlobalTheory.Published.DeligneRibet :=
  PositivityTheory.PfDRL.deligneRibet
