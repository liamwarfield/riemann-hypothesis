module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TorsionTotientBound

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemTorsionOfMulConj
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TwoLeAbsNormPrime
noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

variable {E : Type} [Field E] [NumberField E]

theorem two_le_absNorm_prime {P : Ideal (𝓞 E)} (hP : P.IsPrime) (h0 : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  have h2 : Ideal.absNorm P ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0
  omega

theorem card_dvd_le_absNorm (M : Ideal (𝓞 E)) (hM : M ≠ ⊥) (D : Finset (Ideal (𝓞 E)))
    (hD : ∀ I ∈ D, I ∣ M) : D.card ≤ Ideal.absNorm M := by
  classical
  have hI0 : ∀ I ∈ D, I ≠ ⊥ := fun I hI h => hM (by obtain ⟨c, hc⟩ := hD I hI; rw [hc, h, Ideal.bot_mul])
  have hinj : Set.InjOn (fun I => UniqueFactorizationMonoid.normalizedFactors I) (D : Set (Ideal (𝓞 E))) := by
    intro I hI J hJ h
    rw [← Ideal.prod_normalizedFactors_eq_self (hI0 I hI), ← Ideal.prod_normalizedFactors_eq_self (hI0 J hJ)]
    exact congrArg Multiset.prod h
  have hsub : D.image (fun I => UniqueFactorizationMonoid.normalizedFactors I) ⊆
      (UniqueFactorizationMonoid.normalizedFactors M).powerset.toFinset := by
    intro s hs
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hs
    rw [Multiset.mem_toFinset, Multiset.mem_powerset]
    exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors (hI0 I hI) hM).1 (hD I hI)
  have h1 : D.card ≤ 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) := by
    calc D.card = (D.image fun I => UniqueFactorizationMonoid.normalizedFactors I).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (UniqueFactorizationMonoid.normalizedFactors M).powerset.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M).powerset := Multiset.toFinset_card_le _
      _ = 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) := Multiset.card_powerset _
  have h2 : 2 ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors M) ≤ Ideal.absNorm M := by
    have hprod : Ideal.absNorm M =
        ((UniqueFactorizationMonoid.normalizedFactors M).map Ideal.absNorm).prod := by
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hM]
      exact map_multiset_prod Ideal.absNorm _
    rw [hprod, ← Multiset.card_map Ideal.absNorm]
    refine Multiset.pow_card_le_prod fun n hn => ?_
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hn
    have hpr := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    exact two_le_absNorm_prime (Ideal.isPrime_of_prime hpr) hpr.ne_zero
  exact h1.trans h2

theorem absNorm_map_equiv (σ : 𝓞 E ≃+* 𝓞 E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.map σ) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map σ) σ rfl).toEquiv.symm

end Formalism.L2.SG.NGCut.TorsionTotientBound
end
end

noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cO (E : Type) [Field E] [NumberField E] [IsCMField E] : 𝓞 E ≃+* 𝓞 E :=
  RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv

theorem cO_coe (y : 𝓞 E) : ((cO E y : 𝓞 E) : E) = IsCMField.complexConj E (y : E) := rfl

theorem mem_torsion_of_mul_conj (u : (𝓞 E)ˣ)
    (hu : ((u : 𝓞 E) : E) * IsCMField.complexConj E ((u : 𝓞 E) : E) = 1) : u ∈ Units.torsion E := by
  rw [Units.mem_torsion]
  intro w
  have h1 : w.embedding ((u : 𝓞 E) : E) *
      w.embedding (IsCMField.complexConj E ((u : 𝓞 E) : E)) = 1 := by
    rw [← map_mul, hu, map_one]
  rw [IsCMField.complexEmbedding_complexConj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h2 : ‖w.embedding ((u : 𝓞 E) : E)‖ ^ 2 = 1 := by exact_mod_cast h1
  have key : ‖w.embedding ((u : 𝓞 E) : E)‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  exact (InfinitePlace.norm_embedding_eq w _).symm.trans key

theorem count_int (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (m : 𝓞 E) (hm : m ≠ 0) (S : Finset (𝓞 E))
    (hS : ∀ y ∈ S, y ∈ I ∧ y * cO E y = m) :
    S.card * Ideal.absNorm I ^ 2 ≤ 2 * (Module.finrank ℚ E) ^ 2 * (Algebra.norm ℤ m).natAbs := by
  classical
  haveI : Fintype (Units.torsion E) := Fintype.ofFinite _
  rcases S.eq_empty_or_nonempty with hS0 | ⟨y0, hy0⟩
  · simp [hS0]
  have hNI' : Ideal.absNorm (I.map (cO E)) = Ideal.absNorm I :=
    absNorm_map_equiv (cO E) I
  have hI0 : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hI'0 : I.map (cO E) ≠ ⊥ := by
    intro h; apply hI0; rw [← hNI']; exact Ideal.absNorm_eq_zero_iff.mpr h
  have hdvdI : ∀ y ∈ S, I ∣ Ideal.span {y} := fun y hy =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem I).mpr (hS y hy).1)
  have hdvdI' : ∀ y ∈ S, I.map (cO E) ∣ Ideal.span {cO E y} := fun y hy =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_map_of_mem (cO E) (hS y hy).1))
  have hspan : ∀ y ∈ S, Ideal.span {y} * Ideal.span {cO E y} = Ideal.span {m} :=
    fun y hy => by rw [Ideal.span_singleton_mul_span_singleton, (hS y hy).2]
  obtain ⟨M, hM⟩ : I * I.map (cO E) ∣ Ideal.span {m} := by
    rw [← hspan y0 hy0]; exact mul_dvd_mul (hdvdI y0 hy0) (hdvdI' y0 hy0)
  have hm0 : Ideal.span {m} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hM0 : M ≠ ⊥ := by
    rintro rfl; rw [Ideal.mul_bot] at hM; exact hm0 hM
  have hNm : (Algebra.norm ℤ m).natAbs = Ideal.absNorm I ^ 2 * Ideal.absNorm M := by
    rw [← Ideal.absNorm_span_singleton, hM, map_mul, map_mul, hNI', sq]
  have hII' : I * I.map (cO E) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.mul_eq_bot, not_or]; exact ⟨hI, hI'0⟩
  have hdiv : ∀ y ∈ S, ∃ K : Ideal (𝓞 E), Ideal.span {y} = I * K := fun y hy => by
    obtain ⟨K, hK⟩ := hdvdI y hy; exact ⟨K, hK⟩
  choose! J hJ using hdiv
  have hJM : ∀ y ∈ S, J y ∣ M := fun y hy => by
    obtain ⟨K, hK⟩ := hdvdI' y hy
    refine ⟨K, ?_⟩
    have h := hspan y hy
    rw [hJ y hy, hK, hM] at h
    apply mul_left_cancel₀ hII'
    rw [← h]; ring
  have hcardJ : (S.image J).card ≤ Ideal.absNorm M :=
    card_dvd_le_absNorm M hM0 _ (fun K hK => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hK; exact hJM y hy)
  have hT : ∀ K ∈ S.image J, (S.filter fun y => J y = K).card ≤ Fintype.card (Units.torsion E) := by
    intro K hK
    obtain ⟨y1, hy1, rfl⟩ := Finset.mem_image.mp hK
    calc (S.filter fun y => J y = J y1).card
        ≤ ((Finset.univ : Finset (Units.torsion E)).image
            (fun ζ : Units.torsion E => ((ζ : (𝓞 E)ˣ) : 𝓞 E) * y1)).card := by
          apply Finset.card_le_card
          intro y hy
          rw [Finset.mem_filter] at hy
          obtain ⟨hyS, hyJ⟩ := hy
          have hsp : Ideal.span {y1} = Ideal.span {y} := by rw [hJ y hyS, hJ y1 hy1, hyJ]
          obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hsp
          have hy1m := (hS y1 hy1).2
          have hym := (hS y hyS).2
          rw [← hu, map_mul] at hym
          have huu : (u : 𝓞 E) * cO E (u : 𝓞 E) = 1 := by
            apply mul_left_cancel₀ hm
            calc m * ((u : 𝓞 E) * cO E (u : 𝓞 E))
                = y1 * (u : 𝓞 E) * (cO E y1 * cO E (u : 𝓞 E)) := by
                  rw [← hy1m]; ring
              _ = m * 1 := by rw [hym, mul_one]
          have htor : u ∈ Units.torsion E := by
            apply mem_torsion_of_mul_conj
            have h := congrArg (fun z : 𝓞 E => (z : E)) huu
            simpa [cO_coe] using h
          rw [Finset.mem_image]
          exact ⟨(⟨u, htor⟩ : Units.torsion E), Finset.mem_univ _, by
            show (u : 𝓞 E) * y1 = y
            rw [mul_comm]; exact hu⟩
      _ ≤ Fintype.card (Units.torsion E) := by
          rw [← Finset.card_univ]; exact Finset.card_image_le
  have hcard : S.card ≤ Fintype.card (Units.torsion E) * (S.image J).card :=
    Finset.card_le_mul_card_image S _ hT
  have htors : Fintype.card (Units.torsion E) ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
    have h := torsionOrder_le E
    first
    | exact h
    | (rw [← Nat.card_eq_fintype_card]; exact h)
    | (rw [← Nat.card_eq_fintype_card]; unfold Units.torsionOrder at h; exact h)
    | (simpa [Units.torsionOrder, Nat.card_eq_fintype_card] using h)
  have hS' : S.card ≤ 2 * (Module.finrank ℚ E) ^ 2 * Ideal.absNorm M :=
    hcard.trans (Nat.mul_le_mul htors hcardJ)
  calc S.card * Ideal.absNorm I ^ 2
      ≤ 2 * (Module.finrank ℚ E) ^ 2 * Ideal.absNorm M * Ideal.absNorm I ^ 2 :=
        Nat.mul_le_mul hS' le_rfl
    _ = 2 * (Module.finrank ℚ E) ^ 2 * (Algebra.norm ℤ m).natAbs := by rw [hNm]; ring

end Formalism.L2.SG.NGCut.TorsionTotientBound
end
end

noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

theorem card_mul_conj_eq_le_of_fractionalIdeal (E : Type) [Field E] [NumberField E] [IsCMField E]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (m : E) (hJ : J ≠ 0) (hm : m ≠ 0)
    (S : Finset E) (hS : ∀ x ∈ S, x ∈ J ∧ x * IsCMField.complexConj E x = m) :
    (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤
      2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, a = (J.den : 𝓞 E) := ⟨_, rfl⟩
  have hcoe : ∀ y : 𝓞 E, algebraMap (𝓞 E) E y = (y : E) := fun _ => rfl
  have ha0 : algebraMap (𝓞 E) E a ≠ 0 := by
    rw [ha]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors J.den.2
  have hmem : ∀ x ∈ S, ∃ y ∈ J.num, algebraMap (𝓞 E) E y = algebraMap (𝓞 E) E a * x := by
    intro x hx
    have h1 : J.den • x ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J.num := by
      rw [← J.den_mul_self_eq_num]
      exact Submodule.smul_mem_pointwise_smul x _ _ (hS x hx).1
    obtain ⟨y, hy, hy'⟩ := Submodule.mem_map.1 h1
    refine ⟨y, hy, ?_⟩
    rw [ha]
    simpa [Algebra.smul_def, Submonoid.smul_def] using hy'
  choose! g hgI hg using hmem
  have hginj : Set.InjOn g S := by
    intro x hx y hy hxy
    have h := (hg x hx).symm.trans ((congrArg (algebraMap (𝓞 E) E) hxy).trans (hg y hy))
    exact mul_left_cancel₀ ha0 h
  have hTcard : (S.image g).card = S.card := Finset.card_image_of_injOn hginj
  have hgm : ∀ x ∈ S, algebraMap (𝓞 E) E (g x * cO E (g x)) =
      algebraMap (𝓞 E) E a * IsCMField.complexConj E (algebraMap (𝓞 E) E a) * m := by
    intro x hx
    rw [map_mul, hcoe (cO E (g x)), cO_coe, ← hcoe, hg x hx, map_mul, ← (hS x hx).2]
    ring
  have hT : ∀ y ∈ S.image g, y ∈ J.num ∧ y * cO E y = g x0 * cO E (g x0) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    refine ⟨hgI x hx, ?_⟩
    apply IsFractionRing.injective (𝓞 E) E
    rw [hgm x hx, hgm x0 hx0]
  have hnum : J.num ≠ ⊥ := by
    intro h
    apply hJ
    rw [← FractionalIdeal.num_eq_zero_iff]
    exact h
  have hc0 : IsCMField.complexConj E (algebraMap (𝓞 E) E a) ≠ 0 :=
    (map_ne_zero_iff _ (IsCMField.complexConj E).injective).2 ha0
  have hm'0 : g x0 * cO E (g x0) ≠ 0 := by
    intro h
    have h2 := hgm x0 hx0
    rw [h, map_zero] at h2
    exact (mul_ne_zero (mul_ne_zero ha0 hc0) hm) h2.symm
  have key := count_int J.num hnum (g x0 * cO E (g x0)) hm'0 (S.image g) hT
  have key' : ((((S.image g).card * Ideal.absNorm J.num ^ 2 : ℕ)) : ℝ) ≤
      ((2 * Module.finrank ℚ E ^ 2 * (Algebra.norm ℤ (g x0 * cO E (g x0))).natAbs : ℕ) : ℝ) := by
    exact_mod_cast key
  push_cast [Nat.cast_natAbs, Int.cast_abs] at key'
  rw [hTcard] at key'
  have hconj : ∀ y : E, Algebra.norm ℚ (IsCMField.complexConj E y) = Algebra.norm ℚ y := by
    intro y
    exact Algebra.norm_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) y
  have hNaQ : ((Algebra.norm ℤ a : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 E) E a) :=
    Algebra.coe_norm_int a
  have hNa0 : ((Algebra.norm ℤ a : ℤ) : ℝ) ≠ 0 := by
    have h : Algebra.norm ℚ (algebraMap (𝓞 E) E a) ≠ 0 := Algebra.norm_ne_zero_iff.2 ha0
    rw [← hNaQ] at h
    exact_mod_cast h
  have hNm' : ((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℝ) =
      ((Algebra.norm ℤ a : ℤ) : ℝ) ^ 2 * ((Algebra.norm ℚ m : ℚ) : ℝ) := by
    have h : ((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℚ) =
        Algebra.norm ℚ (algebraMap (𝓞 E) E a) ^ 2 * Algebra.norm ℚ m := by
      rw [Algebra.coe_norm_int, ← hcoe, hgm x0 hx0, map_mul (Algebra.norm ℚ), map_mul (Algebra.norm ℚ),
        hconj]
      ring
    have h3 : ((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℝ) =
        (((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℚ) : ℝ) := by norm_cast
    rw [h3, h, ← hNaQ]
    push_cast
    ring
  have hJn : ((FractionalIdeal.absNorm J : ℚ) : ℝ) =
      ((Ideal.absNorm J.num : ℕ) : ℝ) / |((Algebra.norm ℤ a : ℤ) : ℝ)| := by
    rw [FractionalIdeal.absNorm_eq, ha]
    push_cast
    rfl
  have hpos : (0 : ℝ) < ((Algebra.norm ℤ a : ℤ) : ℝ) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hNa0))
  rw [hJn, div_pow, sq_abs, mul_div_assoc', div_le_iff₀ hpos]
  calc (S.card : ℝ) * ((Ideal.absNorm J.num : ℕ) : ℝ) ^ 2
      ≤ 2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℤ (g x0 * cO E (g x0)) : ℤ) : ℝ)| := key'
    _ = 2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| *
        ((Algebra.norm ℤ a : ℤ) : ℝ) ^ 2 := by
      rw [hNm', abs_mul, abs_of_nonneg (sq_nonneg _)]
      ring

end Formalism.L2.SG.NGCut.TorsionTotientBound
