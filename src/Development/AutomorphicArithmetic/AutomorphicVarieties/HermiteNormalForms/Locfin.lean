module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.locfin :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N → ∀ B : ℝ,
    ∃ S : Set (Lat L N), S.Finite ∧ ∀ᶠ k in nhds h, ∀ y ∉ S, B < q k y := by
  intro L _ _ N h hh B
  obtain ⟨c, hc, hev⟩ := lowbd L N h hh
  obtain ⟨R, hR⟩ := exists_nat_gt (max (B / c) 1)
  have hR1 : (1 : ℝ) < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRB : B / c < R := lt_of_le_of_lt (le_max_left _ _) hR
  set T := {a : 𝓞 L | ∀ w : InfinitePlace L, ‖embO w a‖ ≤ (R : ℝ)} with hT
  refine ⟨Set.pi Set.univ (fun _ => T), Set.Finite.pi (fun _ => (cntconj L R).1), ?_⟩
  filter_upwards [hev] with k hk
  intro y hy
  have hy' : ∃ a w, (R : ℝ) < ‖embO w (y a)‖ := by
    by_contra hne
    push_neg at hne
    exact hy (fun a _ w => hne a w)
  obtain ⟨a, w, hlt⟩ := hy'
  have hle : ‖embO w (y a)‖ ≤ ‖toR y‖ :=
    (norm_le_pi_norm (toR y w) a).trans (norm_le_pi_norm (toR y) w)
  have hzR : (R : ℝ) < ‖toR y‖ := hlt.trans_le hle
  have hz1 : (1 : ℝ) ≤ ‖toR y‖ := hR1.le.trans hzR.le
  have hsq : ‖toR y‖ ≤ ‖toR y‖ ^ 2 := by nlinarith
  have hB : B < c * ‖toR y‖ := by
    rw [div_lt_iff₀ hc] at hRB
    nlinarith
  exact lt_of_lt_of_le (hB.trans_le (mul_le_mul_of_nonneg_left hsq hc.le)) (hk (toR y))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnfone
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnfeq
open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.hnfeq :
    ∀ (R : Type) [CommRing R] [IsDomain R] (N : ℕ) (r : R), r ≠ 0 → ∀ A A' B B' X : Matrix (Fin N) (Fin N) R,
    A * B = r • (1 : Matrix (Fin N) (Fin N) R) → B * A = r • (1 : Matrix (Fin N) (Fin N) R) →
    A' * B' = r • (1 : Matrix (Fin N) (Fin N) R) → B' * A' = r • (1 : Matrix (Fin N) (Fin N) R) →
    B - B' = r • X → ∃ g : GL (Fin N) R, (g : Matrix (Fin N) (Fin N) R) * A = A' := by
  intro R _ _ N r hr A A' B B' X hAB hBA hAB' hBA' hX
  have canc : ∀ P Q : Matrix (Fin N) (Fin N) R, r • P = r • Q → P = Q := by
    intro P Q h
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hr this
  have hg : r • (1 + A' * X) = A' * B := by
    rw [smul_add, ← Matrix.mul_smul, ← hX, Matrix.mul_sub, hAB']; abel
  have hh : r • (1 - A * X) = A * B' := by
    rw [smul_sub, ← Matrix.mul_smul, ← hX, Matrix.mul_sub, hAB]; abel
  have h1 : (1 + A' * X) * (1 - A * X) = 1 := by
    apply canc
    apply canc
    calc r • r • ((1 + A' * X) * (1 - A * X)) = (r • (1 + A' * X)) * (r • (1 - A * X)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = A' * (B * A) * B' := by rw [hg, hh]; simp only [Matrix.mul_assoc]
      _ = r • r • (1 : Matrix (Fin N) (Fin N) R) := by
          rw [hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAB']
  have h2 : (1 - A * X) * (1 + A' * X) = 1 := by
    apply canc
    apply canc
    calc r • r • ((1 - A * X) * (1 + A' * X)) = (r • (1 - A * X)) * (r • (1 + A' * X)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = A * (B' * A') * B := by rw [hg, hh]; simp only [Matrix.mul_assoc]
      _ = r • r • (1 : Matrix (Fin N) (Fin N) R) := by
          rw [hBA', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAB]
  refine ⟨⟨1 + A' * X, 1 - A * X, h1, h2⟩, ?_⟩
  apply canc
  change r • ((1 + A' * X) * A) = r • A'
  rw [← Matrix.smul_mul, hg, Matrix.mul_assoc, hBA, Matrix.mul_smul, Matrix.mul_one]
end

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.hnfone :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (I : ℕ), 0 < I →
    ∃ S : Finset (Matrix (Fin N) (Fin N) (𝓞 L)), S.card ≤ I ^ (dd L N * N) ∧ ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → nrmDet A = I →
      ∃ g : Gm L N, (g : Matrix (Fin N) (Fin N) (𝓞 L)) * A ∈ S := by
  classical
  intro L _ _ N I hI
  have hr0 : (I : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hI.ne'
  have hcardQ : Nat.card (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) = I ^ Module.finrank ℚ L := by
    have h1 := Ideal.absNorm_span_singleton (I : 𝓞 L)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    rw [h1, ← map_natCast (algebraMap ℤ (𝓞 L)) I, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank]
    simp
  haveI : Finite (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact pow_ne_zero _ hI.ne')
  letI : Fintype (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) := Fintype.ofFinite _
  have hB : ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ nrmDet A = I →
      ∃ B, A * B = (I : 𝓞 L) • 1 ∧ B * A = (I : 𝓞 L) • 1 := by
    intro A hA
    obtain ⟨_, B, h1, h2⟩ := scinv L N A hA.1
    rw [hA.2] at h1 h2
    exact ⟨B, h1, h2⟩
  let key : Matrix (Fin N) (Fin N) (𝓞 L) → Matrix (Fin N) (Fin N) (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) :=
    fun A => if h : A.det ≠ 0 ∧ nrmDet A = I then
      (Classical.choose (hB A h)).map (Ideal.Quotient.mk _) else 0
  let rep : Matrix (Fin N) (Fin N) (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) → Matrix (Fin N) (Fin N) (𝓞 L) :=
    fun k => if h : ∃ A, (A.det ≠ 0 ∧ nrmDet A = I) ∧ key A = k then Classical.choose h else 0
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ]
    change Fintype.card (Fin N → Fin N → 𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) = _
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcardQ,
      dd, ← pow_mul, ← pow_mul, mul_assoc]
  · intro A hdet hnrm
    have hA : A.det ≠ 0 ∧ nrmDet A = I := ⟨hdet, hnrm⟩
    have hex : ∃ A', (A'.det ≠ 0 ∧ nrmDet A' = I) ∧ key A' = key A := ⟨A, hA, rfl⟩
    have hrep : rep (key A) = Classical.choose hex := dif_pos hex
    obtain ⟨hA'P, hA'k⟩ := Classical.choose_spec hex
    obtain ⟨h1, h2⟩ := Classical.choose_spec (hB A hA)
    obtain ⟨h1', h2'⟩ := Classical.choose_spec (hB _ hA'P)
    have hkk : (Classical.choose (hB _ hA'P)).map (Ideal.Quotient.mk (Ideal.span {(I : 𝓞 L)})) =
        (Classical.choose (hB A hA)).map (Ideal.Quotient.mk _) := by
      have keyeq : ∀ (M : Matrix (Fin N) (Fin N) (𝓞 L)) (h : M.det ≠ 0 ∧ nrmDet M = I),
          key M = (Classical.choose (hB M h)).map (Ideal.Quotient.mk _) := fun M h => dif_pos h
      exact (keyeq _ hA'P).symm.trans (hA'k.trans (keyeq A hA))
    have hent : ∀ i j, ∃ x, Classical.choose (hB A hA) i j - Classical.choose (hB _ hA'P) i j =
        (I : 𝓞 L) * x := by
      intro i j
      have h := congrFun (congrFun hkk i) j
      simp only [Matrix.map_apply] at h
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      exact ⟨-c, by rw [mul_neg, ← hc, neg_sub]⟩
    choose X hX using hent
    obtain ⟨g, hg⟩ := hnfeq (𝓞 L) N (I : 𝓞 L) hr0 A (Classical.choose hex) _ _ (Matrix.of X)
      h1 h2 h1' h2' (by ext i j; simp [hX])
    refine ⟨g, ?_⟩
    rw [hg, Finset.mem_image]
    exact ⟨key A, Finset.mem_univ _, hrep⟩
end

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.hnf :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (J : ℕ),
    ∃ S : Finset (Matrix (Fin N) (Fin N) (𝓞 L)), S.card ≤ J ^ (1 + dd L N * N) ∧ ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → nrmDet A ≤ J →
      ∃ g : Gm L N, (g : Matrix (Fin N) (Fin N) (𝓞 L)) * A ∈ S := by
  intro L _ _ N J
  classical
  have hpos : ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → 0 < nrmDet A := by
    intro A hA
    unfold nrmDet
    exact Int.natAbs_pos.mpr ((Algebra.norm_ne_zero_iff (R := ℤ)).mpr hA)
  have hex : ∀ I : ℕ, ∃ S : Finset (Matrix (Fin N) (Fin N) (𝓞 L)), S.card ≤ I ^ (dd L N * N) ∧
      ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → nrmDet A = I →
        ∃ g : Gm L N, (g : Matrix (Fin N) (Fin N) (𝓞 L)) * A ∈ S := by
    intro I
    rcases Nat.eq_zero_or_pos I with rfl | hI
    · refine ⟨∅, by simp, ?_⟩
      intro A hA hn
      exact absurd hn (hpos A hA).ne'
    · exact hnfone L N I hI
  choose S hScard hS using hex
  refine ⟨(Finset.Icc 1 J).biUnion S, ?_, ?_⟩
  · calc ((Finset.Icc 1 J).biUnion S).card
        ≤ ∑ I ∈ Finset.Icc 1 J, (S I).card := Finset.card_biUnion_le
      _ ≤ ∑ I ∈ Finset.Icc 1 J, J ^ (dd L N * N) := by
        apply Finset.sum_le_sum
        intro I hI
        exact (hScard I).trans (Nat.pow_le_pow_left (Finset.mem_Icc.mp hI).2 _)
      _ = J ^ (1 + dd L N * N) := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, pow_add, pow_one]
        simp
  · intro A hA hJ
    obtain ⟨g, hg⟩ := hS (nrmDet A) A hA rfl
    refine ⟨g, Finset.mem_biUnion.mpr ⟨nrmDet A, ?_, hg⟩⟩
    exact Finset.mem_Icc.mpr ⟨hpos A hA, hJ⟩
end
