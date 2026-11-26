module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
public import Formalism.UnipotentAdelicQuotients.ThmBInHecke

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegral
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem gramLB_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    ∃ U : Matrix n n ℝ, U * Uᴴ = 1 ∧
      A + t • (1 : Matrix n n ℝ) = U * diagonal (fun i => hA.eigenvalues i + t) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℝ), Unitary.coe_mul_star_self _, ?_⟩
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) * star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  have hD : diagonal (fun i => hA.eigenvalues i + t) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) + t • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, ← star_eq_conjTranspose, hU]

theorem gramLB_one_le_det {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℝ}
    (hR : R.PosSemidef) : 1 ≤ (R + 1).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hR.1 1
  rw [one_smul] at hEq
  have hdet : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
  rw [hEq, det_mul, det_mul, det_diagonal]
  have e : U.det * (∏ i, (hR.1.eigenvalues i + 1)) * Uᴴ.det = ∏ i, (hR.1.eigenvalues i + 1) := by
    linear_combination (∏ i, (hR.1.eigenvalues i + 1)) * hdet
  rw [e]
  calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
    _ ≤ ∏ i, (hR.1.eigenvalues i + 1) :=
      Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => by linarith [hR.eigenvalues_nonneg i]

theorem gramLB_exists_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosDef) : ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ (A - k • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min hA.1.eigenvalues
      exact ⟨_, hA.eigenvalues_pos i0, hi0⟩
  refine ⟨min 1 m, lt_min one_pos hm0, min_le_left _ _, ?_⟩
  obtain ⟨U, -, hEq⟩ := gramLB_shift hA.1 (-(min 1 m))
  rw [sub_eq_add_neg, ← neg_smul, hEq]
  exact (posSemidef_diagonal_iff.2 fun i => by linarith [hm i, min_le_right 1 m]).mul_mul_conjTranspose_same U

open scoped MatrixOrder in
theorem gramLB_det_mono {n : Type} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℝ}
    (hP : P.PosDef) (hQ : Q.PosSemidef) : P.det ≤ (P + Q).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hP.1 0
  simp only [zero_smul, add_zero] at hEq
  have hd : ∀ i, 0 < hP.1.eigenvalues i := hP.eigenvalues_pos
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  let s : n → ℝ := fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹
  let B : Matrix n n ℝ := U * diagonal s
  have hBt : Bᴴ = diagonal s * Uᴴ := by
    simp [B]
  have hBPB : Bᴴ * P * B = 1 := by
    rw [hBt, hEq]
    simp only [B, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
      diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hs : Real.sqrt (hP.1.eigenvalues i) * Real.sqrt (hP.1.eigenvalues i) = hP.1.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have hs0 : Real.sqrt (hP.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s]
    field_simp
    try nlinarith [hs, Real.sq_sqrt (hd i).le]
  have hsum : Bᴴ * (P + Q) * B = 1 + Bᴴ * Q * B := by
    rw [Matrix.mul_add, Matrix.add_mul, hBPB]
  have h1 : Bᴴ.det * B.det * P.det = 1 := by
    have e := congrArg det hBPB
    rw [det_mul, det_mul, det_one] at e
    linear_combination e
  have h2 : Bᴴ.det * B.det * (P + Q).det = (1 + Bᴴ * Q * B).det := by
    rw [← hsum, det_mul (Bᴴ * (P + Q)) B, det_mul Bᴴ (P + Q)]
    ring
  have h3 : 1 ≤ (1 + Bᴴ * Q * B).det := by
    rw [add_comm]
    exact gramLB_one_le_det (hQ.conjTranspose_mul_mul_same B)
  have hc : 0 < Bᴴ.det * B.det := by
    have := hP.det_pos
    by_contra hneg
    nlinarith [not_lt.mp hneg]
  exact le_of_mul_le_mul_left (by linarith) hc

theorem gramLB_posDef {n : Type} [Fintype n] [DecidableEq n] {g : Matrix n n ℝ}
    (hg : g.det ≠ 0) : (gᵀ * g).PosDef := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact PosDef.conjTranspose_mul_self g
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (Ne.isUnit hg)))

theorem gram_leading_minor_lower_bound :
    ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ γ : Matrix (Fin N) (Fin N) ℤ, γ.det ≠ 0 → ∀ (j : ℕ) (h : j ≤ N), c ≤ (((g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  intro N g hg
  obtain ⟨k, hk0, hk1, hkQ⟩ := gramLB_exists_shift (gramLB_posDef hg)
  refine ⟨k ^ N, pow_pos hk0 N, fun γ hγ j hj => ?_⟩
  set Γ : Matrix (Fin N) (Fin N) ℝ := γ.map (Int.cast : ℤ → ℝ) with hΓ
  set E : Fin j → Fin N := Fin.castLE hj with hE
  let C : Matrix (Fin N) (Fin j) ℝ := Γ.submatrix id E
  let Cz : Matrix (Fin N) (Fin j) ℤ := γ.submatrix id E
  have hGram : ((g * Γ)ᵀ * (g * Γ)).submatrix E E = Cᵀ * (gᵀ * g) * C := by
    have e1 : (g * Γ)ᵀ * (g * Γ) = Γᵀ * (gᵀ * g) * Γ := by
      rw [transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.submatrix_mul _ _ E id E Function.bijective_id,
      Matrix.submatrix_mul _ _ E id id Function.bijective_id, submatrix_id_id, transpose_submatrix]
  have hsplit : Cᵀ * (gᵀ * g) * C = k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    abel
  have hΓdet : Γ.det ≠ 0 := by
    have e := (Int.castRingHom ℝ).map_det γ
    rw [show Γ = (Int.castRingHom ℝ).mapMatrix γ from rfl, ← e]
    simpa using hγ
  have hCinj : Function.Injective C.mulVec := by
    have hC : C = Γ * (1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E := by
      rw [← Matrix.submatrix_id_id Γ, ← Matrix.submatrix_mul _ _ id id E Function.bijective_id,
        Matrix.mul_one]
    have hI : Function.Injective ((1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E).mulVec := by
      intro x y hxy
      funext a
      have hEinj : Function.Injective E := Fin.castLE_injective hj
      have e := congrFun hxy (E a)
      simpa [mulVec, dotProduct, Matrix.one_apply, hEinj.eq_iff] using e
    rw [hC]
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact hI (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det Γ).2 (Ne.isUnit hΓdet)) hxy)
  have hCC : (Cᵀ * C).PosDef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact PosDef.conjTranspose_mul_self C hCinj
  have hQ' : (Cᵀ * (gᵀ * g - k • 1) * C).PosSemidef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hkQ.conjTranspose_mul_mul_same C
  have hCz : Cᵀ * C = (Int.castRingHom ℝ).mapMatrix (Czᵀ * Cz) := by
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
    rfl
  have hdet1 : 1 ≤ (Cᵀ * C).det := by
    have hpos := hCC.det_pos
    rw [hCz, ← RingHom.map_det, eq_intCast] at hpos
    rw [hCz, ← RingHom.map_det, eq_intCast]
    have hz : 0 < (Czᵀ * Cz).det := by exact_mod_cast hpos
    have hz1 : (1 : ℤ) ≤ (Czᵀ * Cz).det := hz
    exact_mod_cast hz1
  calc k ^ N ≤ k ^ j := pow_le_pow_of_le_one hk0.le hk1 hj
    _ ≤ k ^ j * (Cᵀ * C).det := le_mul_of_one_le_right (pow_nonneg hk0.le _) hdet1
    _ = (k • (Cᵀ * C)).det := by rw [det_smul, Fintype.card_fin]
    _ ≤ (k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C).det := gramLB_det_mono (hCC.smul hk0) hQ'
    _ = _ := by rw [← hsplit, ← hGram]

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegralStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_leading_minor_lower_bound_integral : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ γ : Matrix (Fin N) (Fin N) ℤ, γ.det ≠ 0 → ∀ (j : ℕ) (h : j ≤ N), c ≤ (((g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  first | exact @GlobalTheory.ClassFin.gram_leading_minor_lower_bound | exact GlobalTheory.ClassFin.gram_leading_minor_lower_bound | (intros; apply GlobalTheory.ClassFin.gram_leading_minor_lower_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmConjugationOnPrimesProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPrimeInvolutionOfRingInvolution
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem exists_primeInvolution_of_ringInvolution {R : Type} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] (s : R ≃+* R) (hs : ∀ x, s (s x) = x) :
    ∃ c : HeightOneSpectrum R ≃ HeightOneSpectrum R, (∀ P, c (c P) = P) ∧
      (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2) := by
  have hm : ∀ (I : Ideal R) (x : R), s x ∈ I.map s ↔ x ∈ I := by
    intro I x
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, h⟩
      rwa [← s.injective h]
    · intro h
      exact ⟨x, h, rfl⟩
  let f : HeightOneSpectrum R → HeightOneSpectrum R := fun P =>
    { asIdeal := P.asIdeal.map s
      isPrime := by
        have := P.isPrime
        exact Ideal.map_isPrime_of_equiv s
      ne_bot := by
        intro h
        apply P.ne_bot
        rw [eq_bot_iff]
        intro x hx
        have h1 := (hm _ x).2 hx
        rw [h, Ideal.mem_bot] at h1
        rw [Ideal.mem_bot]
        exact s.injective (by simpa using h1) }
  have hf : Function.Involutive f := by
    intro P
    ext x
    show x ∈ (P.asIdeal.map s).map s ↔ _
    rw [← hm P.asIdeal x, ← hm _ (s x), hs]
  refine ⟨hf.toPerm f, hf, ?_, ?_, ?_⟩
  · intro P
    show Ideal.absNorm (P.asIdeal.map s) = _
    rw [Ideal.absNorm_of_ne_bot (f P).ne_bot, Ideal.absNorm_of_ne_bot P.ne_bot,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (P.asIdeal.map s) s rfl).toEquiv).symm
  · intro P x
    exact hm _ x
  · intro P x
    show s x ∈ (P.asIdeal.map s) ^ 2 ↔ _
    rw [← Ideal.map_pow, hm]

theorem cmConjugation_on_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → (∀ x, σ (σ x) = x) ∧ ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧ (∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ ∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hσ, hσ, star_star]
  have hfix : ∀ x, σ x = x → ∃ a : F, algebraMap F E a = x := by
    intro x hx
    have := Subalgebra.isSimpleOrder_of_finrank h2
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have hx' : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
      rw [h] at hx'
      exact hx'
    · exfalso
      apply IsTotallyComplex.complexEmbedding_not_isReal τ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      have hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      have hy' : σ y = y := hy
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := hσ τ y
      rw [hy'] at this
      exact this.symm
  let e : E ≃+* E :=
    { toFun := σ, invFun := σ, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul σ, map_add' := map_add σ }
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv e
  have hs : ∀ x : 𝓞 E, ((s x : 𝓞 E) : E) = σ x := fun x => rfl
  have hss : ∀ x, s (s x) = x := by
    intro x
    apply RingOfIntegers.ext
    rw [hs, hs, hinv]
  have hsF : ∀ a : 𝓞 F, s (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hs]
    exact σ.commutes (a : F)
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_primeInvolution_of_ringInvolution s hss
  refine ⟨hinv, c, hc1, hc2, fun x => ⟨s x, hs x⟩, ?_, ?_⟩
  · intro P x y hy
    have : y = s x := RingOfIntegers.ext (by rw [hy, hs])
    subst this
    exact ⟨hc3 P x, hc4 P x⟩
  · intro P Q
    have hu : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 F),
        a ∈ (P.under (𝓞 F)).asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := fun P a => Iff.rfl
    constructor
    · intro h
      by_contra hne
      push Not at hne
      have hnot : ¬ ((Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (c P).asIdeal) := by
        rw [Ideal.subset_union]
        rintro (h' | h')
        · exact hne.1 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h'))
        · exact hne.2 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (c P).isPrime.ne_top h'))
      rw [Set.not_subset] at hnot
      obtain ⟨x, hxQ, hx⟩ := hnot
      simp only [Set.mem_union, SetLike.mem_coe, not_or] at hx hxQ
      obtain ⟨a, ha⟩ := hfix ((x * s x : 𝓞 E) : E) (by
        rw [← hs, map_mul, hss, mul_comm])
      have hai : IsIntegral ℤ a := by
        have h1 : IsIntegral ℤ (algebraMap F E a) := by
          rw [ha]; exact RingOfIntegers.isIntegral_coe _
        exact (isIntegral_algebraMap_iff ).1 h1
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = x * s x :=
        ⟨⟨a, hai⟩, RingOfIntegers.ext ha⟩
      have h1 : b ∈ (Q.under (𝓞 F)).asIdeal := by
        rw [hu, hb]; exact Ideal.mul_mem_right _ _ hxQ
      rw [← h, hu, hb] at h1
      rcases P.isPrime.mem_or_mem h1 with h3 | h3
      · exact hx.1 h3
      · apply hx.2
        have := (hc3 P _).2 h3
        rwa [hss] at this
    · rintro (rfl | rfl)
      · rfl
      · ext a
        rw [hu, hu, ← hc3 P, hsF]

end GlobalTheory
end

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

section ConjIdem

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem conjIdem_sigR_tmul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) (x : E) :
    sigR R σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := rfl

theorem conjIdem_sigR_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => rw [conjIdem_sigR_tmul, conjIdem_sigR_tmul, h]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem conjIdem_sigR_algebraMap (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) a) = algebraMap R (R ⊗[F] E) a := by
  show sigR R σ (a ⊗ₜ[F] 1) = a ⊗ₜ[F] 1
  rw [conjIdem_sigR_tmul, map_one]

theorem conjIdem_sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR (F := F) R x) = inclR (F := F) R (σ x) := rfl

variable [NumberField F] [NumberField E]

omit [NumberField E] in
theorem conjIdem_finPart_cA (σ : E →ₐ[F] E) (y : AE F E) :
    finPart F E (cA σ y) = sigR (Af F) σ (finPart F E y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

omit [NumberField E] in
theorem conjIdem_sigR_mem_intAE (σ : E →ₐ[F] E) (h : ∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x)
    (y : Af F ⊗[F] E) (hy : y ∈ intAE F E) : sigR (Af F) σ y ∈ intAE F E := by
  unfold intAE at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    obtain ⟨z, hz⟩ := h x
    exact AddSubgroup.subset_closure ⟨a, ha, z, by rw [conjIdem_sigR_tmul, hz]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end ConjIdem

theorem cmConjugation_on_primes_adeles_idempotents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, normP (c P) = normP P) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ (∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P) ∧ (∀ y, cA σ (cA σ y) = y) ∧ (∀ y : AE F E, finPart F E (cA σ y) ∈ intAE F E ↔ finPart F E y ∈ intAE F E) ∧ ∀ P e f, IsPrimeIdem σ P e f → IsPrimeIdem σ (c P) (cA σ e) f := by
  intro F E _ _ _ _ _ σ hCM
  obtain ⟨h1, h2, h3, h4⟩ := hCM
  obtain ⟨hinv, c, hc1, hc2, hint, hc3, hc4⟩ := cmConjugation_on_primes F E σ h1 h2 h3 h4
  have hcc : ∀ y : AE F E, cA σ (cA σ y) = y := conjIdem_sigR_sigR (AF F) σ hinv
  have hfin : ∀ y : AE F E, finPart F E (cA σ y) ∈ intAE F E ↔ finPart F E y ∈ intAE F E := by
    have key : ∀ y : AE F E, finPart F E y ∈ intAE F E → finPart F E (cA σ y) ∈ intAE F E := by
      intro y hy
      rw [conjIdem_finPart_cA]
      exact conjIdem_sigR_mem_intAE σ hint _ hy
    intro y
    exact ⟨fun h => by have := key _ h; rwa [hcc] at this, key y⟩
  have hcrit : ∀ (P : HeightOneSpectrum (𝓞 E)) (e : AE F E),
      (∀ x : 𝓞 E, x ≠ 0 →
        (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)) →
      ∀ x : 𝓞 E, x ≠ 0 →
        (x ∈ (c P).asIdeal ↔ finPart F E (cA σ e * incA F E ((x : E)⁻¹)) ∉ intAE F E) := by
    intro P e h x hx
    obtain ⟨z, hz⟩ := hint x
    have hxz : (x : E) = σ z := by rw [hz, hinv]
    have hz0 : z ≠ 0 := by
      rintro rfl
      apply hx
      apply RingOfIntegers.ext
      rw [hxz]
      simp
    have hm : cA σ e * incA F E ((x : E)⁻¹) = cA σ (e * incA F E ((z : E)⁻¹)) := by
      rw [map_mul, conjIdem_sigR_inclR, map_inv₀ σ, hxz]
    rw [(hc3 P z x hxz).1, h z hz0, hm, hfin]
  refine ⟨c, hc1, hc2, hc3, hc4, hcc, hfin, ?_⟩
  intro P e f h
  rcases h with ⟨⟨⟨he1, he2, v, ε, hv, he3⟩, hP⟩, hf⟩ | ⟨hf, ⟨v, ε, hv, he⟩, hP⟩
  · left
    refine ⟨⟨⟨?_, ?_, v, ε, hv, ?_⟩, hcrit P e hP⟩, ?_⟩
    · rw [← map_mul, he1]
    · rw [hcc, mul_comm, he2]
    · rw [hcc, add_comm, he3]
    · rw [hcc, add_comm, hf]
  · right
    have hce : cA σ e = e := by rw [he]; exact conjIdem_sigR_algebraMap _ σ ε
    exact ⟨by rw [hce, hf], ⟨v, ε, hv, by rw [hce, he]⟩, hcrit P e hP⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyTensorFormProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyTensorFormProperties
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_monomial_eq_prod_X {σ : Type} (n : ℕ) : ∀ d : σ →₀ ℕ, d.degree = n →
    ∃ a : Fin n → σ, (MvPolynomial.monomial d (1 : ℂ)) = ∏ k, MvPolynomial.X (a k) := by
  classical
  induction n with
  | zero =>
    intro d hd
    rw [Finsupp.degree_eq_zero_iff] at hd
    subst hd
    exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro d hd
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    have hle : Finsupp.single i 1 ≤ d := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr hi
    obtain ⟨d', rfl⟩ := exists_add_of_le hle
    have hd' : d'.degree = n := by
      rw [map_add (f := _), Finsupp.degree_single] at hd
      omega
    obtain ⟨a, ha⟩ := ih d' hd'
    refine ⟨Fin.cons i a, ?_⟩
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← ha, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC, map_add (f := _)] at *
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul] at *
    rw [hp]
    simp [ltr, Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem evC_ext {f f' : MvPolynomial (ι × ι) ℂ} (h : ∀ y, evC f y = evC f' y) : f = f' := by
  apply MvPolynomial.funext
  intro x
  exact h (Matrix.of fun i j => x (i, j))

theorem tpow_mul_complex (n : ℕ) (y z : Matrix ι ι ℂ) : tpow n (y * z) = tpow n y * tpow n z := by
  ext a b
  simp only [tpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib]

noncomputable def tensorForm (n : ℕ) (b : Fin n → ι) : ((Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ :=
  ∑ a : Fin n → ι, (LinearMap.proj a).smulRight (∏ k, MvPolynomial.X (a k, b k))

theorem tensorForm_apply (n : ℕ) (b : Fin n → ι) (l : (Fin n → ι) → ℂ) :
    tensorForm n b l = ∑ a : Fin n → ι, l a • ∏ k, MvPolynomial.X (a k, b k) := by
  simp [tensorForm, LinearMap.sum_apply]

theorem evC_tensorForm (n : ℕ) (b : Fin n → ι) (l : (Fin n → ι) → ℂ) (y : Matrix ι ι ℂ) :
    evC (tensorForm n b l) y = (l ᵥ* tpow n y) b := by
  rw [tensorForm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [evC, tpow, Matrix.vecMul, dotProduct, map_sum, map_prod]

theorem ltr_tensorForms : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ), evC (ltr g f) y = evC f (g * y)) ∧ (∀ (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ), IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f) ∧ (∀ (g : Matrix ι ι ℂ) (n : ℕ) (f : MvPolynomial (ι × ι) ℂ), f.IsHomogeneous n → (ltr g f).IsHomogeneous n) ∧ ∀ n : ℕ, ∃ p : (Fin n → ι) → ((Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ, (∀ b l (y : Matrix ι ι ℂ), evC (p b l) y = (l ᵥ* tpow n y) b) ∧ (∀ b l (g : Matrix ι ι ℂ), ltr g (p b l) = p b (l ᵥ* tpow n g)) ∧ ∀ f : MvPolynomial (ι × ι) ℂ, f.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, f = ∑ b, p b (l b) := by
  intro ι _ _
  refine ⟨evC_ltr, ?_, ?_, ?_⟩
  · intro Γ f
    constructor
    · intro h g hg
      exact evC_ext fun y => by rw [evC_ltr, h g hg]
    · intro h g hg y
      rw [← evC_ltr, h g hg]
  · intro g n f hf
    have := hf.aeval (S := ℂ) (n := 1)
      (fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * MvPolynomial.X (k, ij.2)) (fun ij =>
        MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
    rw [one_mul] at this
    exact this
  · intro n
    refine ⟨tensorForm n, evC_tensorForm n, ?_, ?_⟩
    · intro b l g
      apply evC_ext
      intro y
      rw [evC_ltr, evC_tensorForm, evC_tensorForm, tpow_mul_complex, Matrix.vecMul_vecMul]
    · intro f hf
      let Φ : ((Fin n → ι) → (Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ :=
        ∑ b, (tensorForm n b).comp (LinearMap.proj b)
      have hΦ : ∀ l, Φ l = ∑ b, tensorForm n b (l b) := by
        intro l
        simp [Φ, LinearMap.sum_apply]
      suffices h : f ∈ LinearMap.range Φ by
        obtain ⟨l, hl⟩ := h
        exact ⟨l, by rw [← hΦ, hl]⟩
      rw [f.as_sum]
      refine Submodule.sum_mem _ fun d hd => ?_
      have hdeg : d.degree = n := by
        by_contra h
        exact (MvPolynomial.mem_support_iff.mp hd) (hf.coeff_eq_zero h)
      obtain ⟨a, ha⟩ := exists_monomial_eq_prod_X n d hdeg
      have h1 : MvPolynomial.monomial d (f.coeff d) = f.coeff d • MvPolynomial.monomial d (1 : ℂ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [h1, ha]
      refine Submodule.smul_mem _ _ ⟨Pi.single (fun k => (a k).2) (Pi.single (fun k => (a k).1) 1), ?_⟩
      rw [hΦ, Finset.sum_eq_single (fun k => (a k).2)]
      · rw [Pi.single_eq_same, tensorForm_apply, Finset.sum_eq_single (fun k => (a k).1)]
        · simp
        · intro c _ hc
          simp [hc]
        · simp
      · intro c _ hc
        simp [hc]
      · simp

end GlobalTheory.ClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyTensorFormPropertiesStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftTranslateMatrixPoly_tensorForm_properties : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ), evC (ltr g f) y = evC f (g * y)) ∧ (∀ (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ), IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f) ∧ (∀ (g : Matrix ι ι ℂ) (n : ℕ) (f : MvPolynomial (ι × ι) ℂ), f.IsHomogeneous n → (ltr g f).IsHomogeneous n) ∧ ∀ n : ℕ, ∃ p : (Fin n → ι) → ((Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ, (∀ b l (y : Matrix ι ι ℂ), evC (p b l) y = (l ᵥ* tpow n y) b) ∧ (∀ b l (g : Matrix ι ι ℂ), ltr g (p b l) = p b (l ᵥ* tpow n g)) ∧ ∀ f : MvPolynomial (ι × ι) ℂ, f.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, f = ∑ b, p b (l b) := by
  first | exact @GlobalTheory.ClassFin.ltr_tensorForms | exact GlobalTheory.ClassFin.ltr_tensorForms | (intros; apply GlobalTheory.ClassFin.ltr_tensorForms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducible
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {V : Type} [AddCommGroup V] [Module ℂ V] in
private lemma projection_comm_of_mapsTo {p q : Submodule ℂ V} (h : IsCompl p q)
    (T : V →ₗ[ℂ] V) (hp : ∀ v ∈ p, T v ∈ p) (hq : ∀ v ∈ q, T v ∈ q) (v : V) :
    p.projection q h (T v) = T (p.projection q h v) := by
  have hv : v ∈ p ⊔ q := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have e1 := (Submodule.IsCompl.projection_eq_self_iff h a).mpr ha
  have e2 := (Submodule.IsCompl.projection_eq_self_iff h (T a)).mpr (hp a ha)
  have e3 := (Submodule.IsCompl.projection_apply_eq_zero_iff h).mpr hb
  have e4 := (Submodule.IsCompl.projection_apply_eq_zero_iff h).mpr (hq b hb)
  simp only [map_add (f := _), e1, e2, e3, e4, add_zero]

variable {V : Type} [AddCommGroup V] [Module ℂ V] in
private lemma sub_projection_mem' {p q : Submodule ℂ V} (h : IsCompl p q) (v : V) :
    v - p.projection q h v ∈ q := by
  rw [← Submodule.IsCompl.projection_apply_eq_zero_iff h, map_sub,
    (Submodule.IsCompl.projection_eq_self_iff h _).mpr
      (Submodule.IsCompl.projection_apply_mem h v), sub_self]


variable {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible (V : Type) [AddCommGroup V] [Module ℂ V]
    (S : Set (V →ₗ[ℂ] V)) :
    (∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, (s : V → V) v ∈ U) →
      ∃ U' : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U', (s : V → V) v ∈ U') ∧ IsCompl U U') →
    ∃ Rey : V →ₗ[ℂ] V,
      (∀ v : V, ∀ s ∈ S, (s : V → V) ((Rey : V → V) v) = (Rey : V → V) v) ∧
      (∀ v : V, (∀ s ∈ S, (s : V → V) v = v) → (Rey : V → V) v = v) ∧
      (∀ v : V, ∀ s ∈ S, (Rey : V → V) ((s : V → V) v) = (Rey : V → V) v) ∧
      (∀ v : V, v - (Rey : V → V) v ∈
        Submodule.span ℂ {x : V | ∃ s ∈ S, ∃ w : V, x = (s : V → V) w - w}) ∧
      (∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v : V, (T : V → V) ((s : V → V) v) = (s : V → V) ((T : V → V) v)) →
        ∀ v : V, (Rey : V → V) ((T : V → V) v) = (T : V → V) ((Rey : V → V) v)) ∧
      ∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, (s : V → V) v ∈ U) →
        ∀ v ∈ U, (Rey : V → V) v ∈ U := by
  intro hS
  let W : Submodule ℂ V := Submodule.span ℂ {x : V | ∃ s ∈ S, ∃ w : V, x = (s : V → V) w - w}
  have hWgen : ∀ s ∈ S, ∀ w, (s : V → V) w - w ∈ W := fun s hs w =>
    Submodule.subset_span ⟨s, hs, w, rfl⟩
  have hWT : ∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v ∈ W, T v ∈ W := by
    intro T hT v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, hs, w, rfl⟩ := hx
      rw [map_sub, hT s hs]
      exact hWgen s hs (T w)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact W.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact W.smul_mem a hx
  have hWS : ∀ s ∈ S, ∀ v ∈ W, (s : V → V) v ∈ W := by
    intro s hs v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s', hs', w, rfl⟩ := hx
      have e : s (s' w - w) = (s (s' w) - s' w) + (s' w - w) - (s w - w) := by
        rw [map_sub]
        abel
      rw [e]
      exact W.sub_mem (W.add_mem (hWgen s hs _) (hWgen s' hs' w)) (hWgen s hs w)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact W.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact W.smul_mem a hx
  let Fix : Submodule ℂ V :=
    { carrier := {x | ∀ s ∈ S, (s : V → V) x = x}
      add_mem' := fun ha hb s hs => by simp [map_add (f := _), ha s hs, hb s hs]
      zero_mem' := fun s _ => map_zero s
      smul_mem' := fun c x hx s hs => by simp [map_smul, hx s hs] }
  have hFixW : ∀ v ∈ Fix, v ∈ W → v = 0 := by
    intro v hvF hvW
    have hZS : ∀ s ∈ S, ∀ x ∈ Fix ⊓ W, (s : V → V) x ∈ Fix ⊓ W := by
      intro s hs x hx
      rw [hx.1 s hs]
      exact hx
    obtain ⟨Z', hZ'S, hZZ'⟩ := hS (Fix ⊓ W) hZS
    let Q := (Fix ⊓ W).projection Z' hZZ'
    have hQS : ∀ s ∈ S, ∀ x, Q (s x) = s (Q x) := fun s hs x =>
      projection_comm_of_mapsTo hZZ' s (hZS s hs) (hZ'S s hs) x
    have hQW : W ≤ LinearMap.ker Q := by
      rw [Submodule.span_le]
      rintro _ ⟨s, hs, w, rfl⟩
      have hmem := Submodule.IsCompl.projection_apply_mem hZZ' w
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hQS s hs, Q]
      rw [hmem.1 s hs, sub_self]
    have h1 : Q v = v := (Submodule.IsCompl.projection_eq_self_iff hZZ' v).mpr ⟨hvF, hvW⟩
    have h2 : Q v = 0 := hQW hvW
    rw [← h1, h2]
  obtain ⟨W', hW'S, hWW'⟩ := hS W hWS
  have hW'Fix : ∀ v ∈ W', v ∈ Fix := by
    intro v hv s hs
    have h1 : (s : V → V) v - v ∈ W := hWgen s hs v
    have h2 : (s : V → V) v - v ∈ W' := W'.sub_mem (hW'S s hs v hv) hv
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hWW'.disjoint _ h1 h2)
  let P := W'.projection W hWW'.symm
  have hPfix : ∀ v ∈ Fix, P v = v := by
    intro v hv
    have hd : v - P v ∈ Fix := Fix.sub_mem hv (hW'Fix _ (Submodule.IsCompl.projection_apply_mem _ v))
    exact (sub_eq_zero.mp (hFixW _ hd (sub_projection_mem' hWW'.symm v))).symm
  have hPT : ∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v, P (T v) = T (P v) := by
    intro T hT v
    refine projection_comm_of_mapsTo hWW'.symm T (fun x hx => ?_) (hWT T hT) v
    have hTx : T x ∈ Fix := fun s hs => by rw [← hT s hs, hW'Fix x hx s hs]
    rw [← hPfix _ hTx]
    exact Submodule.IsCompl.projection_apply_mem _ _
  refine ⟨P, fun v s hs => hW'Fix _ (Submodule.IsCompl.projection_apply_mem _ v) s hs,
    fun v hv => hPfix v hv, fun v s hs => ?_, fun v => sub_projection_mem' hWW'.symm v,
    hPT, fun U hU v hv => ?_⟩
  · have h0 : P ((s : V → V) v - v) = 0 :=
      (Submodule.IsCompl.projection_apply_eq_zero_iff _).mpr (hWgen s hs v)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · obtain ⟨U', hU'S, hUU'⟩ := hS U hU
    let Q := U.projection U' hUU'
    have hQ : ∀ s ∈ S, ∀ x, Q (s x) = s (Q x) := fun s hs x =>
      projection_comm_of_mapsTo hUU' s (hU s hs) (hU'S s hs) x
    have hQv : Q v = v := (Submodule.IsCompl.projection_eq_self_iff hUU' v).mpr hv
    have e := hPT Q hQ v
    rw [hQv] at e
    rw [e]
    exact Submodule.IsCompl.projection_apply_mem hUU' _

end GlobalTheory.ClassFin
end
