module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumSingularAndInvertible
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem matrixGaussSum_mul_unit (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type)
    [CommRing R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ) (a : Matrix (Fin r) (Fin r) k)
    (g : GL (Fin r) k) :
    (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
      ψ (Matrix.trace ((a * (g : Matrix (Fin r) (Fin r) k)) * (x : Matrix (Fin r) (Fin r) k)))) =
    ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
        ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))) := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft g)
    (fun x : GL (Fin r) k => ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      ((((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
        ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h2 : ξ (Matrix.GeneralLinearGroup.det (g * x)) =
      ξ (Matrix.GeneralLinearGroup.det g) * ξ (Matrix.GeneralLinearGroup.det x) := by
    rw [map_mul, map_mul]
  have h3 : ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      (((ξ (Matrix.GeneralLinearGroup.det (g * x)))⁻¹ : Rˣ) : R) =
      (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) := by
    rw [h2, ← Units.val_mul, mul_inv, mul_inv_cancel_left]
  have h4 : ((g * x : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) =
      (g : Matrix (Fin r) (Fin r) k) * (x : Matrix (Fin r) (Fin r) k) := rfl
  rw [Equiv.coe_mulLeft, ← mul_assoc, h3, h4, Matrix.mul_assoc]

theorem exists_gl_det_eq_mul_eq_of_det_eq_zero (k : Type) [Field k] (r : ℕ)
    (a : Matrix (Fin r) (Fin r) k) (ha : a.det = 0) (t : kˣ) :
    ∃ g : GL (Fin r) k, Matrix.GeneralLinearGroup.det g = t ∧
      a * (g : Matrix (Fin r) (Fin r) k) = a := by
  obtain ⟨v, hv, hav⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ha
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := hi
  let w : Fin r → k := Pi.single i (((t : k) - 1) / v i)
  have hdet : (1 + Matrix.vecMulVec v w).det = (t : k) := by
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [w, single_dotProduct]
    field_simp
    ring
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + Matrix.vecMulVec v w)
    (by rw [hdet]; exact t.ne_zero), ?_, ?_⟩
  · ext
    exact hdet
  · change a * (1 + Matrix.vecMulVec v w) = a
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, hav]
    simp

theorem matrixGaussSum_singular_and_invertible :
    ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∀ a : Matrix (Fin r) (Fin r) k, a.det = 0 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))) = 0) ∧ ∀ a : GL (Fin r) k, (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace ((a : Matrix (Fin r) (Fin r) k) * (x : Matrix (Fin r) (Fin r) k)))) = ((ξ (Matrix.GeneralLinearGroup.det a) : Rˣ) : R) * (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) := by
  intro k _ _ _ R _ _ ψ ξ r _ hξ
  refine ⟨fun a ha => ?_, fun a => ?_⟩
  · obtain ⟨t, ht⟩ : ∃ t, ξ t ≠ 1 := by
      by_contra h
      push_neg at h
      exact hξ (MonoidHom.ext h)
    obtain ⟨g, hg, hag⟩ := exists_gl_det_eq_mul_eq_of_det_eq_zero k r a ha t
    have h := matrixGaussSum_mul_unit k R ψ ξ r a g
    rw [hag, hg] at h
    have h1 : ((ξ t : Rˣ) : R) ≠ 1 := fun h' => ht (Units.ext h')
    by_contra hS
    exact h1 (mul_right_cancel₀ hS (h.symm.trans (one_mul _).symm))
  · have h := matrixGaussSum_mul_unit k R ψ ξ r 1 a
    rwa [Matrix.one_mul] at h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInvariantsEqOfInvertiblePeriodMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInvariantsEqOfInvertiblePeriodMatrix
open TensorProduct Module

open Matrix

theorem GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by
  intro F E _ _ _ _ B _ _ _ _ _ G act n _ _ A hfix Q hQ W hW
  set Q' : Matrix n n B := (Q : Matrix n n B) with hQ'
  have hQQ' : (↑Q⁻¹ : Matrix n n B) * Q' = 1 := by rw [hQ']; exact_mod_cast Q.inv_mul
  have hQQ : Q' * (↑Q⁻¹ : Matrix n n B) = 1 := by rw [hQ']; exact_mod_cast Q.mul_inv
  have key : ∀ g (y : n → B), (A g).mulVec (fun i => act g ((Q' *ᵥ y) i)) = Q' *ᵥ (fun i => act g (y i)) := by
    intro g y
    have h1 : (fun i => act g ((Q' *ᵥ y) i)) = Q'.map (act g) *ᵥ (fun i => act g (y i)) := by
      funext i; exact RingHom.map_mulVec _ _ _ _
    rw [h1, Matrix.mulVec_mulVec, hQ g]
  have inj : ∀ u v : n → B, Q' *ᵥ u = Q' *ᵥ v → u = v := by
    intro u v h
    have h2 := congrArg (fun w => (↑Q⁻¹ : Matrix n n B) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec] at h2
    rwa [hQQ', Matrix.one_mulVec, Matrix.one_mulVec] at h2
  let φ : (n → E) →ₗ[F] (n → B) :=
    { toFun := fun c => Q' *ᵥ (fun i => algebraMap E B (c i))
      map_add' := by
        intro a b
        have : (fun i => algebraMap E B ((a + b) i)) = (fun i => algebraMap E B (a i)) + (fun i => algebraMap E B (b i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add]
      map_smul' := by
        intro r a
        have : (fun i => algebraMap E B ((r • a) i)) = r • (fun i => algebraMap E B (a i)) := by
          funext i
          simp only [Pi.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
        rw [this, Matrix.mulVec_smul]
        rfl }
  have hφ : ∀ c, φ c = Q' *ᵥ (fun i => algebraMap E B (c i)) := fun c => rfl
  have φinj : Function.Injective φ := by
    intro a b h
    rw [hφ, hφ] at h
    have h3 := inj _ _ h
    funext i
    exact (algebraMap E B).injective (congrFun h3 i)
  have hWr : W = LinearMap.range φ := by
    ext x
    rw [hW, LinearMap.mem_range]
    constructor
    · intro hx
      set y : n → B := (↑Q⁻¹ : Matrix n n B) *ᵥ x with hy
      have hxy : Q' *ᵥ y = x := by rw [hy, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
      have hfixy : ∀ i g, act g (y i) = y i := by
        intro i g
        have h4 := hx g
        rw [← hxy, key] at h4
        exact congrFun (inj _ _ h4) i
      choose c hc using fun i => (hfix (y i)).1 (hfixy i)
      refine ⟨c, ?_⟩
      rw [hφ, ← hxy]
      congr 1
      funext i; exact hc i
    · rintro ⟨c, rfl⟩ g
      rw [hφ, key]
      congr 1
      funext i
      exact ((hfix _).2 ⟨c i, rfl⟩) g
  subst hWr
  rw [LinearMap.finrank_range_of_inj φinj, Module.finrank_pi_fintype]
  simp [Finset.sum_const, Finset.card_univ, mul_comm]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInvariantsEqOfInvertiblePeriodMatrixStatement
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by
  first | exact @GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | exact GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | (intros; apply GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModule
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModule
open Module

noncomputable section

namespace GlobalTheory.DVRQuotCount

open scoped TensorProduct DirectSum

theorem card_quot_smul_top_of_flat' {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Flat R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
    Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem rank_prod_of_rank_zero {R A B : Type} [CommRing R] [IsDomain R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (hB : ∀ x : B, ∃ a : R, a ≠ 0 ∧ a • x = 0) :
    Module.rank R (A × B) = Module.rank R A := by
  have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst R A B)
  have hk : Module.rank R (LinearMap.ker (LinearMap.fst R A B)) = 0 := by
    rw [rank_eq_zero_iff]
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, hax⟩ := hB x.2
    refine ⟨a, ha, ?_⟩
    ext
    · simpa using congrArg (a • ·) (show x.1 = 0 from hx)
    · simpa using hax
  rw [LinearMap.range_eq_top.2 (fun a => ⟨(a, 0), rfl⟩), rank_top, hk, add_zero] at h
  exact h.symm

theorem irreducible_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p t : O}
    (hp : Irreducible p) (ht : t ≠ 0) (htu : ¬ IsUnit t) : p ∣ t := by
  obtain ⟨q, hq, hqt⟩ := WfDvdMonoid.exists_irreducible_factor htu ht
  exact (IsDiscreteValuationRing.associated_of_irreducible O hp hq).dvd.trans hqt

theorem card_quot_pow_smul_bounds : ∀ (O M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (t : O), t ≠ 0 → ¬ IsUnit t →
    (∀ r : ℕ, Finite (O ⧸ Ideal.span {t ^ r})) → ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ,
      Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M ≤
        Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ∧
      Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ≤
        C * Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M := by
  intro O M _ _ _ _ _ _ t ht htu hfin
  obtain ⟨n, ι, _, p, hp, e, ⟨eqv⟩⟩ := Module.equiv_free_prod_directSum O M
  set T := ⨁ i : ι, O ⧸ O ∙ p i ^ e i
  set F := Fin n →₀ O

  have hTi : ∀ i, Finite (O ⧸ O ∙ p i ^ e i) := by
    intro i
    have hle : Ideal.span {t ^ e i} ≤ Ideal.span {p i ^ e i} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow_of_dvd (irreducible_dvd (hp i) ht htu) _
    haveI := hfin (e i)
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  haveI : Finite T := Finite.of_equiv _ (DirectSum.linearEquivFunOnFintype O ι _).toEquiv.symm

  have hkill : ∀ x : T, ∃ a : O, a ≠ 0 ∧ a • x = 0 := by
    intro x
    refine ⟨∏ i, p i ^ e i, Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hp i).ne_zero, ?_⟩
    ext i
    rw [DirectSum.smul_apply, DirectSum.zero_apply]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x i)
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Submodule.mem_span_singleton]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j => p j ^ e j) (Finset.mem_univ i)
    exact ⟨c * y, by rw [hc, smul_eq_mul]; ring⟩
  have hrank : finrank O M = n := by
    rw [eqv.finrank_eq]
    unfold Module.finrank
    rw [rank_prod_of_rank_zero hkill]
    change finrank O F = n
    simp [F]
  refine ⟨Nat.card T, Nat.card_pos, fun r => ?_⟩
  set I : Ideal O := Ideal.span {t ^ r}
  haveI := hfin r
  have hcard : Nat.card (M ⧸ (I • ⊤ : Submodule O M)) =
      Nat.card (O ⧸ I) ^ n * Nat.card (T ⧸ (I • ⊤ : Submodule O T)) := by
    rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul M I).toEquiv,
      Nat.card_congr (TensorProduct.congr (LinearEquiv.refl O (O ⧸ I)) eqv).toEquiv,
      Nat.card_congr (TensorProduct.prodRight O O (O ⧸ I) F T).toEquiv, Nat.card_prod,
      Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul F I).toEquiv,
      Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul T I).toEquiv,
      card_quot_smul_top_of_flat']
    simp [F]
  haveI : Finite (T ⧸ (I • ⊤ : Submodule O T)) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have h1 : 1 ≤ Nat.card (T ⧸ (I • ⊤ : Submodule O T)) := Nat.card_pos
  have h2 : Nat.card (T ⧸ (I • ⊤ : Submodule O T)) ≤ Nat.card T :=
    Nat.card_le_card_of_surjective _ (Submodule.mkQ_surjective _)
  rw [hcard, hrank]
  constructor
  · exact Nat.le_mul_of_pos_right _ h1
  · rw [mul_comm]; exact Nat.mul_le_mul_right _ h2

end GlobalTheory.DVRQuotCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardQuotPowSmulBoundsDvrFgModuleStatement
open Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_quot_pow_smul_bounds_dvr_fg_module : ∀ (O M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup M] [Module O M] [Module.Finite O M] (t : O), t ≠ 0 → ¬ IsUnit t → (∀ r : ℕ, Finite (O ⧸ Ideal.span {t ^ r})) → ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M ≤ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ∧ Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ≤ C * Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M := by
  first | exact @GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | exact GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds | (intros; apply GlobalTheory.DVRQuotCount.card_quot_pow_smul_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegral
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem exists_not_mem_mul_mem {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (t : K)
    (ht : v.valuation K t ≤ 1) :
    ∃ s : R, s ∉ v.asIdeal ∧ ∃ r : R, algebraMap R K s * t = algebraMap R K r := by
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) t
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [valuation_of_mk'] at ht
  set n := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hn
  have hvb : v.intValuation b = WithZero.exp (-(n : ℤ)) := v.intValuation_if_neg hb0
  have hpos : (0 : WithZero (Multiplicative ℤ)) < v.intValuation b := by
    rw [hvb]; exact WithZero.exp_pos
  have hva : v.intValuation a ≤ WithZero.exp (-(n : ℤ)) := by
    rw [← hvb]; exact (div_le_one₀ hpos).1 ht
  have haI : a ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem a n).1 hva
  have hbI : b ∈ v.asIdeal ^ n := (v.intValuation_le_pow_iff_mem b n).1 hvb.le
  have hbI' : b ∉ v.asIdeal ^ (n + 1) := by
    intro h
    have := (v.intValuation_le_pow_iff_mem b (n + 1)).2 h
    rw [hvb] at this
    have h2 := WithZero.exp_le_exp.1 this
    push_cast at h2
    omega
  have hdvd : v.asIdeal ^ n ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbI)
  obtain ⟨B', hB'⟩ := hdvd
  have hB'p : ¬ B' ≤ v.asIdeal := by
    intro hle
    apply hbI'
    have : Ideal.span {b} ≤ v.asIdeal ^ (n + 1) := by
      rw [hB', pow_succ]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self b)
  obtain ⟨s, hsB, hsp⟩ := Set.not_subset.1 hB'p
  refine ⟨s, hsp, ?_⟩
  have hmem : a * s ∈ Ideal.span {b} := by
    rw [hB']; exact Ideal.mul_mem_mul haI hsB
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨r, ?_⟩
  show algebraMap R K s * IsLocalization.mk' K a ⟨b, hb⟩ = algebraMap R K r
  rw [IsFractionRing.mk'_eq_div]
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K), (IsFractionRing.injective R K).eq_iff]; exact hb0
  rw [mul_div_assoc', div_eq_iff hbK, ← map_mul, ← map_mul, hr, mul_comm a s]

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal

theorem mul_mem_of_trace_mem {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : L)
    (hx : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range) :
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∃ c : 𝓞 L, (c : L) = x * (d : L) := by
  intro d hd
  have hxd : x ∈ FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx b
  have hdd : (d : L) ∈ ((differentIdeal (𝓞 K) (𝓞 L) : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  rw [coeIdeal_differentIdeal (𝓞 K) K] at hdd
  have hm := FractionalIdeal.mul_mem_mul hxd hdd
  rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero (𝓞 K) K (by simp))] at hm
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  exact ⟨c, hc⟩

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem exists_approx_idempotent {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)) (N : ℕ) :
    ∃ z : 𝓞 L, z ∉ la.asIdeal ∧ ∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la →
      la'.asIdeal.under (𝓞 K) = p.asIdeal → z ∈ la'.asIdeal ^ N := by
  set S : Set (HeightOneSpectrum (𝓞 L)) := {la' | la' ≠ la ∧ la'.asIdeal.under (𝓞 K) = p.asIdeal}
  haveI := p.isMaximal
  have hfin : S.Finite := by
    refine ((IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L)).preimage
      (f := HeightOneSpectrum.asIdeal) ?_).subset ?_
    · intro a _ b _ h; exact HeightOneSpectrum.ext h
    · intro la' h
      exact ⟨la'.isPrime, ⟨h.2.symm⟩⟩
  haveI := la.isPrime
  have hw : ∀ la' ∈ S, ∃ w : 𝓞 L, w ∈ la'.asIdeal ^ N ∧ w ∉ la.asIdeal := by
    intro la' h
    by_contra hc
    push_neg at hc
    have h1 : la'.asIdeal ^ N ≤ la.asIdeal := fun w hw => hc w hw
    have h2 := Ideal.IsPrime.le_of_pow_le h1
    exact h.1 (HeightOneSpectrum.ext (la'.isMaximal.eq_of_le la.isPrime.ne_top h2))
  choose! w hwN hwla using hw
  refine ⟨∏ la' ∈ hfin.toFinset, w la', ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, hi, hmem⟩
    exact hwla i (hfin.mem_toFinset.1 hi) hmem
  · intro la' h1 h2
    have hS : la' ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨h1, h2⟩
    rw [← Finset.mul_prod_erase _ _ hS]
    exact Ideal.mul_mem_right _ _ (hwN la' ⟨h1, h2⟩)

end GlobalTheory.InvDiffLocal

namespace GlobalTheory.InvDiffLocal


open IsDedekindDomain.HeightOneSpectrum in
theorem valuation_mul_different_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)),
    la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ y : L, (∃ N : ℕ, ∀ b : 𝓞 L,
      (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal →
        b ∈ la'.asIdeal ^ N) → p.valuation K (Algebra.trace K L ((b : L) * y)) ≤ 1) →
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1 := by
  intro K L _ _ _ _ _ la p hp y ⟨N, hN⟩ d hd
  obtain ⟨z, hzla, hzN⟩ := exists_approx_idempotent (K := K) la p N
  set x : L := (z : L) * y with hxdef
  have hx : ∀ b : 𝓞 L, p.valuation K (Algebra.trace K L ((b : L) * x)) ≤ 1 := by
    intro b
    have h := hN (b * z) (fun la' h1 h2 => Ideal.mul_mem_left _ _ (hzN la' h1 h2))
    rw [hxdef, ← mul_assoc]
    simpa using h
  set bs := RingOfIntegers.basis L
  have hloc : ∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K s * Algebra.trace K L ((bs i : L) * x) = algebraMap (𝓞 K) K r :=
    fun i => exists_not_mem_mul_mem p _ (hx (bs i))
  choose s hsp r hr using hloc
  set s0 : 𝓞 K := ∏ i, s i with hs0
  haveI := p.isPrime
  have hs0p : s0 ∉ p.asIdeal := by
    rw [hs0, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨i, _, hi⟩
    exact hsp i hi
  have hgen : ∀ b : 𝓞 L,
      algebraMap (𝓞 K) K s0 * Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have hb : b ∈ Submodule.span ℤ (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨i, rfl⟩ := hb
      rw [hs0, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), map_mul, mul_comm (algebraMap _ _ (s i)),
        mul_assoc, hr i, ← map_mul]
      exact ⟨_, rfl⟩
    | zero => simp
    | add b c _ _ hb hc =>
      have : ((b + c : 𝓞 L) : L) * x = (b : L) * x + (c : L) * x := by push_cast; ring
      rw [this, map_add (f := _), mul_add]
      exact add_mem hb hc
    | smul n b _ hb =>
      have : ((n • b : 𝓞 L) : L) * x = n • ((b : L) * x) := by
        rw [← smul_mul_assoc]; congr 1
      rw [this, map_zsmul, mul_smul_comm]
      exact zsmul_mem hb n
  set x' : L := algebraMap (𝓞 K) L s0 * x with hx'def
  have htr : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x') ∈ (algebraMap (𝓞 K) K).range := by
    intro b
    have : (b : L) * x' = (algebraMap (𝓞 K) K s0) • ((b : L) * x) := by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, hx'def]; ring
    rw [this, map_smul, smul_eq_mul]
    exact hgen b
  obtain ⟨c, hc⟩ := mul_mem_of_trace_mem x' htr d hd
  have hcle : la.valuation L (c : L) ≤ 1 := la.valuation_le_one c
  have hs0la : la.valuation L (algebraMap (𝓞 K) L s0) = 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
    refine le_antisymm (la.valuation_le_one _) (not_lt.1 fun h => hs0p ?_)
    rw [la.valuation_lt_one_iff_mem] at h
    rw [← hp]
    exact h
  have hzla' : la.valuation L (z : L) = 1 := by
    refine le_antisymm (la.valuation_le_one z) (not_lt.1 fun h => hzla ?_)
    exact (la.valuation_lt_one_iff_mem z).1 h
  have : (c : L) = (algebraMap (𝓞 K) L s0 * (z : L)) * (y * (d : L)) := by
    rw [hc, hx'def, hxdef]; ring
  rw [this, map_mul, map_mul, hs0la, hzla', one_mul, one_mul] at hcle
  exact hcle

end GlobalTheory.InvDiffLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationMulLeOneOfTraceApproxIdempotentIntegralStatement
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_mul_le_one_of_trace_approxIdempotent_integral : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ y : L, (∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → p.valuation K (Algebra.trace K L ((b : L) * y)) ≤ 1) → ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1 := by
  first | exact @GlobalTheory.InvDiffLocal.valuation_mul_different_le_one | exact GlobalTheory.InvDiffLocal.valuation_mul_different_le_one | (intros; apply GlobalTheory.InvDiffLocal.valuation_mul_different_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumOneAddNormRpowNegLeEuclidean
open MeasureTheory Metric Module
open scoped ENNReal

namespace GlobalTheory.LatticeCount

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma one_add_norm_rpow_neg_le {s r : ℝ} (hs : 0 ≤ s) {x y : V} (hx : r ≤ ‖x‖)
    (hy : y ∈ ball x (r / 2)) :
    (1 + ‖x‖) ^ (-s) ≤ 2 ^ s * (1 + ‖y‖) ^ (-s) := by
  have hd : dist y x < r / 2 := mem_ball.mp hy
  rw [dist_eq_norm] at hd
  have h1 := norm_sub_norm_le y x
  have hx0 := norm_nonneg x
  have key : 1 + ‖y‖ ≤ 2 * (1 + ‖x‖) := by linarith
  have hpos : 0 < 1 + ‖y‖ := by positivity
  calc (1 + ‖x‖) ^ (-s) = 2 ^ s * (2 * (1 + ‖x‖)) ^ (-s) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← mul_assoc, ← Real.rpow_add (by norm_num)]
        simp
    _ ≤ 2 ^ s * (1 + ‖y‖) ^ (-s) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos key (by linarith)) (by positivity)

lemma sum_mul_measure_ball_le [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {s : ℝ} (hs : 0 ≤ s) (Λ : AddSubgroup V) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) (t : Finset ((Λ : Set V) \ {0} : Set V)) :
    (∑ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s))) * μ (ball 0 (r / 2)) ≤
      ENNReal.ofReal (2 ^ s) * ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ := by
  classical
  have hpt : ∀ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s)) * μ (ball 0 (r / 2)) ≤
      ENNReal.ofReal (2 ^ s) *
        ∫⁻ y in ball (x : V) (r / 2), ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ := by
    intro x _
    rw [← Measure.addHaar_ball_center μ (x : V) (r / 2), ← setLIntegral_const,
      ← lintegral_const_mul' (ENNReal.ofReal (2 ^ s)) _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_ball
    intro y hy
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    exact one_add_norm_rpow_neg_le hs (hmin _ (SetLike.mem_coe.mp x.2.1) (by simpa using x.2.2)) hy
  have hdisj : Set.PairwiseDisjoint (↑t)
      (fun x : ((Λ : Set V) \ {0} : Set V) => ball (x : V) (r / 2)) := by
    intro a _ b _ hab
    show Disjoint (ball (a : V) (r / 2)) (ball (b : V) (r / 2))
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have hmem : (a : V) - b ∈ Λ :=
      Λ.sub_mem (SetLike.mem_coe.mp a.2.1) (SetLike.mem_coe.mp b.2.1)
    have hne : (a : V) - b ≠ 0 := sub_ne_zero.mpr (fun h => hab (Subtype.ext h))
    linarith [hmin _ hmem hne]
  calc (∑ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s))) * μ (ball 0 (r / 2))
      = ∑ x ∈ t, ENNReal.ofReal ((1 + ‖(x : V)‖) ^ (-s)) * μ (ball 0 (r / 2)) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ t, ENNReal.ofReal (2 ^ s) *
          ∫⁻ y in ball (x : V) (r / 2), ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ :=
        Finset.sum_le_sum hpt
    _ = ENNReal.ofReal (2 ^ s) *
          ∫⁻ y in ⋃ x ∈ t, ball (x : V) (r / 2), ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
    _ ≤ ENNReal.ofReal (2 ^ s) * ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ :=
        mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) (zero_le)

lemma sum_le_mul_rpow [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    [Nontrivial V] {s : ℝ} (hs : (finrank ℝ V : ℝ) < s) (Λ : AddSubgroup V) {r : ℝ} (hr : 0 < r)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) (t : Finset ((Λ : Set V) \ {0} : Set V)) :
    ∑ x ∈ t, (1 + ‖(x : V)‖) ^ (-s) ≤
      (2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ).toReal * 2 ^ finrank ℝ V /
        (μ (ball 0 1)).toReal) * r ^ (-(finrank ℝ V : ℝ)) := by
  have hD0 : (0 : ℝ) ≤ finrank ℝ V := Nat.cast_nonneg _
  have hs0 : 0 ≤ s := by linarith
  have hI : ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ < ∞ := finite_integral_one_add_norm hs
  have hB0 : 0 < μ (ball (0 : V) 1) := measure_ball_pos μ 0 one_pos
  have hBt : μ (ball (0 : V) 1) < ∞ := measure_ball_lt_top
  have hBpos : 0 < (μ (ball (0 : V) 1)).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
  have h2 := sum_mul_measure_ball_le μ hs0 Λ hr hmin t
  rw [Measure.addHaar_ball μ 0 (by positivity : (0 : ℝ) ≤ r / 2),
    ← ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity)] at h2
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun x _ => by positivity)),
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at h3
  have e : 2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ).toReal * 2 ^ finrank ℝ V /
        (μ (ball 0 1)).toReal * r ^ (-(finrank ℝ V : ℝ)) =
      (2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂μ).toReal) /
        ((r / 2) ^ finrank ℝ V * (μ (ball 0 1)).toReal) := by
    rw [Real.rpow_neg hr.le, Real.rpow_natCast, div_pow]
    field_simp
  rw [e, le_div_iff₀ (mul_pos (pow_pos (by positivity) _) hBpos)]
  linarith [h3]

private lemma rpow_neg_mul_one_add_le_two_mul {D : ℝ} (hD : 1 ≤ D) {r : ℝ} (hr : 0 < r) :
    r ^ (-D) * (1 + r) ≤ 2 * (r ^ (-D) + 1) := by
  have h0 : 0 ≤ r ^ (-D) := by positivity
  rcases le_total r 1 with h | h
  · have : r ^ (-D) * r ≤ r ^ (-D) := mul_le_of_le_one_right h0 h
    nlinarith
  · have h1 : r ^ (-D) * r ≤ 1 := by
      rw [← Real.rpow_add_one hr.ne']
      exact Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have h2 : r ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    nlinarith

theorem tsum_one_add_norm_rpow_neg_le (hD : 1 ≤ finrank ℝ V) {M : ℝ}
    (hM : (finrank ℝ V : ℝ) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup V) (r : ℝ), 0 < r → (∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) →
      Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-M)) ∧
      ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M) ≤
        C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
  let _ : MeasurableSpace V := borel V
  have _ : BorelSpace V := ⟨rfl⟩
  have _ : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hD1 : (1 : ℝ) ≤ (finrank ℝ V : ℝ) := by exact_mod_cast hD
  set s : ℝ := min M ((finrank ℝ V : ℝ) + 1) with hsdef
  have hsD : (finrank ℝ V : ℝ) < s := lt_min hM (by linarith)
  have hsM : s ≤ M := min_le_left _ _
  have hsD1 : s ≤ (finrank ℝ V : ℝ) + 1 := min_le_right _ _
  set K : ℝ := 2 ^ s * (∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ (-s)) ∂(Measure.addHaar : Measure V)).toReal *
    2 ^ finrank ℝ V / ((Measure.addHaar : Measure V) (ball 0 1)).toReal with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨2 * K + 1, by positivity, fun Λ r hr hmin => ?_⟩
  have hfs : ∀ u : Finset ((Λ : Set V) \ {0} : Set V),
      ∑ x ∈ u, (1 + ‖(x : V)‖) ^ (-s) ≤ K * r ^ (-(finrank ℝ V : ℝ)) :=
    fun u => sum_le_mul_rpow (Measure.addHaar : Measure V) hsD Λ hr hmin u
  have hf0 : ∀ x : ((Λ : Set V) \ {0} : Set V), 0 ≤ (1 + ‖(x : V)‖) ^ (-s) :=
    fun x => by positivity
  have hsum : Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-s)) :=
    summable_of_sum_le hf0 hfs
  have hle : ∀ x : ((Λ : Set V) \ {0} : Set V),
      (1 + ‖(x : V)‖) ^ (-M) ≤ (1 + ‖(x : V)‖) ^ (-s) * (1 + r) ^ (s - M) := by
    intro x
    have hx : r ≤ ‖(x : V)‖ := hmin _ (SetLike.mem_coe.mp x.2.1) (by simpa using x.2.2)
    have hpos : 0 < 1 + ‖(x : V)‖ := by positivity
    calc (1 + ‖(x : V)‖) ^ (-M) = (1 + ‖(x : V)‖) ^ (-s) * (1 + ‖(x : V)‖) ^ (s - M) := by
          rw [← Real.rpow_add hpos]; congr 1; ring
      _ ≤ (1 + ‖(x : V)‖) ^ (-s) * (1 + r) ^ (s - M) := by
          apply mul_le_mul_of_nonneg_left _ (hf0 x)
          exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hsumM : Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-M)) :=
    Summable.of_nonneg_of_le (fun x => by positivity) hle (hsum.mul_right _)
  refine ⟨hsumM, ?_⟩
  have hpow := rpow_neg_mul_one_add_le_two_mul hD1 hr
  have hsplit : (1 + r) ^ (s - M) = (1 + r) ^ (s - finrank ℝ V) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have hsD' : (1 + r) ^ (s - finrank ℝ V) ≤ 1 + r := by
    calc (1 + r) ^ (s - finrank ℝ V) ≤ (1 + r) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 + r := Real.rpow_one _
  have hA : 0 ≤ r ^ (-(finrank ℝ V : ℝ)) := by positivity
  have hB : 0 ≤ (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by positivity
  calc ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M)
      ≤ ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-s) * (1 + r) ^ (s - M) :=
        Summable.tsum_le_tsum hle hsumM (hsum.mul_right _)
    _ = (∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-s)) * (1 + r) ^ (s - M) :=
        tsum_mul_right
    _ ≤ (K * r ^ (-(finrank ℝ V : ℝ))) * (1 + r) ^ (s - M) :=
        mul_le_mul_of_nonneg_right (hsum.tsum_le_of_sum_le hfs) (by positivity)
    _ = K * (r ^ (-(finrank ℝ V : ℝ)) * (1 + r) ^ (s - finrank ℝ V)) *
          (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by rw [hsplit]; ring
    _ ≤ K * (r ^ (-(finrank ℝ V : ℝ)) * (1 + r)) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
        gcongr
    _ ≤ K * (2 * (r ^ (-(finrank ℝ V : ℝ)) + 1)) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
        gcongr
    _ ≤ (2 * K + 1) * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := by
        nlinarith [mul_nonneg (add_nonneg hA zero_le_one) hB]

theorem tsum_one_add_norm_rpow_neg_le_regimes (hD : 1 ≤ finrank ℝ V) {M : ℝ}
    (hM : (finrank ℝ V : ℝ) < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : AddSubgroup V) (r : ℝ), 0 < r → (∀ x ∈ Λ, x ≠ 0 → r ≤ ‖x‖) →
      Summable (fun x : ((Λ : Set V) \ {0} : Set V) => (1 + ‖(x : V)‖) ^ (-M)) ∧
      (r ≤ 1 → ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M) ≤
        C * r ^ (-(finrank ℝ V : ℝ))) ∧
      (1 ≤ r → ∑' x : ((Λ : Set V) \ {0} : Set V), (1 + ‖(x : V)‖) ^ (-M) ≤
        C * r ^ ((finrank ℝ V : ℝ) - M)) := by
  obtain ⟨C, hC, h⟩ := tsum_one_add_norm_rpow_neg_le hD hM
  have hD0 : (0 : ℝ) ≤ finrank ℝ V := Nat.cast_nonneg _
  refine ⟨2 * C, by positivity, fun Λ r hr hmin => ⟨(h Λ r hr hmin).1, fun hr1 => ?_, fun hr1 => ?_⟩⟩
  · have hb := (h Λ r hr hmin).2
    have e1 : (1 + r) ^ ((finrank ℝ V : ℝ) - M) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have e2 : 1 ≤ r ^ (-(finrank ℝ V : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
    have e3 : 0 ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) := by positivity
    calc _ ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := hb
      _ ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * 1 := mul_le_mul_of_nonneg_left e1 e3
      _ ≤ 2 * C * r ^ (-(finrank ℝ V : ℝ)) := by nlinarith
  · have hb := (h Λ r hr hmin).2
    have e1 : (1 + r) ^ ((finrank ℝ V : ℝ) - M) ≤ r ^ ((finrank ℝ V : ℝ) - M) :=
      Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
    have e2 : r ^ (-(finrank ℝ V : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith)
    calc _ ≤ C * (r ^ (-(finrank ℝ V : ℝ)) + 1) * (1 + r) ^ ((finrank ℝ V : ℝ) - M) := hb
      _ ≤ (C * 2) * r ^ ((finrank ℝ V : ℝ) - M) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC.le) e1 (by positivity)
            (by positivity)
      _ = 2 * C * r ^ ((finrank ℝ V : ℝ) - M) := by ring

end GlobalTheory.LatticeCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapPiEqOfMapAddHaarEq
open MeasureTheory

namespace GlobalTheory

theorem map_pi_eq_of_map_addHaar_eq (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (φ : G →+ G) (hφ : Continuous φ)
    (h : ∀ ν : Measure G, ν.IsAddHaarMeasure → ν.map φ = ν) (m : ℕ)
    (μ : @Measure (Fin m → G) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (Fin m → G) _ _ (borel _) μ) :
    @Measure.map _ _ (borel _) (borel _) (fun x i => φ (x i)) μ = μ := by
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin m → G)) = borel _ := BorelSpace.measurable_eq
  revert μ hμ
  rw [← hb]
  intro μ hμ
  let ν : Measure G := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  have hp : MeasurePreserving φ ν ν := ⟨hφ.measurable, h ν hν⟩
  have hpi : MeasurePreserving (fun (x : Fin m → G) i => φ (x i)) (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) :=
    measurePreserving_pi _ _ (fun _ => hp)
  have hH : (Measure.pi fun _ : Fin m => ν).IsAddHaarMeasure := inferInstance
  have he := Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin m => ν)
  generalize Measure.addHaarScalarFactor μ (Measure.pi fun _ : Fin m => ν) = c at he
  subst he
  rw [Measure.map_smul c hpi.measurable.aemeasurable, hpi.map_eq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRankMapField
open Matrix
namespace GlobalTheory
private lemma rank_fromBlocks_one_zero_lemma {F G : Type} [Field F] [Field G] (r s : ℕ) :
    (fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0 (0 : Matrix (Fin s) (Fin s) F)).rank =
      (fromBlocks (1 : Matrix (Fin r) (Fin r) G) 0 0 (0 : Matrix (Fin s) (Fin s) G)).rank := by
  classical
  rw [← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, rank_diagonal,
    ← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by cases i <;> simp)
theorem matrix_rank_map_field {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := exists_rank_normal_form M
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det _).1 hV
  have hUd : IsUnit U.det := (isUnit_iff_isUnit_det _).1 hU
  have hV' : IsUnit (V.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hVd.map φ
  have hU' : IsUnit (U.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hUd.map φ
  have hmap : V.map φ * M.map φ * U.map φ =
      (fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0 0).submatrix e e := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h, ← submatrix_map, fromBlocks_map]
    simp
  calc (M.map φ).rank = (V.map φ * M.map φ * U.map φ).rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hU', rank_mul_eq_right_of_isUnit_det _ _ hV']
    _ = (fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) K) 0 0 0).rank := by
        rw [hmap, rank_submatrix]
        exact rank_fromBlocks_one_zero_lemma _ _
    _ = (V * M * U).rank := by rw [h, rank_submatrix]
    _ = M.rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hUd, rank_mul_eq_right_of_isUnit_det _ _ hVd]
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndexSmulCocycleEqCoboundary
namespace GlobalTheory

theorem index_smul_cocycle_eq_coboundary (R G X : Type) [CommRing R] [Group G] [AddCommGroup X]
    [Module R X] (ρ : Representation R G X) (H : Subgroup G) [H.FiniteIndex] (f : G → X)
    (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (hH : ∃ x, ∀ h ∈ H, f h = ρ h x - x) :
    ∃ x, ∀ g, H.index • f g = ρ g x - x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hH
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → X := fun g => f g - (ρ g x₀ - x₀) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + ρ g (f' h) := by
    intro g h
    simp only [hf', hf, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hz : ∀ h ∈ H, f' h = 0 := by
    intro h hh
    simp only [hf', hx₀ h hh, sub_self]
  have hq : ∀ (g : G) (q : G ⧸ H), f' (g • q).out = f' g + ρ g (f' q.out) := by
    intro g q
    have h1 : ((g * q.out : G) : G ⧸ H) = ((g • q).out : G ⧸ H) := by
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    have h2 := QuotientGroup.eq.mp h1
    have h3 : (g • q).out = (g * q.out) * ((g * q.out)⁻¹ * (g • q).out) := by group
    rw [h3, hc, hz _ h2, map_zero, add_zero, hc]
  refine ⟨H.index • x₀ - ∑ q : G ⧸ H, f' q.out, fun g => ?_⟩
  have hs : ∑ q : G ⧸ H, f' (g • q).out = ∑ q : G ⧸ H, f' q.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => f' q.out)
  simp only [hq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card] at hs
  have hfg : f g = f' g + (ρ g x₀ - x₀) := by simp [hf']
  have hs' : H.index • f' g = ∑ q : G ⧸ H, f' q.out - ρ g (∑ q : G ⧸ H, f' q.out) :=
    eq_sub_of_add_eq hs
  rw [hfg, smul_add, hs', map_sub, map_nsmul, smul_sub]
  abel

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeModuleAdicCompleteSeparated
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeModuleAdicCompleteSeparated
namespace GlobalTheory

theorem freeModule_adicComplete_separated : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → (∀ a : R, (∀ n : ℕ, ∃ b : R, a = ϖ ^ n * b) → a = 0) → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M], (∀ x : ℕ → M, ∃ y : M, ∀ n : ℕ, ∃ z : M, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) ∧ (∀ m : M, (∀ n : ℕ, ∃ z : M, m = ϖ ^ n • z) → m = 0) := by
  intro R _ ϖ hc hs M _ _ _ _
  classical
  let b := Module.Free.chooseBasis R M
  haveI : Fintype (Module.Free.ChooseBasisIndex R M) := Module.Free.ChooseBasisIndex.fintype R M
  constructor
  · intro x
    choose a ha using fun i => hc (fun j => b.equivFun (x j) i)
    refine ⟨b.equivFun.symm a, fun n => ?_⟩
    choose c hc' using fun i => ha i n
    refine ⟨b.equivFun.symm c, ?_⟩
    apply b.equivFun.injective
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, LinearEquiv.apply_symm_apply, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hc' i
  · intro m hm
    apply b.equivFun.injective
    funext i
    show b.equivFun m i = b.equivFun 0 i
    rw [map_zero]
    show b.equivFun m i = 0
    apply hs
    intro n
    obtain ⟨z, hz⟩ := hm n
    refine ⟨b.equivFun z i, ?_⟩
    rw [hz, map_smul]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeModuleAdicCompleteSeparatedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_finite_module_adicComplete_and_separated : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → (∀ a : R, (∀ n : ℕ, ∃ b : R, a = ϖ ^ n * b) → a = 0) → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M], (∀ x : ℕ → M, ∃ y : M, ∀ n : ℕ, ∃ z : M, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) ∧ (∀ m : M, (∀ n : ℕ, ∃ z : M, m = ϖ ^ n • z) → m = 0) := by
  first | exact @GlobalTheory.freeModule_adicComplete_separated | exact GlobalTheory.freeModule_adicComplete_separated | (intros; apply GlobalTheory.freeModule_adicComplete_separated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddPowOfMulSelfEqZero
namespace GlobalTheory.OneAddPowSquareZero

theorem one_add_pow_of_mul_self_eq_zero :
    ∀ {S : Type} [inst : Ring S] (X : S), X * X = (0 : S) →
      ∀ (N : ℕ), ((1 : S) + X) ^ N = (1 : S) + (↑N : S) * X := by
  intro S _ X hX N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, mul_add, mul_one, add_mul, one_mul, mul_assoc, hX,
      mul_zero, add_zero, add_mul, one_mul, add_assoc]

end GlobalTheory.OneAddPowSquareZero
end
