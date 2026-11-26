module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSzNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis.FrameCompl

variable {E : Type} [Field E]

theorem cT_mul (τ : E →+* E) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add (τ : E →+* E) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i k; simp [cT]

theorem cT_cT (τ : E →+* E) (hτ : ∀ x, τ (τ x) = x) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i k; simp [cT, hτ]

theorem cT_one (τ : E →+* E) {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) E) = 1 := by
  ext i k; simp [cT, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]

theorem cT_zero (τ : E →+* E) {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i k; simp [cT]

end GlobalTheory.SphEis.FrameCompl


open GlobalTheory.SphEis.FrameCompl in
theorem GlobalTheory.SphEis.exists_fr_of_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (j : ℕ) (C D : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) C * J * C = 0 → cT (σ : E →+* E) D * J * D = 0 → cT (σ : E →+* E) C * J * D = 1 → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ := by
  intro F E _ _ _ _ _ σ hcm n J hJ j C D hcc hdd hcd
  set τ : E →+* E := (σ : E →+* E) with hτdef
  have hτ : ∀ x, τ (τ x) = x := fun x => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm x
  have hJJ : cT τ J = J := by ext i k; exact hJ.1 i k
  have hdc : cT τ D * J * C = 1 := by
    have := congrArg (cT τ) hcd
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_one, ← Matrix.mul_assoc] at this

  let W : Submodule E (Fin n → E) :=
    LinearMap.ker (Matrix.toLin' (cT τ C * J)) ⊓ LinearMap.ker (Matrix.toLin' (cT τ D * J))
  let m := Module.finrank E W
  let b : Module.Basis (Fin m) E W := Module.finBasis E W
  let Z : Matrix (Fin n) (Fin m) E := Matrix.of fun r k => (b k : Fin n → E) r
  have hZv : ∀ u : Fin m → E, Z *ᵥ u = ((∑ k, u k • b k : W) : Fin n → E) := by
    intro u; ext r
    simp [Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hk : ∀ k, Z *ᵥ Pi.single k 1 = (b k : Fin n → E) := by
    intro k; rw [hZv]; simp [Pi.single_apply]
  have hCZ : cT τ C * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.1
  have hDZ : cT τ D * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.2
  have hZC : cT τ Z * J * C = 0 := by
    have := congrArg (cT τ) hCZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this
  have hZD : cT τ Z * J * D = 0 := by
    have := congrArg (cT τ) hDZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this

  set Pr : Matrix (Fin n) (Fin n) E := 1 - C * (cT τ D * J) - D * (cT τ C * J) with hPr
  have hCPr : cT τ C * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hcc, hcd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hDPr : cT τ D * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hdc, hdd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hmem : ∀ i, Pr *ᵥ Pi.single i 1 ∈ W := by
    intro i
    refine ⟨?_, ?_⟩
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hCPr, Matrix.zero_mulVec]
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDPr, Matrix.zero_mulVec]
  let M : Matrix (Fin m) (Fin n) E := Matrix.of fun k i => b.repr ⟨_, hmem i⟩ k
  have hZM : Z * M = Pr := by
    apply Matrix.ext_of_mulVec_single; intro i
    rw [← Matrix.mulVec_mulVec]
    have : M *ᵥ Pi.single i 1 = fun k => b.repr ⟨_, hmem i⟩ k := by
      ext k; simp [M, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hZv, b.sum_repr]
  have hdec : C * (cT τ D * J) + D * (cT τ C * J) + Z * M = 1 := by
    rw [hZM, hPr]; abel

  set J₀ : Matrix (Fin m) (Fin m) E := cT τ Z * J * Z with hJ₀
  have hJ₀h : cT τ J₀ = J₀ := by
    rw [hJ₀, cT_mul, cT_mul, cT_cT τ hτ, hJJ, Matrix.mul_assoc]
  have hCZ' : cT τ C * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hCZ
  have hDZ' : cT τ D * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hDZ
  have key : J * Z = cT τ M * J₀ := by
    have h1 : cT τ (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) = 1 := by rw [hdec, cT_one]
    rw [cT_add, cT_add, cT_mul, cT_mul, cT_mul, cT_mul, cT_mul, cT_cT τ hτ, cT_cT τ hτ, hJJ] at h1
    conv_lhs => rw [← Matrix.one_mul (J * Z), ← h1]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', Matrix.mul_zero, zero_add, hJ₀]
  have hdet : J₀.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hJz : J *ᵥ (Z *ᵥ u) = 0 := by
      rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hJz
    rw [hZv] at hz
    have hs : (∑ k, u k • b k : W) = 0 := Subtype.ext hz
    exact hu0 (funext fun k => Fintype.linearIndependent_iff.mp b.linearIndependent u hs k)
  have hinv : J₀⁻¹ * J₀ = 1 := Matrix.nonsing_inv_mul J₀ (isUnit_iff_ne_zero.mpr hdet)
  set S : Matrix (Fin n) (Fin n) E := C * (cT τ D * J) + Z * (J₀⁻¹ * (cT τ Z * J)) + D * (cT τ C * J) with hS
  have a1 : cT τ D * (J * C) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hdc
  have a2 : cT τ Z * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZC
  have a3 : cT τ C * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hcc
  have a4 : cT τ D * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hdd
  have a5 : cT τ Z * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZD
  have a6 : cT τ C * (J * D) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hcd
  have a7 : cT τ Z * (J * Z) = J₀ := (Matrix.mul_assoc _ _ _).symm
  have hSC : S * C = C := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a1, a2, a3, Matrix.mul_zero, Matrix.mul_one, add_zero]
  have hSD : S * D = D := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a4, a5, a6, Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hSZ : S * Z = Z := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', a7, Matrix.mul_zero, add_zero, zero_add]
    rw [hinv, Matrix.mul_one]
  have hS1 : S = 1 := by
    calc S = S * (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) := by rw [hdec, Matrix.mul_one]
      _ = S * C * (cT τ D * J) + S * D * (cT τ C * J) + S * Z * M := by
          simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = 1 := by rw [hSC, hSD, hSZ, hdec]
  have hdim : m + 2 * j = n := by
    have ht := congrArg Matrix.trace hS1
    rw [hS, Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm C, Matrix.trace_mul_comm Z,
      Matrix.trace_mul_comm D] at ht
    simp only [Matrix.mul_assoc, a1, a6, a7, hinv, Matrix.trace_one, Fintype.card_fin] at ht
    have : ((m + 2 * j : ℕ) : E) = (n : E) := by push_cast; rw [← ht]; ring
    exact_mod_cast this
  refine ⟨m, Z, J₀, hcm, hJ, ⟨fun i k => ?_, hdet⟩, hcc, hdd, hcd, hdc, hCZ, hDZ, hZC, hZD, rfl, hS1, hdim⟩
  have := congrFun (congrFun hJ₀h i) k
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNorm
open NumberField

open scoped Pointwise

namespace GlobalTheory.VacRead

theorem mul_smul_eq_span_absNorm {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]
    (h2 : Module.finrank ℚ K = 2) (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ 1) (I : Ideal (𝓞 K)) :
    I * (τ • I) = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} := by
  classical
  by_cases hI : I = ⊥
  · subst hI; simp
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, τ} := by
    symm; apply Finset.eq_univ_of_card
    rw [Finset.card_pair (Ne.symm hτ), ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have hprin : (I ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨x, hx⟩ := hprin
  have hx' : I ^ h = Ideal.span {x} := hx
  have hτx : τ • (I ^ h) = Ideal.span {τ • x} := by
    rw [hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 K) = x * (τ • x) := by
    have hp : ((Algebra.norm ℤ x : ℤ) : 𝓞 K) = ∏ σ : K ≃ₐ[ℚ] K, σ • x := by
      apply RingOfIntegers.ext
      have h1 := Algebra.norm_eq_prod_automorphisms ℚ (x : K)
      rw [← Algebra.coe_norm_int] at h1
      change algebraMap (𝓞 K) K _ = algebraMap (𝓞 K) K _
      rw [map_prod, map_intCast]
      rw [map_intCast] at h1
      exact h1
    rw [hp, huniv, Finset.prod_pair (Ne.symm hτ), one_smul]
  have key : (I * (τ • I)) ^ h = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} ^ h := by
    rw [mul_pow, ← smul_pow', hx', ← hx', hτx, hx', Ideal.span_singleton_mul_span_singleton, ← hnorm,
      Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]
    rcases Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4
    · conv_lhs => rw [h4]
      rw [Int.cast_natCast]
    · conv_lhs => rw [h4]
      rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
  exact pow_left_injective hpos key

theorem hostConj_quadraticGenerator_eq_neg (D : Formalism.BasicNotions.D7) :
    D.host.conj (D.host.sqd) = -D.host.sqd :=
  D.host.conj_sqd

theorem conj_mul_cE_absNorm (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) :
    (∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, ∃ o : 𝓞 D.host.E,
      D.host.conj α * β = (Ideal.absNorm cc : D.host.E) * (o : D.host.E)) ∧
    (Ideal.absNorm cc : D.host.E) ∈ Submodule.span (𝓞 D.host.E)
      {t | ∃ α ∈ GlobalTheory.VacRead.cE D cc, ∃ β ∈ GlobalTheory.VacRead.cE D cc, t = D.host.conj α * β} := by
  classical
  haveI : Algebra.IsQuadraticExtension ℚ D.host.K := ⟨GlobalTheory.CurveLattice.finrank_hostK D⟩
  let τ : D.host.K ≃ₐ[ℚ] D.host.K := D.host.conj.restrictNormal D.host.K
  have hτ : ∀ k : D.host.K, ((τ k : D.host.K) : D.host.E) = D.host.conj (k : D.host.E) :=
    fun k => AlgEquiv.restrictNormal_commutes D.host.conj D.host.K k
  have hτ1 : τ ≠ 1 := by
    intro h1
    have hs : D.host.sqd ∈ D.host.K :=
      IntermediateField.mem_adjoin_simple_self ℚ _
    have h2 := hτ ⟨_, hs⟩
    rw [h1, AlgEquiv.one_apply, hostConj_quadraticGenerator_eq_neg] at h2
    have h3 : D.host.sqd = 0 := by
      have : (2 : D.host.E) * D.host.sqd = 0 := by
        simp only at h2; linear_combination h2
      simpa using this
    have h4 := D.host.sqd_sq
    rw [h3] at h4
    have hd : (D.host.d : D.host.E) ≠ 0 := by exact_mod_cast D.host.hyp.2.1.pos.ne'
    exact hd (by simpa using h4.symm)
  have hI := mul_smul_eq_span_absNorm (GlobalTheory.CurveLattice.finrank_hostK D) τ hτ1 cc

  let iK : 𝓞 D.host.K →+* 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E)
  have hiK : ∀ k : 𝓞 D.host.K, ((iK k : 𝓞 D.host.E) : D.host.E) = ((k : D.host.K) : D.host.E) := fun k => rfl
  have hsm : ∀ k : 𝓞 D.host.K, (((τ • k : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((k : D.host.K) : D.host.E) :=
    fun k => hτ k
  set N : D.host.E := (Ideal.absNorm cc : D.host.E) with hN
  let M : Submodule (𝓞 D.host.E) D.host.E := Submodule.span (𝓞 D.host.E) {N}
  have hgen : ∀ c₁ ∈ cc, ∀ c₂ ∈ cc, D.host.conj ((c₁ : D.host.K) : D.host.E) * ((c₂ : D.host.K) : D.host.E) ∈ M := by
    intro c₁ h₁ c₂ h₂
    have hm : c₂ * (τ • c₁) ∈ cc * (τ • cc) := Ideal.mul_mem_mul h₂ (Ideal.smul_mem_pointwise_smul _ _ _ h₁)
    rw [hI, Ideal.mem_span_singleton'] at hm
    obtain ⟨k, hk⟩ := hm
    have hE : D.host.conj ((c₁ : D.host.K) : D.host.E) * ((c₂ : D.host.K) : D.host.E) = (iK k : D.host.E) * N := by
      rw [hiK, ← hsm, mul_comm, hN]
      have := congrArg (fun y : 𝓞 D.host.K => ((y : D.host.K) : D.host.E)) hk
      simp only [map_mul, map_natCast] at this
      push_cast at this ⊢
      rw [← this]
    rw [hE]
    exact Submodule.mem_span_singleton.mpr ⟨iK k, rfl⟩
  have hpart : ∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, D.host.conj α * β ∈ M := by
    intro α hα β hβ
    induction hα using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c₁, h₁, rfl⟩ := hx
      have hle : GlobalTheory.VacRead.cE D cc ≤ M.comap (LinearMap.mulLeft (𝓞 D.host.E) (D.host.conj ((c₁ : D.host.K) : D.host.E))) := by
        refine Submodule.span_le.mpr ?_
        rintro y ⟨c₂, h₂, rfl⟩
        exact hgen c₁ h₁ c₂ h₂
      exact hle hβ
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), add_mul]; exact M.add_mem hx hy
    | smul o x _ hx =>
      have : D.host.conj (o • x) * β = (RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) o) • (D.host.conj x * β) := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
        rfl
      rw [this]
      exact M.smul_mem _ hx
  refine ⟨fun α hα β hβ => ?_, ?_⟩
  · obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.mp (hpart α hα β hβ)
    exact ⟨o, by rw [← ho, Algebra.smul_def, mul_comm]⟩
  · have hNK : ((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) ∈ cc * (τ • cc) := by
      rw [hI]; exact Ideal.mem_span_singleton_self _
    have hcoe : N = ((((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E) := by
      rw [hN]; push_cast; rfl
    rw [hcoe]
    refine Submodule.mul_induction_on hNK ?_ ?_
    · intro a ha b hb
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
      have hb' : b = τ • (τ⁻¹ • b) := by rw [smul_inv_smul]
      refine Submodule.subset_span ⟨((τ⁻¹ • b : 𝓞 D.host.K) : D.host.K), Submodule.subset_span ⟨_, hb, rfl⟩,
        ((a : D.host.K) : D.host.E), Submodule.subset_span ⟨a, ha, rfl⟩, ?_⟩
      conv_lhs => rw [hb']
      rw [← hsm]
      push_cast
      ring
    · intro x y hx hy
      push_cast
      exact Submodule.add_mem _ hx hy

end GlobalTheory.VacRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNormStatement
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealExtend_conj_mul_eq_absNorm : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)), (∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, ∃ o : 𝓞 D.host.E, D.host.conj α * β = (Ideal.absNorm cc : D.host.E) * (o : D.host.E)) ∧ (Ideal.absNorm cc : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t | ∃ α ∈ GlobalTheory.VacRead.cE D cc, ∃ β ∈ GlobalTheory.VacRead.cE D cc, t = D.host.conj α * β} := by
  first | exact @GlobalTheory.VacRead.conj_mul_cE_absNorm | exact GlobalTheory.VacRead.conj_mul_cE_absNorm | (intros; apply GlobalTheory.VacRead.conj_mul_cE_absNorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupProperties
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {j m : ℕ}
  {C D : Matrix (Fin n) (Fin j) E} {Z : Matrix (Fin n) (Fin m) E} {J₀ : Matrix (Fin m) (Fin m) E}

theorem Fr.invol (hF : Fr σ J C D Z J₀) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hF.cm.2.2.2, hF.cm.2.2.2, star_star])

theorem Fr.isIsoCols (hF : Fr σ J C D Z J₀) : IsIsoCols σ J C := by
  refine ⟨Matrix.mulVec_injective_iff.1 ?_, hF.cc⟩
  intro v w h
  have := congrArg ((cT (σ : E →+* E) D * J) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, hF.dc, Matrix.one_mulVec] using this

theorem isClosed_fixG' {k : ℕ} (X : Matrix (Fin n) (Fin k) E) : IsClosed (fixG σ J X : Set (GAd σ J)) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : T2Space (AF F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have hm : Continuous fun g : GAd σ J => (matHom _ σ J g).1 := Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq (hm.matrix_mul continuous_const) continuous_const

theorem unipRad_le_fixG' (X : Matrix (Fin n) (Fin j) E) : unipRad σ J X ≤ fixG σ J X := by
  rw [unipRad, Subgroup.closure_le]
  intro g hg
  obtain ⟨h, -, -⟩ := hg
  show _ * _ = _
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h

theorem unipRad_onZ (hF : Fr σ J C D Z J₀) {g : GAd σ J} (hg : g ∈ unipRad σ J C) :
    ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J g).1 * adMat F Z = adMat F Z + adMat F C * b := by
  unfold unipRad at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨-, -, h3⟩ := hx
    choose a ha using fun k : Fin m => h3 (fun i => Z i k) (funext fun i => congrFun (congrFun hF.cz i) k)
    have e : ((matHom _ σ J x).1 - 1) * adMat F Z = adMat F C * Matrix.of fun i k => a k i :=
      Matrix.ext fun i k => congrFun (ha k) i
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add'] at e
    exact ⟨_, e⟩
  | one => exact ⟨0, by simp⟩
  | mul x y hxm _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := unipRad_le_fixG' (σ := σ) (J := J) C hxm
    refine ⟨b + b', ?_⟩
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb', Matrix.mul_add, hb, ← Matrix.mul_assoc, hxC, Matrix.mul_add,
      add_assoc]
  | inv x hxm hx =>
    obtain ⟨b, hb⟩ := hx
    have hi : (matHom _ σ J x⁻¹).1 * (matHom _ σ J x).1 = 1 := Units.inv_mul x.1
    have hxC : (matHom _ σ J x⁻¹).1 * adMat F C = adMat F C :=
      unipRad_le_fixG' (σ := σ) (J := J) C (inv_mem (show x ∈ unipRad σ J C from hxm))
    have e : (matHom _ σ J x⁻¹).1 * ((matHom _ σ J x).1 * adMat F Z) = (matHom _ σ J x⁻¹).1 * (adMat F Z + adMat F C * b) :=
      congrArg _ hb
    rw [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_add, ← Matrix.mul_assoc, hxC] at e
    refine ⟨-b, ?_⟩
    rw [Matrix.mul_neg, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq e.symm

theorem unipRad_inf_fixG (hF : Fr σ J C D Z J₀) (g : GAd σ J) (hu : g ∈ unipRad σ J C)
    (hg : g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) : g = 1 := by
  obtain ⟨b, hb⟩ := unipRad_onZ hF hu
  have hC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg.1
  have hD : (matHom _ σ J g).1 * adMat F D = adMat F D := hg.2
  have hD1 : (matHom _ σ J g).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by rw [Matrix.mul_one]; exact hD
  have e := form_mul_of_mul_cols hD1
  rw [Formalism.UG.cT_one, Matrix.one_mul] at e
  have hi : (matHom _ σ J g⁻¹).1 * (matHom _ σ J g).1 = 1 := Units.inv_mul g.1
  have e2 : adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) D * J) := by
    conv_lhs => rw [← e, Matrix.mul_assoc, hi, Matrix.mul_one]
  have hb0 : b = 0 := by
    have h : adMat F (cT (σ : E →+* E) D * J) * ((matHom _ σ J g).1 * adMat F Z) =
        adMat F (cT (σ : E →+* E) D * J) * (adMat F Z + adMat F C * b) := congrArg _ hb
    have hdc : adMat F (cT (σ : E →+* E) D * J) * adMat F C = 1 := by
      rw [adMat, adMat, ← Matrix.map_mul, hF.dc, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.mul_assoc, e2, Matrix.mul_add, ← Matrix.mul_assoc, hdc, Matrix.one_mul] at h
    calc b = (adMat F (cT (σ : E →+* E) D * J) * adMat F Z + b) -
          adMat F (cT (σ : E →+* E) D * J) * adMat F Z := by abel
      _ = 0 := by rw [← h, sub_self]
  rw [hb0, Matrix.mul_zero, add_zero] at hb
  have key : ∀ h : GAd σ J, (matHom _ σ J h).1 =
      (matHom _ σ J h).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J) +
      (matHom _ σ J h).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (matHom _ σ J h).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
    intro h
    have e : (matHom _ σ J h).1 = (matHom _ σ J h).1 * adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) := by
      rw [hF.sum, adMat, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    conv_lhs => rw [e]
    simp only [adMat, Matrix.map_add (inclR (F := F) (E := E) (AF F)) (map_add _), Matrix.map_mul, Matrix.mul_add,
      Matrix.mul_assoc]
  apply matHom_injective _ σ J
  apply Units.ext
  have k1 := key 1
  simp only [map_one, Units.val_one, Matrix.one_mul] at k1
  rw [key g, hC, hb, hD, map_one, Units.val_one]
  exact k1.symm

theorem frame_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → IsIsoCols σ J C ∧ IsClosed (fixG σ J C : Set (GAd σ J)) ∧ IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) ∧ IsClosed (unipRad σ J C : Set (GAd σ J)) ∧ unipRad σ J C ≤ fixG σ J C ∧ fixG σ J C ≤ parFlag σ J C (fun _ => 0) ∧ (∀ g ∈ unipRad σ J C, g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) → g = 1) ∧ (∀ p ∈ parFlag σ J C (fun _ => 0), ∀ u, u ∈ unipRad σ J C ↔ p * u * p⁻¹ ∈ unipRad σ J C) ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → p ∈ parFlag σ J C (fun _ => 0) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  have hJ := hF.herm
  have hσ := hF.invol
  have hIC := hF.isIsoCols
  refine ⟨hIC, isClosed_fixG' C, ?_, ?_, unipRad_le_fixG' C, ?_, unipRad_inf_fixG hF, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact (isClosed_fixG' C).inter (isClosed_fixG' D)
  · rw [← unipFlag_const C 0]; exact isClosed_unipFlag hJ hσ hIC _
  · intro g hg
    have hg' : g⁻¹ ∈ fixG σ J C := inv_mem hg
    refine ⟨⟨1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩, 1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩
    · rw [Matrix.mul_one]; exact hg
    · rw [Matrix.mul_one]; exact hg'
  · intro p hp u
    rw [← unipFlag_const C 0]
    exact ⟨fun hu => conj_mem_unipFlag hJ hσ hIC _ hp hu, fun hu => by
      have := conj_mem_unipFlag hJ hσ hIC _ (inv_mem hp) hu
      simpa [mul_assoc] using this⟩
  · intro p β h
    have hi : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := Units.inv_mul p.1
    have hb : β.1 * (β⁻¹).1 = 1 := Units.mul_inv β
    refine ⟨⟨β.1, fun _ _ h => absurd h (lt_irrefl 0), h⟩, (β⁻¹).1, fun _ _ h => absurd h (lt_irrefl 0), ?_⟩
    calc (matHom _ σ J p⁻¹).1 * adMat F C = (matHom _ σ J p⁻¹).1 * (adMat F C * (β.1 * (β⁻¹).1)) := by
          rw [hb, Matrix.mul_one]
      _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * adMat F C * (β⁻¹).1 := by
          rw [← Matrix.mul_assoc (adMat F C), ← h]; simp only [Matrix.mul_assoc]
      _ = adMat F C * (β⁻¹).1 := by rw [hi, Matrix.one_mul]

end GlobalTheory.SphEis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupPropertiesStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFrameDecomposition_subgroup_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → IsIsoCols σ J C ∧ IsClosed (fixG σ J C : Set (GAd σ J)) ∧ IsClosed ((fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) : Set (GAd σ J)) ∧ IsClosed (unipRad σ J C : Set (GAd σ J)) ∧ unipRad σ J C ≤ fixG σ J C ∧ fixG σ J C ≤ parFlag σ J C (fun _ => 0) ∧ (∀ g ∈ unipRad σ J C, g ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) → g = 1) ∧ (∀ p ∈ parFlag σ J C (fun _ => 0), ∀ u, u ∈ unipRad σ J C ↔ p * u * p⁻¹ ∈ unipRad σ J C) ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → p ∈ parFlag σ J C (fun _ => 0) := by
  first | exact @GlobalTheory.SphEis.frame_facts | exact GlobalTheory.SphEis.frame_facts | (intros; apply GlobalTheory.SphEis.frame_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelChartSupportedMulFormEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelFnMulEqZeroOfIsForm
set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

theorem delAt_eq_zero_of_eventually {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) : delAt F v = 0 := by
  have hS : ∀ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v = 0 := fun S => by
    have e : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => 0 := h.mono fun x hx => by simp [hx]
    rw [GlobalTheory.del_congr e]
    exact GlobalTheory.del_const _ _
  simp [delAt, coefwise, hS]

theorem del_integral {f : V n → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (u : V n) :
    Integrable (fun v => GlobalTheory.del f v u) ∧ ∫ v, GlobalTheory.del f v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ f y w) := fun w =>
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  have hD : Integrable (fun v => GlobalTheory.del f v u) := by
    simp only [GlobalTheory.del_apply, smul_eq_mul]
    exact ((hint _).sub ((hint _).const_mul _)).const_mul _
  refine ⟨hD, ?_⟩
  simp only [GlobalTheory.del_apply, smul_eq_mul]
  rw [integral_const_mul, integral_sub (hint _) ((hint _).const_mul _), integral_const_mul,
    ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc, ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc]
  simp

theorem dens_delAt (F : V n → Alt n) (v : V n) : dens (delAt F v) =
    ∑ a, ∑ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dens, delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_dens_delAt {F : V n → Alt n} (hF : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S)
    (hc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S) :
    Integrable (fun v => dens (delAt F v)) ∧ ∫ v, dens (delAt F v) = 0 := by
  have hi : ∀ a S, Integrable fun v => GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) :=
    fun a S => (del_integral (hF S) (hc S) _).1.mul_const _
  simp only [dens_delAt]
  refine ⟨integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S, ?_⟩
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [integral_mul_const, (del_integral (hF S) (hc S) _).2, zero_mul]

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_eq_of_vanish {M : Type} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α) (i : A.ι) {K : Set M} (hKm : MeasurableSet K)
    (hKs : K ⊆ (A.e i).source) (h0 : ∀ x : A.Pt, x.pt ∉ K → α x = 0)
    (hI : Integrable fun v => (dens (A.loc α i v)).re) :
    A.integral α = ∫ v, (dens (A.loc α i v)).re := by
  have hl : ∀ j y (hy : y ∈ (A.e j).source), A.loc α j (A.e j y) = α ⟨(j, y), hy⟩ := fun j y hy =>
    A.loc_crd α ⟨(j, y), hy⟩
  have hρ : ∀ (ε : ℤˣ) j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) =
      ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) *
        ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α k (A.e k y))).re) := by
    intro ε j k y hj hk
    rw [hl j y hj, hl k y hk, hα.compat ⟨(j, y), hj⟩ ⟨(k, y), hk⟩ rfl, dens_pull,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    simp only [ChartGlue.transDet, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hz : ∀ (ε : ℤˣ) j y, y ∈ (A.e j).source → y ∉ K →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) = 0 := by
    intro ε j y hy hyK
    rw [hl j y hy, h0 ⟨(j, y), hy⟩ hyK, dens_zero]
    simp
  have hc : ∀ ε : ℤˣ, A.part α ε Kᶜ = 0 := fun ε => by
    have key : A.part α ε ≤ (A.part α ε).restrict K := iSup_le fun j => by
      have e : ChartGlue.chartMeas (A.e j)
          (fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) Kᶜ = 0 := by
        rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
        refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
          ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
        rintro _ ⟨y, hy, rfl⟩
        simp only [(A.e j).left_inv hy.1]
        exact hz ε j y hy.1 hy.2
      rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
      exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j)
        fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) j)
    refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
    rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
  have hv : ∀ v, v ∉ (A.e i) '' K → (dens (A.loc α i v)).re = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht, h0 ⟨(i, (A.e i).symm v), (A.e i).map_target ht⟩
        fun h => hv ⟨_, h, (A.e i).right_inv ht⟩, dens_zero, Complex.zero_re]
    · rw [HolAtlas.loc, dite_eq_right ht, dens_zero, Complex.zero_re]
  have hp : ∀ ε : ℤˣ, A.part α ε univ = ∫⁻ v, ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α i v)).re) := fun ε => by
    rw [← measure_add_measure_compl hKm, hc ε, add_zero, HolAtlas.part,
      ChartGlue.glueMeas_apply A.e _ (fun j k => A.holo j k) (hρ ε) i hKm hKs,
      ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs,
      ← lintegral_indicator (ChartGlue.measurableSet_image _ hKm hKs)]
    refine lintegral_congr fun v => ?_
    by_cases hvK : v ∈ (A.e i) '' K
    · obtain ⟨y, hy, rfl⟩ := hvK
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), (A.e i).left_inv (hKs hy)]
    · rw [Set.indicator_of_notMem hvK, hv v hvK, mul_zero, ENNReal.ofReal_zero]
  rw [HolAtlas.integral, measureReal_def, measureReal_def, hp, hp,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
  simp

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_del_fn_mul_eq_zero_of_isForm {M : Type} [TopologicalSpace M] [CompactSpace M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M n) (γ : A.Fld) (χ : M → ℝ)
    (i : A.ι) (hγ : A.IsForm γ) (hχ : A.SmoothOn univ (fun y => (χ y : ℂ))) (hs : tsupport χ ⊆ (A.e i).source)
    (hd : A.IsForm (A.del (A.fn χ * γ))) : A.integral (A.del (A.fn χ * γ)) = 0 := by
  set β : A.Fld := A.fn χ * γ with hβdef
  set K : Set M := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have hKm : MeasurableSet K := (isClosed_tsupport χ).measurableSet
  have hβ : A.IsForm β := FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hγ
  have hβ0 : ∀ x : A.Pt, x.pt ∉ K → β x = 0 := fun x hx => by
    simp [hβdef, HolAtlas.fn, image_eq_zero_of_notMem_tsupport hx]

  have hβn : ∀ j, ∀ y ∈ (A.e j).source, y ∉ K → A.loc β j =ᶠ[𝓝 (A.e j y)] fun _ => 0 := fun j y hy hyK => by
    filter_upwards [(ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl).mem_nhds
      (ChartGlue.mem_over (A.e j) (S := Kᶜ) hy hyK)] with w hw
    rw [HolAtlas.loc, dite_eq_left hw.1]
    exact hβ0 _ hw.2
  have hd0 : ∀ x : A.Pt, x.pt ∉ K → A.del β x = 0 := fun x hx =>
    delAt_eq_zero_of_eventually (hβn x.1.1 x.pt x.2 hx)

  set F : V n → Alt n := A.loc β i with hFdef
  set AK : Set (V n) := (A.e i) '' K with hAKdef
  have hAK : IsCompact AK := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hs)
  have hAKt : AK ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hs hy)
  have hF0 : ∀ v ∉ AK, F v = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [hFdef, HolAtlas.loc, dite_eq_left ht]
      exact hβ0 _ fun h => hv ⟨_, h, (A.e i).right_inv ht⟩
    · rw [hFdef, HolAtlas.loc, dite_eq_right ht]
  have hFA : ∀ v ∉ AK, F =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hAK.isClosed.isOpen_compl.mem_nhds hv] with w hw
    exact hF0 w hw
  have hFS : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S := fun S => contDiff_iff_contDiffAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact ((hβ.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by simp)
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ((hFA v fun h => ht (hAKt h)).mono fun w hw => ?_)
      simp [hw]
  have hFc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S := fun S =>
    HasCompactSupport.intro hAK fun v hv => by simp [hF0 v hv]
  have hloc : ∀ v, A.loc (A.del β) i v = delAt F v := fun v => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dite_eq_left ht]
      show delAt (A.loc β i) ((A.e i) ((A.e i).symm v)) = _
      rw [(A.e i).right_inv ht]
    · rw [HolAtlas.loc, dite_eq_right ht]
      exact (delAt_eq_zero_of_eventually (hFA v fun h => ht (hAKt h))).symm
  obtain ⟨hI, h0⟩ := integral_dens_delAt hFS hFc
  have hIre : Integrable fun v => (dens (A.loc (A.del β) i v)).re := by
    simp only [hloc]
    exact Complex.reCLM.integrable_comp hI
  rw [integral_eq_of_vanish A hd i hKm hs hd0 hIre]
  simp only [hloc]
  have := Complex.reCLM.integral_comp_comm hI
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm.LocStokes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelChartSupportedMulFormEqZero
set_option autoImplicit false

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.LocStokes

theorem integral_del_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.del (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hs
  exact integral_del_fn_mul_eq_zero_of_isForm A γ χ i hγ hχ hs
    (GlobalTheory.T.holAtlas_isForm_del A _ (FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hγ))

end GlobalTheory.CxForm.LocStokes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelChartSupportedMulFormEqZeroStatement
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.del (A.fn χ * γ)) = 0 := by
  first | exact @GlobalTheory.CxForm.LocStokes.integral_del_fn_mul_eq_zero | exact GlobalTheory.CxForm.LocStokes.integral_del_fn_mul_eq_zero | (intros; apply GlobalTheory.CxForm.LocStokes.integral_del_fn_mul_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneJacobianIdentity
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.ThK.CuspTransfer.Smooth


end GlobalTheory.ThK.CuspTransfer.Smooth

open GlobalTheory.SiegelSet (IsRealLine)
open GlobalTheory.Orb (archMat IsSmoothRealFam)

namespace GlobalTheory.ThK.CuspTransfer.Smooth

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem line_fam (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : IsSmoothRealFam γ ∧ Continuous γ := by
  obtain ⟨w, τ, Z, -, hγ⟩ := hγ
  choose y e1 e2 using hγ
  obtain rfl : γ = fun t => embArch σ J w (y t) := funext e1
  exact GlobalTheory.Orb.isSmoothRealFam_embArch h τ fun i j => by
    simp only [e2]; exact GlobalTheory.Orb.contDiff_exp_smul_entry Z i j





end GlobalTheory.ThK.CuspTransfer.Smooth


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSkewA
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.ResidueEisenstein.ModConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def skewA (σ : E →ₐ[F] E) (j : ℕ) : AddSubgroup (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) where
  carrier := {c | c + cT (sigR (AF F) σ) c = 0}
  add_mem' := fun {a b} ha hb => by
    have e : cT (sigR (AF F) σ) (a + b) = cT (sigR (AF F) σ) a + cT (sigR (AF F) σ) b :=
      Matrix.ext fun i k => by simp [cT]
    change a + b + cT _ (a + b) = 0
    change a + cT _ a = 0 at ha
    change b + cT _ b = 0 at hb
    rw [e, add_add_add_comm, ha, hb, add_zero]
  zero_mem' := by
    change (0 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) + cT _ 0 = 0
    ext i k; simp [cT]
  neg_mem' := fun {a} ha => by
    have e : cT (sigR (AF F) σ) (-a) = -cT (sigR (AF F) σ) a := Matrix.ext fun i k => by simp [cT]
    change -a + cT _ (-a) = 0
    change a + cT _ a = 0 at ha
    rw [e, ← neg_add, ha, neg_zero]

theorem mem_skewA {σ : E →ₐ[F] E} {j : ℕ} {c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)} :
    c ∈ skewA σ j ↔ c + cT (sigR (AF F) σ) c = 0 := Iff.rfl

end GlobalTheory.ResidueEisenstein.ModConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalHeisenbergEndomorphism
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertRho

theorem exists_rho : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∃ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      ∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC
  obtain ⟨-, -, -, -, -, -, -, -, -, hAt, -⟩ := hC
  have hstd := hTr.base.std
  let ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)) := fun x =>
    { toFun := fun m => ⟨schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (κ x)) m,
        GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v _ _ m.2⟩
      map_add' := fun m m' => by
        ext y
        simp only [schr, Submodule.coe_add, Pi.add_apply]
        ring
      map_smul' := fun c m => by
        ext y
        simp only [schr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  exact ⟨ρ, fun x m => GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v (κ x) (hAt x) m⟩

end GlobalTheory.InertRho

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NrmOneNonneg
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nrm_one_nonneg {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (v : VV ℂ lam) :
    0 ≤ nrm lam (fun _ => 1) v := by
  by_cases hv : v = 0
  · simp [nrm, hv]
  · exact (Complex.le_def.1 (GlobalTheory.CoefModel.pairK_pos lam (fun _ => Matrix.PosDef.one) v hv).le).1

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b C1 : ℝ)

def RatRowAt : Prop := ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m),
  ∃ f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m)), ∀ u,
    ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)

def ConjRowAt : Prop := ∃ a0 nD Gd : ℝ, 0 ≤ a0 ∧ 0 ≤ nD ∧ 0 ≤ Gd ∧ 2 * a0 + (nD + Gd) * C1 * Real.log b ≤ aOne ch.G C b ∧
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.grid i D.R.m)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.grid (i + 1) D.R.m))),
    (∀ u, ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ, ∀ u (B : ℝ),
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ u) ≤ B →
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (σ.comp (starRingEnd D.what₂.LL)) _ (f u)) ≤
        Real.exp (a0 + nD * hArea D ch.S.Z.δ ch.S.Z.t0 ρ + Gd * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) * B

end Claims

end GlobalTheory.KerConjMean

end
end
