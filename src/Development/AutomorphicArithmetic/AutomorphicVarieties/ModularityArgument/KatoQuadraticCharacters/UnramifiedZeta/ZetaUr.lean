module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.KatoGlobalUnitLawOfSmoothedClasses
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormFactorLeOne
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.AdmissibleWeightedDataMonoCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SmoothedZetaClasses.SmoothedZetaClassHodgeTateLaw
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRestrict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdmissibleHeckeProjectionNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesRingHomPadicAlgCl
open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.HV

namespace GlobalTheory

namespace PowerSeriesEvalAlgCl

theorem isIntegral_iff_norm_le_one {l : ℕ} [Fact l.Prime] (y : PadicAlgCl l) :
    IsIntegral ℤ_[l] y ↔ ‖y‖ ≤ 1 := by
  have hm : (minpoly ℚ_[l] y).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  have key : ‖y‖ ≤ 1 ↔ ∀ n, ‖(minpoly ℚ_[l] y).coeff n‖ ≤ 1 := spectralValue_le_one_iff hm
  rw [key]
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · obtain ⟨q, hq, -, hq'⟩ := lifts_and_degree_eq_and_monic
      ((lifts_iff_coeff_lifts (f := algebraMap ℤ_[l] ℚ_[l]) _).2 fun n => ⟨⟨_, h n⟩, rfl⟩) hm
    refine ⟨q, hq', ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq]
    exact minpoly.aeval ℚ_[l] y

theorem exists_coef_ge_finset {l : ℕ} [Fact l.Prime] (c : Coef l) (s : Finset (PadicAlgCl l))
    (hs : ∀ y ∈ s, IsIntegral ℤ_[l] y) : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ y ∈ s, y ∈ c'.O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c₁, h₁, h₂⟩ := ih fun y hy => hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨c₂, h₃, h₄⟩ := (coefSup l).2.2.1 c₁ a (hs a (Finset.mem_insert_self _ _))
    refine ⟨c₂, h₁.trans h₃, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact h₄
    · exact h₃ (h₂ y hy)

end PowerSeriesEvalAlgCl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyPolyOfStable
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInertiaFixedNearAlmostFixedCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInertiaFixedNearAlmostFixedCoefficients
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.PerFix

variable {l : ℕ} [Fact l.Prime]

theorem norm_aut (σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (y : Qbar l) : ‖σ y‖ = ‖y‖ :=
  (spectralNorm_eq_of_equiv σ y).symm

def inertiaC (c : Coef l) : Subgroup (Qbar l ≃ₐ[ℚ_[l]] Qbar l) where
  carrier := {σ | (∀ b ∈ c.O, σ b = b) ∧ ∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := ⟨fun b _ => rfl, fun y _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ1, hσ2⟩ ⟨hτ1, hτ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ (τ b) = b
      rw [hτ1 b hb, hσ1 b hb]
    · show ‖σ (τ y) - y‖ < 1
      have e : σ (τ y) - y = (σ (τ y) - τ y) + (τ y - y) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hσ2 _ ((norm_aut τ y).le.trans hy)) (hτ2 y hy))
  inv_mem' := by
    rintro σ ⟨hσ1, hσ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ.symm b = b
      exact σ.symm_apply_eq.2 (hσ1 b hb).symm
    · show ‖σ.symm y - y‖ < 1
      have e : σ.symm y - y = σ.symm (y - σ y) := by simp
      rw [e, norm_aut, norm_sub_rev]
      exact hσ2 y hy

theorem exists_fixed_near : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  intro l _ c
  obtain ⟨C, -, hC⟩ := GlobalTheory.AxLemma.ax_lemma l
  have hl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    rw [show ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : Qbar l) from (map_natCast _ _).symm,
      PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt C hl1
  refine ⟨c₁, fun k x hx hfix => ?_⟩
  by_cases hk : k ≤ c₁
  · refine ⟨0, by simp, fun σ _ _ => map_zero σ, ?_⟩
    have h0 : k - c₁ = 0 := by omega
    simpa [Cg, h0] using hx
  · obtain ⟨y, hyH, hxy⟩ := hC (inertiaC c) x ‖((l : ℕ) : Qbar l) ^ k‖ (fun g hg => hfix g hg.1 hg.2)
    have hlpos : (0 : ℝ) < l := by linarith
    have key : C * ‖((l : ℕ) : Qbar l) ^ k‖ ≤ ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ := by
      rw [norm_pow, norm_pow, hl]
      have e : (l : ℝ)⁻¹ ^ k = (l : ℝ)⁻¹ ^ (k - c₁) * (l : ℝ)⁻¹ ^ c₁ := by
        rw [← pow_add]; congr 1; omega
      rw [e, mul_comm, mul_assoc]
      apply mul_le_of_le_one_right (by positivity)
      rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
      linarith
    have hxy' := hxy.trans key
    have hle1 : ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ ≤ 1 := by
      rw [norm_pow, hl]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hl1.le)
    refine ⟨y, ?_, fun σ h1 h2 => hyH σ ⟨h1, h2⟩, hxy'⟩
    have e : y = x + (y - x) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx ((norm_sub_rev y x).le.trans (hxy'.trans hle1)))

end GlobalTheory.PerFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInertiaFixedNearAlmostFixedCoefficientsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertiaFixed_near_almostFixed_coefficients : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  first | exact @GlobalTheory.PerFix.exists_fixed_near | exact GlobalTheory.PerFix.exists_fixed_near | (intros; apply GlobalTheory.PerFix.exists_fixed_near <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois
open scoped TensorProduct MatrixGroups Matrix
open GlobalTheory.LambdaValuationPowers

namespace GlobalTheory.LamChi

open GlobalTheory.LamPr

variable {l : ℕ} [Fact l.Prime]

theorem norm_aut (τ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (x : Qbar l) : ‖τ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv τ x).symm

theorem norm_l_pow_mul (k : ℕ) : ‖((l : ℕ) : Qbar l) ^ k‖ * (l : ℝ) ^ k = 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  have h0 : (l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [norm_pow, h, norm_algebraMap', Padic.norm_p, ← mul_pow, inv_mul_cancel₀ h0, one_pow]

theorem exists_fixed_near (c : Coef l) (y : ℂ_[l]) (C : ℝ)
    (hx : ∀ n : ℕ, ∃ x : Qbar l, ‖x‖ ≤ C ∧ ‖(x : ℂ_[l]) - y‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖ ∧
      ∀ τ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, τ b = b) → (∀ z : Qbar l, ‖z‖ ≤ 1 → ‖τ z - z‖ < 1) →
        ‖τ x - x‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ n‖) (δ : ℝ) (hδ : 0 < δ) :
    ∃ z : Qbar l, FixIc c z ∧ ‖(z : ℂ_[l]) - y‖ ≤ δ := by
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_inertiaFixed_near_almostFixed_coefficients l c
  obtain ⟨k, hk⟩ := exists_le_l_pow l C
  have ht : Filter.Tendsto (fun n : ℕ => (l : ℝ) ^ k * (l : ℝ) ^ c₁ * ‖((l : ℕ) : Qbar l) ^ n‖) Filter.atTop (nhds 0) := by
    simp_rw [norm_pow]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_l_lt_one (l := l))).const_mul
      ((l : ℝ) ^ k * (l : ℝ) ^ c₁)
  obtain ⟨n, hn, hnc⟩ := ((ht.eventually (ge_mem_nhds hδ)).and (Filter.eventually_ge_atTop c₁)).exists
  obtain ⟨x, h1, h2, h3⟩ := hx n
  have hlk : ((l : ℕ) : Qbar l) ^ k ≠ 0 := pow_ne_zero _ l_ne_zero
  have hm := norm_l_pow_mul (l := l) k
  have hkC : ‖((l : ℕ) : Qbar l) ^ k‖ * C ≤ 1 := hm ▸ mul_le_mul_of_nonneg_left hk (norm_nonneg _)
  obtain ⟨x', -, hf, hx'⟩ := hc₁ n (((l : ℕ) : Qbar l) ^ k * x)
    (by rw [norm_mul]; exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans hkC)
    (fun τ ha hb => by
      unfold Cg
      rw [map_mul, map_pow, map_natCast, ← mul_sub, norm_mul]
      refine (mul_le_mul_of_nonneg_left (h3 τ ha hb) (norm_nonneg _)).trans ?_
      rw [← mul_assoc]
      exact mul_le_of_le_one_left (norm_nonneg _) hkC)
  have h4 := (cg_sub_iff hnc _ _).1 hx'
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  have hc1 : (1 : ℝ) ≤ (l : ℝ) ^ c₁ := one_le_pow₀ hl1
  have hk0 : (0 : ℝ) ≤ (l : ℝ) ^ k := by positivity
  refine ⟨x' / ((l : ℕ) : Qbar l) ^ k, fun τ ha hb => by rw [map_div₀, map_pow, map_natCast, hf τ ha hb], ?_⟩
  have h5 : ‖x' / ((l : ℕ) : Qbar l) ^ k - x‖ ≤ δ := by
    have e : x' / ((l : ℕ) : Qbar l) ^ k - x = -((((l : ℕ) : Qbar l) ^ k * x - x') * (((l : ℕ) : Qbar l) ^ k)⁻¹) := by
      field_simp; ring
    rw [e, norm_neg, norm_mul, norm_inv, inv_eq_of_mul_eq_one_right hm, mul_comm]
    refine le_trans ?_ hn
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h4 hk0
  rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub] at h5
  have e : ((x' / ((l : ℕ) : Qbar l) ^ k : Qbar l) : ℂ_[l]) - y =
      (((x' / ((l : ℕ) : Qbar l) ^ k : Qbar l) : ℂ_[l]) - x) + ((x : ℂ_[l]) - y) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h5 (h2.trans (le_trans ?_ hn)))
  exact mul_le_mul_of_nonneg_right (hk.trans (le_mul_of_one_le_right hk0 hc1)) (norm_nonneg _)

theorem exists_fixed_period (c : Coef l) (y : ℂ_[l]) (hy : y ≠ 0)
    (h : ∀ δ : ℝ, 0 < δ → ∃ z : Qbar l, FixIc c z ∧ ‖(z : ℂ_[l]) - y‖ ≤ δ) :
    ∃ (a : Qbar l) (u : ℂ_[l]) (p : ℕ → Qbar l), y = u * a ∧ ‖u‖ = 1 ∧
      ∀ n, ‖p n‖ = 1 ∧ FixIc c (p n) ∧ ‖(p n : ℂ_[l]) - u‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hp : ∀ n : ℕ, 0 < ‖((l : ℕ) : Qbar l) ^ (n + 1)‖ := fun n => norm_pos_iff.2 (pow_ne_zero _ l_ne_zero)
  have h1 : ∀ n : ℕ, ‖((l : ℕ) : Qbar l) ^ (n + 1)‖ < 1 := fun n => by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) norm_l_lt_one (by omega)
  choose z hz hzy using fun n : ℕ => h _ (mul_pos (hp n) hy0)
  have hn : ∀ n, ‖(z n : ℂ_[l])‖ = ‖y‖ := fun n => by
    have hlt : ‖(z n : ℂ_[l]) - y‖ < ‖y‖ := (hzy n).trans_lt (mul_lt_of_lt_one_left hy0 (h1 n))
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (z n : ℂ_[l]) - y) (y := y) hlt.ne
    rwa [sub_add_cancel, max_eq_right hlt.le] at this
  have h0 : (z 0 : ℂ_[l]) ≠ 0 := by rw [← norm_ne_zero_iff, hn]; exact hy0.ne'
  have hd : ∀ n, ((z n / z 0 : Qbar l) : ℂ_[l]) = (z n : ℂ_[l]) / z 0 := fun n =>
    map_div₀ (algebraMap (Qbar l) ℂ_[l]) _ _
  refine ⟨z 0, y / z 0, fun n => z n / z 0, by field_simp, by rw [norm_div, hn, div_self hy0.ne'], fun n => ⟨?_, ?_, ?_⟩⟩
  · rw [← PadicComplex.norm_extends, hd, norm_div, hn, hn, div_self hy0.ne']
  · intro τ ha hb
    rw [map_div₀, hz n τ ha hb, hz 0 τ ha hb]
  · rw [hd, ← sub_div, norm_div, hn, div_le_iff₀ hy0]
    refine (hzy n).trans (mul_le_mul_of_nonneg_right ?_ hy0.le)
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) norm_l_lt_one.le (by omega)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def chiPart (X : Tower Ω ε) (N w : ℕ) (χ : ℕ → ℤ_[l]) : Submodule ℤ_[l] (X.Fn l) where
  carrier := {b | InChi X N w χ b}
  zero_mem' := ⟨Submodule.zero_mem _, fun d _ => by simp⟩
  add_mem' := fun ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun d hd => by rw [map_add (f := _), ha.2 d hd, hb.2 d hd, smul_add]⟩
  smul_mem' := fun r _ ha => ⟨Submodule.smul_mem _ r ha.1, fun d hd => by rw [map_smul, ha.2 d hd, smul_comm]⟩

theorem apply_poly_of_stable (X : Tower Ω ε) (N : ℕ) (B' : Submodule ℤ_[l] (X.Fn l))
    (hst : ∀ T, GlobalTheory.KZ.admitted N l T → ∀ b ∈ B', X.op N l T b ∈ B')
    (L : Qbar l ⊗[ℤ_[l]] X.Fn l →ₗ[Qbar l] ℂ_[l]) (ev : Letter → Qbar l)
    (hL : ∀ T, GlobalTheory.KZ.admitted N l T → ∀ b ∈ B', L (1 ⊗ₜ[ℤ_[l]] X.op N l T b) = ev T • L (1 ⊗ₜ[ℤ_[l]] b))
    (P : FreeAlgebra (Qbar l) Letter) (hP : P ∈ admissibleLettersSubalgebra (Qbar l) N l) (hP1 : FreeAlgebra.lift (Qbar l) ev P = 1)
    (x : Qbar l ⊗[ℤ_[l]] X.Fn l) (hx : x ∈ LinearMap.range (LinearMap.baseChange (Qbar l) B'.subtype)) :
    L (FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x) = L x := by
  have key : ∀ T, GlobalTheory.KZ.admitted N l T → ∀ y ∈ LinearMap.range (LinearMap.baseChange (Qbar l) B'.subtype),
      X.opV N l (Qbar l) T y ∈ LinearMap.range (LinearMap.baseChange (Qbar l) B'.subtype) ∧
        L (X.opV N l (Qbar l) T y) = ev T • L y := by
    rintro T hT _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      refine ⟨⟨a ⊗ₜ ⟨_, hst T hT b b.2⟩, by simp [Tower.opV]⟩, ?_⟩
      have e : ∀ z : X.Fn l, a ⊗ₜ[ℤ_[l]] z = a • ((1 : Qbar l) ⊗ₜ[ℤ_[l]] z) := fun z => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [Tower.opV, LinearMap.baseChange_tmul, Submodule.subtype_apply]
      rw [e, e (b : X.Fn l), map_smul, map_smul, hL T hT b b.2, smul_comm]
    | add y z hy hz =>
      simp only [map_add (f := _)]
      exact ⟨Submodule.add_mem _ hy.1 hz.1, by rw [hy.2, hz.2, smul_add]⟩
  have h := SSAdm.lift_sub_smul_mem (A := {T | GlobalTheory.KZ.admitted N l T}) (f := X.opV N l (Qbar l)) (lam := ev)
    (W := LinearMap.range (LinearMap.baseChange (Qbar l) B'.subtype) ⊓ LinearMap.ker L)
    (fun T hT y hy => ⟨(key T hT y hy.1).1, LinearMap.mem_ker.2 <| by
      rw [(key T hT y hy.1).2, LinearMap.mem_ker.1 hy.2, smul_zero]⟩) (x := x)
    (fun T hT => ⟨Submodule.sub_mem _ (key T hT x hx).1 (Submodule.smul_mem _ _ hx), LinearMap.mem_ker.2 <| by
      rw [map_sub, map_smul, (key T hT x hx).2, sub_self]⟩) hP
  have h2 := LinearMap.mem_ker.1 h.2
  rwa [hP1, one_smul, map_sub, sub_eq_zero] at h2

theorem act_sgD_one (X : Tower Ω ε) {N w : ℕ} (hN : N ≠ 0) {b : X.Fn l} (hb : b ∈ X.B N l w) :
    X.act l (sgD N l 1 : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  obtain ⟨⟨h0, h1⟩, h2⟩ := Betti.isDiam_sgD (d := 1) hN (Fact.out : l.Prime).ne_zero (Nat.coprime_one_left N)
  have h3 : (⟨sgD N l 1, h0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem']
    simpa [en, CongruenceSubgroup.Gamma0Map] using h2
  have hγ : sgD N l 1 ∈ Gam N l :=
    ⟨(CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3), h1⟩
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 _ hγ
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

theorem mem_Ine_of_restrict {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (τ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (hτ : ∀ z : Qbar l, ‖z‖ ≤ 1 → ‖τ z - z‖ < 1) (s : Ω ≃ₐ[ℚ] Ω)
    (hs : ∀ x, j (s x) = τ (j x)) : (∀ x, x ∈ A ↔ s x ∈ A) ∧ s ∈ Ine (F := ℚ) A := by
  have hsA : ∀ x, x ∈ A ↔ s x ∈ A := fun x => by rw [hj, hj, hs, norm_aut]
  refine ⟨hsA, mem_Dec.2 ?_, fun x hx => ?_⟩
  · ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hsA, AlgEquiv.smul_def]
    simp
  · have h := hτ _ ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
    rw [← hs, ← map_sub] at h
    rw [valuation_lt_one_iff', hj, hj]
    refine ⟨h.le, or_iff_not_imp_left.2 fun h0 => ?_⟩
    rw [map_inv₀, norm_inv, not_le]
    exact (one_lt_inv₀ (norm_pos_iff.2 ((map_ne_zero j).2 h0))).2 h

theorem exists_pr_isLamFR : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l w : ℕ)
  [Fact l.Prime] (j : Ω →+* Qbar l),
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → Odd w →
  (∀ x ∈ A, ‖j x‖ ≤ 1) →
  ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
  (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
  (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
    (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (w + 1)) →
  ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
    (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
  P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l w (Qbar l)) →
  (∀ i s, ∀ x ∈ X.VB N l w (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
  (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
  (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
  (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
  (∀ x ∈ X.VB N l w (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
  ∀ (χ : ℕ → ℤ_[l]) (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
  (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N w χ b →
    Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
  ∃ pr : X.Fn l → Fin 2 → Qbar l, (∃ κ : Fin m → Qbar l, ∀ b, pr b = ∑ i, κ i • π i ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)) ∧
    IsLamFR X A N w χ j pr c lam := by
  intro Ω _ _ _ ε X A N l w _ j hhol' hlA hl2 hlN hN hw hjA ev ρ F hDec hIne hsub m π σ P hP hP1 hσ hπg hσg _ _ hPσπ χ c lam
    hfin hwt heig
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hj := mem_iff_of_le hlA hjA
  have hhol : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := hhol'.imp fun _ h => h.symm
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hlN).symm
  have hth : ∀ n, ∀ b ∈ X.B N l w, IsThB X A N l n b (thN X A N l n 1 b) := fun n b hb => by
    have h := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l hhol' hl2 hlN hN hlA n w 1 hw (Nat.coprime_one_left N) b hb).1
    rwa [act_sgD_one X (by omega) hb] at h
  have hstB := GlobalTheory.KZ.B_stable_op ε X ε.injective hhol N l w hl2 hN hNl hw
  have hst : ∀ T, GlobalTheory.KZ.admitted N l T → ∀ b ∈ chiPart X N w χ, X.op N l T b ∈ chiPart X N w χ := fun T hT b hb =>
    ⟨hstB T hT b hb.1, fun d hd => by
      have h := GlobalTheory.KZ.B_op_comm ε X ε.injective hhol N l w hl2 hN hNl hw (Letter.D d) T hd hT b hb.1
      change X.diam N l d _ = X.op N l T (X.diam N l d b) at h
      rw [h, hb.2 d hd, map_smul]⟩
  have hstG : ∀ s, ∀ b ∈ chiPart X N w χ, X.galB l s b ∈ chiPart X N w χ := fun s b hb =>
    ⟨GlobalTheory.KZ.StabGal.galB_mem_B ε X ε.injective hhol N l w hl2 hN hNl hw s b hb.1, fun d hd => by
      have h := GlobalTheory.KZ.HeckeGal.op_galB_comm ε X ε.injective hhol N l w hl2 hN hNl hw (Letter.D d) hd s b hb.1
      change X.diam N l d _ = X.galB l s (X.diam N l d b) at h
      rw [h, hb.2 d hd, map_smul]⟩
  have hVB : ∀ b ∈ X.B N l w, (1 : Qbar l) ⊗ₜ[ℤ_[l]] b ∈ X.VB N l w (Qbar l) := fun b hb => ⟨1 ⊗ₜ ⟨b, hb⟩, by simp⟩
  obtain ⟨C, hC, -⟩ := exists_bound hfin
  obtain ⟨L, κ, per, hL, hb, hper, hLσ⟩ :=
    exists_period X A j hj hhol N w 1 hl2 hN hNl hw lam hfin C hC ρ
      ⟨F, fun s hs hsF => ⟨hDec s (Ine_le_Dec A hs), by
        rw [map_pow, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
        simpa using hsub s hs hsF⟩⟩ m σ hσ hσg
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hb 0 (Submodule.zero_mem _))

  have hLT : ∀ T, GlobalTheory.KZ.admitted N l T → ∀ b ∈ chiPart X N w χ,
      L (1 ⊗ₜ[ℤ_[l]] X.op N l T b) = ev T • L (1 ⊗ₜ[ℤ_[l]] b) := by
    intro T hT b hbB
    obtain ⟨c₂, hc⟩ := heig
    rw [← sub_eq_zero]
    refine eq_zero_of_le (C := C + (l : ℝ) ^ c₂ + ‖ev T‖ * C) (c := c₂) fun n hn => ?_
    have h1 := hL n _ (hstB T hT b hbB.1) _ (hth n _ (hstB T hT b hbB.1))
    have h2 := (cg_sub_iff hn _ _).1 (hc n hn T b hT hbB)
    have h3 := mul_le_mul_of_nonneg_left (hL n b hbB.1 _ (hth n b hbB.1)) (norm_nonneg (ev T))
    set φ := thN X A N l n 1 b
    set φ' := thN X A N l n 1 (X.op N l T b)
    rw [← PadicComplex.norm_extends] at h2
    rw [← PadicComplex.norm_extends l (ev T), ← norm_mul, PadicComplex.norm_extends] at h3
    have e : L (1 ⊗ₜ[ℤ_[l]] X.op N l T b) - ev T • L (1 ⊗ₜ[ℤ_[l]] b) =
        -((lam (seqN 1 j φ') : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] X.op N l T b)) +
          ((lam (seqN 1 j φ') - ev T * lam (seqN 1 j φ) : Qbar l) : ℂ_[l]) +
          (ev T : ℂ_[l]) * ((lam (seqN 1 j φ) : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)) := by
      rw [Algebra.smul_def, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul]
      change _ - (ev T : ℂ_[l]) * _ = _
      ring
    rw [e]
    refine norm_add₃_le.trans ?_
    rw [norm_neg]
    nlinarith
  set pr : X.Fn l → Fin 2 → Qbar l := fun b => ∑ i, κ i • π i (1 ⊗ₜ[ℤ_[l]] b) with hpr
  have hLpr : ∀ b ∈ chiPart X N w χ, L (1 ⊗ₜ[ℤ_[l]] b) = per * ((pr b 1 : Qbar l) : ℂ_[l]) := by
    intro b hbB
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← apply_poly_of_stable X N (chiPart X N w χ) hst L ev hLT P hP hP1 ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b)
      ⟨1 ⊗ₜ ⟨b, hbB⟩, by simp⟩, hPσπ _ (hVB b hbB.1), map_sum]
    simp only [hLσ, hpr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    congr 1
    exact (map_sum (algebraMap (Qbar l) ℂ_[l]) _ _).symm

  have hLg : ∀ s ∈ Ine (F := ℚ) A, ∀ b ∈ chiPart X N w χ, L (1 ⊗ₜ[ℤ_[l]] X.galB l s b) = L (1 ⊗ₜ[ℤ_[l]] b) := by
    intro s hs b hbB
    have e : (1 : Qbar l) ⊗ₜ[ℤ_[l]] (X.galB l s b) = X.galV l (Qbar l) s (1 ⊗ₜ[ℤ_[l]] b) := by simp [Tower.galV]
    rw [hLpr _ (hstG s b hbB), hLpr b hbB]
    congr 2
    simp only [hpr, e, hπg _ s _ (hVB b hbB.1), Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hDec s (Ine_le_Dec A hs), hIne s hs]
  obtain ⟨S, hS⟩ := hfin.exists_sum
  have hnear : ∀ b ∈ chiPart X N w χ, ∀ δ : ℝ, 0 < δ → ∃ z : Qbar l, FixIc c z ∧ ‖(z : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ δ := by
    intro b hbB
    refine exists_fixed_near c _ C fun n => ?_
    have h := hth n b hbB.1
    set φ := thN X A N l n 1 b
    have h2 := hL n b hbB.1 φ h
    refine ⟨lam (seqN 1 j φ), ?_, h2, fun τ ha hτ => ?_⟩
    · obtain ⟨f, -, -, -, hint, -⟩ := h
      exact hC _ fun s => (hj _).1 (hint _)
    · obtain ⟨s, hs⟩ := exists_restrict j τ.toRingEquiv
      obtain ⟨hsA, hsI⟩ := mem_Ine_of_restrict hj τ hτ s hs
      have h1 := hL n _ (hstG s b hbB).1 _ (GlobalTheory.isThB_galB Ω ε X A N l n w s hlA hsA b hbB.1 φ h)
      have e1 : lam (seqN 1 j (HahnSeries.map φ (s : Ω →+* Ω))) = τ (lam (seqN 1 j φ)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hS, hS (seqN 1 j φ), map_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [map_mul, hwt t τ ha hτ]
        congr 1
        exact hs _
      rw [e1, hLg s hsI b hbB] at h1
      rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub]
      have e : ((τ (lam (seqN 1 j φ)) : Qbar l) : ℂ_[l]) - (lam (seqN 1 j φ) : ℂ_[l]) =
          (((τ (lam (seqN 1 j φ)) : Qbar l) : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)) +
            -((lam (seqN 1 j φ) : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))

  have hres : ∃ (t : Qbar l) (u : ℂ_[l]) (p : ℕ → Qbar l), ‖u‖ = 1 ∧
      (∀ n, ‖p n‖ = 1 ∧ FixIc c (p n) ∧ ‖(p n : ℂ_[l]) - u‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) ∧
      ∀ b ∈ chiPart X N w χ, L (1 ⊗ₜ[ℤ_[l]] b) = u * ((t * pr b 1 : Qbar l) : ℂ_[l]) := by
    by_cases h0 : ∀ b ∈ chiPart X N w χ, L (1 ⊗ₜ[ℤ_[l]] b) = 0
    · refine ⟨0, 1, fun _ => 1, norm_one, fun n => ⟨norm_one, fun τ _ _ => map_one τ, by
        rw [UniformSpace.Completion.coe_one, sub_self, norm_zero]; exact norm_nonneg _⟩, fun b hb => ?_⟩
      rw [h0 b hb]; simp
    · push Not at h0
      obtain ⟨b₀, hb₀, hne⟩ := h0
      obtain ⟨a, u, p, hau, hu, hp⟩ := exists_fixed_period c _ hne (hnear b₀ hb₀)
      have h1 := hLpr b₀ hb₀
      have h2 : ((pr b₀ 1 : Qbar l) : ℂ_[l]) ≠ 0 := fun h => hne (by rw [h1, h, mul_zero])
      refine ⟨a / pr b₀ 1, u, p, hu, hp, fun b hb => ?_⟩
      have hd : ((a / pr b₀ 1 : Qbar l) : ℂ_[l]) = (a : ℂ_[l]) / (pr b₀ 1 : Qbar l) :=
        map_div₀ (algebraMap (Qbar l) ℂ_[l]) _ _
      rw [hLpr b hb, UniformSpace.Completion.coe_mul (a / pr b₀ 1), hd, ← mul_assoc, ← mul_div_assoc, ← hau, h1,
        mul_div_assoc, div_self h2, mul_one]
  obtain ⟨t, u, p, hu, hp, hLu⟩ := hres
  have hpc : ∀ n, Cg n (p (n + 1)) (p n) := by
    intro n
    unfold Cg
    rw [← PadicComplex.norm_extends l (p (n + 1) - p n), UniformSpace.Completion.coe_sub]
    have e : (p (n + 1) : ℂ_[l]) - p n = ((p (n + 1) : ℂ_[l]) - u) + -((p n : ℂ_[l]) - u) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hp _).2.2.trans ?_) (by rw [norm_neg]; exact (hp n).2.2))
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) norm_l_lt_one.le (by omega)
  obtain ⟨k, hk⟩ := exists_le_l_pow l C
  refine ⟨fun b => t • pr b, ⟨fun i => t * κ i, fun b => by simp only [hpr, Finset.smul_sum, mul_smul]⟩, hfin, hwt, k, p,
    fun n => ⟨(hp n).1, hpc n, (hp n).2.1⟩, fun n hn b hbB φ hφ => ?_⟩
  refine (cg_sub_iff hn _ _).2 (le_trans ?_ (mul_le_mul_of_nonneg_right hk (norm_nonneg _)))
  have h1 := hL n b hbB.1 φ hφ
  have h2 := hb b hbB.1
  rw [hLu b hbB] at h1 h2
  rw [norm_mul, hu, one_mul] at h2
  change ‖lam (seqN 1 j φ) - p n * (t * pr b 1)‖ ≤ _
  set r := t * pr b 1
  rw [← PadicComplex.norm_extends l (lam (seqN 1 j φ) - p n * r), UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.coe_mul]
  have e : (lam (seqN 1 j φ) : ℂ_[l]) - (p n : ℂ_[l]) * (r : ℂ_[l]) =
      ((lam (seqN 1 j φ) : ℂ_[l]) - u * (r : ℂ_[l])) + -(((p n : ℂ_[l]) - u) * (r : ℂ_[l])) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rw [norm_neg, norm_mul, mul_comm]
  exact mul_le_mul h2 (hp n).2.2 (norm_nonneg _) hC0

end GlobalTheory.LamChi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdmissibleHeckeProjectionNonvanishing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4
open scoped TensorProduct MatrixGroups Matrix
open GlobalTheory.LambdaValuationPowers

noncomputable section

namespace GlobalTheory.AdmProj

theorem tmul_mem_VB {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    {b : X.Fn l} (hb : b ∈ X.B N l w) : (1 : Qbar l) ⊗ₜ[ℤ_[l]] b ∈ X.VB N l w (Qbar l) :=
  LinearMap.mem_range.2 ⟨(1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : X.B N l w), by simp⟩

theorem fixIc_mono {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) {x : Qbar l} (hx : FixIc c x) : FixIc c' x :=
  fun σ h1 h2 => hx σ (fun y hy => h1 y (h hy)) h2

theorem fixIc_l_pow_mul {l : ℕ} [Fact l.Prime] {c : Coef l} (a : ℕ) {x : Qbar l} (hx : FixIc c x) :
    FixIc c (((l : ℕ) : Qbar l) ^ a * x) := fun σ h1 h2 => by
  rw [map_mul, map_pow, map_natCast, hx σ h1 h2]

theorem exists_admissible_hecke_projection_nonvanishing_alt : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
  [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
  (j : Ω →+* Qbar l),
  Nf e S A W → 1 ≤ e →
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
  (∀ x ∈ A, ‖j x‖ ≤ 1) →
  ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
  (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
  (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
  (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
    (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
  (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
  ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
  ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
    (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
  P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
  (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
  (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
  (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
  (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
  (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
  (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
  ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
  (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
    Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
  ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
    c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
    (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
    IsLamFR2 X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
  intro Ω _ _ _ ε X A N l _ e S W ψ ι gN j hNf he hφ hlA hl2 hlN hN5 hj ev ρ F hρ hDec hIne hIne0 hev χ hχ m π σ P hPadm hPev
    hσV hπgal hσgal hσT heig hπσ hPx c lam hlamF hlamI hlamE
  classical
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hinj : Function.Injective ε := ε.injective
  have hφ' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := hφ; exact ⟨φ, h2, h1⟩
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hlN).symm
  obtain ⟨pr0, ⟨κ, hκ⟩, hLam⟩ := GlobalTheory.LamChi.exists_pr_isLamFR ε X A N l (2 * e - 1) j hφ hlA hl2 hlN hN5 hodd hj ev ρ F hDec hIne hIne0
    m π σ P hPadm hPev hσV hπgal hσgal hσT hπσ hPx χ c lam hlamF hlamI hlamE

  have hadd0 : ∀ b b', pr0 (b + b') = pr0 b + pr0 b' := by
    intro b b'
    simp only [hκ, TensorProduct.tmul_add, map_add (f := _), smul_add, Finset.sum_add_distrib]
  have hsmul0 : ∀ (z : ℤ_[l]) b, pr0 (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr0 b := by
    intro z b
    rw [hκ, hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (Qbar l) z, map_smul, smul_comm]
    rfl
  have hgal0 : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr0 (X.galB l s b) = rhoK W e ψ s *ᵥ pr0 b := by
    intro s b hb
    rw [hκ, hκ, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (1 : Qbar l) ⊗ₜ[ℤ_[l]] X.galB l s b = X.galV l (Qbar l) s ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) := by
      simp [Tower.galV]
    rw [e1, hπgal i s _ (tmul_mem_VB X N l (2 * e - 1) hb), hρ s, Matrix.mulVec_smul]
  have hop0 : ∀ T : Letter, GlobalTheory.KZ.admitted N l T → ∀ b, b ∈ X.B N l (2 * e - 1) → pr0 (X.op N l T b) = ev T • pr0 b := by
    intro T hT b hb
    rw [hκ, hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (1 : Qbar l) ⊗ₜ[ℤ_[l]] X.op N l T b = X.opV N l (Qbar l) T ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) := by
      simp [Tower.opV]
    rw [e1, heig i T hT _ (tmul_mem_VB X N l (2 * e - 1) hb), smul_comm]

  obtain ⟨c1, hc1⟩ := hNf.int
  obtain ⟨c0, hcc0, hc10⟩ := (UpperTheory.V.HV.coefSup l).1 c c1
  have hfree := GlobalTheory.KZ.B_free_finite ε X hinj hφ' N l (2 * e - 1) hl2 hN5 hcop hodd
  haveI := hfree.1
  haveI := hfree.2
  let bs := Module.Free.chooseBasis ℤ_[l] (X.B N l (2 * e - 1))
  obtain ⟨a, ha⟩ := exists_le_l_pow l
    (∑ p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2, ‖pr0 (bs p.1) p.2‖)
  have hsmall : ∀ p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2,
      ‖((l : ℕ) : Qbar l) ^ a * pr0 (bs p.1) p.2‖ ≤ 1 := by
    intro p
    have h1 : ‖pr0 (bs p.1) p.2‖ ≤ (l : ℝ) ^ a :=
      le_trans (Finset.single_le_sum
        (f := fun p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2 => ‖pr0 (bs p.1) p.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p)) ha
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    rw [norm_mul, norm_l_pow]
    calc ((l : ℝ)⁻¹) ^ a * ‖pr0 (bs p.1) p.2‖ ≤ ((l : ℝ)⁻¹) ^ a * (l : ℝ) ^ a :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow]
  obtain ⟨cf, hcf, hs⟩ := GlobalTheory.PowerSeriesEvalAlgCl.exists_coef_ge_finset c0
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2 =>
      ((l : ℕ) : Qbar l) ^ a * pr0 (bs p.1) p.2)
    (fun y hy => by
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy
      exact (GlobalTheory.PowerSeriesEvalAlgCl.isIntegral_iff_norm_le_one _).2 (hsmall p))

  obtain ⟨pr, hpr⟩ : ∃ pr : X.Fn l → Fin 2 → Qbar l, ∀ b, pr b = ((l : ℕ) : Qbar l) ^ a • pr0 b := ⟨_, fun _ => rfl⟩
  have hadd : ∀ b b', pr (b + b') = pr b + pr b' := by
    intro b b'; rw [hpr, hpr, hpr, hadd0, smul_add]
  have hsmul : ∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b := by
    intro z b; rw [hpr, hpr, hsmul0, smul_comm]
  have hint : ∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O := by
    intro b hb i
    let g : X.B N l (2 * e - 1) →ₗ[ℤ_[l]] Qbar l :=
      { toFun := fun y => pr y.1 i
        map_add' := fun y y' => by
          simp only [Submodule.coe_add, hadd, Pi.add_apply]
        map_smul' := fun z y => by
          simp only [SetLike.val_smul, hsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def]
          rfl }
    have hle : Submodule.span ℤ_[l] (Set.range bs) ≤ (Subalgebra.toSubmodule cf.O).comap g := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := hs _ (Finset.mem_image.2 ⟨(k, i), Finset.mem_univ _, rfl⟩)
      simpa [g, hpr] using this
    rw [bs.span_eq] at hle
    exact hle (Submodule.mem_top (x := (⟨b, hb⟩ : X.B N l (2 * e - 1))))
  have hgal : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b := by
    intro s b hb; rw [hpr, hpr, hgal0 s b hb, Matrix.mulVec_smul]
  have hhecke : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b := by
    intro q hq hqd b hb
    have hT : GlobalTheory.KZ.admitted N l (Letter.T q) := ⟨hq, fun h => hqd (by rwa [mul_comm] at h)⟩
    have := hop0 _ hT b hb
    rw [hpr, hpr, show X.heckeT N l q b = X.op N l (Letter.T q) b from rfl, this, hev q hq hqd, smul_comm]
  have hdiam : ∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b := by
    intro d hd b hb
    have := hop0 (Letter.D d) hd b hb
    rw [hpr, hpr, show X.diam N l d b = X.op N l (Letter.D d) b from rfl, this, hχ d hd, smul_comm]
  have hU : ∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b := by
    intro b hb
    have := hop0 Letter.U trivial b hb
    rw [hpr, hpr, show X.heckeU l b = X.op N l Letter.U b from rfl, this, smul_comm]
  have hnorm : ‖((l : ℕ) : Qbar l) ^ a‖ ≤ 1 := by
    rw [norm_l_pow]
    have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
  have hccf : c.O ≤ cf.O := hcc0.trans hcf
  have hlam : IsLamFR X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
    obtain ⟨hf, hw, cL, per, hper, hc⟩ := hLam
    refine ⟨hf.smul _, fun i => fixIc_l_pow_mul a (fixIc_mono hccf (hw i)), cL, per,
      fun n => ⟨(hper n).1, (hper n).2.1, fixIc_mono hccf (hper n).2.2⟩, fun n hn b hb φ hφ => ?_⟩
    have h := hc n hn b hb φ hφ
    unfold GlobalTheory.Ord2.Cg at h ⊢
    rw [hpr, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    calc ‖((l : ℕ) : Qbar l) ^ a * lam (seqN 1 j φ) - per n * (((l : ℕ) : Qbar l) ^ a * pr0 b 1)‖
        = ‖((l : ℕ) : Qbar l) ^ a‖ * ‖lam (seqN 1 j φ) - per n * pr0 b 1‖ := by
          rw [← norm_mul]; congr 1; ring
      _ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ (n - cL)‖ := mul_le_mul hnorm h (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact ⟨pr, a, cf, hccf, fun s i k => hcf (hc10 (hc1 s i k)), hadd, hsmul, hint, hgal, hhecke, hdiam, hU, hdiam, hlam⟩

end GlobalTheory.AdmProj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdmissibleHeckeProjectionNonvanishingStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4
open scoped TensorProduct MatrixGroups Matrix
open GlobalTheory.LambdaValuationPowers
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_hecke_projection_nonvanishing : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
  [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
  (j : Ω →+* Qbar l),
  Nf e S A W → 1 ≤ e →
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
  (∀ x ∈ A, ‖j x‖ ≤ 1) →
  ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
  (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
  (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
  (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
    (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
  (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
  ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
  ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
    (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
  P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
  (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
  (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
  (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
  (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
  (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
  (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
  ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
  (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
    Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
  ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
    c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
    (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
    IsLamFR2 X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
  first | (exact @GlobalTheory.AdmProj.exists_admissible_hecke_projection_nonvanishing_alt) | (exact GlobalTheory.AdmProj.exists_admissible_hecke_projection_nonvanishing_alt) | (intros; apply GlobalTheory.AdmProj.exists_admissible_hecke_projection_nonvanishing_alt  <;> assumption)
end
end

namespace UpperTheory.V.Z.Kato.Final

theorem zetaUr : GlobalTheory.Ord2.ZetaUr := GlobalTheory.KZ.zetaUr_of_halves2 _
  (UpperTheory.V.Z.Kato.Joint.kato_global_unit_law_of_smoothed_classes UpperTheory.Kd.K4.kato_eulerSystem_integrality UpperTheory.V.Z.Kato.K5.smoothedZetaClass_hodgeTateLaw
    (fun {Ω} _ _ _ => GlobalTheory.T.exists_admissible_hecke_projection_nonvanishing))
  UpperTheory.Kd.C7.pLocu

end UpperTheory.V.Z.Kato.Final
