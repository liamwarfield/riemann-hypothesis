module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem sum_mul_cosetTrace_eq (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (N : Subgroup G) [Fintype (G ⧸ N)] (n : ℕ) (a b : Fin n → L) (c : L)
    (h : IsSep v N a b c) : ∀ x ∈ Fix L N, ∑ i, a i * cosetTrace N (b i * x) = c * x := by
  classical
  intro x hx
  have hmem : ∀ q : G ⧸ N, q.out ∈ N ↔ q = ((1 : G) : G ⧸ N) := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  have key : ∀ q : G ⧸ N, (∑ i, a i * q.out • b i) * q.out • x
      = if ((1 : G) : G ⧸ N) = q then c * x else 0 := by
    intro q
    by_cases hq : q.out ∈ N
    · rw [if_pos ((hmem q).mp hq).symm, h.sum_in _ hq]
      congr 1
      exact hx ⟨_, hq⟩
    · rw [if_neg (fun h1 => hq ((hmem q).mpr h1.symm)), h.sum_out _ hq, zero_mul]
  calc ∑ i, a i * cosetTrace N (b i * x)
      = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) * q.out • x := by
        simp only [cosetTrace, smul_mul', Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = c * x := by rw [Finset.sum_congr rfl fun q _ => key q]; simp

end GlobalTheory.AlmostEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEqStatement
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (N : Subgroup G) [Fintype (G ⧸ N)] (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, ∑ i, a i * cosetTrace N (b i * x) = c * x := by
  first | exact @GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq | exact GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq | (intros; apply GlobalTheory.AlmostEt.sum_mul_cosetTrace_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmul
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem polySlash_map_conj (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, lcoeff_apply, Polynomial.map_sum, Polynomial.map_smul,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    map_intCast, coeff_map, Polynomial.map_intCast, Polynomial.map_natCast]

theorem eichler_smul (w : ℕ) (c : ℂ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    eichler w (c • f) τ = c • eichler w f τ := by
  simp only [eichler, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_C_mul, ← mul_assoc, ← C_mul]
  congr 2
  have : ∀ t : ℝ, ((c • f) ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I) =
      c * ((f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) := by
    intro t; simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [this, intervalIntegral.integral_const_mul]
  ring

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

theorem polynomialMapCoeffConj_mem_eichlerShimuraCocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : Γ → ℂ[X]) (hz : z ∈ Z1 Γ w) : cj z ∈ Z1 Γ w := by
  obtain ⟨h1, h2⟩ := hz
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · have := h1 γ
    rw [mem_degreeLT] at this ⊢
    exact lt_of_le_of_lt (degree_map_le) this
  · simp only [cj, h2, Polynomial.map_add (f := _), polySlash_map_conj]

theorem polynomialMapCoeffConj_mem_eichlerShimuraCoboundaries (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : Γ → ℂ[X]) (hz : z ∈ B1 Γ w) : cj z ∈ B1 Γ w := by
  obtain ⟨⟨p, hp⟩, rfl⟩ := hz
  have hp' : p.map (starRingEnd ℂ) ∈ degreeLT ℂ (w + 1) := by
    rw [mem_degreeLT] at hp ⊢
    exact lt_of_le_of_lt (degree_map_le) hp
  refine ⟨⟨p.map (starRingEnd ℂ), hp'⟩, ?_⟩
  funext γ
  simp only [cj, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply,
    LinearMap.sub_apply, LinearMap.id_apply, Polynomial.map_sub, polySlash_map_conj]

theorem per_smul (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (f : ℍ → ℂ) (c : ℂ) :
    per Γ w (c • f) = c • per Γ w f := by
  funext γ
  simp only [per, Pi.smul_apply, eichler_smul, map_smul]

theorem cj_mem_Z1_cj_mem_B1_per_smul : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ), (∀ z ∈ Z1 Γ w, cj z ∈ Z1 Γ w) ∧
    (∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w) ∧ ∀ (f : ℍ → ℂ) (c : ℂ), per Γ w (c • f) = c • per Γ w f :=
  fun Γ w => ⟨polynomialMapCoeffConj_mem_eichlerShimuraCocycles Γ w, polynomialMapCoeffConj_mem_eichlerShimuraCoboundaries Γ w, per_smul Γ w⟩

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraConjCocyclesCoboundariesPeriodSmulStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul : ∀ (Γ : Subgroup SL(2, ℤ)) (w : ℕ), (∀ z ∈ Z1 Γ w, cj z ∈ Z1 Γ w) ∧ (∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w) ∧ ∀ (f : ℍ → ℂ) (c : ℂ), per Γ w (c • f) = c • per Γ w f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul | exact GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul | (intros; apply GlobalTheory.HeckeFamilyMatrices.cj_mem_Z1_cj_mem_B1_per_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubring
open Finset

namespace GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring : ∀ (K : Type) [Field K] [CharZero K]
    (R : Subring K) (c M : ℕ) (ζ : K) (a b : ℤ),
    0 < M → Nat.Coprime c M → ¬ (M : ℤ) ∣ a → ζ ^ b ∈ R → ζ ^ (-b) ∈ R →
    ∀ n : ℕ, _root_.GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M ζ a b n ∈ R := by
  intro K _ _ R c M ζ a b hM hcop ha hb hbneg n
  have hca : ¬ (M : ℤ) ∣ (c : ℤ) * a := by
    intro h
    apply ha
    refine Int.dvd_of_dvd_mul_right_of_gcd_one h ?_
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.symm hcop
  have hpow : ∀ m : ℕ, ζ ^ (b * (m : ℤ)) ∈ R ∧ ζ ^ (-(b * (m : ℤ))) ∈ R := by
    intro m
    refine ⟨?_, ?_⟩
    · rw [zpow_mul, zpow_natCast]; exact R.pow_mem hb m
    · rw [← neg_mul, zpow_mul, zpow_natCast]; exact R.pow_mem hbneg m
  have hpow' : ∀ m : ℕ, ζ ^ ((c : ℤ) * b * (m : ℤ)) ∈ R ∧ ζ ^ (-((c : ℤ) * b * (m : ℤ))) ∈ R := by
    intro m
    have h := hpow (c * m)
    rwa [show (c : ℤ) * b * (m : ℤ) = b * ((c * m : ℕ) : ℤ) by push_cast; ring]
  unfold _root_.GlobalTheory.KummerEisensteinGalois.smF _root_.GlobalTheory.KummerEisensteinGalois.eisF
  split_ifs with hn
  · unfold _root_.GlobalTheory.KummerEisensteinGalois.const0
    simp only [if_true, if_neg ha, if_neg hca]
    have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (c : ℚ) ^ 2 * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M a) -
        c * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M (c * a)) =
        (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) - (c : ℤ) ^ 2 * (a / M)) : ℤ) := by
      unfold _root_.GlobalTheory.KummerEisensteinGalois.frc
      rw [Int.emod_def, Int.emod_def]
      push_cast
      rw [Nat.cast_choose_two]
      field_simp
      ring
    convert intCast_mem R (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) -
      (c : ℤ) ^ 2 * (a / M))) using 1
    have hK := congrArg (fun q : ℚ => (q : K)) key
    simp only [Rat.cast_intCast] at hK
    rw [← hK]
    push_cast
    norm_num
  · unfold _root_.GlobalTheory.KummerEisensteinGalois.coefPos
    refine R.sub_mem (R.mul_mem (R.pow_mem (intCast_mem R _) 2) (R.sum_mem fun d _ => ?_))
      (R.mul_mem ?_ (R.sum_mem fun d _ => ?_))
    · simp only [Nat.sub_self, pow_zero, one_mul]
      refine R.sub_mem ?_ ?_ <;> split_ifs
      · exact (hpow d).1
      · exact R.zero_mem
      · exact (hpow d).2
      · exact R.zero_mem
    · norm_num
    · simp only [Nat.sub_self, pow_zero, one_mul]
      refine R.sub_mem ?_ ?_ <;> split_ifs
      · exact (hpow' d).1
      · exact R.zero_mem
      · exact (hpow' d).2
      · exact R.zero_mem

end GlobalTheory.KummerEisensteinGalois
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubringStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring : ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (c M : ℕ) (ζ : K) (a b : ℤ), 0 < M → Nat.Coprime c M → ¬ (M : ℤ) ∣ a → ζ ^ b ∈ R → ζ ^ (-b) ∈ R → ∀ n : ℕ, GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M ζ a b n ∈ R := by
  first | exact @GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | exact GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring | (intros; apply GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLang
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLang
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

open MvPolynomial

theorem is_c1_of_finite_of_tsen_lang_systems : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  intro F K _ _ _ _ hF n d f hf hd hdn
  set m := Module.finrank F K with hm
  have hm0 : 0 < m := Module.finrank_pos
  let b : Module.Basis (Fin m) F K := Module.finBasis F K
  let e : Fin n × Fin m ≃ Fin (n * m) := finProdFinEquiv
  let g : Fin n → MvPolynomial (Fin (n * m)) K := fun i => ∑ j, MvPolynomial.C (b j) * MvPolynomial.X (e (i, j))
  have hg : ∀ i, (g i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)
  let G : MvPolynomial (Fin (n * m)) K := aeval g f
  have hG : G.IsHomogeneous d := by
    have h1 := hf.aeval g hg
    rwa [one_mul] at h1
  let P : Fin m → MvPolynomial (Fin (n * m)) F := fun l =>
    ∑ s ∈ G.support, monomial s (b.repr (G.coeff s) l)
  have hP : ∀ l, (P l).IsHomogeneous d := fun l =>
    IsHomogeneous.sum _ _ _ (fun s hs => isHomogeneous_monomial _ (by
      rw [Finsupp.degree_eq_weight_one]; exact hG (mem_support_iff.mp hs)))
  have hlt : m * d < n * m := by
    rw [mul_comm n m]; exact Nat.mul_lt_mul_of_pos_left hdn hm0
  obtain ⟨y, hy0, hy⟩ := hF (n * m) m d P hP hd hlt
  let x : Fin n → K := fun i => ∑ j, algebraMap F K (y (e (i, j))) * b j
  refine ⟨x, ?_, ?_⟩
  · intro hx
    apply hy0
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
    have hxi : ∑ j, y (e (i, j)) • b j = 0 := by
      have := congrFun hx i
      simpa [x, Algebra.smul_def] using this
    exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => y (e (i, j))) hxi j
  · have key : MvPolynomial.eval x f = MvPolynomial.eval (fun k => algebraMap F K (y k)) G := by
      rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
      show _ = MvPolynomial.aeval _ (MvPolynomial.bind₁ g f)
      rw [MvPolynomial.aeval_bind₁]
      have hxe : x = fun i => MvPolynomial.aeval (fun k => algebraMap F K (y k)) (g i) := by
        funext i
        simp [g, x, mul_comm]
      rw [hxe]
      rfl
    have key2 : MvPolynomial.eval (fun k => algebraMap F K (y k)) G
        = ∑ l, algebraMap F K (MvPolynomial.eval y (P l)) * b l := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, map_sum, MvPolynomial.eval_monomial, Finset.sum_mul]
      rw [Finset.sum_comm, MvPolynomial.eval_eq]
      refine Finset.sum_congr rfl (fun s hs => ?_)
      conv_lhs => rw [← b.sum_repr (G.coeff s)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp [Finsupp.prod, map_prod, map_pow, Algebra.smul_def]
      ring
    rw [key, key2]
    exact Finset.sum_eq_zero (fun l _ => by rw [hy l, map_zero, zero_mul])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLangStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  first | exact @GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | exact GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | (intros; apply GlobalTheory.is_c1_of_finite_of_tsen_lang_systems <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCuspFormGamma1InterGamma0
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCuspFormGamma1InterGamma0
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem conj_mem_lev {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ lev N l) : σ * γ * σ⁻¹ ∈ lev N l := by
  obtain ⟨h1, -⟩ := hσ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
  push_cast at h1
  have hN : ((σ 1 0 : ℤ) : ZMod N) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_right _ _) h1)
  have hl : ((σ 1 0 : ℤ) : ZMod l) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_trans (dvd_mul_left _ _) h1)
  obtain ⟨hg1, hg0⟩ := Subgroup.mem_inf.1 hγ
  rw [Gamma1_mem] at hg1
  obtain ⟨hx, hw, hz⟩ := hg1
  rw [Gamma0_mem] at hg0
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hdN := congrArg (Int.cast : ℤ → ZMod N) hdet
  push_cast at hdN
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    rw [hN, hx, hw, hz] at *
    refine ⟨?_, ?_, ?_⟩
    · linear_combination hdN
    · linear_combination hdN
    · ring
  · rw [Gamma0_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    push_cast
    rw [hl, hg0]
    ring

end GlobalTheory.Hk

namespace GlobalTheory.Hk

open scoped Pointwise in
theorem dia_cuspForm : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.dia k σ ⇑f := by
  intro N l k d σ _ hσ f
  have hle : ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ) •
      (lev N l : Subgroup (GL (Fin 2) ℝ)) ≤ (lev N l : Subgroup (GL (Fin 2) ℝ)) := by
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.toConjAct_smul, inv_inv] at hy
    obtain ⟨γ, hγ, hγe⟩ := hy
    refine ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, ?_⟩
    change Matrix.SpecialLinearGroup.mapGL ℝ (σ * γ * σ⁻¹) = y
    rw [map_mul, map_mul, map_inv, hγe]
    group
  refine ⟨{ toFun := dia k σ f
            slash_action_eq' := fun A hA => ?_
            holo' := ?_
            zero_at_cusps' := fun {x} hx => ?_ }, rfl⟩
  · obtain ⟨γ, hγ, rfl⟩ := hA
    have h : (f : ℍ → ℂ) ∣[k] (σ * γ * σ⁻¹) = f :=
      f.slash_action_eq' _ ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, rfl⟩
    show ((f : ℍ → ℂ) ∣[k] σ) ∣[k] γ = (f : ℍ → ℂ) ∣[k] σ
    rw [← SlashAction.slash_mul]
    have e : σ * γ = (σ * γ * σ⁻¹) * σ := by group
    rw [e, SlashAction.slash_mul, h]
  · exact MDifferentiable.slash f.holo' _ _
  · have h3 : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ σ • x) (lev N l : Subgroup (GL (Fin 2) ℝ)) :=
      (hx.smul _).mono hle
    show x.IsZeroAt ((f : ℍ → ℂ) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ) k
    exact OnePoint.IsZeroAt.smul_iff.1 (f.zero_at_cusps' h3)

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCuspFormGamma1InterGamma0Statement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.dia k σ ⇑f := by
  first | exact @GlobalTheory.Hk.dia_cuspForm | exact GlobalTheory.Hk.dia_cuspForm | (intros; apply GlobalTheory.Hk.dia_cuspForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacter
noncomputable section

open Polynomial IntermediateField

namespace GlobalTheory.NeedB.KumLemma

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem pow_val_add {N : ℕ} [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N]
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem exists_pow {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    ∃ i : ZMod N, g θ = ζ ^ i.val * θ := by
  obtain ⟨c, hc⟩ := hN
  have hg : (g θ) ^ N = θ ^ N := by rw [← map_pow, ← hc, AlgEquiv.commutes]
  have h1 : (g θ / θ) ^ N = 1 := by
    rw [div_pow, hg, div_self (pow_ne_zero _ hθ)]
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one h1
  refine ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_cast_of_lt hi, hi', div_mul_cancel₀ _ hθ]

theorem unique_pow {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    {a b : ZMod N} (h : ζ ^ a.val * θ = ζ ^ b.val * θ) : a = b := by
  have h' : ζ ^ a.val = ζ ^ b.val := mul_right_cancel₀ hθ h
  exact ZMod.val_injective N (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')

theorem kum_spec {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    g θ = ζ ^ (kum (N := N) ζ θ g).val * θ := by
  have h := exists_pow hζ hθ hN g
  unfold kum
  rw [dite_eq_left h]
  exact h.choose_spec

theorem kum_eq {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) {i : ZMod N}
    (hi : g θ = ζ ^ i.val * θ) : kum (N := N) ζ θ g = i :=
  unique_pow hζ hθ ((kum_spec hζ hθ hN g).symm.trans hi)

theorem kum_mul {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ)
    (hθ : θ ≠ 0) (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g h : Ω ≃ₐ[K] Ω) :
    kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h := by
  apply kum_eq hζ hθ hN
  rw [AlgEquiv.mul_apply, kum_spec hζ hθ hN h, map_mul, map_pow, hfix, kum_spec hζ hθ hN g,
    add_comm, pow_val_add hζ]
  ring

theorem kum_eq_zero_iff {N : ℕ} [NeZero N] {ζ θ : Ω} (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) (g : Ω ≃ₐ[K] Ω) :
    kum (N := N) ζ θ g = 0 ↔ g θ = θ := by
  constructor
  · intro h
    have := kum_spec hζ hθ hN g
    rwa [h, ZMod.val_zero, pow_zero, one_mul] at this
  · intro h
    apply kum_eq hζ hθ hN
    rw [h, ZMod.val_zero, pow_zero, one_mul]

theorem kummer_character [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω) (hN0 : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) (hfix : ∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) (hθ : θ ≠ 0)
    (hN : θ ^ N ∈ Set.range (algebraMap K Ω)) :
    IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
    (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧
    (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) := by
  haveI : NeZero N := ⟨by omega⟩
  refine ⟨?_, kum_spec hζ hθ hN, kum_mul hζ hfix hθ hN, kum_eq_zero_iff hζ hθ hN⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  haveI : FiniteDimensional K K⟮θ⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral θ)
  have hopen : IsOpen ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' ((K⟮θ⟯).fixingSubgroup : Set (Ω ≃ₐ[K] Ω)),
    hopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro g' hg'
    have hfθ : (g⁻¹ * g') θ = θ := by
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg' θ
        (IntermediateField.mem_adjoin_simple_self K θ)
      exact this
    have h0 := (kum_eq_zero_iff hζ hθ hN _).2 hfθ
    have : g' = g * (g⁻¹ * g') := by group
    rw [this, kum_mul hζ hfix hθ hN, h0, add_zero]

end GlobalTheory.NeedB.KumLemma

open GlobalTheory.NeedB in
theorem GlobalTheory.NeedB.KumLemma.kummer_character_main : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → θ ≠ 0 → θ ^ N ∈ Set.range (algebraMap K Ω) →
  IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
  (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧ (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) :=
  fun K Ω _ _ _ _ N ζ θ h0 hζ hf hθ hN => GlobalTheory.NeedB.KumLemma.kummer_character N ζ θ h0 hζ hf hθ hN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExponentOfGaloisElementIsKummerCharacterStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ θ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → θ ≠ 0 → θ ^ N ∈ Set.range (algebraMap K Ω) →
  IsLocallyConstant (kum (N := N) (K := K) ζ θ) ∧ (∀ g : Ω ≃ₐ[K] Ω, g θ = ζ ^ (kum (N := N) ζ θ g).val * θ) ∧
  (∀ g h : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ (g * h) = kum ζ θ g + kum ζ θ h) ∧ (∀ g : Ω ≃ₐ[K] Ω, kum (N := N) ζ θ g = 0 ↔ g θ = θ) := by
  first | exact @GlobalTheory.NeedB.KumLemma.kummer_character_main | exact GlobalTheory.NeedB.KumLemma.kummer_character_main | (intros; apply GlobalTheory.NeedB.KumLemma.kummer_character_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalPolyDegreeSlashAction
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem eval_polySlash : ∀ (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (z : ℂ), p ∈ degreeLT ℂ (w + 1) → ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ≠ 0 → (slP w g p).eval z = ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ w * p.eval (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) := by
  intro w g p z hp hz
  have hn : p.natDegree < w + 1 := by
    rcases eq_or_ne p 0 with rfl | h
    · simp
    · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)
  have hs : slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
    simp [slP, LinearMap.sum_apply, LinearMap.toSpanSingleton_apply]
  rw [hs, eval_finsetSum, eval_eq_sum_range' hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [eval_smul, eval_mul, eval_pow, eval_add, eval_C, eval_X, smul_eq_mul]
  rw [div_pow, ← Nat.sub_add_cancel hi', pow_add]
  rw [Nat.sub_add_cancel hi']
  have hD : ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ i ≠ 0 := pow_ne_zero _ hz
  have e := mul_inv_cancel₀ hD
  linear_combination (-(p.coeff i * ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) ^ i *
    ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ (w - i))) * e

end GlobalTheory.HeckeFamilyMatrices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesAlgebraicConstant
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem addVal_eq_zero_of_root_sub_const {k K : Type} [Field k] [Field K] (φ : k →+* K)
    (v : AddValuation K (WithTop ℤ)) (hv : ∀ a : k, a ≠ 0 → v (φ a) = 0) (f : K) (P : k[X])
    (hP : P ≠ 0) (hf : eval₂ φ f P = 0) (c : k) (h : f - φ c ≠ 0) : v (f - φ c) = 0 := by
  letI : Algebra k K := φ.toAlgebra
  have h1 : IsAlgebraic k f := ⟨P, hP, hf⟩
  have h2 : IsAlgebraic k (f - φ c) := h1.sub (isAlgebraic_algebraMap c)
  haveI : Valuation.IsTrivialOn k (AddValuation.toValuation v) := ⟨fun a ha => hv a ha⟩
  by_contra hne
  exact Valuation.transcendental_of_ne_one k (v := AddValuation.toValuation v) _ h hne h2

theorem laurentSeries_eq_C_of_root : ∀ (k : Type) [Field k] (f : LaurentSeries k),
    (∃ P : k[X], P ≠ 0 ∧ eval₂ HahnSeries.C f P = 0) → ∃ c : k, f = HahnSeries.C c := by
  rintro k _ f ⟨P, hP, hf⟩
  refine ⟨f.coeff 0, ?_⟩
  by_contra hne
  have h : f - HahnSeries.C (f.coeff 0) ≠ 0 := sub_ne_zero.2 hne
  have h0 := addVal_eq_zero_of_root_sub_const (K := LaurentSeries k) HahnSeries.C
    (HahnSeries.addVal ℤ k) (fun a ha => by
      rw [HahnSeries.addVal_apply_of_ne (HahnSeries.C_ne_zero ha), HahnSeries.order_C]; rfl)
    f P hP hf _ h
  rw [HahnSeries.addVal_apply] at h0
  have h1 := HahnSeries.coeff_orderTop_ne (g := 0) h0
  apply h1
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowSmulHeckeVOperatorExplicitEqSlashDiag
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowSmulHeckeVOperatorExplicitEqSlashDiag
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem smul_vOp_eq_slash (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q) : (q : ℂ) ^ (k - 1) • vOp q f = f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  set g := (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) with hg
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = q := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hdet : (g.det : ℝ) = q := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdpos : 0 < (g.det : ℝ) := by rw [hdet]; exact_mod_cast hq
  ext τ
  have hden : denom g τ = 1 := by simp [denom, h10, h11]
  have hnum : num g τ = q * τ := by simp [num, h00, h01]
  have hsmul : ((g • τ : ℍ) : ℂ) = q * τ := by
    rw [UpperHalfPlane.coe_smul_of_det_pos hdpos, hnum, hden, div_one]
  have hof : ofComplex ((q : ℂ) * τ) = g • τ := by
    rw [← hsmul]; exact ofComplex_apply _
  rw [slash_apply, hden, one_zpow, mul_one, hdet, abs_of_pos (by exact_mod_cast hq : (0:ℝ) < q)]
  simp only [σ, hdpos, if_true, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, vOp, hof]
  push_cast
  ring_nf
  rfl

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowSmulHeckeVOperatorExplicitEqSlashDiagStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_smul_heckeVOperatorExplicit_eq_slash_diag : ∀ (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q), (q : ℂ) ^ (k - 1) • GlobalTheory.Hk.vOp q f = f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  first | exact @GlobalTheory.Hk.smul_vOp_eq_slash | exact GlobalTheory.Hk.smul_vOp_eq_slash | (intros; apply GlobalTheory.Hk.smul_vOp_eq_slash <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashRatIsBoundedAtGamma1InterGamma0Level
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashRatIsBoundedAtGamma1InterGamma0Level
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_finiteIndex_of_pos (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

theorem isCusp_SL2Z_smul_ratGL (g : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  refine ⟨g • c, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul]

theorem slash_rat_isBoundedAt :
    ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) →
      ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) →
        c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  intro N l k g hN hl _ f c hc
  haveI := lev_finiteIndex_of_pos N l hN hl
  have key : IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) (GlobalTheory.Hk.lev N l) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact isCusp_SL2Z_smul_ratGL g hc
  exact OnePoint.IsBoundedAt.smul_iff.1 (f.bdd_at_cusps' key)

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashRatIsBoundedAtGamma1InterGamma0LevelStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) → c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  first | exact @GlobalTheory.Hk.slash_rat_isBoundedAt | exact GlobalTheory.Hk.slash_rat_isBoundedAt | (intros; apply GlobalTheory.Hk.slash_rat_isBoundedAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0Level
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0Level
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isDia_conj_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ γ : SL(2, ℤ)), IsDia N l d σ → γ ∈ lev N l →
    σ * γ * σ⁻¹ ∈ lev N l := by
  intro N l d σ γ hσ hγ
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ.1
  have hσN : σ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_right N l)) hc)
  have hσl : σ ∈ Gamma0 l := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_left l N)) hc)
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  refine Subgroup.mem_inf.2
    ⟨?_, (Gamma0 l).mul_mem ((Gamma0 l).mul_mem hσl hγ0) ((Gamma0 l).inv_mem hσl)⟩
  have hγN : γ ∈ Gamma0 N := ((Gamma1_mem N γ).1 hγ1).2.2
  set S : Gamma0 N := ⟨σ, hσN⟩
  set G : Gamma0 N := ⟨γ, hγN⟩
  have hG : G ∈ Gamma1' N := (Gamma1_to_Gamma0_mem G).2 ((Gamma1_mem N γ).1 hγ1)
  have hX : S * G * S⁻¹ ∈ Gamma1' N := by
    rw [Gamma1_mem'] at hG ⊢
    rw [map_mul, map_mul, hG, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have h := (Gamma1_to_Gamma0_mem _).1 hX
  exact (Gamma1_mem N _).2 h

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0LevelStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level : ∀ (N l : ℕ) (d : ℤ) (σ γ : SL(2, ℤ)), GlobalTheory.Hk.IsDia N l d σ → γ ∈ GlobalTheory.Hk.lev N l → σ * γ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  first | exact @GlobalTheory.Hk.isDia_conj_mem_lev | exact GlobalTheory.Hk.isDia_conj_mem_lev | (intros; apply GlobalTheory.Hk.isDia_conj_mem_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeCupProps
open GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KEdge

theorem edge_cup_props : ∀ (Γ : Type) [Group Γ] (N : ℕ) (Δ : Subgroup Γ) [Δ.Normal] (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
  CobOn Δ x y η →
  (∀ σ, ∀ h ∈ Δ, ∀ h' ∈ Δ, edge x y η σ (h * h') = edge x y η σ h + edge x y η σ h') ∧
  (∀ σ τ, ∀ h ∈ Δ, edge x y η (σ * τ) h = edge x y η σ (τ * h * τ⁻¹) + edge x y η τ h) ∧
  (∀ σ ∈ Δ, ∀ h ∈ Δ, edge x y η σ h = 0) := by
  intro Γ _ N Δ hN x y η hC
  have hmul : ∀ (z : Γ →* Multiplicative (ZMod N)) (a b : Γ), (z (a * b)).toAdd = (z a).toAdd + (z b).toAdd := by
    intro z a b; rw [z.map_mul]; rfl
  have hconj : ∀ (z : Γ →* Multiplicative (ZMod N)) (s a : Γ), (z (s * a * s⁻¹)).toAdd = (z a).toAdd := by
    intro z s a
    rw [hmul, hmul, z.map_inv, toAdd_inv]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro σ h hh h' hh'
    have m1 : σ * h * σ⁻¹ ∈ Δ := hN.conj_mem h hh σ
    have m2 : σ * h' * σ⁻¹ ∈ Δ := hN.conj_mem h' hh' σ
    have e1 := hC _ m1 _ m2
    have e2 := hC h hh h' hh'
    have g : σ * (h * h') * σ⁻¹ = (σ * h * σ⁻¹) * (σ * h' * σ⁻¹) := by group
    simp only [edge]
    rw [g, hmul x h h', hmul y h h']
    rw [hconj x, hconj y] at e1
    linear_combination e1 - e2
  · intro σ τ h _
    have g : σ * τ * h * (σ * τ)⁻¹ = σ * (τ * h * τ⁻¹) * σ⁻¹ := by group
    simp only [edge]
    rw [g, hmul x σ τ, hmul y σ τ, hconj x τ h, hconj y τ h]
    ring
  · intro σ hσ h hh
    have m1 : σ * h * σ⁻¹ ∈ Δ := hN.conj_mem h hh σ
    have e1 := hC _ m1 σ hσ
    have e2 := hC σ hσ h hh
    have g : σ * h * σ⁻¹ * σ = σ * h := by group
    rw [g, hconj x] at e1
    simp only [edge]
    linear_combination e2 - e1

end GlobalTheory.KEdge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormGamma1InterGamma0SlashRatIsZeroAt
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormGamma1InterGamma0SlashRatIsZeroAt
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace GlobalTheory.Hk

private theorem finiteIndex_lev_of_pos' (N l : ℕ) (hN : 0 < N) (hl : 0 < l) : (lev N l).FiniteIndex := by
  exact lev_finiteIndex_of_pos N l hN hl

private theorem isCusp_SL2Z_ratGL_smul' (g : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    IsCusp (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g • c) 𝒮ℒ := by
  exact isCusp_SL2Z_smul_ratGL g hc

theorem cuspForm_slash_rat_isZeroAt : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l →
    0 < (g.det : ℚ) → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ,
    IsCusp c (GlobalTheory.Hk.lev N l) →
    c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  intro N l k g hN hl _ f c hc
  haveI := finiteIndex_lev_of_pos' N l hN hl
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [← OnePoint.IsZeroAt.smul_iff]
  have h := isCusp_SL2Z_ratGL_smul' g hc
  rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((GlobalTheory.Hk.lev N l : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ))] at h
  exact f.zero_at_cusps' h

end GlobalTheory.Hk
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormGamma1InterGamma0SlashRatIsZeroAtStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) → c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  first | exact @GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt | exact GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt | (intros; apply GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSubQExpansionPartialSumIsBigO
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSubQExpansionPartialSumIsBigO
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem slash_sub_partialSum_isBigO : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → ∀ x : SL(2, ℤ),
    (fun τ : ℍ => (f ∣[k] x) τ - ∑ n ∈ Finset.range M, co M k f x n * Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ n)
      =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  intro M Γ k f hM hΓ hf x
  haveI : NeZero M := ⟨hM.ne'⟩
  have hg : IsMF (CongruenceSubgroup.Gamma M) k (f ∣[k] x) := by
    refine ⟨fun γ hγ => ?_, mdiff_slash hf.2.1 k x, fun y => ?_⟩
    · have h1 : x * γ * x⁻¹ ∈ Γ := hΓ ((CongruenceSubgroup.Gamma_normal M).conj_mem γ hγ x)
      rw [← SlashAction.slash_mul, show x * γ = (x * γ * x⁻¹) * x by group]
      exact hf.slash_mul h1 x
    · rw [← SlashAction.slash_mul]; exact hf.2.2 _
  have hper : (M : ℝ) ∈ ((CongruenceSubgroup.Gamma M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma]; exact AddSubgroup.mem_zmultiples _
  have hperiodic : Function.Periodic ((f ∣[k] x) ∘ ofComplex) (M : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex hg.toMF hper
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsum := hasSum_qExpansion hMpos hperiodic hg.2.1 (hf.2.2 x)
  have ha := analyticAt_cuspFunction_zero hMpos hperiodic hg.2.1 (hf.2.2 x)
  have hps := hasFPowerSeriesOnBall_cuspFunction hMpos ha hsum
  have hbig := (hps.hasFPowerSeriesAt.isBigO_sub_partialSum_pow M).comp_tendsto (qParam_tendsto_atImInfty hMpos)
  refine hbig.congr (fun τ => ?_) (fun τ => ?_)
  · simp only [Function.comp_apply, zero_add, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, co]
    rw [eq_cuspFunction τ (by positivity) hperiodic]
  · simp only [Function.comp_apply, Function.Periodic.norm_qParam, coe_im]
    rw [← Real.exp_nat_mul]; congr 1; field_simp

end GlobalTheory.OddFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSubQExpansionPartialSumIsBigOStatement
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → ∀ x : SL(2, ℤ), (fun τ : ℍ => (f ∣[k] x) τ - ∑ n ∈ Finset.range M, co M k f x n * Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ n) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  first | exact @GlobalTheory.OddFrame.slash_sub_partialSum_isBigO | exact GlobalTheory.OddFrame.slash_sub_partialSum_isBigO | (intros; apply GlobalTheory.OddFrame.slash_sub_partialSum_isBigO <;> assumption)
end
end
