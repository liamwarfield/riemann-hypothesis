module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuous
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeight
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory

theorem isThB_coeff_cong : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) →
    l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w →
    ∀ φ φ' : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l _ _ hl2 hlN hN hlA n w _ b _ φ φ' h h' r
  obtain ⟨f, hfinv, hfcls, hfδ, hfdl⟩ := h
  obtain ⟨f', hf'inv, hf'cls, hf'δ, hf'dl⟩ := h'
  obtain ⟨u, hu⟩ := Tower.cls_eq_pow X l n f f' (hfcls.symm.trans hf'cls)
  have hL : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hfne : (f : X.K) ≠ 0 := f.ne_zero
  have hune : (u : X.K) ≠ 0 := u.ne_zero
  have hpow : (u : X.K) ^ (l ^ n) = (f' : X.K) * (f : X.K)⁻¹ := by
    rw [hu]; field_simp
  have hinv : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) ((u : X.K) ^ (l ^ n)) := by
    intro γ hγ
    rw [hpow, map_mul, map_inv₀, hfinv γ hγ, hf'inv γ hγ]
  have hT : X.sl (ofSL ModularGroup.T) (u : X.K) = u := by
    refine TInv.sl_T_eq X N l n (Fact.out) hl2 hlN hN u hune hinv ?_
    intro δ hδ hδ'
    obtain ⟨g, hg, hfg⟩ := hfδ δ hδ hδ'
    obtain ⟨g', hg', hfg'⟩ := hf'δ δ hδ hδ'
    have hgne : g ≠ 0 := by
      rintro rfl
      rw [zero_pow hL.ne'] at hfg
      exact mul_ne_zero hfne ((map_ne_zero _).2 hfne) hfg
    refine ⟨g' * g⁻¹, ?_, ?_⟩
    · intro γ hγ
      rw [map_mul, map_inv₀, hg γ hγ, hg' γ hγ]
    · have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := (map_ne_zero _).2 hfne
      rw [mul_pow g', inv_pow, ← hfg, ← hfg', hu, map_mul, map_pow]
      field_simp
      ring
  have : Algebra.IsAlgebraic ℚ Ω := DlPow.isAlgebraic_of_tower X
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  rw [hu] at hf'dl
  exact DlPow.isDl_mul_lpow_cong X A l hlA n f u hfne hune hT φ φ' hfdl hf'dl r

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN
  exact GlobalTheory.isThB_coeff_cong Ω ε X A N l hj hl2 hlN (by omega)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevel
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

def scaleH (l : ℕ) (hl : 0 < l) (τ : ℍ) : ℍ :=
  UpperHalfPlane.mk ((l : ℂ) * τ) (by simp; positivity)

lemma coe_sl_apply (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ)) / (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp

lemma denom_sl_ne (g : SL(2, ℤ)) (z : ℍ) : ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
  have h2 := UpperHalfPlane.denom_ne_zero g z
  simpa [UpperHalfPlane.denom] using h2

theorem Vo_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 0 < l →
    (MF k L χ a → MF k (L * l) χ (Vo l a)) ∧ (CF k L χ a → CF k (L * l) χ (Vo l a)) := by
  intro k L l χ a hl
  have key : MF k L χ a → MF k (L * l) χ (Vo l a) := by
    rintro ⟨hP, hI⟩
    obtain ⟨hP', hq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl hP
    refine ⟨hP', ?_⟩
    intro γ hγ τ
    obtain ⟨m, hm⟩ := hγ
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this; exact this
    let γ' : SL(2, ℤ) := ⟨!![γ 0 0, (l : ℤ) * γ 0 1; (L : ℤ) * m, γ 1 1], by
      rw [Matrix.det_fin_two_of]; rw [hm] at hdet; push_cast at hdet; linear_combination hdet⟩
    have h1 : ((L : ℕ) : ℤ) ∣ γ' 1 0 := ⟨m, by simp [γ']⟩
    have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    have hc : ((γ 1 0 : ℤ) : ℂ) = (L : ℂ) * l * m := by rw [hm]; push_cast; ring
    have e1 : γ' • scaleH l hl τ = scaleH l hl (γ • τ) := by
      apply UpperHalfPlane.ext
      rw [coe_sl_apply]
      simp only [scaleH, UpperHalfPlane.coe_mk, coe_sl_apply]
      have hd := denom_sl_ne γ τ
      rw [hc] at hd ⊢
      simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      push_cast
      have hd2 : (L : ℂ) * m * (l * (τ : ℂ)) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
        convert hd using 1; ring
      field_simp
    rw [hq (γ • τ) (scaleH l hl (γ • τ)) rfl, hq τ (scaleH l hl τ) rfl, ← e1, hI γ' h1]
    simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, scaleH, UpperHalfPlane.coe_mk]
    rw [hc]; push_cast; ring_nf
  refine ⟨key, ?_⟩
  rintro ⟨hM, C, hC⟩
  refine ⟨key hM, C, fun τ => ?_⟩
  obtain ⟨_, hq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion l a hl hM.1
  rw [hq τ (scaleH l hl τ) rfl]
  have him : (scaleH l hl τ).im = l * τ.im := by
    change ((l:ℂ) * (τ:ℂ)).im = (l:ℝ) * (τ:ℂ).im
    simp
  have hle : τ.im ≤ (scaleH l hl τ).im := by
    rw [him]; have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith [τ.im_pos]
  calc ‖qs a (scaleH l hl τ)‖ ^ 2 * τ.im ^ k ≤ ‖qs a (scaleH l hl τ)‖ ^ 2 * (scaleH l hl τ).im ^ k := by
        gcongr
    _ ≤ C := hC _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevelStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffHeckeVOperator_raises_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 0 < l → (MF k L χ a → MF k (L * l) χ (Vo l a)) ∧ (CF k L χ a → CF k (L * l) χ (Vo l a)) := by
  first | exact @GlobalTheory.Vo_level | exact GlobalTheory.Vo_level | (intros; apply GlobalTheory.Vo_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlash
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlash
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem sum_exp_fin_div (l : ℕ) (hl : 0 < l) (m : ℕ) :
    ∑ j : Fin l, cexp (2 * π * Complex.I * ((j : ℕ) * m : ℂ) / l) = if l ∣ m then (l : ℂ) else 0 := by
  have hl' : l ≠ 0 := hl.ne'
  set ζ : ℂ := cexp (2 * π * Complex.I / l)
  have hζ : IsPrimitiveRoot ζ l := Complex.isPrimitiveRoot_exp l hl'
  have e : ∀ j : ℕ, cexp (2 * π * Complex.I * ((j : ℂ) * m) / l) = (ζ ^ m) ^ j := by
    intro j
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) l]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]
    simp
  · have h1 : ζ ^ m ≠ 1 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem slz_repU (k l : ℕ) (hk : 1 ≤ k) (hl : 0 < l) (j : Fin l) (f : ℍ → ℂ) (τ : ℍ) :
    slz k (repU l j) f τ = (l : ℂ)⁻¹ * f (ofComplex (((τ : ℂ) + (j : ℕ)) / l)) := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [slz, repU, Matrix.det_fin_two_of, pow_succ]
  field_simp
  simp

theorem polyB_Uo (l : ℕ) (a : ℕ → ℂ) (hl : 0 < l) (h : PolyB a) : PolyB (Uo l a) := by
  obtain ⟨C, A, hC⟩ := h
  have C0 : 0 ≤ C := by
    have := hC 0
    simp at this
    linarith [norm_nonneg (a 0)]
  refine ⟨C * (l : ℝ) ^ A, A, fun n => ?_⟩
  have h1 := hC (l * n)
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  calc ‖Uo l a n‖ = ‖a (l * n)‖ := rfl
    _ ≤ C * (((l * n : ℕ) : ℝ) + 1) ^ A := h1
    _ ≤ C * ((l : ℝ) * ((n : ℝ) + 1)) ^ A := by
        gcongr
        push_cast
        nlinarith
    _ = C * (l : ℝ) ^ A * ((n : ℝ) + 1) ^ A := by rw [mul_pow]; ring

theorem Uo_qs_sum_slz : ∀ (k l : ℕ) (a : ℕ → ℂ), 1 ≤ k → 0 < l → PolyB a → PolyB (Uo l a) ∧
    ∀ τ : ℍ, qs (Uo l a) τ = ∑ j : Fin l, slz k (repU l j) (qs a) τ := by
  intro k l a hk hl ha
  refine ⟨polyB_Uo l a hl ha, fun τ => ?_⟩
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hpos : ∀ j : Fin l, 0 < (((τ : ℂ) + (j : ℕ)) / l).im := by
    intro j
    rw [Complex.div_natCast_im]
    exact div_pos (by simpa using τ.im_pos) (by exact_mod_cast hl)
  simp_rw [slz_repU k l hk hl _ (qs a) τ]
  have hqs : ∀ j : Fin l, qs a (ofComplex (((τ : ℂ) + (j : ℕ)) / l))
      = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l)) := by
    intro j
    rw [ofComplex_apply_of_im_pos (hpos j)]
    rfl
  simp_rw [hqs]
  have hsum : ∀ j ∈ (Finset.univ : Finset (Fin l)),
      Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l)) :=
    fun j _ => ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 ⟨_, hpos j⟩).of_norm
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hsum]
  have hinner : ∀ n : ℕ, ∑ j : Fin l, a n * cexp (2 * π * Complex.I * n * (((τ : ℂ) + (j : ℕ)) / l))
      = a n * cexp (2 * π * Complex.I * n * τ / l) * (if l ∣ n then (l : ℂ) else 0) := by
    intro n
    rw [← sum_exp_fin_div l hl n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc (a n), ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hinner, ← tsum_mul_left]
  have hg : Function.Injective (fun m : ℕ => l * m) := fun x y h => Nat.eq_of_mul_eq_mul_left hl h
  rw [← hg.tsum_eq]
  · show ∑' m : ℕ, Uo l a m * cexp (2 * π * Complex.I * m * τ) = _
    refine tsum_congr fun m => ?_
    simp only [Uo, dvd_mul_right, if_true]
    rw [show (2 * π * Complex.I * ((l * m : ℕ) : ℂ) * τ / l : ℂ) = 2 * π * Complex.I * m * τ by
      push_cast
      field_simp]
    field_simp
  · intro n hn
    by_cases hd : l ∣ n
    · exact ⟨n / l, Nat.mul_div_cancel' hd⟩
    · exact (hn (by simp [hd])).elim

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionHeckeUEqSumSlashStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_heckeU_eq_sum_slash : ∀ (k l : ℕ) (a : ℕ → ℂ), 1 ≤ k → 0 < l → PolyB a → PolyB (Uo l a) ∧ ∀ τ : ℍ, qs (Uo l a) τ = ∑ j : Fin l, slz k (repU l j) (qs a) τ := by
  first | exact @GlobalTheory.EisM.Uo_qs_sum_slz | exact GlobalTheory.EisM.Uo_qs_sum_slz | (intros; apply GlobalTheory.EisM.Uo_qs_sum_slz <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCong
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCong
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThBCompat

private theorem cast_eq_of_dvd {N M : ℕ} (h : N ∣ M) (x y : ℤ) (hxy : (x : ZMod M) = (y : ZMod M)) :
    (x : ZMod N) = (y : ZMod N) := by
  have := congrArg (ZMod.castHom h (ZMod N)) hxy
  simpa only [map_intCast] using this

private theorem gamma_le {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h1)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h2)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h3)
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h4)

private theorem gamma1_le {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma1 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h1)
  · simpa using cast_eq_of_dvd h _ 1 (by simpa using h2)
  · simpa using cast_eq_of_dvd h _ 0 (by simpa using h3)

theorem isThB_succ_coeff_cong : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n : ℕ) (b : X.Fn l) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l (n + 1) b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l hl l2 hN hN1 hlA n b φ φ' h1 h2
  obtain ⟨f, hfI, hfc, hfδ, hfD⟩ := h1
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h2
  have hfc' : AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f := by
    have h := AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) (b ![1, 0])
    change (b ![1, 0]).val n = _
    rw [← h]
    change AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n)
      (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) (b ![1, 0])) = _
    rw [hfc]
    rfl
  obtain ⟨u, hu⟩ := GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc'.symm.trans hf'c)
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hu0 : (u : X.K) ≠ 0 := u.ne_zero
  have hle : CongruenceSubgroup.Gamma1 (N * l ^ (n + 1)) ≤ CongruenceSubgroup.Gamma1 (N * l ^ n) :=
    gamma1_le (Nat.mul_dvd_mul_left N (pow_dvd_pow l (Nat.le_succ n)))
  have hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f' := by rw [hu]; field_simp
  have hT := GlobalTheory.TInv.sl_T_eq X N l (n + 1) hl.out l2 hN hN1 (u : X.K) hu0 (by
      intro γ hγ
      rw [pow_succ, pow_mul, hL, map_pow, map_mul, map_inv₀, hfI γ hγ, hf'I γ (hle hγ)]) (by
      intro δ hδ hδ'
      obtain ⟨g, hgI, hg⟩ := hfδ δ hδ hδ'
      obtain ⟨g', hg'I, hg'⟩ := hf'δ δ hδ (gamma_le (pow_dvd_pow l (Nat.le_succ n)) hδ')
      have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := by
        intro h0; exact hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hg; exact mul_ne_zero hf0 hsf hg
      refine ⟨g' / g ^ l, ?_, ?_⟩
      · intro γ hγ; rw [map_div₀, map_pow, hgI γ hγ, hg'I γ (hle hγ)]
      · have key : ((u : X.K) * X.sl (ofSL δ) u) ^ (l ^ n) = (g' / g ^ l) ^ (l ^ n) := by
          rw [div_pow, ← pow_mul, ← pow_succ', ← hg', ← hg, hu, map_mul, map_pow]; field_simp; ring
        rw [pow_succ, pow_mul, pow_mul, key])
  have hfD' : IsDl X A l n 1 (f : X.K) φ := by
    obtain ⟨hA, a, c, κ, hκ, hac, ha, hc, hcg⟩ := hfD
    refine ⟨hA, a, c, κ, hκ, hac, ha, hc, fun r => ?_⟩
    obtain ⟨z, hz, e⟩ := hcg r
    exact ⟨l * z, A.mul_mem _ _ (natCast_mem A l) hz, by rw [e, pow_succ, mul_assoc]⟩
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, GlobalTheory.Glue.DlPow.isAlgebraic_of_tower X⟩
  exact GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD' (by rw [← hu]; exact hf'D)

end GlobalTheory.ThBCompat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsThBSuccCoeffCongStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cgA_coeff_of_isThB_succ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n : ℕ) (b : X.Fn l) (φ φ' : HahnSeries ℚ Ω),
  IsThB X A N l (n + 1) b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  first | (exact @GlobalTheory.ThBCompat.isThB_succ_coeff_cong) | (exact GlobalTheory.ThBCompat.isThB_succ_coeff_cong) | (intros; apply GlobalTheory.ThBCompat.isThB_succ_coeff_cong  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqMulAndQExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqMulAndQExpansion
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem polyB_mul (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : PolyB (mul a b) := by
  obtain ⟨C, A, hC⟩ := ha
  obtain ⟨C', A', hC'⟩ := hb
  have C0 : 0 ≤ C := by
    have := hC 0
    simp at this
    exact le_trans (norm_nonneg _) this
  have C0' : 0 ≤ C' := by
    have := hC' 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C * C', A + A' + 1, fun n => ?_⟩
  unfold mul
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2‖
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ‖a p.1 * b p.2‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, C * C' * ((n : ℝ) + 1) ^ (A + A') := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [norm_mul]
        have h1 : ((p.1 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : p.1 ≤ n := by omega
          exact_mod_cast Nat.add_le_add_right this 1
        have h2 : ((p.2 : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : p.2 ≤ n := by omega
          exact_mod_cast Nat.add_le_add_right this 1
        have e1 : ‖a p.1‖ ≤ C * ((n : ℝ) + 1) ^ A :=
          (hC p.1).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 A) C0)
        have e2 : ‖b p.2‖ ≤ C' * ((n : ℝ) + 1) ^ A' :=
          (hC' p.2).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 A') C0')
        calc ‖a p.1‖ * ‖b p.2‖ ≤ (C * ((n : ℝ) + 1) ^ A) * (C' * ((n : ℝ) + 1) ^ A') :=
              mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
          _ = C * C' * ((n : ℝ) + 1) ^ (A + A') := by rw [pow_add]; ring
    _ = (n + 1 : ℕ) * (C * C' * ((n : ℝ) + 1) ^ (A + A')) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    _ = C * C' * ((n : ℝ) + 1) ^ (A + A' + 1) := by push_cast; ring

theorem qs_mul (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) :
    qs (mul a b) = fun τ => qs a τ * qs b τ := by
  funext τ
  have sa := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 τ
  have sb := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).1 τ
  unfold qs
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm sa sb]
  congr 1
  funext n
  unfold mul
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have e : cexp (2 * π * Complex.I * (n : ℂ) * τ) =
      cexp (2 * π * Complex.I * (p.1 : ℂ) * τ) * cexp (2 * π * Complex.I * (p.2 : ℂ) * τ) := by
    rw [← Complex.exp_add, ← hp]
    congr 1
    push_cast
    ring
  rw [e]
  ring

theorem mul_main : (∀ a b : ℕ → ℂ, PolyB a → PolyB b → PolyB (mul a b) ∧ qs (mul a b) = fun τ => qs a τ * qs b τ) ∧ ∀ (k k' L : ℕ) (χ χ' : ℤ → ℂ) (a b : ℕ → ℂ), MF k L χ a → MF k' L χ' b → MF (k + k') L (fun d => χ d * χ' d) (mul a b) := by
  refine ⟨fun a b ha hb => ⟨polyB_mul a b ha hb, qs_mul a b ha hb⟩, ?_⟩
  intro k k' L χ χ' a b ha hb
  refine ⟨polyB_mul a b ha.1 hb.1, ?_⟩
  intro γ hγ τ
  rw [qs_mul a b ha.1 hb.1]
  simp only
  rw [ha.2 γ hγ τ, hb.2 γ hγ τ, pow_add]
  ring

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqMulAndQExpansionStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFormCoeffSeq_mul_and_qExpansion : (∀ a b : ℕ → ℂ, PolyB a → PolyB b → PolyB (mul a b) ∧ qs (mul a b) = fun τ => qs a τ * qs b τ) ∧ ∀ (k k' L : ℕ) (χ χ' : ℤ → ℂ) (a b : ℕ → ℂ), MF k L χ a → MF k' L χ' b → MF (k + k') L (fun d => χ d * χ' d) (mul a b) := by
  first | exact @GlobalTheory.EisM.mul_main | exact GlobalTheory.EisM.mul_main | (intros; apply GlobalTheory.EisM.mul_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumIndepReps
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumIndepReps
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RepInd

theorem exists_inj (L : ℕ) (Δ : Set M2) {ι κ : Type} (β : ι → M2) (β' : κ → M2)
    (hβ : LRep L Δ β) (hβ' : LRep L Δ β') :
    ∃ σ : κ → ι, Function.Injective σ ∧ ∃ g : κ → Gamma0 L,
      ∀ j, β' j = (((g j : SL(2, ℤ)) : M2)) * β (σ j) := by
  have hmem : ∀ j, ∃ p : Gamma0 L × ι, ((p.1 : SL(2, ℤ)) : M2) * β p.2 = β' j := by
    intro j
    have h1 : β' j ∈ Δ := by
      have := hβ'.mapsTo (Set.mem_univ ((1 : Gamma0 L), j))
      simpa using this
    obtain ⟨p, -, hp⟩ := hβ.surjOn h1
    exact ⟨p, hp⟩
  choose p hp using hmem
  refine ⟨fun j => (p j).2, ?_, fun j => (p j).1, fun j => (hp j).symm⟩
  intro j j' hjj
  have key : (((((p j).1 * ((p j').1)⁻¹ : Gamma0 L) : SL(2, ℤ)) : M2)) * β' j'
      = (((1 : Gamma0 L) : SL(2, ℤ)) : M2) * β' j := by
    rw [← hp j', ← hp j]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
      Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, one_mul]
    simp only at hjj
    rw [hjj, ← mul_assoc, mul_assoc (((p j).1 : SL(2, ℤ)) : M2)]
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, mul_one]
  have := hβ'.injOn (Set.mem_univ (((p j).1 * ((p j').1)⁻¹), j')) (Set.mem_univ ((1 : Gamma0 L), j)) key
  exact (congrArg Prod.snd this).symm

end GlobalTheory.EisM.RepInd

namespace GlobalTheory.EisM.RepInd

theorem term_eq (k L N : ℕ) (ε : DirichletCharacter ℂ N) (β : M2) (γ : Gamma0 L) (f : ℍ → ℂ)
    (hk : 1 ≤ k) (hNL : N ∣ L) (hdet : 0 < β.det) (hN : (N : ℤ) ∣ β 1 0) (hf : Inv k L (ch ε) f) (τ : ℍ) :
    ch ε (((((γ : SL(2, ℤ)) : M2)) * β) 0 0) * slz k ((((γ : SL(2, ℤ)) : M2)) * β) f τ
      = ch ε (β 0 0) * slz k β f τ := by
  obtain ⟨hc, -, hinv, -, -⟩ := GlobalTheory.T.slashIntMatrixPosDet_properties k f hk
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hg
  have hgL : (L : ℤ) ∣ g 1 0 := by
    have := (Gamma0_mem).1 γ.2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have hgN : (N : ℤ) ∣ g 1 0 := dvd_trans (Int.natCast_dvd_natCast.2 hNL) hgL
  have hgdet : 0 < (g : M2).det := by simp
  rw [hc _ _ hgdet hdet, (hinv L (ch ε)).1 hf g hgL]
  have hlin : slz k β (fun τ => ch ε (g 1 1) * f τ) τ = ch ε (g 1 1) * slz k β f τ := by
    simp only [slz]; ring
  rw [hlin]
  have hdetg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have h00 : ((((g : M2)) * β) 0 0 : ZMod N) = (g 0 0 : ZMod N) * (β 0 0 : ZMod N) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have : ((β 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hN
    push_cast
    rw [this]; simp
  have h1 : (g 0 0 : ZMod N) * (g 1 1 : ZMod N) = 1 := by
    have : ((g 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hgN
    have h2 : ((g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℤ) : ZMod N) = 1 := by rw [hdetg]; simp
    push_cast at h2
    rw [this, mul_zero, sub_zero] at h2
    exact h2
  simp only [ch]
  rw [h00, map_mul]
  have : ε (g 0 0 : ZMod N) * ε (g 1 1 : ZMod N) = 1 := by rw [← map_mul, h1, map_one]
  calc ε (g 0 0 : ZMod N) * ε (β 0 0 : ZMod N) * (ε (g 1 1 : ZMod N) * slz k β f τ)
      = (ε (g 0 0 : ZMod N) * ε (g 1 1 : ZMod N)) * (ε (β 0 0 : ZMod N) * slz k β f τ) := by ring
    _ = ε (β 0 0 : ZMod N) * slz k β f τ := by rw [this, one_mul]

theorem hsum_indep : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (β' : κ → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → LRep L Δ β' → Inv k L (ch ε) f → hsum k (ch ε) β f = hsum k (ch ε) β' f := by
  intro k L N ε Δ ι κ _ _ β β' f hk hNL hΔ hβ hβ' hf
  obtain ⟨σ, hσ, g, hg⟩ := exists_inj L Δ β β' hβ hβ'
  obtain ⟨σ', hσ', -, -⟩ := exists_inj L Δ β' β hβ' hβ
  have hcard : Fintype.card κ = Fintype.card ι :=
    le_antisymm (Fintype.card_le_of_injective σ hσ) (Fintype.card_le_of_injective σ' hσ')
  have hbij : Function.Bijective σ := (Fintype.bijective_iff_injective_and_card σ).2 ⟨hσ, hcard⟩
  have hin : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
    simpa using this
  funext τ
  simp only [hsum]
  symm
  refine Fintype.sum_bijective σ hbij _ _ ?_
  intro j
  rw [hg j]
  exact term_eq k L N ε (β (σ j)) (g j) f hk hNL (hΔ _ (hin _)).1 (hΔ _ (hin _)).2 hf τ

end GlobalTheory.EisM.RepInd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumIndepRepsStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacterSlashSum_indep_reps : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (β' : κ → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → LRep L Δ β' → Inv k L (ch ε) f → hsum k (ch ε) β f = hsum k (ch ε) β' f := by
  first | exact @GlobalTheory.EisM.RepInd.hsum_indep | exact GlobalTheory.EisM.RepInd.hsum_indep | (intros; apply GlobalTheory.EisM.RepInd.hsum_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLine
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLine
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

def hch (n : ℕ) (x : ℝ) : ℂ := cexp (2 * π * Complex.I * n * x)

theorem hch_norm (n : ℕ) (x : ℝ) : ‖hch n x‖ = 1 := by
  have : (2 * π * Complex.I * n * x : ℂ) = ((2 * π * n * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hch, this, Complex.norm_exp_ofReal_mul_I]

theorem hch_cont (n : ℕ) : Continuous (hch n) := by unfold hch; fun_prop

theorem hch_orth (m n : ℕ) : ∫ x in (0 : ℝ)..1, conj (hch m x) * hch n x = if m = n then 1 else 0 := by
  have e : ∀ x : ℝ, conj (hch m x) * hch n x = cexp ((2 * π * Complex.I * ((n : ℂ) - m)) * x) := fun x => by
    rw [hch, hch, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
    ring
  simp only [e]
  split_ifs with h
  · simp [h]
  · have h0 : ((n : ℂ) - m) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast Ne.symm h)
    have hc : (2 * π * Complex.I * ((n : ℂ) - m)) ≠ 0 := mul_ne_zero Complex.two_pi_I_ne_zero h0
    rw [integral_exp_mul_complex hc]
    have := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
    push_cast at this
    rw [mul_comm] at this
    simp [this]

theorem hasSum_parseval_unit (a b : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (F G : ℝ → ℂ) (hF : ∀ x, HasSum (fun n => a n * hch n x) (F x))
    (hG : ∀ x, HasSum (fun n => b n * hch n x) (G x)) :
    HasSum (fun n => conj (b n) * a n) (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
  let T : ℕ × ℕ → ℝ → ℂ := fun p x => conj (b p.1 * hch p.1 x) * (a p.2 * hch p.2 x)
  have hT : ∀ p, Continuous (T p) := fun p =>
    (Complex.continuous_conj.comp (continuous_const.mul (hch_cont p.1))).mul
      (continuous_const.mul (hch_cont p.2))
  have hn : ∀ p x, ‖T p x‖ = ‖b p.1‖ * ‖a p.2‖ := fun p x => by
    simp [T, hch_norm]
  have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := T)
    (fun p => (hT p).integrableOn_Ioc) (by
      refine (summable_mul_of_summable_norm' hb.norm hb ha.norm ha).congr fun p => ?_
      simp only [hn]
      simp)
  have hs : ∀ x, ∑' p, T p x = conj (G x) * F x := fun x => by
    have h1 : HasSum (fun n => conj (b n * hch n x)) (conj (G x)) := by
      simpa using (Complex.hasSum_conj'.2 (hG x))
    have h2 := tsum_mul_tsum_of_summable_norm h1.summable.norm (hF x).summable.norm
    rw [h1.tsum_eq, (hF x).tsum_eq] at h2
    exact h2.symm
  have hi : ∀ p, ∫ x in Set.Ioc (0 : ℝ) 1, T p x = conj (b p.1) * a p.2 * if p.1 = p.2 then 1 else 0 := fun p => by
    rw [← hch_orth, ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    simp only [T, map_mul]
    ring
  simp only [hs, hi] at h
  rw [← intervalIntegral.integral_of_le zero_le_one] at h
  have hinj : Function.Injective fun n : ℕ => (n, n) := fun _ _ h => (Prod.ext_iff.1 h).1
  have := (hinj.hasSum_iff (f := fun p : ℕ × ℕ => conj (b p.1) * a p.2 * if p.1 = p.2 then 1 else 0) (fun p hp => by
    rw [if_neg, mul_zero]
    intro h
    exact hp ⟨p.1, Prod.ext rfl h⟩)).2 h
  refine cast (congrArg (HasSum · _) (funext fun n => ?_)) this
  simp

theorem qs_line (a : ℕ → ℂ) (ha : PolyB a) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun n : ℕ => (a n * (Real.exp (-2 * π * n * y) : ℝ)) * hch n x)
      (qs a (ofComplex (x + y * Complex.I))) := by
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
  have hterm : ∀ n : ℕ, a n * cexp (2 * π * Complex.I * n * (ofComplex ((x : ℂ) + y * Complex.I) : ℂ)) =
      (a n * (Real.exp (-2 * π * n * y) : ℝ)) * hch n x := fun n => by
    rw [ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_mk, hch, Complex.ofReal_exp, mul_assoc (a n), ← Complex.exp_add]
    congr 2
    push_cast
    linear_combination (2 * π * n * y : ℂ) * Complex.I_mul_I
  have hs := ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 (ofComplex ((x : ℂ) + y * Complex.I))).of_norm
  have := hs.hasSum
  simp only [qs]
  simpa only [hterm] using this

theorem parseval_line : ∀ (h b : ℕ → ℂ) (y : ℝ), PolyB h → PolyB b → 0 < y →
    HasSum (fun n : ℕ => conj (h n) * b n * (Real.exp (-4 * π * n * y) : ℝ))
      (∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I))) := by
  intro h b y hh hb hy
  have sm : ∀ a : ℕ → ℂ, PolyB a → Summable fun n : ℕ => ‖a n * (Real.exp (-2 * π * n * y) : ℝ)‖ := fun a ha => by
    have := (qs_line a ha y hy 0).summable.norm
    simpa [hch_norm] using this
  have H := hasSum_parseval_unit _ _ (sm b hb) (sm h hh) _ _ (qs_line b hb y hy) (qs_line h hh y hy)
  refine cast (congrArg (HasSum · _) (funext fun n => ?_)) H
  have : Real.exp (-4 * π * n * y) = Real.exp (-2 * π * n * y) * Real.exp (-2 * π * n * y) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

end GlobalTheory.EisM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLineStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line : ∀ (h b : ℕ → ℂ) (y : ℝ), PolyB h → PolyB b → 0 < y → HasSum (fun n : ℕ => conj (h n) * b n * (Real.exp (-4 * π * n * y) : ℝ)) (∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I))) := by
  first | exact @GlobalTheory.EisM.parseval_line | exact GlobalTheory.EisM.parseval_line | (intros; apply GlobalTheory.EisM.parseval_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedHeckeUHeckeV
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedHeckeUHeckeV
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem eis_U_pair (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) (hl : l.Prime)
    (ha : ∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) (hb : ∀ y, b (l * y) = t * b y) (n : ℕ) (hn : n ≠ 0) :
    eis j c a b (l * n) = t * eis j c a b n := by
  have hl0 : l ≠ 0 := hl.ne_zero
  have hln : l * n ≠ 0 := mul_ne_zero hl0 hn
  simp only [eis, hln, hn, if_false]
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (p.1, l * p.2)) ?_ ?_ ?_ ?_
  · intro p hp _
    rw [Nat.mem_divisorsAntidiagonal] at hp ⊢
    refine ⟨?_, hln⟩
    rw [← hp.1]; ring
  · intro p _ _ q _ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Nat.eq_of_mul_eq_mul_left hl.pos h.2)
  · intro q hq hne
    rw [Nat.mem_divisorsAntidiagonal] at hq
    have h1 : ¬ l ∣ q.1 := by
      intro hd
      apply hne
      rw [ha q.1 (by exact_mod_cast hd)]; ring
    have h2 : l ∣ q.2 := by
      have : l ∣ q.1 * q.2 := by rw [hq.1]; exact dvd_mul_right _ _
      exact (hl.dvd_mul.mp this).resolve_left h1
    obtain ⟨y, hy⟩ := h2
    refine ⟨(q.1, y), ?_, ?_, ?_⟩
    · rw [Nat.mem_divisorsAntidiagonal]
      refine ⟨?_, hn⟩
      have h := hq.1
      rw [hy] at h
      have : l * (q.1 * y) = l * n := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left hl.pos this
    · intro h0
      apply hne
      have : b (q.2 : ℤ) = t * b (y : ℤ) := by rw [hy]; push_cast; exact hb _
      rw [this]
      simp only at h0
      linear_combination h0
    · ext <;> simp [hy]
  · intro p _ _
    simp only
    push_cast
    rw [hb]; ring

theorem eis_V_pair (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) (hl : l.Prime)
    (ha : ∀ x, a (l * x) = t * a x) (n : ℕ) (hn : n ≠ 0) :
    eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n := by
  have hl0 : l ≠ 0 := hl.ne_zero
  by_cases hd : l ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    simp only [Vo, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl.pos]
    simp only [eis, hn, hm, if_false]
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij_ne_zero (fun p _ _ => (l * p.1, p.2)) ?_ ?_ ?_ ?_
    · intro p hp _
      rw [Nat.mem_divisorsAntidiagonal] at hp ⊢
      refine ⟨?_, hn⟩
      rw [← hp.1]; ring
    · intro p _ _ q _ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Nat.eq_of_mul_eq_mul_left hl.pos h.1) h.2
    · intro q hq hne
      rw [Nat.mem_divisorsAntidiagonal] at hq
      have h1 : l ∣ q.1 := by
        by_contra h
        apply hne
        have : ¬ (l : ℤ) ∣ (q.1 : ℤ) := by exact_mod_cast h
        simp [this]
      obtain ⟨x, hx⟩ := h1
      refine ⟨(x, q.2), ?_, ?_, ?_⟩
      · rw [Nat.mem_divisorsAntidiagonal]
        refine ⟨?_, hm⟩
        have h := hq.1
        rw [hx] at h
        have : l * (x * q.2) = l * m := by rw [← h]; ring
        exact Nat.eq_of_mul_eq_mul_left hl.pos this
      · intro h0
        apply hne
        have hdv : (l : ℤ) ∣ (q.1 : ℤ) := by rw [hx]; push_cast; exact dvd_mul_right _ _
        simp only [hdv, if_true]
        have : a (q.1 : ℤ) = t * a (x : ℤ) := by rw [hx]; push_cast; exact ha _
        rw [this, hx]
        simp only at h0
        push_cast
        rw [mul_pow]
        linear_combination h0
      · ext <;> simp [hx]
    · intro p _ _
      have hdv : (l : ℤ) ∣ ((l * p.1 : ℕ) : ℤ) := by push_cast; exact dvd_mul_right _ _
      simp only [hdv, if_true]
      push_cast
      rw [ha, mul_pow]; ring
  · have h0 : Vo l (eis j c a b) n = 0 := by simp [Vo, hd]
    rw [h0, mul_zero]
    simp only [eis, hn, if_false]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hq
    have : ¬ (l : ℤ) ∣ (q.1 : ℤ) := by
      intro h
      apply hd
      have h' : l ∣ q.1 := by exact_mod_cast h
      rw [← hq.1]; exact dvd_mul_of_dvd_left h' _
    simp [this]

theorem eis_U_V (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) : l.Prime → ((∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) → (∀ y, b (l * y) = t * b y) → ∀ n, n ≠ 0 → eis j c a b (l * n) = t * eis j c a b n) ∧ (1 ≤ j → (∀ x, a (l * x) = t * a x) → ∀ n, n ≠ 0 → eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n) :=
  fun hl => ⟨fun ha hb n hn => eis_U_pair j l c t a b hl ha hb n hn,
    fun _ ha n hn => eis_V_pair j l c t a b hl ha n hn⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedHeckeUHeckeVStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffEisensteinSeriesTwisted_heckeU_heckeV : ∀ (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ), l.Prime → ((∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) → (∀ y, b (l * y) = t * b y) → ∀ n, n ≠ 0 → eis j c a b (l * n) = t * eis j c a b n) ∧ (1 ≤ j → (∀ x, a (l * x) = t * a x) → ∀ n, n ≠ 0 → eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n) := by
  first | exact @GlobalTheory.eis_U_V | exact GlobalTheory.eis_U_V | (intros; apply GlobalTheory.eis_U_V <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZsEqMulDepEis
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZsEqMulDepEis
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem zs_eq_mul_dep_eis : ∀ (k l j : ℕ) (u v A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zs k l u v (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c A u)) (dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1)) := by
  intro k l j u v A A' c c' hjk
  funext n
  unfold Zs mul
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : l ∣ p.1 ∨ l ∣ p.2
  · have hz : dep l (eis (k - 1 - j) c A u) p.1 * dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1) p.2 = 0 := by
      rcases h with h | h <;> simp [dep, h]
    rw [hz]
    simp [h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have p1 : p.1 ≠ 0 := fun e => h1 (e ▸ dvd_zero l)
    have p2 : p.2 ≠ 0 := fun e => h2 (e ▸ dvd_zero l)
    simp only [dep, eis, h1, h2, p1, p2, if_false, or_self]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
    have hx0 : (x.1 : ℂ) ≠ 0 := by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have : x.1 ≠ 0 := fun e => p1 (by rw [← this, e, zero_mul])
      exact_mod_cast this
    have hk : k - 2 = (k - 1 - j - 1) + j := by omega
    have hj : j + 1 - 1 = j := by omega
    rw [hk, hj, pow_add, div_pow]
    field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZsEqMulDepEisStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zs_monomial_ratio_eq_mul_dep_eis : ∀ (k l j : ℕ) (u v A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zs k l u v (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c A u)) (dep l (eis (j + 1) c' (fun y => A' y * v y) fun _ => 1)) := by
  first | exact @GlobalTheory.zs_eq_mul_dep_eis | exact GlobalTheory.zs_eq_mul_dep_eis | (intros; apply GlobalTheory.zs_eq_mul_dep_eis <;> assumption)
end
end
