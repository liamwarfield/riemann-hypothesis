module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFunctionalOddWeightOddPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommute
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGammaOneOfCoeffSeq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondAction
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondAction
open scoped MatrixGroups
open Matrix GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

noncomputable section

namespace GlobalTheory.CyclotomicQExpansion.ThnEx

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem toGQ_coe (σ : SL(2, ℤ)) : toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL σ := by
  have h : (0 : ℤ) < (σ : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  unfold toGQ
  rw [dite_eq_left h]
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [ofSL]

theorem kmap_SL_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (σ : SL(2, ℤ)) :
    ∀ a ∈ X.A l, X.kmap l (X.sl (toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv a ∈ X.A l := by
  apply KmapA.kmap_mem_A
  intro W hW
  refine ⟨fun c => ?_, ?_⟩
  · rw [ValuationSubring.mem_comap]
    change X.sl _ (algebraMap Ω X.K c) ∈ W
    rw [AlgEquiv.commutes]; exact hW.1 c
  · rw [ValuationSubring.mem_comap]
    change X.sl _ X.jK ∈ W
    rw [toGQ_coe, X.j_inv]; exact hW.2

private theorem exists_isDiam_of_coprime {N l d : ℕ} (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  obtain ⟨e, heN, hel⟩ := Nat.chineseRemainder hNl d 1
  have hcop : Nat.Coprime e (N * l) := by
    apply Nat.Coprime.mul_right
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq heN]; exact hd
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hel]; simp
  have hbez := Nat.gcd_eq_gcd_ab e (N * l)
  rw [hcop.gcd_eq_one] at hbez
  refine ⟨⟨!![Nat.gcdA e (N * l), -Nat.gcdB e (N * l); ((N * l : ℕ) : ℤ), (e : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; push_cast at hbez ⊢; linear_combination -hbez
  · refine Subgroup.mem_inf.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr ?_, CongruenceSubgroup.Gamma0_mem.mpr ?_⟩
    · simp
    · simp
  · simp only [en]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Int.cast_natCast]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heN

private theorem conj_mem_Gamma1_of_mem_Gamma0 {N : ℕ} {σ γ : SL(2, ℤ)} (hσ : σ ∈ CongruenceSubgroup.Gamma0 N)
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma1_in_Gamma0 N hγ
  have hg0 : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma0 N :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hγ0) (Subgroup.inv_mem _ hσ)
  have h1 : (⟨γ, hγ0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem]
    exact (CongruenceSubgroup.Gamma1_mem N γ).1 hγ
  have h2 : (⟨σ * γ * σ⁻¹, hg0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N :=
    (CongruenceSubgroup.Gamma0Map N).normal_ker.conj_mem _ h1 ⟨σ, hσ⟩
  exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h2)

private theorem kmap_kmap_eq_kmap_trans (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) (x : X.Khat l) :
    X.kmap l ψ (X.kmap l φ x) = X.kmap l (φ.trans ψ) x := by
  unfold Tower.kmap
  simp only [LinearMap.coe_restrictScalars]
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp]
  rfl

private theorem act_act_eq_act_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (σ τ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  funext u
  change X.kmap l (X.sl (toGQ (τ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.sl (toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
        (b (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ (mZl l (τ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)))) =
    X.kmap l (X.sl (toGQ ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (b (mZl l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
  have hm : mZl l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) * mZl l (τ : Matrix (Fin 2) (Fin 2) ℤ) := by
    simp only [mZl, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]
  have hs : (X.sl (ofSL σ * ofSL τ)).toRingEquiv =
      (X.sl (ofSL σ)).toRingEquiv.trans (X.sl (ofSL τ)).toRingEquiv := by
    ext f; exact X.sl_mul _ _ f
  rw [kmap_kmap_eq_kmap_trans, toGQ_coe, toGQ_coe, toGQ_coe, map_mul, Matrix.mulVec_mulVec, hm, hs]

theorem diam_BSet (X : Tower Ω ε) (N l w d : ℕ) [Fact l.Prime] (hN : 0 < N) (hNl : Nat.Coprime N l)
    (hd : Nat.Coprime d N) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.BSet N l w := by
  have hσ : IsDiam N l d (sgD N l d) := Classical.epsilon_spec (exists_isDiam_of_coprime hNl hd)
  obtain ⟨hpol, hinv⟩ := hb
  refine ⟨GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ (kmap_SL_A X l (sgD N l d)) b hpol, ?_⟩
  intro γ hγ
  obtain ⟨hσN, hσl⟩ := Subgroup.mem_inf.mp hσ.1
  obtain ⟨hγN, hγl⟩ := Subgroup.mem_inf.mp hγ
  have hconj : sgD N l d * γ * (sgD N l d)⁻¹ ∈ Gam N l :=
    Subgroup.mem_inf.mpr ⟨conj_mem_Gamma1_of_mem_Gamma0 hσN hγN,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hσl hγl) (Subgroup.inv_mem _ hσl)⟩
  have hswap : sgD N l d * γ = sgD N l d * γ * (sgD N l d)⁻¹ * sgD N l d :=
    (inv_mul_cancel_right _ _).symm
  rw [act_act_eq_act_mul X l _ _ b, hswap, ← act_act_eq_act_mul X l (sgD N l d * γ * (sgD N l d)⁻¹) (sgD N l d) b,
    hinv _ hconj]

theorem diam_B (X : Tower Ω ε) (N l w d : ℕ) [Fact l.Prime] (hN : 0 < N) (hNl : Nat.Coprime N l)
    (hd : Nat.Coprime d N) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l w := by
  have hle : X.B N l w ≤ (X.B N l w).comap (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span (diam_BSet X N l w d hN hNl hd x hx))
  exact hle hb

end GlobalTheory.CyclotomicQExpansion.ThnEx

namespace GlobalTheory.CyclotomicQExpansion

theorem thN_isThB : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime],
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
    ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) (thN X A N l n d b) ∧
      IsLat 1 (thN X A N l n d b) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : l.Prime := Fact.out
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hlN).symm
  have hb' := ThnEx.diam_B X N l w d (by omega) hNl hd b hb
  exact thN_spec X A N l n d b (GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l (IsAlgClosure.isAlgebraic (R := ℚ)) hj hl2 hlN (by omega) hlA n w hw _ hb')

end GlobalTheory.CyclotomicQExpansion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondActionStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lattice_diamond_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) (thN X A N l n d b) ∧ IsLat 1 (thN X A N l n d b) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.thN_isThB | exact GlobalTheory.CyclotomicQExpansion.thN_isThB | (intros; apply GlobalTheory.CyclotomicQExpansion.thN_isThB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSum
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem polyB_add_smul {u v : ℕ → ℂ} (c : ℂ) (hu : PolyB u) (hv : PolyB v) :
    PolyB (fun n => u n + c * v n) := by
  obtain ⟨C₁, A₁, h₁⟩ := hu
  obtain ⟨C₂, A₂, h₂⟩ := hv
  have hC₁ : 0 ≤ C₁ := by
    have := h₁ 0; simp at this; exact le_trans (norm_nonneg _) this
  have hC₂ : 0 ≤ C₂ := by
    have := h₂ 0; simp at this; exact le_trans (norm_nonneg _) this
  refine ⟨C₁ + ‖c‖ * C₂, A₁ + A₂, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have e1 : ((n : ℝ) + 1) ^ A₁ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  have e2 : ((n : ℝ) + 1) ^ A₂ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  calc ‖u n + c * v n‖ ≤ ‖u n‖ + ‖c‖ * ‖v n‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ A₁ + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ A₂) := by
        gcongr; exacts [h₁ n, h₂ n]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ (A₁ + A₂) + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ (A₁ + A₂)) := by
        gcongr
    _ = (C₁ + ‖c‖ * C₂) * ((n : ℝ) + 1) ^ (A₁ + A₂) := by ring

theorem qs_To_hsum : ∀ (k q : ℕ) (ε : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → 0 < q → ε 1 = 1 → PolyB a →
    PolyB (To k (ε q) q a) ∧ qs (To k (ε q) q a) = hsum k ε (repT q) (qs a) := by
  intro k q ε a hk hq hε ha
  obtain ⟨hU, hUq⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k q a hk hq ha
  obtain ⟨hV, hVq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion q a hq ha
  have hTo : To k (ε q) q a = fun n => Uo q a n + (ε q * (q : ℂ) ^ (k - 1)) * Vo q a n := by
    funext n; simp only [To, Uo]
  refine ⟨by rw [hTo]; exact polyB_add_smul _ hU hV, ?_⟩
  funext τ
  have sU : Summable fun n : ℕ => Uo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous _ hU).1 τ).of_norm
  have sV : Summable fun n : ℕ => Vo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous _ hV).1 τ).of_norm
  have hsplit : qs (To k (ε q) q a) τ = qs (Uo q a) τ + (ε q * (q : ℂ) ^ (k - 1)) * qs (Vo q a) τ := by
    rw [hTo]; simp only [qs]
    rw [← tsum_mul_left, ← sU.tsum_add (sV.mul_left _)]
    congr 1; funext n; ring
  have him : 0 < ((q : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hq) τ.im_pos
  have hσ : qs (Vo q a) τ = qs a ⟨(q : ℂ) * τ, him⟩ := hVq τ ⟨(q : ℂ) * τ, him⟩ rfl
  rw [hsplit, hUq τ, hσ, hsum, Fintype.sum_option]
  have hnone : ε (repT q none 0 0) * slz k (repT q none) (qs a) τ
      = (ε q * (q : ℂ) ^ (k - 1)) * qs a ⟨(q : ℂ) * τ, him⟩ := by
    have : ofComplex ((((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ))) = ⟨(q : ℂ) * τ, him⟩ := by
      rw [show (((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ)) = (q : ℂ) * τ by
        push_cast; ring]
      exact ofComplex_apply_of_im_pos him
    simp only [repT, slz, Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    rw [this]
    push_cast
    simp
    ring
  have hsome : ∀ j : Fin q, ε (repT q (some j) 0 0) * slz k (repT q (some j)) (qs a) τ
      = slz k (repU q j) (qs a) τ := by
    intro j
    simp only [repT, repU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hε, one_mul]
  rw [hnone, Finset.sum_congr rfl (fun j _ => hsome j)]
  ring

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSumStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffHeckeTOperator_qExpansion_slashSum : ∀ (k q : ℕ) (ε : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → 0 < q → ε 1 = 1 → PolyB a → PolyB (To k (ε q) q a) ∧ qs (To k (ε q) q a) = hsum k ε (repT q) (qs a) := by
  first | exact @GlobalTheory.EisM.qs_To_hsum | exact GlobalTheory.EisM.qs_To_hsum | (intros; apply GlobalTheory.EisM.qs_To_hsum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspForm
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.MeanSquareEstimates

theorem key (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y)) ∧
      ∑' n : ℕ, ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) ≤ C / y ^ k := by
  have hp := GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line h h y hc.1.1 hc.1.1 hy
  set I := ∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))
  have hr := Complex.hasSum_re hp
  have e : (fun n : ℕ => (conj (h n) * h n * ((Real.exp (-4 * π * n * y) : ℝ) : ℂ)).re) =
      fun n : ℕ => ‖h n‖ ^ 2 * Real.exp (-4 * π * n * y) := by
    funext n
    rw [Complex.conj_mul']
    norm_cast
  rw [e] at hr
  refine ⟨hr.summable, ?_⟩
  rw [hr.tsum_eq]
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) 1, ‖conj (qs h (ofComplex (x + y * Complex.I))) * qs h (ofComplex (x + y * Complex.I))‖ ≤ C / y ^ k := by
    intro x _
    have him : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
    rw [ofComplex_apply_of_im_pos him, Complex.conj_mul']
    have h1 := hC ⟨(x : ℂ) + y * Complex.I, him⟩
    have h2 : (⟨(x : ℂ) + y * Complex.I, him⟩ : ℍ).im = y := by simp [UpperHalfPlane.im]
    rw [h2] at h1
    rw [le_div_iff₀ (by positivity)]
    simpa using h1
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc I.re ≤ ‖I‖ := Complex.re_le_norm I
    _ ≤ C / y ^ k * |1 - 0| := this
    _ = C / y ^ k := by simp

theorem key2 (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ) (hc : CF k L χ h) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖qs h τ‖ ^ 2 * τ.im ^ k ≤ C) (t : ℝ) (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ C * (4 * π) ^ k / t ^ k := by
  have hy : 0 < t / (4 * π) := by positivity
  obtain ⟨hs, hb⟩ := key k L χ h hc C hC _ hy
  have e : ∀ n : ℕ, -4 * π * n * (t / (4 * π)) = -(n : ℝ) * t := fun n => by field_simp
  simp only [e] at hs hb
  have e2 : C / (t / (4 * π)) ^ k = C * (4 * π) ^ k / t ^ k := by rw [div_pow]; field_simp
  rw [e2] at hb
  exact (hs.sum_le_tsum _ (fun n _ => by positivity)).trans hb

theorem blk (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (a0 : a 0 = 0) (k : ℕ) (D : ℝ)
    (hD : ∀ t : ℝ, 0 < t → ∀ N : ℕ, ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k)
    (s : ℝ) (hs : 0 < s) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) := by
  set x : ℝ := (2 : ℝ) ^ (-s) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hD0 : 0 ≤ D := by
    have := hD 1 one_pos 0
    simpa using this
  set G : ℕ → ℕ → ℝ := fun j n => Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) with hG
  have G0 : ∀ j n, 0 ≤ G j n := fun j n => by have := ha n; positivity
  have pt : ∀ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ j ∈ Finset.range N, G j n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [a0, zero_div]; exact Finset.sum_nonneg fun j _ => G0 j 0
    set j := Nat.log 2 n
    have hj1 : 2 ^ j ≤ n := Nat.pow_log_le_self 2 hn0.ne'
    have hj2 : n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hjN : j < N := by
      have : j < 2 ^ j := Nat.lt_two_pow_self
      have := Finset.mem_range.mp hn
      omega
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => G0 i n) (Finset.mem_range.mpr hjN))
    have npos : (0 : ℝ) < n := by exact_mod_cast hn0
    have h2j : ((2 : ℝ) ^ j) ≤ n := by exact_mod_cast hj1
    have h2j' : (n : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
      have : (n : ℝ) < ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hj2
      push_cast at this; rw [pow_succ] at this; linarith
    have P : ((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s ≤ (n : ℝ) ^ k * (n : ℝ) ^ s := by gcongr
    have E : 1 ≤ Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have : (n : ℝ) * ((2 : ℝ) ^ j)⁻¹ ≤ 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]; linarith
      linarith
    have hxj : x ^ j = (((2 : ℝ) ^ j) ^ s)⁻¹ := by
      rw [hxdef, Real.rpow_neg (by norm_num), inv_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have L : (n : ℝ) ^ ((k : ℝ) + s) = (n : ℝ) ^ k * (n : ℝ) ^ s := by
      rw [Real.rpow_add npos, Real.rpow_natCast]
    have R : G j n = a n * (Real.exp 2 * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹)) / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
      rw [hG]; dsimp only; rw [hxj]; field_simp
    rw [L, R]
    have an := ha n
    calc a n / ((n : ℝ) ^ k * (n : ℝ) ^ s) ≤ a n / (((2 : ℝ) ^ j) ^ k * ((2 : ℝ) ^ j) ^ s) := by
          gcongr
      _ ≤ _ := by gcongr; exact le_mul_of_one_le_right an E
  calc ∑ n ∈ Finset.range N, a n / (n : ℝ) ^ ((k : ℝ) + s) ≤ ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range N, G j n :=
        Finset.sum_le_sum pt
    _ = ∑ j ∈ Finset.range N, ∑ n ∈ Finset.range N, G j n := Finset.sum_comm
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) *
          ∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) * ((2 : ℝ) ^ j)⁻¹) := by
        simp only [hG, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range N, Real.exp 2 * (x ^ j / ((2 : ℝ) ^ j) ^ k) * (D / (((2 : ℝ) ^ j)⁻¹) ^ k) := by
        gcongr with j _
        exact hD _ (by positivity) N
    _ = ∑ j ∈ Finset.range N, Real.exp 2 * D * x ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [inv_pow]; field_simp
    _ = Real.exp 2 * D * ∑ j ∈ Finset.range N, x ^ j := by rw [Finset.mul_sum]
    _ ≤ Real.exp 2 * D * (x ^ 0 / (1 - x)) := by
        gcongr
        rw [Finset.range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one hx0 hx1
    _ = Real.exp 2 * D / (1 - x) := by rw [pow_zero]; ring

theorem geo (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) : s / 3 ≤ 1 - (2 : ℝ) ^ (-s) := by
  have L := Real.log_two_gt_d9
  have h1 : 1 + s * Real.log 2 ≤ (2 : ℝ) ^ s := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    linarith [Real.add_one_le_exp (Real.log 2 * s)]
  have hp : 0 < 1 + s * Real.log 2 := by nlinarith
  have h2 : (2 : ℝ) ^ (-s) ≤ 1 / (1 + s * Real.log 2) := by
    rw [Real.rpow_neg (by norm_num), one_div]
    exact inv_anti₀ hp h1
  have h3 : 1 / (1 + s * Real.log 2) ≤ 1 - s / 3 := by
    rw [div_le_iff₀ hp]
    have q : 0 ≤ Real.log 2 - 1 / 3 - s * Real.log 2 / 3 := by nlinarith
    nlinarith [mul_nonneg hs.le q]
  linarith

end GlobalTheory.MeanSquareEstimates

namespace GlobalTheory


open GlobalTheory.MeanSquareEstimates in
theorem rankin_mean_square : ∀ (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ), 1 ≤ k → CF k L χ h → h 0 = 0 ∧ (∃ C : ℝ, ∀ n : ℕ, ‖h n‖ ^ 2 ≤ C * (n : ℝ) ^ k) ∧ (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s)) ∧ ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ C := by
  intro k L χ h hk hc
  obtain ⟨C, hC⟩ := hc.2
  have C0 : 0 ≤ C := le_trans (by positivity) (hC UpperHalfPlane.I)
  set D := C * (4 * π) ^ k with hDdef
  have D0 : 0 ≤ D := by positivity
  have K := key2 k L χ h hc C hC
  have K1 : ∀ t : ℝ, 0 < t → ∀ n : ℕ, ‖h n‖ ^ 2 * Real.exp (-(n : ℝ) * t) ≤ D / t ^ k := by
    intro t ht n
    refine le_trans ?_ (K t ht (n + 1))
    exact Finset.single_le_sum (f := fun m : ℕ => ‖h m‖ ^ 2 * Real.exp (-(m : ℝ) * t)) (fun m _ => by positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have h0 : h 0 = 0 := by
    have lim : Tendsto (fun t : ℝ => D / t ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
    have b : ‖h 0‖ ^ 2 ≤ 0 := by
      refine ge_of_tendsto lim ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      simpa using K1 t ht 0
    have : ‖h 0‖ = 0 := by nlinarith [norm_nonneg (h 0)]
    exact norm_eq_zero.mp this
  have B : ∀ s : ℝ, 0 < s → ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s)) :=
    fun s hs N => blk (fun n => ‖h n‖ ^ 2) (fun n => by positivity) (by simp [h0]) k D K s hs N
  have nn : ∀ s : ℝ, ∀ n : ℕ, 0 ≤ ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) := fun s n => by positivity
  refine ⟨h0, ⟨D * Real.exp 1, fun n => ?_⟩, fun s hs => summable_of_sum_range_le (nn s) (B s hs), ⟨3 * (Real.exp 2 * D), fun s hs hs1 => ?_⟩⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h0, zero_pow (by omega : k ≠ 0)]
    have npos : (0 : ℝ) < n := by exact_mod_cast hn
    have := K1 (n : ℝ)⁻¹ (by positivity) n
    rw [neg_mul, mul_inv_cancel₀ npos.ne', inv_pow, div_inv_eq_mul] at this
    have e : ‖h n‖ ^ 2 = ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [e]
    calc ‖h n‖ ^ 2 * Real.exp (-1) * Real.exp 1 ≤ D * (n : ℝ) ^ k * Real.exp 1 := by gcongr
      _ = D * Real.exp 1 * (n : ℝ) ^ k := by ring
  · have T := Real.tsum_le_of_sum_range_le (nn s) (B s hs)
    have g := geo s hs hs1
    have pos : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
    calc s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ s * (Real.exp 2 * D / (1 - (2 : ℝ) ^ (-s))) := by gcongr
      _ ≤ 3 * (Real.exp 2 * D) := by
        rw [mul_div_assoc', div_le_iff₀ pos]
        have : 0 ≤ Real.exp 2 * D := by positivity
        nlinarith

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspFormStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_mean_square_cuspForm : ∀ (k L : ℕ) (χ : ℤ → ℂ) (h : ℕ → ℂ), 1 ≤ k → CF k L χ h → h 0 = 0 ∧ (∃ C : ℝ, ∀ n : ℕ, ‖h n‖ ^ 2 ≤ C * (n : ℝ) ^ k) ∧ (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s)) ∧ ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖h n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s) ≤ C := by
  first | exact @GlobalTheory.rankin_mean_square | exact GlobalTheory.rankin_mean_square | (intros; apply GlobalTheory.rankin_mean_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommuteStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTowerB_admissibleHecke_commute : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T T' : Letter, admitted N l T → admitted N l T' → ∀ b ∈ X.B N l w, X.op N l T (X.op N l T' b) = X.op N l T' (X.op N l T b) := by
  first | exact @GlobalTheory.KZ.B_op_comm | exact GlobalTheory.KZ.B_op_comm | (intros; apply GlobalTheory.KZ.B_op_comm <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGamma1OfIsCuspFormCoeffSeq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGamma1OfIsCuspFormCoeffSeq
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma norm_petersson_self (k : ℕ) (h : ℍ → ℂ) (z : ℍ) :
    ‖petersson (k : ℤ) h h z‖ = ‖h z‖ ^ 2 * z.im ^ k := by
  simp only [petersson, norm_mul, Complex.norm_conj, zpow_natCast, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos z.im_pos]
  ring

lemma isZeroAtImInfty_of_bound (k : ℕ) (hk : 1 ≤ k) (h : ℍ → ℂ) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖h τ‖ ^ 2 * τ.im ^ k ≤ C) : IsZeroAtImInfty h := by
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero]
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hsq : Tendsto (fun τ : ℍ => ‖h τ‖ ^ 2) atImInfty (𝓝 0) := by
    have hlim : Tendsto (fun τ : ℍ => max C 0 * (τ.im)⁻¹) atImInfty (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp him).const_mul (max C 0)
    refine squeeze_zero' (Eventually.of_forall fun τ => by positivity) ?_ hlim
    filter_upwards [him.eventually_ge_atTop 1] with τ hτ
    have hpos : 0 < τ.im := τ.im_pos
    have hpow : τ.im ≤ τ.im ^ k := by
      calc τ.im = τ.im ^ 1 := (pow_one _).symm
        _ ≤ τ.im ^ k := pow_le_pow_right₀ hτ hk
    rw [le_mul_inv_iff₀ hpos]
    calc ‖h τ‖ ^ 2 * τ.im ≤ ‖h τ‖ ^ 2 * τ.im ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ C := hC τ
      _ ≤ max C 0 := le_max_left _ _
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

end GlobalTheory.EisM

theorem GlobalTheory.EisM.cuspForm_of_CF : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) a → ∃ f : CuspForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  intro k L N ε a hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.modularForm_gammaOne_of_coeffSeq k L N ε a hL hNL hcf.1
  obtain ⟨C, hC⟩ := hcf.2
  have hall : ∀ γ : SL(2, ℤ), IsZeroAtImInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] γ) := by
    intro γ
    refine isZeroAtImInfty_of_bound k hk _ C fun τ => ?_
    have h1 := congrArg norm (petersson_slash_SL (k : ℤ) (f : ℍ → ℂ) f γ τ)
    rw [norm_petersson_self, norm_petersson_self, hf] at h1
    rw [hf, h1]
    exact hC _
  refine ⟨⟨f.toSlashInvariantForm, f.holo', ?_⟩, hf⟩
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  exact hall γ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGamma1OfIsCuspFormCoeffSeqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) a → ∃ f : CuspForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  first | exact @GlobalTheory.EisM.cuspForm_of_CF | exact GlobalTheory.EisM.cuspForm_of_CF | (intros; apply GlobalTheory.EisM.cuspForm_of_CF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

open Asymptotics Function

theorem isBigO_qParam_pow_of_qExpansion_coeff_zero {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ) (h : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
    intro i hi
    have := h i hi
    rw [qExpansion_coeff] at this
    exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero (by exact_mod_cast i.factorial_ne_zero))
  obtain ⟨g, hg, hfg⟩ := (natCast_le_analyticOrderAt ha).mp h1
  have ht := qParam_tendsto_atImInfty (h := 1) one_pos
  have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp ht).isBigO_one ℂ
  have h3 := (isBigO_refl (fun τ : ℍ => Periodic.qParam 1 τ ^ m) atImInfty).mul h2
  simp only [mul_one] at h3
  refine h3.congr' ?_ EventuallyEq.rfl
  filter_upwards [ht.eventually hfg] with τ hτ
  rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
  rw [hτ]; simp

theorem qExpansion_coeff_zero_of_isBigO_qParam_pow {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have h1 : (m : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hlt.ne_top
    rw [← hj] at hlt
    have hjm : j < m := by exact_mod_cast hlt
    obtain ⟨g, hg, hg0, hfg⟩ := ha.analyticOrderAt_eq_natCast.mp hj.symm
    have ht := qParam_tendsto_atImInfty (h := 1) one_pos
    have h2 : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty]
        fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j) := by
      have h3 := (isBigO_refl (fun τ : ℍ => (Periodic.qParam 1 τ ^ j)⁻¹) atImInfty).mul h
      refine h3.congr' ?_ ?_
      · filter_upwards [ht.eventually hfg] with τ hτ
        rw [SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero] at hτ
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        rw [hτ, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
      · refine Eventually.of_forall fun τ => ?_
        have hq : Periodic.qParam 1 τ ≠ 0 := Periodic.qParam_ne_zero _
        simp only
        rw [pow_sub₀ _ hq hjm.le, mul_comm]
    have h4 : Tendsto (fun τ : ℍ => Periodic.qParam 1 τ ^ (m - j)) atImInfty (𝓝 0) := by
      have := ht.pow (m - j)
      rwa [zero_pow (by omega)] at this
    exact hg0 (tendsto_nhds_unique (hg.continuousAt.tendsto.comp ht) (h2.trans_tendsto h4))
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha] at h1
  intro n hn
  rw [qExpansion_coeff, h1 n hn, mul_zero]

theorem modularFormNorm_isBigO_self_atImInfty {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))
  have hb : ∀ q : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ),
      SlashInvariantForm.quotientFunc (k := k) f q =O[atImInfty] fun _ => (1 : ℂ) := by
    refine Quotient.forall.mpr fun ⟨r, hr⟩ => ?_
    have hc : IsCusp OnePoint.infty 𝒮ℒ := Fact.out
    have := (ModularForm.translate f r⁻¹).bdd_at_cusps' (c := OnePoint.infty)
      (by simpa using hc.of_isFiniteRelIndex_conj hr)
    rw [OnePoint.isBoundedAt_infty_iff] at this
    have h2 : (ModularForm.translate f r⁻¹ : ℍ → ℂ) =O[atImInfty] (1 : ℍ → ℝ) := this
    refine IsBigO.trans h2 ?_
    exact IsBigO.of_bound 1 (by simp)
  have h1 : (∏ q ∈ Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)),
      SlashInvariantForm.quotientFunc (k := k) f q) =O[atImInfty] fun _ => (1 : ℂ) := by
    have := IsBigO.finsetProd (s := Finset.univ.erase (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))) (fun q _ => hb q)
    simpa [Finset.prod_fn] using this
  have h2 := (isBigO_refl (f : ℍ → ℂ) atImInfty).mul h1
  simp only [mul_one] at h2
  refine h2.congr_left fun τ => ?_
  have h3 := congr_fun (Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (k := k) f q)
    (Finset.mem_univ (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)))) τ
  rw [ModularForm.coe_norm]
  have h4 : SlashInvariantForm.quotientFunc (k := k) f (⟦1⟧ : 𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ)) = f := by simp
  rw [h4, Pi.mul_apply] at h3
  convert h3

theorem exists_sturmBound_modularForm_arithmetic {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : ModularForm Γ k, (∀ n < m, (qExpansion 1 f).coeff n = 0) → f = 0 := by
  refine ⟨(k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1, fun f hf => ?_⟩
  have h1 := qExpansion_coeff_zero_of_isBigO_qParam_pow one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) _
    ((modularFormNorm_isBigO_self_atImInfty f).trans (isBigO_qParam_pow_of_qExpansion_coeff_zero hΓ f _ hf))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

theorem sturm_coef_zero : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N), 0 < L → N ∣ L →
    ∃ B : ℕ, ∀ a, MF k L (ch ε) a → (∀ n < B, a n = 0) → a = 0 := by
  intro k L N ε hL hN
  have hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨m, hm⟩ := exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)
  refine ⟨m, fun a ha hz => ?_⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.modularForm_gammaOne_of_coeffSeq k L N ε a hL hN ha
  have hc : ∀ n, (qExpansion 1 f).coeff n = a n := by
    intro n
    have := GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane a ha.1 n
    unfold coef at this
    rw [← this, hf]
  have h0 : f = 0 := hm f fun n hn => by rw [hc n]; exact hz n hn
  funext n
  rw [← hc n, h0]
  simp [qExpansion_zero]

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeqStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a, MF k L (ch ε) a → (∀ n < B, a n = 0) → a = 0 := by
  first | exact @GlobalTheory.EisM.sturm_coef_zero | exact GlobalTheory.EisM.sturm_coef_zero | (intros; apply GlobalTheory.EisM.sturm_coef_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUOperatorLowersLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUOperatorLowersLevel
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.LevelLower

def idx (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) : Fin l :=
  ⟨(((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l).val, ZMod.val_lt _⟩

lemma idx_cast (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) :
    ((idx l b d j : ℕ) : ZMod l) = (((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l) := by
  simp [idx, ZMod.natCast_zmod_val]

lemma idx_inj (l : ℕ) [NeZero l] (a b d : ℤ) (had : ((a * d : ℤ) : ZMod l) = 1) :
    Function.Injective (idx l b d) := by
  intro j₁ j₂ h
  have h' := congrArg (fun x : Fin l => ((x : ℕ) : ZMod l)) h
  simp only [idx_cast] at h'
  push_cast at h' had
  have e : ((j₁ : ℕ) : ZMod l) = ((j₂ : ℕ) : ZMod l) := by
    linear_combination (a : ZMod l) ^ 2 * h' -
      (((j₁ : ℕ) : ZMod l) - ((j₂ : ℕ) : ZMod l)) * (1 + (a : ZMod l) * d) * had
  apply Fin.ext
  rw [ZMod.natCast_eq_natCast_iff'] at e
  simpa [Nat.mod_eq_of_lt j₁.2, Nat.mod_eq_of_lt j₂.2] using e

lemma coset (L l : ℕ) [NeZero l] (hlL : l ∣ L) (γ : SL(2, ℤ)) (hc : (L : ℤ) ∣ γ 1 0) (j : Fin l) :
    ∃ γ' : SL(2, ℤ), ((L * l : ℕ) : ℤ) ∣ γ' 1 0 ∧
      γ' 1 1 = γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) ∧
      repU l j * (γ : M2) = (γ' : M2) * repU l (idx l (γ 0 1) (γ 1 1) j) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
  have hdiv : (l : ℤ) ∣ γ 0 1 + ((j : ℕ) : ℤ) * γ 1 1 -
      (γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0) * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have hj' := idx_cast l (γ 0 1) (γ 1 1) j
    have hd1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at hj' hd1 ⊢
    rw [hj']
    linear_combination (-((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l))) * hd1 -
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) *
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) * hc0
  obtain ⟨B, hB⟩ := hdiv
  obtain ⟨m, hm⟩ := hc
  refine ⟨⟨!![γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0, B; (l : ℤ) * γ 1 0,
      γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)], ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + γ 1 0 * hB
  · refine ⟨m, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [hm]; push_cast; ring
  · simp
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [repU, Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination hB | linear_combination -hB

end GlobalTheory.LevelLower

namespace GlobalTheory.LevelLower

lemma slz_sum (k : ℕ) (δ : M2) {ι : Type} [Fintype ι] (F : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => ∑ i, F i τ) τ = ∑ i, slz k δ (F i) τ := by
  simp only [slz, Finset.mul_sum]

lemma slz_smul (k : ℕ) (δ : M2) (c : ℂ) (f : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => c * f τ) τ = c * slz k δ f τ := by
  simp only [slz]; ring

lemma per (L : ℕ) (χ : ℤ → ℂ) (hχ : ∀ d, χ (d + L) = χ d) (m : ℤ) : ∀ d : ℤ, χ (d + m * L) = χ d := by
  refine Int.induction_on m ?_ ?_ ?_
  · intro d; simp
  · intro i ih d
    rw [show d + ((i : ℤ) + 1) * (L : ℤ) = (d + (i : ℤ) * L) + L by ring, hχ, ih]
  · intro i ih d
    have := hχ (d + (-(i : ℤ) - 1) * L)
    rw [show d + (-(i : ℤ) - 1) * (L : ℤ) + L = d + -(i : ℤ) * L by ring, ih] at this
    exact this.symm

end GlobalTheory.LevelLower

theorem GlobalTheory.Uo_lowers_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L →
    (∀ d, χ (d + L) = χ d) → MF k (L * l) χ a → MF k L χ (Uo l a) := by
  intro k L l χ a hk hl hlL hχ hMF
  obtain ⟨hP, hI⟩ := hMF
  haveI : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨hPU, hqs⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k l a hk hl.pos hP
  obtain ⟨hcoc, -, hinv, -, -⟩ := GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk
  have hI' := (hinv (L * l) χ).mp hI
  refine ⟨hPU, ?_⟩
  rw [(GlobalTheory.T.slashIntMatrixPosDet_properties k (qs (Uo l a)) hk).2.2.1]
  intro γ hc
  have hg : qs (Uo l a) = fun τ => ∑ j : Fin l, slz k (repU l j) (qs a) τ := funext hqs
  have hdU : ∀ j : Fin l, 0 < (repU l j).det := by
    intro j; simp [repU, Matrix.det_fin_two_of]; exact hl.pos
  have hdγ : ∀ γ : SL(2, ℤ), 0 < (γ : M2).det := by
    intro γ; rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos

  have had : ((γ 0 0 * γ 1 1 : ℤ) : ZMod l) = 1 := by
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2
      rw [Matrix.det_fin_two] at this
      exact this
    have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have h1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at h1 hc0 ⊢
    rw [hc0, mul_zero, sub_zero] at h1
    exact h1
  let e : Fin l ≃ Fin l := Equiv.ofBijective (GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1))
    (Finite.injective_iff_bijective.mp (GlobalTheory.LevelLower.idx_inj l _ _ _ had))
  have key : ∀ (τ : ℍ) (j : Fin l), slz k (γ : M2) (slz k (repU l j) (qs a)) τ =
      χ (γ 1 1) * slz k (repU l (e j)) (qs a) τ := by
    intro τ j
    obtain ⟨γ', h1, h2, h3⟩ := GlobalTheory.LevelLower.coset L l hlL γ hc j
    rw [← hcoc _ _ (hdU j) (hdγ γ), h3, hcoc _ _ (hdγ γ') (hdU _), hI' γ' h1,
      GlobalTheory.LevelLower.slz_smul, h2]
    obtain ⟨m, hm⟩ := hc
    have : χ (γ 1 1 - γ 1 0 * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)) = χ (γ 1 1) := by
      rw [hm, show γ 1 1 - (L : ℤ) * m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) =
        γ 1 1 + (-(m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ))) * L by ring,
        GlobalTheory.LevelLower.per L χ hχ]
    rw [this]
    rfl
  rw [hg]
  funext τ
  rw [GlobalTheory.LevelLower.slz_sum]
  simp_rw [key τ]
  rw [← Finset.mul_sum, Equiv.sum_comp e (fun j => slz k (repU l j) (qs a) τ)]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUOperatorLowersLevelStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffHeckeUOperator_lowers_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k (L * l) χ a → MF k L χ (Uo l a) := by
  first | exact @GlobalTheory.Uo_lowers_level | exact GlobalTheory.Uo_lowers_level | (intros; apply GlobalTheory.Uo_lowers_level <;> assumption)
end
end
