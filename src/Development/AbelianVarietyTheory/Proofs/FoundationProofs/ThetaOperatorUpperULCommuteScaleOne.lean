module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormGamma1PrimePowInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormGamma1PrimePowInvariant
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.HeckeUNormInv

theorem coe_toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  simp [toGQ, h]

theorem coe_ofSL (γ : SL(2, ℤ)) :
    (((ofSL γ : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  simp [ofSL]

theorem det_mj (j l : ℤ) (hl : 0 < l) : 0 < (!![1, j; 0, l] : Matrix (Fin 2) (Fin 2) ℤ).det := by
  simp [Matrix.det_fin_two]; exact hl

theorem key (N l n : ℕ) (hn : 0 < n) (hl : 0 < l) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 (N * l ^ n))
    (j : ℕ) : ∃ γ' ∈ CongruenceSubgroup.Gamma1 (N * l ^ n),
      toGQ !![1, (j : ℤ); 0, (l : ℤ)] * ofSL γ =
        ofSL γ' * toGQ !![1, ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ); 0, (l : ℤ)] := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨ha, hd, hc⟩ := (CongruenceSubgroup.Gamma1_mem _ _).1 hγ
  have hdvd : l ∣ N * l ^ n := dvd_mul_of_dvd_right (dvd_pow_self l hn.ne') N
  have ha' : ((γ 0 0 : ℤ) : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) ha; rwa [map_intCast, map_one] at this
  have hd' : ((γ 1 1 : ℤ) : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) hd; rwa [map_intCast, map_one] at this
  have hc' : ((γ 1 0 : ℤ) : ZMod l) = 0 := by
    have := congrArg (ZMod.castHom hdvd (ZMod l)) hc; rwa [map_intCast, map_zero] at this
  have hk : ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ) = (γ 0 1 + j) % (l : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [hk]
  set k : ℤ := (γ 0 1 + j) % (l : ℤ) with hkdef
  obtain ⟨b', hb'⟩ : (l : ℤ) ∣ γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ha', hd', hc', hkdef, ZMod.intCast_mod]
    push_cast; ring
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0 + j * γ 1 0, b'; l * γ 1 0, γ 1 1 - k * γ 1 0], by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + γ 1 0 * hb'⟩
  have hbq : ((γ 0 1 : ℚ) + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) = l * b' := by exact_mod_cast hb'
  refine ⟨γ', ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [γ'] <;> push_cast <;> simp [ha, hd, hc]
  · apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [coe_toGQ _ (det_mj _ _ (by omega)), coe_toGQ _ (det_mj _ _ (by omega)), coe_ofSL, coe_ofSL]
    ext i i'
    fin_cases i <;> fin_cases i' <;> simp [Matrix.mul_apply, γ'] <;> push_cast <;> first | linear_combination | linear_combination hbq

theorem emod_toNat_lt (x : ℤ) {l : ℕ} (hl : 0 < l) : (x % (l : ℤ)).toNat < l := by
  have h1 := Int.emod_nonneg x (show (l : ℤ) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos x (show (0 : ℤ) < l by omega)
  omega

theorem emod_inv (b : ℤ) {l : ℕ} (hl : 0 < l) (a : ℕ) (ha : a < l) :
    ((((((b + a) % (l : ℤ)).toNat : ℕ) : ℤ) - b) % (l : ℤ)).toNat = a := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.sub_emod, Int.emod_emod, ← Int.sub_emod,
    add_sub_cancel_left, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem emod_inv' (b : ℤ) {l : ℕ} (hl : 0 < l) (a : ℕ) (ha : a < l) :
    ((b + ((((a : ℤ) - b) % (l : ℤ)).toNat : ℤ)) % (l : ℤ)).toNat = a := by
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.add_emod, Int.emod_emod, ← Int.add_emod,
    add_sub_cancel, Int.emod_eq_of_lt (by omega) (by omega)]
  simp

end GlobalTheory.HeckeUNormInv

open GlobalTheory.HeckeUNormInv in
theorem GlobalTheory.normInv_gamma1 : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ g : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g →
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) := by
  intro Ω _ _ ε X N l _ n hn g hg γ hγ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  rw [map_prod]
  have step : ∀ j : ℕ, X.sl (ofSL γ) (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) =
      X.sl (toGQ !![1, ((((γ 0 1 + j) % (l : ℤ)).toNat : ℕ) : ℤ); 0, (l : ℤ)]) g := by
    intro j
    obtain ⟨γ', hγ', heq⟩ := key N l n hn hl γ hγ j
    rw [← X.sl_mul, heq, X.sl_mul, hg γ' hγ']
  rw [Finset.prod_congr rfl (fun j _ => step j)]
  exact Finset.prod_nbij' (fun j => ((γ 0 1 + j) % (l : ℤ)).toNat) (fun k => (((k : ℤ) - γ 0 1) % (l : ℤ)).toNat)
    (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl)) (fun a _ => Finset.mem_range.2 (emod_toNat_lt _ hl))
    (fun a ha => emod_inv _ hl a (Finset.mem_range.1 ha)) (fun a ha => emod_inv' _ hl a (Finset.mem_range.1 ha))
    (fun _ _ => rfl)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormGamma1PrimePowInvariantStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeNorm_gamma1PrimePow_invariant : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ g : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g →
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) := by
  first | exact @GlobalTheory.normInv_gamma1 | exact GlobalTheory.normInv_gamma1 | (intros; apply GlobalTheory.normInv_gamma1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormPreservesDeltaPowerCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormPreservesDeltaPowerCondition
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.NormDelta

def conjM (γ : SL(2, ℤ)) (l : ℕ) (j k B : ℤ) (hB : (l : ℤ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) : SL(2, ℤ) :=
  ⟨!![γ 0 0 + j * γ 1 0, B; l * γ 1 0, γ 1 1 - k * γ 1 0], by
    have hd := γ.2
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 at hd
    linear_combination hd - γ 1 0 * hB⟩

private lemma toGQ_mul_ofSL_eq_ofSL_mul_toGQ (γ γ' : SL(2, ℤ)) (l : ℕ) (hl : 0 < l) (j k B : ℤ)
    (hB : (l : ℤ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0))
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 0 0 + j * γ 1 0, B; l * γ 1 0, γ 1 1 - k * γ 1 0]) :
    _root_.GlobalTheory.KZ.toGQ !![1, j; 0, (l : ℤ)] * _root_.GlobalTheory.KZ.ofSL γ =
      _root_.GlobalTheory.KZ.ofSL γ' * _root_.GlobalTheory.KZ.toGQ !![1, k; 0, (l : ℤ)] := by
  have hdet : ∀ m : ℤ, 0 < (!![1, m; 0, (l : ℤ)]).det := by
    intro m
    simp only [Matrix.det_fin_two_of, one_mul, mul_zero, sub_zero]
    exact_mod_cast hl
  unfold _root_.GlobalTheory.KZ.toGQ _root_.GlobalTheory.KZ.ofSL
  rw [dite_eq_left (hdet j), dite_eq_left (hdet k)]
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i i'
  have h00 := congrFun (congrFun hγ' 0) 0
  have h01 := congrFun (congrFun hγ' 0) 1
  have h10 := congrFun (congrFun hγ' 1) 0
  have h11 := congrFun (congrFun hγ' 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at h00 h01 h10 h11
  have hBq : ((l : ℚ) * B = γ 0 1 + j * γ 1 1 - k * (γ 0 0 + j * γ 1 0)) := by exact_mod_cast hB
  fin_cases i <;> fin_cases i' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.toGLPos,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, h00, h01, h10, h11] <;>
    first | ring1 | linear_combination -hBq

theorem _root_.GlobalTheory.NormDelta.norm_delta (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : _root_.GlobalTheory.KZ.Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ)
    (hn : 0 < n) (hlN : ¬ l ∣ N) (f : X.K) (hf : _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f)
    (hδ : ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (_root_.GlobalTheory.KZ.ofSL δ) f = g ^ (l ^ n)) :
    ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, _root_.GlobalTheory.Glue.Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧
        (∏ j ∈ Finset.range l, X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) *
          X.sl (_root_.GlobalTheory.KZ.ofSL δ) (∏ j ∈ Finset.range l, X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) = g ^ (l ^ n) := by
  intro δ hδN hδl
  obtain ⟨g, hg, hfg⟩ := hδ δ hδN hδl
  have hlp : l.Prime := Fact.out
  have hl0 : 0 < l := hlp.pos
  refine ⟨∏ j ∈ Finset.range l,
      X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g,
    _root_.GlobalTheory.normInv_gamma1 Ω ε X N l n hn g hg, ?_⟩
  rw [CongruenceSubgroup.Gamma1_mem] at hδN
  obtain ⟨-, -, hcN⟩ := hδN
  rw [CongruenceSubgroup.Gamma_mem] at hδl
  obtain ⟨ha', hb', hc', hd'⟩ := hδl
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at ha' hb' hc' hd'
  have hlpow : ∀ x : ℤ, ((x : ZMod (l ^ n)) = 0) → (l : ℤ) ∣ x := fun x hx =>
    (dvd_pow_self (l : ℤ) hn.ne').trans (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd x (l ^ n)).1 hx)
  obtain ⟨xa, hxa⟩ := hlpow (δ 0 0 + 1) (by push_cast; linear_combination -ha')
  obtain ⟨xd, hxd⟩ := hlpow (δ 1 1 + 1) (by push_cast; linear_combination -hd')
  obtain ⟨xb, hxb⟩ := hlpow (δ 0 1) (by linear_combination -hb')
  obtain ⟨xc, hxc⟩ := hlpow (δ 1 0) (by linear_combination -hc')
  have hcop : IsCoprime (N : ℤ) ((l : ℤ) ^ n) := by
    have := Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hlp).2 hlN).symm
    exact_mod_cast Nat.isCoprime_iff_coprime.2 this
  have hcM : ((δ 1 0 : ℤ) : ZMod (N * l ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    refine hcop.mul_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hcN) ?_
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 1 0) (l ^ n)).1 (by linear_combination -hc')
    exact_mod_cast this
  have hdetM : ((δ 0 0 : ℤ) : ZMod (N * l ^ n)) * (δ 1 1 : ℤ) = 1 := by
    have hdet := δ.2
    rw [Matrix.det_fin_two] at hdet
    have := congrArg (Int.cast : ℤ → ZMod (N * l ^ n)) hdet
    push_cast at this
    rw [hcM] at this
    simpa using this
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hB : (l : ℤ) * (xb + j * xd - j * xa - j * j * xc) =
      δ 0 1 + j * δ 1 1 - j * (δ 0 0 + j * δ 1 0) := by
    linear_combination -hxb - j * hxd + j * hxa + j * j * hxc
  have hη : _root_.GlobalTheory.NormDelta.conjM δ l j j _ hB * δ⁻¹ ∈ CongruenceSubgroup.Gamma1 (N * l ^ n) := by
    rw [CongruenceSubgroup.Gamma1_mem, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [_root_.GlobalTheory.NormDelta.conjM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_cons]
    push_cast
    rw [hcM]
    refine ⟨?_, ?_, ?_⟩ <;> first | ring1 | linear_combination hdetM
  have hsplit : _root_.GlobalTheory.KZ.ofSL (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB) =
      _root_.GlobalTheory.KZ.ofSL (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB * δ⁻¹) *
        _root_.GlobalTheory.KZ.ofSL δ := by
    rw [← map_mul, inv_mul_cancel_right]
  have hact : X.sl (_root_.GlobalTheory.KZ.ofSL δ)
      (X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) =
      X.sl (_root_.GlobalTheory.KZ.toGQ !![1, (j : ℤ); 0, (l : ℤ)])
        (X.sl (_root_.GlobalTheory.KZ.ofSL δ) f) := by
    rw [← _root_.GlobalTheory.KZ.Tower.sl_mul,
      toGQ_mul_ofSL_eq_ofSL_mul_toGQ δ (_root_.GlobalTheory.NormDelta.conjM δ l j j _ hB) l hl0 j j _ hB rfl,
      _root_.GlobalTheory.KZ.Tower.sl_mul, hsplit,
      _root_.GlobalTheory.KZ.Tower.sl_mul, hf _ hη]
  rw [hact, ← map_mul, hfg, map_pow]

end GlobalTheory.NormDelta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeNormPreservesDeltaPowerConditionStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeNorm_preserves_delta_powerCondition : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ¬ l ∣ N → ∀ f : X.K,
  Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f →
  (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ f * X.sl (ofSL δ) f = g ^ (l ^ n)) →
  (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧
        (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) *
          X.sl (ofSL δ) (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) = g ^ (l ^ n)) := by
  first | exact @GlobalTheory.NormDelta.norm_delta | exact GlobalTheory.NormDelta.norm_delta | (intros; apply GlobalTheory.NormDelta.norm_delta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowHeckeNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowHeckeNorm
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue GlobalTheory.ThAdd
open scoped MatrixGroups

namespace GlobalTheory.NormDl

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)

theorem eOm_mul_nat (x : ℚ) (k : ℕ) : eOm ε (x * k) = eOm ε x ^ k := by
  induction k with
  | zero => simp only [Nat.cast_zero, mul_zero, pow_zero]; exact eOm_zero ε
  | succ k ih => rw [Nat.cast_succ, mul_add, mul_one, eOm_add, ih, pow_succ]

theorem eOm_of_den {x : ℚ} (h : x.den = 1) : eOm ε x = 1 := by
  apply ε.injective
  rw [CyclotomicQExpansion.eOm_spec, map_one, ← Rat.coe_int_num_of_den_eq_one h]
  have := Complex.exp_int_mul_two_pi_mul_I x.num
  rw [← this]; congr 1; push_cast; ring

theorem eOm_mem (A : ValuationSubring Ω) (x : ℚ) : eOm ε x ∈ A := by
  have h : eOm ε x ^ x.den = 1 := by
    rw [← eOm_mul_nat, eOm_of_den]; rw [Rat.mul_den_eq_num]; simp
  rcases A.mem_or_inv_mem (eOm ε x) with hz | hz
  · exact hz
  · have h1 : eOm ε x * eOm ε x ^ (x.den - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel x.den_pos, h]
    rw [eq_inv_of_mul_eq_one_left h1, ← _root_.inv_pow]
    exact pow_mem hz _

theorem eOm_neg_mul (x : ℚ) : eOm ε (-x) * eOm ε x = 1 := by rw [← eOm_add, neg_add_cancel, eOm_zero]

theorem eOm_ne_zero (x : ℚ) : eOm ε x ≠ 0 := right_ne_zero_of_mul_eq_one (eOm_neg_mul ε x)

theorem eOm_inv_mem (A : ValuationSubring Ω) (x : ℚ) : (eOm ε x)⁻¹ ∈ A := by
  rw [← eq_inv_of_mul_eq_one_left (eOm_neg_mul ε x)]
  exact eOm_mem ε A _

def subHom (j : ℚ) (d : ℕ) [NeZero d] : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω where
  toFun := sub ε 1 j d
  map_one' := (sub_mul_and_one Ω ε 1 j d (one_div_pos.2 (Nat.cast_pos.2 (NeZero.pos d))) 1 1).2
  map_mul' x y := (sub_mul_and_one Ω ε 1 j d (one_div_pos.2 (Nat.cast_pos.2 (NeZero.pos d))) x y).1
  map_add' := Api.sub_map_add 1 j d
  map_zero' := by simpa using Api.sub_map_smul (ε := ε) 1 j d 0 0

theorem coeff_subHom (j : ℚ) (d : ℕ) [NeZero d] (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (subHom ε j d φ).coeff r = eOm ε (r * j) * φ.coeff (d * r) := by
  have h0 : (0 : ℚ) < d := Nat.cast_pos.2 (NeZero.pos d)
  have := Api.coeff_sub_upper (ε := ε) (a := 1) (d := d) (by positivity) j φ (d * r)
  rw [show (d : ℚ) * r * 1 / d = r by field_simp, show (d : ℚ) * r * j / d = r * j by field_simp] at this
  exact this

theorem coeff_tr (j : ℚ) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (subHom ε j 1 φ).coeff r = eOm ε (r * j) * φ.coeff r := by
  rw [coeff_subHom, Nat.cast_one, one_mul]

theorem tr_subHom (i j : ℚ) (d : ℕ) [NeZero d] (φ : HahnSeries ℚ Ω) :
    subHom ε j 1 (subHom ε i d φ) = subHom ε (i + j) d φ := by
  ext r
  rw [coeff_tr, coeff_subHom, coeff_subHom, mul_add, eOm_add]; ring

theorem subHom_period (i : ℚ) (d : ℕ) [NeZero d] {φ : HahnSeries ℚ Ω} (h : subHom ε 1 1 φ = φ) :
    subHom ε (i + d) d φ = subHom ε i d φ := by
  ext r
  conv_rhs => rw [← h]
  rw [coeff_subHom, coeff_subHom, coeff_tr, mul_add, eOm_add, mul_one, mul_comm r d]; ring

theorem theta_subHom (j : ℚ) (d : ℕ) [NeZero d] (φ : HahnSeries ℚ Ω) :
    theta 1 (subHom ε j d φ) = HahnSeries.C ((d : Ω)⁻¹) * subHom ε j d (theta 1 φ) := by
  haveI : CharZero Ω := ε.charZero
  have h0 : (d : Ω) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  ext r
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, coeff_subHom]
  show algebraMap ℚ Ω (1 * r) * (subHom ε j d φ).coeff r =
    (d : Ω)⁻¹ * (eOm ε (r * j) * (algebraMap ℚ Ω (1 * (d * r)) * φ.coeff (d * r)))
  rw [coeff_subHom, one_mul, one_mul, map_mul, map_natCast]
  field_simp

theorem ig_subHom {A : ValuationSubring Ω} (j : ℚ) (d : ℕ) [NeZero d] {φ : HahnSeries ℚ Ω} (h : Ig A φ) :
    Ig A (subHom ε j d φ) := fun r => by
  rw [coeff_subHom]; exact mul_mem (eOm_mem ε A _) (h _)

theorem dv_subHom {A : ValuationSubring Ω} {l n : ℕ} (j : ℚ) (d : ℕ) [NeZero d] {φ : HahnSeries ℚ Ω} (h : Dv A l n φ) :
    Dv A l n (subHom ε j d φ) := fun r => by
  obtain ⟨z, hz, e⟩ := h (d * r)
  exact ⟨eOm ε (r * j) * z, mul_mem (eOm_mem ε A _) hz, by rw [coeff_subHom, e]; ring⟩

theorem prim_subHom {A : ValuationSubring Ω} (j : ℚ) (d : ℕ) [NeZero d] {φ : HahnSeries ℚ Ω} (h : Prim A φ) :
    Prim A (subHom ε j d φ) := by
  have h0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  obtain ⟨h1, r, hr0, hr⟩ := h
  refine ⟨ig_subHom ε j d h1, r / d, ?_, ?_⟩
  · rw [coeff_subHom, mul_div_cancel₀ _ h0]; exact mul_ne_zero (eOm_ne_zero ε _) hr0
  · rw [coeff_subHom, mul_div_cancel₀ _ h0, mul_inv]; exact mul_mem (eOm_inv_mem ε A _) hr

omit [IsAlgClosed Ω] in
theorem prim_prod {A : ValuationSubring Ω} {ι : Type} (s : Finset ι) {U : ι → HahnSeries ℚ Ω} (h : ∀ i, Prim A (U i)) :
    Prim A (∏ i ∈ s, U i) :=
  Finset.prod_induction U (Prim A) (fun _ _ => prim_mul)
    ⟨fun r => by rw [HahnSeries.coeff_one]; split_ifs <;> simp, 0, by simp⟩ (fun i _ => h i)

omit [IsAlgClosed Ω] [Algebra ℚ Ω] in
theorem prim_ne_zero {A : ValuationSubring Ω} {φ : HahnSeries ℚ Ω} (h : Prim A φ) : φ ≠ 0 := by
  obtain ⟨-, r, hr, -⟩ := h
  rintro rfl; simp at hr

omit [IsAlgClosed Ω] in
theorem wron_prod (k : ℕ) {U V : ℕ → HahnSeries ℚ Ω} (hU : ∀ i, U i ≠ 0) (hV : ∀ i, V i ≠ 0) :
    theta 1 (∏ i ∈ Finset.range k, U i) * ∏ i ∈ Finset.range k, V i -
      (∏ i ∈ Finset.range k, U i) * theta 1 (∏ i ∈ Finset.range k, V i) =
    (∏ i ∈ Finset.range k, U i) * (∏ i ∈ Finset.range k, V i) *
      ∑ i ∈ Finset.range k, (theta 1 (U i) * V i - U i * theta 1 (V i)) / (U i * V i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Finset.prod_range_succ, Finset.sum_range_succ, theta_mul, mul_add]
    have h1 := hU k
    have h2 := hV k
    have e : (∏ i ∈ Finset.range k, U i) * U k * ((∏ i ∈ Finset.range k, V i) * V k) *
        ((theta 1 (U k) * V k - U k * theta 1 (V k)) / (U k * V k)) =
        (∏ i ∈ Finset.range k, U i) * (∏ i ∈ Finset.range k, V i) * (theta 1 (U k) * V k - U k * theta 1 (V k)) := by
      field_simp
    rw [e]
    linear_combination (U k * V k) * ih

theorem tr_norm (l : ℕ) [NeZero l] {c : HahnSeries ℚ Ω} (h0 : c ≠ 0) (h : subHom ε 1 1 c = c) (j : ℕ) :
    subHom ε j 1 (∏ i ∈ Finset.range l, subHom ε (i : ℕ) l c) = ∏ i ∈ Finset.range l, subHom ε (i : ℕ) l c := by
  rw [map_prod]
  simp only [tr_subHom]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    have h1 := Finset.prod_range_succ (fun i : ℕ => subHom ε ((i : ℚ) + j) l c) l
    rw [Finset.prod_range_succ'] at h1
    rw [add_comm (l : ℚ), subHom_period ε _ l h, Nat.cast_zero, zero_add] at h1
    rw [← mul_right_cancel₀ ((map_ne_zero _).2 h0) h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 2; push_cast; ring

theorem dv_mean {A : ValuationSubring Ω} {n : ℕ} (l : ℕ) [NeZero l] {w : HahnSeries ℚ Ω} (hw : Dv A l n w)
    (h : subHom ε l 1 w = w) :
    Dv A l n (HahnSeries.C ((l : Ω)⁻¹) * ∑ j ∈ Finset.range l, subHom ε (j : ℕ) 1 w) := by
  haveI : CharZero Ω := ε.charZero
  have h0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  intro r
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_sum]
  simp only [coeff_tr, eOm_mul_nat]
  rw [← Finset.sum_mul]
  by_cases h1 : eOm ε r = 1
  · obtain ⟨z, hz, e⟩ := hw r
    refine ⟨z, hz, ?_⟩
    rw [← e, h1]; simp [h0]
  · refine ⟨0, zero_mem A, ?_⟩
    by_cases h2 : w.coeff r = 0
    · simp [h2]
    have h3 : eOm ε r ^ l = 1 := by
      have := congrArg (fun x => x.coeff r) h
      simp only [coeff_tr, eOm_mul_nat] at this
      exact (mul_left_eq_self₀.1 this).resolve_right h2
    rw [geom_sum_eq h1, h3]; simp

theorem dv_norm {A : ValuationSubring Ω} {n : ℕ} (l : ℕ) [NeZero l] {φ a b : HahnSeries ℚ Ω}
    (ha : Prim A a) (hb : Prim A b) (tφ : subHom ε 1 1 φ = φ) (ta : subHom ε 1 1 a = a) (tb : subHom ε 1 1 b = b)
    (hE : Dv A l n (φ * a * b - (theta 1 a * b - a * theta 1 b))) :
    Dv A l n (hq ε l φ * (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l a) * (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l b) -
      (theta 1 (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l a) * (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l b) -
        (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l a) * theta 1 (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l b))) := by
  have a0 := prim_ne_zero ha
  have b0 := prim_ne_zero hb
  have tc : subHom ε 1 1 (a * b) = a * b := by rw [map_mul, ta, tb]
  have tθ : ∀ x : HahnSeries ℚ Ω, subHom ε 1 1 x = x → subHom ε 1 1 (theta 1 x) = theta 1 x := fun x hx => by
    have := theta_subHom ε 1 1 x
    rw [hx] at this
    simpa using this.symm
  set E := φ * a * b - (theta 1 a * b - a * theta 1 b) with hEdef
  have tE : subHom ε 1 1 E = E := by
    simp only [hEdef, map_sub, map_mul, tφ, ta, tb, tθ a ta, tθ b tb]
  obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne l)
  set R := ∏ i ∈ Finset.range m, subHom ε ((i + 1 : ℕ) : ℚ) l (a * b) with hR
  have hN : ∏ i ∈ Finset.range l, subHom ε (i : ℕ) l (a * b) = R * subHom ε 0 l (a * b) := by
    have : Finset.range l = Finset.range (m + 1) := by rw [hm]
    rw [this, Finset.prod_range_succ', Nat.cast_zero]
  have iR : Ig A R := (prim_prod _ fun i => prim_subHom ε _ l (prim_mul ha hb)).1
  have tR : subHom ε l 1 R = R := by
    rw [hR, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [tr_subHom, subHom_period ε _ l tc]
  have hw := dv_mean ε l ((dv_subHom ε 0 l hE).mul iR)
    (by rw [map_mul, tR, tr_subHom, subHom_period ε _ l tE])
  convert hw using 1
  rw [wron_prod l (U := fun j : ℕ => subHom ε (j : ℕ) l a) (V := fun j : ℕ => subHom ε (j : ℕ) l b)
    (fun i => (map_ne_zero _).2 a0) (fun i => (map_ne_zero _).2 b0), mul_assoc (hq ε l φ), ← Finset.prod_mul_distrib]
  simp only [← map_mul]
  have hhq : hq ε l φ = ∑ j ∈ Finset.range l, HahnSeries.C ((l : Ω)⁻¹) * subHom ε (j : ℕ) l φ := by
    rw [← Finset.mul_sum, HahnSeries.C_mul_eq_smul]; rfl
  rw [hhq, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← tr_norm ε l (mul_ne_zero a0 b0) tc j, hN, theta_subHom, theta_subHom]
  simp only [map_mul, tr_subHom, zero_add, hEdef, map_sub]
  have h1 : subHom ε (j : ℕ) l a ≠ 0 := (map_ne_zero _).2 a0
  have h2 : subHom ε (j : ℕ) l b ≠ 0 := (map_ne_zero _).2 b0
  field_simp

theorem modularTowerExp_slAction_T_pow (X : Tower Ω ε) (k : ℕ) (g : X.K) :
    X.exp (X.sl (ofSL (ModularGroup.T ^ k)) g) = subHom ε k 1 (X.exp g) := by
  have he : ∀ i j, ent (ofSL (ModularGroup.T ^ k)) i j = ((!![1, (k : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
    intro i j
    rw [← ModularGroup.coe_T_zpow, zpow_natCast]; rfl
  rw [Api.exp_sl_upper X _ (by rw [he]; simp), he, he, he]
  simp [subHom]

theorem exp_sl_m (X : Tower Ω ε) (j l : ℕ) [NeZero l] (g : X.K) :
    X.exp (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) = subHom ε j l (X.exp g) := by
  have hd : (0 : ℤ) < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two, NeZero.pos l]
  have he : ∀ a b, ent (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) a b =
      ((!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) a b : ℚ) := by
    intro a b
    unfold ent toGQ
    rw [dite_eq_left hd]; rfl
  rw [Api.exp_sl_upper X _ (by rw [he]; simp), he, he, he]
  simp [subHom]

theorem exists_inv_pres (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (f : X.K) (φ : HahnSeries ℚ Ω)
    (hf : X.sl (ofSL ModularGroup.T) f = f) (h : IsDl X A l n 1 f φ) :
    ∃ (a b : X.K) (κ : Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧
      X.sl (ofSL ModularGroup.T) a = a ∧ X.sl (ofSL ModularGroup.T) b = b ∧
      Dv A l n (φ * X.exp a * X.exp b - (theta 1 (X.exp a) * X.exp b - X.exp a * theta 1 (X.exp b))) := by
  obtain ⟨-, a, b, κ, hκ, e, pa, pb, c⟩ := h
  rw [dv_iff] at c
  obtain ⟨M, hM, hb⟩ := X.level b
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := Nat.exists_eq_succ_of_ne_zero hM.ne'
  have hT : X.sl (ofSL (ModularGroup.T ^ (m + 1))) b = b := by
    apply hb
    rw [CongruenceSubgroup.Gamma_mem]
    have := ModularGroup.coe_T_zpow ((m + 1 : ℕ) : ℤ)
    rw [zpow_natCast] at this
    have h' : ∀ i j, (ModularGroup.T ^ (m + 1)) i j =
      (!![1, ((m + 1 : ℕ) : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := fun i j => by rw [← this]
    simp only [h']
    simp [-Nat.cast_add, -Nat.cast_succ]
  set Q := ∏ k ∈ Finset.range m, X.sl (ofSL (ModularGroup.T ^ (k + 1))) b with hQ
  have pQ : Prim A (X.exp Q) := by
    rw [hQ, map_prod]
    exact prim_prod _ fun k => by rw [modularTowerExp_slAction_T_pow]; exact prim_subHom ε _ 1 pb
  have tb : X.sl (ofSL ModularGroup.T) (b * Q) = b * Q := by
    have h1 : b * Q = ∏ k ∈ Finset.range (m + 1), X.sl (ofSL (ModularGroup.T ^ k)) b := by
      rw [Finset.prod_range_succ', pow_zero, map_one, X.sl_one, mul_comm]
    conv_lhs => rw [h1, map_prod]
    simp only [← X.sl_mul, ← map_mul, ← pow_succ]
    rw [Finset.prod_range_succ, hT, mul_comm]
  have e' : f * (b * Q) = algebraMap Ω X.K κ * (a * Q) := by rw [← mul_assoc, e, mul_assoc]
  refine ⟨a * Q, b * Q, κ, hκ, e', by rw [map_mul]; exact prim_mul pa pQ, by rw [map_mul]; exact prim_mul pb pQ,
    ?_, tb, ?_⟩
  · have := congrArg (X.sl (ofSL ModularGroup.T)) e'
    rw [map_mul, hf, tb, e', map_mul (X.sl _) (algebraMap Ω X.K κ), AlgEquiv.commutes] at this
    exact (mul_left_cancel₀ ((map_ne_zero _).2 hκ) this).symm
  · convert c.mul (Ig.mul pQ.1 pQ.1) using 1
    simp only [map_mul, theta_mul]; ring

theorem isDl_norm : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.K) (φ : HahnSeries ℚ Ω),
  X.sl (ofSL ModularGroup.T) f = f → (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → IsDl X A l n 1 f φ →
  IsDl X A l n 1 (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) (hq ε l φ) := by
  intro Ω _ _ _ ε X A l hl n f φ hf hφ h
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨a, b, κ, hκ, e, pa, pb, ta, tb, c⟩ := exists_inv_pres ε X A l n f φ hf h
  have tx : ∀ x : X.K, X.sl (ofSL ModularGroup.T) x = x → subHom ε 1 1 (X.exp x) = X.exp x := fun x hx => by
    have := modularTowerExp_slAction_T_pow ε X 1 x
    rw [pow_one, hx, Nat.cast_one] at this
    exact this.symm
  have tφ : subHom ε 1 1 φ = φ := by
    ext r
    rw [coeff_tr, mul_one]
    by_cases h0 : φ.coeff r = 0
    · simp [h0]
    · rw [eOm_of_den ε (hφ r h0), one_mul]
  have hx : ∀ x : X.K, X.exp (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) x) =
      ∏ j ∈ Finset.range l, subHom ε (j : ℕ) l (X.exp x) := fun x => by
    rw [map_prod]; exact Finset.prod_congr rfl fun j _ => exp_sl_m ε X j l x
  refine ⟨fun r => ?_, ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) a,
    ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) b, κ ^ l, pow_ne_zero _ hκ, ?_, ?_, ?_, ?_⟩
  · rw [Api.hq_eq_uq_of_isAlgClosed (NeZero.pos l) (fun r hr => by simpa using hφ r hr), Api.coeff_uq (NeZero.pos l)]
    split_ifs
    · exact h.1 _
    · exact zero_mem A
  · rw [← Finset.prod_mul_distrib]
    simp only [← map_mul, e]
    simp only [map_mul, AlgEquiv.commutes]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, map_pow]
  · rw [hx]; exact prim_prod _ fun j => prim_subHom ε _ l pa
  · rw [hx]; exact prim_prod _ fun j => prim_subHom ε _ l pb
  · rw [dv_iff, hx, hx]
    exact dv_norm ε l pa pb tφ (tx a ta) (tx b tb) c

end GlobalTheory.NormDl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowHeckeNormStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_heckeNorm : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.K) (φ : HahnSeries ℚ Ω),
  X.sl (ofSL ModularGroup.T) f = f → (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → IsDl X A l n 1 f φ →
  IsDl X A l n 1 (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) (hq ε l φ) := by
  first | exact @GlobalTheory.NormDl.isDl_norm | exact GlobalTheory.NormDl.isDl_norm | (intros; apply GlobalTheory.NormDl.isDl_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponents
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponents
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion

namespace GlobalTheory.HeckeInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_pre_exp [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ∃ ω : Ω, ε ω = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hn : x.den ≠ 0 := x.den_nz
  haveI : NeZero ((x.den : ℕ) : Ω) := ⟨by exact_mod_cast hn⟩
  haveI : NeZero x.den := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω x.den
  have hζ' := hζ.map_of_injective ε.injective
  have hz : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hx : (x : ℂ) * (x.den : ℂ) = (x.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = (x.num : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * hx
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hz
  exact ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

theorem eps_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) :=
  Function.invFun_eq (exists_pre_exp ε x)

theorem sub_coeff (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (j : ℚ) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε 1 j (q : ℚ) φ).coeff s = eOm ε (s * j) * φ.coeff ((q : ℚ) * s) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have h : (0 : ℚ) < 1 / (q : ℚ) := by positivity
  unfold sub scale
  rw [dite_eq_left h]
  have e : (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding ((q : ℚ) * s) = s := by
    simp only [RelIso.coe_toRelEmbedding, OrderIso.coe_toOrderEmbedding, OrderIso.mulLeft₀_apply]
    field_simp
  have key := HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ (1 / (q : ℚ)) h).toOrderEmbedding)
    (x := cm (fun r => eOm ε (r * j / (q : ℚ))) φ) (a := (q : ℚ) * s)
  rw [e] at key
  rw [key]
  simp only [cm]
  congr 2
  field_simp

theorem sum_eOm [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ) (hq : 0 < q) (s : ℚ) (hs : ((q : ℚ) * s).den = 1) :
    ∑ j ∈ Finset.range q, eOm ε (s * (j : ℚ)) = if s.den = 1 then (q : Ω) else 0 := by
  apply ε.injective
  have hz : ∀ j : ℕ, ε (eOm ε (s * (j : ℚ))) = (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ j := by
    intro j
    rw [eps_eOm, ← Complex.exp_nat_mul]
    congr 1
    push_cast; ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [hz]
  split_ifs with hd
  · have h1 : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) = 1 := by
      have : (s : ℂ) = ((s.num : ℤ) : ℂ) := by
        have := Rat.coe_int_num_of_den_eq_one hd
        rw [← this]; push_cast; rfl
      rw [this, show 2 * (Real.pi : ℂ) * Complex.I * ((s.num : ℤ) : ℂ) = (s.num : ℂ) * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp [h1]
  · have hne : Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hsn : (s : ℂ) = (n : ℂ) := by
        have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        apply mul_left_cancel₀ h2
        linear_combination hn
      have : s = (n : ℚ) := by exact_mod_cast hsn
      exact hd (by rw [this]; rfl)
    have hpow : (Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) ^ q = 1 := by
      rw [← Complex.exp_nat_mul]
      have hx : ((q : ℚ) * s : ℚ) = ((((q : ℚ) * s).num : ℤ) : ℚ) := (Rat.coe_int_num_of_den_eq_one hs).symm
      have hx' : (q : ℂ) * (s : ℂ) = ((((q : ℚ) * s).num : ℤ) : ℂ) := by exact_mod_cast hx
      rw [show (q : ℂ) * (2 * Real.pi * Complex.I * (s : ℂ)) = ((((q : ℚ) * s).num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        rw [← hx']; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, map_zero]

theorem hq_coeff_of_int : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
    (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ,
      (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  intro Ω _ _ _ ε q hq0 φ hφ s
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  unfold hq
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_sum, smul_eq_mul]
  simp only [GlobalTheory.HeckeInt.sub_coeff ε q hq0]
  rw [← Finset.sum_mul]
  by_cases hc : φ.coeff ((q : ℚ) * s) = 0
  · simp [hc]
  · rw [GlobalTheory.HeckeInt.sum_eOm ε q hq0 s (hφ _ hc)]
    have hqne : (q : Ω) ≠ 0 := by exact_mod_cast hq0.ne'
    split_ifs
    · field_simp
    · simp

end GlobalTheory.HeckeInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumAtCuspHahnCoeffOfIntegralExponentsStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSumAtCuspHahn_coeff_of_integral_exponents : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (q : ℕ), 0 < q → ∀ φ : HahnSeries ℚ Ω,
  (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → ∀ s : ℚ, (hq ε q φ).coeff s = if s.den = 1 then φ.coeff ((q : ℚ) * s) else 0 := by
  first | exact @GlobalTheory.HeckeInt.hq_coeff_of_int | exact GlobalTheory.HeckeInt.hq_coeff_of_int | (intros; apply GlobalTheory.HeckeInt.hq_coeff_of_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOne
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThHeckeU

theorem eval_kmap {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (σ : X.K ≃+* X.K) (x : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l σ x) = X.cls l n (Units.map σ.toMonoidHom f) := by
  rw [AdicCompletion.eval_apply]
  change (AdicCompletion.map _ _ x).val n = _
  rw [AdicCompletion.map_val_apply, ← AdicCompletion.eval_apply, h]
  rw [Tower.cls, Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
  rfl

theorem cls_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (f g : X.Kˣ) : X.cls l n (f * g) = X.cls l n f + X.cls l n g := by
  simp only [Tower.cls, ← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add]
  rfl

theorem eval_sum_kmap {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (s : Finset ℕ) (σ : ℕ → (X.K ≃+* X.K)) (x : X.Khat l) (f : X.Kˣ)
    (h : AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f) :
    AdicCompletion.eval (idl l) (X.Kl l) n (∑ j ∈ s, X.kmap l (σ j) x) =
      X.cls l n (∏ j ∈ s, Units.map (σ j).toMonoidHom f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, map_zero, Finset.prod_empty]
    simp [Tower.cls]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, map_add (f := _), ih, cls_mul, eval_kmap X l n _ x f h]

theorem isThB_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω)
    (N l : ℕ) [Fact l.Prime] (b : X.Fn l) (ψ : HahnSeries ℚ Ω) (hψ : ∀ r, ψ.coeff r ∈ A) : IsThB X A N l 0 b ψ := by
  have hprim : Prim A (X.exp 1) := by
    rw [map_one]
    refine ⟨fun r => ?_, 0, by simp, by simp⟩
    by_cases h : r = 0
    · subst h; simp
    · simp [HahnSeries.coeff_one, h]
  refine ⟨1, fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩, hψ, 1, 1, 1, one_ne_zero, by simp,
    hprim, hprim, fun r => ⟨(ψ * X.exp 1 * X.exp 1).coeff r -
      (theta 1 (X.exp 1) * X.exp 1 - X.exp 1 * theta 1 (X.exp 1)).coeff r, ?_, by simp⟩⟩
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) 0 (b ![1, 0]))
    rw [← hy, Tower.cls, Submodule.Quotient.eq]
    simp
  · simp only [map_one, mul_one, one_mul, sub_self, HahnSeries.coeff_zero, sub_zero]
    exact hψ r

theorem isThB_act_heckeU_same : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l,
    b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) →
  IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (hq ε l φ) := by
  intro Ω _ _ _ ε X A N l _ n w d hd hl b hb φ hφ h
  rw [GlobalTheory.T.diamond_commutes_hecke_U Ω ε X N l w d hd hl b hb]
  obtain ⟨f, hinv, hcls, hδ, hdl⟩ := h
  have hint : ∀ r, (hq ε l φ).coeff r ∈ A := by
    intro r
    rw [GlobalTheory.T.heckeSumAtCuspHahn_coeff_of_integral_exponents Ω ε l (Nat.Prime.pos Fact.out) φ hφ r]
    split_ifs
    · exact hdl.1 _
    · exact A.zero_mem
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact isThB_zero X A N l _ _ hint
  set b' := X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b
  have hT : X.sl (ofSL ModularGroup.T) (f : X.K) = f := hinv _ (by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  have hcoe : ((∏ j ∈ Finset.range l,
      Units.map (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv.toMonoidHom f : X.Kˣ) : X.K)
      = ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) (f : X.K) := by
    rw [Units.coe_prod]; rfl
  refine ⟨∏ j ∈ Finset.range l, Units.map (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv.toMonoidHom f,
    ?_, ?_, ?_, ?_⟩
  · rw [hcoe]; exact GlobalTheory.T.heckeNorm_gamma1PrimePow_invariant Ω ε X N l n hn _ hinv
  · have hv : X.heckeU l b' ![1, 0] = ∑ j ∈ Finset.range l,
        X.kmap l (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv (b' ![1, 0]) := by
      simp only [Tower.heckeU]
      rw [LinearMap.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      show X.kmap l _ (b' _) = _
      congr 2
      ext i; fin_cases i <;> simp [mZl]
    rw [hv]
    exact eval_sum_kmap X l n (Finset.range l)
      (fun j => (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)])).toRingEquiv) _ f hcls
  · rw [hcoe]; exact GlobalTheory.T.heckeNorm_preserves_delta_powerCondition Ω ε X N l n hn hl _ hinv hδ
  · rw [hcoe]; exact GlobalTheory.T.isLogDerivQExpansionModPrimePow_heckeNorm Ω ε X A l n _ φ hT hφ hdl

theorem isThB_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ)
    (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (hlA : (l : Ω) ∈ A.nonunits)
    (x : X.Fn l) (ψ ψ₂ : HahnSeries ℚ Ω) (h : IsThB X A N l n x ψ) (hint : ∀ r, ψ₂.coeff r ∈ A)
    (hc : ∀ r, CgA A l n (ψ.coeff r) (ψ₂.coeff r)) : IsThB X A N l n x ψ₂ := by
  obtain ⟨f, h1, h2, h3, h4⟩ := h
  obtain ⟨φ₀, han, hdiff⟩ := hj
  exact ⟨f, h1, h2, h3, (GlobalTheory.T.isLogDerivQExpansionModPrimePow_calculus ε X ⟨φ₀, hdiff, han⟩ l A hlA n 1 (f : X.K) (f : X.K) ψ ψ₂).2.2.1 h4 hint hc⟩

theorem isThB_act_heckeU : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), Algebra.IsAlgebraic ℚ Ω →
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → 1 ≤ N → Odd w →
    (l : Ω) ∈ A.nonunits → d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsLat 1 φ →
  IsThB X A N l (n + 1) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (uq l φ) := by
  intro Ω _ _ _ ε X A N l _ n w d hAlg hj hl2 hN1 hw hlA hd hl b hb φ _ h
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, hAlg⟩
  have hl0 : 0 < l := Nat.Prime.pos Fact.out
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hl).symm
  obtain ⟨φ', h', hlat'⟩ := GlobalTheory.ThEx.of_lift GlobalTheory.ThLift.exists_invariant_lift Ω ε X A N l hAlg hj hl2 hl hN1 hlA n w hw _
    (GlobalTheory.CyclotomicQExpansion.ThnEx.diam_B X N l w d hN1 hNl hd b hb)
  have hU := isThB_act_heckeU_same Ω ε X A N l n w d hd hl b hb _
    (fun r hr => by simpa using hlat' r hr) h'
  rw [Api.hq_eq_uq_of_isAlgClosed hl0 hlat'] at hU
  have hc := GlobalTheory.ThBCompat.isThB_succ_coeff_cong Ω ε X A N l hl2 hl hN1 hlA n _ φ _ h h'
  have hφA : ∀ r, φ.coeff r ∈ A := by
    obtain ⟨f, -, -, -, hdl⟩ := h
    exact hdl.1
  refine isThB_congr X A N l n hj hlA _ _ _ hU ?_ ?_
  · intro r
    rw [Api.coeff_uq hl0]
    split_ifs
    · exact hφA _
    · exact A.zero_mem
  · intro r
    rw [Api.coeff_uq hl0, Api.coeff_uq hl0]
    split_ifs
    · obtain ⟨z, hz, e⟩ := hc ((l : ℚ) * r)
      exact ⟨-z, A.neg_mem _ hz, by linear_combination -e⟩
    · exact ⟨0, A.zero_mem, by simp⟩

end GlobalTheory.ThHeckeU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOneStatement
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOperator_upperU_l_commute_scale_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ), Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → 1 ≤ N → Odd w → (l : Ω) ∈ A.nonunits → d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsLat 1 φ →
  IsThB X A N l (n + 1) (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b)) (uq l φ) := by
  first | exact @GlobalTheory.ThHeckeU.isThB_act_heckeU | exact GlobalTheory.ThHeckeU.isThB_act_heckeU | (intros; apply GlobalTheory.ThHeckeU.isThB_act_heckeU <;> assumption)
end
