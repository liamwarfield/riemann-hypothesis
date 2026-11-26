module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypothesesOfGlobalRowsAndNodes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelPrimesSizeBoundsColumnDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CriticalLevelLePowAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstVandermondeNodeLargeOfSmallThreshold
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.RowVand

open Formalism.FourierDecayAlt Finset

lemma prod_le_pow_of_le {s : Finset ℕ} {f : ℕ → ℝ} {B : ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h : ∀ i ∈ s, f i ≤ B) : ∏ i ∈ s, f i ≤ B ^ s.card := by
  calc ∏ i ∈ s, f i ≤ ∏ _i ∈ s, B := Finset.prod_le_prod₀ h0 h
    _ = B ^ s.card := Finset.prod_const B

lemma one_le_prod_of_le {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := (Finset.prod_const_one).symm
    _ ≤ ∏ i ∈ s, f i := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h

lemma b_le (c : Sz.Cfg) (hc : c.Ok) : ∀ i j, 1 ≤ i → i ≤ j → j ≤ c.m → c.b i ≤ c.b j := by
  intro i j hi hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have := hc.hgap j (by omega) (by omega)
    linarith [ih (by omega)]

lemma one_le_b (c : Sz.Cfg) (hc : c.Ok) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ c.m) : 1 ≤ c.b j :=
  le_trans hc.hb1 (b_le c hc 1 j le_rfl h1 h2)

lemma v_bounds (c : Sz.Cfg) (hc : c.Ok) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ c.k) :
    0 ≤ c.v i ∧ c.v i ≤ c.v 1 := by
  have hi : (i : ℝ) + 1 ≤ c.k := by exact_mod_cast h2
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
  have hD := hc.hDel
  have hv := hc.hv0
  unfold Sz.Cfg.v
  constructor
  · nlinarith
  · push_cast; nlinarith

lemma vlast_le (c : Sz.Cfg) (hc : c.Ok) : c.vlast ≤ c.v 1 := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast hc.hk
  have hD := hc.hDel
  unfold Sz.Cfg.v
  push_cast
  nlinarith

lemma firstVandermondeNode_large_of_small_threshold (c : Sz.Cfg) (hc : c.Ok) (hs : c.vth ≤ 1 / 10) : 40 * c.m * c.k * c.Del ≤ c.b 1 := by
  have hb : 0 < c.b 1 := lt_of_lt_of_le one_pos hc.hb1
  unfold Sz.Cfg.vth at hs
  rw [div_le_iff₀ hb] at hs
  linarith

lemma vand_inner_le (c : Sz.Cfg) (hc : c.Ok) (hs : c.vth ≤ 1 / 10) (de : ℕ → ℝ) (hw : Sz.IsWord c.k de)
    (hpos : 0 ≤ Sz.Vand (c.k - 2) (fun i => c.u de (i + 1))) :
    Sz.Vand (c.k - 2) (fun i => c.u de (i + 1)) ≤ Sz.Vand c.k (c.u de) := by
  have hk := hc.hk
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk
  have hmR : (2 : ℝ) ≤ c.m := by exact_mod_cast hc.hm
  have hD := hc.hDel
  have hb1 := firstVandermondeNode_large_of_small_threshold c hc hs
  have hvl := vlast_le c hc
  have hv0 := hc.hv0
  have ha := hc.ha
  have hde : ∀ i, 0 ≤ de i ∧ de i ≤ 1 := fun i => by rcases hw.1 i with h | h <;> rw [h] <;> norm_num
  have e1 : Sz.Vand c.k (c.u de) =
      (∏ j ∈ Icc 2 c.k, (c.u de 1 - c.u de j)) * Sz.Vand (c.k - 1) (fun i => c.u de (i + 1)) := by
    have := Formalism.FourierDecayAlt.P.Sz4.vand_succ_bot (c.k - 1) (c.u de)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have e2 : Sz.Vand (c.k - 1) (fun i => c.u de (i + 1)) =
      Sz.Vand (c.k - 2) (fun i => c.u de (i + 1)) * ∏ i ∈ Icc 1 (c.k - 2), (c.u de (i + 1) - c.u de c.k) := by
    have := Formalism.FourierDecayAlt.P.Sz4.vand_succ_top (c.k - 2) (fun i => c.u de (i + 1))
    rw [show c.k - 2 + 1 = c.k - 1 by omega] at this
    rw [this]
    congr 2
    ext i
    congr 2
    omega

  have hu1 : c.u de 1 = c.a := by unfold Sz.Cfg.u; simp
  have huk : c.u de c.k = c.ulast := by
    unfold Sz.Cfg.u; rw [if_neg (by omega), if_pos rfl]
  have F1 : ∀ j ∈ Icc 2 c.k, 1 ≤ c.u de 1 - c.u de j := by
    intro j hj
    rw [mem_Icc] at hj
    rw [hu1]
    by_cases hjk : j = c.k
    · rw [hjk, huk]
      unfold Sz.Cfg.ulast
      split_ifs with ht
      · have := (hc.htop ht).1
        have hb0 := hc.hb1
        nlinarith
      · nlinarith
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [Formalism.FourierDecayAlt.P.Sz4.u_succ c de hw i (by omega) (by omega) (Or.inl (by omega))]
      have := (v_bounds c hc i (by omega) (by omega)).2
      have := hde i
      nlinarith

  have F2 : ∀ i ∈ Icc 1 (c.k - 2), 1 ≤ c.u de (i + 1) - c.u de c.k := by
    intro i hi
    rw [mem_Icc] at hi
    rw [Formalism.FourierDecayAlt.P.Sz4.u_succ c de hw i (by omega) (by omega) (Or.inl (by omega)), huk]
    have hvi := v_bounds c hc i (by omega) (by omega)
    have hdi := hde i
    unfold Sz.Cfg.ulast
    split_ifs with ht
    · have := (hc.htop ht).1
      have h8 : (8 : ℝ) ≤ c.m * c.k := by nlinarith
      have h9 : 8 * c.Del ≤ c.m * c.k * c.Del := mul_le_mul_of_nonneg_right h8 (by linarith)
      have h10 : de i * c.Del ≤ 1 * c.Del := mul_le_mul_of_nonneg_right hdi.2 (by linarith)
      linarith [hvi.1]
    · have hsub := Formalism.FourierDecayAlt.P.Sz4.v_sub c i (c.k - 1)
      have hvk : c.v (c.k - 1) = c.vlast := by
        unfold Sz.Cfg.v
        rw [Nat.cast_sub (by omega)]
        push_cast; ring
      have hik : (i : ℝ) + 2 ≤ ((c.k - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (by omega)]
        have : ((i + 2 : ℕ) : ℝ) ≤ c.k := by exact_mod_cast (by omega : i + 2 ≤ c.k)
        push_cast at this ⊢
        linarith
      rw [hvk] at hsub
      have h10 : de i * c.Del ≤ 1 * c.Del := mul_le_mul_of_nonneg_right hdi.2 (by linarith)
      have h11 : 4 * c.Del * 1 ≤ 4 * c.Del * (((c.k - 1 : ℕ) : ℝ) - i) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
  rw [e1, e2]
  have P1 := one_le_prod_of_le F1
  have P2 := one_le_prod_of_le F2
  calc Sz.Vand (c.k - 2) (fun i => c.u de (i + 1))
      = 1 * (Sz.Vand (c.k - 2) (fun i => c.u de (i + 1)) * 1) := by ring
    _ ≤ _ := by
      apply mul_le_mul P1 _ (by positivity) (by linarith)
      exact mul_le_mul le_rfl P2 zero_le_one hpos

lemma vand_lam_le_cfg (c : Sz.Cfg) (hc : c.Ok) (hs : c.vth ≤ 1 / 10) (hmk : c.m ≤ c.k) (L : ℝ) (hL : 1 ≤ L)
    (hbj : ∀ j, 1 ≤ j → j ≤ c.m → c.b j ≤ Real.exp (2 * L)) (de : ℕ → ℝ) (hw : Sz.IsWord c.k de) :
    Sz.Vand (c.k + c.m - 1) c.lam ≤ Real.exp (10 * c.k * c.m * L) * Sz.Vand c.k (c.u de) := by
  have hk := hc.hk
  have hm := hc.hm
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk
  have hmR : (2 : ℝ) ≤ c.m := by exact_mod_cast hm
  have hmkR : (c.m : ℝ) ≤ c.k := by exact_mod_cast hmk
  have hD := hc.hDel
  have hkD : 0 ≤ (c.k : ℝ) * c.Del := mul_nonneg (by linarith) (by linarith)
  have h4 : 4 * c.k * c.Del ≤ Real.exp (2 * L) := by
    have h1 := firstVandermondeNode_large_of_small_threshold c hc hs
    have h2 := hbj 1 le_rfl (by omega)
    have h3 : 2 * ((c.k : ℝ) * c.Del) ≤ c.m * (c.k * c.Del) := mul_le_mul_of_nonneg_right hmR hkD
    linarith
  obtain ⟨hV, hRel, hRlo, -, hVk⟩ := Formalism.FourierDecayAlt.P.vandermondeTop c de hc hw
  obtain ⟨hLam, -⟩ := Formalism.FourierDecayAlt.P.vandermonde_lambda_lower_bound c hc
  have hR : 0 < Sz.Rde (c.k - 2) de := lt_of_lt_of_le (Real.exp_pos _) hRlo
  have hU0 : 0 ≤ Sz.Vand (c.k - 2) (fun i => c.u de (i + 1)) := by
    rw [hRel]; exact (mul_pos hR hV).le
  have hU := vand_inner_le c hc hs de hw hU0
  have hU1 : 0 ≤ Sz.Vand c.k (c.u de) := le_trans hU0 hU

  have A1 : Sz.Vand (c.k - 2) c.v ≤ Real.exp (((c.k : ℝ) - 1) / 4) * Sz.Vand c.k (c.u de) := by
    have e : Real.exp (((c.k : ℝ) - 1) / 4) * Real.exp (-(((c.k : ℝ) - 1) / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    calc Sz.Vand (c.k - 2) c.v
        = Real.exp (((c.k : ℝ) - 1) / 4) * (Real.exp (-(((c.k : ℝ) - 1) / 4)) * Sz.Vand (c.k - 2) c.v) := by
          rw [← mul_assoc, e, one_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (le_trans ?_ hU) (Real.exp_pos _).le
          rw [hRel]
          exact mul_le_mul_of_nonneg_right hRlo hV.le

  have hE : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have A2 : (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ) ≤ Real.exp (2 * L) ^ c.k := by
    have f1 : ((c.k - 2).factorial : ℝ) ≤ (c.k : ℝ) ^ (c.k - 2) := by
      have := le_trans (Nat.factorial_le_pow (c.k - 2)) (Nat.pow_le_pow_left (Nat.sub_le c.k 2) (c.k - 2))
      exact_mod_cast this
    calc (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ)
        ≤ (4 * c.Del) ^ (c.k - 2) * (c.k : ℝ) ^ (c.k - 2) :=
          mul_le_mul_of_nonneg_left f1 (pow_nonneg (by linarith) _)
      _ = (4 * c.k * c.Del) ^ (c.k - 2) := by rw [← mul_pow]; congr 1; ring
      _ ≤ Real.exp (2 * L) ^ (c.k - 2) := pow_le_pow_left₀ (by linarith) h4 _
      _ ≤ Real.exp (2 * L) ^ c.k := pow_le_pow_right₀ hE (Nat.sub_le _ _)
  have A20 : 0 ≤ (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ) :=
    mul_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _)

  have h23 : 2 * Real.exp (2 * L) ≤ Real.exp (3 * L) := by
    have h1 : 2 ≤ Real.exp L := le_trans (by linarith) (Real.add_one_le_exp L)
    rw [show 3 * L = L + 2 * L by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hf : ∀ i ∈ Icc 1 (c.k - 1), ∀ j ∈ Icc 1 c.m, 0 ≤ c.v i + c.b j ∧ c.v i + c.b j ≤ Real.exp (3 * L) := by
    intro i hi j hj
    rw [mem_Icc] at hi hj
    have h1 := v_bounds c hc i hi.1 (by omega)
    have h2 := one_le_b c hc j hj.1 hj.2
    have h3 := hbj j hj.1 hj.2
    have h5 := hc.hv1
    constructor <;> linarith [h1.1, h1.2]
  have A30 : ∀ i ∈ Icc 1 (c.k - 1), 0 ≤ ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) :=
    fun i hi => Finset.prod_nonneg fun j hj => (hf i hi j hj).1
  have A3 : ∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j) ≤ (Real.exp (3 * L) ^ c.m) ^ c.k := by
    refine le_trans (prod_le_pow_of_le (B := Real.exp (3 * L) ^ c.m) A30 fun i hi => ?_) ?_
    · have := prod_le_pow_of_le (fun j hj => (hf i hi j hj).1) (fun j hj => (hf i hi j hj).2)
      simpa using this
    · exact pow_le_pow_right₀ (one_le_pow₀ (by linarith)) (by simp)

  have hg : ∀ i ∈ Icc 1 c.m, ∀ j ∈ Ioc i c.m, 0 ≤ -c.b i - -c.b j ∧ -c.b i - -c.b j ≤ Real.exp (2 * L) := by
    intro i hi j hj
    rw [mem_Icc] at hi
    rw [mem_Ioc] at hj
    have h1 := b_le c hc i j hi.1 hj.1.le hj.2
    have h2 := one_le_b c hc i hi.1 hi.2
    have h3 := hbj j (by omega) hj.2
    constructor <;> linarith
  have A40 : ∀ i ∈ Icc 1 c.m, 0 ≤ ∏ j ∈ Ioc i c.m, (-c.b i - -c.b j) :=
    fun i hi => Finset.prod_nonneg fun j hj => (hg i hi j hj).1
  have A4 : Sz.Vand c.m (fun j => -c.b j) ≤ (Real.exp (2 * L) ^ c.m) ^ c.k := by
    unfold Sz.Vand
    refine le_trans (prod_le_pow_of_le (B := Real.exp (2 * L) ^ c.m) A40 fun i hi => ?_) ?_
    · exact le_trans (prod_le_pow_of_le (fun j hj => (hg i hi j hj).1) (fun j hj => (hg i hi j hj).2))
        (pow_le_pow_right₀ hE (by simp))
    · exact pow_le_pow_right₀ (one_le_pow₀ hE) (by simpa using hmk)
  have A41 : 0 ≤ Sz.Vand c.m (fun j => -c.b j) := Finset.prod_nonneg A40

  have hexp : Real.exp (((c.k : ℝ) - 1) / 4) * Real.exp (2 * L) ^ c.k * (Real.exp (3 * L) ^ c.m) ^ c.k *
      (Real.exp (2 * L) ^ c.m) ^ c.k ≤ Real.exp (10 * c.k * c.m * L) := by
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : (c.k : ℝ) * 1 ≤ c.k * L := mul_le_mul_of_nonneg_left hL (by linarith)
    have h2 : (c.k : ℝ) * L * 2 ≤ c.k * L * c.m := mul_le_mul_of_nonneg_left hmR (by linarith)
    nlinarith
  rw [hLam, hVk]
  calc Sz.Vand (c.k - 2) c.v * (4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ) *
        (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) * Sz.Vand c.m (fun j => -c.b j)
      = Sz.Vand (c.k - 2) c.v * ((4 * c.Del) ^ (c.k - 2) * ((c.k - 2).factorial : ℝ)) *
        (∏ i ∈ Icc 1 (c.k - 1), ∏ j ∈ Icc 1 c.m, (c.v i + c.b j)) * Sz.Vand c.m (fun j => -c.b j) := by ring
    _ ≤ (Real.exp (((c.k : ℝ) - 1) / 4) * Sz.Vand c.k (c.u de)) * Real.exp (2 * L) ^ c.k *
        (Real.exp (3 * L) ^ c.m) ^ c.k * (Real.exp (2 * L) ^ c.m) ^ c.k :=
      mul_le_mul (mul_le_mul (mul_le_mul A1 A2 A20 (by positivity)) A3 (Finset.prod_nonneg A30)
        (by positivity)) A4 A41 (by positivity)
    _ = (Real.exp (((c.k : ℝ) - 1) / 4) * Real.exp (2 * L) ^ c.k * (Real.exp (3 * L) ^ c.m) ^ c.k *
        (Real.exp (2 * L) ^ c.m) ^ c.k) * Sz.Vand c.k (c.u de) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp hU1

theorem vand_lamSH_le : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ),
    Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ,
      vand (lamSH D.R (D.hc τ)) ≤ Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) * vand (uS D u τ) := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 hH h40 u τ
  obtain ⟨hS, hD, -⟩ := hH
  have hok := BridgeLemma.cfg_ok hD hS τ
  have hsm := BridgeLemma.cfg_small hS h40 τ
  unfold StandingNumericalData at hD
  obtain ⟨-, -, -, -, d5, -⟩ := hD
  rw [← BridgeLemma.Vand_lam D τ, ← BridgeLemma.Vand_u D u τ (d5 u τ)]
  have hb : large₂.sc.b ^ 2 = Real.exp (2 * large₂.sc.L) := by
    rw [← BridgeLemma.log_b large₂, two_mul, Real.exp_add, Real.exp_log (by linarith [BridgeLemma.one_lt_b large₂]), sq]
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact vand_lam_le_cfg (BridgeLemma.cfgOf D τ) hok hsm.hvth hmk large₂.sc.L (BridgeLemma.one_le_L large₂)
    (fun j h1 h2 => hb ▸ hsm.hbj j h1 h2) _ (BridgeLemma.isWord_deOf D u)

end GlobalTheory.RowVand
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CriticalLevelLePowAllPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelUpper

theorem root_le (ka rd g Q b Cg m k : ℝ) (hb1 : 1 < b) (hm : 2 ≤ m) (hmk : 40 * m ^ 2 ≤ k)
    (hka0 : 0 < ka) (hki : ka⁻¹ ≤ b) (hrd1 : 1 ≤ rd) (hg0 : 0 ≤ g) (hgg : g ≤ b ^ (2 * Cg)) (hCg : 0 ≤ Cg)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ b ^ (10 * k * m)) :
    (ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q) ^
      ((1 : ℝ) / k) ≤ b ^ ((4 * Cg + 12) * m) := by
  have hb0 : 0 < b := by linarith
  have hk0 : 0 < k := by nlinarith
  have hkm : 0 ≤ k * m := by positivity
  have hE1a : 0 ≤ (m - 1) * k + m * (m - 1) / 2 := by nlinarith
  have hE1b : (m - 1) * k + m * (m - 1) / 2 ≤ 3 / 2 * (k * m) := by nlinarith
  have hE3a : 0 ≤ k * m + m * (m - 1) / 2 := by nlinarith
  have hE3b : k * m + m * (m - 1) / 2 ≤ 3 / 2 * (k * m) := by nlinarith
  have hP1 : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) ≤ b ^ (3 / 2 * (k * m)) := by
    rw [Real.rpow_neg hka0.le, ← Real.inv_rpow hka0.le]
    calc ka⁻¹ ^ ((m - 1) * k + m * (m - 1) / 2) ≤ b ^ ((m - 1) * k + m * (m - 1) / 2) :=
          Real.rpow_le_rpow (by positivity) hki hE1a
      _ ≤ b ^ (3 / 2 * (k * m)) := Real.rpow_le_rpow_of_exponent_le hb1.le hE1b
  have hP10 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2)) := Real.rpow_nonneg hka0.le _
  have hP2 : rd ^ (-((m - 1) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrd1 (by linarith)
  have hP20 : 0 ≤ rd ^ (-((m - 1) / 2)) := Real.rpow_nonneg (by linarith) _
  have hP3 : g ^ (k * m + m * (m - 1) / 2) ≤ b ^ (3 * Cg * (k * m)) := by
    calc g ^ (k * m + m * (m - 1) / 2) ≤ (b ^ (2 * Cg)) ^ (k * m + m * (m - 1) / 2) :=
          Real.rpow_le_rpow hg0 hgg hE3a
      _ = b ^ (2 * Cg * (k * m + m * (m - 1) / 2)) := (Real.rpow_mul hb0.le _ _).symm
      _ ≤ b ^ (3 * Cg * (k * m)) := by
        apply Real.rpow_le_rpow_of_exponent_le hb1.le
        nlinarith
  have hP30 : 0 ≤ g ^ (k * m + m * (m - 1) / 2) := Real.rpow_nonneg hg0 _
  have hX0 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) *
      g ^ (k * m + m * (m - 1) / 2) * Q := by positivity
  have hXb : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) *
      g ^ (k * m + m * (m - 1) / 2) * Q ≤ b ^ (k * ((4 * Cg + 12) * m)) := by
    calc ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q
        ≤ b ^ (3 / 2 * (k * m)) * 1 * b ^ (3 * Cg * (k * m)) * b ^ (10 * k * m) := by
          gcongr
      _ = b ^ (3 / 2 * (k * m) + 3 * Cg * (k * m) + 10 * k * m) := by
          rw [Real.rpow_add hb0, Real.rpow_add hb0]; ring
      _ ≤ b ^ (k * ((4 * Cg + 12) * m)) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1.le
          nlinarith
  calc _ ≤ (b ^ (k * ((4 * Cg + 12) * m))) ^ ((1 : ℝ) / k) :=
        Real.rpow_le_rpow hX0 hXb (by positivity)
    _ = b ^ ((4 * Cg + 12) * m) := by
        rw [← Real.rpow_mul hb0.le]
        congr 1
        field_simp

theorem tcrit_le_pow : Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ, Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m : ℝ)) := by
  intro hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT h h40 u τ
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hH := h.1
  obtain ⟨_, _, _, _, _, _, hm2L, _, _, _, hlogrd, hkg1, hg1, _, hg2, -⟩ := hH
  have hL : 1 ≤ large₂.sc.L := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hbexp : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have hb1 : 1 < large₂.sc.b := by
    rw [hbexp]; exact lt_of_lt_of_le (by linarith) (Real.add_one_le_exp large₂.sc.L)
  have hb0 : 0 < large₂.sc.b := by linarith
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by have := D.R.two_le_m; exact_mod_cast this
  have hmk : 40 * (D.R.m : ℝ) ^ 2 ≤ (D.R.k : ℝ) := by
    have h1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := le_mul_of_one_le_right (by positivity) hL
    have h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) :=
      mul_le_mul_of_nonneg_right h40 (by positivity)
    linarith
  have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by nlinarith

  have hCL : 1 ≤ Cl * large₂.sc.L := by nlinarith
  have hVV := Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT h.1 hCL τ
  have hlam0 : 0 < vand (lamSH D.R (D.hc τ)) :=
    Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb =>
      sub_pos.2 (Formalism.MainNotions.BridgeLemma.szh_anti h.1 τ (Finset.mem_filter.1 hb).2)
  have hvand : vand (lamSH D.R (D.hc τ)) ≤ Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) * vand (uS D u τ) :=
    GlobalTheory.RowVand.vand_lamSH_le D large₂ C' Cl Cg cb Cu cT CT C0 h h40 u τ
  have hexp : Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) = large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := by
    rw [hbexp, ← Real.exp_mul]; ring_nf
  rw [hexp] at hvand
  have hbp : 0 < large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := Real.rpow_pos_of_pos hb0 _
  have hu0 : 0 < vand (uS D u τ) := (pos_iff_pos_of_mul_pos (hlam0.trans_le hvand)).1 hbp
  have hQ0 : 0 ≤ VV D τ / vand (uS D u τ) := by rw [hVV]; positivity
  have hQ : VV D τ / vand (uS D u τ) ≤ large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := by
    rw [div_le_iff₀ hu0, hVV]; exact hvand

  have hrd1 : 1 ≤ D.host.rdE := by
    have h1 : (1 : ℝ) ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
    exact Real.one_le_rpow h1 (by positivity)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    have hCl0 : 0 < Cl := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine hlogrd.trans ?_
      rw [div_le_iff₀ hCl0]; nlinarith
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log hrd0).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.mpr h1
      _ = large₂.sc.b := hbexp.symm

  have hka : D.host.ka = 2 * Real.pi / D.host.rdE := by
    show Real.pi / (D.host.rdE / 2) = 2 * Real.pi / D.host.rdE
    field_simp
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hki : D.host.ka⁻¹ ≤ large₂.sc.b := by
    rw [hka, inv_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]

  have hg1ge : 1 ≤ (D.host.g 0 : ℝ) :=
    le_trans (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hk1 hb1.le)) hkg1
  have hCg : 0 ≤ Cg := by
    by_contra hc
    push_neg at hc
    have := Real.rpow_lt_one_of_one_lt_of_neg hb1 hc
    linarith
  have hgg : gg D ≤ large₂.sc.b ^ (2 * Cg) := by
    rw [show 2 * Cg = Cg + Cg by ring, Real.rpow_add hb0]
    unfold gg
    exact mul_le_mul hg1 hg2 (by positivity) (by positivity)
  have hgg0 : 0 ≤ gg D := by unfold gg; positivity
  have key := root_le D.host.ka D.host.rdE (gg D) (VV D τ / vand (uS D u τ)) large₂.sc.b Cg D.R.m D.R.k
    hb1 hm hmk hka0 hki hrd1 hgg0 hgg hCg hQ0 hQ
  unfold Tcrit
  rw [mul_div_assoc]
  exact key

end GlobalTheory.CritLevelUpper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CriticalLevelLePowAllPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.criticalLevel_le_pow_allPlaces : Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ, Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m : ℝ)) := by
  first | exact @GlobalTheory.CritLevelUpper.tcrit_le_pow | exact GlobalTheory.CritLevelUpper.tcrit_le_pow | (intros; apply GlobalTheory.CritLevelUpper.tcrit_le_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelPrimesSizeBoundsColumnDimension
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem levelPrime_size : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → C0 * Real.exp 8 ≤ D.R.k → LocalBesselAndTopKernel.FamilyMidVolume D → ∀ u, large₂.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m : ℝ)) := by
  intro hS hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl hCu hC0 hR u
  obtain ⟨hF, hA, -, hk⟩ := pgFrame_at_record hS hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl hCu hC0 hR
  have hcrit := GlobalTheory.T.criticalLevel_le_pow_allPlaces hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT hH hCl
  obtain ⟨hS0, hData, hC01⟩ := hH
  dsimp only [StandingHypotheses] at hS0
  obtain ⟨-, -, hm4, hfk, -, -, -, -, -, -, -, hg1, -, hg2, -, -, -, -, hv, -, -, -, -, hClm, -⟩ := hS0
  have hwin := (hData.2.2.2.2.2.2.2.2.2.1 u).2

  have hLpos : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hb : 1 < large₂.sc.b := by
    have := Real.add_one_le_exp large₂.sc.L
    show 1 < Real.exp large₂.sc.L
    linarith
  have hbpos : 0 < large₂.sc.b := by linarith
  have hm40 : (40:ℝ) ≤ D.R.m := le_trans hCl hClm
  have hmk : ((D.R.m + 3 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  push_cast at hmk
  have hk40 : (40:ℝ) ≤ D.R.k := by linarith
  have hkpos : (0:ℝ) < D.R.k := by linarith
  have hfpos : (0:ℝ) < D.R.f := by
    have h1 : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_trans h1 hm4)
  have hfk' : (D.R.f:ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hrS : 2 * D.R.rS + 2 = D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    omega

  have hkb : 0 < (D.R.k:ℝ) * large₂.sc.b := mul_pos hkpos hbpos
  have hgg : ((D.R.k:ℝ) * large₂.sc.b) ^ 16 ≤ gg D := by
    show _ ≤ (D.host.g 0 : ℝ) * D.host.g 1
    have h0 : 0 ≤ ((D.R.k:ℝ) * large₂.sc.b) ^ 8 := (pow_pos hkb 8).le
    calc ((D.R.k:ℝ) * large₂.sc.b) ^ 16 = ((D.R.k:ℝ) * large₂.sc.b) ^ 8 * ((D.R.k:ℝ) * large₂.sc.b) ^ 8 := by ring
      _ ≤ _ := mul_le_mul hg1 hg2 h0 (le_trans h0 hg1)
  have hggpos : 0 < gg D := lt_of_lt_of_le (pow_pos hkb 16) hgg

  have hka_pos : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
  have hka_le : D.host.ka ≤ 4 := by
    show Real.pi / D.host.v ≤ 4
    rw [div_le_iff₀ (by linarith)]
    linarith [Real.pi_le_four]
  have hK_pos : 0 < Bridge.kaS D := div_pos hka_pos hggpos
  have hK : Bridge.kaS D * large₂.sc.b ^ 16 ≤ 1 := by
    show D.host.ka / gg D * large₂.sc.b ^ 16 ≤ 1
    rw [div_mul_eq_mul_div, div_le_one hggpos]
    have hk16 : (D.R.k:ℝ) ≤ (D.R.k:ℝ) ^ 16 := le_self_pow₀ (by linarith) (by norm_num)
    have hb16 : 0 ≤ large₂.sc.b ^ 16 := (pow_pos hbpos 16).le
    calc D.host.ka * large₂.sc.b ^ 16 ≤ 4 * large₂.sc.b ^ 16 := mul_le_mul_of_nonneg_right hka_le hb16
      _ ≤ (D.R.k:ℝ) ^ 16 * large₂.sc.b ^ 16 := mul_le_mul_of_nonneg_right (by linarith) hb16
      _ = ((D.R.k:ℝ) * large₂.sc.b) ^ 16 := by ring
      _ ≤ gg D := hgg
  unfold Formalism.L2.SG.RowsConc.TFrameAt at hF
  have hT0 : 0 ≤ Tr D u := Nat.cast_nonneg _
  have hlow : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ Tr D u := by
    have h1 := hF u
    have h2 : (Bridge.kaS D * large₂.sc.b ^ 16) ^ (2 * D.R.rS) ≤ 1 :=
      pow_le_one₀ (mul_pos hK_pos (pow_pos hbpos 16)).le hK
    rw [mul_pow] at h2
    have hP : 0 ≤ (large₂.sc.b ^ 16) ^ (2 * D.R.rS) := (pow_pos (pow_pos hbpos 16) _).le
    have e : (large₂.sc.b ^ 16) ^ (2 * D.R.rS) * (Tr D u * Bridge.kaS D ^ (2 * D.R.rS)) =
        Tr D u * (Bridge.kaS D ^ (2 * D.R.rS) * (large₂.sc.b ^ 16) ^ (2 * D.R.rS)) := by ring
    linarith [mul_le_mul_of_nonneg_left h1 hP, mul_le_mul_of_nonneg_left h2 hT0]
  refine ⟨le_trans ?_ hlow, ?_⟩
  · rw [← pow_mul, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb.le
    have : ((2 * D.R.rS + 2 : ℕ) : ℝ) = D.R.m := by exact_mod_cast hrS
    push_cast at this ⊢
    linarith
  ·
    by_contra hup
    push Not at hup
    have hbm : 0 < large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := Real.rpow_pos_of_pos hbpos _
    have hTpos : 0 < Tr D u := lt_trans hbm hup
    obtain ⟨q, hq⟩ : ∃ q, q = large₂.sc.b ^ (-(D.R.m:ℝ)) := ⟨_, rfl⟩
    have hq0 : 0 ≤ q := by rw [hq]; exact (Real.rpow_pos_of_pos hbpos _).le
    have hq1 : q ≤ 1 := by
      rw [hq]; exact (Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)).le
    have hq_eq : large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m:ℝ)) = q * large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := by
      rw [hq, ← Real.rpow_add hbpos]; congr 1; ring
    have hgg0 : 0 ≤ gg D := hggpos.le
    have hTc_pos : ∀ τ, 0 < Tcrit D u τ := by
      intro τ
      have h := hk u τ
      have h1 : (0:ℝ) < (D.R.k:ℝ) ^ (3 * D.R.rS) := pow_pos hkpos _
      by_contra hc
      push Not at hc
      have : gg D ^ (-(D.R.m:ℝ)) * Tcrit D u τ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hgg0 _) hc
      linarith
    have hxpos : ∀ τ, 0 < Tcrit D u τ / Tr D u := fun τ => div_pos (hTc_pos τ) hTpos
    have hx : ∀ τ, Tcrit D u τ / Tr D u ≤ q := by
      intro τ
      rw [div_le_iff₀ hTpos]
      calc Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m:ℝ)) := hcrit u τ
        _ = q * large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m:ℝ)) := hq_eq
        _ ≤ q * Tr D u := mul_le_mul_of_nonneg_left hup.le hq0
    have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
    obtain ⟨τ0⟩ := hTau
    classical
    have hprod : ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k ≤ q ^ D.R.k := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ0)]
      have hrest : ∏ τ ∈ Finset.univ.erase τ0, (Tcrit D u τ / Tr D u) ^ D.R.k ≤ 1 :=
        Finset.prod_le_one₀ (fun τ _ => pow_nonneg (hxpos τ).le _)
          (fun τ _ => pow_le_one₀ (hxpos τ).le (le_trans (hx τ) hq1))
      calc (Tcrit D u τ0 / Tr D u) ^ D.R.k * ∏ τ ∈ Finset.univ.erase τ0, (Tcrit D u τ / Tr D u) ^ D.R.k
          ≤ (Tcrit D u τ0 / Tr D u) ^ D.R.k * 1 :=
            mul_le_mul_of_nonneg_left hrest (pow_nonneg (hxpos τ0).le _)
        _ ≤ q ^ D.R.k := by rw [mul_one]; exact pow_le_pow_left₀ (hxpos τ0).le (hx τ0) _
    have hP0 : 0 < ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k :=
      Finset.prod_pos (fun τ _ => pow_pos (hxpos τ) _)
    unfold UnitaryVolumeMass.cTvA at hA
    obtain ⟨hlo, hhi⟩ := hA u
    have hQ : 0 < D.what₂.Dstar / (D.duS u : ℝ) := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hP0) hlo
    have hd : 0 < (D.duS u : ℝ) := by
      rcases (Nat.cast_nonneg (D.duS u) : (0:ℝ) ≤ _).eq_or_lt with h | h
      · rw [← h, div_zero] at hQ
        exact absurd hQ (lt_irrefl 0)
      · exact h
    have hDs : 0 < D.what₂.Dstar := by
      have := mul_pos hQ hd
      rwa [div_mul_cancel₀ _ hd.ne'] at this
    have hC0pos : 0 < C0 := by linarith

    have hlogG : 0 < Real.log (D.mem u).A.GamP := by
      rw [large₂.Gam_eq u]
      have hL0 : 0 < large₂.sc.L := by linarith
      have hm0 : (0:ℝ) < D.R.m := by linarith
      exact mul_pos (mul_pos (mul_pos large₂.CGam_pos (pow_pos hm0 5)) hfpos) hL0
    have hG0 : (D.mem u).A.GamP ≠ 0 := by
      intro h
      rw [h, Real.log_zero] at hlogG
      exact lt_irrefl 0 hlogG
    have hGabs : 1 < |(D.mem u).A.GamP| := by
      rw [← Real.exp_log_eq_abs hG0]
      have := Real.add_one_le_exp (Real.log (D.mem u).A.GamP)
      linarith
    have hGz : (D.mem u).A.GamP ^ (-2:ℤ) ≤ 1 := by
      rw [zpow_neg, zpow_two]
      apply inv_le_one_of_one_le₀
      rw [← abs_mul_abs_self (D.mem u).A.GamP]
      exact (one_lt_mul_of_lt_of_le hGabs hGabs.le).le
    have hwin' : (D.duS u : ℝ) ≤ 1 * D.what₂.Dstar * C0 :=
      le_trans hwin (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hGz hDs.le) hC0pos.le)
    have hinv : 1 / C0 ≤ D.what₂.Dstar / (D.duS u : ℝ) :=
      (div_le_div_iff₀ hC0pos hd).mpr (by linarith)

    have h2pow : (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ 8 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by linarith : (3:ℝ) - D.R.k ≤ 3)
      have h8 : (2:ℝ) ^ (3:ℝ) = 8 := by
        rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      linarith
    have hexp1 : (D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ 8 * D.R.k := by
      calc (D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) ≤ (D.R.f:ℝ) * 8 := mul_le_mul_of_nonneg_left h2pow hfpos.le
        _ ≤ 8 * D.R.k := by linarith
    have hqk : q ^ D.R.k = Real.exp (-((D.R.k:ℝ) * large₂.sc.L * D.R.m)) := by
      rw [hq, show large₂.sc.b = Real.exp large₂.sc.L from rfl, ← Real.exp_mul, ← Real.exp_nat_mul]
      congr 1
      ring
    have hLm : (40:ℝ) * D.R.k ≤ (D.R.k:ℝ) * large₂.sc.L * D.R.m := by
      have h40 : (1:ℝ) * 40 ≤ large₂.sc.L * D.R.m := mul_le_mul hLpos.le hm40 (by norm_num) (by linarith)
      rw [mul_assoc]
      linarith [mul_le_mul_of_nonneg_left h40 hkpos.le]
    have hmain : 1 / C0 ≤ Real.exp (-(32 * (D.R.k:ℝ))) := by
      calc 1 / C0 ≤ D.what₂.Dstar / (D.duS u : ℝ) := hinv
        _ ≤ Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k)) * ∏ τ, (Tcrit D u τ / Tr D u) ^ D.R.k := hhi
        _ ≤ Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k)) * q ^ D.R.k :=
            mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
        _ = Real.exp ((D.R.f:ℝ) * (2:ℝ) ^ ((3:ℝ) - D.R.k) - (D.R.k:ℝ) * large₂.sc.L * D.R.m) := by
            rw [hqk, ← Real.exp_add]
            ring_nf
        _ ≤ Real.exp (-(32 * (D.R.k:ℝ))) := Real.exp_le_exp.mpr (by linarith)
    have hC0k : C0 ≤ D.R.k := by
      have h8 := Real.add_one_le_exp 8
      calc C0 = C0 * 1 := (mul_one C0).symm
        _ ≤ C0 * Real.exp 8 := mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
        _ ≤ D.R.k := hC0
    have hkexp : (D.R.k:ℝ) + 1 ≤ Real.exp D.R.k := Real.add_one_le_exp _
    have h31 : Real.exp (-(31 * (D.R.k:ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hsplit : Real.exp (D.R.k:ℝ) * Real.exp (-(32 * (D.R.k:ℝ))) = Real.exp (-(31 * (D.R.k:ℝ))) := by
      rw [← Real.exp_add]
      ring_nf
    have he32 : 0 < Real.exp (-(32 * (D.R.k:ℝ))) := Real.exp_pos _
    have h1C : 1 ≤ C0 * Real.exp (-(32 * (D.R.k:ℝ))) := by
      rw [div_le_iff₀ hC0pos] at hmain
      linarith
    have e : ((D.R.k:ℝ) + 1) * Real.exp (-(32 * (D.R.k:ℝ))) =
        (D.R.k:ℝ) * Real.exp (-(32 * (D.R.k:ℝ))) + Real.exp (-(32 * (D.R.k:ℝ))) := by ring
    linarith [mul_le_mul_of_nonneg_right hC0k he32.le, mul_le_mul_of_nonneg_right hkexp he32.le]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelPrimesSizeBoundsColumnDimensionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimes_size_bounds_columnDimension : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → Cu * large₂.sc.L ≤ (D.R.m : ℝ) - 1 → C0 * Real.exp 8 ≤ D.R.k → LocalBesselAndTopKernel.FamilyMidVolume D → ∀ u, large₂.sc.b ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧ Tr D u ≤ large₂.sc.b ^ ((4 * Cg + 13) * (D.R.m : ℝ)) := by
  first | exact @GlobalTheory.levelPrime_size | exact GlobalTheory.levelPrime_size | (intros; apply GlobalTheory.levelPrime_size <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoLeRootDiscriminantAndSplitArithmeticCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoLeRootDiscriminantAndSplitArithmeticCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem two_le_rdE_and_arithmeticConditionsS0 : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := fun D =>
  ⟨S.root_discriminant_ge_two _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _),
    fun u => S.splitsCompl_of_ncard _ _ (D.mem u).A.T_prime
      (Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion.split_clause _ Formalism.L2.SG.ResidEvFree.cycSplit_holds _ (D.mem u).A.T_prime (S.level_norm_one_mod_conductor _ u)).2,
    Formalism.L2.SG.ResidEvFree.splitsE_g _ 0, Formalism.L2.SG.ResidEvFree.splitsE_g _ 1, S.discriminant_eq_base_sq _ (UnusedSlot33.ramification_two_and_conjugation_at_q_and_d _)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoLeRootDiscriminantAndSplitArithmeticConditionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_le_rootDiscriminant_and_split_arithmetic_conditions : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := by
  first | exact @GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | exact GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | (intros; apply GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DataConditionsOfGlobalAndRealRows
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DataConditionsOfGlobalAndRealRows
noncomputable section

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem data_of_rows (eps CD : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (hCD : 3 ≤ CD) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D →
      DuWin D C0 → StandingNumericalData D C0 := by
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.globalRankNumberBounds_size_comparisons eps CD he he' hCD 1 one_pos
  refine ⟨max x1 1, fun x hx D Cg C0 hG hN hA hW => ?_⟩
  have hxx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨-, -, -, h12, -⟩ := hx1 x hxx1 _ _ _ _ _ hG.nums
  have hk : 5 ≤ D.R.k := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    omega
  have hm2 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl

  have hF : ∀ {n : ℕ} (g : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n), a = b →
      g ⟨a, ha⟩ = g ⟨b, hb⟩ := by
    intro n g a b ha hb h
    subst h
    rfl

  have huO : ∀ u τ (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k),
      Formalism.MainNotions.S.uOne D u τ i = (((D.hcW u τ).u ⟨i - 1, by omega⟩ : ℚ) : ℝ) := by
    intro u τ i h1 h2
    unfold Formalism.MainNotions.S.uOne Formalism.MainNotions.S.uS
    rw [dite_eq_left ⟨h1, h2⟩]
  have hvO : ∀ τ (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 1),
      Formalism.MainNotions.S.vOne D τ l = (((D.hc τ).v ⟨l - 1, by omega⟩ : ℚ) : ℝ) := by
    intro τ l h1 h2
    unfold Formalism.MainNotions.S.vOne
    rw [dite_eq_left ⟨h1, h2⟩]
  have hbO : ∀ τ, Formalism.MainNotions.S.bOne D τ 1 = bFirst D τ := by
    intro τ
    unfold Formalism.MainNotions.S.bOne bFirst
    rw [dite_eq_left ⟨le_rfl, by have := D.R.two_le_m; omega⟩]
  have hu1 : ∀ u τ, Formalism.MainNotions.S.uOne D u τ 1 = uFirst D τ := by
    intro u τ
    rw [huO u τ 1 le_rfl (by omega)]
    unfold uFirst
    exact congrArg (fun q : ℚ => (q : ℝ))
      ((hF _ (1 - 1) 0 _ (by omega) (by norm_num)).trans (D.hcW_first u τ (by omega)))
  have huk : ∀ u τ, Formalism.MainNotions.S.uOne D u τ D.R.k = uLast D τ := by
    intro u τ
    rw [huO u τ D.R.k (by omega) le_rfl]
    unfold uLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (D.hcW_last u τ (by omega))
  have hv1 : ∀ τ, Formalism.MainNotions.S.vOne D τ 1 = vFirst D τ := by
    intro τ
    rw [hvO τ 1 le_rfl (by omega)]
    unfold vFirst
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by norm_num))
  have hvk : ∀ τ, Formalism.MainNotions.S.vOne D τ (D.R.k - 1) = vLast D τ := by
    intro τ
    rw [hvO τ (D.R.k - 1) (by omega) le_rfl]
    unfold vLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by omega))
  have hDel : (0 : ℝ) < D.s.Del := by exact_mod_cast D.s.Del_pos
  have hkDel : (0 : ℝ) ≤ (D.R.k : ℝ) * D.s.Del := mul_nonneg (Nat.cast_nonneg _) hDel.le

  have hbx : 1 ≤ bx x eps := by
    unfold bx
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hg : ∀ i, 2 ≤ D.host.g i := by
    intro i
    have h := (hG.g_win i).1
    have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
    have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * bx x eps := by nlinarith
    have h2 : (2 : ℝ) ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 :=
      calc (2 : ℝ) ≤ 5 := by norm_num
        _ ≤ (D.R.k : ℝ) * bx x eps := h5
        _ ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast h2.trans h
  unfold Formalism.MainNotions.S.StandingNumericalData
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩
  ·
    intro τ l h1 h2
    rw [hvO τ l h1 h2]
    exact hG.cloud τ ⟨l - 1, by omega⟩
  ·
    intro u l h1 h2
    have key : ∀ τ, Formalism.MainNotions.S.uOne D u τ (l + 1) = Formalism.MainNotions.S.vOne D τ l - 1 / 2 -
        (if D.s.letter u ⟨l - 1, by omega⟩ then (D.s.Del : ℝ) else 0) := by
      intro τ
      rw [huO u τ (l + 1) (by omega) (by omega), hvO τ l h1 (by omega)]
      have e := D.s.u_letter u τ (l - 1) (by omega)
      rw [D.hcW_v u τ] at e
      have e' : (D.hcW u τ).u ⟨l + 1 - 1, by omega⟩ = (D.hcW u τ).u ⟨l - 1 + 1, by omega⟩ :=
        hF _ _ _ _ _ (by omega)
      rw [e', e]
      split_ifs <;> push_cast <;> ring
    by_cases hL : D.s.letter u ⟨l - 1, by omega⟩ = true
    · right
      intro τ
      rw [key τ, if_pos hL]
    · left
      intro τ
      rw [key τ, if_neg hL]
      ring
  ·
    intro u τ
    rw [hu1 u τ, hv1 τ]
    by_cases ht : Top D τ
    · have h1 := (hN.top τ ht).1
      have h2 := (hG.cloud τ ⟨0, by omega⟩).2
      have hvF : vFirst D τ = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
        unfold vFirst
        rfl
      rw [hvF]
      nlinarith
    · exact (hG.off τ ht).1
  ·
    intro u τ ht
    rw [hu1 u τ, hv1 τ]
    exact (hG.off τ ht).2.1
  ·
    intro u τ ht
    rw [huk u τ, hvk τ]
    exact (hG.off τ ht).2.2
  ·
    intro τ ht
    unfold Formalism.MainNotions.S.bTop
    rw [huk D.u₀ τ, hbO τ]
    obtain ⟨-, -, h3, h4⟩ := hN.top τ ht
    constructor <;> linarith
  ·
    intro u τ
    constructor
    · intro i hi
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨i, by omega⟩ = (((D.hcW u τ).v ⟨i, by omega⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dite_eq_left (show i < D.R.k - 1 by omega), D.hcW_v u τ]
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact ⟨by exact_mod_cast (D.hcW u τ).u_gt_v ⟨i, by omega⟩,
        by exact_mod_cast (D.hcW u τ).v_gt_u ⟨i, by omega⟩⟩
    · intro h
      have hm : 0 < D.R.m := by
        have := D.R.two_le_m
        omega
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨D.R.k - 1, by omega⟩ =
          -(((D.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dite_eq_right (show ¬ (D.R.k - 1 < D.R.k - 1) by omega),
          dite_eq_left (show D.R.k - 1 - (D.R.k - 1) < D.R.m by omega), D.hcW_b u τ]
        exact congrArg (fun q : ℚ => -(q : ℝ)) (hF _ _ _ _ _ (by simp))
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact_mod_cast (D.hcW u τ).u_last_gt h hm
  ·
    intro u u' hne τ heq
    have hl : D.s.letter u ≠ D.s.letter u' := fun h => hne (D.s.letter_inj h)
    obtain ⟨⟨j, hj⟩, hjl⟩ := Function.ne_iff.mp hl
    have e := congrFun heq ⟨j + 1, by omega⟩
    simp only [Formalism.MainNotions.S.uS] at e
    have e' : (D.hcW u τ).u ⟨j + 1, by omega⟩ = (D.hcW u' τ).u ⟨j + 1, by omega⟩ := by
      exact_mod_cast e
    rw [D.s.u_letter u τ j hj, D.s.u_letter u' τ j hj, D.hcW_v, D.hcW_v] at e'
    have hQ := D.s.Del_pos
    cases h1 : D.s.letter u ⟨j, hj⟩ <;> cases h2 : D.s.letter u' ⟨j, hj⟩ <;>
      simp only [h1, h2] at e' hjl <;> simp at e' hjl <;> linarith
  ·
    intro u
    exact ⟨hA.1 u, Formalism.MainNotions.S.T_mod D u⟩
  ·
    intro u
    exact Formalism.MainNotions.S.ne_of_mod (hg 0) (hg 1) (Formalism.MainNotions.S.T_mod D u)

end GlobalTheory.Diag.PG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DataConditionsOfGlobalAndRealRowsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataConditions_of_global_and_real_rows : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D → DuWin D C0 → StandingNumericalData D C0 := by
  first | exact @GlobalTheory.Diag.PG.data_of_rows | exact GlobalTheory.Diag.PG.data_of_rows | (intros; apply GlobalTheory.Diag.PG.data_of_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalHypothesesOfRowsAndWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem lemmaPG_record : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg C : ℝ, 40 ≤ Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Glob0 D x eps CD Cg → Nodes D x eps → DuWin D 3 → AdmissibleBoundsFromSource.hyp D large₂ 3 C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ Formalism.L2.SG.RowsConc.TFrameAt D ∧ C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 ∧ C ≤ (D.R.k : ℝ) := by
  intro hSM hDs eps CD heps0 heps1 hCD C' Cl Cg C hCl40 hClCD
  have hCl0 : (0 : ℝ) < Cl := by linarith
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.dataConditions_of_global_and_real_rows eps CD heps0 heps1 hCD
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.hypotheses_of_global_rows_and_nodes eps CD heps0 heps1 hCD C' Cl Cg hCl0 hClCD
  obtain ⟨x3, hx3⟩ := GlobalTheory.T.eventually_rankNums_imp_parameter_lower_bounds eps CD heps0 heps1 hCD (max C (3 * Real.exp 8))
  refine ⟨max x1 (max x2 x3), ?_⟩
  intro x hx D large₂ hL hC' hTies hAdm hG hN hW
  have hx1' : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2' : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3' : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx

  obtain ⟨-, hAr⟩ := GlobalTheory.T.two_le_rootDiscriminant_and_split_arithmetic_conditions D
  have hData : StandingNumericalData D 3 := hx1 x hx1' D Cg 3 hG hN hAr hW

  obtain ⟨-, -, -, -, -, hm1, hk, hxe⟩ := hx3 x hx3' _ _ _ _ _ hG.nums
  have hxe0 : (0 : ℝ) ≤ x ^ eps := le_of_lt (lt_trans zero_lt_one hxe)
  have h3 : (3 : ℝ) ≤ max C (3 * Real.exp 8) :=
    le_trans (by have := Real.add_one_le_exp (8 : ℝ); linarith) (le_max_right _ _)
  have hCm : C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxe0) hm1
  have h3m : 3 * large₂.sc.L ≤ (D.R.m : ℝ) - 1 := by
    rw [hL]; exact le_trans (mul_le_mul_of_nonneg_right h3 hxe0) hm1
  have h3k : 3 * Real.exp 8 ≤ (D.R.k : ℝ) := le_trans (le_max_right _ _) hk
  have hCk : C ≤ (D.R.k : ℝ) := le_trans (le_max_left _ _) hk

  have hLpos : 0 < large₂.sc.L := by rw [hL]; linarith
  have hb1 : 1 < large₂.sc.b := by
    show 1 < Real.exp large₂.sc.L
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hLpos
  have hb0 : 0 < large₂.sc.b := lt_trans zero_lt_one hb1
  have hm0 : (0 : ℝ) < (D.R.m : ℝ) := by
    have := D.R.two_le_m
    exact_mod_cast (show 0 < D.R.m by omega)
  have hT1 : ∀ u, (1 : ℝ) ≤ Tr D u := fun u => by
    show (1 : ℝ) ≤ ((D.mem u).A.T : ℝ)
    exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hmb : (D.R.m : ℝ) * Real.log large₂.sc.b ≠ 0 := (mul_pos hm0 (Real.log_pos hb1)).ne'
  obtain ⟨CT0, hCT0⟩ : ∃ c : ℝ, c * ((D.R.m : ℝ) * Real.log large₂.sc.b) = ∑ v, Real.log (Tr D v) :=
    ⟨(∑ v, Real.log (Tr D v)) / ((D.R.m : ℝ) * Real.log large₂.sc.b), div_mul_cancel₀ _ hmb⟩
  have hwin0 : ∀ u, large₂.sc.b ^ ((0 : ℝ) * (D.R.m : ℝ)) ≤ Tr D u ∧
      Tr D u ≤ large₂.sc.b ^ (CT0 * (D.R.m : ℝ)) := by
    intro u
    refine ⟨by rw [zero_mul, Real.rpow_zero]; exact hT1 u, ?_⟩
    rw [Real.rpow_def_of_pos hb0,
      show Real.log large₂.sc.b * (CT0 * (D.R.m : ℝ)) = CT0 * ((D.R.m : ℝ) * Real.log large₂.sc.b) by ring, hCT0]
    calc Tr D u = Real.exp (Real.log (Tr D u)) :=
          (Real.exp_log (lt_of_lt_of_le zero_lt_one (hT1 u))).symm
      _ ≤ Real.exp (∑ v, Real.log (Tr D v)) :=
          Real.exp_le_exp.mpr (Finset.single_le_sum (fun v _ => Real.log_nonneg (hT1 v))
            (Finset.mem_univ u))

  have hHyp0 : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 := hx2 x hx2' D large₂ 0 CT0 hL hC' hG hN hwin0
  have hCnt : Cnt.Hyp0 D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 :=
    (⟨hHyp0, hData, by norm_num⟩ : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 0 CT0 ∧ StandingNumericalData D 3 ∧ (1 : ℝ) ≤ 3)

  have hFr := (GlobalTheory.pgFrame_at_record hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm).1
  have hwin := GlobalTheory.T.levelPrimes_size_bounds_columnDimension hSM hDs D large₂ C' Cl Cg (1 / 4) 3 0 CT0 3 hTies hCnt hCl40 h3m h3k hAdm

  have hHyp : StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) :=
    hx2 x hx2' D large₂ (1 / 2) (4 * Cg + 13) hL hC' hG hN hwin
  exact ⟨(⟨hData, hHyp, by norm_num⟩ :
      StandingNumericalData D 3 ∧ StandingHypotheses D large₂ C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ (1 : ℝ) ≤ 3), hFr, hCm, hCk⟩

end GlobalTheory.Diag.PG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalHypothesesOfRowsAndWindowStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_hypotheses_of_rows_and_window : Formalism.HermitianLatticesTheory.SiegelMassRatio → Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C' Cl Cg C : ℝ, 40 ≤ Cl → Cl ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.L = x ^ eps → 8 * large₂.CGam ≤ C' → Ties D → LocalBesselAndTopKernel.FamilyMidVolume D → Glob0 D x eps CD Cg → Nodes D x eps → DuWin D 3 → AdmissibleBoundsFromSource.hyp D large₂ 3 C' Cl Cg (1 / 4) 3 (1 / 2) (4 * Cg + 13) ∧ Formalism.L2.SG.RowsConc.TFrameAt D ∧ C * large₂.sc.L ≤ (D.R.m : ℝ) - 1 ∧ C ≤ (D.R.k : ℝ) := by
  first | exact @GlobalTheory.Diag.PG.lemmaPG_record | exact GlobalTheory.Diag.PG.lemmaPG_record | (intros; apply GlobalTheory.Diag.PG.lemmaPG_record <;> assumption)
end
