module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddings
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitriangularFramesGramEqCellPoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMeanEmbeddedPairsLeMassMulPairBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBounded
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PairsLab

theorem norms_of_relevant : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  intro Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost hNF hLab hTerm hH t ht
  have hS : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := hHost D large₂ hS
  obtain ⟨N, hN, hNj, hNT⟩ := hNF D large₂ X Y u hS t ht
  have hT : N.IsTerm (gS D) t.lam := hTerm D large₂ X Y u hS t N hN
  obtain ⟨-, -, hDel, hDb, -⟩ := hLab D large₂ X Y u hS t N hN
  obtain ⟨𝔠, -, hDb1, hDel1, -⟩ := GlobalTheory.DegCnt.Absorb.exists_absorbing_ideal D.host.E (VS D).V (HV D) hK D.R.rS N (gS D)
    t.lam (by omega) hT
  have hPF : PFHost D := PFHost_of_data D hH.1.2.1
  have hC : 2 * (CH + 1) ≤ 2 * (CH + 1) := le_rfl
  have hup := (delta_pos_le_height_sq hPF large₂ hCH hC t ht).2
  have hb := two_le_scale_b D large₂
  have hHb : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := by
    unfold Hb
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hS1 := one_le_sigma_product (D := D) (H1C large₂ CH) (jT t) (labT t)
  have hA : (1 : ℝ) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hHb (one_le_pow₀ hS1)
  refine ⟨hDel ▸ hDel1, hDb ▸ hDb1, hup, ?_⟩
  have hcard : (k2ends D (jT t) (labT t)).card ≤ D.R.rS := by
    unfold k2ends
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]
    unfold jT
    omega
  calc DbL D (jT t) (labT t)
      ≤ ∏ _l ∈ k2ends D (jT t) (labT t),
          Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 := by
        unfold DbL
        refine Finset.prod_le_prod₀ (fun l _ => ?_) (fun l hl => localNorm_le_height_sq hPF large₂ hCH hC t l hl)
        unfold Nloc
        exact_mod_cast FractionalIdeal.absNorm_nonneg _
    _ = _ ^ (k2ends D (jT t) (labT t)).card := Finset.prod_const _
    _ ≤ _ := pow_le_pow_right₀ hA hcard

end GlobalTheory.TypeAsm.PairsLab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermNormsGeOneAndBoundedStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relevantTerm_norms_ge_one_and_bounded : ∀ (Cg cb Cw cT CT C0 CH C' Cl : ℝ), 0 ≤ CH → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word), HostC → NFExC → LabC → TermC → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
    ∀ t ∈ relSet Y u, 1 ≤ k2Del D (jT t) (labT t) ∧ 1 ≤ DbL D (jT t) (labT t) ∧
      k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2 ∧
      DbL D (jT t) (labT t) ≤ (Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2) ^ D.R.rS := by
  first | exact @GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | exact GlobalTheory.TypeAsm.PairsLab.norms_of_relevant | (intros; apply GlobalTheory.TypeAsm.PairsLab.norms_of_relevant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairBdMulDatBdLe
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm

theorem parith_small (k f g : ℕ) (b e : ℝ) (hb : 2 ≤ b) (hk : 9 ≤ k) (hf : 1 ≤ f) (hfk : f ≤ k)
    (he : 42 * (e * Real.log b) ≤ k) (hg : ((k : ℝ) * b) ^ 8 ≤ g) :
    (32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * (b ^ (e * f)) ^ 42 ≤ 1 / 2 := by
  have hb0 : 0 < b := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk0 : (0 : ℝ) < k := by linarith
  have hfk' : (f : ℝ) ≤ k := by exact_mod_cast hfk
  have h1 : (b ^ (e * f)) ^ 42 = (Real.exp (42 * (e * Real.log b))) ^ f := by
    rw [Real.rpow_def_of_pos hb0, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [h1, pow_mul, pow_mul, ← mul_pow, ← mul_pow]
  have hb8 : (256 : ℝ) ≤ b ^ 8 := by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ b ^ 8 := by gcongr
  have hk8 : (1 : ℝ) ≤ (k : ℝ) ^ 8 := one_le_pow₀ hk1
  have hg' : 256 * (k : ℝ) ^ 8 ≤ g := by
    refine le_trans ?_ hg
    rw [mul_pow]; nlinarith
  have hg0 : (0 : ℝ) < g := by linarith
  have h2 : 32 / (g : ℝ) ≤ (1 / 8) * (1 / (k : ℝ) ^ 8) := by
    rw [div_mul_div_comm, div_le_div_iff₀ hg0 (by positivity)]; linarith
  have h3 : (32 / (g : ℝ)) ^ k ≤ (1 / 8) ^ k * (1 / (k : ℝ) ^ 8) := by
    calc (32 / (g : ℝ)) ^ k ≤ ((1 / 8) * (1 / (k : ℝ) ^ 8)) ^ k := by gcongr
      _ = (1 / 8) ^ k * (1 / (k : ℝ) ^ 8) ^ k := mul_pow _ _ _
      _ ≤ _ := by
        gcongr
        exact pow_le_of_le_one (by positivity) (by rw [div_le_one (by positivity)]; exact hk8) (by omega)
  have h4 : ((4 * k * f : ℕ) : ℝ) ^ 4 ≤ 256 * (k : ℝ) ^ 8 := by
    push_cast
    calc (4 * (k : ℝ) * f) ^ 4 ≤ (4 * (k : ℝ) * k) ^ 4 := by gcongr
      _ = _ := by ring
  have h5 : Real.exp (42 * (e * Real.log b)) ≤ 4 ^ k := by
    calc _ ≤ Real.exp (k * 1) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 1 ^ k := Real.exp_nat_mul _ _
      _ ≤ 4 ^ k := by
        gcongr
        have := Real.exp_one_lt_d9
        linarith
  have h6 : (32 / (g : ℝ)) ^ k * ((4 * k * f : ℕ) : ℝ) ^ 4 * Real.exp (42 * (e * Real.log b)) ≤ 1 / 2 := by
    calc _ ≤ ((1 / 8) ^ k * (1 / (k : ℝ) ^ 8)) * (256 * (k : ℝ) ^ 8) * 4 ^ k := by gcongr
      _ = 256 * ((1 / 8) * 4) ^ k := by rw [mul_pow]; field_simp
      _ = 256 * (1 / 2) ^ k := by norm_num
      _ ≤ 256 * (1 / 2) ^ 9 := by
        gcongr 256 * ?_
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 2 := by norm_num
  exact le_trans (pow_le_of_le_one (by positivity) (by linarith) (by omega)) h6

theorem parith_bracket (k : ℕ) (M q q' Z : ℝ) (hM0 : 0 ≤ M) (hq : 0 ≤ q) (hq' : 0 ≤ q') (hqq : q' ≤ q) (hZ : 1 ≤ Z)
    (hqZ : q ≤ 1 / 2 * Z) :
    1 + M * (∑ s ∈ Finset.Ico 1 k, q ^ s) + q' ^ k ≤ (2 + 2 * M) * Z ^ k := by
  have hZk : 1 ≤ Z ^ k := one_le_pow₀ hZ
  have h1 : ∑ s ∈ Finset.Ico 1 k, q ^ s ≤ 2 * Z ^ k := by
    calc ∑ s ∈ Finset.Ico 1 k, q ^ s ≤ ∑ s ∈ Finset.range k, q ^ s := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro s hs; simp at hs ⊢; omega
          · intros; positivity
      _ ≤ ∑ s ∈ Finset.range k, (1 / 2 : ℝ) ^ s * Z ^ k := by
          apply Finset.sum_le_sum
          intro s hs
          have hs' : s ≤ k := (Finset.mem_range.1 hs).le
          calc q ^ s ≤ (1 / 2 * Z) ^ s := by gcongr
            _ = (1 / 2 : ℝ) ^ s * Z ^ s := mul_pow _ _ _
            _ ≤ _ := by gcongr
      _ ≤ 2 * Z ^ k := by
          rw [← Finset.sum_mul]
          gcongr
          exact sum_geometric_two_le k
  have h2 : q' ^ k ≤ Z ^ k := by gcongr; linarith
  have h3 : M * (∑ s ∈ Finset.Ico 1 k, q ^ s) ≤ M * (2 * Z ^ k) := by gcongr
  linarith

theorem parith_rest (r : ℕ) (hr : 1 ≤ r) (c f Del Db NT U : ℝ) (hc : c ≤ 4 * r) (hU : 1 ≤ U) (h8 : 8 ^ (r + 1) ≤ U)
    (hf : f ^ 2 ≤ U) (hD : 1 ≤ Del) (hDU : Del ≤ U) (hN : 0 ≤ NT) (hNU : NT ≤ U) (hDb : 0 ≤ Db) (hDbU : Db ≤ U ^ r) :
    8 ^ (r + 1) * f ^ 2 * Del ^ (3 * c + 6) * NT ^ 2 * (Db * Del * NT) ^ (10000 * (r + 1) ^ 3) ≤ U ^ (250000 * r ^ 4) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : Del ^ (3 * c + 6) ≤ U ^ (18 * r) := by
    calc Del ^ (3 * c + 6) ≤ Del ^ ((18 * r : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hD; push_cast; linarith
      _ = Del ^ (18 * r) := Real.rpow_natCast _ _
      _ ≤ _ := by gcongr
  calc _ ≤ U * U * U ^ (18 * r) * U ^ 2 * (U ^ r * U * U) ^ (10000 * (r + 1) ^ 3) := by gcongr
    _ = U ^ (4 + 18 * r + (r + 2) * (10000 * (r + 1) ^ 3)) := by
        rw [show U ^ r * U * U = U ^ (r + 2) by ring, ← pow_mul, pow_add, pow_add]; ring
    _ ≤ _ := by
        apply pow_le_pow_right₀ hU
        have a1 : (r + 1) ^ 3 ≤ (2 * r) ^ 3 := by gcongr; omega
        have a2 : (r + 2) * (10000 * (r + 1) ^ 3) ≤ (3 * r) * (10000 * (2 * r) ^ 3) := by gcongr; omega
        have a3 : r ≤ r ^ 4 := Nat.le_self_pow (by norm_num) r
        have a4 : (3 * r) * (10000 * (2 * r) ^ 3) = 240000 * r ^ 4 := by ring
        omega

theorem parith_const (r f : ℕ) (hr : 1 ≤ r) (hf : 1 ≤ f) (b w c : ℝ) (hb : 2 ≤ b) (hw : 1 ≤ w) (hwb : w ≤ b)
    (hc : c ≤ 4 * r) (hfb : (f : ℝ) ≤ b ^ (2 * r)) :
    2 + 2 * ((20 * (f : ℝ) * w ^ 2) ^ (2 * (f : ℝ) * (6 + c)) * w ^ f) ≤ (b ^ (r ^ 2 * f)) ^ 183 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hb1 : 1 ≤ b := by linarith
  have h20 : (20 : ℝ) ≤ b ^ 5 := by
    calc (20 : ℝ) ≤ 2 ^ 5 := by norm_num
      _ ≤ b ^ 5 := by gcongr
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw
  have h1 : (20 * (f : ℝ) * w ^ 2) ^ (2 * (f : ℝ) * (6 + c)) ≤ b ^ ((9 * r) * (20 * r * f)) := by
    calc _ ≤ (20 * (f : ℝ) * w ^ 2) ^ ((20 * r * f : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by nlinarith); push_cast; nlinarith
      _ = (20 * (f : ℝ) * w ^ 2) ^ (20 * r * f) := Real.rpow_natCast _ _
      _ ≤ (b ^ 5 * b ^ (2 * r) * b ^ 2) ^ (20 * r * f) := by gcongr
      _ ≤ (b ^ (9 * r)) ^ (20 * r * f) := by
          gcongr
          rw [← pow_add, ← pow_add]
          exact pow_le_pow_right₀ hb1 (by omega)
      _ = _ := by rw [← pow_mul]
  have hn : f ≤ r ^ 2 * f := Nat.le_mul_of_pos_left _ (by positivity)
  set X := b ^ (r ^ 2 * f) with hX
  have hX2 : b ^ f ≤ X := pow_le_pow_right₀ hb1 hn
  have hX3 : 2 ≤ X := le_trans (le_trans hb (le_self_pow₀ hb1 (by omega))) hX2
  have h2 : b ^ ((9 * r) * (20 * r * f)) = X ^ 180 := by rw [hX, ← pow_mul]; congr 1; ring
  have h3 : w ^ f ≤ X := le_trans (by gcongr) hX2
  have h4 : (20 * (f : ℝ) * w ^ 2) ^ (2 * (f : ℝ) * (6 + c)) * w ^ f ≤ X ^ 181 := by
    calc _ ≤ X ^ 180 * X := by rw [← h2]; gcongr
      _ = _ := by ring
  have h5 : 1 ≤ X ^ 181 := one_le_pow₀ (by linarith)
  have h6 : X ^ 183 = X ^ 181 * X ^ 2 := by ring
  have h7 : 4 ≤ X ^ 2 := by nlinarith
  rw [h6]
  nlinarith

theorem parith_pair (K : Type) [Field K] [NumberField K] (k g r T x x' : ℕ) (hr : 1 ≤ r) (A S S' : ℝ) (hA : 1 ≤ A)
    (hS : 1 ≤ S) (hS' : 1 ≤ S') (hx : 1 ≤ x) (hx' : 1 ≤ x') (hxA : (x : ℝ) ≤ A * S ^ 2) (hxA' : (x' : ℝ) ≤ A * S' ^ 2)
    (hT : 1 ≤ T) (hTA : (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K ≤ A) (hc : cf K ≤ 4 * r) (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv K)
    (hsm : (32 / (g : ℝ)) ^ (k * Formalism.HermitianLatticesTheory.fDeg K) * ((4 * k * Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) ^ (4 * Formalism.HermitianLatticesTheory.fDeg K) * A ^ 42 ≤ 1 / 2)
    (hco : 2 + 2 * ((20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (6 + cf K)) *
      (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) ≤ A ^ 183) :
    pairBd K k g r T x x' ≤ ((x : ℝ) * x') ^ ((k : ℝ) / 2) *
      (((A * S ^ 2) * (A * S' ^ 2)) ^ (96 * r + 183) * (S * S') ^ (14 * k)) := by
  unfold pairBd
  simp only []
  generalize Formalism.HermitianLatticesTheory.fDeg K = f at *
  generalize cf K = c at *
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1' : (1 : ℝ) ≤ x' := by exact_mod_cast hx'
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hD1 : (1 : ℝ) ≤ (T : ℝ) ^ (2 * f) := one_le_pow₀ hT1
  have hDA : (T : ℝ) ^ (2 * f) ≤ A ^ 2 := by rw [mul_comm, pow_mul]; gcongr
  generalize (T : ℝ) ^ (2 * f) = D at *
  have hD0 : 0 ≤ D := by linarith
  have hxx : (1 : ℝ) ≤ (x : ℝ) * x' := one_le_mul_of_one_le_of_one_le hx1 hx1'
  have hY1 : (1 : ℝ) ≤ (x : ℝ) * x' * D ^ 2 := one_le_mul_of_one_le_of_one_le hxx (one_le_pow₀ hD1)
  have hYA : (x : ℝ) * x' * D ^ 2 ≤ A ^ 6 * (S * S') ^ 2 := by
    calc _ ≤ (A * S ^ 2) * (A * S' ^ 2) * (A ^ 2) ^ 2 := by gcongr
      _ = _ := by ring
  have hDY : D * x * x' ≤ ((x : ℝ) * x' * D ^ 2) ^ 7 := by
    refine le_trans ?_ (le_self_pow₀ hY1 (by norm_num))
    have : D ≤ D ^ 2 := le_self_pow₀ hD1 (by norm_num)
    calc D * x * x' = x * x' * D := by ring
      _ ≤ _ := by gcongr
  generalize (x : ℝ) * x' * D ^ 2 = Y at *
  have hY0 : 0 ≤ Y := by linarith
  have hv0 : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by linarith
  have hSS : 1 ≤ S * S' := one_le_mul_of_one_le_of_one_le hS hS'
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have hS2' : 1 ≤ S' ^ 2 := one_le_pow₀ hS'
  have hZ : 1 ≤ (S * S') ^ 14 := one_le_pow₀ hSS
  set V := (A * S ^ 2) * (A * S' ^ 2) with hV
  have hVe : V = A ^ 2 * (S * S') ^ 2 := by rw [hV]; ring
  have hSS2 : 1 ≤ (S * S') ^ 2 := one_le_pow₀ hSS
  have hAV : A ≤ V := by
    rw [hVe]
    calc A = A * 1 := by ring
      _ ≤ _ := by gcongr; exact le_self_pow₀ hA (by norm_num)
  have hYV : Y ≤ V ^ 3 := by
    refine le_trans hYA ?_
    rw [hVe, mul_pow (A ^ 2), ← pow_mul]
    gcongr
    exact le_self_pow₀ hSS2 (by norm_num)
  have h1 : Y ^ (6 * (r : ℝ) + 10 + 4 * c) ≤ V ^ (96 * r) := by
    calc _ ≤ Y ^ ((32 * r : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hY1; push_cast; linarith
      _ = Y ^ (32 * r) := Real.rpow_natCast _ _
      _ ≤ (V ^ 3) ^ (32 * r) := by gcongr
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hB := parith_bracket k
    ((20 * (f : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (f : ℝ) * (6 + c)) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ f)
    ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * Y ^ 7)
    ((2 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * D * x * x') ((S * S') ^ 14)
    (by positivity) (by positivity) (by positivity)
    (by
      rw [mul_assoc _ D, mul_assoc _ (D * x)]
      gcongr
      norm_num)
    hZ
    (by
      calc _ ≤ (32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * (A ^ 6 * (S * S') ^ 2) ^ 7 := by gcongr
        _ = ((32 / (g : ℝ)) ^ (k * f) * ((4 * k * f : ℕ) : ℝ) ^ (4 * f) * A ^ 42) * (S * S') ^ 14 := by ring
        _ ≤ _ := by gcongr)
  have hB' := le_trans hB (mul_le_mul_of_nonneg_right (le_trans hco (pow_le_pow_left₀ (by linarith) hAV 183))
    (by positivity))
  have hV0 : 0 ≤ V := by linarith
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc _ ≤ V ^ (96 * r) * (V ^ 183 * ((S * S') ^ 14) ^ k) := mul_le_mul h1 hB' (by positivity) (by positivity)
    _ = _ := by rw [← pow_mul, pow_add V, ← mul_assoc]

theorem parith_cancel (x x' Del Del' e : ℝ) (hx : 0 < x) (hx' : 0 < x') (hD : 0 ≤ Del) (hD' : 0 ≤ Del') :
    (x * x') ^ e * ((Del / x) ^ e * (Del' / x') ^ e) = Del ^ e * Del' ^ e := by
  rw [Real.mul_rpow hx.le hx'.le, Real.div_rpow hD hx.le, Real.div_rpow hD' hx'.le]
  have := Real.rpow_pos_of_pos hx e
  have := Real.rpow_pos_of_pos hx' e
  field_simp

theorem parith_sum (K : Type) [Field K] [NumberField K] [StarRing K] (k g r T : ℕ) (hr : 1 ≤ r) (A S S' Del Del' Db Db' : ℝ)
    (hA : 1 ≤ A) (hS : 1 ≤ S) (hS' : 1 ≤ S') (hD : 1 ≤ Del) (hD' : 1 ≤ Del') (hDb : 1 ≤ Db) (hDb' : 1 ≤ Db')
    (hDA : Del ≤ A * S ^ 2) (hDA' : Del' ≤ A * S' ^ 2) (hDbA : Db ≤ (A * S ^ 2) ^ r) (hDbA' : Db' ≤ (A * S' ^ 2) ^ r)
    (hT : 1 ≤ T) (hTA : (T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K ≤ A) (hc : cf K ≤ 4 * r) (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv K)
    (h8 : 8 ^ (r + 1) ≤ A) (hf : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ^ 2 ≤ A)
    (hsm : (32 / (g : ℝ)) ^ (k * Formalism.HermitianLatticesTheory.fDeg K) * ((4 * k * Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) ^ (4 * Formalism.HermitianLatticesTheory.fDeg K) * A ^ 42 ≤ 1 / 2)
    (hco : 2 + 2 * ((20 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv K) ^ 2) ^ (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * (6 + cf K)) *
      (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) ≤ A ^ 183) :
    ∑ x ∈ Finset.Icc 1 ⌊Del⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊Del'⌋₊, pairBd K k g r T x x' *
      (datBd K k r Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x * datBd K k r Del' Db' ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x') ≤
      (Del ^ ((k : ℝ) / 2) * (A * S ^ 2) ^ (300000 * r ^ 4) * S ^ (14 * k)) *
        (Del' ^ ((k : ℝ) / 2) * (A * S' ^ 2) ^ (300000 * r ^ 4) * S' ^ (14 * k)) := by
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have hS2' : 1 ≤ S' ^ 2 := one_le_pow₀ hS'
  have hAU : A ≤ A * S ^ 2 := le_mul_of_one_le_right (by linarith) hS2
  have hAU' : A ≤ A * S' ^ 2 := le_mul_of_one_le_right (by linarith) hS2'
  have hR := parith_rest r hr (cf K) (Formalism.HermitianLatticesTheory.fDeg K) Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) (A * S ^ 2) hc (by linarith)
    (by linarith) (by linarith) hD hDA (by positivity) (by linarith) (by linarith) hDbA
  have hR' := parith_rest r hr (cf K) (Formalism.HermitianLatticesTheory.fDeg K) Del' Db' ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) (A * S' ^ 2) hc (by linarith)
    (by linarith) (by linarith) hD' hDA' (by positivity) (by linarith) (by linarith) hDbA'
  have hfl : (⌊Del⌋₊ : ℝ) ≤ A * S ^ 2 := le_trans (Nat.floor_le (by linarith)) hDA
  have hfl' : (⌊Del'⌋₊ : ℝ) ≤ A * S' ^ 2 := le_trans (Nat.floor_le (by linarith)) hDA'
  set U := A * S ^ 2 with hU
  set U' := A * S' ^ 2 with hU'
  have hU1 : 1 ≤ U := by linarith
  have hU1' : 1 ≤ U' := by linarith
  have hD0 : 0 ≤ Del := by linarith
  have hD0' : 0 ≤ Del' := by linarith
  set C := (Del ^ ((k : ℝ) / 2) * Del' ^ ((k : ℝ) / 2)) *
    ((U * U') ^ (96 * r + 183) * (S * S') ^ (14 * k) * (U ^ (250000 * r ^ 4) * U' ^ (250000 * r ^ 4))) with hC
  have hC0 : 0 ≤ C := by positivity
  have hterm : ∀ x ∈ Finset.Icc 1 ⌊Del⌋₊, ∀ x' ∈ Finset.Icc 1 ⌊Del'⌋₊, pairBd K k g r T x x' *
      (datBd K k r Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x * datBd K k r Del' Db' ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x') ≤ C := by
    intro x hx x' hx'
    obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.1 hx
    obtain ⟨hx1', hx2'⟩ := Finset.mem_Icc.1 hx'
    have hxU : (x : ℝ) ≤ U := le_trans (by exact_mod_cast hx2) hfl
    have hxU' : (x' : ℝ) ≤ U' := le_trans (by exact_mod_cast hx2') hfl'
    have hP := parith_pair K k g r T x x' hr A S S' hA hS hS' hx1 hx1' hxU hxU' hT hTA hc hv hsm hco
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    have hx0' : (0 : ℝ) < x' := by exact_mod_cast hx1'
    rw [hC, ← parith_cancel x x' Del Del' _ hx0 hx0' hD0 hD0']
    unfold datBd
    calc _ ≤ (((x : ℝ) * x') ^ ((k : ℝ) / 2) * ((U * U') ^ (96 * r + 183) * (S * S') ^ (14 * k))) *
          (((Del / x) ^ ((k : ℝ) / 2) * U ^ (250000 * r ^ 4)) * ((Del' / x') ^ ((k : ℝ) / 2) * U' ^ (250000 * r ^ 4))) := by
          gcongr
      _ = _ := by ring
  calc _ ≤ ∑ x ∈ Finset.Icc 1 ⌊Del⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊Del'⌋₊, C :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun x' hx' => hterm x hx x' hx'
    _ = (⌊Del⌋₊ : ℝ) * (⌊Del'⌋₊ * C) := by simp
    _ ≤ U * (U' * C) := by gcongr
    _ = (Del ^ ((k : ℝ) / 2) * U ^ (1 + (96 * r + 183) + 250000 * r ^ 4) * S ^ (14 * k)) *
        (Del' ^ ((k : ℝ) / 2) * U' ^ (1 + (96 * r + 183) + 250000 * r ^ 4) * S' ^ (14 * k)) := by
        rw [hC, pow_add U, pow_add U, pow_add U', pow_add U', mul_pow U, mul_pow S, pow_one, pow_one]
        generalize U ^ (96 * r + 183) = a1
        generalize U' ^ (96 * r + 183) = a2
        generalize U ^ (250000 * r ^ 4) = a3
        generalize U' ^ (250000 * r ^ 4) = a4
        generalize S ^ (14 * k) = a5
        generalize S' ^ (14 * k) = a6
        ring
    _ ≤ _ := by
        have a3 : r ≤ r ^ 4 := Nat.le_self_pow (by norm_num) r
        have : 1 + (96 * r + 183) + 250000 * r ^ 4 ≤ 300000 * r ^ 4 := by omega
        gcongr

theorem parith_abs (k r : ℕ) (A B S Ch : ℝ) (hA : 1 ≤ A) (hAB : A ≤ B) (hS : 1 ≤ S) (hCh : 300000 ≤ Ch)
    (hk : 300000 * r ^ 4 ≤ k) (E : ℝ) (hE : 0 ≤ E) :
    E * (A * S ^ 2) ^ (300000 * r ^ 4) * S ^ (14 * k) ≤ E * B ^ (Ch * (r : ℝ) ^ 4) * S ^ (16 * (k : ℝ)) := by
  have h1 : A ^ (300000 * r ^ 4) ≤ B ^ (Ch * (r : ℝ) ^ 4) := by
    calc _ ≤ B ^ (300000 * r ^ 4) := by gcongr
      _ = B ^ ((300000 * r ^ 4 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith); push_cast; gcongr
  have h2 : (S ^ 2) ^ (300000 * r ^ 4) * S ^ (14 * k) ≤ S ^ (16 * (k : ℝ)) := by
    rw [← pow_mul, ← pow_add, show (16 * (k : ℝ)) = ((16 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact pow_le_pow_right₀ hS (by omega)
  have hB : 0 ≤ B := by linarith
  rw [mul_pow, mul_assoc, mul_assoc, mul_assoc]
  gcongr


set_option maxHeartbeats 1600000 in
theorem sum_pairBd_mul_datBd_le : ∀ Ca : ℝ, 1 ≤ Ca → ∃ Ch Cl : ℝ, 0 ≤ Ch ∧ ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (k r m g T : ℕ) (b Del Del' Db Db' S S' : ℝ), Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K → m = 2 * r + 2 → Cl ≤ m → m ^ 4 ≤ Formalism.HermitianLatticesTheory.fDeg K → m ^ 5 * Formalism.HermitianLatticesTheory.fDeg K ≤ k → Cl * ((m : ℝ) ^ 2 * Real.log b) ≤ k → Real.log (Formalism.HermitianLatticesTheory.fDeg K) ≤ Real.sqrt r → 2 ≤ b → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → 2 * Formalism.HermitianLatticesTheory.vInv K ≤ b → ((k : ℝ) * b) ^ 8 ≤ g → 1 ≤ T → (T : ℝ) ≤ b ^ (Ca * m) → 1 ≤ S → 1 ≤ S' → 1 ≤ Del → 1 ≤ Del' → 1 ≤ Db → 1 ≤ Db' → Del ≤ b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) * S ^ 2 → Del' ≤ b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) * S' ^ 2 → Db ≤ (b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) * S ^ 2) ^ r → Db' ≤ (b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) * S' ^ 2) ^ r → ∑ x ∈ Finset.Icc 1 ⌊Del⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊Del'⌋₊, pairBd K k g r T x x' * (datBd K k r Del Db ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x * datBd K k r Del' Db' ((T : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K) x') ≤ (Del ^ ((k : ℝ) / 2) * (b ^ (Ch * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K)) ^ (Ch * (r : ℝ) ^ 4) * S ^ (16 * (k : ℝ))) * (Del' ^ ((k : ℝ) / 2) * (b ^ (Ch * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K)) ^ (Ch * (r : ℝ) ^ 4) * S' ^ (16 * (k : ℝ))) := by
  intro Ca hCa
  refine ⟨300000 * Ca, 42 * Ca, by linarith, ?_⟩
  intro K _ _ _ k r m g T b Del Del' Db Db' S S' hfin hm hCm hmf hmk hCk hlog hb hv hvb hg hT hTb hS hS' hD hD' hDb hDb'
    hDA hDA' hDbA hDbA'
  have hm42 : 42 ≤ m := by
    have : (42 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hr : 1 ≤ r := by omega
  have hrm : r ≤ m := by omega
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm5 : 42 ^ 5 ≤ m ^ 5 := by gcongr
  have hm4 : 42 ^ 4 ≤ m ^ 4 := by gcongr
  have hr4 : r ^ 4 ≤ m ^ 4 := by gcongr
  have hc : cf K ≤ 4 * r := by
    have hf0 : (0 : ℝ) < Formalism.HermitianLatticesTheory.fDeg K := by exact_mod_cast (by omega : 0 < Formalism.HermitianLatticesTheory.fDeg K)
    unfold cf
    rw [hfin]
    push_cast
    rw [Real.logb_mul (by norm_num) hf0.ne', Real.logb_self_eq_one (by norm_num), Real.logb]
    have h2 := Real.log_two_gt_d9
    have hs : Real.sqrt r ≤ r := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have : Real.log (Formalism.HermitianLatticesTheory.fDeg K) / Real.log 2 ≤ 2 * r := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  obtain ⟨f, hfdef⟩ : ∃ f, f = Formalism.HermitianLatticesTheory.fDeg K := ⟨_, rfl⟩
  rw [← hfdef] at hmf hmk hlog hDA hDA' hDbA hDbA'
  have hf1 : 1 ≤ f := by omega
  have hf1' : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  have hm1' : (1 : ℝ) ≤ m := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hk1 : 42 ^ 5 * f ≤ k := le_trans (by gcongr) hmk
  have hfb : (f : ℝ) ≤ b ^ (2 * r) := by
    have hs : Real.sqrt r ≤ r := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
    calc (f : ℝ) = Real.exp (Real.log f) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (r * 1) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp 1 ^ r := Real.exp_nat_mul _ _
      _ ≤ (b ^ 2) ^ r := by
        gcongr
        have := Real.exp_one_lt_d9
        nlinarith
      _ = _ := by rw [← pow_mul]
  have hpow : ∀ n : ℕ, n ≤ m ^ 2 * f → b ^ n ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by
    intro n hn
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb1
    have h1 : (n : ℝ) ≤ (m : ℝ) ^ 2 * f := by exact_mod_cast hn
    have h2 : (0 : ℝ) ≤ (m : ℝ) ^ 2 * f := by positivity
    nlinarith
  have hmf2 : m ^ 2 ≤ m ^ 2 * f := Nat.le_mul_of_pos_right _ hf1
  have hmm : 42 * m ≤ m ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right m hm42
  have hA : 1 ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by simpa using hpow 0 (by omega)
  have hTA : (T : ℝ) ^ f ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by
    calc (T : ℝ) ^ f ≤ (b ^ (Ca * m)) ^ f := by gcongr
      _ = b ^ (Ca * m * f) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb1
        gcongr
        exact le_self_pow₀ hm1' (by norm_num)
  have h8 : (8 : ℝ) ^ (r + 1) ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by
    refine le_trans ?_ (hpow (3 * (r + 1)) (by omega))
    rw [pow_mul]
    gcongr
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ b ^ 3 := by gcongr
  have hf2 : (f : ℝ) ^ 2 ≤ b ^ (Ca * (m : ℝ) ^ 2 * f) := by
    refine le_trans ?_ (hpow (2 * r * 2) (by omega))
    rw [pow_mul]
    gcongr
  have hsm := parith_small k f g b (Ca * (m : ℝ) ^ 2) hb (by omega) hf1 (by omega) (by linarith) hg
  have hco := le_trans (parith_const r f hr hf1 b (2 * Formalism.HermitianLatticesTheory.vInv K) (cf K) hb (by linarith) hvb hc hfb)
    (pow_le_pow_left₀ (by positivity) (hpow (r ^ 2 * f) (by gcongr)) 183)
  subst hfdef
  refine le_trans (parith_sum K k g r T hr _ S S' Del Del' Db Db' hA hS hS' hD hD' hDb hDb' hDA hDA' hDbA hDbA' hT hTA hc hv
    h8 hf2 hsm hco) ?_
  have hAB : b ^ (Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) ≤ b ^ (300000 * Ca * (m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg K) := by
    apply Real.rpow_le_rpow_of_exponent_le hb1
    gcongr
    linarith
  have hkr : 300000 * r ^ 4 ≤ k := by omega
  have hD0 : 0 ≤ Del := by linarith
  have hD0' : 0 ≤ Del' := by linarith
  exact mul_le_mul
    (parith_abs k r _ _ S _ hA hAB hS (by linarith) hkr _ (by positivity))
    (parith_abs k r _ _ S' _ hA hAB hS' (by linarith) hkr _ (by positivity)) (by positivity) (by positivity)

end GlobalTheory.DegAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometricEmbeddedDatumPairsEncardIsometrySmul
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometricEmbeddedDatumPairsEncardIsometrySmul
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.TripInv

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

abbrev lin (s : V ≃ₗ[K] V) : V →ₗ[𝓞 K] V := (s : V →ₗ[K] V).restrictScalars (𝓞 K)

def pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) : Submodule (𝓞 K) (V × V) :=
  Γ.map ((lin s).prodMap (lin s))

theorem gmap_eq (s : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap s M = M.map (lin s) := rfl

theorem mem_gmap (s : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) :
    y ∈ Formalism.HermitianLatticesTheory.gmap s M ↔ s.symm y ∈ M := by
  rw [gmap_eq, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨s.symm y, h, by simp⟩

theorem mem_pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) (p : V × V) :
    p ∈ pmap s Γ ↔ (s.symm p.1, s.symm p.2) ∈ Γ := by
  rw [pmap, Submodule.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro h
    exact ⟨_, h, by ext <;> simp⟩

theorem gmap_injective (s : V ≃ₗ[K] V) : Function.Injective (Formalism.HermitianLatticesTheory.gmap (R := 𝓞 K) s) := by
  intro M M' h
  ext x
  have := congrArg (s x ∈ ·) h
  simpa [mem_gmap] using this

theorem pmap_injective (s : V ≃ₗ[K] V) : Function.Injective (pmap s) := by
  intro Γ Γ' h
  ext p
  have := congrArg ((s p.1, s p.2) ∈ ·) h
  simpa [mem_pmap] using this

theorem smulLat_gmap (s : V ≃ₗ[K] V) (g : 𝓞 K) (M : Submodule (𝓞 K) V) :
    smulLat g (Formalism.HermitianLatticesTheory.gmap s M) = Formalism.HermitianLatticesTheory.gmap s (smulLat g M) := by
  rw [gmap_eq, gmap_eq, smulLat, smulLat, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  rw [← algebraMap_smul K g x, ← algebraMap_smul K g (s x), map_smul]

theorem prod_gmap (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    (Formalism.HermitianLatticesTheory.gmap s A).prod (Formalism.HermitianLatticesTheory.gmap s B) = pmap s (A.prod B) := by
  ext p
  simp [mem_pmap, mem_gmap, Submodule.mem_prod]

theorem fixLat_pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) :
    fixLat (pmap s Γ) = Formalism.HermitianLatticesTheory.gmap s (fixLat Γ) := by
  ext x
  simp [fixLat, mem_pmap, mem_gmap]

theorem toAddSubgroup_gmap (s : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    (Formalism.HermitianLatticesTheory.gmap s M).toAddSubgroup = M.toAddSubgroup.map (lin s).toAddMonoidHom := by
  ext x
  rfl

theorem idx_gmap (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    idx (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) = idx A B := by
  unfold idx
  rw [toAddSubgroup_gmap, toAddSubgroup_gmap]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (by simpa using s.injective)

theorem idxN_gmap (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    GlobalTheory.Mass.idxN (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) = GlobalTheory.Mass.idxN A B :=
  idx_gmap s A B

variable {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V}

theorem isom_symm {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (x y : V) :
    H.B (s.symm x) (s.symm y) = H.B x y := by
  rw [← hs]
  simp

theorem dual_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.dual H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) = Formalism.HermitianLatticesTheory.gmap s (Formalism.HermitianLatticesTheory.dual H.B.flip M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, mem_gmap,
    LinearMap.restrictScalars_apply, LinearMap.flip_apply]
  constructor
  · intro h z hz
    have := h (s z) (by simpa using hz)
    rwa [← isom_symm hs, LinearEquiv.symm_apply_apply] at this
  · intro h y hy
    have := h _ hy
    rwa [isom_symm hs] at this

theorem isIntLat_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {M : Submodule (𝓞 K) V}
    (hM : GlobalTheory.Mass.IsIntLat H.B.flip M) : GlobalTheory.Mass.IsIntLat H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) := by
  obtain ⟨hL, hI⟩ := hM
  have hfull : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap s M) := by
    rw [gmap_eq]
    haveI : Submodule.IsLattice K (M.map (lin s)) :=
      Submodule.IsLattice.of_fg K (hL.fg.map _)
    refine ⟨?_⟩
    change Submodule.span K ((s : V →ₗ[K] V) '' (M : Set V)) = ⊤
    rw [← Submodule.map_span, hL.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.2 s.surjective]
  refine ⟨hfull, ?_⟩
  · intro x hx y hy
    rw [mem_gmap] at hx hy
    have := hI _ hx _ hy
    simp only [LinearMap.flip_apply] at this ⊢
    rwa [isom_symm hs] at this

theorem discN_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (M : Submodule (𝓞 K) V) :
    GlobalTheory.Mass.discN H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) = GlobalTheory.Mass.discN H.B.flip M := by
  unfold GlobalTheory.Mass.discN
  rw [dual_gmap hs, idxN_gmap]

theorem genBy_gmap (s : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} {j : ℕ} (h : GenBy A B j) :
    GenBy (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) j := by
  classical
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨t.image s, (Finset.card_image_le).trans ht, ?_⟩
  rw [gmap_eq, gmap_eq, Submodule.map_sup, Submodule.map_span, Finset.coe_image]
  rfl

theorem isModIso_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {g : 𝓞 K}
    {M L : Submodule (𝓞 K) V} {Γ : Submodule (𝓞 K) (V × V)} (h : IsModIso H g M L Γ) :
    IsModIso H g (Formalism.HermitianLatticesTheory.gmap s M) (Formalism.HermitianLatticesTheory.gmap s L) (pmap s Γ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prod_gmap]
    exact Submodule.map_mono h1
  · rw [smulLat_gmap, smulLat_gmap, prod_gmap]
    exact Submodule.map_mono h2
  · intro y' hy'
    rw [mem_gmap] at hy'
    obtain ⟨y, hy⟩ := h3 _ hy'
    exact ⟨s y, by simpa [mem_pmap] using hy⟩
  · intro y hy
    rw [mem_gmap] at hy
    obtain ⟨y', hy'⟩ := h4 _ hy
    exact ⟨s y', by simpa [mem_pmap] using hy'⟩
  · intro y hy
    rw [mem_pmap] at hy
    rw [smulLat_gmap, mem_gmap]
    exact h5 _ (by simpa using hy)
  · intro y' hy'
    rw [mem_pmap] at hy'
    rw [smulLat_gmap, mem_gmap]
    exact h6 _ (by simpa using hy')
  · intro p hp q hq
    rw [mem_pmap] at hp hq
    obtain ⟨t, ht⟩ := h7 _ hp _ hq
    exact ⟨t, by simpa only [isom_symm hs] using ht⟩

theorem isDat_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {g : ℕ} {L : Submodule (𝓞 K) V}
    {j x : ℕ} {d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)} (h : IsDat H g L j x d) :
    IsDat H g (Formalism.HermitianLatticesTheory.gmap s L) j x (Formalism.HermitianLatticesTheory.gmap s d.1, pmap s d.2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨isIntLat_gmap hs h1, ?_, isModIso_gmap hs h3, ?_, ?_⟩
  · rw [discN_gmap hs, discN_gmap hs, h2]
  · rw [fixLat_pmap, idx_gmap, h4]
  · rw [fixLat_pmap]
    exact genBy_gmap s h5

def tr (s : V ≃ₗ[K] V)
    (p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V)) :
    (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) :=
  ((Formalism.HermitianLatticesTheory.gmap s p.1.1, pmap s p.1.2), (Formalism.HermitianLatticesTheory.gmap s p.2.1.1, pmap s p.2.1.2), s * p.2.2 * s⁻¹)

theorem tr_injective (s : V ≃ₗ[K] V) : Function.Injective (tr (K := K) s) := by
  rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, η⟩ ⟨⟨a1', a2'⟩, ⟨b1', b2'⟩, η'⟩ h
  simp only [tr, Prod.mk.injEq] at h
  obtain ⟨⟨e1, e2⟩, ⟨e3, e4⟩, e5⟩ := h
  simp only [gmap_injective s e1, pmap_injective s e2, gmap_injective s e3, pmap_injective s e4,
    mul_left_cancel (mul_right_cancel e5)]

theorem tr_mapsTo {s : V ≃ₗ[K] V} (hs : s ∈ isomGrp H) (g : ℕ) (L : Submodule (𝓞 K) V) (j x x' : ℕ) :
    Set.MapsTo (tr s) (Trip H g L j x x') (Trip H g (Formalism.HermitianLatticesTheory.gmap s L) j x x') := by
  have hs' := (mem_isomGrp H s).1 hs
  rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, η⟩ ⟨hA, hB, hη, him, hgr⟩
  refine ⟨isDat_gmap hs' hA, isDat_gmap hs' hB, ?_, ?_, ?_⟩
  · exact (isomGrp H).mul_mem ((isomGrp H).mul_mem hs hη) ((isomGrp H).inv_mem hs)
  · change Formalism.HermitianLatticesTheory.gmap (s * η * s⁻¹) (Formalism.HermitianLatticesTheory.gmap s b1) = Formalism.HermitianLatticesTheory.gmap s a1
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv, Formalism.HermitianLatticesTheory.genusBasic_gmap_mul]
    exact congrArg _ him
  · intro y y'
    change (y, y') ∈ pmap s b2 ↔ (s (η (s.symm y)), y') ∈ pmap s a2
    rw [mem_pmap, mem_pmap]
    simpa using hgr (s.symm y) (s.symm y')

theorem encard_le (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (L : Submodule (𝓞 K) V) :
    (Trip HW g L j x x').encard ≤ (Trip HW g (s • L) j x x').encard :=
  Set.encard_le_encard_of_injOn (tr_mapsTo s.2 g L j x x') (tr_injective _).injOn

theorem trip_encard_smul : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip)
    (L : Submodule (𝓞 K) W), (Trip HW g (s • L) j x x').encard = (Trip HW g L j x x').encard := by
  intro K W _ _ _ _ _ _ _ HW g j x x' s L
  refine le_antisymm ?_ (encard_le HW g j x x' s L)
  have := encard_le HW g j x x' s⁻¹ (s • L)
  exact this.trans_eq (congrArg (fun M => (Trip HW g M j x x').encard)
    (Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (s : W ≃ₗ[K] W) L))

end GlobalTheory.TripInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometricEmbeddedDatumPairsEncardIsometrySmulStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometricEmbeddedDatumPairs_encard_isometry_smul : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : Formalism.HermitianLatticeCounting.S6.HermSpace K W) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (L : Submodule (𝓞 K) W), (Trip HW g (s • L) j x x').encard = (Trip HW g L j x x').encard := by
  first | exact @GlobalTheory.TripInv.trip_encard_smul | exact GlobalTheory.TripInv.trip_encard_smul | (intros; apply GlobalTheory.TripInv.trip_encard_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatios
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PairsPf

theorem massC_nonneg {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : 0 ≤ massC Y u := by
  show 0 ≤ ∑ Λ ∈ Y.what₂ u, wRow D (X.Fu u) Λ
  exact Finset.sum_nonneg fun Λ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem datBd_nonneg (K : Type) [Field K] [NumberField K] [StarRing K] (k r : ℕ) (Del Db NT x : ℝ) (hD : 0 ≤ Del)
    (hDb : 0 ≤ Db) (hN : 0 ≤ NT) (hx : 0 ≤ x) : 0 ≤ GlobalTheory.DegAsm.datBd K k r Del Db NT x := by
  unfold GlobalTheory.DegAsm.datBd
  positivity

theorem termPairBoundFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Ch Cp : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2e large₂ CH Ch Cp j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have h1 : 0 ≤ k2Del D j δ := Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have h2 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := Real.rpow_nonneg hb.le _
  have h3 : 0 ≤ k2S D (H1C large₂ CH) j δ := by
    unfold k2S k2sg
    exact Finset.prod_nonneg fun τ _ => le_trans zero_le_one ((Finset.le_fold_max 1).2 (Or.inl le_rfl))
  unfold k2e
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)) (Real.rpow_nonneg h3 _)
private lemma le_mul_sum_sum_of_ofReal_le_ennreal_sum (s s' : Finset ℕ) (f P : ℕ → ℕ → ℝ) (c L : ℝ) (hf : ∀ x x', 0 ≤ f x x')
    (hP : ∀ x x', 0 ≤ P x x') (hc : 0 ≤ c)
    (h : ENNReal.ofReal L ≤ ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x')) :
    L ≤ c * ∑ x ∈ s, ∑ x' ∈ s', P x x' * f x x' := by
  have hnn : ∀ x x', 0 ≤ f x x' * (c * P x x') := fun x x' => mul_nonneg (hf x x') (mul_nonneg hc (hP x x'))
  have e : ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x') =
      ENNReal.ofReal (∑ x ∈ s, ∑ x' ∈ s', f x x' * (c * P x x')) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [ENNReal.ofReal_mul (hf x x')]
  rw [e] at h
  have h' := (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')).1 h
  refine le_trans h' (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

end PairsPf

open PairsPf in
theorem pair_count_bound_of_siegel_mass : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → PairsP := by
  intro hMM hSR
  unfold PairsP
  intro Cg cb Cw cT CT C0 CH hCH

  obtain ⟨Ca, hCa1, hCaH, hCaT⟩ : ∃ Ca : ℝ, 1 ≤ Ca ∧ 2 * (CH + 1) ≤ Ca ∧ CT ≤ Ca :=
    ⟨max 1 (max (2 * (CH + 1)) CT), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨Ch, Cl', hCh, hsum⟩ := GlobalTheory.DegAsm.sum_pairBd_mul_datBd_le Ca hCa1
  refine ⟨Ch, 16, hCh, by norm_num, 1, max 1 Cl', ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hK2 _
  have hStd : GlobalTheory.TypeAsm.Std D large₂ :=
    show ∃ C' Cl Cg cb Cw cT CT C0 : ℝ, Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 from
      ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK2⟩
  have hHost : HostC := GlobalTheory.T.unitaryHostFieldArithmeticConditions
  have hfD : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := (hHost D large₂ hStd).2.2.2.2.1
  have hCl1 : 1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hClCl : Cl' ≤ Cl := le_trans (le_max_right _ _) hCl
  obtain ⟨hrk, hm, hClm, hm4, hm5, hClk, hlog, hb2, hv1, hvb, hg, hTu⟩ :=
    GlobalTheory.T.parameter_size_constraints Ca Cg cb Cw cT CT C0 C' Cl D large₂ hHost hK2 hC' hCl1 hCaT
  have hlb : 0 ≤ (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hClm' : Cl' ≤ (D.R.m : ℝ) := le_trans hClCl hClm
  have hClk' : Cl' * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k :=
    le_trans (mul_le_mul_of_nonneg_right hClCl hlb) hClk

  have hHb : Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f ≤
      large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E) := by
    show large₂.sc.b ^ (2 * (CH + 1) * (D.R.m : ℝ) ^ 2 * D.R.f) ≤ _
    rw [hfD]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr)
  have hHb0 : 0 ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := Real.rpow_nonneg (by linarith) _
  have hNT : NT D u = ((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E := by
    rw [hfD]
    rfl
  have hNT0 : 0 ≤ NT D u := by
    rw [hNT]
    positivity
  have hk2e : ∀ (j : ℕ) (δ : ℕ → D.host.E), k2e large₂ CH Ch 16 j δ =
      k2Del D j δ ^ ((D.R.k : ℝ) / 2) * (large₂.sc.b ^ (Ch * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E)) ^ (Ch * (D.R.rS : ℝ) ^ 4) *
        k2S D (H1C large₂ CH) j δ ^ (16 * (D.R.k : ℝ)) := by
    intro j δ
    rw [hfD]
    rfl
  unfold PairsAt
  intro j' _ j'' _ δ' δ'' S hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [Finset.sum_empty]
    exact mul_nonneg (massC_nonneg Y u) (mul_nonneg (termPairBoundFactor_nonneg large₂ CH Ch 16 j' δ') (termPairBoundFactor_nonneg large₂ CH Ch 16 j'' δ''))
  obtain ⟨hpp, hj1, hj2, hl1, hl2⟩ := hS p hp
  obtain ⟨hr1, hr2, -⟩ := hpp
  have hF := GlobalTheory.T.relevantTerm_norms_ge_one_and_bounded Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost GlobalTheory.T.exists_adaptedNormalForm_relevantTerm GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label GlobalTheory.T.rowLattice_term_adaptedNormalForm hK2
  obtain ⟨hD1, hDb1, hDle, hDble⟩ := hF p.1 hr1
  obtain ⟨hD1', hDb1', hDle', hDble'⟩ := hF p.2 hr2
  rw [hj1, hl1] at hD1 hDb1 hDle hDble
  rw [hj2, hl2] at hD1' hDb1' hDle' hDble'
  have hS1 : 1 ≤ k2S D (H1C large₂ CH) j' δ' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))
  have hS1' : 1 ≤ k2S D (H1C large₂ CH) j'' δ'' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))

  have hDA := le_trans hDle (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDA' := le_trans hDle' (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDbA := le_trans hDble (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hDbA' := le_trans hDble' (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hbound := hsum D.host.E D.R.k D.R.rS D.R.m (gS D) (Tu D u) large₂.sc.b (k2Del D j' δ') (k2Del D j'' δ'')
    (DbL D j' δ') (DbL D j'' δ'') (k2S D (H1C large₂ CH) j' δ') (k2S D (H1C large₂ CH) j'' δ'') hrk hm hClm' hm4 hm5 hClk'
    hlog hb2 hv1 hvb hg (hTu u).1 (hTu u).2 hS1 hS1' hD1 hD1' hDb1 hDb1' hDA hDA' hDbA hDbA'

  obtain ⟨W, HW, hemb, hrkW, hPD⟩ := GlobalTheory.T.definite_quotient_model_exists D large₂ X u hStd
  have hI := GlobalTheory.T.weightedTermPairs_sum_le_via_rows_genusMeans D large₂ X Y u hStd GlobalTheory.T.termsOverRow_compatible GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings GlobalTheory.T.rowsMeanC_holds W HW hemb
    (fun s M x x' => GlobalTheory.T.isometricEmbeddedDatumPairs_encard_isometry_smul _ _ HW (gS D) D.R.rS x x' s M)
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x')
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _)
    (fun Λ hΛ x x' hx hx' => GlobalTheory.T.genusMean_embeddedPairs_le_mass_mul_pairBound hMM hSR hHost GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hStd W HW hemb hrkW hPD Λ hΛ x x' hx hx')
    j' j'' δ' δ'' S hS
  rw [hNT] at hI
  have hstep := le_mul_sum_sum_of_ofReal_le_ennreal_sum _ _
    (fun x x' => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x *
      GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x')
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') (massC Y u) _
    (fun x x' => mul_nonneg (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _))
      (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _)))
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _) (massC_nonneg Y u) hI
  refine le_trans hstep ?_
  rw [hk2e, hk2e]
  exact mul_le_mul_of_nonneg_left hbound (massC_nonneg Y u)

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatiosStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termPairCountBound_of_siegelMassRatios : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.TypeAsm.PairsP := by
  first | exact @GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass | exact GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass | (intros; apply GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass <;> assumption)
end
