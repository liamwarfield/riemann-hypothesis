module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneSubPowLe

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightProductGermIndep
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem std_Px (S : C.HidaSetting E Wp Wq) (s : ℕ) (hs : 2 ≤ s) (h : C.LPt) (hsz : D.ptSize h + s = S.G.r + 1)
    (t c : ℂ) : PBL.stdS S (h ++ [(s - 1, t), (1, c)]) = PBL.stdS S h ++ [(s - 1, lam1 S s * t), (1, c)] := by
  unfold PBL.stdS
  have e : h ++ [(s - 1, t), (1, c)] = (h ++ [(s - 1, t)]) ++ [(1, c)] := by simp
  rw [e, PBL.toStd_append_blkT, PBL.toStd_append_blkT]
  have hsz2 : D.ptSize (h ++ [(s - 1, t)]) = S.G.r := by
    rw [PBJ.Asm.ptSize_append, PBJ.Asm.ptSize_single]; omega
  have n1 : S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) ((s - 1 : ℕ) : ℤ) = (s : ℤ) := by
    unfold S6.nuBlock; push_cast [Nat.cast_sub (by omega : 1 ≤ s)]; omega
  have n2 : S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize (h ++ [(s - 1, t)]) : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
    rw [hsz2]; unfold S6.nuBlock; push_cast; ring
  rw [n1, n2]
  simp only [List.append_assoc, List.singleton_append, zpow_zero, Complex.ofReal_one, one_mul, Nat.sub_self,
    pow_zero, zpow_natCast, lam1]
  congr 3

theorem std_Qz (S : C.HidaSetting E Wp Wq) (s : ℕ) (hs : 2 ≤ s) (h : C.LPt) (hsz : D.ptSize h + s = S.G.r + 1)
    (z : ℂ) : PBL.stdS S (h ++ [(s, z)]) = PBL.stdS S h ++ [(s, lam2 S s * z)] := by
  unfold PBL.stdS
  rw [PBL.toStd_append_blkT]
  have n1 : S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) (s : ℤ) = ((s - 1 : ℕ) : ℤ) := by
    unfold S6.nuBlock; push_cast [Nat.cast_sub (by omega : 1 ≤ s)]; omega
  rw [n1, zpow_natCast]
  simp only [lam2]

section copied

theorem weight_product_append (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) :
    ∀ (b : ℕ) (P Q : C.LPt), C.nAux k r GG fr b (P ++ Q) = C.nAux k r GG fr b P * C.nAux k r GG fr (b + D.ptSize P) Q
  | b, [], Q => by simp [C.nAux, D.ptSize]
  | b, (s, t) :: rest, Q => by
    simp only [List.cons_append, C.nAux]
    rw [weight_product_append k r GG fr (b + s) rest Q, ← mul_assoc]
    simp only [D.ptSize, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem weight_product_germ_indep (k r : ℕ) (GG GG' : ℝ) (fr : ℕ → ℕ → ℝ) :
    ∀ (b : ℕ) (P : C.LPt), b + D.ptSize P ≤ r + 1 → C.nAux k r GG fr b P = C.nAux k r GG' fr b P
  | b, [], _ => by simp [C.nAux]
  | b, (s, t) :: rest, h => by
    simp only [C.nAux]
    have hrest : b + s + D.ptSize rest ≤ r + 1 := by
      simpa only [D.ptSize, List.map_cons, List.sum_cons, Nat.add_assoc] using h
    have hc : ¬ (b + s - 1 = r + 1 ∧ s = 1) := by omega
    simp only [ite_eq_right hc, weight_product_germ_indep k r GG GG' fr (b + s) rest hrest]

theorem bSt_append (κ : ℝ) (P Q : C.LPt) : D.bSt κ (P ++ Q) = D.bSt κ P * D.bSt κ Q := by
  simp [D.bSt, List.map_append, List.prod_append]

def betaZ (κ : ℝ) (N : ℤ) : ℝ := ∏ x ∈ Finset.Ico 1 N, (κ ^ (1 - 2 * x) / Real.pi) ^ (N - x)

theorem bSt_cons (κ : ℝ) (n : ℕ) (t : ℂ) (P : C.LPt) : D.bSt κ ((n, t) :: P) = betaZ κ n * D.bSt κ P := by
  simp [D.bSt, betaZ]

theorem bSt_nil (κ : ℝ) : D.bSt κ [] = 1 := by simp [D.bSt]

theorem betaZ_one (κ : ℝ) : betaZ κ 1 = 1 := by simp [betaZ]

theorem prod_Ico_int_succ (f : ℤ → ℝ) (a b : ℤ) (h : a ≤ b) :
    ∏ x ∈ Finset.Ico a (b + 1), f x = (∏ x ∈ Finset.Ico a b, f x) * f b := by
  rw [Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_insert_right h, Finset.prod_insert (by simp), mul_comm]

theorem betaZ_succ (κ : ℝ) (hκ : κ ≠ 0) (n : ℕ) :
    betaZ κ ((n : ℤ) + 1) = betaZ κ n * ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) := by
  unfold betaZ
  have hc : ∀ x : ℤ, κ ^ (1 - 2 * x) / Real.pi ≠ 0 := fun x => div_ne_zero (zpow_ne_zero _ hκ) Real.pi_ne_zero
  have e : ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) + 1 - x) =
      ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), ((κ ^ (1 - 2 * x) / Real.pi) ^ ((n : ℤ) - x) * (κ ^ (1 - 2 * x) / Real.pi)) := by
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← zpow_add_one₀ (hc x)]; congr 1; ring
  rw [e, Finset.prod_mul_distrib]
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [prod_Ico_int_succ _ _ _ (by omega), sub_self, zpow_zero, mul_one]

theorem prod_c (κ : ℝ) (hκ : κ ≠ 0) : ∀ n : ℕ,
    ∏ x ∈ Finset.Ico 1 ((n : ℤ) + 1), (κ ^ (1 - 2 * x) / Real.pi) = κ ^ (-((n : ℤ) ^ 2)) / Real.pi ^ n
  | 0 => by simp
  | n + 1 => by
    rw [show ((n + 1 : ℕ) : ℤ) + 1 = ((n : ℤ) + 1) + 1 by push_cast; ring, prod_Ico_int_succ _ _ _ (by omega),
      prod_c κ hκ n, div_mul_div_comm, ← zpow_add₀ hκ, pow_succ]
    congr 2
    push_cast; ring

theorem betaZ_succ' (κ : ℝ) (hκ : κ ≠ 0) (n : ℕ) :
    betaZ κ ((n : ℤ) + 1) = betaZ κ n * (κ ^ (-((n : ℤ) ^ 2)) / Real.pi ^ n) := by
  rw [betaZ_succ κ hκ, prod_c κ hκ]

theorem weight_product_nonneg (k r : ℕ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 ≤ fr b s) :
    ∀ (b : ℕ) (P : C.LPt), 0 ≤ C.nAux k r 0 fr b P
  | _, [] => by simp [C.nAux]
  | b, (s, t) :: rest => by
    simp only [C.nAux]
    refine mul_nonneg ?_ (weight_product_nonneg k r fr hfr (b + s) rest)
    split_ifs
    · rcases Nat.eq_zero_or_pos (k - 1) with h | h
      · rw [h]; simp
      · rw [zero_pow h.ne']
    · exact zpow_nonneg (mul_nonneg (hfr _ _) (norm_nonneg _)) _

theorem betaZ_pos (κ : ℝ) (hκ : 0 < κ) (N : ℤ) : 0 < betaZ κ N :=
  Finset.prod_pos fun _ _ => zpow_pos (div_pos (zpow_pos hκ _) Real.pi_pos) _

end copied

theorem A_alg (u R Gm dG βn qB nh bh GGs Dn : ℝ) (hu : 0 < u) (hR : 0 < R) (hGm : 0 < Gm) (hdG : 0 < dG)
    (hβ : 0 < βn) (hq : 0 < qB) (hbh : 0 < bh) (hD : 0 < Dn) (n j : ℕ) :
    u ^ n * (√(1 / dG))⁻¹ * (√nh * ((R ^ (n + 1))⁻¹ * u⁻¹) ^ (n * ((j + 1) + n)) * GGs / (bh * βn)) * qB⁻¹ =
      (√nh / bh * (√dG * ((R ^ (n + 1))⁻¹) ^ (n * ((j + 1) + n)) * βn⁻¹ * qB⁻¹ / (Gm ^ ((n + 1) * n ^ 2)))) *
        Dn ^ j * (Gm ^ (n + 1) * u⁻¹) ^ (n ^ 2) * (GGs / (u ^ n * Dn) ^ j) := by
  rw [Real.sqrt_div' _ hdG.le, Real.sqrt_one]
  simp only [mul_pow, inv_pow, ← pow_mul]
  field_simp
  ring

theorem B_alg (u R Gm dG βn qL nh bh sR κ π' : ℝ) (hu : 0 < u) (hR : 0 < R) (hGm : 0 < Gm) (hdG : 0 < dG)
    (hβ : 0 < βn) (hbh : 0 < bh) (hs : 0 < sR) (n j : ℕ) (hκ : κ * R * Gm = 1) (hπ : 0 < π')
    (hqL : 0 < qL) :
    (sR * u ^ n)⁻¹ * (√(R ^ (2 * n) / dG))⁻¹ *
        (√nh * ((R ^ n)⁻¹ * u) ^ ((n + 1) * ((j + 1) + n - 1)) / (bh * (βn * (κ ^ (n ^ 2))⁻¹ / π' ^ n))) * qL⁻¹ =
      (√nh / bh * (√dG * ((R ^ (n + 1))⁻¹) ^ (n * ((j + 1) + n)) * βn⁻¹ * (π'⁻¹ ^ n * qL)⁻¹ / (Gm ^ ((n + 1) * n ^ 2)))) *
        (u ^ (n + 1)) ^ j * (sR⁻¹ * (Gm ^ n * u) ^ (n ^ 2)) := by
  have hκ' : κ = (R * Gm)⁻¹ := by field_simp; linarith
  subst hκ'
  rw [Real.sqrt_div' _ hdG.le, show R ^ (2 * n) = (R ^ n) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [show (j + 1) + n - 1 = j + n by omega]
  simp only [mul_pow, inv_pow, ← pow_mul, inv_inv]
  field_simp
  ring

theorem qU_eq : qU = Real.pi⁻¹ := by
  unfold qU
  have h1 : ‖U.betaU‖ = 2 := by
    simp [U.betaU, Formalism.QuantumDeterminants.cStd]
  rw [h1, Real.coe_toNNReal _ (by positivity)]
  field_simp

theorem sqrt_pow_two_mul (y : ℝ) (hy : 0 ≤ y) (m : ℕ) : √(y ^ (2 * m)) = y ^ m := by
  rw [pow_mul', Real.sqrt_sq (pow_nonneg hy _)]

theorem const_match (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s)
    (hbs : b + s = S.G.r + 2) (hk : 1 ≤ S.G.k) (h : C.LPt) (hsz : D.ptSize h = b - 1) :
    ∃ Kh : ℝ,
      (∀ x D : ℂ, x ≠ 0 → D ≠ 0 →
        ‖x‖ ^ (s - 1) * (√(KB.dlB S (S.G.r + 1) 1))⁻¹ *
            (√(PBL.nnS S (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])) /
              PBL.bS S (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])) *
            (qU ^ ((s - 1) + (Fintype.card (G.UT (s - 1)) + (s - 1))))⁻¹ =
          Kh * ‖D‖ ^ (S.G.k - 1) * ‖lam1 S s * x⁻¹‖ ^ ((s - 1) ^ 2) *
            (√((Complex.normSq (x ^ (s - 1) * D) - S.T * S.T') ^ (S.G.k - 1)) /
              ‖x ^ (s - 1) * D‖ ^ (S.G.k - 1))) ∧
      (∀ z : ℂ, z ≠ 0 →
        ((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√(KB.dlB S b s))⁻¹ *
            (√(PBL.nnS S (h ++ [(s, z)])) / PBL.bS S (h ++ [(s, z)])) * (qU ^ Fintype.card (G.UT s))⁻¹ =
          Kh * ‖z ^ s‖ ^ (S.G.k - 1) * ((s : ℝ)⁻¹ * ‖lam2 S s * z‖ ^ ((s - 1) ^ 2))) := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, S.G.k = j + 1 := ⟨S.G.k - 1, by omega⟩
  have hn1 : n + 1 - 1 = n := by omega
  simp only [hn1]
  rw [show S.G.k - 1 = j by omega]
  set R := S6.rd E with hRdef
  have hR : 0 < R := PBD.rd_pos' E
  set gg : ℝ := (S.g : ℝ) with hgg
  have hgg0 : 0 < gg := by rw [hgg]; exact_mod_cast hg
  set Gm : ℝ := gg / (2 * Real.pi) with hGm
  have hGm0 : 0 < Gm := by positivity
  set κ := D.kapG gg R with hκdef
  have hκ0 : 0 < κ := by rw [hκdef]; unfold D.kapG; positivity
  have hκ : κ * R * Gm = 1 := by
    rw [hκdef, hGm]; unfold D.kapG; field_simp
  set dG := D.deG gg R with hdG
  have hdG0 : 0 < dG := by rw [hdG]; unfold D.deG; positivity
  have hfr : ∀ b s, 0 ≤ S.fr b s := fun b s => by unfold C.HidaSetting.fr; exact Real.rpow_nonneg hR.le _
  set nh := C.nAux S.G.k S.G.r 0 S.fr 1 h with hnh
  have hnh0 : 0 ≤ nh := weight_product_nonneg _ _ _ hfr _ _
  set bh := D.bSt κ h with hbh
  have hbh0 : 0 < bh := PBD.bSt_pos' κ hκ0 h
  set βn := betaZ κ (n : ℤ) with hβn
  have hβ0 : 0 < βn := betaZ_pos κ hκ0 _
  have hq0 : 0 < qU := by rw [qU_eq]; positivity
  set Kc := √dG * ((R ^ (n + 1))⁻¹) ^ (n * ((j + 1) + n)) * βn⁻¹ * (qU ^ (n + (Fintype.card (G.UT n) + n)))⁻¹ /
    (Gm ^ ((n + 1) * n ^ 2)) with hKc
  refine ⟨√nh / bh * Kc, ?_, ?_⟩
  · intro x Dd hx hD
    have hb0 : D.ptSize h + n = S.G.r := by omega
    have hdl1 : KB.dlB S (S.G.r + 1) 1 = 1 / dG := by
      have e : 2 * S6.nuBlock (S.G.r : ℤ) ((S.G.r + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) = 0 := by
        unfold S6.nuBlock; push_cast; ring
      unfold KB.dlB
      rw [e, zpow_zero]
    have hfrA : S.fr (1 + D.ptSize h) n = (R ^ (n + 1))⁻¹ := by
      unfold C.HidaSetting.fr
      have e : ((S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) (n : ℤ) : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
        unfold S6.nuBlock; push_cast
        have : ((D.ptSize h : ℕ) : ℝ) + n = S.G.r := by exact_mod_cast hb0
        linarith
      rw [e, Real.rpow_neg hR.le, Real.rpow_natCast]
    have hM : C.Mlev S.G.k S.G.r (1 + D.ptSize h + n - 1) = (S.G.k : ℤ) + 3 := by
      unfold C.Mlev
      rw [show 1 + D.ptSize h + n - 1 = S.G.r by omega]
      ring
    have hexp : 2 * ((n : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + D.ptSize h + n - 1) + ((n : ℕ) : ℤ) - 3) =
        ((2 * (n * ((j + 1) + n)) : ℕ) : ℤ) := by
      rw [hM, hj]; push_cast; ring
    have hGG : D.ptGG (S.T * S.T') (h ++ [(n, x⁻¹), (1, x ^ n * Dd)]) = Complex.normSq (x ^ n * Dd) - S.T * S.T' := by
      unfold D.ptGG D.ptLast
      simp
    have hnnA : PBL.nnS S (h ++ [(n, x⁻¹), (1, x ^ n * Dd)]) =
        nh * (((R ^ (n + 1))⁻¹ * ‖x⁻¹‖) ^ (2 * (n * ((j + 1) + n))) *
          ((Complex.normSq (x ^ n * Dd) - S.T * S.T') ^ j * 1)) := by
      unfold PBL.nnS C.nLoc
      rw [hGG, weight_product_append, weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 h (by omega)]
      simp only [C.nAux]
      split_ifs with H1 H2 <;> first | (exfalso; omega) | (exfalso; simp only [and_true] at *; omega) | skip
      rw [hfrA, hexp, zpow_natCast, show S.G.k - 1 = j by omega]
    have hbA : PBL.bS S (h ++ [(n, x⁻¹), (1, x ^ n * Dd)]) = bh * βn := by
      unfold PBL.bS
      rw [bSt_append, bSt_cons, bSt_cons, bSt_nil, Nat.cast_one, betaZ_one, mul_one, mul_one]
    have hsq : √(PBL.nnS S (h ++ [(n, x⁻¹), (1, x ^ n * Dd)])) =
        √nh * ((R ^ (n + 1))⁻¹ * ‖x‖⁻¹) ^ (n * ((j + 1) + n)) * √((Complex.normSq (x ^ n * Dd) - S.T * S.T') ^ j) := by
      rw [hnnA, mul_one, ← mul_assoc, Real.sqrt_mul (mul_nonneg hnh0 (pow_nonneg (by positivity) _)),
        Real.sqrt_mul hnh0, sqrt_pow_two_mul _ (by positivity), norm_inv]
    have hl1 : ‖lam1 S (n + 1) * x⁻¹‖ = Gm ^ (n + 1) * ‖x‖⁻¹ := by
      unfold lam1
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity), norm_inv]
    have hcn : ‖x ^ n * Dd‖ = ‖x‖ ^ n * ‖Dd‖ := by rw [norm_mul, norm_pow]
    rw [hdl1, hsq, hbA, hl1, hcn]
    exact A_alg ‖x‖ R Gm dG βn (qU ^ (n + (Fintype.card (G.UT n) + n))) nh bh _ ‖Dd‖ (norm_pos_iff.2 hx) hR hGm0
      hdG0 hβ0 (by positivity) hbh0 (norm_pos_iff.2 hD) n j
  · intro z hz
    have hb0 : D.ptSize h + n = S.G.r := by omega
    have hdl2 : KB.dlB S b (n + 1) = R ^ (2 * n) / dG := by
      have e : 2 * S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((n + 1 : ℕ) : ℤ) = ((2 * n : ℕ) : ℤ) := by
        unfold S6.nuBlock; push_cast; omega
      unfold KB.dlB
      rw [e, zpow_natCast]
    have hfrB : S.fr (1 + D.ptSize h) (n + 1) = (R ^ n)⁻¹ := by
      unfold C.HidaSetting.fr
      have e : ((S6.nuBlock (S.G.r : ℤ) ((1 + D.ptSize h : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ) : ℤ) : ℝ) = ((n : ℕ) : ℝ) := by
        unfold S6.nuBlock; push_cast
        have : ((D.ptSize h : ℕ) : ℝ) + n = S.G.r := by exact_mod_cast hb0
        linarith
      rw [e, Real.rpow_neg hR.le, Real.rpow_natCast]
    have hMB : C.Mlev S.G.k S.G.r (1 + D.ptSize h + (n + 1) - 1) = (S.G.k : ℤ) + 1 := by
      unfold C.Mlev
      rw [show 1 + D.ptSize h + (n + 1) - 1 = S.G.r + 1 by omega]
      push_cast; ring
    have hexpB : 2 * ((n + 1 : ℕ) : ℤ) * (C.Mlev S.G.k S.G.r (1 + D.ptSize h + (n + 1) - 1) + ((n + 1 : ℕ) : ℤ) - 3) =
        ((2 * ((n + 1) * ((j + 1) + n - 1)) : ℕ) : ℤ) := by
      rw [hMB, hj, show j + 1 + n - 1 = j + n by omega]; push_cast; ring
    have hnnB : PBL.nnS S (h ++ [(n + 1, z)]) = nh * (((R ^ n)⁻¹ * ‖z‖) ^ (2 * ((n + 1) * ((j + 1) + n - 1))) * 1) := by
      unfold PBL.nnS C.nLoc
      rw [weight_product_append, weight_product_germ_indep S.G.k S.G.r _ 0 S.fr 1 h (by omega)]
      simp only [C.nAux]
      split_ifs with H1 <;> first | (exfalso; omega) | skip
      rw [hfrB, hexpB, zpow_natCast]
    have hsqB : √(PBL.nnS S (h ++ [(n + 1, z)])) = √nh * ((R ^ n)⁻¹ * ‖z‖) ^ ((n + 1) * ((j + 1) + n - 1)) := by
      rw [hnnB, mul_one, Real.sqrt_mul hnh0, sqrt_pow_two_mul _ (by positivity)]
    have hbB : PBL.bS S (h ++ [(n + 1, z)]) = bh * (βn * (κ ^ (n ^ 2))⁻¹ / Real.pi ^ n) := by
      unfold PBL.bS
      rw [bSt_append, bSt_cons, bSt_nil, mul_one, Nat.cast_add, Nat.cast_one, betaZ_succ' κ hκ0.ne' n,
        show (-((n : ℤ) ^ 2)) = -((n ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
      ring
    have hl2 : ‖lam2 S (n + 1) * z‖ = Gm ^ n * ‖z‖ := by
      unfold lam2
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity), hn1]
    have hzs : ‖z ^ (n + 1)‖ = ‖z‖ ^ (n + 1) := norm_pow _ _
    have hcard : Fintype.card (G.UT (n + 1)) = Fintype.card (G.UT n) + n := by
      rw [StandardCharacterExists.card_UT, StandardCharacterExists.card_UT, Finset.sum_range_succ]
    have hqB : qU ^ (n + (Fintype.card (G.UT n) + n)) = Real.pi⁻¹ ^ n * qU ^ Fintype.card (G.UT (n + 1)) := by
      rw [hcard, pow_add, qU_eq]
    rw [hdl2, hsqB, hbB, hl2, hzs, hKc, hqB]
    exact B_alg ‖z‖ R Gm dG βn (qU ^ Fintype.card (G.UT (n + 1))) nh bh ((n + 1 : ℕ) : ℝ) κ Real.pi
      (norm_pos_iff.2 hz) hR hGm0 hdG0 hβ0 hbh0 (by positivity) n j hκ Real.pi_pos (by positivity)

end pts

theorem det_congr_size (P : C.LPt) {N N' : ℕ} (h : N = N') : (D.ptMatN P N).det = (D.ptMatN P N').det := by
  subst h; rfl

theorem det_block_diagonal_two {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Dm : Matrix (Fin s) (Fin s) ℂ) :
    (U.blk2 A 0 0 Dm).det = A.det * Dm.det := by
  unfold U.blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem det_append (H L : C.LPt) :
    (D.ptMatN (H ++ L) (D.ptSize H + D.ptSize L)).det = (D.ptMatN H (D.ptSize H)).det * (D.ptMatN L (D.ptSize L)).det := by
  rw [PBJ.Asm.ptMatN_append, det_block_diagonal_two]

theorem det_ptLong (n : ℕ) (t : ℂ) : (G.ptLong n t).det = t ^ n * (G.wMat n).det := by
  unfold G.ptLong
  rw [Matrix.det_smul, Fintype.card_fin]

theorem det_pair (n : ℕ) (hn : 1 ≤ n) (t c : ℂ) :
    (D.ptMatN [(n, t), (1, c)] (D.ptSize [(n, t), (1, c)])).det = t ^ n * (G.wMat n).det * c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [det_congr_size _ (show D.ptSize [(m + 1, t), (1, c)] = m + 1 + 1 by simp [D.ptSize]), PBJ.Asm.ptMatN_block,
    PBJ.Asm.ptBlock_eq, det_block_diagonal_two, det_ptLong]
  have h1 : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => c).det = c := by
    rw [Matrix.det_unique]; rfl
  rw [h1]

theorem det_single (n : ℕ) (t : ℂ) : (D.ptMatN [(n, t)] (D.ptSize [(n, t)])).det = t ^ n * (G.wMat n).det := by
  rw [det_congr_size _ (show D.ptSize [(n, t)] = n by simp [D.ptSize]), PBJ.Asm.ptMatN_long, det_ptLong]

theorem ptMatN_drop_last (H : C.LPt) (n : ℕ) (t c : ℂ) (r : ℕ) (hr : D.ptSize H + n = r) :
    D.ptMatN (H ++ [(n, t), (1, c)]) r = D.ptMatN (H ++ [(n, t)]) r := by
  ext a b
  have e : H ++ [(n, t), (1, c)] = (H ++ [(n, t)]) ++ [(1, c)] := by simp
  simp only [D.ptMatN]
  rw [e, PBJ.Asm.ptEntry_append, if_pos]
  rw [PBJ.Asm.ptSize_append, PBJ.Asm.ptSize_single]
  exact ⟨by omega, by omega⟩

theorem normSq_det_wMat (n : ℕ) : Complex.normSq (G.wMat n).det = 1 := by
  rw [Complex.normSq_eq_norm_sq, G5.norm_det_wMat]; norm_num

theorem det_top_Px (H : C.LPt) (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr : D.ptSize H + n + 1 = r + 1) (t c : ℂ) :
    (D.ptMatN (H ++ [(n, t), (1, c)]) (r + 1)).det = (D.ptMatN H (D.ptSize H)).det * (t ^ n * (G.wMat n).det * c) := by
  have hL : D.ptSize [(n, t), (1, c)] = n + 1 := by simp [D.ptSize]
  rw [det_congr_size _ (show r + 1 = D.ptSize H + D.ptSize [(n, t), (1, c)] by omega), det_append,
    det_pair n hn]

theorem det_low_Px (H : C.LPt) (n : ℕ) (r : ℕ) (hr : D.ptSize H + n + 1 = r + 1) (t c : ℂ) :
    (D.ptMatN (H ++ [(n, t), (1, c)]) r).det = (D.ptMatN H (D.ptSize H)).det * (t ^ n * (G.wMat n).det) := by
  rw [ptMatN_drop_last H n t c r (by omega),
    det_congr_size _ (show r = D.ptSize H + D.ptSize [(n, t)] by rw [PBJ.Asm.ptSize_single]; omega), det_append, det_single]

theorem ptG_Px (TT : ℝ) (H : C.LPt) (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr : D.ptSize H + n + 1 = r + 1) (t c : ℂ) :
    D.ptG TT r (H ++ [(n, t), (1, c)]) =
      Complex.normSq (D.ptMatN H (D.ptSize H)).det * ‖t‖ ^ (2 * n) * (Complex.normSq c - TT) := by
  unfold D.ptG
  rw [det_top_Px H n hn r hr, det_low_Px H n r hr]
  simp only [map_mul, map_pow, normSq_det_wMat, Complex.normSq_eq_norm_sq t]
  ring

theorem wPt_Px (TT : ℝ) (H : C.LPt) (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr : D.ptSize H + n + 1 = r + 1) (t c : ℂ)
    (hG : D.ptG TT r (H ++ [(n, t), (1, c)]) ≠ 0) :
    Top.wPt TT r (H ++ [(n, t), (1, c)]) = Complex.normSq c / (Complex.normSq c - TT) := by
  have hG' := hG
  rw [ptG_Px TT H n hn r hr] at hG'
  have hA : Complex.normSq (D.ptMatN H (D.ptSize H)).det * ‖t‖ ^ (2 * n) ≠ 0 := by
    intro h0; apply hG'; rw [h0, zero_mul]
  have key : Complex.normSq (D.ptMatN (H ++ [(n, t), (1, c)]) (r + 1)).det =
      Complex.normSq (D.ptMatN H (D.ptSize H)).det * ‖t‖ ^ (2 * n) * Complex.normSq c := by
    rw [det_top_Px H n hn r hr]
    simp only [map_mul, map_pow, normSq_det_wMat, Complex.normSq_eq_norm_sq t]
    ring
  unfold Top.wPt
  rw [ptG_Px TT H n hn r hr, key, mul_div_mul_left _ _ hA]

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactRoots
namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

theorem norm_psi_one (b w : ℂ) : ‖G.psi b w‖ = 1 := by
  unfold G.psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem isCompact_roots (n : ℕ) (hn : 0 < n) (K : Set ℂ) (hK : IsCompact K) :
    IsCompact {z : ℂ | z ^ n ∈ K} := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine Metric.isCompact_of_isClosed_isBounded (hK.isClosed.preimage (continuous_pow n)) ?_
  refine isBounded_iff_forall_norm_le.2 ⟨max 1 R, fun z hz => ?_⟩
  have h1 : ‖z ^ n‖ ≤ R := hR _ hz
  rw [norm_pow] at h1
  by_cases hz1 : ‖z‖ ≤ 1
  · exact le_trans hz1 (le_max_left _ _)
  · push Not at hz1
    have : ‖z‖ ≤ ‖z‖ ^ n := by
      calc ‖z‖ = ‖z‖ ^ 1 := (pow_one _).symm
        _ ≤ ‖z‖ ^ n := pow_le_pow_right₀ hz1.le hn
    exact le_trans (le_trans this h1) (le_max_right _ _)

theorem germ_core (m p : ℕ) (σh : Equiv.Perm (Fin p)) (dh : Fin p → ℂ) (hdh : ∀ i, dh i ≠ 0)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Φ0 : G.Mat (p + (m + 1 + 1)) → V) (hΦ0 : PBJ.KCls Φ0)
    (l1 l2 : ℂ) (hl1 : l1 ≠ 0) (hl : l2 ^ (m + 2) = (-1) ^ (m + 3) * l1 ^ (m + 1))
    (βL : ℝ) (hψ : ∀ w : ℂ, G.psi U.betaU (l2 / l1 * w) = conj (G.psi (βL : ℂ) w))
    (K : Set ℂ) (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) (ρ : ℂ → ℂ → ℝ) (R0 L : ℝ)
    (hρ : ∀ x D : ℂ, x ≠ 0 → D ∈ K →
      G.OmBlock U.betaU (m + 1) (U.PhiTop (p := p) (s := m + 1 + 1) U.betaU σh dh Φ0) (l1 * x⁻¹) (x ^ (m + 1) * D) ≠ 0 →
      |ρ x D| ≤ R0 ∧ |ρ x D - 1| ≤ L * ‖x‖⁻¹ ^ (2 * (m + 1))) :
    ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x D : ℝ) : ℂ) •
          G.OmBlock U.betaU (m + 1) (U.PhiTop (p := p) (s := m + 1 + 1) U.betaU σh dh Φ0) (l1 * x⁻¹) (x ^ (m + 1) * D) -
        ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) D,
          (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
            G.OmLong U.betaU (m + 1) (U.PhiTop (p := p) (s := m + 1 + 1) U.betaU σh dh Φ0) (l2 * z)‖ ≤ C * ‖x‖⁻¹ := by
  classical
  set Ψ := U.PhiTop (p := p) (s := m + 1 + 1) U.betaU σh dh Φ0 with hΨ
  have hβ : U.betaU ≠ 0 := Formalism.FourierDecayAlt.P.scale_matching.2.1

  obtain ⟨C₁, C₂, hUG⟩ := Formalism.FourierDecayAlt.P.germ_expansion_top_level
  set Nr : ℝ := ((p + (m + 1 + 1) : ℕ) : ℝ) with hNr
  have hN0 : 0 < 5 * Nr := by rw [hNr]; positivity
  set A : ℝ := (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 with hA
  set E : ℝ := 5 * Nr * (|A| + 2 * Nr ^ 2 + 1) with hEdef
  have hEq : E / (5 * Nr) = |A| + 2 * Nr ^ 2 + 1 := by
    have hNr0 : Nr ≠ 0 := by intro h0; rw [h0] at hN0; simp at hN0
    rw [hEdef]; field_simp
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hE : ∀ i ≤ C₂ * (m + 2) ^ 2, A ≤ (fun _ : ℕ => E) i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ)) ∧
      2 * ((p + (m + 1 + 1) : ℕ) : ℝ) ^ 2 < (fun _ : ℕ => E) i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ)) := by
    intro i _
    simp only
    rw [← hNr, hEq]
    constructor
    · have := le_abs_self A; nlinarith [sq_nonneg Nr]
    · have := abs_nonneg A; linarith
  have hl1p : l1 ^ (m + 1) ≠ 0 := pow_ne_zero _ hl1
  set Kc : Set ℂ := (fun D => l1 ^ (m + 1) * D) '' K with hKc
  have hKcc : IsCompact Kc := hK.image (continuous_const.mul continuous_id)
  have hKc0 : (0 : ℂ) ∉ Kc := by
    rintro ⟨D, hD, hD0⟩
    rcases mul_eq_zero.1 hD0 with h | h
    · exact hl1p h
    · exact hK0 (h ▸ hD)
  obtain ⟨Cst, hC⟩ := hUG p m U.betaU hβ σh dh hdh (fun _ => E) A le_rfl hE Kc hKcc hKc0
  obtain ⟨K0, hK0d⟩ := PBJ.Asm.decayAll_of_cls Φ0 hΦ0 (C₂ * (m + 2) ^ 2) E hE0
  have hct : ∀ x : ℂ, x ≠ 0 → ∀ D : ℂ, x ^ (m + 1) * D * (l1 * x⁻¹) ^ (m + 1) = l1 ^ (m + 1) * D := by
    intro x hx D
    have hxp : x ^ (m + 1) ≠ 0 := pow_ne_zero _ hx
    rw [mul_pow, inv_pow]
    field_simp
  set B1 : ℝ := |Cst * K0| * ‖l1‖ with hB1def
  have hB1 : 0 ≤ B1 := by positivity
  have hrem : ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖G.remainder U.betaU m (fun _ => 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D)‖ ≤ B1 * ‖x‖⁻¹ := by
    intro x hx D hD
    have ht : l1 * x⁻¹ ≠ 0 := mul_ne_zero hl1 (inv_ne_zero hx)
    have h := hC V Φ0 K0 hK0d (l1 * x⁻¹) (x ^ (m + 1) * D) ht (by rw [hct x hx D]; exact ⟨D, hD, rfl⟩)
    rw [norm_mul, norm_inv] at h
    calc _ ≤ Cst * K0 * (‖l1‖ * ‖x‖⁻¹) := h
      _ ≤ |Cst * K0| * (‖l1‖ * ‖x‖⁻¹) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = B1 * ‖x‖⁻¹ := by rw [hB1def]; ring

  have hm2 : ((m : ℂ) + 2) ≠ 0 := by
    have h : ((m : ℂ) + 2) = ((m + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [h]; exact_mod_cast (by omega : m + 2 ≠ 0)
  have hneg : ((-1 : ℂ)) ^ (m + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hl2 : l2 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hl
    exact (mul_ne_zero hneg hl1p) hl.symm
  have hs : 0 < m + 2 := by omega
  have hroots : ∀ D : ℂ, G.rootSet (m + 2) ((-1) ^ (m + 3) * (l1 ^ (m + 1) * D)) =
      (G.rootSet (m + 2) D).image (fun z => l2 * z) := by
    intro D; ext ζ
    rw [Finset.mem_image, Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs]
    constructor
    · intro hζ
      refine ⟨ζ / l2, (Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs).2 ?_, by field_simp⟩
      rw [div_pow, hζ, hl]
      field_simp
    · rintro ⟨z, hz, rfl⟩
      rw [Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs] at hz
      rw [mul_pow, hl, hz]; ring
  have hmain : ∀ x : ℂ, x ≠ 0 → ∀ D : ℂ,
      G.mainTerm U.betaU m (fun _ => 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D * (l1 * x⁻¹) ^ (m + 1)) =
        ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) D,
          (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
            G.OmLong U.betaU (m + 1) Ψ (l2 * z) := by
    intro x hx D
    unfold G.mainTerm
    rw [hct x hx D, hroots D, Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hl2 h)]
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    have harg : ((m : ℂ) + 2) * (l2 * z) / (l1 * x⁻¹) = l2 / l1 * (((m : ℂ) + 2) * z * x) := by
      field_simp
    rw [mul_one, harg, hψ]

  obtain ⟨KΨ, hΨc, hΨd⟩ := LastBlockContinuity.lastBlock_decay U.betaU p (m + 1 + 1) (by omega) σh dh hdh Φ0 hΦ0
    (2 * ((((m + 1 : ℕ) : ℝ) + 1) * (((m + 1 : ℕ) : ℝ) + 1)) + 1)
  have hOmc : ContinuousOn (G.OmLong U.betaU (m + 1) Ψ) {0}ᶜ :=
    LastBlockContinuity.omLong_continuousOn U.betaU (m + 1) Ψ hΨc KΨ _ (by linarith) hΨd
  set Kz : Set ℂ := {z : ℂ | z ^ (m + 2) ∈ K} with hKz
  have hKzc : IsCompact Kz := isCompact_roots (m + 2) hs K hK
  have hKz0 : ∀ z ∈ Kz, z ≠ 0 := by
    intro z hz h0
    rw [hKz, Set.mem_ofPred_eq, h0, zero_pow (by omega)] at hz
    exact hK0 hz
  have hfc : ContinuousOn (fun z : ℂ => ‖l2 * z‖ ^ ((m + 1) ^ 2) * ‖G.OmLong U.betaU (m + 1) Ψ (l2 * z)‖) Kz := by
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) ?_
    refine ContinuousOn.norm ?_
    refine hOmc.comp (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
    exact mul_ne_zero hl2 (hKz0 z hz)
  obtain ⟨M1, hM1⟩ := hKzc.exists_bound_of_continuousOn hfc
  set M : ℝ := ((m : ℝ) + 2) * max M1 0 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hmb : ∀ x : ℂ, ∀ D ∈ K, ‖((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) D,
      (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
        G.OmLong U.betaU (m + 1) Ψ (l2 * z)‖ ≤ M := by
    intro x D hD
    have hterm : ∀ z ∈ G.rootSet (m + 2) D, ‖(((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) *
        conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) • G.OmLong U.betaU (m + 1) Ψ (l2 * z)‖ ≤ max M1 0 := by
      intro z hz
      have hzK : z ∈ Kz := by
        show z ^ (m + 2) ∈ K
        rw [(Formalism.FourierDecayAlt.P.mem_rootSet_iff_pow_eq hs).1 hz]
        exact hD
      rw [norm_smul, norm_mul, Complex.norm_conj, norm_psi_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      have := hM1 z hzK
      rw [Real.norm_eq_abs] at this
      exact le_trans (le_trans (le_abs_self _) this) (le_max_left _ _)
    have hcard : ((G.rootSet (m + 2) D).card : ℝ) ≤ (m : ℝ) + 2 := by
      have h1 : (G.rootSet (m + 2) D).card ≤ m + 2 :=
        le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots (m + 2) D)
      exact_mod_cast h1
    have hsum := norm_sum_le_of_le (G.rootSet (m + 2) D) hterm
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    rw [norm_smul, norm_inv]
    have hn2 : ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2 := by
      have h : ((m : ℂ) + 2) = (((m : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
      rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hn2]
    have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    calc ((m : ℝ) + 2)⁻¹ * ‖∑ z ∈ G.rootSet (m + 2) D, _‖
        ≤ 1 * (((m : ℝ) + 2) * max M1 0) := by
          apply mul_le_mul (inv_le_one_of_one_le₀ (by linarith)) _ (norm_nonneg _) zero_le_one
          exact hsum.trans (mul_le_mul_of_nonneg_right hcard (le_max_right _ _))
      _ = M := by rw [one_mul]

  refine ⟨B1 + (|L| + |R0| + 1) * (B1 + M), fun x hx D hD => ?_⟩
  set X : V := ((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D)
    with hX
  set main : V := ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) D,
      (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
        G.OmLong U.betaU (m + 1) Ψ (l2 * z) with hmaindef
  have hXm : ‖X - main‖ ≤ B1 * ‖x‖⁻¹ := by
    have h := hrem x hx D hD
    unfold G.remainder at h
    rw [hmain x hx D] at h
    exact h
  have hmM : ‖main‖ ≤ M := hmb x D hD
  have hexpr : ((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x D : ℝ) : ℂ) •
      G.OmBlock U.betaU (m + 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D) = ((ρ x D : ℝ) : ℂ) • X := by
    rw [hX, smul_smul]; push_cast; ring_nf
  rw [hexpr]
  set y : ℝ := ‖x‖⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  have hC0 : 0 ≤ (|L| + |R0| + 1) * (B1 + M) := by positivity
  by_cases hOm : G.OmBlock U.betaU (m + 1) Ψ (l1 * x⁻¹) (x ^ (m + 1) * D) = 0
  · have hX0 : X = 0 := by rw [hX, hOm, smul_zero]
    rw [hX0, smul_zero]
    rw [hX0] at hXm
    calc ‖0 - main‖ ≤ B1 * y := hXm
      _ ≤ (B1 + (|L| + |R0| + 1) * (B1 + M)) * y := mul_le_mul_of_nonneg_right (by linarith) hy0
  · obtain ⟨hR, hLb⟩ := hρ x D hx hD hOm
    have key : ((ρ x D : ℝ) : ℂ) • X - main = (X - main) + ((ρ x D - 1 : ℝ) : ℂ) • X := by
      push_cast; rw [sub_smul, one_smul]; abel
    rw [key]
    have hXb : ‖X‖ ≤ B1 * y + M := by
      calc ‖X‖ = ‖(X - main) + main‖ := by rw [sub_add_cancel]
        _ ≤ ‖X - main‖ + ‖main‖ := norm_add_le _ _
        _ ≤ B1 * y + M := add_le_add hXm hmM
    have hsc : ‖((ρ x D - 1 : ℝ) : ℂ) • X‖ = |ρ x D - 1| * ‖X‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have htri := norm_add_le (X - main) (((ρ x D - 1 : ℝ) : ℂ) • X)
    rw [hsc] at htri
    have hR0 : 0 ≤ R0 := le_trans (abs_nonneg _) hR
    by_cases hx1 : 1 ≤ ‖x‖
    · have hy1 : y ≤ 1 := by rw [hy]; exact inv_le_one_of_one_le₀ hx1
      have hpow : y ^ (2 * (m + 1)) ≤ y := by
        calc y ^ (2 * (m + 1)) ≤ y ^ 1 := pow_le_pow_of_le_one hy0 hy1 (by omega)
          _ = y := pow_one y
      have h1 : |ρ x D - 1| ≤ |L| * y := by
        calc |ρ x D - 1| ≤ L * y ^ (2 * (m + 1)) := hLb
          _ ≤ |L| * y ^ (2 * (m + 1)) := mul_le_mul_of_nonneg_right (le_abs_self L) (by positivity)
          _ ≤ |L| * y := mul_le_mul_of_nonneg_left hpow (abs_nonneg L)
      have h2 : ‖X‖ ≤ B1 + M := by
        have : B1 * y ≤ B1 := mul_le_of_le_one_right hB1 hy1
        linarith
      have h3 : |ρ x D - 1| * ‖X‖ ≤ |L| * y * (B1 + M) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      calc ‖(X - main) + ((ρ x D - 1 : ℝ) : ℂ) • X‖ ≤ ‖X - main‖ + |ρ x D - 1| * ‖X‖ := htri
        _ ≤ B1 * y + |L| * y * (B1 + M) := add_le_add hXm h3
        _ = B1 * y + (|L| * (B1 + M)) * y := by ring
        _ ≤ B1 * y + ((|L| + |R0| + 1) * (B1 + M)) * y := by
          have : |L| * (B1 + M) ≤ (|L| + |R0| + 1) * (B1 + M) :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg R0]) (by positivity)
          linarith [mul_le_mul_of_nonneg_right this hy0]
        _ = (B1 + (|L| + |R0| + 1) * (B1 + M)) * y := by ring
    · push Not at hx1
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hy1 : 1 ≤ y := by rw [hy]; exact (one_le_inv₀ hxpos).2 hx1.le
      have h1 : |ρ x D - 1| ≤ |R0| + 1 := by
        have hr := abs_le.1 hR
        have hR' := le_abs_self R0
        exact abs_le.2 ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have h2 : ‖X‖ ≤ (B1 + M) * y := by
        have : M ≤ M * y := le_mul_of_one_le_right hM0 hy1
        calc ‖X‖ ≤ B1 * y + M := hXb
          _ ≤ B1 * y + M * y := by linarith
          _ = (B1 + M) * y := by ring
      have h3 : |ρ x D - 1| * ‖X‖ ≤ (|R0| + 1) * ((B1 + M) * y) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      calc ‖(X - main) + ((ρ x D - 1 : ℝ) : ℂ) • X‖ ≤ ‖X - main‖ + |ρ x D - 1| * ‖X‖ := htri
        _ ≤ B1 * y + (|R0| + 1) * ((B1 + M) * y) := add_le_add hXm h3
        _ = B1 * y + ((|R0| + 1) * (B1 + M)) * y := by ring
        _ ≤ B1 * y + ((|L| + |R0| + 1) * (B1 + M)) * y := by
          have : (|R0| + 1) * (B1 + M) ≤ (|L| + |R0| + 1) * (B1 + M) :=
            mul_le_mul_of_nonneg_right (by linarith [abs_nonneg L]) (by positivity)
          linarith [mul_le_mul_of_nonneg_right this hy0]
        _ = (B1 + (|L| + |R0| + 1) * (B1 + M)) * y := by ring

end

end Formalism.FourierDecayAlt.P.GermRateSplit
end

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

def ptJ (s : ℕ) (h : C.LPt) (x D : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]
  | some z => h ++ [(s, z)]

section core

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def coJ (S : C.HidaSetting E Wp Wq) (b s : ℕ) (x : ℂ) : Option ℂ → ℂ
  | none => ((‖x‖ ^ (s - 1) * (√(KB.dlB S (S.G.r + 1) 1))⁻¹ : ℝ) : ℂ)
  | some z => -(G.psi (GermRealisation.betaL S) ((s : ℂ) * z * x) *
      ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√(KB.dlB S b s))⁻¹ : ℝ) : ℂ))

variable [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem top_core {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f)
    (F' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hF' : KB.CptCoef (p v).T.base F') (N : ℕ)
    (b s : ℕ) (hb : 1 ≤ b) (hs : 2 ≤ s) (hbs : b + s = S.G.r + 2) (h : C.LPt) (hsz : D.ptSize h = b - 1)
    (K : Set ℂ) (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖∑ j ∈ Finset.insertNone (G.rootSet s D), (conj (coJ S b s x j) * (omN S N (ptJ s h x D j) : ℂ)) •
          (p v).V F' (PBL.stdS S (ptJ s h x D j))‖ ≤ C * ‖x‖⁻¹ := by
  have hg : (0 : ℝ) < (S.g : ℝ) := PBL.g_pos_of_built hB
  have hgN : 0 < S.g := by exact_mod_cast hg
  have hk : 1 ≤ S.G.k := by
    obtain ⟨-, -, -, -, -, -, -, hl1, hlk, -⟩ := hB
    omega

  by_cases hgood : ∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0
  swap
  · refine ⟨0, fun x hx y hy => ?_⟩
    have hz : ∀ j, (p v).V F' (PBL.stdS S (ptJ s h x y j)) = 0 := by
      intro j
      unfold KB.Pl.V D.vecV
      rw [dite_eq_right]
      rintro ⟨hl, -⟩
      have hl' := (PBD.isLocPt_toStd_iff _ _ hg _ 1 _).1 hl
      refine hgood fun q hq => hl'.1 q ?_
      cases j <;> simp [ptJ, hq]
    simp [hz]
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have hTTeq := (PBL.pdG_of_built hB v).2
  have hTT : 0 < S.T * S.T' := by rw [← hTTeq]; exact mul_pos (p v).T.base.T_pos (p v).T.base.T'_pos
  obtain ⟨ε0, hε0, hsupp⟩ := hF'.2.2
  set H := PBL.stdS S h with hHdef
  have hH : ∀ q ∈ H, 1 ≤ q.1 ∧ q.2 ≠ 0 := ((PBD.isLocPt_toStd_iff _ _ hg h 1 (D.ptSize h)).2 ⟨hgood, rfl⟩).1
  have hHs : D.ptSize H = b - 1 := by rw [hHdef, PBL.stdS_size, hsz]
  obtain ⟨Φ0, hs0, hc0, hdet0, hV0⟩ := Formalism.FourierDecayAlt.P.phi_zero_hermitian_curvature _ _ (D.parOf S v) (p v) F' hF'
  have hn : D.ptSize H + (m + 1 + 1) = (D.parOf S v).r + 1 := by
    rw [hHs]; change _ = S.G.r + 1; omega
  obtain ⟨σh, dh, Ψ0, hdh, hΨ0, hOB, hOL⟩ := vec_om ((p v).V F') Φ0 ⟨hs0, hc0, hdet0⟩ hV0 H hH m hn
  obtain ⟨Kh, hKA, hKB⟩ := const_match S hgN b (m + 2) hb hs hbs hk h hsz
  set l1 := lam1 S (m + 2) with hl1def
  set l2 := lam2 S (m + 2) with hl2def
  have hq0 : ((S.g : ℝ) / (2 * Real.pi)) ≠ 0 := (div_pos hg (by positivity)).ne'
  have hl1 : l1 ≠ 0 := by
    rw [hl1def, lam1]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 (pow_ne_zero _ hq0)) (pow_ne_zero _ Complex.I_ne_zero)
  have hl : l2 ^ (m + 2) = (-1) ^ (m + 3) * l1 ^ (m + 1) := by
    rw [hl2def, hl1def, lam1, lam2, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← pow_mul, ← pow_mul]
    have e2 : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
    have e3 : (m + 2) * (m + 1) = (m + 1) * (m + 2) := by ring
    rw [e3, e2, pow_add Complex.I, pow_mul Complex.I 2 (m + 1), Complex.I_sq]
    ring
  have hl2ne : l2 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hl
    exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hl1)) hl.symm
  set βL : ℝ := 4 * Real.pi / (S.g : ℝ) with hβL
  have hq : l2 / l1 = (((2 * Real.pi / (S.g : ℝ)) : ℝ) : ℂ) * Complex.I := by
    have hgc : ((S.g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hg.ne'
    have hpc : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have hgc' : (S.g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hgN.ne'
    have hcq : (2 * (Real.pi : ℂ) / (S.g : ℂ)) * ((S.g : ℂ) / (2 * (Real.pi : ℂ))) = 1 := by
      field_simp
    have e : l2 = (((2 * Real.pi / (S.g : ℝ)) : ℝ) : ℂ) * Complex.I * l1 := by
      rw [hl2def, hl1def, lam1, lam2, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
      push_cast
      linear_combination (-(((S.g : ℂ) / (2 * (Real.pi : ℂ))) ^ (m + 1) * Complex.I ^ (m + 1))) * hcq
    rw [e, mul_div_assoc, div_self hl1, mul_one]
  have hψ : ∀ w : ℂ, G.psi U.betaU (l2 / l1 * w) = conj (G.psi (βL : ℂ) w) := by
    intro w
    have hbU : U.betaU = 2 * Complex.I := by
      unfold U.betaU Formalism.QuantumDeterminants.cStd; ring
    unfold G.psi
    rw [← Complex.exp_conj, hq, hbU, hβL]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    have hre : ((2 * Complex.I) * ((((2 * Real.pi / (S.g : ℝ)) : ℝ) : ℂ) * Complex.I * w)).re =
        -((4 * Real.pi / (S.g : ℝ)) * w.re) := by
      simp [Complex.mul_re, Complex.mul_im]
      ring
    have hre2 : ((((4 * Real.pi / (S.g : ℝ)) : ℝ) : ℂ) * w).re = (4 * Real.pi / (S.g : ℝ)) * w.re := by
      simp [Complex.mul_re]
    rw [hre, hre2]
    push_cast
    ring
  obtain ⟨MK, hMK⟩ := hK.isBounded.exists_norm_le
  obtain ⟨mK, hmK, hmK'⟩ : ∃ mK : ℝ, 0 < mK ∧ ∀ y ∈ K, mK ≤ ‖y‖ := by
    have ho : (Kᶜ : Set ℂ) ∈ 𝓝 (0 : ℂ) := hK.isClosed.isOpen_compl.mem_nhds hK0
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ho
    refine ⟨r, hr, fun y hy => ?_⟩
    by_contra hlt
    exact hball (by simpa [dist_zero_right] using not_le.1 hlt) hy
  set dH0 := Complex.normSq (D.ptMatN H (D.ptSize H)).det with hdH0
  set δ : ℝ := ε0 / (max dH0 1 * ‖l1‖ ^ (2 * (m + 1)) * (max MK 1) ^ 2) with hδ
  set ρ : ℂ → ℂ → ℝ := fun x y => √((Complex.normSq (x ^ (m + 1) * y) - S.T * S.T') ^ (S.G.k - 1)) /
      ‖x ^ (m + 1) * y‖ ^ (S.G.k - 1) *
      √(Top.wPt (S.T * S.T') S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) ^ N) with hρdef
  set R0 : ℝ := √((δ⁻¹) ^ N) with hR0
  set L : ℝ := ((S.G.k - 1 : ℕ) + N * (δ⁻¹) ^ N) * (S.T * S.T' / mK ^ 2) with hL
  have hρ : ∀ x y : ℂ, x ≠ 0 → y ∈ K →
      G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l1 * x⁻¹)
        (x ^ (m + 1) * y) ≠ 0 →
      |ρ x y| ≤ R0 ∧ |ρ x y - 1| ≤ L * ‖x‖⁻¹ ^ (2 * (m + 1)) := by
    intro x y hx hy hOm
    have hy0 : y ≠ 0 := fun h0 => hK0 (h0 ▸ hy)
    have hc0 : x ^ (m + 1) * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) hy0
    have ht0 : l1 * x⁻¹ ≠ 0 := mul_ne_zero hl1 (inv_ne_zero hx)
    have hV : (p v).V F' (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) ≠ 0 := by
      rw [hOB _ _ ht0 hc0]
      refine smul_ne_zero ?_ hOm
      exact Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_ne_zero _ qU_pos.ne'))
    have hGe : ε0 ≤ D.ptG (S.T * S.T') S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) := by
      by_contra hlt
      exact hV (Formalism.FourierDecayAlt.P.PBO.vecV_zero_small (p v).T.base (p v).ν' (p v).m₀ hsupp _
        (lt_of_eq_of_lt (congrArg (fun T => D.ptG T S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)])) hTTeq)
          (not_le.1 hlt)))
    have hr : D.ptSize H + (m + 1) + 1 = S.G.r + 1 := by rw [hHs]; omega
    have hptG := ptG_Px (S.T * S.T') H (m + 1) (by omega) S.G.r hr (l1 * x⁻¹) (x ^ (m + 1) * y)
    have hGne : D.ptG (S.T * S.T') S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) ≠ 0 :=
      (lt_of_lt_of_le hε0 hGe).ne'
    have hwPt := wPt_Px (S.T * S.T') H (m + 1) (by omega) S.G.r hr (l1 * x⁻¹) (x ^ (m + 1) * y) hGne
    have hnc : Complex.normSq (x ^ (m + 1) * y) = ‖x‖ ^ (2 * (m + 1)) * ‖y‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm (m + 1) 2]
    have hA : ε0 ≤ dH0 * ‖l1 * x⁻¹‖ ^ (2 * (m + 1)) * (Complex.normSq (x ^ (m + 1) * y) - S.T * S.T') := by
      rw [hptG] at hGe; exact hGe
    have hρe : ρ x y = √((Complex.normSq (x ^ (m + 1) * y) - S.T * S.T') ^ (S.G.k - 1)) /
        ‖x ^ (m + 1) * y‖ ^ (S.G.k - 1) *
        √((Complex.normSq (x ^ (m + 1) * y) / (Complex.normSq (x ^ (m + 1) * y) - S.T * S.T')) ^ N) := by
      simp only [hρdef]; rw [hwPt]
    rw [hρe]
    exact rho_bound (S.T * S.T') ε0 dH0 MK mK hTT hε0 (Complex.normSq_nonneg _) hmK (S.G.k - 1) N m l1 x y
      (x ^ (m + 1) * y) hl1 hx hy0 hc0 (hMK y hy) (hmK' y hy) hnc hA
  obtain ⟨Cg, hCg⟩ := germ_core m (D.ptSize H) σh dh hdh Ψ0 hΨ0 l1 l2 hl1 hl βL hψ K hK hK0 ρ R0 L hρ
  refine ⟨|Kh| * (max MK 0) ^ (S.G.k - 1) * Cg, fun x hx y hy => ?_⟩
  have key : ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) y), (conj (coJ S b (m + 2) x j) *
      (omN S N (ptJ (m + 2) h x y j) : ℂ)) • (p v).V F' (PBL.stdS S (ptJ (m + 2) h x y j)) =
      ((Kh * ‖y‖ ^ (S.G.k - 1) : ℝ) : ℂ) •
        (((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x y : ℝ) : ℂ) •
          G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l1 * x⁻¹)
            (x ^ (m + 1) * y) -
        ((m : ℂ) + 2)⁻¹ • ∑ z ∈ G.rootSet (m + 2) y,
          (((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
            G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z)) := by
    have hy0 : y ≠ 0 := fun h0 => hK0 (h0 ▸ hy)
    have hc0 : x ^ (m + 1) * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) hy0
    have ht0 : l1 * x⁻¹ ≠ 0 := mul_ne_zero hl1 (inv_ne_zero hx)

    have hnone : (conj (coJ S b (m + 2) x none) * (omN S N (ptJ (m + 2) h x y none) : ℂ)) •
        (p v).V F' (PBL.stdS S (ptJ (m + 2) h x y none)) =
        ((Kh * ‖y‖ ^ (S.G.k - 1) : ℝ) : ℂ) •
          (((‖l1 * x⁻¹‖ ^ ((m + 1) ^ 2) * ρ x y : ℝ) : ℂ) •
            G.OmBlock U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l1 * x⁻¹)
              (x ^ (m + 1) * y)) := by
      have hstd := std_Px S (m + 2) hs h (by omega) x⁻¹ (x ^ (m + 2 - 1) * y)
      have hKA' := hKA x y hx hy0
      simp only [e1] at hstd hKA'
      simp only [coJ, ptJ, omN, e1]
      rw [hstd, hOB _ _ ht0 hc0, Complex.conj_ofReal, smul_smul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul]
      congr 2
      simp only [hρdef]
      rw [← hHdef, ← hl1def]
      linear_combination √(Top.wPt (S.T * S.T') S.G.r (H ++ [(m + 1, l1 * x⁻¹), (1, x ^ (m + 1) * y)]) ^ N) * hKA'

    have hLong : ∀ z : ℂ, z ≠ 0 →
        ((√(Top.wPt (S.T * S.T') S.G.r (H ++ [(m + 2, l2 * z)]) ^ N) : ℝ) : ℂ) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z) =
        G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z) := by
      intro z hz
      have hl2z : l2 * z ≠ 0 := mul_ne_zero hl2ne hz
      have hOL2 : (p v).V F' (H ++ [(m + 2, l2 * z)]) = (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z) :=
        hOL _ hl2z
      by_cases hG : 0 < D.ptG (S.T * S.T') S.G.r (H ++ [(m + 2, l2 * z)])
      · rw [PBL.wPt_big (S.T * S.T') H (m + 2) (l2 * z) S.G.r (by omega) (by rw [hHs]; omega) hG, one_pow,
          Real.sqrt_one, Complex.ofReal_one, one_smul]
      · have h0 : (p v).V F' (H ++ [(m + 2, l2 * z)]) = 0 := by
          unfold KB.Pl.V D.vecV
          rw [dite_eq_right]
          rintro ⟨-, hpos⟩
          exact hG (lt_of_lt_of_eq hpos (congrArg (fun T => D.ptG T S.G.r (H ++ [(m + 2, l2 * z)])) hTTeq))
        rw [hOL2] at h0
        have hq : (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_ne_zero _ qU_pos.ne'))
        rw [(smul_eq_zero.1 h0).resolve_left hq, smul_zero]
    have hsome : ∀ z ∈ G.rootSet (m + 2) y,
        (conj (coJ S b (m + 2) x (some z)) * (omN S N (ptJ (m + 2) h x y (some z)) : ℂ)) •
          (p v).V F' (PBL.stdS S (ptJ (m + 2) h x y (some z))) =
        -(((Kh * ‖y‖ ^ (S.G.k - 1) : ℝ) : ℂ) • (((m : ℂ) + 2)⁻¹ •
          ((((‖l2 * z‖ ^ ((m + 1) ^ 2) : ℝ) : ℂ) * conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x))) •
            G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z)))) := by
      intro z hz
      have hzs : z ^ (m + 2) = y := by
        unfold G.rootSet at hz
        exact (Polynomial.mem_nthRoots (by omega)).1 (Multiset.mem_toFinset.1 hz)
      have hz0 : z ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hzs; exact hy0 hzs.symm
      have hl2z : l2 * z ≠ 0 := mul_ne_zero hl2ne hz0
      have hstd := std_Qz S (m + 2) hs h (by omega) z
      have hKB' := hKB z hz0
      rw [hzs] at hKB'
      simp only [e1] at hKB'
      have hOL2 : (p v).V F' (H ++ [(m + 2, l2 * z)]) = (((qU ^ Fintype.card (G.UT (m + 1 + 1)))⁻¹ : ℝ) : ℂ) •
          G.OmLong U.betaU (m + 1) (U.PhiTop (p := D.ptSize H) (s := m + 1 + 1) U.betaU σh dh Ψ0) (l2 * z) :=
        hOL _ hl2z
      simp only [coJ, ptJ, omN, e1]
      rw [hstd, ← hHdef, ← hl2def, hOL2, smul_smul,
        Complex.ofReal_mul (√(PBL.nnS S (h ++ [(m + 2, z)])) / PBL.bS S (h ++ [(m + 2, z)])),
        show ∀ a b c d : ℂ, a * (b * c) * d = (a * b * d) * c from fun a b c d => by ring, ← smul_smul,
        hLong z hz0, smul_smul, smul_smul, ← neg_smul]
      congr 1
      have hβ : GermRealisation.betaL S = (βL : ℂ) := by simp only [GermRealisation.betaL, hβL]
      have hpsi : G.psi (GermRealisation.betaL S) (((m + 2 : ℕ) : ℂ) * z * x) = G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x) := by
        rw [hβ]; congr 1; push_cast; ring
      rw [hpsi, map_neg, map_mul, Complex.conj_ofReal]
      have hKc := congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hKB'
      push_cast at hKc ⊢
      linear_combination (-(conj (G.psi (βL : ℂ) (((m : ℂ) + 2) * z * x)))) * hKc
    rw [Finset.sum_insertNone, hnone, Finset.sum_congr rfl hsome, Finset.sum_neg_distrib, smul_sub,
      Finset.smul_sum, Finset.smul_sum, sub_eq_add_neg]
  rw [key, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ (S.G.k - 1))]
  have h1 := hCg x hx y hy
  have h2 : ‖y‖ ^ (S.G.k - 1) ≤ (max MK 0) ^ (S.G.k - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) ((hMK y hy).trans (le_max_left _ _)) _
  have h3 : 0 ≤ Cg * ‖x‖⁻¹ := le_trans (norm_nonneg _) h1
  calc |Kh| * ‖y‖ ^ (S.G.k - 1) * ‖_‖ ≤ |Kh| * ‖y‖ ^ (S.G.k - 1) * (Cg * ‖x‖⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ |Kh| * (max MK 0) ^ (S.G.k - 1) * (Cg * ‖x‖⁻¹) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) h3
    _ = |Kh| * (max MK 0) ^ (S.G.k - 1) * Cg * ‖x‖⁻¹ := by ring

end core

end

end Formalism.FourierDecayAlt.P.GermRateSplit
