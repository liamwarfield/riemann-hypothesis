module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmRingIdempotentUnitRatioIdentity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaBoundOnBoundary
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensitySumsAndDomination
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupremumAIsMajorant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionMatrixFunction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentBlockMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealWeightedForms
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AAInvTrans
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumLocalExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.Curves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ListSumSplittings
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RoomOffGridSymmetric
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinLeTruncatedExponential
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralFormulaPassesToLimits
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AntidiagMulDiagonal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorsCommuteTranslations

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.XiYZhatIdentity
section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovecEntries
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianCovectors.HermBvecLeft
open Matrix

noncomputable section

namespace CovecW

open Formalism.QuantumDeterminants

def sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

lemma sig_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sig k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold sig
  split_ifs <;> rfl

lemma sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sig k r (sig k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  rw [sig_val, sig_val]
  split_ifs <;> omega

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

lemma sgn_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by
  have hi := i.isLt
  unfold sgn
  rw [sig_val]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma Hpk_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sig k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, sgn, Fin.ext_iff, sig_val]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma Hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Hpk_eq]
  rw [Finset.sum_eq_single (sig k r i)]
  · rw [if_pos rfl, sig_sig, sgn_sig]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl]
      unfold sgn
      split_ifs <;> norm_num
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  · intro l _ hl
    rw [if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma sig_eI (k r : ℕ) (a : Fin r) : sig k r (eI k r a) = esI k r a := by
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  apply Fin.ext
  rw [sig_val, h1, h2]
  split_ifs <;> omega

lemma sig_esI (k r : ℕ) (a : Fin r) : sig k r (esI k r a) = eI k r a := by
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
  apply Fin.ext
  rw [sig_val, h1, h2]
  split_ifs <;> omega

lemma sgn_eI (k r : ℕ) (a : Fin r) : sgn k r (eI k r a) = 1 := by
  have ha := a.isLt
  have h1 : (eI k r a).val = a.val := rfl
  unfold sgn
  rw [h1, if_neg (by omega)]

lemma sgn_esI (k r : ℕ) (a : Fin r) : sgn k r (esI k r a) = 1 := by
  have ha := a.isLt
  have h1 : (esI k r a).val = 2 * r + k - a.val := rfl
  unfold sgn
  rw [h1, if_neg (by omega)]

lemma Hpk_mul_eI (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (j : Fin (2 * r + k + 1)) : (Hpk k r * M) (eI k r a) j = M (esI k r a) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sig k r (eI k r a))]
  · rw [Hpk_eq, if_pos rfl, sgn_eI, sig_eI, one_mul]
  · intro l _ hl
    rw [Hpk_eq, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma Hpk_mul_esI (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : Fin r)
    (j : Fin (2 * r + k + 1)) : (Hpk k r * M) (esI k r b) j = M (eI k r b) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sig k r (esI k r b))]
  · rw [Hpk_eq, if_pos rfl, sgn_esI, sig_esI, one_mul]
  · intro l _ hl
    rw [Hpk_eq, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma mul_Hpk_eI (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (i : Fin (2 * r + k + 1)) : (M * Hpk k r) i (eI k r a) = M i (esI k r a) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r a)]
  · rw [Hpk_eq, if_pos (sig_esI k r a).symm, sgn_esI, mul_one]
  · intro l _ hl
    rw [Hpk_eq, if_neg, mul_zero]
    intro h
    apply hl
    have h2 := congrArg (sig k r) h
    rw [sig_sig, sig_eI] at h2
    exact h2.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma mulVec_bvec (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (y : Fin (2 * r + k + 1)) :
    M *ᵥ bvec y = fun i => M i y := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma herm_bvec_left (k r : ℕ) (H M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x y : Fin (2 * r + k + 1)) :
    herm H (M *ᵥ bvec y) (bvec x) = (H * M) x y := by
  unfold herm
  rw [Matrix.mulVec_mulVec, mulVec_bvec, dotProduct, Finset.sum_eq_single x]
  · simp [bvec]
  · intro l _ hl
    simp [bvec, Pi.single_apply, hl]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma zhat_lo (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Fin r) :
    Zhat k r z z' g a.castSucc b.castSucc = herm (Hpk k r) (g *ᵥ bvec (eI k r b)) (bvec (eI k r a)) := by
  have ha : (a.castSucc : Fin (r + 1)).val < r := by simp
  have hb : (b.castSucc : Fin (r + 1)).val < r := by simp
  simp only [Zhat, fvec, dif_pos ha, dif_pos hb]
  rfl

lemma inv_eq (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Hpk_sq]

theorem covec_entries : Formalism.FourierDecayAlt.C3.XiYZhat := by
  intro k r z z' g a b hg
  refine ⟨(zhat_lo k r z z' g a b).symm, ?_⟩
  rw [zhat_lo, herm_bvec_left, Hpk_mul_eI, mulVec_bvec, inv_eq k r g hg]
  beta_reduce
  rw [Matrix.mul_assoc, Hpk_mul_esI, mul_Hpk_eI, Matrix.conjTranspose_apply]

end CovecW
end
end

theorem covector_entries : Formalism.FourierDecayAlt.C3.XiYZhat := CovecW.covec_entries
end

theorem Formalism.FourierDecayAlt.P.xi_Y_zhat_identity : Formalism.FourierDecayAlt.C3.XiYZhat :=
  covector_entries
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionGivesUniformBoundsForm
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix

namespace Formalism.FourierDecayAlt.P.Jx6

end Formalism.FourierDecayAlt.P.Jx6

namespace Formalism.FourierDecayAlt.P

open Jx6

theorem form_gives_theorem_A : Formalism.FourierDecayAlt.J.FormGivesMain := by
  intro hM P _ B hPos he hKV h2A hF hMass hform hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩ := hPos
  have hn : 0 < B.n0c := a33
  have hen : 0 < B.e1 * B.n0c := mul_pos he hn
  have key := hM P { B with supdens := B.e1, KtopV := B.KV / (B.e1 * B.n0c) }
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, he.le, a35⟩ h2A hF
    (by
      constructor
      · show B.KV ≤ B.e1 * B.n0c * (B.KV / (B.e1 * B.n0c))
        rw [mul_div_cancel₀ _ hen.ne']
      · show 0 ≤ B.KV / (B.e1 * B.n0c)
        exact div_nonneg hKV hen.le)
    hMass
    (by show B.e1 ≤ B.e1; exact le_refl _)
    (by
      show B.c0 * B.c0' * (B.KV / (B.e1 * B.n0c)) ≤ (1 + B.δ) * B.IntN
      rw [← mul_div_assoc, div_le_iff₀ hen]
      have e : (1 + B.δ) * B.e1 * (B.n0c * B.IntN) = (1 + B.δ) * B.IntN * (B.e1 * B.n0c) := by ring
      linarith)
    hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  exact key

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SixteenMulLeTwoPow
namespace Formalism.FourierDecayAlt.P.Sz9

open Finset Formalism.FourierDecayAlt.Sz

lemma sixteen_mul_le_two_pow (n : ℕ) (hn : 7 ≤ n) : n * 16 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h16 : 16 ≤ 2 ^ k :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    linarith

lemma small_f (f k : ℕ) (hfk : f ≤ k) (hk : 7 ≤ k) : (f : ℝ) * (8 / 2 ^ k) ≤ Real.log 2 := by
  have h1 := sixteen_mul_le_two_pow k hk
  have h2 : (k : ℝ) * 16 ≤ (2 : ℝ) ^ k := by exact_mod_cast h1
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hf : (f : ℝ) ≤ k := by exact_mod_cast hfk
  have hlog := Real.log_two_gt_d9
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith [mul_lt_mul_of_pos_right hlog hpos]

lemma vand_pos (p : ℕ) (x : ℕ → ℝ) (h : ∀ s t, 1 ≤ s → s < t → t ≤ p → x t < x s) :
    0 < Vand p x := by
  unfold Vand
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_Icc] at hi
  rw [Finset.mem_Ioc] at hj
  have hx := h i j hi.1 hj.1 hj.2
  linarith

lemma anti_of_step (p : ℕ) (x : ℕ → ℝ) (h : ∀ i, 1 ≤ i → i < p → x (i + 1) < x i) :
    ∀ s t, 1 ≤ s → s < t → t ≤ p → x t < x s := by
  intro s t hs hst htp
  obtain ⟨d, rfl⟩ : ∃ d, t = s + 1 + d := ⟨t - (s + 1), by omega⟩
  induction d with
  | zero => simpa using h s hs (by omega)
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := h (s + 1 + d) (by omega) (by omega)
    have e : s + 1 + (d + 1) = s + 1 + d + 1 := by omega
    rw [e]
    linarith

lemma vand_word_pos (hIL : Interlacing) (c : Cfg) (de : ℕ → ℝ) (hOk : c.Ok)
    (hde : IsWord c.k de) : 0 < Vand c.k (c.u de) := by
  unfold Interlacing at hIL
  obtain ⟨h1, -⟩ := hIL c de hOk hde
  refine vand_pos _ _ (anti_of_step _ _ (fun i hi1 hi2 => ?_))
  have hx := h1 i hi1 hi2
  linarith [hx.1, hx.2]

lemma sfac_pos (p : ℕ) : 0 < sfac p := by
  unfold sfac
  exact Finset.prod_pos (fun i _ => Nat.factorial_pos i)

lemma tcrit_nonneg (k m : ℕ) (ka rd g VV Vu : ℝ) (hka : 0 < ka) (hrd : 0 < rd) (hg : 0 < g)
    (hVV : 0 < VV) (hVu : 0 < Vu) : 0 ≤ Tcrit k m ka rd g VV Vu := by
  unfold Tcrit
  apply Real.rpow_nonneg
  unfold TcritPow
  positivity

lemma beta_bound (hBeta : BetaOnCut) (hAZ : AZeroBound) (c : Cfg) (r : ℕ) (bb : ℝ)
    (de de' : ℕ → ℝ) (ka rd g VV T T' : ℝ) (l : ℕ)
    (hOk : c.Ok) (hm : c.m = 2 * r + 2) (hSm : c.Small bb) (hde : IsWord c.k de)
    (hde' : IsWord c.k de') (hrd : 1 ≤ rd) (hka : ka = 2 * Real.pi / rd) (hg : 2 * Real.pi ≤ g)
    (hFD : FormalDegreeLower c (1 / 2) VV) (hT : 0 < T) (hT' : 0 < T') (hl1 : 1 ≤ l)
    (hl2 : l + 2 ≤ c.k) (hdl : de l ≠ de' l) (D : ℝ) (hD : D ≤ c.Del / 2) (Y : ℝ)
    (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ D) :
    0 ≤ g ^ c.m * c.be ka de de' T T' Y ∧
      g ^ c.m * c.be ka de de' T T' Y ≤
        160 * tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt (D / c.Del) := by
  have hpi := Real.pi_pos
  have hg0 : 0 < g := by linarith
  have hka0 : 0 < ka := by rw [hka]; positivity
  have hDel : 0 < c.Del := by linarith [hOk.hDel]
  constructor
  · unfold Cfg.be Cfg.core
    positivity
  · have hYI : Y ∈ c.cutI l := ⟨hY1, hY2.trans hD⟩
    have h := hBeta c r bb de de' ka rd g VV T T' Y l hOk hm hSm hde hde' hrd hka hg hFD hT hT'
      hl1 hl2 hdl hYI
    have hA := (hAZ c bb hOk hSm).2
    have ht : 0 ≤ tv c de de' ka rd g VV T T' := by unfold tv; exact Real.sqrt_nonneg _
    have hs : Real.sqrt ((c.v l + Y) / c.Del) ≤ Real.sqrt (D / c.Del) := by
      apply Real.sqrt_le_sqrt
      gcongr
    calc g ^ c.m * c.be ka de de' T T' Y
        ≤ AZero c bb * tv c de de' ka rd g VV T T' * Real.sqrt c.k *
          Real.sqrt ((c.v l + Y) / c.Del) := h
      _ ≤ 160 * tv c de de' ka rd g VV T T' * Real.sqrt c.k * Real.sqrt (D / c.Del) := by
          gcongr

end Formalism.FourierDecayAlt.P.Sz9

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz9


set_option maxHeartbeats 1000000 in
theorem sz_sizesMain_of (hCorA : CorA) (hBeta : BetaOnCut) (hAZ : AZeroBound)
    (hIL : Interlacing) (hLA : LamAnti) (hTP : ThresholdProducts) (hTL : ThetaLower) (hThP : ThetaPower)
    (hFS : FinalSmall) : SizesMain := by
  intro CA C0 CG CDel cT Cb hCA hC0 hCG hCDel hcT hCb hcTCb
  have hc : 0 < cExp CDel cT Cb := by
    unfold cExp
    have : 0 < min ((CDel - 4) / 2) ((cT * Cb - 1) / 4) := lt_min (by linarith) (by linarith)
    positivity
  obtain ⟨Ct, hCt⟩ : ∃ Ct : ℝ, Ct = 2 * C0 * Real.exp (1 / 4) := ⟨_, rfl⟩
  have hCt1 : 1 ≤ Ct := by
    have : 1 ≤ Real.exp (1 / 4) := Real.one_le_exp (by norm_num)
    rw [hCt]; nlinarith
  obtain ⟨k1, hk1⟩ := hThP CA 160 Ct CDel cT Cb hCA (by norm_num) hCt1 hCDel hcT hCb hcTCb
  obtain ⟨k2, hk2⟩ := hFS CA (cExp CDel cT Cb) hCA hc
  refine ⟨max 7 (max k1 k2), ?_⟩
  intro ι _ G bb C' Cf Th de de' T T' du du' l hk H hde hde' hl1 hl2 hdl hT hT' hC' hkbig hMR hLB
    hCC hCC' hCh hCh' hFD hTh hGr
  have hk7 : 7 ≤ G.k := le_trans (le_max_left _ _) hk
  have hkk1 : k1 ≤ G.k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkk2 : k2 ≤ G.k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hkR : (7 : ℝ) ≤ G.k := by exact_mod_cast hk7
  have hm2 : 2 ≤ G.m := by unfold Glob.m; omega
  have hf2 : 2 ≤ G.f := le_trans hm2 H.hmf
  have hbb := H.hbb
  have hv := H.hv
  have hpi := Real.pi_pos
  have hne : Nonempty ι := by
    have : 0 < Fintype.card ι := lt_of_lt_of_le (by norm_num) hf2
    exact Fintype.card_pos_iff.1 this
  obtain ⟨w0⟩ := hne

  have hbbk : (G.k : ℝ) ^ (Cb / 2) ≤ bb := by
    have h1 : (G.k : ℝ) ^ Cb ≤ G.b w0 1 := H.hnode w0 1 le_rfl (by omega)
    have h2 : G.b w0 1 ≤ bb ^ 2 := (H.hsmall w0).hbj 1 le_rfl (by show 1 ≤ 2 * G.r + 2; omega)
    have h3 : ((G.k : ℝ) ^ (Cb / 2)) ^ 2 = (G.k : ℝ) ^ Cb := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast; ring
    have h4 : ((G.k : ℝ) ^ (Cb / 2)) ^ 2 ≤ bb ^ 2 := by rw [h3]; exact h1.trans h2
    exact (pow_le_pow_iff_left₀ (by positivity) (by linarith) (by norm_num)).1 h4
  have hpw : 1 < bb ^ (cT * (G.m : ℝ)) := by
    apply Real.one_lt_rpow hbb
    have : (0 : ℝ) < G.m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm2)
    positivity
  have hTR : (1 : ℝ) < T := lt_of_lt_of_le hpw hT
  have hTR' : (1 : ℝ) < T' := lt_of_lt_of_le hpw hT'
  have hT2 : 2 ≤ T := by
    have : 1 < T := by exact_mod_cast hTR
    omega
  have hT2' : 2 ≤ T' := by
    have : 1 < T' := by exact_mod_cast hTR'
    omega
  have hTT : (bb ^ (cT * (G.m : ℝ))) ^ 2 ≤ (T : ℝ) * T' := by
    rw [sq]
    exact mul_le_mul hT hT' (by linarith) (by linarith)
  have hTTpos : (0 : ℝ) < (T : ℝ) * T' := mul_pos (by linarith) (by linarith)
  have hNm : G.N = 10 * (G.m : ℝ) := by
    unfold Glob.N Glob.m; push_cast; ring
  have hN20 : 20 ≤ G.N := by
    unfold Glob.N
    have : (0 : ℝ) ≤ G.r := Nat.cast_nonneg _
    linarith
  have hN : 0 < G.N := by linarith
  obtain ⟨hCpi, hmin⟩ := hk1 G.k G.m G.f bb G.N G.lenI G.Del ((T : ℝ) * T') hkk1 hm2 H.hmf H.hfk
    hNm rfl hbbk H.hDel hTT
  have hkc1 : 1 ≤ (G.k : ℝ) ^ cExp CDel cT Cb := Real.one_le_rpow (by linarith) hc.le

  have hDelBig : 160 ^ 2 * ((G.k : ℝ) * G.N ^ 3) ≤ G.Del := by
    have h1 : (G.k : ℝ) ^ cExp CDel cT Cb ≤
        Real.sqrt (G.Del / (G.k * G.N ^ 3)) / (Ct * CA * 160) :=
      le_trans hmin (le_trans (min_le_left _ _) (min_le_left _ _))
    have hpos : 0 < Ct * CA * 160 := by positivity
    have h2 : Ct * CA * 160 ≤ Real.sqrt (G.Del / (G.k * G.N ^ 3)) := by
      have := (le_div_iff₀ hpos).1 (le_trans hkc1 h1)
      linarith
    have h3 : (160 : ℝ) ≤ Real.sqrt (G.Del / (G.k * G.N ^ 3)) := by
      have : 1 ≤ Ct * CA := one_le_mul_of_one_le_of_one_le hCt1 hCA
      linarith
    have h4 := (Real.le_sqrt' (by norm_num : (0 : ℝ) < 160)).1 h3
    have hkN : 0 < (G.k : ℝ) * G.N ^ 3 := by positivity
    exact (le_div_iff₀ hkN).1 h4
  have hN3 : 1 ≤ G.N ^ 3 := one_le_pow₀ (by linarith)
  have hkN3 : G.N ^ 3 ≤ (G.k : ℝ) * G.N ^ 3 := le_mul_of_one_le_left (by linarith) (by linarith)
  have hN3Del : G.N ^ 3 ≤ G.Del / 2 := by linarith
  have hDelpos : 0 < G.Del := by linarith
  have hI : 0 < G.lenI := by unfold Glob.lenI; linarith

  have hkb : (4 : ℝ) ≤ ((G.k : ℝ) * bb) ^ 8 := by
    have h1 : (4 : ℝ) ≤ (G.k : ℝ) * bb := by
      have := mul_le_mul hkR hbb.le zero_le_one (by linarith)
      linarith
    exact le_trans h1 (le_self_pow₀ (by linarith) (by norm_num))
  have hg1R : (4 : ℝ) ≤ G.g1 := le_trans hkb H.hg1
  have hg2R : (4 : ℝ) ≤ G.g2 := le_trans hkb H.hg2
  have hg1N : 4 ≤ G.g1 := by exact_mod_cast hg1R
  have hg2N : 4 ≤ G.g2 := by exact_mod_cast hg2R
  have hg16 : 16 ≤ G.g := by
    have := mul_le_mul hg1R hg2R (by norm_num) (by linarith)
    unfold Glob.g; linarith
  have h2pig : 2 * Real.pi ≤ G.g := by linarith [Real.pi_le_four]
  have hgpos : 0 < G.g := by linarith
  have hka : G.ka = 2 * Real.pi / (2 * G.v) := by
    unfold Glob.ka; field_simp
  have hkapos : 0 < G.ka := by unfold Glob.ka; positivity
  have hkapi : G.ka ≤ Real.pi := by
    unfold Glob.ka
    exact div_le_self hpi.le hv

  have hVu : ∀ w, 0 < Vand G.k ((G.place w).u de) := fun w =>
    vand_word_pos hIL (G.place w) de (H.hplace w) hde
  have hVu' : ∀ w, 0 < Vand G.k ((G.place w).u de') := fun w =>
    vand_word_pos hIL (G.place w) de' (H.hplace w) hde'
  have hVV : ∀ w, 0 < (G.size de T du).VV w := by
    intro w
    have h1 : 0 < Vand ((G.place w).k + (G.place w).m - 1) (G.place w).lam :=
      vand_pos _ _ (hLA (G.place w) (H.hplace w))
    have h2 := hFD w
    unfold FormalDegreeLower at h2
    linarith
  have hdsig : ∀ w, 0 < G.dsig w := by
    intro w
    have h1 : 0 < G.dsig w * (sfac (G.size de T du).n : ℝ) := hVV w
    have h2 : (0 : ℝ) < (sfac (G.size de T du).n : ℝ) := by exact_mod_cast sfac_pos _
    exact (mul_pos_iff_of_pos_right h2).1 h1

  have hsm := small_f G.f G.k H.hfk hk7
  have hlogbb : 0 ≤ Real.log bb := Real.log_nonneg hbb.le
  have hOkS : (G.size de T du).Ok :=
    ⟨(by omega : 1 ≤ G.k), (by linarith : 0 < G.v), H.hdF, (by omega : 2 ≤ G.g1),
      (by omega : 2 ≤ G.g2), hT2, H.hvol, hVu⟩
  have hOkS' : (G.size de' T' du').Ok :=
    ⟨(by omega : 1 ≤ G.k), (by linarith : 0 < G.v), H.hdF, (by omega : 2 ≤ G.g1),
      (by omega : 2 ≤ G.g2), hT2', H.hvol, hVu'⟩
  have hA := hCorA ι (G.size de T du) C0 CG C' (Real.log bb) hOkS hMR hLB hCC hdsig
    (by omega : 2 ≤ G.k) hg1N hg2N hC0 hCG hlogbb hC' hkbig hsm hCh
  have hA' := hCorA ι (G.size de' T' du') C0 CG C' (Real.log bb) hOkS' hMR hLB hCC' hdsig
    (by omega : 2 ≤ G.k) hg1N hg2N hC0 hCG hlogbb hC' hkbig hsm hCh'
  have hP : ∏ w, ((G.size de T du).Tcrit w / (T : ℝ)) ≤ Ct := by
    rw [hCt]; exact le_trans hA.2.1 hA.2.2
  have hP' : ∏ w, ((G.size de' T' du').Tcrit w / (T' : ℝ)) ≤ Ct := by
    rw [hCt]; exact le_trans hA'.2.1 hA'.2.2
  have hTc : ∀ w, 0 ≤ (G.size de T du).Tcrit w := fun w =>
    tcrit_nonneg _ _ _ _ _ _ _ hkapos (by show 0 < 2 * G.v; linarith) hgpos (hVV w) (hVu w)
  have hTc' : ∀ w, 0 ≤ (G.size de' T' du').Tcrit w := fun w =>
    tcrit_nonneg _ _ _ _ _ _ _ hkapos (by show 0 < 2 * G.v; linarith) hgpos (hVV w) (hVu' w)
  obtain ⟨t, ht⟩ : ∃ t : ι → ℝ, t = fun w =>
      tv (G.place w) de de' G.ka (2 * G.v) G.g ((G.size de T du).VV w) T T' := ⟨_, rfl⟩
  have ht0 : ∀ w, 0 ≤ t w := by
    intro w; rw [ht]; exact Real.sqrt_nonneg _
  have htsq : ∀ w, t w ^ 2 =
      ((G.size de T du).Tcrit w / (T : ℝ)) * ((G.size de' T' du').Tcrit w / (T' : ℝ)) := by
    intro w
    rw [ht]
    show (Real.sqrt ((G.size de T du).Tcrit w * (G.size de' T' du').Tcrit w /
      ((T : ℝ) * T'))) ^ 2 = _
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg (hTc w) (hTc' w)) hTTpos.le), div_mul_div_comm]
  have htprod : ∏ w, t w ≤ Ct := by
    have h1 : (∏ w, t w) ^ 2 ≤ Ct ^ 2 := by
      rw [← prod_pow, prod_congr rfl (fun w _ => htsq w), prod_mul_distrib, sq]
      apply mul_le_mul hP hP' _ (by linarith)
      exact prod_nonneg fun w _ => div_nonneg (hTc' w) (by linarith)
    exact (pow_le_pow_iff_left₀ (prod_nonneg fun w _ => ht0 w) (by linarith) (by norm_num)).1 h1

  have hbd : ∀ (w : ι) (D : ℝ), D ≤ G.Del / 2 → ∀ Y : ℝ, 5 / 2 ≤ (G.place w).v l + Y →
      (G.place w).v l + Y ≤ D →
      0 ≤ G.g ^ G.m * (G.place w).be G.ka de de' T T' Y ∧
        G.g ^ G.m * (G.place w).be G.ka de de' T T' Y ≤
          160 * t w * Real.sqrt G.k * Real.sqrt (D / G.Del) := by
    intro w D hD Y hY1 hY2
    rw [ht]
    exact beta_bound hBeta hAZ (G.place w) G.r bb de de' G.ka (2 * G.v) G.g
      ((G.size de T du).VV w) T T' l (H.hplace w) rfl (H.hsmall w) hde hde' (by linarith) hka h2pig
      (hFD w) (by linarith) (by linarith) hl1 hl2 hdl D hD Y hY1 hY2
  have hB1 : ∀ w, 0 ≤ G.cutSupLong de de' T T' l w ∧ G.cutSupLong de de' T T' l w ≤
      160 * t w * Real.sqrt G.k * Real.sqrt (G.N ^ 3 / G.Del) := by
    intro w
    unfold Glob.cutSupLong
    constructor
    · apply Real.sSup_nonneg
      rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
      exact (hbd w _ hN3Del Y hY1 hY2).1
    · apply Real.sSup_le
      · rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
        exact (hbd w _ hN3Del Y hY1 hY2).2
      · have := ht0 w
        positivity
  have hB : ∀ w, 0 ≤ G.supI de de' T T' l w ∧ G.supI de de' T T' l w ≤
      160 * t w * Real.sqrt G.k := by
    intro w
    have hs1 : Real.sqrt (G.Del / 2 / G.Del) ≤ 1 := by
      apply Real.sqrt_le_one.2
      rw [div_le_one hDelpos]; linarith
    have h0 : 0 ≤ 160 * t w * Real.sqrt G.k := by
      have := ht0 w
      positivity
    unfold Glob.supI
    constructor
    · apply Real.sSup_nonneg
      rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
      exact (hbd w _ le_rfl Y hY1 hY2).1
    · apply Real.sSup_le
      · rintro _ ⟨Y, ⟨hY1, hY2⟩, rfl⟩
        exact le_trans (hbd w _ le_rfl Y hY1 hY2).2 (mul_le_of_le_one_right h0 hs1)
      · exact h0

  have key := fun i s : ℕ => hTP ι t (G.cutSupLong de de' T T' l) (G.supI de de' T T' l) G.k CA 160 Ct
    G.ka G.N G.lenI G.g G.Del ((T : ℝ) * T') i s hCA (by norm_num) (by linarith) hkapos hkapi hN hI
    (by linarith) hDelpos hTTpos hCpi ht0 htprod hB1 hB
  have hTheta : (G.k : ℝ) ^ cExp CDel cT Cb ≤ Th := by
    refine le_trans hmin ?_
    apply hTL G.f G.k CA 160 Ct G.N G.lenI G.Del ((T : ℝ) * T') Th (by omega) (by omega) hCA
      (by norm_num) hCt1 hN hI hDelpos hTTpos hTh hCpi
    obtain ⟨i, hi1, hi2, hcase⟩ := hGr.1
    rcases hcase with ⟨_, hx⟩ | ⟨h2i, hx⟩ | ⟨s, hs2, _, hx⟩ | hx
    · left; rw [hx]; exact (key 1 1 le_rfl).1
    · right; left; rw [hx]; exact (key i 1 hi1).2.1 h2i
    · right; right; left; rw [hx]; exact (key i s hi1).2.2.1 hs2
    · right; right; right; rw [hx]; exact (key i 1 hi1).2.2.2
  refine ⟨hTheta, ?_⟩
  intro h16 hCf
  exact hk2 G.k G.r G.f bb Cf Th hkk2 H.hmf hbb.le h16 hCf hTheta

theorem size_bounds_conclusion : Formalism.FourierDecayAlt.Sz.SizesMain :=
  sz_sizesMain_of corollary_a_of_proposition_a beta_bound_on_boundary a_zero_le_one_sixty interlacing
    lamStrictAnti threshold_products theta_lower_bound theta_power_bound final_smallness

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordLiftInduction
namespace Formalism.FourierDecayAlt.P.WordLiftInduction

open Finset Polynomial Formalism.FourierDecayAlt.F7

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

end

end Formalism.FourierDecayAlt.P.WordLiftInduction

namespace Formalism.FourierDecayAlt.P

open Finset Polynomial Formalism.FourierDecayAlt.F7

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.Block32EqZeroOfUnipotent
namespace Formalism.FourierDecayAlt.P.S3x9

open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)

end Formalism.FourierDecayAlt.P.S3x9
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ReductionSurjective
namespace Formalism.FourierDecayAlt.P.S3x2

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]

variable {c : ι → ℕ} {x y : Matrix ι ι A}


end Generic

section Prod

variable {G : Type} [Group G]

end Prod

section Specific

variable {A : Type} [CommRing A] {r k : ℕ}




end Specific

section Local

variable (o : Type) [CommRing o] [IsLocalRing o]

variable {o} {r k : ℕ}

end Local

end Formalism.FourierDecayAlt.P.S3x2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CentreBlockStructure
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.S3x8

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3

section Key

variable {A F : Type} [CommRing A] [CommRing F]

end Key

section Corner

variable {A F : Type} [CommRing A] [CommRing F]

end Corner

section Maps

variable {A F : Type} [CommRing A] [CommRing F]

end Maps

section DVR

variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]

variable [IsDomain o] [IsDiscreteValuationRing o]

end DVR

section Blocks

variable {A : Type} {r k : ℕ}

variable [CommRing A]

section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
end mk

end Blocks

section Stab

variable {F : Type} [Field F] {r k : ℕ}

end Stab

section Forcing

variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}

variable [IsDomain o] [IsDiscreteValuationRing o] [IsFractionRing o k0]


end Forcing

end Formalism.FourierDecayAlt.P.S3x8
end

namespace Formalism.FourierDecayAlt.Final

theorem field_extension_degree_facts : Formalism.FourierDecayAlt.S6.DegreeFacts := Formalism.FourierDecayAlt.P.degreeFacts_statement
theorem ideal_norm_formula : Formalism.FourierDecayAlt.S6.NormIdl := Formalism.FourierDecayAlt.P.scaledIdealNorm
theorem ideals_match : Formalism.FourierDecayAlt.S6.IdealsMatch := Formalism.FourierDecayAlt.P.dualIdealEqLiftIdeal
theorem parahoric_gram_matrix : Formalism.FourierDecayAlt.A5.KpGram := Formalism.FourierDecayAlt.P.kernel_gram_property
theorem ns_support : Formalism.FourierDecayAlt.A5.NsSupport := Formalism.FourierDecayAlt.P.added_block_kernel_support
theorem zero_level_ones_vector : Formalism.FourierDecayAlt.A5.BaseKernelOne := Formalism.FourierDecayAlt.P.zero_kernel_all_ones
theorem latticeAverage_of_gram : Formalism.FourierDecayAlt.A5.LemmaAAssemble := Formalism.FourierDecayAlt.P.lattice_average_lemma_from_parts
theorem poisson_summation_text : Formalism.FourierDecayAlt.F7.PoissonStepText := Formalism.FourierDecayAlt.P.poisson_summation_level_statement
theorem ns_block_diagonal : Formalism.FourierDecayAlt.A5.NsBlockDiag := Formalism.FourierDecayAlt.P.added_block_kernel_block_diagonal
theorem lattices_general_position_bound : Formalism.FourierDecayAlt.S6.LatticesGeneral := Formalism.FourierDecayAlt.P.lattice_facts_general
theorem counting_theorem : Formalism.FourierDecayAlt.S3.MainTheorem := Formalism.FourierDecayAlt.P.mass_formula_constant_one
theorem singleBlockParseval_true : Formalism.FourierDecayAlt.A5.SingleBlockParseval := Formalism.FourierDecayAlt.P.first_kernel_parseval
theorem theta_equality_first : Formalism.FourierDecayAlt.A5.Th1Eq := Formalism.FourierDecayAlt.P.first_theta_kernel_equality
theorem singleBlockThetaProps_true : Formalism.FourierDecayAlt.A5.SingleBlockThetaProps := Formalism.FourierDecayAlt.P.first_theta_equals_first_kernel
theorem sz_propA : Formalism.FourierDecayAlt.Sz.PropA := Formalism.FourierDecayAlt.P.massRatioFormula
theorem sz_eaSize : Formalism.FourierDecayAlt.Sz.EaSize := Formalism.FourierDecayAlt.P.exponent_sizes
theorem gram_determinant_dual_bound_a : Formalism.FourierDecayAlt.A5.A2 := Formalism.FourierDecayAlt.P.second_gram_and_vanishing
theorem sz_sizesMain : Formalism.FourierDecayAlt.Sz.SizesMain := Formalism.FourierDecayAlt.P.size_bounds_conclusion
theorem sz_tcritLower : Formalism.FourierDecayAlt.Sz.TcritLower := Formalism.FourierDecayAlt.P.critical_threshold_lower_bound
theorem lemma_b_norm_of_parts : Formalism.FourierDecayAlt.B2.LemmaBNormFromParts := Formalism.FourierDecayAlt.P.lemma_b_normalised_of_parts
theorem lemma_b_from_norm_bound : Formalism.FourierDecayAlt.B2.LemmaBAnyFromNorm := Formalism.FourierDecayAlt.P.lemma_b_any_measure_from_normalised
theorem compact_conjugation : Formalism.FourierDecayAlt.B2.CompactConj := Formalism.FourierDecayAlt.P.compact_subgroup_conjugation
theorem dilation_jacobian_formula : Formalism.FourierDecayAlt.B2.DilJacRaw := Formalism.FourierDecayAlt.P.dilation_jacobian_unipotent
theorem dilation_jacobian_all : Formalism.FourierDecayAlt.B2.DilJacAll := Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting
theorem closed_subgroup_general_linear : Formalism.FourierDecayAlt.B2.ClosedG := Formalism.FourierDecayAlt.P.unitary_group_closed
theorem closed_subgroup_unipotent_radical : Formalism.FourierDecayAlt.B2.ClosedN := Formalism.FourierDecayAlt.P.unipotent_radical_closed
theorem conjugation_invariance_all : Formalism.FourierDecayAlt.B2.ConjInvAll := Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting
theorem tc_domMinOfText : Formalism.FourierDecayAlt.TC.DomMinOfText := Formalism.FourierDecayAlt.P.domination_minimum_of_text
theorem tc_theoremAAfter : Formalism.FourierDecayAlt.TC.TheoremAAfter := Formalism.FourierDecayAlt.P.theorem_a_after
theorem tc_densLeTwo : Formalism.FourierDecayAlt.TC.DensLeTwo := Formalism.FourierDecayAlt.P.density_le_two
theorem tc_densSize : Formalism.FourierDecayAlt.TC.DensSize := Formalism.FourierDecayAlt.P.density_size
theorem tc_sumBoundMax : Formalism.FourierDecayAlt.TC.SumBoundMax := Formalism.FourierDecayAlt.P.sum_bound_max
theorem tc_recursionWithDens : Formalism.FourierDecayAlt.TC.RecursionWithDens := Formalism.FourierDecayAlt.P.recursion_with_densities
theorem tc_domScaleTop : Formalism.FourierDecayAlt.TC.DomScaleTop := Formalism.FourierDecayAlt.P.domination_scale_top
theorem tc_recHypScaleTop : Formalism.FourierDecayAlt.TC.RecHypScaleTop := Formalism.FourierDecayAlt.P.recursion_hypothesis_scale_top
theorem tc_domAfterOfLocal : Formalism.FourierDecayAlt.TC.DomAfterOfLocal := Formalism.FourierDecayAlt.P.domination_after_of_local
theorem tc_densSum : Formalism.FourierDecayAlt.TC.DensSum := Formalism.FourierDecayAlt.P.density_sum
theorem tc_densChain : Formalism.FourierDecayAlt.TC.DensChain := Formalism.FourierDecayAlt.P.density_chain
theorem jx_pSDAgree : Formalism.FourierDecayAlt.J.PSDAgree := Formalism.FourierDecayAlt.P.psd_agree
theorem jx_instSizes : Formalism.FourierDecayAlt.J.InstSizes := Formalism.FourierDecayAlt.P.instance_sizes
theorem jx_instLatticeSums : Formalism.FourierDecayAlt.J.InstLatticeSums := Formalism.FourierDecayAlt.P.instance_lattice_sums
theorem jx_sizesToRecursion : Formalism.FourierDecayAlt.J.SizesToRecursion := Formalism.FourierDecayAlt.P.sizes_to_recursion
theorem jx_globPositive : Formalism.FourierDecayAlt.J.GlobPositive := Formalism.FourierDecayAlt.P.global_positive
theorem jx_latticeSumsJoint : Formalism.FourierDecayAlt.J.LatticeSumsJoint := Formalism.FourierDecayAlt.P.lattice_sums_joint
theorem jx_scaleOk : Formalism.FourierDecayAlt.J.ScaleOk := Formalism.FourierDecayAlt.P.scaling_bound
theorem jx_phaseOk : Formalism.FourierDecayAlt.J.PhaseOk := Formalism.FourierDecayAlt.P.phaseOk_statement
theorem jx_outsideSysOk : Formalism.FourierDecayAlt.J.OutsideSysOk := Formalism.FourierDecayAlt.P.outside_systems_bound
theorem jx_outsideDomination : Formalism.FourierDecayAlt.J.OutsideDomination := Formalism.FourierDecayAlt.P.outside_domination
theorem jx_uniformMajorantOn : Formalism.FourierDecayAlt.J.UniformMajorantOn := Formalism.FourierDecayAlt.P.uniform_majorant_on
theorem jx_poissonJoint : Formalism.FourierDecayAlt.J.PoissonJoint := Formalism.FourierDecayAlt.P.poisson_joint
theorem jx_localPullback : Formalism.FourierDecayAlt.J.LocalPullback := Formalism.FourierDecayAlt.P.local_pullback
theorem jx_localUnitHeads : Formalism.FourierDecayAlt.J.LocalUnitHeads := Formalism.FourierDecayAlt.P.local_unit_heads
theorem jx_topPullback : Formalism.FourierDecayAlt.J.TopPullback := Formalism.FourierDecayAlt.P.top_pullback
theorem jx_axiomsFromSystems : Formalism.FourierDecayAlt.J.AxiomsFromSystems := Formalism.FourierDecayAlt.P.axioms_from_systems
theorem jx_globalOfLocal : Formalism.FourierDecayAlt.J.GlobalOfLocal := Formalism.FourierDecayAlt.P.global_of_local
theorem jx_axiomsFromFamilies : Formalism.FourierDecayAlt.J.AxiomsFromFamilies := Formalism.FourierDecayAlt.P.axioms_from_families
theorem jx_kernelOfLocal : Formalism.FourierDecayAlt.J.KernelOfLocal := Formalism.FourierDecayAlt.P.kernel_of_local
theorem jx_poissonStepJoint : Formalism.FourierDecayAlt.J.PoissonStepJoint := Formalism.FourierDecayAlt.P.poisson_level_joint
theorem jx_xIsLamOne : Formalism.FourierDecayAlt.J.XIsLamOne := Formalism.FourierDecayAlt.P.lattice_x_eq_lambda_one
theorem jx_frameProducts : Formalism.FourierDecayAlt.J.FrameProducts := Formalism.FourierDecayAlt.P.frame_product_identities
theorem jx_schurProduct : Formalism.FourierDecayAlt.J.SchurProduct := Formalism.FourierDecayAlt.P.schur_product
theorem jx_productDomination : Formalism.FourierDecayAlt.J.ProductDomination := Formalism.FourierDecayAlt.P.product_domination
theorem jx_diagScale : Formalism.FourierDecayAlt.J.DiagScale := Formalism.FourierDecayAlt.P.diagonal_scaling
theorem jx_productLemma : Formalism.FourierDecayAlt.J.ProductLemma := Formalism.FourierDecayAlt.P.product_lemma
theorem jx_localKernelPSD : Formalism.FourierDecayAlt.J.LocalKernelPSD := Formalism.FourierDecayAlt.P.local_kernel_psd
theorem jx_formGivesMain : Formalism.FourierDecayAlt.J.FormGivesMain := Formalism.FourierDecayAlt.P.form_gives_theorem_A
theorem integral_norm_bound_variant_b : Formalism.FourierDecayAlt.B2.IntNormB := Formalism.FourierDecayAlt.P.normalisation_unique_every_setting
theorem integral_bound_all : Formalism.FourierDecayAlt.B2.CCIntAll := Formalism.FourierDecayAlt.P.matrix_coefficient_integrable_all
theorem jx_topUnitHeads : Formalism.FourierDecayAlt.J.TopUnitHeads := Formalism.FourierDecayAlt.P.top_unit_heads
theorem jx_diagPhase : Formalism.FourierDecayAlt.J.DiagPhase := Formalism.FourierDecayAlt.P.diagonal_phase_conj
theorem jx_blockDiagPSD : Formalism.FourierDecayAlt.J.BlockDiagPSD := Formalism.FourierDecayAlt.P.block_diagonal_psd
theorem pb_loopsGiveRows : Formalism.FourierDecayAlt.PB.LoopsGiveRows := Formalism.FourierDecayAlt.P.loops_give_series
theorem pb_loopsJoint : Formalism.FourierDecayAlt.PB.LoopsJoint := Formalism.FourierDecayAlt.P.loops_joint
theorem pn_normBound : Formalism.FourierDecayAlt.PN.NormBound := Formalism.FourierDecayAlt.P.pn_norm_bound
theorem pn_framePassage : Formalism.FourierDecayAlt.PN.FramePassage := Formalism.FourierDecayAlt.P.frame_passage
theorem pn_normRe : Formalism.FourierDecayAlt.PN.NormRe := Formalism.FourierDecayAlt.P.norm_real_part
theorem pn_meanAmpJoint : Formalism.FourierDecayAlt.PN.MeanAmpJoint := Formalism.FourierDecayAlt.P.mean_amplitude_joint
theorem pn_classSquaresSum : Formalism.FourierDecayAlt.PN.ClassSquaresSum := Formalism.FourierDecayAlt.P.class_squares_sum
theorem pn_classCS : Formalism.FourierDecayAlt.PN.ClassCS := Formalism.FourierDecayAlt.P.class_cauchy_schwarz
theorem pn_firstBracket : Formalism.FourierDecayAlt.PN.FirstBracket := Formalism.FourierDecayAlt.P.first_bracket
theorem pn_secondBracket : Formalism.FourierDecayAlt.PN.SecondBracket := Formalism.FourierDecayAlt.P.second_bracket
theorem pn_rowFromClasses : Formalism.FourierDecayAlt.PN.RowFromClasses := Formalism.FourierDecayAlt.P.line_from_classes
theorem pn_rowNGAbstract : Formalism.FourierDecayAlt.PN.RowNGAbstract := Formalism.FourierDecayAlt.P.line_norm_abstract
theorem pn_exponentSum : Formalism.FourierDecayAlt.PN.ExponentSum := Formalism.FourierDecayAlt.P.exponent_sum
theorem pn_nGNumbers : Formalism.FourierDecayAlt.PN.NGNumbers := Formalism.FourierDecayAlt.P.norm_numbers
theorem pn_rowNGJoint : Formalism.FourierDecayAlt.PN.RowNGJoint := Formalism.FourierDecayAlt.P.line_norm_joint
theorem jf_psiOnto : Formalism.FourierDecayAlt.JF.PsiOnto := Formalism.FourierDecayAlt.P.psiOnto_true
theorem jf_jqSmooth : Formalism.FourierDecayAlt.JF.JqSmooth := Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates
theorem d_ptPermSpec : Formalism.FourierDecayAlt.D.PtPermSpec := Formalism.FourierDecayAlt.P.ptPerm_spec
theorem d_ptGSpec : Formalism.FourierDecayAlt.D.PtGSpec := Formalism.FourierDecayAlt.P.ptG_spec
theorem d_ptRelevant : Formalism.FourierDecayAlt.D.PtRelevant := Formalism.FourierDecayAlt.P.relevant_points_holds
theorem d_muNHaar : Formalism.FourierDecayAlt.D.MuNHaar := Formalism.FourierDecayAlt.P.nilpotent_measure_is_haar
theorem ma_modelFrameAn : Formalism.FourierDecayAlt.MA.ModelFrameAn := Formalism.FourierDecayAlt.P.model_frame_analytic
theorem jc_propGramOfPlaces : Formalism.FourierDecayAlt.JC.PropGramOfPlaces := Formalism.FourierDecayAlt.P.gram_proposition_of_places
theorem jc_gramPlaceBuilt : Formalism.FourierDecayAlt.JC.GramPlaceBuilt := Formalism.FourierDecayAlt.P.gram_at_built_place
theorem jc_orbJCutScalar : Formalism.FourierDecayAlt.JC.OrbJCutScalar := Formalism.FourierDecayAlt.P.orbital_integral_cutoff_scalar
theorem d_muRHaar : Formalism.FourierDecayAlt.D.MuRHaar := Formalism.FourierDecayAlt.P.radial_measure_is_haar
theorem tbb_stepOne : Formalism.FourierDecayAlt.TBB.StepOne := Formalism.FourierDecayAlt.P.lemma_s_induction_base
theorem tbb_stepUp : Formalism.FourierDecayAlt.TBB.StepUp := Formalism.FourierDecayAlt.P.lemma_s_induction_up
theorem tbb_lemmaSOfSteps : Formalism.FourierDecayAlt.TBB.LemmaSOfSteps := Formalism.FourierDecayAlt.P.lemma_s_of_parts
theorem tbb_ptBoundOfCorS : Formalism.FourierDecayAlt.TBB.PtBoundOfCorS := Formalism.FourierDecayAlt.P.point_bound_of_corollary_s
theorem tbb_thmBpOfParts : Formalism.FourierDecayAlt.TBB.ThmBpOfParts := Formalism.FourierDecayAlt.P.theorem_b_of_parts

end Formalism.FourierDecayAlt.Final
