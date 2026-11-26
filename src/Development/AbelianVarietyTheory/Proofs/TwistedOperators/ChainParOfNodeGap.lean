module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianParamOppositeSignEntriesDistGeGap
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare

namespace GlobalTheory.Chain.ParOfSizes

section HC

variable {R : Ranks} (P : HCParam R) {h₀ : ℝ}

theorem b_le_of_le {i j : Fin R.m} (h : i.1 ≤ j.1) : P.b i ≤ P.b j := by
  rcases h.lt_or_eq with hlt | heq
  ·
    have h1 := gap_of_lt P hlt
    have h2 := gap_of_le P (le_refl i.1)
    have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
    linarith
  · exact le_of_eq (congrArg P.b (Fin.ext heq))

theorem le_b_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    {i j : Fin R.m} (h : i.1 < j.1) : h₀ ≤ ((P.b j - P.b i : ℚ) : ℝ) := by
  have hi : i.1 + 1 < R.m := by omega

  have hstep := hg i.1 hi
  have hmono : P.b ⟨i.1 + 1, hi⟩ ≤ P.b j := b_le_of_le P (show i.1 + 1 ≤ j.1 by omega)
  have hq : (P.b ⟨i.1 + 1, hi⟩ - P.b ⟨i.1, by omega⟩ : ℚ) ≤ P.b j - P.b i := by
    have e : (⟨i.1, by omega⟩ : Fin R.m) = i := Fin.ext rfl
    rw [e]
    linarith
  exact hstep.trans (by exact_mod_cast hq)

theorem hermitianParam_oppositeSign_entries_dist_ge_gap (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (x y : Idx R j) (hx : sgn R j x = false) (hy : sgn R j y = true) :
    h₀ ≤ |((val P j x - val P j y : ℚ) : ℝ)| := by
  rw [← Rat.cast_abs]
  rcases x with a | i | a
  · simp [sgn] at hx
  · simp only [sgn, decide_eq_false_iff_not, not_or, not_le] at hx
    obtain ⟨hij, hodd⟩ := hx
    have hi1 : i.1 - 1 < R.m := by omega
    rcases y with c | i2 | ⟨⟨i2, hi2⟩, a⟩
    ·
      have h1 := neg_b_lt_v P c ⟨i.1 - 1, hi1⟩
      have h2 := le_b_sub P hg (i := ⟨i.1 - 1, hi1⟩) (j := i) (show i.1 - 1 < i.1 by omega)
      refine h2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
    · simp only [sgn, decide_eq_true_eq] at hy
      rcases lt_trichotomy i2.1 i.1 with h2 | h2 | h2
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        rw [abs_sub_comm]
        exact le_abs.mpr (Or.inl (by linarith))
      · exfalso
        rw [h2] at hy
        rcases hy with hy | hy
        · omega
        · exact hodd hy
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        exact le_abs.mpr (Or.inl (by linarith))
    ·
      have hi3 : i2.1 + 1 < R.m := by omega
      have g1 := gap_of_lt P (i := i2) (j := ⟨i2.1 + 1, hi3⟩) (show i2.1 < i2.1 + 1 by omega)
      have g2 := le_b_sub P hg (i := ⟨i2.1 + 1, hi3⟩) (j := i) (show i2.1 + 1 < i.1 by omega)
      have ha0 : (0 : ℚ) ≤ (a.1 : ℚ) := Nat.cast_nonneg _
      have ha1 : (a.1 : ℚ) + 1 ≤ R.t := by exact_mod_cast a.2
      refine g2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
  · simp [sgn] at hx

theorem le_val_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (c : ℚ) (x y : Idx R j) (h : sgn R j x ≠ sgn R j y) :
    h₀ ≤ |(((val P j x + c) - (val P j y + c) : ℚ) : ℝ)| := by
  rw [add_sub_add_right_eq_sub]
  by_cases hx : sgn R j x = false
  · have hy : sgn R j y = true := by
      cases hy' : sgn R j y
      · exact absurd (hx.trans hy'.symm) h
      · rfl
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j x y hx hy
  · have hx' : sgn R j x = true := by simpa using hx
    have hy : sgn R j y = false := by
      cases hy' : sgn R j y
      · rfl
      · exact absurd (hx'.trans hy'.symm) h
    rw [← neg_sub, Rat.cast_neg, abs_neg]
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j y x hy hx'

end HC

end GlobalTheory.Chain.ParOfSizes

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes

namespace GlobalTheory.Chain.ParOfNodeGap

theorem minSig_lamS_le {D : D7} (k : Fin D.R.m) (τ : D.what₂.Tau) : minSig (lamS D k τ) ≤ D.R.m := by
  unfold minSig
  refine (min_le_right _ _).trans ?_
  calc ((lamS D k τ).filter fun x => x.2 = false).card
      ≤ (Finset.univ.image fun i : Fin D.R.m =>
          ((val (D.hc τ) (k : ℕ) (Sum.inr (Sum.inl i)) + (D.hc τ).e k : ℚ), false)).card := by
        apply Finset.card_le_card
        rintro ⟨a, s⟩ hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hx, hs⟩ := hx
        simp only at hs
        subst hs
        obtain ⟨y, hy, hsy⟩ := (mem_lamS k τ a false).1 hx
        rcases y with y | y | y
        · simp [sgn] at hsy
        · exact Finset.mem_image.2 ⟨y, Finset.mem_univ _, by rw [hy]⟩
        · simp [sgn] at hsy
    _ ≤ (Finset.univ : Finset (Fin D.R.m)).card := Finset.card_image_le
    _ = D.R.m := by simp

theorem num_bound' {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 2 ≤ m) (hN : 3 * m ^ 2 ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 * (N : ℝ) ^ 3 := by
  have hqm : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ (2 : ℕ) := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
        positivity
      · rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le
        · exact Nat.one_le_cast.mpr h
        · norm_num
    refine h1.trans ?_
    have : (q : ℝ) ≤ m := by exact_mod_cast hq
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hNR : 3 * (m : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hN12 : (12 : ℝ) ≤ N := by nlinarith
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 :=
        mul_le_mul (by linarith) hqm hpos (by positivity)
    _ ≤ 120 * (N : ℝ) * ((N : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 40 * (N : ℝ) ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (by linarith : (0 : ℝ) ≤ N - 10)]

private theorem le_sub_b_succ_of_nodeGap {D : D7} {h : ℝ} (H : D.NodeGap h) (τ : D.what₂.Tau) :
    ∀ (i : ℕ) (hi : i + 1 < D.R.m), h ≤ (((D.hc τ).b ⟨i + 1, hi⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
  intro i hi
  have := H D.u₀ τ i hi
  rwa [D.hcW_base] at this

private theorem rankY_le_N (D : D7) {j : ℕ} (hj : j ≤ D.R.m) : D.R.rankY j ≤ D.R.N D.R.m := by
  have h1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul hj le_rfl
  simp only [Ranks.rankY, Ranks.r, Ranks.N]
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem three_mul_m_sq_le_N (D : D7) : 3 * D.R.m ^ 2 ≤ D.R.N D.R.m := by
  have h1 : 3 * D.R.m + 1 ≤ D.R.t := D.R.three_m_lt_t
  have h2 : D.R.m * (3 * D.R.m + 1) ≤ D.R.m * D.R.t := Nat.mul_le_mul le_rfl h1
  simp only [Ranks.N]
  nlinarith

theorem stepGap_of_nodeGap {D : D7} (h : D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6))
    (k : Fin D.R.m) : StepGap D k := by
  set H : ℝ := 4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6 with hH
  have hg := le_sub_b_succ_of_nodeGap h
  have hNpos : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcube : ∀ j : ℕ, j ≤ D.R.m → ((D.R.rankY j : ℕ) : ℝ) ^ 3 < H := by
    intro j hj
    have : ((D.R.rankY j : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := by exact_mod_cast rankY_le_N D hj
    have : ((D.R.rankY j : ℕ) : ℝ) ^ 3 ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) this 3
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    nlinarith [pow_nonneg hNpos 3]
  intro τ
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    refine le_trans ?_ (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
    have hb := num_bound' (minSig_lamS_le k τ) (rankY_le_N D k.isLt.le) D.R.two_le_m (three_mul_m_sq_le_N D)
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith

theorem chainPar_of_nodeGap :
    ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) → ∀ k, GlobalTheory.Chain.ChainPar D k := by
  intro D h k
  exact (chainPar_iff_stepGap k).mpr (stepGap_of_nodeGap h k)

end GlobalTheory.Chain.ParOfNodeGap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
noncomputable section

namespace GlobalTheory.LiftPole

open scoped Topology
open NumberField IsDedekindDomain Filter GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

theorem isOpen_re_gt (σ : ℝ) : IsOpen {s : ℂ | σ < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem hasSimplePole_of {Λ G : ℂ → ℂ} {s₀ : ℂ} (hG : AnalyticAt ℂ G s₀) (h0 : G s₀ ≠ 0)
    (h : ∀ᶠ s in 𝓝[≠] s₀, Λ s = (s - s₀)⁻¹ * G s) : HasSimplePole Λ s₀ := by
  have hM : MeromorphicAt (fun s => (s - s₀)⁻¹ * G s) s₀ :=
    ((analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun s : ℂ => s - s₀) s₀).meromorphicAt.inv).mul
      hG.meromorphicAt
  have hΛ : MeromorphicAt Λ s₀ := hM.congr (h.mono fun s hs => hs.symm)
  refine ⟨hΛ, ?_, G s₀, h0, ?_⟩
  · rw [meromorphicOrderAt_eq_int_iff hΛ]
    refine ⟨G, hG, h0, h.mono fun s hs => ?_⟩
    rw [hs, zpow_neg_one, smul_eq_mul]
  · have hc : Tendsto G (𝓝[≠] s₀) (𝓝 (G s₀)) := hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [h, self_mem_nhdsWithin] with s hs hne
    rw [hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), one_mul]

section ZetaNonvanishing₂

variable {K : Type} [Field K] [NumberField K] {T : Set (HeightOneSpectrum (𝓞 K))}

theorem isZetaCont_of_entire {Y : ℂ → ℂ} (hY : Differentiable ℂ Y)
    (h : ∀ s : ℂ, 1 < s.re → Y s = (s - 1) * zetaOff T s) : IsZetaCont T fun s => (s - 1)⁻¹ * Y s := by
  refine ⟨fun x _ => ?_, fun s hs => ?_⟩
  · exact ((analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun s : ℂ => s - 1) x).meromorphicAt.inv).mul
      (hY.analyticAt x).meromorphicAt
  · have hne : s - 1 ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h1
      linarith
    simp only [h s hs, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem eventuallyEq_of_isZetaCont {Z Z' : ℂ → ℂ} (h : IsZetaCont T Z) (h' : IsZetaCont T Z') (x : ℂ) :
    ∀ᶠ s in 𝓝[≠] x, Z s = Z' s := by
  have hM : MeromorphicOn (Z - Z') Set.univ := fun y _ => (h.1 y trivial).sub (h'.1 y trivial)
  have h2 : meromorphicOrderAt (Z - Z') 2 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hU : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := (isOpen_re_gt 1).mem_nhds (by norm_num [Set.mem_ofPred_eq])
    filter_upwards [nhdsWithin_le_nhds hU] with s hs
    simp [h.2 s hs, h'.2 s hs]
  have hx : meromorphicOrderAt (Z - Z') x = ⊤ := by
    by_contra hne
    exact hM.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ trivial trivial hne h2
  rw [meromorphicOrderAt_eq_top_iff] at hx
  filter_upwards [hx] with s hs
  simp only [Pi.sub_apply, sub_eq_zero] at hs
  exact hs

theorem bounded_one : Bounded T (fun _ => {1}) 1 0 := by
  intro w _
  refine ⟨by simp, fun b hb => ?_⟩
  simp only [Multiset.mem_singleton] at hb
  subst hb
  simp

theorem analyticAt_zetaOff {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (zetaOff T) s := by
  have hd : DifferentiableOn ℂ (zetaOff T) {s : ℂ | (0 : ℝ) + 1 < s.re} := (bounded_one (T := T)).differentiableOn
  have hU : {s : ℂ | (0 : ℝ) + 1 < s.re} ∈ 𝓝 s := (isOpen_re_gt _).mem_nhds (by simpa using hs)
  exact hd.analyticAt hU

theorem bounded_segFam (t : ℕ) : Bounded T (segFam 1 t) t (((t : ℝ) - 1) / 2) := by
  intro w _
  have hN : (1 : ℝ) ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast (one_lt_absNorm w).le
  refine ⟨by simp [segFam], fun b hb => ?_⟩
  simp only [segFam, seg, Multiset.mem_map, Finset.mem_val, Finset.mem_range] at hb
  obtain ⟨i, _, rfl⟩ := hb
  have hre : (((t : ℂ) - 1) / 2 - (i : ℂ)).re = ((t : ℝ) - 1) / 2 - i := by
    rw [show ((t : ℂ) - 1) / 2 - (i : ℂ) = ((((t : ℝ) - 1) / 2 - i : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  simp only [Pi.one_apply, one_mul, coe_npowU, norm_npow, hre]
  exact Real.rpow_le_rpow_of_exponent_le hN (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])

theorem Bounded.mono {c : Fam K} {r : ℕ} {κ κ' : ℝ} (h : Bounded T c r κ) (hκ : κ ≤ κ') : Bounded T c r κ' :=
  fun w hw => ⟨(h w hw).1, fun b hb => ((h w hw).2 b hb).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (one_lt_absNorm w).le) hκ)⟩

theorem one_lt_re_shift {t i : ℕ} (hi : i < t) {s : ℂ} (hs : ((t : ℝ) + 1) / 2 < s.re) :
    1 < (s + ((t : ℂ) - 1) / 2 - i).re := by
  have hre : (s + ((t : ℂ) - 1) / 2 - i).re = s.re + (((t : ℝ) - 1) / 2 - i) := by
    rw [show s + ((t : ℂ) - 1) / 2 - i = s + ((((t : ℝ) - 1) / 2 - i : ℝ) : ℂ) by push_cast; ring,
      Complex.add_re, Complex.ofReal_re]
  have hit : (i : ℝ) + 1 ≤ t := by exact_mod_cast hi
  rw [hre]
  linarith

theorem eulerProd_segFam {t : ℕ} {s : ℂ} (hs : ((t : ℝ) + 1) / 2 < s.re) :
    eulerProd T (segFam 1 t) s = ∏ i ∈ Finset.range t, zetaOff T (s + ((t : ℂ) - 1) / 2 - i) := by
  have hp : HasProd (fun w : {w // w ∉ T} =>
      ∏ i ∈ Finset.range t, locL (fun _ => {1}) w.1 (s + ((t : ℂ) - 1) / 2 - i))
      (∏ i ∈ Finset.range t, zetaOff T (s + ((t : ℂ) - 1) / 2 - i)) :=
    hasProd_prod fun i hi => (converges_zeta T (one_lt_re_shift (Finset.mem_range.mp hi) hs)).hasProd
  have he : (fun w : {w // w ∉ T} => locL (segFam 1 t) w.1 s) =
      fun w => ∏ i ∈ Finset.range t, locL (fun _ => {1}) w.1 (s + ((t : ℂ) - 1) / 2 - i) := by
    funext w
    rw [locL_segFam']
    rfl
  rw [show eulerProd T (segFam 1 t) s = ∏' w : {w // w ∉ T}, locL (segFam 1 t) w.1 s from rfl, he]
  exact hp.tprod_eq

end ZetaNonvanishing₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_above {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Finite) : (above E S).Finite := by
  have he : above E S = ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v} := by
    ext w
    simp [above]
  rw [he]
  exact hS.biUnion fun v _ => Formalism.L2.Host.finite_aboveF (L := E) F v

theorem simplePole_of_hecke (hH : GlobalTheory.Published.HeckeLPartialContinuation) : SimplePole := by
  intro F E _ _ _ _ _ S r t c P m x hyp
  obtain ⟨hS, hrt, hw⟩ := hyp
  have hm1 : ∀ w ∉ above E S, ‖((m⁻¹ w : ℂˣ) : ℂ)‖ = 1 := fun w hw' => by
    simp [(hw w hw').2.2.1]
  have hbc : Bounded (above E S) (twist c m⁻¹) r (((r : ℝ) - 1) / 2) :=
    Bounded.twist (fun w hw' => ⟨(hw w hw').1.le, (hw w hw').2.1⟩) hm1
  have hrt' : (r : ℝ) + 5 ≤ t := by exact_mod_cast hrt
  have hbs : Bounded (above E S) (segFam 1 t) t (((t : ℝ) - 1) / 2) := bounded_segFam t
  have hbc' : Bounded (above E S) (twist c m⁻¹) r (((t : ℝ) - 1) / 2) := Bounded.mono hbc (by linarith)
  have hbsum := hbc'.add hbs
  have htw : ∀ w ∉ above E S, twist P x⁻¹ w = (twist c m⁻¹ + segFam 1 t : Fam E) w := fun w hw' => by
    rw [← congrFun (twist_liftFam c m x t) w]
    simp only [twist, (hw w hw').2.2.2.2]
  have hA : ∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re →
      Converges (above E S) (twist P x⁻¹) s ∧
      (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧
      LSTw S P x s = rhs S c m t (zetaOff (above E S)) s := by
    intro s hs
    have hs' : ((t : ℝ) - 1) / 2 + 1 < s.re := by linarith
    have hcs : Converges (above E S) (twist c m⁻¹ + segFam 1 t) s := hbsum.converges hs'
    refine ⟨hcs.congr fun w hw' => (htw w hw').symm, fun i hi => converges_zeta _ (one_lt_re_shift hi hs), ?_⟩
    have hc1 : Converges (above E S) (twist c m⁻¹) s := hbc'.converges hs'
    have hc2 : Converges (above E S) (segFam 1 t) s := hbs.converges hs'
    show eulerProd (above E S) (twist P x⁻¹) s = eulerProd (above E S) (twist c m⁻¹) s *
      ∏ i ∈ Finset.range t, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)
    rw [eulerProd_congr htw, eulerProd_add hc1 hc2, eulerProd_segFam hs]
  have hr : ((r : ℝ) - 1) / 2 + 1 = ((r : ℝ) + 1) / 2 := by ring
  have hB : (∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧
      DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re} := by
    refine ⟨fun s hs => ?_, ?_⟩
    · have h1 : Converges (above E S) (twist c m⁻¹) s := hbc.converges (by rw [hr]; exact hs)
      exact ⟨h1, h1.ne_zero⟩
    · have h1 := hbc.differentiableOn
      rw [hr] at h1
      exact h1
  obtain ⟨Z0, hZ0d, hZ0eq, hZ0ne⟩ := (hH E (above E S) (finite_above hS)).2
  refine ⟨hA, hB, ⟨_, isZetaCont_of_entire hZ0d hZ0eq⟩, fun Z hZ => ?_⟩
  have hZeq : ∀ u : ℂ, 1 < u.re → Z u = zetaOff (above E S) u := hZ.2
  have hs₀re : ((1 + (t : ℂ)) / 2).re = (1 + (t : ℝ)) / 2 := by
    rw [show (1 + (t : ℂ)) / 2 = (((1 + (t : ℝ)) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  refine ⟨fun s hs => ?_, by rw [hs₀re]; linarith, fun s hs => ?_, ?_⟩
  · have hU : {s : ℂ | ((r : ℝ) + 1) / 2 < s.re} ∈ 𝓝 s := (isOpen_re_gt _).mem_nhds hs
    have h1 : MeromorphicAt (LSTw S c m) s := (hB.2.analyticAt hU).meromorphicAt
    have h2 : MeromorphicAt (fun s => ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)) s := by
      refine MeromorphicAt.fun_prod fun i _ => ?_
      have hg : AnalyticAt ℂ (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i) s := by fun_prop
      exact (hZ.1 _ trivial).comp_analyticAt hg
    exact h1.mul h2
  · rw [(hA s hs).2.2]
    show LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i) =
      LSTw S c m s * ∏ i ∈ Finset.range t, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)
    congr 1
    exact Finset.prod_congr rfl fun i hi => hZeq _ (one_lt_re_shift (Finset.mem_range.mp hi) hs)
  · have hcast : ((t - 1 : ℕ) : ℂ) = (t : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
    have hid : ∀ u : ℂ, u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ) - 1 = u - (1 + (t : ℂ)) / 2 := by
      intro u
      rw [hcast]
      ring
    have hsh0 : (1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ) = 1 := by
      rw [hcast]
      ring
    have hre0 : ∀ i : ℕ, ((1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - i).re = (t : ℝ) - i := by
      intro i
      rw [show (1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - i = (((t : ℝ) - i : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    have hlt : ∀ i ∈ Finset.range t \ {t - 1}, 1 < ((1 + (t : ℂ)) / 2 + ((t : ℂ) - 1) / 2 - i).re := by
      intro i hi
      rw [hre0]
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
      obtain ⟨hi1, hi2⟩ := hi
      have h2 : (i : ℝ) + 2 ≤ t := by exact_mod_cast (by omega : i + 2 ≤ t)
      linarith
    have hmem : t - 1 ∈ Finset.range t := Finset.mem_range.mpr (by omega)
    have hE1 : ∀ᶠ s in 𝓝 ((1 + (t : ℂ)) / 2), ∀ i ∈ Finset.range t \ {t - 1},
        Z (s + ((t : ℂ) - 1) / 2 - i) = zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i) := by
      rw [Filter.eventually_all_finset]
      intro i hi
      have hc : Continuous (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i) := by fun_prop
      filter_upwards [(hc.tendsto _).eventually ((isOpen_re_gt 1).mem_nhds (hlt i hi))] with u hu
      exact hZeq _ hu
    have hZZ0 := eventuallyEq_of_isZetaCont hZ (isZetaCont_of_entire hZ0d hZ0eq) 1
    have hc' : Continuous (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ)) := by fun_prop
    have htend : Tendsto (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ))
        (𝓝[≠] ((1 + (t : ℂ)) / 2)) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h1 := hc'.tendsto ((1 + (t : ℂ)) / 2)
        rw [hsh0] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with u hu
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hu ⊢
        intro heq
        apply hu
        have h1 := hid u
        rw [heq, sub_self] at h1
        exact sub_eq_zero.mp h1.symm
    have hE2 := htend.eventually hZZ0
    have hU : {s : ℂ | ((r : ℝ) + 1) / 2 < s.re} ∈ 𝓝 ((1 + (t : ℂ)) / 2) :=
      (isOpen_re_gt _).mem_nhds (by simp only [Set.mem_ofPred_eq]; rw [hs₀re]; linarith)
    have hA0 : AnalyticAt ℂ (LSTw S c m) ((1 + (t : ℂ)) / 2) := hB.2.analyticAt hU
    have hQ : AnalyticAt ℂ (fun s => ∏ i ∈ Finset.range t \ {t - 1},
        zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)) ((1 + (t : ℂ)) / 2) := by
      refine Finset.analyticAt_fun_prod _ fun i hi => ?_
      have hg : AnalyticAt ℂ (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i) ((1 + (t : ℂ)) / 2) := by fun_prop
      exact AnalyticAt.comp (f := fun u : ℂ => u + ((t : ℂ) - 1) / 2 - i)
        (analyticAt_zetaOff (K := E) (T := above E S) (hlt i hi)) hg
    have hZt : AnalyticAt ℂ (fun s => Z0 (s + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ))) ((1 + (t : ℂ)) / 2) := by
      have hg : AnalyticAt ℂ (fun u : ℂ => u + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ)) ((1 + (t : ℂ)) / 2) := by
        fun_prop
      exact (hZ0d.analyticAt _).comp hg
    have hGan : AnalyticAt ℂ (fun s => LSTw S c m s *
        (∏ i ∈ Finset.range t \ {t - 1}, zetaOff (above E S) (s + ((t : ℂ) - 1) / 2 - i)) *
        Z0 (s + ((t : ℂ) - 1) / 2 - ((t - 1 : ℕ) : ℂ))) ((1 + (t : ℂ)) / 2) :=
      (hA0.fun_mul hQ).fun_mul hZt
    refine hasSimplePole_of (Λ := rhs S c m t Z) (s₀ := (1 + (t : ℂ)) / 2) hGan ?_ ?_
    · refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact (hB.1 _ (by rw [hs₀re]; linarith)).2
      · exact Finset.prod_ne_zero_iff.mpr fun i hi => (converges_zeta _ (hlt i hi)).ne_zero
      · rw [hsh0]
        exact hZ0ne 1 (by simp)
    · filter_upwards [nhdsWithin_le_nhds hE1, hE2] with s hs1 hs2
      unfold rhs
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hmem, hs2, Finset.prod_congr rfl hs1, hid s]
      ring

end GlobalTheory.LiftPole

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParamRegularCardMinusCount
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParamRegularCardMinusCount
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Finset
open GlobalTheory.SignedHC

namespace GlobalTheory.PiCounts

variable {G : GridData}

theorem a_injective (hg : 0 < G.ga) : Function.Injective G.a := by
  intro i j h
  have e := G.a_sub_a i j
  rw [h, sub_self] at e
  have hg' : (G.ga : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have : ((j : ℚ) - i) = 0 := by
    rcases mul_eq_zero.1 e.symm with h | h
    · exact h
    · exact absurd h hg'
  have : (j : ℚ) = i := by linarith
  exact_mod_cast this.symm

theorem a_anti {i j : ℕ} (h : i ≤ j) : G.a j ≤ G.a i := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · have : (0 : ℚ) ≤ G.ga := by positivity
    linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h]

theorem card_tops (hg : 0 < G.ga) : G.tops.card = G.m + 1 := by
  rw [GridData.tops, card_image_of_injective _ (a_injective hg), card_range]

theorem card_cloudHalf : G.cloudHalf.card = G.k - 1 := by
  rw [GridData.cloudHalf, card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i hi j hj h
    have hi := mem_Icc.1 (mem_coe.1 hi)
    have hj := mem_Icc.1 (mem_coe.1 hj)
    have e : G.v i = G.v j := by
      have : (G.v i : ℚ) = G.v j := by simp only [GridData.vHalf] at h; linarith
      exact_mod_cast this
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd e (G.v_anti i j hi.1 h' hj.2).ne'
    · exact h'
    · exact absurd e (G.v_anti j i hj.1 h' hi.2).ne

theorem card_Cs' (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    ((Icc (G.m - i + 1) G.m).biUnion G.blockC').card = i * (G.s - 1) := by
  rw [card_biUnion]
  · have : ∀ u ∈ Icc (G.m - i + 1) G.m, (G.blockC' u).card = G.s - 1 := fun u _ => card_block _ _
    rw [sum_congr rfl this, sum_const, Nat.card_Icc, smul_eq_mul]
    congr 1
    omega
  · intro u hu v hv huv
    have hu := mem_Icc.1 (mem_coe.1 hu)
    have hv := mem_Icc.1 (mem_coe.1 hv)
    refine disjoint_left.2 fun x h1 h2 => ?_
    have b1 := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h1
    have b2 := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hv.2 h2
    rcases lt_or_gt_of_ne huv with h | h <;>
      linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h, b1.1, b1.2, b2.1, b2.2]

theorem card_entries_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    (SignedHC.entries (G.parPi i)).card = G.rankP i := by
  have hg0 : 0 < G.ga := by omega
  have d1 : Disjoint G.tops G.cloudHalf := disjoint_left.2 fun x h1 h2 => by
    obtain ⟨l, hl, rfl⟩ := GridData.mem_tops.1 h1
    linarith [GlobalTheory.ChiGrid.cloudHalf_lt h2, a_anti (G := G) hl]
  have d2 : Disjoint (G.tops ∪ G.cloudHalf) ((Icc (G.m - i + 1) G.m).biUnion G.blockC') :=
    disjoint_left.2 fun x h1 h2 => by
      obtain ⟨u, hu, h2⟩ := mem_biUnion.1 h2
      have hu := mem_Icc.1 hu
      have b := GlobalTheory.ChiGrid.blockC'_between hm hs hg (by omega) hu.2 h2
      rcases mem_union.1 h1 with h1 | h1
      · obtain ⟨l, -, rfl⟩ := GridData.mem_tops.1 h1
        rcases lt_or_ge l u with h | h
        · linarith [GlobalTheory.ChiGrid.a_add_le (G := G) h, b.2]
        · linarith [a_anti (G := G) h, b.1]
      · linarith [GlobalTheory.ChiGrid.cloudHalf_lt h1, a_anti (G := G) hu.2, b.1]
  have := G.two_le_k
  rw [GridData.entries_parPi, GridData.entries_lam, card_union_of_disjoint d2, card_union_of_disjoint d1,
    card_tops hg0, card_cloudHalf, card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]
  omega

theorem card_parPi_le {i : ℕ} (hg : 0 < G.ga) : (G.parPi i).card ≤ (G.m + 1) + (G.k - 1) +
    ((Icc (G.m - i + 1) G.m).biUnion G.blockC').card := by
  rw [GridData.parPi]
  refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact card_image_le.trans (card_range _).le
  · exact card_image_le.trans card_cloudHalf.le
  · exact card_image_le

theorem card_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    (G.parPi i).card = G.rankP i := by
  refine le_antisymm ?_ ((card_entries_parPi hm hs hg hi).symm.le.trans card_image_le)
  have := G.two_le_k
  refine (card_parPi_le (by omega)).trans ?_
  rw [card_Cs' hm hs hg hi, GridData.rankP, G.n_eq]
  omega

theorem isRegular_parPi (hm : G.NearMid) (hs : 1 ≤ G.s) (hg : G.s < G.ga) {i : ℕ} (hi : i ≤ G.m) :
    IsRegular (G.parPi i) :=
  isRegular_iff_card.2 ((card_entries_parPi hm hs hg hi).trans (card_parPi hm hs hg hi).symm)

theorem nMinus_parPi (hg : 0 < G.ga) (i : ℕ) : nMinus (G.parPi i) = (G.m - i + 1) / 2 := by
  have : (G.parPi i).filter (fun x => x.2 = false) =
      (range ((G.m - i + 1) / 2)).image fun c => (G.a (G.m - i - 1 - 2 * c), false) := by
    ext ⟨x, s⟩
    simp only [mem_filter, GridData.mem_parPi, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨l, h1, h2, h3⟩ | ⟨-, h⟩ | ⟨l, -, -, -, h⟩, rfl⟩
      · have h5 : ¬ (G.m - i ≤ l ∨ Even (G.m - i - l)) := by simpa using h3.symm
        rw [Nat.even_iff] at h5
        refine ⟨(G.m - i - l - 1) / 2, by omega, ?_, rfl⟩
        rw [show G.m - i - 1 - 2 * ((G.m - i - l - 1) / 2) = l by omega, h2]
      · simp at h
      · simp at h
    · rintro ⟨c, hc, rfl, rfl⟩
      refine ⟨Or.inl ⟨G.m - i - 1 - 2 * c, by omega, rfl, ?_⟩, rfl⟩
      symm; rw [decide_eq_false_iff_not, Nat.even_iff]; omega
  rw [nMinus, this, card_image_of_injOn, card_range]
  intro c hc c' hc' h
  simp only [coe_range, Set.mem_Iio] at hc hc'
  have h1 := a_injective hg (congrArg Prod.fst h)
  omega

end GlobalTheory.PiCounts

namespace GlobalTheory.Grid

theorem parPi_counts : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (i : ℕ), i ≤ D.R.m →
    GlobalTheory.SignedHC.IsRegular ((GlobalTheory.Grid.grid D τ).parPi i) ∧ ((GlobalTheory.Grid.grid D τ).parPi i).card = GlobalTheory.Grid.rkP D i ∧
      GlobalTheory.SignedHC.nMinus ((GlobalTheory.Grid.grid D τ).parPi i) = (D.R.m - i + 1) / 2 := by
  intro D _ τ i hi
  have hg : (grid D τ).s < (grid D τ).ga := by
    have := (isLeast_gap D).1.2.1
    show sLen D < gap D
    omega
  have hs : 1 ≤ (grid D τ).s := by show 1 ≤ D.R.r + 6; omega
  have hm := grid_nearMid D τ
  have hi' : i ≤ (grid D τ).m := hi
  refine ⟨GlobalTheory.PiCounts.isRegular_parPi hm hs hg hi', ?_, GlobalTheory.PiCounts.nMinus_parPi (by omega) i⟩
  exact (GlobalTheory.PiCounts.card_parPi hm hs hg hi').trans rfl

end GlobalTheory.Grid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParamRegularCardMinusCountStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridParam_regular_card_minusCount : ∀ (D : D7), HostHyp D → ∀ (τ : D.what₂.Tau) (i : ℕ), i ≤ D.R.m → GlobalTheory.SignedHC.IsRegular ((GlobalTheory.Grid.grid D τ).parPi i) ∧ ((GlobalTheory.Grid.grid D τ).parPi i).card = GlobalTheory.Grid.rkP D i ∧ GlobalTheory.SignedHC.nMinus ((GlobalTheory.Grid.grid D τ).parPi i) = (D.R.m - i + 1) / 2 := by
  first | exact @GlobalTheory.Grid.parPi_counts | exact GlobalTheory.Grid.parPi_counts | (intros; apply GlobalTheory.Grid.parPi_counts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorVacuumEqSmulBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorVacuumEqSmulBasePoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacuumLine

open GlobalTheory.FockCompare GlobalTheory.VacUnique

private theorem selfDual_isFullLattice {D : D7} {V : HSp D}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ) :
    Submodule.IsFullLattice D.host.E Λ := _root_.DedupShared.selfDual_isFullLattice V Λ hΛ

theorem eq_smul_base : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∃ c : ℂ, f = c • f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ hb f hf hlat hfock
  have hne : f₀ ≠ 0 := GlobalTheory.PlaceTensor.base_ne_zero hb
  obtain ⟨hS, hT, dS, dT, hψ, hθ, ht₀, hl₀, hF₀, -⟩ := hb
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  obtain ⟨ρ, hρc, hρ1, hρ2⟩ := GlobalTheory.FockCompare.exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.RealChart.exists_chart D θ hθ ρ hρc hρ1 hρ2
  obtain ⟨hdual, hdec, heig⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ dS dT
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  have hinf : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => GlobalTheory.VacUnique.latO_inf S T _ _ _ hu
  have key : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u f = ε • f ∧ heisO ψ S T u f₀ = ε • f₀ := by
    intro u hu
    obtain ⟨ε, hε, h⟩ := heig f hlat u hu
    exact ⟨ε, hε, h f hlat, h f₀ hl₀⟩
  have ext : ∀ w, ∃ z : RW T S, ∃ a : ℂ, f w = a * f (iotaW σ T S z) ∧ f₀ w = a * f₀ (iotaW σ T S z) := by
    intro w
    obtain ⟨γ, z, u, hu, rfl⟩ := GlobalTheory.VacUnique.exists_decomp hσ hdec w
    obtain ⟨ε, -, h1, h2⟩ := key u hu
    refine ⟨z, ψ (-symplOH S T (ratW T S γ) (iotaW σ T S z + u)) * ε, ?_, ?_⟩
    · rw [hf.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h1 z]; ring
    · rw [ht₀.1 γ, GlobalTheory.VacUnique.apply_real_add hσ hψ (hinf u hu) h2 z]; ring
  have hN : ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ Λ :=
    GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT
      (selfDual_isFullLattice dS) (selfDual_isFullLattice dT)
  have hLd := GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf hdual hdec hN
  obtain ⟨hJ, hanti, hinv, hpos⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  classical
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv).choose else 1
  have hc : ∀ v, ‖c v‖ = 1 := by
    intro v
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψn, one_mul]
      rcases (key _ hv).choose_spec.1 with h | h <;> rw [h] <;> simp
    · simp
  have hfd := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ hσ ψ hψ S T sS sT f hf hfock
  have hfd₀ := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ hσ ψ hψ S T sS sT f₀ ht₀ hF₀
  have hspan : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := GlobalTheory.FockCompare.span_piW_ratW_eq_top D θ σ hσ T S
    simpa [GlobalTheory.VacUnique.piW_ratW hθ] using this
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) hJ hanti hinv hpos
    (Matrix (Fin T.rank) (Fin S.rank) D.host.E) (infRat S T) (GlobalTheory.VacUnique.infRat_injective S T) hspan
    (Λ.comap (finRat S T)) (fun x => by simpa using hN x) (fun x => by simpa using hLd x) c hc
    ![fun z => f₀ (iotaW σ T S z), fun z => f (iotaW σ T S z)]
    (Fin.forall_fin_two.2 ⟨hfd₀.1, hfd.1⟩) ?fock ?quasi
  case fock => exact Fin.forall_fin_two.2 ⟨hfd₀.2, hfd.2⟩
  case quasi =>
    intro k v hv z
    have hv' : finRat S T (-v) ∈ Λ := by
      rw [map_neg]
      exact Λ.neg_mem (AddSubgroup.mem_comap.1 hv)
    have hcv : c v = ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * (key _ hv').choose := by
      simp only [c, dif_pos hv']
    obtain ⟨-, h1, h2⟩ := (key _ hv').choose_spec
    have e1 := GlobalTheory.VacUnique.apply_add_infRat hσ hψ hf v h1 z
    have e2 := GlobalTheory.VacUnique.apply_add_infRat hσ hψ ht₀ v h2 z
    have ho : (omO S T z (infRat S T v) : ℂ) = ((-omO S T (infRat S T v) z : ℝ) : ℂ) := by rw [hanti]
    rw [hcv, ho]
    fin_cases k
    · exact e2
    · exact e1
  rw [LinearIndependent.pair_iff] at hli
  push_neg at hli
  obtain ⟨s, t, hst, hne0⟩ := hli
  have hpt : ∀ z, s * f₀ (iotaW σ T S z) + t * f (iotaW σ T S z) = 0 := fun z => by
    have := congrFun hst z
    simpa using this
  by_cases ht : t = 0
  · exfalso
    have hs : s ≠ 0 := fun hs => hne0 hs ht
    apply hne
    funext w
    obtain ⟨z, a, -, h2⟩ := ext w
    have := hpt z
    rw [ht, zero_mul, add_zero] at this
    rw [h2, (mul_eq_zero.1 this).resolve_left hs]
    simp
  · refine ⟨-s / t, ?_⟩
    funext w
    obtain ⟨z, a, h1, h2⟩ := ext w
    have := hpt z
    rw [Pi.smul_apply, smul_eq_mul, h1, h2, div_mul_eq_mul_div, eq_div_iff ht]
    linear_combination a * this

end GlobalTheory.VacuumLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorVacuumEqSmulBasePointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedTensor_vacuum_eq_smul_basePoint : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∃ c : ℂ, f = c • f₀ := by
  first | exact @GlobalTheory.VacuumLine.eq_smul_base | exact GlobalTheory.VacuumLine.eq_smul_base | (intros; apply GlobalTheory.VacuumLine.eq_smul_base <;> assumption)
end
end
