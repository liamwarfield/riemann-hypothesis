module

public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV
public import Development.AutomorphicArithmetic.PrimitiveCosets.charsA
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChCore
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.lemmaL
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.TopWin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.GzEq
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.Gz_eq :
    ∀ y : ℝ, Formalism.Gz y = An.G y ∧ An.G y = Deduction.G y := by
  intro y
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / (n : ℝ) - 1)
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hy : (n : ℝ) ≤ y := by
      have hk : 0 < ⌊y⌋₊ := lt_of_lt_of_le Nat.zero_lt_one (le_trans hn.1 hn.2)
      have hy0 : 0 ≤ y := by
        by_contra hneg
        push_neg at hneg
        rw [Nat.floor_eq_zero.2 (lt_trans hneg zero_lt_one)] at hk
        exact lt_irrefl 0 hk
      exact le_trans (by exact_mod_cast hn.2) (Nat.floor_le hy0)
    have hpos : (0 : ℝ) < n := by linarith
    have : 0 ≤ y / (n : ℝ) - 1 := by
      rw [sub_nonneg, le_div_iff₀ hpos, one_mul]
      exact hy
    rw [max_eq_left this]
  have hre : (Deduction.ramp (fun _ => 1) y).re
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    rw [Finset.sum_subset hsub]
    · simp [Deduction.ramp, Complex.re_sum]
    · intro n hn hn'
      have h0 : n = 0 := by
        rw [Finset.mem_range] at hn
        rw [Finset.mem_Icc] at hn'
        omega
      subst h0
      simp
  refine ⟨?_, ?_⟩
  · simp only [Formalism.Gz, Formalism.Sz, An.G]
    rw [hsum]
    ring
  · simp only [An.G, Deduction.G]
    rw [hre]
    ring
end

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.Imports
section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypOfRpow
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem windowHyp_of_rpow_eventually (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ Y₁ : ℝ, ∀ Y : ℝ, Y₁ ≤ Y → 1 ≤ Y ∧ K * Real.log Y ≤ Y ^ η := by
  have h2 : 0 < η / 2 := by positivity
  have h1 := (tendsto_rpow_atTop h2).eventually_ge_atTop (K / (η / 2))
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1 (h1.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨Y₁, fun Y hY => ?_⟩
  obtain ⟨ha, hb⟩ := hY₁ Y hY
  refine ⟨hb, ?_⟩
  have hY0 : 0 < Y := by linarith
  have hl := Real.log_le_rpow_div hY0.le h2
  have hp : 0 ≤ Y ^ (η / 2) := by positivity
  have he : Y ^ η = Y ^ (η / 2) * Y ^ (η / 2) := by
    rw [← Real.rpow_add hY0]; congr 1; ring
  calc K * Real.log Y ≤ K * (Y ^ (η / 2) / (η / 2)) := mul_le_mul_of_nonneg_left hl hK
    _ = K / (η / 2) * Y ^ (η / 2) := by ring
    _ ≤ Y ^ (η / 2) * Y ^ (η / 2) := mul_le_mul_of_nonneg_right ha hp
    _ = Y ^ η := he.symm

theorem windowHyp_of_rpow (F : CharFamily) {θ δ C : ℝ} (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    WindowHyp F θ δ := by
  intro η hη Y₀
  obtain ⟨Y₁, hY₁⟩ := windowHyp_of_rpow_eventually (|C| * δ) η (by positivity) hη
  obtain ⟨Y, hY, hb⟩ := h (max Y₀ Y₁)
  obtain ⟨h1, hK⟩ := hY₁ Y (le_trans (le_max_right _ _) hY)
  have hY0 : 0 < Y := by linarith
  have hle : Y ≤ Y ^ (1 + δ) := by
    calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
      _ ≤ Y ^ (1 + δ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have heq : Set.EqOn (fun y : ℝ => |C| * y ^ θ * y ^ (-θ - 1)) (fun y : ℝ => |C| * y⁻¹)
      (Set.Icc Y (Y ^ (1 + δ))) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
    simp only
    rw [mul_assoc, ← Real.rpow_add hy0, show θ + (-θ - 1) = -1 by ring, Real.rpow_neg_one]
  refine ⟨Y, le_trans (le_max_left _ _) hY, fun y => |C| * y ^ θ, ?_, ?_, ?_⟩
  · refine (integrableOn_congr_fun heq measurableSet_Icc).2 ?_
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.mul (continuousOn_id.inv₀ fun y hy => (lt_of_lt_of_le hY0 hy.1).ne')
  · intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
    have hp : 0 ≤ y ^ θ := by positivity
    exact ⟨by positivity, (hb y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)⟩
  · rw [setIntegral_congr_fun measurableSet_Icc heq, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hY0 (lt_of_lt_of_le hY0 hle),
      Real.log_div (lt_of_lt_of_le hY0 hle).ne' hY0.ne', Real.log_rpow hY0]
    calc |C| * ((1 + δ) * Real.log Y - Real.log Y) = |C| * δ * Real.log Y := by ring
      _ ≤ Y ^ η := hK

end Deduction

end
end

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem zeroFree_of_rpow_window (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ)
    (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), Gm F y ≤ C * y ^ θ) :
    ZeroFree F θ :=
  lemmaL F hθ hθ1 hδ (windowHyp_of_rpow F hδ h)

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.GChiEq
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.gChi_eq_ramp (f : ℕ → ℂ) (y : ℝ) :
    Deduction.ramp f y = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (An.abelian₂ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ) := by
  unfold Deduction.ramp
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _), zero_add]
  have e : Finset.Ico 1 ⌊y⌋₊.succ = Finset.Icc 1 ⌊y⌋₊ := by
    ext n
    simp [Nat.lt_succ_iff]
  rw [e]
  simp

theorem UpperTheory.Comparison₂.gChi_eq :
    ∀ (ψ : PChar) (y : ℝ), An.gChi ψ.χ y = Deduction.Gchi ψ.χ y := by
  intro ψ y
  unfold An.gChi Deduction.Gchi
  rw [UpperTheory.Comparison₂.gChi_eq_ramp]
  by_cases h : ψ.χ = 1
  · rw [if_pos h, if_pos h]
    have hN : ψ.N = 1 := by
      have hp : ψ.χ.conductor = ψ.N := ψ.prim
      rw [h, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    have h2 : ∀ n : ℕ, ψ.χ (n : ZMod ψ.N) = 1 := fun n => by
      rw [h]
      refine MulChar.one_apply ?_
      rw [ZMod.isUnit_iff_coprime, hN]
      exact Nat.coprime_one_right n
    simp only [h2, An.G, mul_one]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    rfl
end

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.formB :
    ∀ Λ : Level, Λ.FormB := by
  intro Λ la hla θ hθ0 hθ1 hW
  classical
  let weight (ψ : PChar) : ℝ := if ψ = PChar.one then 1 else Λ.wt ψ
  have weight_pos (ψ : PChar) : 0 < weight ψ := by
    unfold weight Level.wt
    split_ifs
    · exact one_pos
    · exact one_pos
    · positivity
  have admissible (ψ : PChar) : ψ.N = 1 ∨ ψ.χ ≠ 1 := by
    by_cases h : ψ.χ = 1
    · left
      have hp := ψ.prim
      rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    · exact Or.inr h
  let F : Deduction.CharFamily :=
    @Deduction.CharFamily.mk Λ.KEPT _ (fun i => i.1.N) (fun i => i.1.ne)
      (fun i => i.1.χ) (fun i => weight i.1) (fun i => weight_pos i.1)
      (fun i => admissible i.1)
  have hG (y : ℝ) : Deduction.Gm F y = Λ.Gm y := by
    change (∑ i : Λ.KEPT, weight i.1 * (Deduction.Gchi i.1.χ y).re) = Λ.Gm y
    rw [Finset.sum_coe_sort Λ.KEPT (fun ψ => weight ψ * (Deduction.Gchi ψ.χ y).re),
      ← Finset.add_sum_erase _ _ Λ.one_mem, Level.Gm, Level.Nt]
    congr 1
    · have hGz : Formalism.Gz y = An.G y := by
        unfold Formalism.Gz Formalism.Sz An.G
        have hsum : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)) =
            ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / n - 1) 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
          have hn_pos : 0 < n := Nat.zero_lt_of_lt hn₁
          have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' hn_pos.ne').mp hn₂
          have hnonneg : 0 ≤ y / (n : ℝ) - 1 := by
            rw [sub_nonneg, le_div_iff₀ (Nat.cast_pos.mpr hn_pos), one_mul]
            exact hny
          rw [max_eq_left hnonneg]
        rw [hsum]
        ring
      rw [show weight PChar.one = 1 by simp [weight], one_mul, ← gChi_eq, hGz]
      simp only [An.gChi, PChar.one]
      exact (congrArg Complex.re (ite_eq_left rfl)).trans (Complex.ofReal_re _)
    · refine Finset.sum_congr rfl fun ψ hψ => ?_
      have hne : ψ ≠ PChar.one := Finset.ne_of_mem_erase hψ
      simp only [weight, ite_eq_right hne, gChi_eq]
  have hZ (h : Deduction.ZeroFree F θ) : Λ.ZeroFreeAbove θ := by
    intro ψ hψ s hs
    exact h ⟨ψ, hψ⟩ s hs
  apply hZ
  refine Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith) fun Y₀ => ?_
  obtain ⟨Y, hY, hx⟩ := hW Y₀
  refine ⟨Y, hY, fun y hy => ?_⟩
  have h1 : (1 : ℝ) + (la - 1) = la := by ring
  rw [h1] at hy
  rw [hG, one_mul]
  exact hx y hy.1 hy.2
end

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales
section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChTop
open Finset

noncomputable section

namespace Deduction

open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

lemma ch_top_main_eq {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (tr : U0 → H) (D : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (hId : IdentU Dd tr D N ell TT a w eT eP) (u0 : U0) :
    Dd.Main u0 = ∑ t ∈ TT, ∑ j : Fin m, (MAIN ell (a t) (w (tr u0) j)).re := by
  obtain ⟨ha, hw, hg, hL, -⟩ := hId
  have hf : (f : ℝ) = (#(PhiSet (H := H)) : ℝ) := by
    have := Fintype.card_congr eP
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    exact_mod_cast this
  have hsum : ∀ g : E0 × H → ℝ, ∑ ρ : Fin f, g (eP ρ) = ∑ x ∈ PhiSet, g x := by
    intro g
    rw [← Finset.sum_coe_sort PhiSet]
    exact Equiv.sum_comp eP (fun x => g x)
  unfold Data.Main
  simp only [ha, hw, hg, hL, hsum, hf]
  rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort TT]
  rw [← Equiv.sum_comp eT]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  simp [MAIN, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  left
  left
  exact hsum (fun x => Real.log (w (tr u0) j x))

theorem ch_top {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (tr : U0 → H) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H))
    (h1 : IdentU Dd tr D N ell TT a w eT eP) (h2 : SizeData₂ Dd C Xpp) (h3 : ErrWindows Dd C Xpp eK K) (h4 : BNBoundsU Dd T2)
    (h5 : LargeX Dd.x Dd.ε K C.cHH eK) (u : U0) :
    gapA D N ell TT a w (tr u) ≤
      Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
  have hmain := ch_top_main_eq Dd tr D N ell TT a w eT eP h1 u
  have hask := h1.2.2.2.2 u
  have hgap : gapA D N ell TT a w (tr u) = Dd.ASK u - Dd.Main u := by
    rw [hask, hmain]
    unfold gapA
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_sub_distrib]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := h2
  have hle := each_unit_bound_statement Dd C Xpp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u
  have herr : ErrX5at Dd C Xpp u ≤ Dd.x ^ (CErr C * Dd.ε) * ErrText Dd := by
    obtain ⟨⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0,
      hXa, haT, hB0, hNc, hlW, hdel, -, -, hC⟩, het⟩ := h3
    obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
    obtain ⟨hlog, hbig⟩ := h5
    have hx0 : 0 < Dd.x := by linarith only [hx]
    have hy : 1 ≤ Dd.x ^ Dd.ε := Real.one_le_rpow hx hε.le
    have hyD : 1 ≤ Dd.x ^ (C.eDiv * Dd.ε) := Real.one_le_rpow hx (mul_nonneg hD hε.le)
    have hyL : 1 ≤ Dd.x ^ (C.eLoss * Dd.ε) := Real.one_le_rpow hx (mul_nonneg hLs hε.le)
    have hb0 : 0 ≤ Dd.b := by linarith only [hb]
    have hbxb : Dd.b ≤ Dd.x * Dd.b := le_mul_of_one_le_left hb0 hx
    have hba : Dd.b ≤ Dd.a := hbxb.trans hxb
    have ha1 : 1 ≤ Dd.a := hb.trans hba
    have hM : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hk : 0 < Dd.k := by linarith only [hk1]
    have hmx : (m : ℝ) ≤ Dd.x := by
      refine hm.trans ?_
      calc Dd.x ^ ((1 : ℝ) / 2 + Dd.ε / 2) ≤ Dd.x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hε1])
        _ = Dd.x := Real.rpow_one _
    have hMk : (m : ℝ) ≤ Dd.k := (le_mul_of_one_le_left hM hx).trans hxm
    have hMb : (m : ℝ) * Dd.b ≤ Dd.a := (mul_le_mul_of_nonneg_right hmx hb0).trans hxb
    have hsA0 : 0 ≤ Dd.sumA := Finset.sum_nonneg (fun t _ => (haT t).1)
    have hsA : Dd.sumA ≤ 2 * (Dd.nT * Dd.a) := by
      unfold Data.sumA Data.nT
      calc ∑ t, Dd.aT t ≤ ∑ _t : Top, 2 * Dd.a := Finset.sum_le_sum (fun t _ => (haT t).2)
        _ = 2 * ((Fintype.card Top : ℝ) * Dd.a) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    have hlWk : Real.log (Fintype.card (W u) : ℝ) ≤ Dd.a :=
      ((hlW u).trans (sub_three_mul_log_two_le hk.le)).trans hka
    have hlk0 : 0 ≤ Real.log Dd.k := Real.log_nonneg hk1
    have hlk : Real.log Dd.k ≤ (1 + eK) * Dd.x ^ Dd.ε := log_le_of_le_rpow hx heK hk hkx hlog hy
    have hxH : 1 ≤ Dd.x ^ C.cHH := Real.one_le_rpow hx hHH
    have hlH0 : 0 ≤ Real.log (1 + Dd.x ^ C.cHH) := Real.log_nonneg (by linarith only [hxH])
    have hlH : Real.log (1 + Dd.x ^ C.cHH) ≤ (1 + C.cHH) * Dd.x ^ Dd.ε :=
      log_one_add_rpow_le hx hHH hlog hy
    obtain ⟨hdI0, hdI⟩ := inv_one_sub_le_two hdel
    have hpow : Dd.x ^ (CErr C * Dd.ε)
        = Dd.x ^ (C.eDiv * Dd.ε) * Dd.x ^ (C.eLoss * Dd.ε) * Dd.x ^ Dd.ε * Dd.x ^ Dd.ε * Dd.x ^ Dd.ε := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1
      unfold CErr
      ring
    rw [hpow]
    unfold KBig at hbig
    have := core_ineq (nT := Dd.nT) (a := Dd.a) (b := Dd.b) (b' := Dd.b') (k := Dd.k) (L := Dd.L) (La := Dd.La)
      (B0 := Dd.B0) (Nc := Dd.Nc) (M := (m : ℝ)) (sA := Dd.sumA)
      (lW := Real.log (Fintype.card (W u) : ℝ)) (lk := Real.log Dd.k)
      (lH := Real.log (1 + Dd.x ^ C.cHH)) (dI := (1 - Dd.delBar)⁻¹)
      (et := (Dd.etaBar + 4 * Real.sqrt Dd.eBar) * (Dd.x ^ C.cHH * Dd.b)) (Xpp := Xpp)
      (y := Dd.x ^ Dd.ε) (yD := Dd.x ^ (C.eDiv * Dd.ε)) (yL := Dd.x ^ (C.eLoss * Dd.ε)) (K := K)
      (h := 1 + C.cHH) (g := 1 + eK)
      hy hyD hyL hnT ha1 hb0 hba hM hk hMk hMb hL0 hL hLa0 hLa hb' hkb' hX0 hXa hsA0 hsA hB0 hNc hlWk
      hlk0 hlk hlH0 hlH hdI0 hdI het c1 c1' c2 c2' c3 c3' c4 c4' c5 c5' c6 c6' c7 c7'
      (by linarith only [hHH]) (by linarith only [heK]) hbig
    unfold ErrX5at UBar5 MLo5 Data.Vvar Data.LoP ErrText
    exact this
  have hnT : Dd.nT = (TT.card : ℝ) := by
    unfold Data.nT
    have := Fintype.card_congr eT
    rw [Fintype.card_coe] at this
    exact_mod_cast this
  have htext : ErrText Dd ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold ErrText errorBracketSizeWindows
    rw [hnT]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    gcongr
    · exact h4.1
    · exact h4.2
  have hpow : 0 ≤ Dd.x ^ (CErr C * Dd.ε) := Real.rpow_nonneg s1.1.le _
  rw [hgap]
  calc Dd.ASK u - Dd.Main u ≤ _ := by linarith
    _ ≤ _ := herr
    _ ≤ _ := mul_le_mul_of_nonneg_left htext hpow

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.WindowInequalityOfArtinInputs
section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm
section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.GmAEq
section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.PrimInj
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.prim_inj :
    ∀ (φ : Frame) (H : HostAx φ), Function.Injective H.toHostRaw.prim ∧ H.toHostRaw.prim 1 = PChar.one := by
  intro φ H
  constructor
  · intro θ θ' h
    apply MonoidHom.ext
    intro g
    obtain ⟨u, rfl⟩ := HostDer.art_surj H.der g
    have h1 := (H.toHostRaw.isPrimOf_prim θ).2
    have h2 := (H.toHostRaw.isPrimOf_prim θ').2
    rw [← h] at h2
    have hc := ZMod.val_coe_unit_coprime u
    have e := (h1 _ hc).symm.trans (h2 _ hc)
    apply Units.ext
    rw [← HostRaw.dir_unit, ← HostRaw.dir_unit]
    simpa [HostRaw.dirAt, ZMod.natCast_zmod_val] using e
  · have hd : H.toHostRaw.dir 1 = 1 := by
      apply MulChar.ext
      intro u
      rw [HostRaw.dir_unit]
      simp
    rw [HostRaw.prim, hd, PChar.of_one]
end

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.ChrBij
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem chr_val (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (g : φ.GG) :
    ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g)) := rfl

private theorem sgn_val (s : ℤˣ) :
    (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 s) = 0 then (1 : ℂ) else -1) = ((s : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · have h0 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 1) = 0 := by
      rw [map_one, toAdd_one]
    rw [if_pos h0]
    simp
  · have h1 : Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 (-1)) = 1 := by decide
    rw [h1, if_neg (by decide)]
    simp

theorem UpperTheory.Comparison₂.chr_bij :
    ∀ φ : Frame, Function.Bijective (chr φ) ∧ chr φ 0 = 1 ∧ chr φ chC = φ.chC ∧ chr φ psC = φ.psC ∧
      (∀ ψ g, ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g))) ∧
      (∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ)) ∧ ∀ ψ, chr φ ψ ∈ φ.Xp ↔ (ψ ∈ PsiA φ.A0 ∧ ψ sgc0 = 1) := by
  intro φ
  obtain ⟨hbij, hiod, -, htau, -⟩ := toE_bij φ
  have trivA : ∀ ψ, ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ) := by
    intro ψ
    have key : ∀ s : φ.A, ((chr φ ψ (φ.tau1 s) : ℂˣ) : ℂ) = ψ ((0 : E0), s) := by
      intro s
      rw [chr_val, htau]
      rfl
    simp only [PsiA, Frame.TrivialOnFirstFactor, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h s hs
      apply Units.ext
      rw [Units.val_one, key]
      exact h s hs
    · intro h s hs
      have h2 := congrArg Units.val (h s hs)
      rw [key, Units.val_one] at h2
      exact h2
  let e := MulEquiv.ofBijective (toE φ) hbij
  have he : ∀ g, e g = toE φ g := fun g => rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, chr_val φ, trivA, ?_⟩
  · intro ψ ψ' h
    apply AddChar.ext
    intro a
    obtain ⟨g, hg⟩ := hbij.2 (Multiplicative.ofAdd a)
    have h2 := congrArg (fun θ : φ.Char => ((θ g : ℂˣ) : ℂ)) h
    simp only [chr_val, hg, toAdd_ofAdd] at h2
    exact h2
  · intro θ
    let ψ : AddChar (E0 × φ.A) ℂ :=
      { toFun := fun a => ((θ (e.symm (Multiplicative.ofAdd a)) : ℂˣ) : ℂ)
        map_zero_eq_one' := by
          simp only [ofAdd_zero, map_one, Units.val_one]
        map_add_eq_mul' := by
          intro a b
          simp only [ofAdd_add, map_mul, Units.val_mul] }
    refine ⟨ψ, ?_⟩
    refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show ((θ (e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (toE φ g)))) : ℂˣ) : ℂ) = _
    rw [ofAdd_toAdd, ← he, MulEquiv.symm_apply_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val, MonoidHom.one_apply, Units.val_one, AddChar.zero_apply]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.2) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.chC, Frame.chD]
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_val]
    show (if Multiplicative.toAdd (LFunctionChainParameters.LHost.sgn2 g.1.1) = 0 then (1 : ℂ) else -1) = _
    rw [sgn_val]
    simp [Frame.psC, Frame.chQ]
  · intro ψ
    have hv : ((chr φ ψ φ.iod : ℂˣ) : ℂ) = ψ sgc0 := by
      rw [chr_val, hiod]
      rfl
    simp only [Frame.Xp, Set.mem_setOf_eq]
    rw [← trivA]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← hv, h2, Units.val_one]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Units.ext ?_⟩
      rw [hv, h2, Units.val_one]
end

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.character_trivial_on_generator_iff (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (s : φ.A) :
    chr φ ψ (φ.tau1 s) = 1 ↔ ψ (0, s) = 1 := by
  rw [← Units.val_eq_one, (chr_bij φ).2.2.2.2.1 ψ (φ.tau1 s)]
  simp [toE, Frame.tau1, Frame.iotaInv, Frame.iota]
  exact Iff.rfl

private theorem UpperTheory.Comparison₂.gmA_eq_triv (φ : Frame) (θ : φ.Char) (hi : θ φ.iod = 1) :
    (∀ h : φ.A, θ (φ.tau1 h) = 1) ↔ θ = 1 ∨ θ = φ.psC := by
  constructor
  · intro h
    have hM : ∀ m : φ.MA, θ ((1, 1), m) = 1 := fun m => h (Multiplicative.toAdd m)
    have hB : ∀ b : ℤˣ, θ ((1, b), 1) = 1 := by
      intro b
      rcases Int.units_eq_one_or b with rfl | rfl
      · exact θ.map_one
      · exact hi
    have hred : ∀ (a b : ℤˣ) (m : φ.MA), θ ((a, b), m) = θ ((a, 1), 1) := by
      intro a b m
      have e : (((a, b), m) : φ.GG) = ((a, 1), 1) * ((1, b), 1) * ((1, 1), m) := by
        ext <;> simp
      rw [e, map_mul, map_mul, hM, hB, mul_one, mul_one]
    have hsq : (θ φ.sg : ℂ) * (θ φ.sg : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul]
      have e : φ.sg * φ.sg = 1 := by
        simp only [Frame.sg]
        ext <;> simp
      rw [e, map_one, Units.val_one]
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · left
      refine MonoidHom.ext fun g => ?_
      obtain ⟨⟨a, b⟩, m⟩ := g
      rw [hred]
      apply Units.ext
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]
        simp
      · simpa [Frame.sg] using h1
    · right
      refine MonoidHom.ext fun g => ?_
      obtain ⟨⟨a, b⟩, m⟩ := g
      rw [hred]
      apply Units.ext
      rcases Int.units_eq_one_or a with rfl | rfl
      · rw [hB 1]
        simp [Frame.psC, Frame.chQ]
      · simpa [Frame.psC, Frame.chQ, Frame.sg] using h1
  · rintro (rfl | rfl) h
    · simp
    · apply Units.ext
      simp [Frame.psC, Frame.chQ, Frame.tau1]

theorem UpperTheory.Comparison₂.gmA_eq :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ),
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell → ∀ y,
        GmA (arith H.toHostRaw) ell (keptA Λ H.toHostRaw) (3 * (Λ.o : ℝ) + 1)⁻¹ y = Λ.Gm y := by
  intro Λ φ H TT x eps C ell hE hell y
  classical
  obtain ⟨hbij, -, -, -, -⟩ := chr_bij φ
  obtain ⟨hpinj, hp1⟩ := prim_inj φ H
  have hmem : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw ↔ H.prim (chr φ ψ) ∈ Λ.KEPT := by
    intro ψ
    simp [keptA, HostRaw.kept_iff]
  have hXp : ∀ ψ, ψ ∈ keptA Λ H.toHostRaw → chr φ ψ ∈ φ.Xp := by
    intro ψ hψ
    obtain ⟨θ, hθ, hpr⟩ := hE.kept _ ((hmem ψ).1 hψ)
    rw [HostRaw.isPrimOf_iff] at hpr
    have e := hpinj hpr
    rw [e]
    exact hθ
  have hKimg : Λ.KEPT = (keptA Λ H.toHostRaw).image (fun ψ => H.prim (chr φ ψ)) := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · intro hp
      obtain ⟨θ, -, hpr⟩ := hE.kept p hp
      rw [HostRaw.isPrimOf_iff] at hpr
      obtain ⟨ψ, rfl⟩ := hbij.2 θ
      refine ⟨ψ, (hmem ψ).2 ?_, hpr.symm⟩
      rw [← hpr]
      exact hp
    · rintro ⟨ψ, hψ, rfl⟩
      exact (hmem ψ).1 hψ
  have hinj : Set.InjOn (fun ψ => H.prim (chr φ ψ)) (keptA Λ H.toHostRaw) :=
    fun a _ b _ h => hbij.1 (hpinj h)
  have hw : ∀ ψ ∈ keptA Λ H.toHostRaw, wtA (3 * (Λ.o : ℝ) + 1)⁻¹ ψ =
      (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ))) := by
    intro ψ hψ
    have hiod : chr φ ψ φ.iod = 1 := (hXp ψ hψ).2
    have htriv : (∀ h : φ.A, ψ (0, h) = 1) ↔ chr φ ψ = 1 ∨ chr φ ψ = φ.psC := by
      rw [← gmA_eq_triv φ (chr φ ψ) hiod]
      exact forall_congr' fun h => (character_trivial_on_generator_iff φ ψ h).symm
    obtain ⟨hps1, hps2⟩ := hE.ps
    unfold wtA
    by_cases hA : ∀ h : φ.A, ψ (0, h) = 1
    · rw [if_pos hA]
      rcases htriv.1 hA with h1 | h1
      · rw [h1, hp1, if_pos rfl]
      · have hK : H.toHostRaw.Kept Λ.KEPT φ.psC := by
          rw [HostRaw.kept_iff, ← h1]
          exact (hmem ψ).1 hψ
        rw [h1]
        split_ifs with hone
        · rfl
        · cases hk : Λ.psK with
          | none => exact absurd hK (hps2 hk)
          | some p =>
            have e := hps1 p hk
            rw [HostRaw.isPrimOf_iff] at e
            simp [Level.wt, hk, e]
    · rw [if_neg hA]
      have hn1 : chr φ ψ ≠ 1 := fun h => hA (htriv.2 (Or.inl h))
      have hnps : chr φ ψ ≠ φ.psC := fun h => hA (htriv.2 (Or.inr h))
      rw [if_neg (fun h => hn1 (hpinj (h.trans hp1.symm)))]
      unfold Level.wt
      rw [if_neg]
      intro hk
      have e := hps1 _ hk
      rw [HostRaw.isPrimOf_iff] at e
      exact hnps (hpinj e)
  have hG : ∀ ψ, (GPsi (arith H.toHostRaw) ell ψ y).re = (An.gChi (H.prim (chr φ ψ)).χ y).re := by
    intro ψ
    rw [(prim_read φ H ell hell ψ).2 y]
  have key : ∑ ψ ∈ keptA Λ H.toHostRaw,
      (if H.prim (chr φ ψ) = PChar.one then 1 else Λ.wt (H.prim (chr φ ψ))) *
        (An.gChi (H.prim (chr φ ψ)).χ y).re =
      ∑ p ∈ Λ.KEPT, (if p = PChar.one then 1 else Λ.wt p) * (An.gChi p.χ y).re := by
    rw [hKimg, Finset.sum_image hinj]
  have hone : (An.gChi PChar.one.χ y).re = An.G y := by
    have h1 : PChar.one.χ = 1 := rfl
    unfold An.gChi
    rw [if_pos h1]
    simp
  unfold GmA Level.Gm Level.Nt
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [hw ψ hψ, hG ψ]), key,
    ← Finset.add_sum_erase _ _ Λ.one_mem]
  congr 1
  · rw [if_pos rfl, one_mul, (Gz_eq y).1, hone]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [if_neg (Finset.ne_of_mem_erase hp)]
end

section -- merged from Development.AutomorphicArithmetic.PrimitiveCosets.SigALe
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

private theorem character_trivial_first_factor (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (h : ψ ∈ PsiA φ.A0) : Frame.TrivialOnFirstFactor (chr φ ψ) := by
  intro s hs
  apply Units.ext
  simp only [PsiA, Finset.mem_filter, Finset.mem_univ, true_and] at h
  have e : ((chr φ ψ (φ.tau1 s)) : ℂ) = ψ (0, s) := by
    simp [chr, toE, Frame.tau1, Frame.iotaInv, Frame.iota]
    rfl
  rw [e, Units.val_one]
  exact h s hs

private theorem chr_bounded (Λ : Level) (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) (h : ψ ∈ PsiA φ.A0)
    (hk : ψ ∉ keptA Λ H) : chr φ ψ ∈ H.Bounded Λ.KEPT := by
  have hT := character_trivial_first_factor φ ψ h
  have hsq : chr φ ψ φ.iod * chr φ ψ φ.iod = 1 := by
    rw [← map_mul]
    have e : φ.iod * φ.iod = 1 := by
      simp only [Frame.iod]
      ext <;> simp
    rw [e, map_one]
  have hv : (chr φ ψ φ.iod : ℂ) * (chr φ ψ φ.iod : ℂ) = 1 := by
    rw [← Units.val_mul, hsq, Units.val_one]
  rcases mul_self_eq_one_iff.mp hv with h1 | h1
  · left
    refine ⟨⟨hT, Units.ext (by simpa using h1)⟩, ?_⟩
    intro hK
    apply hk
    simpa [keptA] using hK
  · right
    exact ⟨hT, Units.ext (by simpa using h1)⟩

theorem UpperTheory.Comparison₂.sigA_le :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), 0 < x →
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell →
        SigA (arith H.toHostRaw) ell φ.A0 (keptA Λ H.toHostRaw) x ≤ 4 * (Λ.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
  intro Λ φ H TT x eps C ell hx hE hell
  classical
  unfold SigA
  have hb : ∀ ψ ∈ PsiA φ.A0 \ keptA Λ H.toHostRaw,
      ‖GPsi (arith H.toHostRaw) ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) := by
    intro ψ hψ
    rw [Finset.mem_sdiff] at hψ
    rw [(prim_read φ H ell hell ψ).2 x]
    exact hE.bdG _ (chr_bounded Λ φ H.toHostRaw ψ hψ.1 hψ.2) _ _ (HostRaw.isPrimOf_prim _ _)
  calc _ ≤ ∑ ψ ∈ PsiA φ.A0 \ keptA Λ H.toHostRaw, x ^ ((1 : ℝ) / 2 + eps) := Finset.sum_le_sum hb
    _ = ((PsiA φ.A0 \ keptA Λ H.toHostRaw).card : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((PsiA φ.A0).card : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
        exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    _ = 4 * (Λ.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
        rw [card_PsiA, hE.o_eq]
        push_cast
        ring
end

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps) := by
  intro Λ eD eL K cHH eK C eps heps
  have ho : (0 : ℝ) ≤ Λ.o := Nat.cast_nonneg _
  have hc : |(3 * (Λ.o : ℝ) + 1)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  obtain ⟨x₁, hx₁⟩ := Deduction.ch_core (max (eD + eL) 0 + 3) eps C (koOf Λ) (3 * (Λ.o : ℝ) + 1)⁻¹ (4 * (Λ.o : ℝ))
    (by positivity) heps hc
  obtain ⟨x₂, hx₂⟩ := large_x_eventually eps K cHH eK heps
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop heps).eventually_ge_atTop (1 + 4 * (Λ.o : ℝ)))
  refine ⟨max x₁ (max x₂ x₃), fun x hx φ H TT hE hCore => ?_⟩
  have g1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have g2 : x₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have g3 : x₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨U0, i0, tr, W, i4, i5, Top, i6, m, f, Dd, Cc, Xpp, ell, N, T2, a, w, eT, eP, η, X', θ,
    hell, hxx, hε, heD, heL, hcHH, hcov, hId, hLed, hWin, hBN, hSz, hThin, hCost, hRest, hT2⟩ := hCore
  subst hxx hε
  have hLX := hx₂ _ g2
  have hWin' := hWin
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC
  have hLX' : LargeX Dd.x Dd.ε K Cc.cHH eK := by
    refine ⟨hLX.1, le_trans ?_ hLX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)
  have hb : 0 < Dd.b := by linarith
  have hx0 : 0 < Dd.x := by linarith
  have hk : 0 < Dd.k := by linarith
  have ha : 0 ≤ Dd.a := le_trans (by positivity) w5
  have hE0 : 0 ≤ eD + eL := by linarith
  rw [max_eq_left hE0] at hx₁
  have hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card φ.A) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold errorBracketSizeWindows
    positivity
  have hExp : Dd.x ^ (CErr Cc * Dd.ε) ≤ Dd.x ^ ((eD + eL + 3) * Dd.ε) := by
    refine Real.rpow_le_rpow_of_exponent_le w1 (mul_le_mul_of_nonneg_right ?_ w2.le)
    unfold CErr
    linarith
  have hmain := hx₁ _ g1 φ.A m (arith H.toHostRaw) _ ell N TT T2 a w Dd.b Dd.b' Dd.k Dd.a η X' θ φ.A0
    (keptA Λ H.toHostRaw) (hostFactsS φ H) hb ha hk w7 w8 hSz hThin hCost hRest hT2
    (charsA Λ φ H TT _ _ C ell hx0 hE hell) (fun u hu => by
      obtain ⟨v, rfl⟩ := hcov u hu
      exact le_trans (Deduction.ch_top Dd tr Cc Xpp eK K _ ell N TT T2 a w eT eP hId hLed hWin hBN hLX' v)
        (mul_le_mul_of_nonneg_right hExp hBr))
  rw [gmA_eq Λ φ H TT _ _ C ell hE hell] at hmain
  have hs := sigA_le Λ φ H TT _ _ C ell hx0 hE hell
  have h1 : Dd.x ^ ((1 : ℝ) / 2 + Dd.ε) ≤ Dd.x ^ ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * Dd.ε) :=
    Real.rpow_le_rpow_of_exponent_le w1 (by nlinarith)
  have h2 : Dd.x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * Dd.ε)
      = Dd.x ^ Dd.ε * Dd.x ^ ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * Dd.ε) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have h3 := mul_le_mul_of_nonneg_right (hx₃ _ g3)
    (Real.rpow_nonneg hx0.le ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * Dd.ε))
  have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4 * (Λ.o : ℝ) by positivity)
  rw [h2]
  linarith
end

noncomputable section

namespace UpperTheory.Comparison₂

open Formalism.HC Formalism.MainNotions Formalism.BasicNotions

def FamCoreConstantBounds {eps : ℝ} (Fm : FamCore eps) (eD eL K cHH eK x : ℝ) : Prop :=
  ∃ i : Fm.Ix x, CoreAtH (Fm.D x i).host.toHostRaw (Fm.D x i).host.TT eD eL K cHH eK eps x

variable {Fam : ℝ → Type 1} {core : ∀ {eps : ℝ}, Fam eps → FamCore eps}
  {Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop}

theorem windowInequality_of_artinInputs
    (h : ∀ {eps : ℝ} (Fm : Fam eps) (eD eL K cHH eK CL x : ℝ), Tied Fm eD eL K cHH eK CL x → FamCoreConstantBounds (core Fm) eD eL K cHH eK x)
    (Λ : Level) : ChebyshevInequalityOnWindows @core @Tied Λ := by
  rintro eD eL eps he Fm ⟨C, xE, hE⟩ ⟨K, cHH, eK, CL, x0, hT⟩
  obtain ⟨x1, hx1⟩ := core_gm Λ eD eL K cHH eK C eps he
  refine ⟨max x1 (max x0 xE), fun x hx hw => ?_⟩
  have b := le_of_max_le_right hx
  obtain ⟨i, hi⟩ := h Fm _ _ _ _ _ _ _ (hT x (le_of_max_le_left b) hw)
  exact hx1 x (le_of_max_le_left hx) _ ((core Fm).D x i).host.toHostAx _ (hE x (le_of_max_le_right b) i) hi

end UpperTheory.Comparison₂

end
end

noncomputable section

namespace UpperTheory.Comparison₂

open Formalism.HC Formalism.MainNotions Formalism.BasicNotions

theorem tiedCore_of_chainTied {eps : ℝ} (Fm : FamP eps) (eD eL K cHH eK CL x : ℝ) (h : ChainTied Fm eD eL K cHH eK CL x) :
    FamCoreConstantBounds Fm.toFamCore eD eL K cHH eK x := by
  obtain ⟨i0, m, f, pt, av, bv, Top, iT, Dd, C, Xpp, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    -, -, -, ⟨tT, t2, -, -, hell⟩, h1, h2, h3, h4, h5, h7, h8, h9, h10, ⟨⟨s1, s2, s3, s4, s5, s6, ⟨n1, n2, n3⟩, s8⟩, th, -⟩, h12, h13⟩ := h
  have hTT : TT = (Fm.D x i0).host.TT := by
    ext t
    rw [tT t, ← Fm.TT_eq x i0, Finset.mem_image]
    exact ⟨fun ⟨s, hs, e⟩ => (Frame.A.val_injective _ e) ▸ hs, fun ht => ⟨t, ht, rfl⟩⟩
  subst hTT
  refine ⟨i0, _, inferInstance, id, fun u0 => (Fm.D x (pt u0)).what₂.Word, fun _ => inferInstance, fun _ => inferInstance, Top, iT,
    m, f, Dd, C, Xpp, ell, N, T2, a, w, eT, eP, η, X', θ, hell, h1, h2, h3, h4, h5, fun s _ => ⟨s, rfl⟩, h7, h8, h9, h10,
    ⟨s1, s2, s3, s4, s5, s6, fun u _ => n1 u, fun u _ => n2 u, fun u _ => n3 u, fun u _ => s8 u⟩, th, h12, h13, fun s hs => ?_⟩
  obtain ⟨k, -, rfl⟩ := (t2 0 s).1 hs
  exact Frame.digit_mem_cyclic_subgroup _ k

theorem level_gm_le_on_family_scales (Λ : Level) :
    ChebyshevInequalityOnWindows (Fam := FamP) (fun Fm => Fm.toFamCore) (fun Fm => ChainTied Fm) Λ :=
  windowInequality_of_artinInputs (fun Fm => tiedCore_of_chainTied Fm) Λ

end UpperTheory.Comparison₂

end
end

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX

def TopG : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore) → FamilyClassConnected (G.cls la)

theorem hypV_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) : HypV Fm.toFamCore :=
  ⟨Fm.x1 + 1, fun x hx i => (h.2 x (by linarith) i).2⟩

theorem eFamC_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) :
    EFamC (Level.cyc ψ) Fm.toFamCore := by
  refine ⟨4, Fm.x1 + 1, fun x hx i => ?_⟩
  have h1 := (h.2 x (by linarith) i).1
  rw [Fm.L_x x i (by linarith), Fm.L_eps x i] at h1
  exact h1

theorem zeroFreeAll_of_topG {la : ℝ} (hla : 1 < la) (h : TopG) (hS : ∀ ψ : PChar, HostExW la (GChi ψ).req) : ZeroFreeAll := by
  have key : ZeroFreeOn fun _ => True :=
    zeroFreeOn_of_tiedWin_cyc (Fam := FamP) (core := fun Fm => Fm.toFamCore) (Tied := fun Fm => ChainTied Fm) hla
      (fun ψ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _) (fun ψ _ => UpperTheory.Comparison₂.formB _) fun ψ _ => by
        obtain ⟨eD, eL, ε₁, h1, h2⟩ := h la (GChi ψ) hla (hS ψ) (hypV_of_cls ψ la)
        refine ⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩
        obtain ⟨Fm, c, d⟩ := h2 eps a b
        exact ⟨Fm, eFamC_of_cls ψ la Fm c, c.1, d⟩
  exact key

end UpperTheory.Top

end
