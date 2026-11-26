module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveOfAdjointSeparatesLabelledParts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainLValuesNeZeroAndParamsInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientCharPartialLEntireNonvanishingIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientCharPartialLEntireNonvanishingIntegers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.QuotL

variable {D : D7}

theorem trivialOnF {c : Com D} (hc : c.Is) {k : ℕ} (hk : k < c.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.TrivialOnF (c.χ k) := fun a => by
  obtain ⟨⟨η, hη⟩, h⟩ := (hc.hecke k hk).2
  exact (h η hη a).trans (pow_zero _)

theorem quotL_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, i < j → j < c.m →
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
  intro D c hc i j hij hj
  have hi : i < c.m := hij.trans hj
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hexp : ∃ (τ : D.what₂.Tau) (e e' : ℚ), HasInfExp D (c.χ i) τ (-e) ∧
      HasInfExp D (c.χ j) τ (-e') ∧ e ≠ e' :=
    ⟨τ, -(c.a i τ), -(c.a j τ), by rw [neg_neg]; exact hc.exp i hi τ, by rw [neg_neg]; exact hc.exp j hj τ,
      fun h => hc.ne i j hij hj τ (neg_injective h)⟩
  have R := GlobalTheory.HeckeRatio.heckeRatioPos D (c.χ i) (c.χ j) (hc.hecke i hi).1 (hc.hecke j hj).1
    (trivialOnF hc hi) (trivialOnF hc hj) hexp
  obtain ⟨Λ, hL, -⟩ := (R 0).2 c.S
  obtain ⟨hd, hp⟩ := hL
  refine ⟨Λ, hd, fun z hz => ?_, fun n h1 h0 => ?_⟩
  · have hunr : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
        GlobalTheory.LFun.UnrAt (c.χ i * (c.χ j)⁻¹) w := fun w hw =>
      (hc.unr i hi w hw).mul (hc.unr j hj w hw).inv
    have hoff : ∀ P, OffS D c.S P ↔ P ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) :=
      fun P => (GlobalTheory.HeckeRatio.offS_iff c.S P).trans Iff.rfl
    let e := Equiv.subtypeEquivRight hoff
    have k := hp z hz
    rw [GlobalTheory.HeckeRatio.lfac_eq] at k
    have k2 : HasProd (fun w : {w // w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} =>
        GlobalTheory.LFun.locL (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) w.1 z) (Λ z) := by
      refine (e.hasProd_iff).1 (k.congr_fun fun P => ?_)
      have hu := hunr P.1 ((hoff P.1).1 P.2)
      rw [GlobalTheory.LFun.lfac_eq_locL (Formalism.IndefR.ThmB.InputsHecke.isCMExt D)]
      simp only [Function.comp_apply, e, Equiv.subtypeEquivRight_apply_coe, GlobalTheory.LFun.locL,
        GlobalTheory.LFun.charFam_of_unrAt hu]
    exact k2.tprod_eq.symm
  · obtain ⟨Λn, hLn, hpos⟩ := (R n).2 c.S
    have hEq : Λ = Λn := GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.IsPartialL.unique ⟨hd, hp⟩ hLn
    have := (hpos n h1 le_rfl).2
    rw [← hEq, h0, Complex.zero_re] at this
    exact lt_irrefl _ this

end GlobalTheory.EvenOnto.QuotL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientCharPartialLEntireNonvanishingIntegersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_char_partial_L_entire_nonvanishing_integers : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, i < j → j < c.m → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ j)⁻¹) w}) z) ∧ ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
  first | exact @GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero | exact GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero | (intros; apply GlobalTheory.EvenOnto.QuotL.quotL_entire_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainLValuesNeZeroAndParamsInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.ChainVal

variable {D : D7}

abbrev vf (χ : (AE D)ˣ →* Circle) : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := GlobalTheory.LFun.val (F := D.host.F) χ

theorem twist_sum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → GlobalTheory.LFun.Fam K)
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : GlobalTheory.LFun.twist (∑ i ∈ s, f i) z = ∑ i ∈ s, GlobalTheory.LFun.twist (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => funext w; simp [GlobalTheory.LFun.twist]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LFun.twist_add, ih]

theorem stepPar_same (χ : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) :
    GlobalTheory.ChainOnto.stepPar χ χ t B = B + GlobalTheory.LFun.segFam (vf χ) t := by
  funext w; simp [GlobalTheory.ChainOnto.stepPar, GlobalTheory.LFun.segFam, vf]

theorem chainPar_closed (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B k = B + ∑ i ∈ Finset.range k, GlobalTheory.LFun.segFam (vf (c.χ i)) c.t := by
  induction k with
  | zero => simp [chainPar]
  | succ k ih => rw [chainPar_succ, ih, stepPar_same, Finset.sum_range_succ, add_assoc]

theorem chainPar_twist (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    GlobalTheory.LFun.twist (chainPar c B k) (vf (c.χ k))⁻¹ =
      GlobalTheory.LFun.twist B (vf (c.χ k))⁻¹ + ∑ i ∈ Finset.range k, GlobalTheory.LFun.segFam (vf (c.χ i * (c.χ k)⁻¹)) c.t := by
  rw [chainPar_closed, GlobalTheory.LFun.twist_add, twist_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.LFun.twist_segFam]
  congr 1
  funext w; simp [vf, mul_comm]

theorem locL_finsetSum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (d : ι → GlobalTheory.LFun.Fam K)
    (w : HeightOneSpectrum (𝓞 K)) (x : ℂ) :
    GlobalTheory.LFun.locL (∑ i ∈ s, d i) w x = ∏ i ∈ s, GlobalTheory.LFun.locL (d i) w x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [GlobalTheory.LFun.locL]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, GlobalTheory.LFun.locL_add, ih]

theorem bounded_single {K : Type} [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K)))
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) (hz : ∀ w, ‖(z w : ℂ)‖ = 1) : GlobalTheory.LFun.Bounded T (fun w => {z w}) 1 0 :=
  fun w _ => ⟨by simp, fun b hb => by rw [Multiset.mem_singleton.1 hb, Real.rpow_zero, hz]⟩

theorem eulerProd_add_segFam {K : Type} [Field K] [NumberField K] {ι : Type} (T : Set (HeightOneSpectrum (𝓞 K)))
    (A : GlobalTheory.LFun.Fam K) (s : Finset ι) (z : ι → HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) (x : ℂ)
    (hA : GlobalTheory.LFun.Converges T A x)
    (hz : ∀ i ∈ s, ∀ l < t, GlobalTheory.LFun.Converges T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :
    GlobalTheory.LFun.eulerProd T (A + ∑ i ∈ s, GlobalTheory.LFun.segFam (z i) t) x = GlobalTheory.LFun.eulerProd T A x *
      ∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l) := by
  have h1 : HasProd (fun w : {w // w ∉ T} => ∏ i ∈ s, ∏ l ∈ Finset.range t,
      GlobalTheory.LFun.locL (fun u => {z i u}) w (x + ((t : ℂ) - 1) / 2 - l))
      (∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :=
    hasProd_prod fun i hi => hasProd_prod fun l hl => (hz i hi l (Finset.mem_range.1 hl)).hasProd
  have h2 := hA.hasProd.mul h1
  show ∏' w : {w // w ∉ T}, _ = _
  refine HasProd.tprod_eq ?_
  convert h2 using 1
  funext w
  rw [GlobalTheory.LFun.locL_add, locL_finsetSum]
  simp only [GlobalTheory.LFun.locL_segFam']

end GlobalTheory.EvenOnto.ChainVal


open GlobalTheory.EvenOnto.ChainVal in
theorem GlobalTheory.EvenOnto.chainL_and_inj : ∀ D : D7, ChainL D ∧ ∀ (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  intro D
  refine ⟨?_, ?_⟩
  · intro c hc B hB k hk
    set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT
    have hnt : c.n + 2 ≤ c.t := hc.step
    have hnt' : (c.n : ℝ) + 2 ≤ c.t := by exact_mod_cast hnt
    have hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.range k → Differentiable ℂ Λ ∧
        (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T
          (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ k)⁻¹) w}) z) ∧
        ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
      intro i
      by_cases hi : i ∈ Finset.range k
      · obtain ⟨Λ, h⟩ := GlobalTheory.T.quotient_char_partial_L_entire_nonvanishing_integers D c hc i k (Finset.mem_range.1 hi) hk
        exact ⟨Λ, fun _ => h⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose Λ hΛ using hΛ
    set A := GlobalTheory.LFun.twist B (vf (c.χ k))⁻¹ with hA
    have hAb : GlobalTheory.LFun.Bounded T A c.n (((c.n : ℝ) - 1) / 2) :=
      hB.twist fun w _ => by simp [vf, GlobalTheory.LFun.norm_val]
    let z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun i => vf (c.χ i * (c.χ k)⁻¹)
    have hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y := fun i y hy =>
      (bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)
    let H : ℂ → ℂ := fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) *
      ∏ i ∈ Finset.range k, ∏ l ∈ Finset.range c.t, Λ i (x + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l)
    have hEq : ∀ x : ℂ, ((c.n : ℝ) + c.t + 2) < x.re →
        H x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.χ k) (x + 1 / 2) := by
      intro x hx
      have hre : ∀ l : ℕ, l < c.t → 1 < (x + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l).re := by
        intro l hl
        have : (l : ℝ) + 1 ≤ c.t := by exact_mod_cast hl
        have hr0 : (0 : ℝ) ≤ c.n := Nat.cast_nonneg _
        simp
        linarith
      show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k)
        (GlobalTheory.LFun.val (F := D.host.F) (c.χ k))⁻¹) (x + 1 / 2)
      change _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k) (vf (c.χ k))⁻¹) (x + 1 / 2)
      rw [chainPar_twist, ← hA, eulerProd_add_segFam T A (Finset.range k) z c.t (x + 1 / 2)
        (hAb.converges (by have hr0 : (0 : ℝ) ≤ c.n := Nat.cast_nonneg _; simp; linarith))
        (fun i _ l hl => hzc i _ (hre l hl))]
      refine congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi =>
        Finset.prod_congr rfl fun l hl => ?_)
      exact (hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))
    have hU : IsOpen (GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2)) := GlobalTheory.Cont.isOpen_rightOf _
    have hD : DifferentiableOn ℂ H (GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2)) := by
      refine DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)
      · refine hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_
        simp only [GlobalTheory.Cont.mem_rightOf] at hx
        simp
        linarith
      · exact Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ =>
          (hΛ i hi).1.comp (by fun_prop)
    have hAn := hD.analyticOnNhd hU
    have hmem : ((c.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2) := by
      simp only [GlobalTheory.Cont.mem_rightOf]
      simp
      linarith
    refine ⟨H ((c.t : ℂ) / 2), ?_, H, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn,
      (c.n : ℝ) + c.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, rfl⟩
    refine mul_ne_zero ((hAb.converges ?_).ne_zero) ?_
    · simp
      linarith
    · refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun l hl => ?_
      have hl' := Finset.mem_range.1 hl
      have e : (c.t : ℂ) / 2 + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l = ((c.t - l : ℕ) : ℂ) := by
        rw [Nat.cast_sub hl'.le]
        ring
      rw [e]
      exact (hΛ i hi).2.2 _ (by omega)
  · intro c k B B' w h
    induction k with
    | zero => simpa [chainPar] using h
    | succ k ih =>
      apply ih
      rw [chainPar_succ, chainPar_succ] at h
      simp only [GlobalTheory.ChainOnto.stepPar] at h
      have h2 := add_right_cancel h
      exact Multiset.map_injective (mul_right_injective _) h2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainLValuesNeZeroAndParamsInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChain_LValues_ne_zero_and_params_injective : ∀ D : D7, ChainL D ∧ ∀ (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  first | exact @GlobalTheory.EvenOnto.chainL_and_inj | exact GlobalTheory.EvenOnto.chainL_and_inj | (intros; apply GlobalTheory.EvenOnto.chainL_and_inj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem exists_tprod_ne_zero_of_cc {D : D7} {c : Com D} {s : PiLocalization₂ D} (z : s.CC c) (hz : z ≠ 0) :
    ∃ v : s.M.Vec, PiTensorProduct.tprod ℂ v ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply hz
  apply Subtype.ext
  show (z : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0
  apply LinearMap.ext_on (PiTensorProduct.span_tprod_eq_top (R := ℂ) (s := fun τ => s.M.sm τ))
  rintro w ⟨v, rfl⟩
  simp [hne v]

theorem ip_unique {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD ipD' : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip ip' : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (h' : IsMet c s ipD' ip')
    (z : s.CC c) (hz : z ≠ 0) (x y : s.CC c) : ip x y = ip' x y := by
  obtain ⟨v, hv⟩ := exists_tprod_ne_zero_of_cc z hz
  have d : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) =
      ipD' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) := by rw [h.pure, h'.pure]
  have dne : ipD (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    intro h0
    have := h.posD _ hv
    rw [h0] at this
    simp at this
  have e1 := h.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  have e2 := h'.schur x y (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v)
  rw [e1, ← d] at e2
  exact mul_right_cancel₀ dne e2

theorem reach_is {D : D7} {c : Com D} {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {k : ℕ} {s : PiLocalization₂ D} {Θ : s.CC c →ₗ[ℂ] s₀.CC c}
    (hR : Reach c s₀ k s Θ) : s.Is c k := by
  cases hR with
  | zero => exact hs₀
  | step _ hs' _ _ => exact hs'

theorem thetaChain_upward_induction_fixed_metric {D : D7} (hMet : MetEx D) (hSU : StepUp D) {c : Com D} (hc : c.Is)
    {s₀ : PiLocalization₂ D} (hs₀ : s₀.Is c 0) {ipD₀ ip₀} (h₀ : IsMet c s₀ ipD₀ ip₀) {u : s₀.CC c} {B : GlobalTheory.LFun.Fam D.host.E}
    (hu : IsPar u B) (hL : ∀ k < c.m, LNe c (c.χ k) (chainPar c B k)) {k : ℕ} {s : PiLocalization₂ D}
    {Θ : s.CC c →ₗ[ℂ] s₀.CC c} (hR : Reach c s₀ k s Θ) : k ≤ c.m → s.Is c k ∧
      ∀ ipD ip, IsMet c s ipD ip → ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k) := by
  induction hR with
  | zero =>
    intro _
    refine ⟨hs₀, fun ipD ip h => ⟨u, fun y => ?_, hu⟩⟩
    exact ip_unique h h₀ u hu.1 y u
  | @step k s Θ _ s' hs' p hp ih =>
    intro hk
    obtain ⟨hsk, ih⟩ := ih (by omega)
    refine ⟨hs', fun ipD' ip' h' => ?_⟩
    obtain ⟨ipD, ip, hm⟩ := hMet c hc k (by omega) s hsk
    obtain ⟨x, hx, hxp⟩ := ih ipD ip hm
    obtain ⟨x', hx', hx'p⟩ := hSU c hc k (by omega) s s' hsk hs' p hp ipD ip ipD' ip' hm h' x (chainPar c B k) hxp
      (hL k (by omega))
    refine ⟨x', fun y => ?_, ?_⟩
    · rw [hx', hx]
      rfl
    · rw [chainPar_succ]
      exact hx'p

theorem chainUp_of : ∀ D : D7, MetEx D → ParBound D → ChainL D → StepUp D → ChainUp D := by
  intro D hMet hPB hCL hSU c hc s₀ hs₀ k hk s Θ hR
  refine ⟨reach_is hs₀ hR, fun ipD₀ ip₀ ipD ip h₀ h u B hu => ?_⟩
  have hb := hPB c hc 0 (Nat.zero_le _) s₀ hs₀ u B hu
  have hr : s₀.V.rank = c.n := by rw [hs₀.rank]; simp
  rw [hr] at hb
  exact (thetaChain_upward_induction_fixed_metric hMet hSU hc hs₀ h₀ hu (fun k hk => hCL c hc B hb k hk) hR hk).2 ipD ip h

theorem ontoAll_of : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ParBound D → StepUp D → OntoAll D := by
  intro D hFin hMet hEig hInd hPB hSU c hc s₀ hs₀ k hk s Θ hR
  have hUp := chainUp_of D hMet hPB (GlobalTheory.T.evenThetaChain_LValues_ne_zero_and_params_injective D).1 hSU
  obtain ⟨hs, hadj⟩ := hUp c hc s₀ hs₀ k hk s Θ hR
  obtain ⟨ipD₀, ip₀, hm₀⟩ := hMet c hc 0 (Nat.zero_le _) s₀ hs₀
  obtain ⟨ipD, ip, hm⟩ := hMet c hc k hk s hs
  haveI : FiniteDimensional ℂ (s₀.CC c) := hFin c hc 0 (Nat.zero_le _) s₀ hs₀
  let Sab := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
  let R : GlobalTheory.LFun.Fam D.host.E → GlobalTheory.LFun.Fam D.host.E → Prop := fun B B' => ∀ w ∉ Sab, B w = B' w
  have hRe : Equivalence R :=
    ⟨fun _ _ _ => rfl, fun h w hw => (h w hw).symm, fun h h' w hw => (h w hw).trans (h' w hw)⟩
  have hlin₀ := (GlobalTheory.T.multiplicity_vanishing_and_same_params_subspace D hMet).2 c s₀
  refine GlobalTheory.T.surjective_of_adjoint_separates_labelled_parts (s₀.CC c) (s.CC c) (GlobalTheory.LFun.Fam D.host.E) (GlobalTheory.LFun.Fam D.host.E) ip₀ ip Θ
    (fun u B => IsPar u B) (fun x B => IsPar x B) R R (fun B => chainPar c B k)
    hm₀.herm hm₀.pos hm.pos hRe (hEig c hc 0 (Nat.zero_le _) s₀ hs₀) hlin₀.1 hlin₀.2 ?_ ?_ ?_
  · intro B B' h w hw
    exact (GlobalTheory.T.evenThetaChain_LValues_ne_zero_and_params_injective D).2 c k B B' w (h w hw)
  · intro ι x B hx hne
    refine hInd c hc k hk s hs ι x B hx ?_
    intro i i' hii'
    have := hne i i' hii'
    by_contra hcon
    push_neg at hcon
    exact this hcon
  · intro u B hu
    exact hadj ipD₀ ip₀ ipD ip hm₀ hm u B hu

end GlobalTheory.EvenOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenRankThetaChainLift_surjective_of_adjoint_nonzero : ∀ D : D7, FinDim D → MetEx D → EigSpan D → ParIndep D → ParBound D → StepUp D → OntoAll D := by
  first | exact @GlobalTheory.EvenOnto.ontoAll_of | exact GlobalTheory.EvenOnto.ontoAll_of | (intros; apply GlobalTheory.EvenOnto.ontoAll_of <;> assumption)
end
