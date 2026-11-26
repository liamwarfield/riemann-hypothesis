module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Count1
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SeenFam
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.MemULOfSplit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PowRep
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem powRep : PowRep := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ u₁ u₂ φ T e₁ e₂ U R hφ hR hU
  obtain ⟨-, -, hpt, hval, -⟩ := ptOk E a b l₁ l₂ D A
  obtain ⟨-, -, -, -, -, hfx, -, -⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨hidm, -⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨-, hrep, hmono, hmul⟩ := repAlg E A.blk (chi l₁) (chi l₂)
  obtain ⟨hrt₁, hrt₂, -⟩ := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.rtAlg' E A.blk u₁ u₂
  have hc : 0 ≤ A.blk.c := A.c_nonneg
  have ok₁ : (A.ptB (A.fx S L T φ (fun _ => .one) fun _ => .one)).Ok :=
    hpt _ _ _ (hfx T φ _ _ hφ).1
  have ok₂ : (A.ptB (rt u₁ u₂ (A.idm S L))).Ok := by
    obtain ⟨r, hr⟩ := hrt₂ (A.ptB (A.idm S L)) (hpt _ _ _ hidm)
    exact hpt _ _ _ hr.ψ
  refine ⟨ok₁, ok₂, ?_⟩
  set t₁ := A.ptB (A.fx S L T φ (fun _ => .one) fun _ => .one) with ht₁
  set t₂ := A.ptB (rt u₁ u₂ (A.idm S L)) with ht₂
  have r₁0 : 0 ≤ max t₁.T t₁.r := le_max_of_le_left ok₁.T
  have r₂0 : 0 ≤ max t₂.T t₂.r := le_max_of_le_left ok₂.T
  have base₁ : Rep A.blk (chi l₁) (chi l₂) t₁.ψ 1 (max t₁.T t₁.r) t₁.op := by
    have := hrep t₁ ok₁
    rwa [hval] at this
  have base₂ : Rep A.blk (chi l₁) (chi l₂) t₂.ψ 1 (max t₂.T t₂.r) t₂.op := by
    have := hrep t₂ ok₂
    rwa [hval] at this
  have step : ∀ k : ℕ, Rep A.blk (chi l₁) (chi l₂)
      (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k) 1
      (max t₁.T t₁.r + k * (R + A.blk.c)) (t₁.op * U ^ k) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]
      exact base₁
    | succ k ih =>
      have h := hmul _ _ _ _ _ _ _ _ ih hU
      rw [(hfx T φ _ _ hφ).2.2 e₁ e₂, one_mul] at h
      have e : max t₁.T t₁.r + (k : ℝ) * (R + A.blk.c) + R + A.blk.c =
          max t₁.T t₁.r + ((k + 1 : ℕ) : ℝ) * (R + A.blk.c) := by
        push_cast; ring
      rw [e, mul_assoc, ← pow_succ] at h
      exact h
  refine ⟨max t₁.T t₁.r + max t₂.T t₂.r + A.blk.c, R + A.blk.c, by positivity, by positivity, fun k => ?_⟩
  have h := hmul _ _ _ _ _ _ _ _ (step k) base₂
  rw [one_mul] at h
  have hψ : mulF A.blk.ν (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k) t₂.ψ =
      rt u₁ u₂ (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k) := by
    show mulF A.blk.ν _ (rt u₁ u₂ (A.idm S L)) = _
    rw [hrt₁, (hfx T φ _ _ hφ).2.1]
  rw [hψ] at h
  refine hmono _ _ _ _ _ (le_of_eq ?_) h
  ring

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.CmbEll
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CmbEllOf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem trM_pt {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {l₁ : InfinitePlace E → DomWeight a}
    {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b} (A : Ar l₁ l₂ D) (S : Set (Pl E)) (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E)
    (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (t : PT A.blk) (ht : t.ψ = rt u₁ u₂ (A.ff S φ₁ φ₂)) :
    trM t.Φ A.tw = A.blk.vol⁻¹ • adel S u₁ u₂ (t.arch (Tl l₁) (Tl l₂)) φ₁ φ₂ := by
  funext g
  have hT3 : F.trM t.Φ (opM (Tl l₁) (Tl l₂) (1 : Matrix Unit Unit ℂ)) g = _ :=
    tensTr E a b (Ml l₁) (Ml l₂) Unit t.ka t.kb (Tl l₁) (Tl l₂) t.ψ 1 g
  have hA : ∏ v, t.arch (Tl l₁) (Tl l₂) v (GeneralLinearGroup.map (cV v) g.1, GeneralLinearGroup.map (cV v) g.2) =
      (∏ v, phiOf (Ml l₁ v) (Tl l₁ v) (t.ka v) (gInf v g.1)) * ∏ v, phiOf (Ml l₂ v) (Tl l₂ v) (t.kb v) (gInf v g.2) := by
    simp only [PT.arch]
    exact Finset.prod_mul_distrib
  have hF : finFn S φ₁ φ₂ (hFin g * (ratF E a u₁, ratF E b u₂)⁻¹) =
      ∏ᶠ v ∈ S, φ₁ v (cpt v u₁ g.1, cpt v u₂ g.2) * if IsSplitAt v then φ₂ v (cpt' v u₁ g.1, cpt' v u₂ g.2) else 1 := by
    simp only [finFn, Adel.cpt_eq, Adel.cpt'_eq]
    rfl
  refine hT3.trans ?_
  rw [ht, Pi.smul_apply, smul_eq_mul, adel, hA, ← hF]
  simp only [F.rt, Ar.ff, Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq]
  ring

theorem cmbEll_of (hT : CmbTest) (hS : SeenFam) (hSl : PositionTest) (hL : LefL) (hF : FfAlg) : CmbEll := by
  intro E _ _ _ hU a b l₁ l₂ D A μ₁ μ₂ h₁ h₂
  haveI := GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace E hU
  haveI := A.ha
  haveI := A.hb
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (GA E a) := ⟨rfl⟩
  haveI : BorelSpace (GA E b) := ⟨rfl⟩
  obtain ⟨c, hc, h4⟩ := global_character_holds E hU a b μ₁ μ₂ A.μa A.μb
  by_cases hv : A.blk.vol = 0
  · exact ⟨1, one_ne_zero, fun S _ _ hS' => absurd hv (hF E a b l₁ l₂ D A S hS').1⟩
  refine ⟨A.blk.vol⁻¹ * c * 2 ^ ((a + b) * Fintype.card (InfinitePlace E)),
    mul_ne_zero (mul_ne_zero (inv_ne_zero hv) hc) (pow_ne_zero _ two_ne_zero), ?_⟩
  intro S Z L hSec hZ u₁ u₂ hu₁ hu₂ φ T e₁ e₂ k C R hφ hreg hIn hR hC
  obtain ⟨c₀, hc₀, ht⟩ := hT E a b l₁ l₂ D A S Z L hSec hZ u₁ u₂ hu₁ hu₂
  have ht' := (ht φ T _ _ C R hφ hreg hR hC).1
  have hr : 0 ≤ c₀ * (1 + R) := mul_nonneg hc₀ (by linarith)
  obtain ⟨-, hseen, htest, -⟩ := (hS E a b S Z L hZ φ T e₁ e₂ hφ hIn).2 k
  obtain ⟨hln, -, hsl⟩ := hSl E a b S Z L hZ
  have h3 := G3.g3 E hU a b S hSec l₁ l₂ _ htest (by
    obtain ⟨w, hw, hw'⟩ := hreg
    exact ⟨w, (hZ w hw).1, by rw [fam, if_pos hw]; exact hw'⟩)
  have one : ∀ j ∈ C.s, ellSum2 μ₁ μ₂ (trM (C.t j).Φ A.tw) =
      A.blk.vol⁻¹ * c * 2 ^ ((a + b) * Fintype.card (InfinitePlace E)) * (C.t j).val (chi l₁) (chi l₂) *
        geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) := fun j hj => by
    obtain ⟨ok, hψ, -, -⟩ := hC j hj
    have e := trM_pt A S u₁ u₂ _ _ (C.t j) hψ
    have e' : adel S u₁ u₂ ((C.t j).arch (Tl l₁) (Tl l₂)) (intersection_update_fsHerm_neg_one Z T φ fun w => (e₁ w).pow k)
        (intersection_update_fsHerm_neg_one Z T L.ln fun w => (e₂ w).pow k) = ∑ _i ∈ ({()} : Finset Unit), A.blk.vol • trM (C.t j).Φ A.tw := by
      rw [Finset.sum_singleton, e, smul_smul, mul_inv_cancel₀ hv, one_smul]
    have h5 := h4 S hSec u₁ u₂ hu₁ hu₂ l₁ l₂ (fun v => (C.t j).va v (chi l₁ v) * (C.t j).vb v (chi l₂ v))
      ((C.t j).arch (Tl l₁) (Tl l₂)) _ _
      (fun v => (hL E a b l₁ l₂ D A).2 v _ _ _ _ _ (ok.ka v) (ok.kb v)) ((hsl φ hφ).2 T fun w => (e₁ w).pow k)
      ((hsl _ hln).2 T fun w => (e₂ w).pow k)
    rw [e', ellLin_holds E a b μ₁ μ₂ Unit _ _ _ _ hr (fun _ _ => ht' j hj), Finset.sum_singleton, hseen, h3,
      Finset.prod_mul_distrib] at h5
    have hval : (C.t j).val (chi l₁) (chi l₂) = (∏ v, (C.t j).va v (chi l₁ v)) * ∏ v, (C.t j).vb v (chi l₂ v) := rfl
    rw [hval, ← inv_mul_cancel_left₀ hv (ellSum2 μ₁ μ₂ (trM (C.t j).Φ A.tw)), h5]
    ring
  rw [Cmb.Φ, Growth.trM_sum, ellLin_holds E a b μ₁ μ₂ _ _ _ _ _ hr ht', Cmb.val, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [one j hj]
  ring

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

open UpperTheory.Zero.ConvolutionTheory.EB in
theorem UpperTheory.Zero.ConvolutionTheory.EB.cmbEll :
    UpperTheory.Zero.ConvolutionTheory.EB.CmbEll := cmbEll_of cmbTest seenFam positionTest lefL ffAlg
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.IdmAct
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH finH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

private theorem mem_Kg {S : Set (Pl E)} {L : ∀ w : Pl E, Subgroup (GLw n w)} {u : GL (Fin n) (Af E)} :
    u ∈ Kg S L ↔ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) u ∈ L w ∧
      (IsSplitAt w → GeneralLinearGroup.map (pLoc E w) (thF E n u) ∈ L w) := by
  simp only [Kg, Subgroup.mem_iInf, Subgroup.mem_inf, Subgroup.mem_comap]
  refine forall₂_congr fun w _ => and_congr_right fun _ => ?_
  split_ifs with hs
  · simp [hs, Subgroup.mem_comap]
  · simp [hs]

private theorem finFn_left {S : Set (Pl E)} {Z : Finset (Pl E)} (L : Lv a b Z) {φ₁ φ₂ : ∀ w : Pl E, LF a b w}
    (h₁ : ∀ w, ∀ k ∈ (L.L₁ w).prod (L.L₂ w), ∀ y, φ₁ w (k * y) = φ₁ w y)
    (h₂ : ∀ w, ∀ k ∈ (L.L₁ w).prod (L.L₂ w), ∀ y, φ₂ w (k * y) = φ₂ w y)
    {u₁ : GL (Fin a) (Af E)} {u₂ : GL (Fin b) (Af E)} (hu₁ : u₁ ∈ Kg S L.L₁) (hu₂ : u₂ ∈ Kg S L.L₂) (h : Hf E a b) :
    finFn S φ₁ φ₂ ((u₁, u₂) * h) = finFn S φ₁ φ₂ h := by
  unfold finFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨p₁, q₁⟩ := mem_Kg.1 hu₁ w hw
  obtain ⟨p₂, q₂⟩ := mem_Kg.1 hu₂ w hw
  have e₁ : atW w ((u₁, u₂) * h) =
      (GeneralLinearGroup.map (pLoc E w) u₁, GeneralLinearGroup.map (pLoc E w) u₂) * atW w h :=
    Prod.ext (map_mul _ _ _) (map_mul _ _ _)
  rw [e₁, h₁ w _ (Subgroup.mem_prod.2 ⟨p₁, p₂⟩)]
  split_ifs with hs
  · have e₂ : atW w (thP E a b ((u₁, u₂) * h)) =
        (GeneralLinearGroup.map (pLoc E w) (thF E a u₁), GeneralLinearGroup.map (pLoc E w) (thF E b u₂)) *
          atW w (thP E a b h) := by
      rw [map_mul]
      exact Prod.ext (map_mul _ _ _) (map_mul _ _ _)
    rw [e₂, h₂ w _ (Subgroup.mem_prod.2 ⟨q₁ hs, q₂ hs⟩)]
  · rfl

private theorem position_left {Z : Finset (Pl E)} (T : Finset (Pl E)) (L : Lv a b Z) {φ : ∀ w : Pl E, LF a b w}
    (hφ : L.Fix φ) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    ∀ k ∈ (L.L₁ w).prod (L.L₂ w), ∀ y, intersection_update_fsHerm_neg_one Z T φ e w (k * y) = intersection_update_fsHerm_neg_one Z T φ e w y := by
  intro k hk y
  unfold intersection_update_fsHerm_neg_one
  by_cases h1 : w ∈ Z
  · simp only [if_pos h1]
    exact ((hφ w h1).2 k hk y).1
  · simp only [if_neg h1]
    have hk' : k ∈ K2 a b w := by
      have ho := L.off w h1
      rw [ho.1, ho.2] at hk
      exact hk
    by_cases h2 : w ∈ T
    · simp only [if_pos h2]
      exact ((UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)).2 k hk' y).1
    · simp only [if_neg h2]
      have hc : k * y ∈ (K2 a b w : Set (GLw a w × GLw b w)) ↔ y ∈ (K2 a b w : Set (GLw a w × GLw b w)) :=
        (K2 a b w).mul_mem_cancel_left hk'
      by_cases hy : y ∈ (K2 a b w : Set (GLw a w × GLw b w))
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hc.2 hy)]
        rfl
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hc.1 h))]

private theorem relIndex_ne {Z : Finset (Pl E)} (L : Lv a b Z) (w : Pl E) :
    ((L.L₁ w).prod (L.L₂ w)).relIndex (K2 a b w) ≠ 0 := by
  have hc : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  have ho : IsOpen (((L.L₁ w).prod (L.L₂ w) : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (L.open₁ w).prod (L.open₂ w)
  haveI : CompactSpace (K2 a b w) := isCompact_iff_compactSpace.1 hc
  have ho' : IsOpen ((((L.L₁ w).prod (L.L₂ w)).subgroupOf (K2 a b w) : Subgroup (K2 a b w)) : Set (K2 a b w)) :=
    ho.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho'
  exact Subgroup.index_ne_zero_of_finite

private theorem ln_one_ne {Z : Finset (Pl E)} (L : Lv a b Z) (w : Pl E) : L.ln w 1 ≠ 0 := by
  unfold Lv.ln
  rw [Set.indicator_of_mem (Subgroup.one_mem _)]
  exact Nat.cast_ne_zero.2 (relIndex_ne L w)

private theorem finFn_one_ne (S : Set (Pl E)) {Z : Finset (Pl E)} (L : Lv a b Z) : finFn S L.ln L.ln 1 ≠ 0 := by
  unfold finFn
  refine finprod_mem_induction (fun x : ℂ => x ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun w _ => ?_
  have e₁ : atW w (1 : Hf E a b) = 1 := Prod.ext (map_one _) (map_one _)
  rw [map_one, e₁]
  refine mul_ne_zero (ln_one_ne L w) ?_
  split_ifs
  · exact ln_one_ne L w
  · exact one_ne_zero

end

theorem idmAct : IdmAct := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ
  have hfixln : L.Fix L.ln := fun w _ => (locAlg E a b Z L w).1
  have hlnl : ∀ w, ∀ k ∈ (L.L₁ w).prod (L.L₂ w), ∀ y, L.ln w (k * y) = L.ln w y :=
    fun w k hk y => (((locAlg E a b Z L w).1).2 k hk y).1
  have c1 : ∀ x y, ∀ u₁ ∈ Kg S L.L₁, ∀ u₂ ∈ Kg S L.L₂, ∀ h, A.idm S L x y ((u₁, u₂) * h) = A.idm S L x y h := by
    intro x y u₁ hu₁ u₂ hu₂ h
    show A.blk.vol⁻¹ * finFn S L.ln L.ln _ = A.blk.vol⁻¹ * finFn S L.ln L.ln _
    rw [finFn_left L hlnl hlnl hu₁ hu₂]
  refine ⟨c1, ?_, ?_⟩
  · intro T φ e₁ e₂ hφ x y u₁ hu₁ u₂ hu₂ h
    show A.blk.vol⁻¹ * finFn S _ _ _ = A.blk.vol⁻¹ * finFn S _ _ _
    rw [finFn_left L (fun w => position_left T L hφ e₁ w) (fun w => position_left T L hfixln e₂ w) hu₁ hu₂]
  · intro f hf
    haveI : BorelSpace (Hf E a b) := ⟨rfl⟩
    set K : Subgroup (Hf E a b) := (Kg S L.L₁).prod (Kg S L.L₂) with hKdef
    have hKo : IsOpen (K : Set (Hf E a b)) := by
      rw [hKdef, Subgroup.coe_prod]
      exact (kgFacts E a S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) fun w hw => (L.off w hw).1).1.prod
        (kgFacts E b S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) fun w hw => (L.off w hw).2).1
    have hKm : MeasurableSet (K : Set (Hf E a b)) := hKo.measurableSet
    set c : ℂ := A.idm S L () () 1 with hc
    have hvol : A.blk.vol ≠ 0 := (ffAlg E a b l₁ l₂ D A S hS).1
    have hc0 : c ≠ 0 := mul_ne_zero (inv_ne_zero hvol) (finFn_one_ne S L)
    have hmem : ∀ h ∈ K, A.idm S L () () h = c := by
      intro h hh
      have := c1 () () h.1 (Subgroup.mem_prod.1 hh).1 h.2 (Subgroup.mem_prod.1 hh).2 1
      rwa [mul_one] at this
    have hnot : ∀ h, h ∉ K → A.idm S L () () h = 0 := by
      intro h hh
      have hz : finFn S L.ln L.ln h = 0 := by
        by_contra hne
        have ht : IsTestP L.ln := (positionTest E a b S Z L hZ).2.1
        have key := fun w hw => GlobalTheory.CompanionTheory.FinTestTw.factors_ne_zero ht ht hne w hw
        have m : ∀ w ∈ S, atW w h ∈ (L.L₁ w).prod (L.L₂ w) ∧
            (IsSplitAt w → atW w (thP E a b h) ∈ (L.L₁ w).prod (L.L₂ w)) := fun w hw =>
          ⟨Set.mem_of_indicator_ne_zero (key w hw).1, fun hs => Set.mem_of_indicator_ne_zero ((key w hw).2 hs)⟩
        refine hh (Subgroup.mem_prod.2 ⟨mem_Kg.2 fun w hw => ⟨(Subgroup.mem_prod.1 (m w hw).1).1, fun hs => ?_⟩,
          mem_Kg.2 fun w hw => ⟨(Subgroup.mem_prod.1 (m w hw).1).2, fun hs => ?_⟩⟩)
        · exact (Subgroup.mem_prod.1 ((m w hw).2 hs)).1
        · exact (Subgroup.mem_prod.1 ((m w hw).2 hs)).2
      show A.blk.vol⁻¹ * finFn S L.ln L.ln h = 0
      rw [hz, mul_zero]
    have hone : (A.ν.real (K : Set (Hf E a b)) : ℂ) * c = 1 := by
      have h0 := congrFun (congrFun (congrFun (hkMul E a b l₁ l₂ D A S Z L hS hZ).2.1 ()) ()) 1
      have hi : (fun h => A.idm S L () () h * A.idm S L () () (h⁻¹ * 1)) =
          (K : Set (Hf E a b)).indicator fun _ => c * c := by
        funext h
        by_cases hh : h ∈ K
        · rw [Set.indicator_of_mem (show h ∈ (K : Set (Hf E a b)) from hh), hmem h hh,
            hmem _ (by simpa using K.inv_mem hh)]
        · rw [Set.indicator_of_notMem (show h ∉ (K : Set (Hf E a b)) from hh), hnot h hh, zero_mul]
      have h1 : ∫ h, A.idm S L () () h * A.idm S L () () (h⁻¹ * 1) ∂A.ν = c := by
        simpa [mulF] using h0
      rw [hi, integral_indicator_const _ hKm] at h1
      have h2 : c * ((A.ν.real (K : Set (Hf E a b)) : ℂ) * c) = c * 1 := by
        rw [mul_one]
        simpa [Complex.real_smul, mul_assoc, mul_comm, mul_left_comm] using h1
      exact mul_left_cancel₀ hc0 h2
    funext i x
    have hi : (fun h => A.idm S L i.2 () h * f (i.1, ()) (x * finH h)) =
        (K : Set (Hf E a b)).indicator fun _ => c * f i x := by
      funext h
      by_cases hh : h ∈ K
      · rw [Set.indicator_of_mem (show h ∈ (K : Set (Hf E a b)) from hh)]
        have := hf (i.1, ()) h.1 (Subgroup.mem_prod.1 hh).1 h.2 (Subgroup.mem_prod.1 hh).2 x
        show A.idm S L () () h * f (i.1, ()) (x * (finGL E a h.1, finGL E b h.2)) = _
        rw [this, hmem h hh]
      · rw [Set.indicator_of_notMem (show h ∉ (K : Set (Hf E a b)) from hh)]
        show A.idm S L () () h * _ = 0
        rw [hnot h hh, zero_mul]
    show ∑ z : Unit, ∫ h, A.idm S L i.2 z h * f (i.1, z) (x * finH h) ∂A.ν = f i x
    rw [Fintype.sum_unique]
    show ∫ h, A.idm S L i.2 () h * f (i.1, ()) (x * finH h) ∂A.ν = f i x
    rw [hi, integral_indicator_const _ hKm, Complex.real_smul, ← mul_assoc, hone, one_mul]

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.GenSt
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HkComm
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SphComm2
theorem UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 :
    UpperTheory.Zero.ConvolutionTheory.EB.SphComm2 := by
  intro E _ _ _ a b w f f' hf hf'
  exact PositivityTheory.Rg.BcB.F.sphComm E a b w f f' hf hf'
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private theorem position_sph (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∉ Z) : IsHecke (K2 a b w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_neg hw]
  split_ifs
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w (e w)
  · exact UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one

private theorem position_Z (Z T : Finset (Pl E)) (L : Lv a b Z) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (w : Pl E) (hw : w ∈ Z) : intersection_update_fsHerm_neg_one Z T L.ln e w = L.ln w := by
  unfold intersection_update_fsHerm_neg_one
  rw [if_pos hw]

private theorem position_comm (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (intersection_update_fsHerm_neg_one Z T' L.ln e' w) =
      PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T' L.ln e' w) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw) (position_sph Z T' L e' w hw)

private theorem position_comm_star (Z T T' : Finset (Pl E)) (L : Lv a b Z) (e e' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) :
    PositivityTheory.Rg.BcN.F2.mconv (intersection_update_fsHerm_neg_one Z T L.ln e w) (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) =
      PositivityTheory.Rg.BcN.F2.mconv (lfStar (intersection_update_fsHerm_neg_one Z T' L.ln e' w)) (intersection_update_fsHerm_neg_one Z T L.ln e w) := by
  have hl := UpperTheory.Zero.ConvolutionTheory.EB.locAlg E a b Z L w
  by_cases hw : w ∈ Z
  · rw [position_Z Z T L e w hw, position_Z Z T' L e' w hw, hl.2.1]
  · exact UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 E a b w _ _ (position_sph Z T L e w hw)
      ((hl.2.2.2.2 _ (position_sph Z T' L e' w hw)).2.2)

theorem _root_.UpperTheory.Zero.ConvolutionTheory.EB.hkComm :
    UpperTheory.Zero.ConvolutionTheory.EB.HkComm := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ T T' e₁ e₂ e₁' e₂'
  have hst := UpperTheory.Zero.ConvolutionTheory.EB.positionTest E a b S Z L hZ
  have ht : ∀ (T : Finset (Pl E)) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))), IsTestP (intersection_update_fsHerm_neg_one Z T L.ln e) :=
    fun T e => (hst.2.2 L.ln hst.1).2 T e
  have hf := (UpperTheory.Zero.ConvolutionTheory.EB.ffAlg E a b l₁ l₂ D A S hS).2
  have h1 := hf _ _ (ht T e₁) (ht T e₂)
  have h2 := hf _ _ (ht T' e₁') (ht T' e₂')
  have hstar := h2.2.1
  refine ⟨?_, ?_⟩
  · show mulF A.ν (A.ff S _ _) (A.ff S _ _) = mulF A.ν (A.ff S _ _) (A.ff S _ _)
    rw [h1.2.2.2.2 _ _ (ht T' e₁') (ht T' e₂'), h2.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm Z T T' L e₁ e₁', position_comm Z T T' L e₂ e₂']
  · show mulF A.ν (A.ff S _ _) (adjF (A.ff S _ _)) = mulF A.ν (adjF (A.ff S _ _)) (A.ff S _ _)
    rw [hstar]
    have hs := hf _ _ h2.2.2.1 h2.2.2.2.1
    rw [h1.2.2.2.2 _ _ h2.2.2.1 h2.2.2.2.1, hs.2.2.2.2 _ _ (ht T e₁) (ht T e₂)]
    simp only [position_comm_star Z T T' L e₁ e₁', position_comm_star Z T T' L e₂ e₂']

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem genSt : GenSt := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ T e₁ e₂
  have hPt := ptOk E a b l₁ l₂ D A
  have hMul := hkMul E a b l₁ l₂ D A S Z L hS hZ
  have hComm := hkComm E a b l₁ l₂ D A S Z L hS hZ
  have hidm : ∀ e e', A.hk S L ∅ e e' = A.idm S L := hMul.2.2.2.2.1
  have hfin : ∀ T' e e', IsFinM (A.hk S L T' e e') := fun T' e e' => (hMul.2.2.2.2.2.2.1 T' e e').1

  have hform : ∀ γ : Gam a b S Z, ∃ wa wb T' e e',
      A.gen S L T e₁ e₂ γ = A.pt wa wb (A.hk S L T' e e') := by
    rintro (_ | x | x | _)
    · exact ⟨_, _, ∅, fun _ => .one, fun _ => .one, by
        rw [hidm]; rfl⟩
    · exact ⟨_, _, ∅, fun _ => .one, fun _ => .one, by
        rw [hidm]; rfl⟩
    · exact ⟨_, _, _, _, _, rfl⟩
    · exact ⟨_, _, _, _, _, rfl⟩
  have hok : ∀ γ, (A.gen S L T e₁ e₂ γ).Ok := by
    intro γ
    obtain ⟨wa, wb, T', e, e', h⟩ := hform γ
    rw [h]
    exact hPt.2.2.1 wa wb _ (hfin T' e e')
  refine ⟨⟨hok, ?_, ?_⟩, ?_⟩
  · intro x y
    obtain ⟨wa, wb, T', e, e', h⟩ := hform x
    obtain ⟨wa', wb', T'', f, f', h'⟩ := hform y
    have hx := hok x
    have hy := hok y
    rw [h] at hx ⊢
    rw [h'] at hy ⊢
    exact BlockFiniteConvolution.blkComm₀ E A.blk _ _ hx hy (hComm T' T'' e e' f f').1
  · intro x y
    obtain ⟨wa, wb, T', e, e', h⟩ := hform x
    obtain ⟨wa', wb', T'', f, f', h'⟩ := hform y
    have hx := hok x
    have hy := hok y
    rw [h] at hx ⊢
    rw [h'] at hy ⊢
    have hop := BlockFiniteConvolution.blkOp₀ E A.blk _ _ hy hy
    rw [ContinuousLinearMap.star_eq_adjoint, ← hop.2.2.2.2.2.1]
    exact BlockFiniteConvolution.blkComm₀ E A.blk _ _ hx hop.2.2.2.2.1 (hComm T' T'' e e' f f').2
  · haveI : Countable (Pl E) := Small.countable_pl E
    infer_instance

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
