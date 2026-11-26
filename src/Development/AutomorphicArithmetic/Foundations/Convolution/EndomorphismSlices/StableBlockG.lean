module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.BadFinite
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RStable
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbAlg

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RealUnivNe
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

private theorem isTestH_sum {a b : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {J : Type} (s : Finset J)
    (f : J → H E a b → ℂ) (h : ∀ j ∈ s, IsTestH (f j)) : IsTestH (∑ j ∈ s, f j) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ⟨continuous_zero, HasCompactSupport.zero⟩
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩

private theorem isTestH_trM {a b : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {ι : Type} [Fintype ι]
    (Φ : Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) (h : IsTestM Φ) : IsTestH (trM Φ M) := by
  have e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i := by
    funext y
    simp [trM, Finset.sum_apply]
  rw [e]
  refine isTestH_sum _ _ fun i _ => isTestH_sum _ _ fun j _ => ?_
  exact ⟨(h i j).1.mul continuous_const, (h i j).2.mul_right⟩

private theorem lef_zero (lam : Fin 0 → ℤ) (μ : Measure (G 0)) [μ.IsHaarMeasure] (k : Mat 0 → ((lefE 0 lam).V →L[ℂ] (lefE 0 lam).V))
    (val : Inf 0 → ℂ) (T : ℝ) (hm : IsMult μ (lefE 0 lam) k val T) :
    (μ.real Set.univ : ℂ) * phiOf (lefE 0 lam) (lefT 0 lam) k 1 = val (infOf lam) := by
  haveI : BorelSpace (G 0) := ⟨rfl⟩
  have h := ((lefModel 0 lam (fun i => i.elim0)).2.2.2 μ k val T hm).2 1 (fun i => i.elim0)
    (Subsingleton.elim _ _) (fun a => a.elim0) (Function.injective_of_subsingleton _)
  have e : (fun x : G 0 => phiOf (lefE 0 lam) (lefT 0 lam) k (PositivityTheory.RgTw.tw x 1)) =
      fun _ => phiOf (lefE 0 lam) (lefT 0 lam) k 1 := by
    funext x
    rw [Subsingleton.elim (PositivityTheory.RgTw.tw x 1) 1]
  have h2 := h.2
  rw [e, integral_const] at h2
  simpa [weylChar] using h2

private theorem real_univ_ne (μ : Measure (G 0)) [μ.IsHaarMeasure] : (μ.real Set.univ : ℂ) ≠ 0 := by
  have h1 : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have h2 : μ Set.univ ≠ ⊤ := (Set.subsingleton_of_subsingleton.isCompact.measure_lt_top).ne
  exact_mod_cast (ENNReal.toReal_ne_zero.2 ⟨h1, h2⟩)

theorem cmbPi : PiTerm → TwTrSum → CmbPi := by
  intro hPi hSum E _ _ _ hU n hn π hreg hdual
  obtain ⟨l, hl, hP⟩ := hPi E hU n hn π hreg hdual
  refine ⟨l, hl, ?_⟩
  intro l₂ D A S hS Z hZ B τ hB hτ u₁ u₂ hu₁
  haveI := A.ha
  haveI := A.hb
  have hμ : D.μ.IsHaarMeasure := by
    obtain ⟨h1, -, h3, h4⟩ := D.haar
    exact { }
  obtain ⟨c₀, hc₀, hc⟩ := hP S hS Z hZ B τ hB hτ u₁ hu₁ A.μa D.μ A.ha hμ
  have hvol : A.blk.vol ≠ 0 := (ffAlg E n 0 l l₂ D A S hS).1
  have hm := real_univ_ne A.μb
  generalize hmdef : (A.μb.real Set.univ : ℂ) = m at hm
  refine ⟨c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E),
    mul_ne_zero (mul_ne_zero hc₀ (inv_ne_zero hvol)) (pow_ne_zero _ (inv_ne_zero hm)), ?_⟩
  intro L φ T e₁ e₂ C R hφ hTE hTZ hC
  have hLc : ∀ w ∈ Z, Lc (K2 n 0 w) (φ w) ∧ Lc (K2 n 0 w) (L.ln w) := by
    intro w hw
    have h := positionTest E n 0 S Z L hZ
    exact ⟨(h.2.2 φ hφ).1 w hw, (h.2.2 L.ln h.1).1 w hw⟩
  have hseen : ∀ w ∈ Z, (fun g => seen φ L.ln w (g, 1)) = fun g => φ w (g, 1) := by
    intro w hw
    have h := ((locAlg E n 0 Z L w).2.2.2.1 (φ w) (hφ w hw)).1
    funext g
    simp only [seen, if_pos (hZ w hw).2]
    exact congrFun h (g, 1)
  have hX : (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => seen φ L.ln w (g, 1)) =
      ∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => φ w (g, 1) :=
    Finset.prod_congr rfl fun w hw => by rw [hseen w hw]
  generalize (∏ w ∈ Z, trc (τ w).ρ (KGL w (n := n)) fun g => φ w (g, 1)) = X at hX ⊢
  have term : ∀ j ∈ C.s, IsTestH (trM (C.t j).Φ A.tw) ∧ IsTwTr D.μ π (trM (C.t j).Φ A.tw)
      (c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * (C.t j).val (chi l) (chi l₂) * X * val T e₁ e₂ B 0) := by
    intro j hj
    obtain ⟨ok, hψ, -, -⟩ := hC j hj
    generalize C.t j = t at ok hψ ⊢
    have hPt := hc φ L.ln hLc T hTZ e₁ e₂ t.ka t.va t.T hTE ok.ka
    rw [hX] at hPt
    have hf : trM t.Φ A.tw = ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) •
        phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) := by
      funext g
      have h1 := tensTr E n 0 (Ml l) (Ml l₂) Unit t.ka t.kb (Tl l) (Tl l₂) t.ψ 1 g
      have hp : (hFin g * (ratF E n u₁, ratF E 0 u₂)⁻¹ : Hf E n 0) = (finOf E n g.1 * (ratF E n u₁)⁻¹, 1) :=
        Prod.ext rfl (Subsingleton.elim _ _)
      have hg : ∀ v, gInf v g.2 = 1 := fun v => Subsingleton.elim _ _
      have h2 : ∑ x, ∑ y, t.ψ x y (hFin g) * (1 : Matrix Unit Unit ℂ) y x =
          A.blk.vol⁻¹ * finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂) (finOf E n g.1) := by
        rw [hψ]
        simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq, mul_one]
        show A.blk.vol⁻¹ * finFn S _ _ (hFin g * (ratF E n u₁, ratF E 0 u₂)⁻¹) = _
        rw [hp]
        rfl
      refine h1.trans ?_
      rw [h2]
      simp only [hg, Pi.smul_apply, smul_eq_mul, phiProd]
      show (∏ v, phiOf (lefE n (l v).w) (lefT n (l v).w) (t.ka v) (gInf v g.1)) * _ * _ = _
      have h3 : ∀ v, gInf v g.1 = infAt E n v g.1 := fun v => rfl
      simp only [h3]
      show _ * (∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * _ = _
      ring
    have hval : c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * t.val (chi l) (chi l₂) * X * val T e₁ e₂ B 0 =
        ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) *
          (c₀ * (∏ v, t.va v (infOf (l v).w)) * X * val T e₁ e₂ B 0) := by
      have hb : ∀ v, t.vb v (chi l₂ v) = m * phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1 := fun v => by
        rw [← hmdef]
        exact (lef_zero (l₂ v).w A.μb (t.kb v) (t.vb v) t.T (ok.kb v)).symm
      have e : t.val (chi l) (chi l₂) = (∏ v, t.va v (infOf (l v).w)) *
          (m ^ Fintype.card (InfinitePlace E) * ∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) := by
        show (∏ v, t.va v (chi l v)) * ∏ v, t.vb v (chi l₂ v) = _
        simp only [hb, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        rfl
      rw [e, inv_pow]
      field_simp
    have htest : IsTestH (trM t.Φ A.tw) := isTestH_trM _ _ (BlockFiniteConvolution.blkOp₀ E A.blk t t ok ok).1
    refine ⟨htest, ?_⟩
    rw [hval, hf]
    by_cases h0 : (∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹ = 0
    · have h := hSum E n D π Empty ∅ (fun _ => 0) (fun _ => 0) (fun _ => 0) (by simp)
      rw [h0, zero_smul, zero_mul]
      simpa using h
    · rw [hf] at htest
      have hPtest : IsTestH (phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))) := by
        refine ⟨(continuous_const_smul_iff₀ h0).1 htest.1, ?_⟩
        have h1 := htest.2.mul_left (f := fun _ => ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹)⁻¹)
        have e : phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) = fun y =>
            ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹)⁻¹ *
              (((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) •
                phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))) y := by
          funext y
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [inv_mul_cancel_left₀ h0]
        rw [e]
        exact h1
      have key : ∀ (s : ℂ) (P : H E n 0 → ℂ) (x : ℂ), IsTestH P → IsTwTr D.μ π P x → IsTwTr D.μ π (s • P) (s * x) := by
        intro s P x h1 h2
        have h := hSum E n D π Unit {()} (fun _ => s) (fun _ => P) (fun _ => x) (fun _ _ => ⟨h1, h2⟩)
        simpa using h
      exact key _ _ _ hPtest hPt
  have hS' := hSum E n D π C.J C.s C.c (fun j => trM (C.t j).Φ A.tw) _ term
  have e1 : trM C.Φ A.tw = ∑ j ∈ C.s, C.c j • trM (C.t j).Φ A.tw := Growth.trM_sum _ _ _ _
  have e2 : c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * C.val (chi l) (chi l₂) * X * val T e₁ e₂ B 0 =
      ∑ j ∈ C.s, C.c j * (c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * (C.t j).val (chi l) (chi l₂) * X *
        val T e₁ e₂ B 0) := by
    rw [Cmb.val, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  exact hS'

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PeakRun
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.ExistsGap
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison

section Core

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {B : Type} [CommRing B] [StarRing B]
  [Algebra ℂ B] [StarModule ℂ B] (Φ : B →⋆ₐ[ℂ] C(X, ℂ)) (A : StarSubalgebra ℂ B)
  (p : A →⋆ₐ[ℂ] ℂ)

private def Nn (c : A) : Prop :=
  p c = 0 ∧ ∀ χ, (Φ (c : B) χ).im = 0 ∧ 0 ≤ (Φ (c : B) χ).re

private lemma nn_add {c d : A} (hc : Nn Φ A p c) (hd : Nn Φ A p d) : Nn Φ A p (c + d) := by
  refine ⟨by simp [hc.1, hd.1], fun χ => ?_⟩
  have h₁ := hc.2 χ
  have h₂ := hd.2 χ
  have e : Φ ((c + d : A) : B) χ = Φ (c : B) χ + Φ (d : B) χ := by simp
  rw [e, Complex.add_im, Complex.add_re]
  exact ⟨by rw [h₁.1, h₂.1, add_zero], add_nonneg h₁.2 h₂.2⟩

private lemma sq_apply (b : A) (χ : X) :
    Φ ((star b * b : A) : B) χ = ((‖Φ (b : B) χ‖ ^ 2 : ℝ) : ℂ) := by
  have e : Φ ((star b * b : A) : B) χ = star (Φ (b : B) χ) * Φ (b : B) χ := by
    simp [map_mul, map_star]
  rw [e]
  simpa using Complex.conj_mul' (Φ (b : B) χ)

private lemma nn_sq {b : A} (hb : p b = 0) : Nn Φ A p (star b * b) := by
  refine ⟨by simp [map_mul, map_star, hb], fun χ => ?_⟩
  rw [sq_apply]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩

private lemma exists_sep {K : Set X} (hK : IsCompact K)
    (hd : ∀ χ ∈ K, ∃ a : A, Φ (a : B) χ ≠ p a) :
    ∃ c : A, Nn Φ A p c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ χ ∈ K, δ ≤ (Φ (c : B) χ).re := by
  refine hK.induction_on
    (p := fun S => ∃ c : A, Nn Φ A p c ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ χ ∈ S, δ ≤ (Φ (c : B) χ).re)
    ?_ ?_ ?_ ?_
  · exact ⟨0, ⟨by simp, fun χ => by simp⟩, 1, one_pos, by simp⟩
  · rintro S T hST ⟨c, hc, δ, hδ, h⟩
    exact ⟨c, hc, δ, hδ, fun χ hχ => h χ (hST hχ)⟩
  · rintro S T ⟨c, hc, δ, hδ, h⟩ ⟨d, hd', ε, hε, h'⟩
    refine ⟨c + d, nn_add Φ A p hc hd', min δ ε, lt_min hδ hε, ?_⟩
    rintro χ (hχ | hχ)
    · have e : Φ ((c + d : A) : B) χ = Φ (c : B) χ + Φ (d : B) χ := by simp
      rw [e, Complex.add_re]
      have := (hd'.2 χ).2
      have := h χ hχ
      have := min_le_left δ ε
      linarith
    · have e : Φ ((c + d : A) : B) χ = Φ (c : B) χ + Φ (d : B) χ := by simp
      rw [e, Complex.add_re]
      have := (hc.2 χ).2
      have := h' χ hχ
      have := min_le_right δ ε
      linarith
  · intro χ hχ
    obtain ⟨a, ha⟩ := hd χ hχ
    set b : A := a - algebraMap ℂ A (p a) with hbdef
    have hb : p b = 0 := by
      rw [hbdef, map_sub, AlgHomClass.commutes]
      simp
    have hbχ : Φ (b : B) χ ≠ 0 := by
      have e : Φ (b : B) χ = Φ (a : B) χ - p a := by
        simp [hbdef, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]
      rw [e]
      exact sub_ne_zero.2 ha
    have hpos : 0 < ‖Φ (b : B) χ‖ ^ 2 / 2 := by
      have := norm_pos_iff.2 hbχ
      positivity
    have hopen : IsOpen {y : X | ‖Φ (b : B) χ‖ ^ 2 / 2 < (Φ ((star b * b : A) : B) y).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp (map_continuous _))
    have hmem : χ ∈ {y : X | ‖Φ (b : B) χ‖ ^ 2 / 2 < (Φ ((star b * b : A) : B) y).re} := by
      rw [Set.mem_setOf_eq, sq_apply, Complex.ofReal_re]
      linarith
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem), star b * b, nn_sq Φ A p hb,
      _, hpos, fun y hy => le_of_lt hy⟩

private lemma exists_gap (x : B) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ χ, (∀ a : A, Φ (a : B) χ = p a) → ‖Φ x χ‖ < ρ) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < ρ ∧ ∀ χ, (∀ a : A, Φ (a : B) χ = p a) → ‖Φ x χ‖ < ρ' := by
  have hcl : IsClosed {χ : X | ∀ a : A, Φ (a : B) χ = p a} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun a => isClosed_eq (map_continuous _) continuous_const
  rcases Set.eq_empty_or_nonempty {χ : X | ∀ a : A, Φ (a : B) χ = p a} with he | hne
  · refine ⟨ρ / 2, by positivity, by linarith, fun χ hχ => ?_⟩
    have : χ ∈ {χ : X | ∀ a : A, Φ (a : B) χ = p a} := hχ
    rw [he] at this
    exact this.elim
  · obtain ⟨χ₀, h₀, hmax⟩ := hcl.isCompact.exists_isMaxOn hne
      (f := fun χ => ‖Φ x χ‖) (continuous_norm.comp (map_continuous _)).continuousOn
    have h₁ := h χ₀ h₀
    have h₂ := norm_nonneg (Φ x χ₀)
    refine ⟨(‖Φ x χ₀‖ + ρ) / 2, by linarith, by linarith, fun χ hχ => ?_⟩
    have : ‖Φ x χ‖ ≤ ‖Φ x χ₀‖ := hmax hχ
    linarith

end Core

section Rep

private theorem exists_rep {B : Type} [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : B →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ (X : Type) (_ : TopologicalSpace X) (_ : CompactSpace X) (Φ : B →⋆ₐ[ℂ] C(X, ℂ)),
      ∀ y, ‖Φ y‖ = ‖R y‖ := by
  let S : StarSubalgebra ℂ (H →L[ℂ] H) := R.range
  have hcomm : ∀ u v : S, u * v = v * u := by
    rintro ⟨_, y, rfl⟩ ⟨_, z, rfl⟩
    apply Subtype.ext
    show R y * R z = R z * R y
    rw [← map_mul, ← map_mul, mul_comm]
  let C := S.topologicalClosure
  have hmc : ∀ u v : C, u * v = v * u := (S.commRingTopologicalClosure hcomm).mul_comm
  haveI hcl : IsClosed (C : Set (H →L[ℂ] H)) := S.isClosed_topologicalClosure
  letI : CStarAlgebra C := inferInstance
  letI : CommCStarAlgebra C := { mul_comm := hmc }
  let G : C →⋆ₐ[ℂ] C(WeakDual.characterSpace ℂ C, ℂ) := (gelfandStarTransform C).toStarAlgHom
  have hmem : ∀ y, R y ∈ C := fun y => S.le_topologicalClosure ⟨y, rfl⟩
  let ι : B →⋆ₐ[ℂ] C := R.codRestrict C hmem
  refine ⟨_, inferInstance, inferInstance, G.comp ι, fun y => ?_⟩
  simpa [G, ι, gelfandStarTransform] using
    (gelfandTransform_isometry C).norm_map_of_map_zero (map_zero _) (ι y)

end Rep

section Peak

variable {X : Type} [TopologicalSpace X] [CompactSpace X] {B : Type} [CommRing B] [StarRing B]
  [Algebra ℂ B] [StarModule ℂ B] (Φ : B →⋆ₐ[ℂ] C(X, ℂ)) (A : StarSubalgebra ℂ B)
  (p : A →⋆ₐ[ℂ] ℂ)

private theorem core (a₀ : A) (x : B) {ρ : ℝ} (ha : p a₀ = 1) (hρ : 0 < ρ)
    (h : ∀ χ, (∀ a : A, Φ (a : B) χ = p a) → ‖Φ x χ‖ < ρ) :
    ∃ g : A, p g = 1 ∧ ‖Φ (x * (g * a₀ : A))‖ < ρ := by
  obtain ⟨ρ', h0, h1, hg⟩ := exists_gap Φ A p x hρ h
  have hKc : IsCompact {χ : X | ρ' ≤ ‖Φ x χ‖} :=
    (isClosed_le continuous_const (continuous_norm.comp (map_continuous _))).isCompact
  obtain ⟨c, hc, δ, hδ, hcK⟩ := exists_sep Φ A p hKc (fun χ hχ => by
    by_contra hne
    push_neg at hne
    exact absurd (hg χ hne) (not_lt.2 hχ))
  obtain ⟨b, hbdef⟩ : ∃ b : A, b = a₀ - 1 := ⟨_, rfl⟩
  have hb : p b = 0 := by rw [hbdef, map_sub, map_one, ha, sub_self]
  have hbχ : ∀ χ, Φ (b : B) χ = Φ (a₀ : B) χ - 1 := fun χ => by simp [hbdef]
  obtain ⟨d, hddef⟩ : ∃ d : A, d = c + star b * b := ⟨_, rfl⟩
  have hd : Nn Φ A p d := hddef ▸ nn_add Φ A p hc (nn_sq Φ A p hb)
  have hdχ : ∀ χ, (Φ (d : B) χ).re = (Φ (c : B) χ).re + ‖Φ (b : B) χ‖ ^ 2 := fun χ => by
    have e : Φ (d : B) χ = Φ (c : B) χ + Φ ((star b * b : A) : B) χ := by
      have e₀ : ((c + star b * b : A) : B) = (c : B) + ((star b * b : A) : B) := rfl
      rw [hddef, e₀, map_add (f := _), ContinuousMap.add_apply]
    rw [e, Complex.add_re, sq_apply, Complex.ofReal_re]
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (ρ - ρ') / ρ' := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact div_pos (sub_pos.2 h1) h0
  have hρε : ρ' * (1 + ε) = ρ := by rw [hεdef]; field_simp; ring
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min δ (ε ^ 2) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact lt_min hδ (by positivity)
  have hηδ : η ≤ δ := by rw [hηdef]; exact min_le_left _ _
  have hηε : η ≤ ε ^ 2 := by rw [hηdef]; exact min_le_right _ _
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ‖Φ (d : B)‖ + η + 1 := ⟨_, rfl⟩
  have hdn := norm_nonneg (Φ (d : B))
  have hM : 0 < M := by rw [hMdef]; linarith
  have hηM : η < M := by rw [hMdef]; linarith
  have ht : ∀ χ, Φ (d : B) χ = (((Φ (d : B) χ).re : ℝ) : ℂ) := fun χ =>
    Complex.ext (by simp) (by simp [(hd.2 χ).1])
  have ht0 : ∀ χ, 0 ≤ (Φ (d : B) χ).re := fun χ => (hd.2 χ).2
  have htM : ∀ χ, (Φ (d : B) χ).re ≤ M := fun χ => by
    have h₁ := Complex.re_le_norm (Φ (d : B) χ)
    have h₂ := ContinuousMap.norm_coe_le_norm (Φ (d : B)) χ
    rw [hMdef]
    linarith
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = 1 - η / M := ⟨_, rfl⟩
  have hθ1 : θ < 1 := by rw [hθdef]; have := div_pos hη hM; linarith
  have hθ0 : 0 < θ := by
    rw [hθdef, sub_pos, div_lt_one hM]
    exact hηM
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ‖Φ x‖ * ‖Φ (a₀ : B)‖ + 1 := ⟨_, rfl⟩
  have hL : 0 < L := by rw [hLdef]; positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hρ hL) hθ1
  have hn' : L * θ ^ n < ρ := by rwa [lt_div_iff₀' hL] at hn
  obtain ⟨g, hgdef⟩ : ∃ g : A, g = (1 - algebraMap ℂ A ((M : ℂ)⁻¹) * d) ^ n := ⟨_, rfl⟩
  refine ⟨g, ?_, ?_⟩
  · rw [hgdef, map_pow, map_sub, map_one, map_mul, hd.1, mul_zero, sub_zero, one_pow]
  have hgχ : ∀ χ, Φ (g : B) χ = (((1 - (Φ (d : B) χ).re / M) ^ n : ℝ) : ℂ) := fun χ => by
    have e : Φ (g : B) χ = (1 - (M : ℂ)⁻¹ * Φ (d : B) χ) ^ n := by
      simp [hgdef, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]
    rw [e, ht χ]
    push_cast
    simp [div_eq_inv_mul]
  rw [ContinuousMap.norm_lt_iff _ hρ]
  intro χ
  have e : Φ (x * (g * a₀ : A)) χ = Φ x χ * (Φ (g : B) χ * Φ (a₀ : B) χ) := by simp
  rw [e, norm_mul, norm_mul]
  have h1t : 0 ≤ 1 - (Φ (d : B) χ).re / M := by
    rw [sub_nonneg, div_le_one hM]
    exact htM χ
  have h2t : 1 - (Φ (d : B) χ).re / M ≤ 1 := by
    have := div_nonneg (ht0 χ) hM.le
    linarith
  have hgn : ‖Φ (g : B) χ‖ = (1 - (Φ (d : B) χ).re / M) ^ n := by
    rw [hgχ, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg h1t n)]
  by_cases hcase : η ≤ (Φ (d : B) χ).re
  · have hgθ : ‖Φ (g : B) χ‖ ≤ θ ^ n := by
      rw [hgn]
      refine pow_le_pow_left₀ h1t ?_ n
      rw [hθdef]
      have := div_le_div_of_nonneg_right hcase hM.le
      linarith
    have hx := ContinuousMap.norm_coe_le_norm (Φ x) χ
    have ha' := ContinuousMap.norm_coe_le_norm (Φ (a₀ : B)) χ
    calc ‖Φ x χ‖ * (‖Φ (g : B) χ‖ * ‖Φ (a₀ : B) χ‖)
        ≤ ‖Φ x‖ * (θ ^ n * ‖Φ (a₀ : B)‖) := by gcongr
      _ = ‖Φ x‖ * ‖Φ (a₀ : B)‖ * θ ^ n := by ring
      _ ≤ L * θ ^ n := by
          have : 0 ≤ θ ^ n := pow_nonneg hθ0.le n
          rw [hLdef]
          nlinarith
      _ < ρ := hn'
  · push_neg at hcase
    have hc0 := (hc.2 χ).2
    have hdt := hdχ χ
    have hxl : ‖Φ x χ‖ < ρ' := by
      by_contra hx
      push_neg at hx
      have := hcK χ hx
      have := sq_nonneg ‖Φ (b : B) χ‖
      linarith
    have hbl : ‖Φ (b : B) χ‖ ≤ ε := by
      by_contra hbe
      push_neg at hbe
      have : ε ^ 2 < ‖Φ (b : B) χ‖ ^ 2 := by
        have := hε.le
        gcongr
      linarith
    have hal : ‖Φ (a₀ : B) χ‖ ≤ 1 + ε := by
      have e' : Φ (a₀ : B) χ = Φ (b : B) χ + 1 := by rw [hbχ]; ring
      rw [e']
      have := norm_add_le (Φ (b : B) χ) (1 : ℂ)
      rw [norm_one] at this
      linarith
    have hg1 : ‖Φ (g : B) χ‖ ≤ 1 := by
      rw [hgn]
      exact pow_le_one₀ h1t h2t
    calc ‖Φ x χ‖ * (‖Φ (g : B) χ‖ * ‖Φ (a₀ : B) χ‖)
        ≤ ‖Φ x χ‖ * (1 * (1 + ε)) := by gcongr
      _ < ρ' * (1 * (1 + ε)) := mul_lt_mul_of_pos_right hxl (by positivity)
      _ = ρ := by rw [one_mul, hρε]

end Peak

end UpperTheory.V.Z.Tf.GlobalTraceComparison

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.peak :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Peak := by
  intro B _ _ _ _ H _ _ _ R A p a₀ x ρ ha hρ h
  obtain ⟨X, _, _, Φ, hΦ⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.exists_rep R
  obtain ⟨g, hg, hn⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.core Φ A p a₀ x ha hρ (fun χ hχ => by
    let s : B →⋆ₐ[ℂ] ℂ := (ContinuousMap.evalStarAlgHom ℂ ℂ χ).comp Φ
    refine h s (fun y => ?_) hχ
    rw [← hΦ y]
    exact ContinuousMap.norm_coe_le_norm (Φ y) χ)
  exact ⟨g, hg, by rw [← hΦ]; exact hn⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RealAlg
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

private theorem conv_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]
    (μ : Measure (H E a b)) (Φ : Matrix ι ι (H E a b → ℂ)) (c : ℂ) (f : ι → H E a b → ℂ) :
    PositivityTheory.Rg.BcB.E.conv μ Φ (c • f) = c • PositivityTheory.Rg.BcB.E.conv μ Φ f := by
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

set_option maxHeartbeats 1000000 in
theorem realAlg : RealAlg := by
  intro E _ _ _ B Q _ Γ _ t v 𝔄 a₀ g s hok hK hT hs hs0
  let gg : Γ → BGen B := fun x => Sum.inr (t x)
  let X : B.Hb →L[ℂ] B.Hb := (t a₀).op
  have hmem : ∀ y : 𝔄.B, 𝔄.F y ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X}) := by
    have hle : StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) ≤ (StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})).comap 𝔄.F := by
      refine StarAlgebra.adjoin_le ?_
      rintro _ ⟨x, rfl⟩
      show 𝔄.F (𝔄.ι x) ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})
      rw [𝔄.hF]
      exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)
    intro y
    have hy : y ∈ StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) := by
      rw [𝔄.top]
      exact StarSubalgebra.mem_top
    exact hle hy
  have hΦ : ∀ y : 𝔄.B, ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ (𝔄.F y * (t a₀).op) := fun y =>
    Rd.phiEx BlockFiniteConvolution.blkOp₀ BlockFiniteConvolution.blkWord₀ blkSum adjWords gg X (t a₀) (t a₀) (fun x => hok x) (hok a₀) rfl (hok a₀)
      ⟨𝔄.F y, hmem y⟩
  choose Φ hΦt hΦr using hΦ
  have hop : ∀ y : 𝔄.B, ∃ T : B.Hb →L[ℂ] B.Hb, IsROp B.D (Φ y) T ∧
      (∀ w : Q, T (Q.subtypeL w) = Q.subtypeL (𝔄.R (y * 𝔄.ι a₀) w)) ∧
      ∀ u, (∀ w : Q, inner ℂ (Q.subtypeL w) u = 0) → ∀ w : Q, inner ℂ (Q.subtypeL w) (T u) = 0 := by
    intro y
    have hTy : 𝔄.F y * (t a₀).op = 𝔄.F (y * 𝔄.ι a₀) := by rw [map_mul, 𝔄.hF]
    refine ⟨_, hΦr y, fun w => ?_, fun u hu w => ?_⟩
    · rw [hTy]
      exact (𝔄.hR _ w).symm
    · rw [hTy]
      have h1 : (ContinuousLinearMap.adjoint (𝔄.F (y * 𝔄.ι a₀))) (w : B.Hb) =
          Q.subtypeL (𝔄.R (star (y * 𝔄.ι a₀)) w) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
        exact (𝔄.hR _ w).symm
      have h2 := hu (𝔄.R (star (y * 𝔄.ι a₀)) w)
      rw [← h1, ContinuousLinearMap.adjoint_inner_left] at h2
      exact h2
  have hC : ({1} ∪ Set.range 𝔄.ι : Set 𝔄.B).Countable :=
    (Set.countable_singleton _).union (Set.countable_range _)
  obtain ⟨M, sk, f, hlim, hk⟩ := PositivityTheory.Rg.BcB.E2.orthogonal_keeping_holds E B.a B.b B.D B.I Q Q.subtypeL (fun w => rfl) 𝔄.B 𝔄.R s
    (𝔄.ι a₀) ({1} ∪ Set.range 𝔄.ι) Φ g hs hs0 hC (Or.inl rfl) hΦt hop
    (fun j w => (Submodule.mem_orthogonal _ _).1 (hT.1 j) w w.2) hT.2
  refine ⟨fun k x => sk k (𝔄.ι x), f, fun x => hlim _ (Or.inr ⟨x, rfl⟩), fun k => ?_⟩
  obtain ⟨h0, hc, hne, hL, hW, hconv, horth⟩ := hk k
  have hO := fun x => BlockFiniteConvolution.blkOp₀ E B (t x) (t a₀) (hok x) (hok a₀)
  have ha : PositivityTheory.Rg.BcB.E.conv B.D.μ (t a₀).Φ (f k) = sk k (𝔄.ι a₀) • f k := by
    have h1 := hconv 1 (Or.inl rfl)
    rw [one_mul] at h1
    rw [← h1]
    refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D (hO a₀).1 (hΦt 1) ?_ (hΦr 1) hc hL
    rw [map_one, one_mul]
    exact (hO a₀).2.1
  have hx : ∀ x, PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) = sk k (𝔄.ι x) • f k := by
    intro x
    have h1 := hconv (𝔄.ι x) (Or.inr ⟨x, rfl⟩)
    have hok' := (hO x).2.2.1
    have hm := BlockFiniteConvolution.blkOp₀ E B _ _ hok' hok'
    have h2 : PositivityTheory.Rg.BcB.E.conv B.D.μ ((t x).mul (t a₀)).Φ (f k) = PositivityTheory.Rg.BcB.E.conv B.D.μ (Φ (𝔄.ι x)) (f k) := by
      refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D hm.1 (hΦt _) ?_ (hΦr _) hc hL
      rw [𝔄.hF, ← (hO x).2.2.2.1]
      exact hm.2.1
    have h3 := (UpperTheory.Zero.ConvolutionTheory.EB.convMul E B (f k) hc).1 (t x) (t a₀) (hok x) (hok a₀)
    rw [ha, conv_smul', h2, h1, map_mul] at h3
    calc PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k)
        = (sk k (𝔄.ι a₀))⁻¹ • (sk k (𝔄.ι a₀)) • PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) := (inv_smul_smul₀ h0 _).symm
      _ = (sk k (𝔄.ι a₀))⁻¹ • ((sk k (𝔄.ι x) * sk k (𝔄.ι a₀)) • f k) := by rw [← h3]
      _ = sk k (𝔄.ι x) • f k := by
        rw [smul_smul]
        congr 1
        field_simp
  exact ⟨h0, ⟨hc, hne, hL, ⟨M, hW⟩, hx⟩, horth⟩

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.WordRep
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

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem rep_sum {B : Block E} {χa : InfinitePlace E → Inf B.a} {χb : InfinitePlace E → Inf B.b}
    {ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)} {J : Type} [Fintype J] (c v : J → ℂ)
    (U : J → (B.Hb →L[ℂ] B.Hb)) (R : J → ℝ) (hR : ∀ j, 0 ≤ R j)
    (h : ∀ j, Rep B χa χb ψ (v j) (R j) (U j)) :
    Rep B χa χb ψ (∑ j, c j * v j) (∑ j, R j) (∑ j, c j • U j) := by
  choose C hC hv hU using h
  refine ⟨⟨Σ j, (C j).J, Finset.univ.sigma fun j => (C j).s, fun p => c p.1 * (C p.1).c p.2,
    fun p => (C p.1).t p.2⟩, ?_, ?_, ?_⟩
  · rintro ⟨j, i⟩ hi
    have hi' : i ∈ (C j).s := (Finset.mem_sigma.1 hi).2
    obtain ⟨h1, h2, h3, h4⟩ := hC j i hi'
    have hle : R j ≤ ∑ k, R k := Finset.single_le_sum (fun k _ => hR k) (Finset.mem_univ j)
    exact ⟨h1, h2, h3.trans hle, h4.trans hle⟩
  · simp only [Cmb.val]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hv j]
    simp only [Cmb.val, Finset.mul_sum, mul_assoc]
  · simp only [Cmb.op]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hU j]
    simp only [Cmb.op, Finset.smul_sum, mul_smul]

private theorem rep_word {B : Block E} {χa : InfinitePlace E → Inf B.a} {χb : InfinitePlace E → Inf B.b}
    (hA : ∀ v, IsHerm (χa v)) (hB : ∀ v, IsHerm (χb v)) {Γ : Type} (t : Γ → PT B) (t₀ : PT B) (h₀ : t₀.Ok)
    (ht : ∀ x, (t x).Ok ∧ (t x).ψ = t₀.ψ) (hm : mulF B.ν t₀.ψ t₀.ψ = t₀.ψ) (ha : adjF t₀.ψ = t₀.ψ)
    (w : List (Γ × Bool)) :
    ∃ R, 0 ≤ R ∧ Rep B χa χb t₀.ψ (wdVal (fun x => (t x).val χa χb) w * t₀.val χa χb) R
      (wdVal (fun x => (t x).op) w * t₀.op) := by
  obtain ⟨-, hp, -, hmul⟩ := repAlg E B χa χb
  induction w with
  | nil => exact ⟨max t₀.T t₀.r, le_max_of_le_left h₀.T, by simpa [wdVal] using hp t₀ h₀⟩
  | cons p w ih =>
    obtain ⟨R, hR, hrep⟩ := ih
    obtain ⟨x, b⟩ := p
    obtain ⟨hx, hψ⟩ := ht x
    obtain ⟨-, -, -, -, hadjOk, hadjOp, -, hadjVal⟩ :=
      PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t x) (t x) hx hx
    have key : ∃ R', 0 ≤ R' ∧ Rep B χa χb t₀.ψ (if b then star ((t x).val χa χb) else (t x).val χa χb) R'
        (if b then star (t x).op else (t x).op) := by
      cases b
      · refine ⟨max (t x).T (t x).r, le_max_of_le_left hx.T, ?_⟩
        have h1 := hp (t x) hx
        rw [hψ] at h1
        simpa using h1
      · refine ⟨max (t x).adj.T (t x).adj.r, le_max_of_le_left hadjOk.T, ?_⟩
        have h1 := hp _ hadjOk
        have e : (t x).adj.ψ = t₀.ψ := by
          change adjF (t x).ψ = _
          rw [hψ, ha]
        rw [hadjOp, hadjVal χa χb hA hB, e] at h1
        simpa [ContinuousLinearMap.star_eq_adjoint] using h1
    obtain ⟨R', hR', hl⟩ := key
    refine ⟨R' + R + B.c, add_nonneg (add_nonneg hR' hR) B.c_nonneg, ?_⟩
    have h2 := hmul _ _ _ _ _ _ _ _ hl hrep
    rw [hm] at h2
    have e1 : ∀ {A : Type} [Monoid A] [Star A] (g : Γ → A), wdVal g ((x, b) :: w) =
        (if b then star (g x) else g x) * wdVal g w := fun g => by simp [wdVal]
    rw [e1, e1, mul_assoc, mul_assoc]
    exact h2

theorem wordRep : WordRep := by
  intro E _ _ _ B χa χb Γ t t₀ J _ c w hA hB h₀ ht hm ha
  choose R hR hrep using fun j => rep_word hA hB t t₀ h₀ ht hm ha (w j)
  refine ⟨∑ j, R j, Finset.sum_nonneg fun j _ => hR j, ?_⟩
  have h1 := rep_sum c _ _ R hR hrep
  rw [Finset.sum_mul, Finset.sum_mul]
  simpa only [mul_assoc, smul_mul_assoc] using h1

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PeakAlg
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

private lemma wdVal_map {B C Γ : Type} [CommRing B] [StarRing B] [Algebra ℂ B] [Ring C] [StarRing C] [Algebra ℂ C]
    (f : B →⋆ₐ[ℂ] C) (gen : Γ → B) (w : List (Γ × Bool)) :
    f (wdVal gen w) = wdVal (fun x => f (gen x)) w := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> simp [map_star]

theorem peakAlg : PeakAlg := by
  intro H _ _ _ Q _ Γ op v 𝔄 arch a₀ x ρ ha hv hρ hs
  let gen : {γ // arch γ} → 𝔄.B := fun γ => 𝔄.ι γ
  let A : StarSubalgebra ℂ 𝔄.B := StarAlgebra.adjoin ℂ (Set.range gen)
  have hmem : ∀ γ : {γ // arch γ}, 𝔄.ι γ ∈ A := fun γ =>
    StarAlgebra.subset_adjoin ℂ (Set.range gen) (Set.mem_range_self γ)
  let p : A →⋆ₐ[ℂ] ℂ := 𝔄.P.comp A.subtype
  let a₁ : A := ⟨𝔄.ι a₀, hmem ⟨a₀, ha⟩⟩
  obtain ⟨g, hg, hn⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.peak 𝔄.B Q 𝔄.R A p a₁ (𝔄.ι x) ρ
    (by
      change 𝔄.P (𝔄.ι a₀) = 1
      rw [𝔄.hP, hv])
    hρ
    (fun s hb hsa => hs s hb fun γ hγ => by
      have h1 := hsa ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩
      have h2 : p ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩ = v γ := by
        change 𝔄.P (𝔄.ι γ) = v γ
        exact 𝔄.hP γ
      rw [← h2]
      exact h1)
  obtain ⟨J, hJ, c, w, L, -, hgw, -⟩ := PositivityTheory.Rg.BcB.F.adjWords _ _ gen (g : 𝔄.B) g.2
  refine ⟨J, hJ, c, w, ?_, ?_⟩
  · have hp : 𝔄.P (g : 𝔄.B) = 1 := hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hgw, map_sum] at hp
    rw [← hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, wdVal_map, smul_eq_mul]
    congr 2
    funext γ
    exact (𝔄.hP γ).symm
  · have hF : op x * ((∑ j, c j • wdVal (fun γ : {γ // arch γ} => op γ) (w j)) * op a₀) =
        𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, map_mul, 𝔄.hF, 𝔄.hF, hgw, map_sum]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, wdVal_map]
      congr 2
      funext γ
      exact (𝔄.hF γ).symm
    rw [hF]
    have hnorm : ‖𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) ∘L Q.subtypeL‖ =
        ‖𝔄.R (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀))‖ := by
      refine ContinuousLinearMap.opNorm_ext _ _ fun q => ?_
      change ‖𝔄.F _ (q : H)‖ = ‖(𝔄.R _ q)‖
      rw [← 𝔄.hR]
      rfl
    rw [hnorm]
    exact hn

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KeepQ
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

section AlgExPf

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem keepQ {Q : Submodule ℂ H} {Γ : Type} {op : Γ → (H →L[ℂ] H)} {v : Γ → ℂ}
    (hQ : ∀ x, ∀ f ∈ Q, op x f ∈ Q ∧ star (op x) f ∈ Q) {y : (H →L[ℂ] H) × ℂ}
    (hy : y ∈ StarAlgebra.adjoin ℂ (Set.range fun x => (op x, v x))) :
    (∀ f ∈ Q, y.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1) f ∈ Q := by
  induction hy using StarAlgebra.adjoin_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨fun f hf => (hQ a f hf).1, fun f hf => (hQ a f hf).2⟩
  | algebraMap r =>
    have h1 : (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = r • (1 : H →L[ℂ] H) := by
      rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    rw [h1]
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · simpa using Q.smul_mem r hf
    · simpa [star_smul] using Q.smul_mem (star r) hf
  | add x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact Q.add_mem (hx.1 f hf) (hy.1 f hf)
    · rw [Prod.fst_add, star_add]
      exact Q.add_mem (hx.2 f hf) (hy.2 f hf)
  | mul x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact hx.1 _ (hy.1 f hf)
    · rw [Prod.fst_mul, star_mul]
      exact hy.2 _ (hx.2 f hf)
  | star x _ hx =>
    refine ⟨fun f hf => hx.2 f hf, fun f hf => ?_⟩
    have : (star (star x).1) = x.1 := by rw [Prod.fst_star, star_star]
    rw [this]
    exact hx.1 f hf

end AlgExPf

end UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.Zero.ConvolutionTheory.EB.algEx :
    UpperTheory.Zero.ConvolutionTheory.EB.AlgEx := by
  intro H _ _ _ Q _ Γ op v hc hs hQ
  let s : Set ((H →L[ℂ] H) × ℂ) := Set.range fun x => (op x, v x)
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hc x y).eq (mul_comm _ _)
  have hcs : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hs x y).eq (mul_comm _ _)
  letI : IsMulCommutative (StarAlgebra.adjoin ℂ s) :=
    StarAlgebra.isMulCommutative_adjoin ℂ
      (fun x hx => ⟨(hcs x hx x hx).symm⟩)
      (fun x hx y hy _ => hcomm x hx y hy)
      (fun x hx y hy _ => hcs x hx y hy)
  letI : CommRing (StarAlgebra.adjoin ℂ s) := { (inferInstance : Ring _) with
    mul_comm := fun a b => mul_comm' a b }
  have keep : ∀ y : StarAlgebra.adjoin ℂ s, (∀ f ∈ Q, y.1.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1.1) f ∈ Q :=
    fun y => UpperTheory.Zero.ConvolutionTheory.EB.keepQ hQ y.2
  let res : StarAlgebra.adjoin ℂ s → (Q →L[ℂ] Q) := fun y =>
    (y.1.1 ∘L Q.subtypeL).codRestrict Q fun q => (keep y).1 q q.2
  let R : StarAlgebra.adjoin ℂ s →⋆ₐ[ℂ] (Q →L[ℂ] Q) :=
    { toFun := res
      map_one' := by ext q; rfl
      map_mul' := fun a b => by ext q; rfl
      map_zero' := by ext q; rfl
      map_add' := fun a b => by ext q; rfl
      commutes' := fun r => by
        ext q
        have h1 : ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 = r • (1 : H →L[ℂ] H) := by
          show (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = _
          rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
        have h2 : algebraMap ℂ (Q →L[ℂ] Q) r = r • (1 : Q →L[ℂ] Q) :=
          Algebra.algebraMap_eq_smul_one r
        show ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 (q : H) = _
        rw [h1, h2]
        simp
      map_star' := fun y => by
        show res (star y) = star (res y)
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
        intro p q
        show inner ℂ (star y.1.1 (p : H)) (q : H) = inner ℂ (p : H) (y.1.1 (q : H))
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] }
  let ι : Γ → StarAlgebra.adjoin ℂ s := fun x => ⟨(op x, v x), StarAlgebra.subset_adjoin ℂ s ⟨x, rfl⟩⟩
  have all : ∀ y : StarAlgebra.adjoin ℂ s, y ∈ StarAlgebra.adjoin ℂ (Set.range ι) := by
    intro y
    induction y using StarAlgebra.adjoin_induction_subtype with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact StarAlgebra.subset_adjoin ℂ _ ⟨a, rfl⟩
    | algebraMap r => exact algebraMap_mem _ r
    | add x y hx hy => exact add_mem hx hy
    | mul x y hx hy => exact mul_mem hx hy
    | star x hx => exact star_mem hx
  have top : StarAlgebra.adjoin ℂ (Set.range ι) = ⊤ := eq_top_iff.2 fun y _ => all y
  exact ⟨{ B := StarAlgebra.adjoin ℂ s
           R := R
           P := (StarAlgHom.snd ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           F := (StarAlgHom.fst ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           ι := ι
           hF := fun _ => rfl
           hP := fun _ => rfl
           hR := fun _ _ => rfl
           top := top }⟩
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

theorem peakRun : PeakRun := by
  intro E _ _ _ B Q _ χa χb Γ _ t arch a₀ x g ρ hG hK hT hHa hHb ha hv hψ hmul hadj hρ hs
  have hkeep : ∀ y, ∀ f ∈ Q, (t y).op f ∈ Q ∧ star (t y).op f ∈ Q := by
    intro y f hf
    have h1 := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t y) (t y) (hG.ok y) (hG.ok y)
    obtain ⟨hT1, hR1, -, -, hadjOk, hadjOp, -, -⟩ := h1
    have h2 := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t y).adj (t y).adj hadjOk hadjOk
    refine ⟨hK _ _ hT1 hR1 f hf, ?_⟩
    rw [ContinuousLinearMap.star_eq_adjoint, ← hadjOp]
    exact hK _ _ h2.1 h2.2.1 f hf
  obtain ⟨𝔄⟩ := algEx B.Hb Q Γ (fun y => (t y).op) (fun y => (t y).val χa χb) hG.comm hG.commStar hkeep
  obtain ⟨J, hJ, c, w, hval, hnorm⟩ := peakAlg B.Hb Q Γ (fun y => (t y).op) (fun y => (t y).val χa χb) 𝔄 arch a₀ x ρ ha hv hρ
    (fun s hb hsa => hs (fun y => s (𝔄.ι y)) hsa
      (realAlg E B Q Γ t (fun y => (t y).val χa χb) 𝔄 a₀ g s hG.ok hK hT hb
        (by rw [hsa a₀ ha, hv]; exact one_ne_zero)))
  obtain ⟨R, hR, hrep⟩ := wordRep E B χa χb {γ // arch γ} (fun γ => t γ) (t a₀) J c w hHa hHb (hG.ok a₀)
    (fun γ => ⟨hG.ok γ, hψ γ γ.2⟩) hmul hadj
  refine ⟨_, R, hR, ?_, hnorm⟩
  rw [hval, hv, one_mul] at hrep
  exact hrep

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

open UpperTheory.V.Z.Tf.GlobalTraceComparison PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.Zero.ConvolutionTheory.EB

theorem specP (P : Pred) (h : CuspReadP P) : Spec P := rSpec_of peakRun genSt ptOk hkMul repAlg positionTest P (rRead P h)

theorem endoP (P : Pred) (h : CuspReadP P) : EndoP P :=
  rEndo_of arEx lvEx powRep cmbTest cmbEll repAlg powNorm P (specP P h)

theorem stableP (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) (P : Pred) (h : CuspReadP P) :
    StableP P := rStable h2 h3 h5 (cmbPi h1 h4) P (specP P h)

theorem endoBlockG (h : CuspReadI) : EndoBlockG := endoG_of (endoP _ (cuspReadP_inf h))

theorem stableBlockG (h : CuspReadI) (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) : StableBlockG :=
  stableG_of (stableP h1 h2 h3 h4 h5 _ (cuspReadP_inf h))

end UpperTheory.Zero.ConvolutionTheory.EB
