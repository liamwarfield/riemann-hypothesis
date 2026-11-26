module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDomInt
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open DiscreteGroups.T1.G
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

private theorem pow_mul_exp_neg_le (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-r) ≤ N.factorial * Real.exp 1 := by
  have h := Real.pow_div_factorial_le_exp (1 + r) (by linarith) N
  rw [div_le_iff₀ (by exact_mod_cast N.factorial_pos)] at h
  have e : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
  calc (1 + r) ^ N * Real.exp (-r) ≤ (Real.exp (1 + r) * N.factorial) * Real.exp (-r) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = N.factorial * Real.exp 1 * (Real.exp r * Real.exp (-r)) := by rw [Real.exp_add]; ring
    _ = N.factorial * Real.exp 1 := by rw [e, mul_one]

private theorem point_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hB : Basic) (hS : Sizes)
    (hn : 1 ≤ n) {π : CuspSub E n} (hθ : ThetaFix π) {ψ : Sm E n} (hψ : ψ ∈ π.V) (M : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R ρ : ℝ, 0 ≤ R → ∀ x : H E n 0, |ldet x| ≤ R → ρ ≤ r0 x →
      ‖ψ.1 x.1‖ ≤ A * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) * wt x ^ (-(2 * M : ℤ)) := by
  obtain ⟨h1, h2, -⟩ := hB E n hn
  obtain ⟨c, hc0, hc⟩ := hS E n hn
  have hA := hθ.1 ψ hψ
  obtain ⟨C₀, hC₀⟩ := Dcy.cp_decay ψ (π.cusp ψ hψ) hA 0 (L + 1)
  set a : ℝ := redSize (1 : GA E 0) with ha
  have ha0 : 0 ≤ a := Dcy.redSize_nonneg _
  set c₁ : ℝ := 2 + a + c with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set C : ℝ := max C₀ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  set K : ℝ := ((2 * M).factorial : ℝ) * Real.exp 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C * c₁ ^ (2 * M) * K, by positivity, fun R ρ hR x hx hρ => ?_⟩
  obtain ⟨hs, -, hr⟩ := hc x
  set r : ℝ := r0 x with hrdef
  set y : H E n 0 := ac E n (-ldet x) * x with hy
  have hy0 : ldet y = 0 := by rw [hy, h2, h1]; ring
  have hψy : ψ.1 y.1 = ψ.1 x.1 := hA _ _
  have hdec : ‖ψ.1 x.1‖ ≤ C * Real.exp (-((L + 1) * r)) := by
    have h := hC₀ y.1 (by
      have : |ldet y| ≤ 0 := by rw [hy0]; simp
      exact this)
    rw [hψy] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hx2 : x.2 = 1 := Units.ext (Subsingleton.elim _ _)
  have hw : wt x = 1 + redSize x.1 + a := by rw [wt, hx2]
  have hrs := Dcy.redSize_nonneg x.1
  have hw1 : 1 ≤ wt x := by rw [hw]; linarith
  have hP : 1 ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
  have hwle : wt x ≤ c₁ * ((1 + r) * (1 + R)) := by
    have h3 : c * (1 + |ldet x|) ≤ c * (1 + R) := mul_le_mul_of_nonneg_left (by linarith) hc0
    have h4 : 1 + R ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
    have h5 : 1 + r ≤ (1 + r) * (1 + R) := by nlinarith [mul_nonneg hr hR]
    have h6 : c * (1 + R) ≤ c * ((1 + r) * (1 + R)) := mul_le_mul_of_nonneg_left h4 hc0
    have h7 : (1 + a) * 1 ≤ (1 + a) * ((1 + r) * (1 + R)) := mul_le_mul_of_nonneg_left hP (by linarith)
    rw [hw, hc₁]
    nlinarith
  have hexp : Real.exp (-((L + 1) * r)) ≤ Real.exp (-(L * ρ)) * Real.exp (-r) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hρ hL]
  have hpow : wt x ^ (2 * M) ≤ c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * (1 + R) ^ (2 * M)) := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hwle _
  have hwpos : 0 < wt x ^ (2 * M) := pow_pos (by linarith) _
  have hz : wt x ^ (-(2 * M : ℤ)) = (wt x ^ (2 * M))⁻¹ := by
    rw [_root_.zpow_neg]
    congr 1
  have hr1 : 0 ≤ 1 + r := by linarith
  have hR1 : 0 ≤ 1 + R := by linarith
  have hmain : ‖ψ.1 x.1‖ * wt x ^ (2 * M) ≤ C * c₁ ^ (2 * M) * K * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by
    have hq := pow_mul_exp_neg_le (2 * M) hr
    calc ‖ψ.1 x.1‖ * wt x ^ (2 * M)
        ≤ (C * (Real.exp (-(L * ρ)) * Real.exp (-r))) *
            (c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * (1 + R) ^ (2 * M))) :=
          mul_le_mul (hdec.trans (mul_le_mul_of_nonneg_left hexp hC0)) hpow hwpos.le (by positivity)
      _ = C * c₁ ^ (2 * M) * ((1 + r) ^ (2 * M) * Real.exp (-r)) * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by ring
      _ ≤ C * c₁ ^ (2 * M) * K * (1 + R) ^ (2 * M) * Real.exp (-(L * ρ)) := by
          gcongr
  rw [hz, ← div_eq_mul_inv, le_div_iff₀ hwpos]
  exact hmain

theorem domInt_pf : Basic → Sizes → DomInt := by
  intro hB hS E _ _ _ n hn D π hθ ψ hψ Ω hΩ
  refine ⟨2 * (2 * n), fun L hL => ?_⟩
  obtain ⟨A, hA0, hA⟩ := point_bound hB hS hn hθ hψ (2 * n) L hL
  have hI := wtCount E n 0 D Ω hΩ (2 * n) (by omega)
  set I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (wt x ^ (-(2 * ((2 * n : ℕ) : ℤ)))) * cnt (ratH E n 0) Ω x ∂D.ν with hIdef
  refine ⟨A * I.toReal, mul_nonneg hA0 ENNReal.toReal_nonneg, fun R ρ hR => ?_⟩
  set B : ℝ := A * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ)) with hBdef
  have hR1 : 0 ≤ 1 + R := by linarith
  have hB0 : 0 ≤ B := by positivity
  calc ∫⁻ x, {x | |ldet x| ≤ R ∧ ρ ≤ r0 x}.indicator (fun x => ‖ψ.1 x.1‖ₑ * cnt (ratH E n 0) Ω x) x ∂D.ν
      ≤ ∫⁻ x, ENNReal.ofReal B * (ENNReal.ofReal (wt x ^ (-(2 * ((2 * n : ℕ) : ℤ)))) * cnt (ratH E n 0) Ω x) ∂D.ν := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ {x : H E n 0 | |ldet x| ≤ R ∧ ρ ≤ r0 x}
        · rw [Set.indicator_of_mem hx, ← mul_assoc, ← ENNReal.ofReal_mul hB0, ← ofReal_norm]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hA R ρ hR x hx.1 hx.2)) _
        · rw [Set.indicator_of_notMem hx]
          exact zero_le
    _ = ENNReal.ofReal B * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A * I.toReal * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ))) := by
        rw [show A * I.toReal * (1 + R) ^ (2 * (2 * n)) * Real.exp (-(L * ρ)) = B * I.toReal by rw [hBdef]; ring,
          ENNReal.ofReal_mul hB0, ENNReal.ofReal_toReal hI]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PGBound
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem cnt_le_sq {G : Type} [Group G] (Γ : Subgroup G) (Ω : Set G) (x : G) :
    cnt Γ Ω x ≤ cnt Γ Ω x ^ 2 := by
  by_cases h : ∃ γ : Γ, x⁻¹ * (γ : G) * x ∈ Ω
  · obtain ⟨γ, hγ⟩ := h
    have h1 : 1 ≤ cnt Γ Ω x := by
      have h2 := ENNReal.le_tsum (f := fun γ : Γ => Ω.indicator (1 : G → ℝ≥0∞) (x⁻¹ * (γ : G) * x)) γ
      have h3 : Ω.indicator (1 : G → ℝ≥0∞) (x⁻¹ * (γ : G) * x) = 1 := by
        rw [Set.indicator_of_mem hγ]; rfl
      rw [h3] at h2
      exact h2
    rw [sq]
    exact le_mul_of_one_le_left zero_le h1
  · have h0 : cnt Γ Ω x = 0 := by
      unfold cnt
      refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem (fun hm => h ⟨γ, hm⟩) _
    simp [h0]

private theorem cnt_central {G : Type} [Group G] (Γ : Subgroup G) (Ω : Set G) (a x : G)
    (ha : ∀ y, a * y = y * a) : cnt Γ Ω (a * x) = cnt Γ Ω x := by
  unfold cnt
  refine tsum_congr fun γ => ?_
  have e : (a * x)⁻¹ * (γ : G) * (a * x) = x⁻¹ * (γ : G) * x := by
    have h1 : (γ : G) * a = a * (γ : G) := (ha _).symm
    calc (a * x)⁻¹ * (γ : G) * (a * x) = x⁻¹ * a⁻¹ * ((γ : G) * a) * x := by group
      _ = x⁻¹ * (γ : G) * x := by rw [h1]; group
  rw [e]

private theorem norm_part_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (K : Submodule ℂ V) [K.HasOrthogonalProjection] (U Up : V →L[ℂ] V)
    (h1 : ∀ f ∈ K, Up f = U f) (h2 : ∀ f ∈ Kᗮ, Up f = 0) : ‖Up‖ ≤ ‖U‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
  have e : Up f = U (K.starProjection f) := by
    have h3 : f = K.starProjection f + (f - K.starProjection f) := by abel
    calc Up f = Up (K.starProjection f) + Up (f - K.starProjection f) := by
          rw [← map_add (f := _), ← h3]
      _ = U (K.starProjection f) := by
          rw [h2 _ (K.sub_starProjection_mem_orthogonal f), add_zero,
            h1 _ (K.starProjection_apply_mem f)]
  rw [e]
  refine (U.le_opNorm _).trans ?_
  exact mul_le_mul_of_nonneg_left (K.norm_starProjection_apply_le f) (norm_nonneg _)

private theorem le_ofReal_sqrt {e : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (h : e ^ 2 ≤ ENNReal.ofReal r) :
    e ≤ ENNReal.ofReal (Real.sqrt r) := by
  refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hr]
  exact h

private theorem enorm_inner_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (a b : V) (T U : V →L[ℂ] V) (hT : ‖T‖ ≤ ‖U‖) (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (c : ℝ≥0∞)
    (ha : ‖a‖ₑ ≤ ENNReal.ofReal P) (hb : ‖b‖ₑ ≤ ENNReal.ofReal Q * c) :
    ‖(inner ℂ a (T b) : ℂ)‖ₑ ≤ ENNReal.ofReal (P * Q * ‖U‖) * c := by
  have h1 : ‖(inner ℂ a (T b) : ℂ)‖ ≤ ‖a‖ * (‖U‖ * ‖b‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((T.le_opNorm b).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))) (norm_nonneg _))
  calc ‖(inner ℂ a (T b) : ℂ)‖ₑ = ENNReal.ofReal ‖(inner ℂ a (T b) : ℂ)‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖a‖ * (‖U‖ * ‖b‖)) := ENNReal.ofReal_le_ofReal h1
    _ = ‖a‖ₑ * (ENNReal.ofReal ‖U‖ * ‖b‖ₑ) := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm, ofReal_norm]
    _ ≤ ENNReal.ofReal P * (ENNReal.ofReal ‖U‖ * (ENNReal.ofReal Q * c)) := by gcongr
    _ = ENNReal.ofReal (P * Q * ‖U‖) * c := by
        rw [ENNReal.ofReal_mul (mul_nonneg hP hQ), ENNReal.ofReal_mul hP]
        ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.gBound_pf :
    Basic → GBound := by
  intro hB E _ _ _ n ι _ s
  obtain ⟨-, -, hcomm, -⟩ := hB E n s.pos
  obtain ⟨C₀, Ω, hC₀, hΩ, hk⟩ := s.vecs.norm
  refine ⟨Ω, hΩ, fun x₀ => ?_⟩
  have hfin : cnt (ratH E n 0) Ω x₀ ≠ ⊤ := (cntBasic (ctx ratProper_holds s.D)).1 Ω hΩ x₀
  have hA : 0 ≤ C₀.toReal := ENNReal.toReal_nonneg
  have hc : 0 ≤ (cnt (ratH E n 0) Ω x₀).toReal := ENNReal.toReal_nonneg
  have hAe : ENNReal.ofReal C₀.toReal = C₀ := ENNReal.ofReal_toReal hC₀
  have hce : ENNReal.ofReal (cnt (ratH E n 0) Ω x₀).toReal = cnt (ratH E n 0) Ω x₀ :=
    ENNReal.ofReal_toReal hfin
  refine ⟨(Fintype.card ι : ℝ) * (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal),
    by positivity, fun m t y => ?_⟩
  have hU : ‖m.Uπ‖ ≤ ‖m.U‖ := norm_part_le _ m.U m.Uπ m.pp.1 m.pp.2
  have h1 : ∀ i, ‖s.k₁ (ac E n t * x₀) i‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal)) := fun i => by
    refine le_ofReal_sqrt (mul_nonneg hA hc) ?_
    rw [ENNReal.ofReal_mul hA, hAe, hce, ← cnt_central (ratH E n 0) Ω (ac E n t) x₀ (hcomm t)]
    exact (hk _ i).1
  have h2 : ∀ i, ‖s.k₂ y i‖ₑ ≤ ENNReal.ofReal (Real.sqrt C₀.toReal) * cnt (ratH E n 0) Ω y := fun i => by
    refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hA, hAe]
    exact (hk y i).2.trans (mul_le_mul_right (cnt_le_sq _ _ _) _)
  have h3 : ∀ i, ‖(inner ℂ (s.k₁ (ac E n t * x₀) i) (m.Uπ (s.k₂ y i)) : ℂ)‖ₑ ≤
      ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal * ‖m.U‖) *
        cnt (ratH E n 0) Ω y := fun i =>
    enorm_inner_le _ _ _ _ hU _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) _ (h1 i) (h2 i)
  calc ‖m.G (ac E n t * x₀) y‖ₑ ≤ ∑ i, ‖(inner ℂ (s.k₁ (ac E n t * x₀) i) (m.Uπ (s.k₂ y i)) : ℂ)‖ₑ :=
        enorm_sum_le _ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (Real.sqrt (C₀.toReal * (cnt (ratH E n 0) Ω x₀).toReal) * Real.sqrt C₀.toReal * ‖m.U‖) *
        cnt (ratH E n 0) Ω y := Finset.sum_le_sum fun i _ => h3 i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_assoc (Fintype.card ι : ℝ)]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailInt
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Meas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem continuous_ac' : Continuous (ac E n) := by
  have hc : Continuous (splitCentre E n) := by
    have e : splitCentre E n = fun t : ℝ =>
        GeneralLinearGroup.scalar (Fin n) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
      funext GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar
    rw [e]
    refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
      (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
    change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin n => x
    exact (continuous_pi fun _ => continuous_id).matrix_diagonal
  exact (hc.comp (continuous_id.div_const _)).prodMk continuous_const

private theorem measurable_reduced_size : Measurable (r0 : H E n 0 → ℝ) := by
  have hc : Continuous fun x : H E n 0 => (ac E n (-ldet x) * x).1 :=
    continuous_fst.comp ((continuous_ac'.comp continuous_ldet.neg).mul continuous_id)
  haveI := borelSpace_H (E := E) (n := n)
  letI : MeasurableSpace (GA E n) := borel _
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  exact (redBasic E n).2.2.comp hc.measurable

private theorem measurable_cnt {Ω : Set (H E n 0)} (hΩ : IsCompact Ω) :
    Measurable (cnt (ratH E n 0) Ω) := by
  haveI := borelSpace_H (E := E) (n := n)
  haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'
  set_option synthInstance.maxHeartbeats 200000 in
    have hm : MeasurableSet Ω := hΩ.measurableSet
    refine Measurable.tsum fun γ => ?_
    have hc : Continuous fun x : H E n 0 => x⁻¹ * (γ : H E n 0) * x :=
      (continuous_inv.mul continuous_const).mul continuous_id
    exact (measurable_one.indicator hm).comp hc.measurable

end Meas

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.tailInt_of_bounds :
    GFac → GBound → Supp → DomInt → TailInt := by
  intro hF hB hS hD E _ _ _ n ι _ s
  haveI := borelSpace_H (E := E) (n := n)
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨Ω, hΩ, hC⟩ := hB E n ι s
  choose Cb hCb0 hCb using fun b => hC (p.x b)
  choose Nb hNb using fun b => hD E n s.pos s.D s.π s.fix (p.w b) (p.mem b) Ω hΩ
  refine ⟨Finset.univ.sup Nb, fun L hL => ?_⟩
  choose Db hDb0 hDb using fun b => hNb b L hL
  refine ⟨∑ b, Cb b * Db b, Finset.sum_nonneg fun b _ => mul_nonneg (hCb0 b) (hDb0 b),
    fun m R ρ hR hφ A hA => ?_⟩
  set S : Set (H E n 0) := {x | |ldet x| ≤ R ∧ ρ ≤ r0 x} with hSdef
  have hSm : MeasurableSet S :=
    ((isClosed_le (continuous_abs.comp continuous_ldet) continuous_const).measurableSet).inter
      (measurableSet_le measurable_const measurable_reduced_size)
  set f : p.B → H E n 0 → ℝ≥0∞ := fun b =>
    S.indicator (fun x => ‖(p.w b).1 x.1‖ₑ * cnt (ratH E n 0) Ω x) with hf
  have hfm : ∀ b, Measurable (f b) := fun b => by
    refine Measurable.indicator ?_ hSm
    refine Measurable.mul ?_ (measurable_cnt hΩ)
    exact (((continuous_of_mem s.π (p.mem b)).comp continuous_fst).enorm).measurable
  have hpt : ∀ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ≤
      ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x := by
    intro x
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      by_cases hx : |ldet x| ≤ R
      · have hxS : x ∈ S := ⟨hx, hA x hxA hx⟩
        rw [hp m x x]
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [enorm_mul, hf]
        simp only [Set.indicator_of_mem hxS]
        calc ‖(p.w b).1 x.1‖ₑ * ‖m.G (ac E n (ldet x) * p.x b) x‖ₑ
            ≤ ‖(p.w b).1 x.1‖ₑ * (ENNReal.ofReal (Cb b * ‖m.U‖) * cnt (ratH E n 0) Ω x) := by
              gcongr; exact hCb b m _ x
          _ = _ := by ring
      · have h0 : m.G x x = 0 := by
          refine hS E n ι s m R hφ x x ?_
          have h1 : R < |ldet x| := not_le.mp hx
          have h2 : |ldet x + ldet x| = 2 * |ldet x| := by
            rw [← two_mul, abs_mul, abs_two]
          rw [h2]
          have := abs_nonneg (ldet x)
          linarith
        simp [h0]
    · rw [Set.indicator_of_notMem hxA]
      exact zero_le
  have h1R : (1 : ℝ) ≤ 1 + R := by linarith
  have hT : ∀ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν ≤
      ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
    intro b
    have hpow : (1 + R) ^ Nb b ≤ (1 + R) ^ (Finset.univ.sup Nb) :=
      pow_le_pow_right₀ h1R (Finset.le_sup (Finset.mem_univ b))
    have h2 : ∫⁻ x, f b x ∂s.D.ν ≤
        ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
      refine (hDb b R ρ hR).trans (ENNReal.ofReal_le_ofReal ?_)
      have := hDb0 b
      have he := (Real.exp_pos (-(L * ρ))).le
      gcongr
    calc _ ≤ ENNReal.ofReal (Cb b * ‖m.U‖) *
          ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (hCb0 b) (norm_nonneg _))]
        congr 1
        ring
  calc ∫⁻ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ∂s.D.ν
      ≤ ∫⁻ x, ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x ∂s.D.ν := lintegral_mono hpt
    _ = ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν := by
        rw [lintegral_finsetSum _ fun b _ => (hfm b).const_mul _]
        exact Finset.sum_congr rfl fun b _ => lintegral_const_mul _ (hfm b)
    _ ≤ ∑ b, ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) :=
        Finset.sum_le_sum fun b _ => hT b
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [Finset.sum_mul]
        · intro b _
          have := mul_nonneg (hCb0 b) (hDb0 b)
          have he := (Real.exp_pos (-(L * ρ))).le
          have hp1 : 0 ≤ (1 + R) ^ (Finset.univ.sup Nb) := by positivity
          positivity

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.FlipHalf
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory Filter Topology

private lemma flip_half (β : ℝ → ℝ) (hi : Integrable β) (h1 : ∫ t, β t = 1) (c : ℝ) :
    Integrable (fun s : ℝ => β (-(s + c) - s)) ∧ ∫ s : ℝ, β (-(s + c) - s) = 1 / 2 := by
  have e : ∀ s : ℝ, β (-(s + c) - s) = (fun y => β (y - c)) ((-2 : ℝ) * s) := by
    intro s
    show β _ = β _
    congr 1
    ring
  have hg : Integrable (fun y => β (y - c)) := hi.comp_sub_right c
  refine ⟨?_, ?_⟩
  · simp_rw [e]
    exact hg.comp_mul_left' (by norm_num)
  · simp_rw [e]
    rw [Measure.integral_comp_mul_left (fun y => β (y - c)) (-2 : ℝ),
      integral_sub_right_eq_self β c, h1]
    norm_num

private lemma flip_core {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z] (ν : Measure X) [SFinite ν]
    (μ : Measure Z) [SFinite μ] (l : X → ℝ) (l' : Z → ℝ) (F : ℝ → X → ℂ) (m : Z → ℂ) (d : X → ℝ)
    (hl : Measurable l) (hl' : Measurable l') (hF : Measurable (Function.uncurry F))
    (hm : Integrable m μ) (hd : Integrable d ν)
    (hb : ∀ s x, |s - l x| ≤ 1 → ‖F s x‖ ≤ d x)
    (hh : ∀ (s : ℝ) (u : ℝ → ℂ), Continuous u → HasCompactSupport u →
      ∫ x, F s x * u (l x) ∂ν = ∫ z, m z * u (-(s + l' z)) ∂μ)
    (β : ℝ → ℝ) (hc : Continuous β) (hs : HasCompactSupport β) (h0 : ∀ t, 0 ≤ β t)
    (h1 : ∫ t, β t = 1) (hr : ∀ t, β t ≠ 0 → |t| ≤ 1) :
    Integrable (fun x => ∫ s : ℝ, F s x * (β (l x - s) : ℂ)) ν ∧
      (∀ x, ‖∫ s : ℝ, F s x * (β (l x - s) : ℂ)‖ ≤ d x) ∧
      ∫ x, (∫ s : ℝ, F s x * (β (l x - s) : ℂ)) ∂ν = (∫ z, m z ∂μ) / 2 := by
  have hi : Integrable β := hc.integrable_of_hasCompactSupport hs
  have hd0 : ∀ x, 0 ≤ d x := fun x => (norm_nonneg _).trans (hb (l x) x (by simp))
  have hpt : ∀ x s, ‖F s x * (β (l x - s) : ℂ)‖ ≤ d x * β (l x - s) := by
    intro x s
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _)]
    by_cases h : β (l x - s) = 0
    · simp [h]
    · have := hr _ h
      rw [abs_sub_comm] at this
      exact mul_le_mul_of_nonneg_right (hb s x this) (h0 _)
  have hmeas : Measurable (fun p : X × ℝ => F p.2 p.1 * (β (l p.1 - p.2) : ℂ)) := by
    have a : Measurable (fun p : X × ℝ => F p.2 p.1) :=
      hF.comp (measurable_snd.prodMk measurable_fst)
    have b : Measurable (fun p : X × ℝ => β (l p.1 - p.2)) :=
      hc.measurable.comp ((hl.comp measurable_fst).sub measurable_snd)
    exact a.mul (Complex.measurable_ofReal.comp b)
  have hsec : ∀ x, Integrable (fun s : ℝ => F s x * (β (l x - s) : ℂ)) := by
    intro x
    have hmaj : Integrable (fun s : ℝ => d x * β (l x - s)) := (hi.comp_sub_left (l x)).const_mul _
    refine hmaj.mono' ?_ (Eventually.of_forall fun s => hpt x s)
    exact (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hle : ∀ x, ∫ s : ℝ, ‖F s x * (β (l x - s) : ℂ)‖ ≤ d x := by
    intro x
    have hmaj : Integrable (fun s : ℝ => d x * β (l x - s)) := (hi.comp_sub_left (l x)).const_mul _
    calc ∫ s : ℝ, ‖F s x * (β (l x - s) : ℂ)‖ ≤ ∫ s : ℝ, d x * β (l x - s) :=
          integral_mono (hsec x).norm hmaj (fun s => hpt x s)
      _ = d x := by
          rw [integral_const_mul, integral_sub_left_eq_self β volume (l x), h1, mul_one]
  have hprod : Integrable (fun p : X × ℝ => F p.2 p.1 * (β (l p.1 - p.2) : ℂ)) (ν.prod volume) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hsec, ?_⟩
    refine hd.mono' hmeas.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hle x
  refine ⟨hprod.integral_prod_left, fun x => (norm_integral_le_integral_norm _).trans (hle x), ?_⟩
  have hsw := integral_integral_swap (f := fun x (s : ℝ) => F s x * (β (l x - s) : ℂ)) hprod
  rw [hsw]
  have hstep : ∀ s : ℝ, ∫ x, F s x * (β (l x - s) : ℂ) ∂ν =
      ∫ z, m z * (β (-(s + l' z) - s) : ℂ) ∂μ := by
    intro s
    have hu : HasCompactSupport (fun t : ℝ => ((β (t - s) : ℝ) : ℂ)) := by
      have : HasCompactSupport (fun t : ℝ => β (t - s)) := hs.comp_homeomorph (Homeomorph.subRight s)
      exact this.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
    exact hh s (fun t => ((β (t - s) : ℝ) : ℂ)) (by fun_prop) hu
  simp_rw [hstep]
  have hmeas2 : AEStronglyMeasurable
      (fun p : ℝ × Z => m p.2 * (β (-(p.1 + l' p.2) - p.1) : ℂ)) ((volume : Measure ℝ).prod μ) := by
    have a : AEStronglyMeasurable (fun p : ℝ × Z => m p.2) ((volume : Measure ℝ).prod μ) :=
      hm.aestronglyMeasurable.comp_snd
    have b : Measurable (fun p : ℝ × Z => β (-(p.1 + l' p.2) - p.1)) :=
      hc.measurable.comp (((measurable_fst.add (hl'.comp measurable_snd)).neg).sub measurable_fst)
    exact a.mul (Complex.measurable_ofReal.comp b).aestronglyMeasurable
  have hnorm : ∀ z, ∫ s : ℝ, ‖m z * (β (-(s + l' z) - s) : ℂ)‖ = ‖m z‖ / 2 := by
    intro z
    have : ∀ s : ℝ, ‖m z * (β (-(s + l' z) - s) : ℂ)‖ = ‖m z‖ * β (-(s + l' z) - s) := by
      intro s
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 _)]
    simp_rw [this]
    rw [integral_const_mul, (flip_half β hi h1 (l' z)).2]
    ring
  have hprod2 : Integrable (fun p : ℝ × Z => m p.2 * (β (-(p.1 + l' p.2) - p.1) : ℂ))
      ((volume : Measure ℝ).prod μ) := by
    rw [integrable_prod_iff' hmeas2]
    refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
    · have := (flip_half β hi h1 (l' z)).1.ofReal (𝕜 := ℂ)
      exact this.const_mul (m z)
    · simp_rw [hnorm]
      exact hm.norm.div_const 2
  have hsw2 := integral_integral_swap (f := fun (s : ℝ) z => m z * (β (-(s + l' z) - s) : ℂ)) hprod2
  rw [hsw2]
  have hin : ∀ z, ∫ s : ℝ, m z * (β (-(s + l' z) - s) : ℂ) = m z / 2 := by
    intro z
    rw [integral_const_mul, integral_complex_ofReal, (flip_half β hi h1 (l' z)).2]
    push_cast
    ring
  simp_rw [hin]
  exact integral_div 2 m

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.flip_pf :
    Flip := by
  intro X Z _ _ ν _ μ _ l l' F m d hl hl' hF hFc hm hd hb hh
  have hmeas : Measurable (fun x => F (l x) x) := hF.comp (hl.prodMk measurable_id)
  refine ⟨hd.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun x => hb (l x) x (by simp)), ?_⟩
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun k =>
    ⟨1 / (2 * ((k : ℝ) + 1)), 1 / ((k : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      exact one_div_lt_one_div_of_lt this (by linarith)⟩
  have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let β : ℕ → ℝ → ℝ := fun k => (φ k).normed volume
  have hr : ∀ k t, β k t ≠ 0 → |t| ≤ 1 := by
    intro k t ht
    have hmem : t ∈ Function.support ((φ k).normed volume) := ht
    rw [(φ k).support_normed_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
    have : (φ k).rOut ≤ 1 := by
      show 1 / ((k : ℝ) + 1) ≤ 1
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := by positivity
      linarith
    linarith
  have hcore := fun k => flip_core ν μ l l' F m d hl hl' hF hm hd hb hh (β k)
    (φ k).continuous_normed (φ k).hasCompactSupport_normed (fun t => (φ k).nonneg_normed t)
    (φ k).integral_normed (hr k)
  have hlim : Tendsto (fun k => ∫ x, (∫ s : ℝ, F s x * (β k (l x - s) : ℂ)) ∂ν) atTop
      (𝓝 (∫ x, F (l x) x ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence d (fun k => (hcore k).1.aestronglyMeasurable) hd
      (fun k => Eventually.of_forall (hcore k).2.1) (Eventually.of_forall fun x => ?_)
    have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure ℝ))
      (g := fun s => F s x) hφ (hFc x) (l x)
    refine this.congr fun k => ?_
    rw [convolution_eq_swap]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp [β, mul_comm]
  have hconst : Tendsto (fun k => ∫ x, (∫ s : ℝ, F s x * (β k (l x - s) : ℂ)) ∂ν) atTop
      (𝓝 ((∫ z, m z ∂μ) / 2)) := by
    simp_rw [fun k => (hcore k).2.2]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PartEq
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem row_int (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) (w : Lp ℂ 2 D.ν) (x : H E n 0) :
    Integrable (fun y => kerH φ x y * (w : H E n 0 → ℂ) y) D.ν :=
  by
    let X : Ctx := by
      haveI := CuspidalL2GL.t2Space_GA E n
      haveI := CuspidalL2GL.t2Space_GA E 0
      haveI := CuspidalL2GL.locallyCompactSpace_GA E n
      haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
      haveI := CuspidalL2GL.secondCountableTopology_GA E n
      haveI := CuspidalL2GL.secondCountableTopology_GA E 0
      haveI := (ratProper_holds E n).2.1
      haveI := (ratProper_holds E 0).2.1
      refine { G := H E n 0
               ms := borelH E n 0
               bs := ⟨rfl⟩
               μ := D.μ
               haar := { toIsFiniteMeasureOnCompacts := @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2, toIsMulLeftInvariant := D.haar.1, toIsOpenPosMeasure := D.haar.2.2.1 }
               Γ := ratH E n 0
               cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
               proper := ?_
               F := D.F
               fd := D.fd }
      intro C hC
      have h1 := (ratProper_holds E n).2.2 _ (hC.image continuous_fst)
      have h2 := (ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
      refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
      rintro ⟨_, γ, rfl⟩ hγ
      exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
    exact MemLp.integrable_mul ((kernel_rows_columns_square_integrable X φ hφ).2 x) (Lp.memLp w)

private theorem ker_trM (D : Dom E n 0) {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ)
    (x y : H E n 0) : kerH (trM Φ M) x y = ∑ i, ∑ j, kerH (Φ i j) x y * M j i := by
  let X : Ctx := by
    haveI := CuspidalL2GL.t2Space_GA E n
    haveI := CuspidalL2GL.t2Space_GA E 0
    haveI := CuspidalL2GL.locallyCompactSpace_GA E n
    haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
    haveI := CuspidalL2GL.secondCountableTopology_GA E n
    haveI := CuspidalL2GL.secondCountableTopology_GA E 0
    haveI := (ratProper_holds E n).2.1
    haveI := (ratProper_holds E 0).2.1
    refine { G := H E n 0
             ms := borelH E n 0
             bs := ⟨rfl⟩
             μ := D.μ
             haar := { toIsFiniteMeasureOnCompacts := @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2, toIsMulLeftInvariant := D.haar.1, toIsOpenPosMeasure := D.haar.2.2.1 }
             Γ := ratH E n 0
             cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
             proper := ?_
             F := D.F
             fd := D.fd }
    intro C hC
    have h1 := (ratProper_holds E n).2.2 _ (hC.image continuous_fst)
    have h2 := (ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
    refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
    rintro ⟨_, γ, rfl⟩ hγ
    exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
  have h := (kerLin X (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1)
    (fun p => hΦ p.1 p.2)).2 x y
  have e : trM Φ M = fun z => ∑ p : ι × ι, Φ p.1 p.2 z * M p.2 p.1 := by
    funext z
    simp only [trM, Fintype.sum_prod_type]
  rw [e]
  refine Eq.trans h ?_
  exact Fintype.sum_prod_type _

private theorem part_eq {D : Dom E n 0} {π : CuspSub E n} {U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D}
    (h : IsPiPart D π U Uπ) (f : Hs (ι := ι) D) : Uπ f = U ((piSp D π ι).starProjection f) := by
  have h1 : Uπ ((piSp D π ι).starProjection f) = U ((piSp D π ι).starProjection f) :=
    h.1 _ (Submodule.starProjection_apply_mem _ _)
  have h2 : Uπ (f - (piSp D π ι).starProjection f) = 0 :=
    h.2 _ (Submodule.sub_starProjection_mem_orthogonal _)
  rw [map_sub, sub_eq_zero] at h2
  rw [h2, h1]

private theorem vec_int {D : Dom E n 0} (w : Lp ℂ 2 D.ν) (c : ι → ℂ) (j : ι) {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    (x : H E n 0) :
    ∫ y, kerH φ x y * ((vecM w c) j : H E n 0 → ℂ) y ∂D.ν = c j * ∫ y, kerH φ x y * (w : H E n 0 → ℂ) y ∂D.ν := by
  have e : ((vecM w c) j : H E n 0 → ℂ) =ᵐ[D.ν] fun y => c j * (w : H E n 0 → ℂ) y := by
    have : (vecM w c) j = c j • w := rfl
    rw [this]
    filter_upwards [Lp.coeFn_smul (c j) w] with y hy
    simpa using hy
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [e] with y hy
  rw [hy]; ring

end SlopeTestRemainingChoices

theorem ker_pf :
    Weak → PointRep → PComm → PDiag → Ker := by
  intro hW hPR hPC hPD E _ _ _ n ι _ s m v x
  set w := P0 s.D s.π v with hw
  let u : ι → Hs (ι := ι) s.D := fun i => ContinuousLinearMap.adjoint m.Uπ (s.k₁ x i)
  have hG : ∀ y, (v : H E n 0 → ℂ) y * m.G x (th y) =
      ∑ i, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) := by
    intro y
    simp only [Mid.G, Gk, Finset.mul_sum, u, ContinuousLinearMap.adjoint_inner_left]
  have hI : ∀ i, Integrable (fun y => (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i)) s.D.ν :=
    fun i => (hW E n ι s v (u i) i).1
  have hterm : ∀ i, ∫ y, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) ∂s.D.ν =
      ∑ j, s.M j i * ∫ y, kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y ∂s.D.ν := by
    intro i
    rw [(hW E n ι s v (u i) i).2]
    have e1 : inner ℂ (u i) (s.T₂ (vecM v fun l => s.M l i)) =
        inner ℂ (s.k₁ x i) (m.U (s.T₂ (vecM w fun l => s.M l i))) := by
      simp only [u, ContinuousLinearMap.adjoint_inner_left]
      rw [part_eq m.pp, hPC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂, hPD E n s.D s.π ι]
    rw [e1, hPR E n ι s m.Φ (s.T₁ * m.U * s.T₂) m.t m.o (m.U (s.T₂ (vecM w fun l => s.M l i)))
      (vecM w fun l => s.M l i) rfl x i]
    exact Finset.sum_congr rfl fun j _ => vec_int w _ j (m.t i j) x
  refine ⟨?_, ?_⟩
  · simp only [hG]
    exact integrable_finsetSum _ fun i _ => hI i
  · simp only [hG]
    rw [integral_finsetSum _ fun i _ => hI i]
    simp only [hterm]
    have e2 : ∀ y, kerH m.φ x y * (w : H E n 0 → ℂ) y =
        ∑ i, ∑ j, s.M j i * (kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) := by
      intro y
      rw [Mid.φ, ker_trM s.D m.t, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e2]
    have hr : ∀ i j, Integrable (fun y => kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) s.D.ν :=
      fun i j => row_int s.D (m.t i j) w x
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hr i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hr i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPositionFacts
open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.G8

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem cc (w : Pl E) : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) = w := GlobalTheory.EulerTwU.cPl_cPl w

private theorem cont_thF : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

private theorem twist_int (v : Pl E) (x : GL (Fin n) (Af E))
    (h : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E v)) x ∈ KGL (GlobalTheory.EulerTw.cPl E v) (n := n)) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) ∈ KGL v (n := n) := by
  rw [GlobalTheory.EulerTwU.pc_thF]
  exact GlobalTheory.EulerTwSplit.theta_mem _ (conjLoc_spec _ v).2.2 h

private theorem twist_int_iff (v : Pl E) (x : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map (pLoc E v) (thF E n x) ∈ KGL v (n := n) ↔
      GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E v)) x ∈ KGL (GlobalTheory.EulerTw.cPl E v) (n := n) := by
  refine ⟨fun h => ?_, twist_int v x⟩
  have h1 : GeneralLinearGroup.map (pLoc E (GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v))) (thF E n x) ∈
      KGL (GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E v)) (n := n) := by
    rw [cc]; exact h
  have h2 := twist_int (GlobalTheory.EulerTw.cPl E v) (thF E n x) h1
  rwa [GlobalTheory.EulerTwU.thF_thF] at h2

private theorem twist_away {u v : Pl E} (h : GlobalTheory.EulerTw.cPl E v ≠ u) (a : GLw n u) :
    GeneralLinearGroup.map (pLoc E v) (thF E n (locGL E n u a)) = 1 := by
  have e : GeneralLinearGroup.map (n := Fin n) (conjLoc (IsCMField.complexConj E).toRingEquiv v) 1 = 1 := map_one _
  rw [GlobalTheory.EulerTwU.pc_thF, pLoc_locGL_of_ne h]
  exact (congrArg (thetaGL n (RingHom.id _)) e).trans (map_one _)

private theorem bad_finite (g : GL (Fin n) (Af E)) :
    {v : Pl E | GeneralLinearGroup.map (pLoc E v) g ∉ KGL v (n := n)}.Finite := by
  have h1 : ∀ x : Af E, ∀ᶠ v : Pl E in cofinite, pLoc E v x ∈ v.adicCompletionIntegers E :=
    fun x => x.2.mono fun _ h => h
  have h2 := eventually_all.2 fun i => eventually_all.2 fun j => h1 (g.1 i j)
  have h3 := eventually_all.2 fun i => eventually_all.2 fun j => h1 ((g⁻¹).1 i j)
  have h4 : ∀ᶠ v : Pl E in cofinite, GeneralLinearGroup.map (pLoc E v) g ∈ KGL v (n := n) := by
    filter_upwards [h2, h3] with v a b
    rw [GlobalTheory.EulerTwRestr.mem_KGL_iff]
    exact ⟨fun i j => a i j, fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact b i j⟩
  exact eventually_cofinite.1 h4

private theorem comm_loc (w : Pl E) (a : GLw n w) (c : GL (Fin n) (Af E))
    (h : GeneralLinearGroup.map (pLoc E w) c = 1) : Commute (locGL E n w a) c := by
  show locGL E n w a * c = c * locGL E n w a
  refine GlobalTheory.EulerTwU.gl_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [h, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

private theorem qj (w : Pl E) (b : Bool) (a : GLw n w) : qw n w b (jw n w b a) = a := by
  cases b
  · exact pLoc_locGL _ _
  · show GeneralLinearGroup.map (pLoc E w) (thF E n (thF E n (locGL E n w a))) = a
    rw [GlobalTheory.EulerTwU.thF_thF]
    exact pLoc_locGL _ _

private theorem comm_mapFactor_of_absIrr (w : Pl E) (b : Bool) (a : GLw n w) (c : GL (Fin n) (Af E))
    (h : qw n w b c = 1) : Commute (jw n w b a) c := by
  cases b
  · exact comm_loc w a c h
  · have h1 := (comm_loc w a (thF E n c) h).map (thF E n)
    rwa [GlobalTheory.EulerTwU.thF_thF] at h1

private theorem cont_j (w : Pl E) (b : Bool) : Continuous (jw n w b) := by
  cases b
  · exact GlobalTheory.CuspRep.CuspSub.continuous_locGL w
  · exact cont_thF.comp (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

private theorem cont_q (w : Pl E) (b : Bool) : Continuous (qw (E := E) n w b) := by
  cases b
  · exact GlobalTheory.BCT.LocCpt.continuous_mapLoc w
  · exact (GlobalTheory.BCT.LocCpt.continuous_mapLoc w).comp cont_thF

end SlopeTestRemainingChoices

theorem slotFacts_pf : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places → SlotBasic := by
  intro hP E _ _ _ n S hS
  obtain ⟨-, hc, -, hs⟩ := hP E
  have hsplit : ∀ w : Pl E, IsSplitAt w ↔ GlobalTheory.EulerTw.cPl E w ≠ w := fun w => (hc w).2
  have hsec : ∀ w : Pl E, w ∈ S → GlobalTheory.EulerTw.cPl E w ∈ S → GlobalTheory.EulerTw.cPl E w = w :=
    fun w => (hs S hS w).2
  have hor : ∀ w : Pl E, w ∈ S ∨ GlobalTheory.EulerTw.cPl E w ∈ S := fun w => (hs S hS w).1
  refine ⟨GlobalTheory.EulerTwU.thF_thF, cont_thF, fun w b => ⟨cont_j w b, cont_q w b, qj w b, comm_mapFactor_of_absIrr w b⟩,
    ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, bi⟩ ⟨k, bk⟩ ⟨hi, hi'⟩ ⟨hk, hk'⟩ hne a
    have hik : bi = bk → i ≠ k := fun e e' => hne (by rw [e, e'])
    cases bi <;> cases bk
    · exact pLoc_locGL_of_ne (hik rfl).symm a
    · refine twist_away (fun e => ?_) a
      have e0 : GlobalTheory.EulerTw.cPl E k = i := e
      have hi0 : i ∈ S := hi
      have hk0 : k ∈ S := hk
      exact (hsplit k).1 (hk' rfl) (hsec k hk0 (e0 ▸ hi0))
    · refine twist_away (fun e => ?_) a
      have e0 : GlobalTheory.EulerTw.cPl E k = i := e
      have hi0 : i ∈ S := hi
      have hk0 : k ∈ S := hk
      have e' : GlobalTheory.EulerTw.cPl E i = k := by rw [← e0, cc]
      exact (hsplit i).1 (hi' rfl) (hsec i hi0 (e' ▸ hk0))
    · show GeneralLinearGroup.map (pLoc E k) (thF E n (thF E n (locGL E n i a))) = 1
      rw [GlobalTheory.EulerTwU.thF_thF]
      exact pLoc_locGL_of_ne (hik rfl).symm a
  · intro g
    refine (((bad_finite g).prod (Set.finite_singleton false)).union
      ((bad_finite (thF E n g)).prod (Set.finite_singleton true))).subset ?_
    rintro ⟨w, b⟩ h
    cases b
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨h, rfl⟩
  · intro w hw g
    have hcw : GlobalTheory.EulerTw.cPl E w = w := by
      by_contra h
      exact hw ((hsplit w).2 h)
    have h1 := twist_int_iff w g
    rw [hcw] at h1
    exact h1
  · intro g
    have hL : g ∈ Lev S (fun w : Pl E => KGL w (n := n)) ↔ ∀ i : Pl E × Bool, Sl S i → qw n i.1 i.2 g ∈ KGL i.1 (n := n) := by
      simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
    have hK : g ∈ Kf E n ↔ ∀ w : Pl E, GeneralLinearGroup.map (pLoc E w) g ∈ KGL w (n := n) := by
      simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
    rw [hL, hK]
    constructor
    · intro h w
      by_cases hw : w ∈ S
      · exact h (w, false) ⟨hw, by simp⟩
      · have hw' : GlobalTheory.EulerTw.cPl E w ∈ S := (hor w).resolve_left hw
        have hne : GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) ≠ GlobalTheory.EulerTw.cPl E w := by
          rw [cc]
          exact fun e => hw (e ▸ hw')
        have h1 := (twist_int_iff (n := n) (GlobalTheory.EulerTw.cPl E w) g).1
          (h (GlobalTheory.EulerTw.cPl E w, true) ⟨hw', fun _ => (hsplit _).2 hne⟩)
        rwa [cc] at h1
    · rintro h ⟨w, b⟩ -
      cases b
      · exact h w
      · exact twist_int w g (h _)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end
