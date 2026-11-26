module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KronHolPsiOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroup
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.DriftUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem _root_.GlobalTheory.DriftUnitary.continuous_orbit {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    Continuous fun g : H => X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC
  refine continuous_pi fun τ => ?_
  exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).matrix_mul
    continuous_const

private theorem single_one_mulVec_eq_pi_single (r : ℕ) (j k : Fin r) (w : Fin r → ℂ) :
    (Matrix.single j k (1 : ℂ)).mulVec w = Pi.single j (w k) := by
  ext i
  by_cases hi : i = j
  · subst hi; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hi, Ne.symm hi]

private theorem eq_bot_or_eq_whole_of_single_mulVec_invariant (r p : ℕ) (hp : 0 < p) (hpr : p < r)
    (W : Submodule ℂ (Fin r → ℂ))
    (hW : ∀ (j k : Fin r), (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W,
      (Matrix.single j k 1).mulVec v ∈ W ∧ (Matrix.single k j 1).mulVec v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  have hsmul : ∀ (i : Fin r) (z : ℂ), z ≠ 0 → Pi.single i z ∈ W → Pi.single i (1 : ℂ) ∈ W := by
    intro i z hz h
    have e : z⁻¹ • (Pi.single i z : Fin r → ℂ) = Pi.single i 1 := by
      ext l
      by_cases hl : l = i <;> simp [hl, hz]
    rw [← e]
    exact W.smul_mem _ h
  let j0 : Fin r := ⟨0, by omega⟩
  let k0 : Fin r := ⟨p, hpr⟩
  have hj0 : (j0 : ℕ) < p := hp
  have hk0' : p ≤ (k0 : ℕ) := le_rfl
  have hk0 : Pi.single k0 (1 : ℂ) ∈ W := by
    rcases Nat.lt_or_ge (m : ℕ) p with h | h
    · have h1 := (hW m k0 h hk0' v hvW).2
      rw [single_one_mulVec_eq_pi_single] at h1
      exact hsmul _ _ hm h1
    · have h1 := (hW j0 m hj0 h v hvW).1
      rw [single_one_mulVec_eq_pi_single] at h1
      have h3 := (hW j0 k0 hj0 hk0' _ (hsmul _ _ hm h1)).2
      rw [single_one_mulVec_eq_pi_single] at h3
      simpa using h3
  have he0 : Pi.single j0 (1 : ℂ) ∈ W := by
    have h1 := (hW j0 k0 hj0 hk0' _ hk0).1
    rw [single_one_mulVec_eq_pi_single] at h1
    simpa using h1
  have hall : ∀ i : Fin r, Pi.single i (1 : ℂ) ∈ W := by
    intro i
    rcases Nat.lt_or_ge (i : ℕ) p with h | h
    · have h1 := (hW i k0 h hk0' _ hk0).1
      rw [single_one_mulVec_eq_pi_single] at h1
      simpa using h1
    · have h1 := (hW j0 i hj0 h _ he0).2
      rw [single_one_mulVec_eq_pi_single] at h1
      simpa using h1
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ i, w i • (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact Submodule.sum_mem _ fun i _ => W.smul_mem _ (hall i)

theorem _root_.GlobalTheory.DriftUnitary.exists_drift_function :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < X.p0 → X.p0 < r → ∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  intro r X H hH _ _ hp0 hpr x0 hx0
  obtain ⟨S, hSne, hS1, hS2, hS3⟩ := _root_.GlobalTheory.exists_finite_symmetric_irreducible_rotations
    eq_bot_or_eq_whole_of_single_mulVec_invariant r X.p0 hp0 hpr
  obtain ⟨τ0⟩ := _root_.GlobalTheory.LineHeight.nonempty_cmType X
  obtain ⟨f, c, b, hc0, hc1, hb, hlsc, hf0, hfinv, hdrift, hla⟩ :=
    _root_.GlobalTheory.exists_drift_function_orthFrames r X hp0 hpr τ0 S hS1 hS2 (fun a ha => (hS3 a ha).1)
  have horb := (((_root_.GlobalTheory.UnitaryFrames.unitary_group_frames (E := E)).2 r X H hH).2.2 x0 hx0).1
  have hstep := fun a : S => _root_.GlobalTheory.UnitaryLift.step_of_right_mul r X H hH x0 hx0 τ0 a.1
    (hS3 a.1 a.2).2.choose (hS3 a.1 a.2).1 (hS3 a.1 a.2).2.choose_spec.1 (hS3 a.1 a.2).2.choose_spec.2
  choose hS kS hkS hupd using hstep
  refine ⟨S, inferInstance, hSne.to_subtype, hS,
    fun g => f (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0), c, b,
    fun s => ⟨kS s, hkS s⟩, ?_, fun g => hf0 _ (horb g), ?_, hc0, hc1, hb, ?_, ?_⟩
  · have hcont := _root_.GlobalTheory.DriftUnitary.continuous_orbit X H x0
    have hl : LowerSemicontinuous fun g : H =>
        f (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
      intro g y hy
      have ht : Filter.Tendsto (fun g : H =>
          X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) (𝓝 g)
          (𝓝[{x | _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x}] (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) :=
        tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto g, Filter.Eventually.of_forall fun g' => show _ ∈ {x | _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x} from horb g'⟩
      exact ht.eventually (hlsc _ (horb g) y hy)
    exact hl.measurable
  · rintro u ⟨γ, hγ, hu⟩ g
    have e : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
      funext τ
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hu τ,
        Matrix.mul_assoc]
      rfl
    show f _ = f _
    rw [e]
    exact hfinv γ hγ _ (horb g)
  · intro g
    simp only [hupd, Fintype.card_coe]
    exact (Finset.sum_coe_sort S _).trans_le (hdrift _ (horb g))
  · intro M
    obtain ⟨ε, hε, h⟩ := hla M
    exact ⟨ε, hε, fun g hg => h _ (horb g) hg⟩

end GlobalTheory.DriftUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroupStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_drift_function_realUnitaryGroup : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < X.p0 → X.p0 < r → ∀ x0, IsOrth X x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  first | exact @GlobalTheory.DriftUnitary.exists_drift_function | exact GlobalTheory.DriftUnitary.exists_drift_function | (intros; apply GlobalTheory.DriftUnitary.exists_drift_function <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CfwMOfExtraBounds
section -- merged from Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.LowSpanCombinations
namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def hf (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ :=
  X.c τ * X.maj x τ (Data.emb τ.1 ξ)

def ExtraBounds (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ,
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, hf X ξ x τ ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ) ∧
    ∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)

def lowIdx (D T : ℕ) : Finset (Fin D → ℕ) :=
  (Fintype.piFinset fun _ : Fin D => Finset.range T).filter fun al => ∑ i, al i + D < T

theorem nonempty_cmType (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have := (X.cmType τ).not.1 h
    exact ⟨⟨_, not_not.1 this⟩⟩

theorem tt_eq (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    X.tt ξ x τ = 1 / hf X ξ x τ := rfl

end

end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
end

namespace GlobalTheory.FlatCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hf_pos (X : Data E r) {ξ : Fin r → E} (hξ : ξ ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    0 < hf X ξ x τ := by
  unfold hf
  refine mul_pos (IsotropicThreshold.c_pos X τ) (X.maj_pos hx τ ?_)
  intro h0
  apply hξ
  funext a
  have h1 := congrFun h0 a
  simpa [Data.emb] using h1

theorem guard_iff (X : Data E r) {ξ : Fin r → E} (hξ : ξ ≠ 0) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    hf X ξ x τ ≤ 1 ↔ 1 ≤ X.tt ξ x τ := by
  rw [tt_eq X ξ x τ, one_le_div (hf_pos X hξ hx τ)]

theorem logTerm_nonneg (X : Data E r) (x : Frame X.Ψ r) : 0 ≤ Real.log (1 + 1 / X.la1 x) := by
  apply Real.log_nonneg
  have h1 : 0 ≤ 1 / X.la1 x := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  linarith

theorem exists_short (X : Data E r) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, 0 < X.firstMinimumSq x → X.firstMinimumSq x < ε →
    ∃ v, X.IsIso v ∧ (∀ τ, 1 ≤ X.tt v x τ) ∧ ∀ τ, 1 / (2 * X.firstMinimumSq x) ≤ X.tt v x τ := by
  obtain ⟨δ0, hδ0, hiso⟩ := IsotropicThreshold.iso_threshold X
  refine ⟨min (δ0 / 2) (1 / 2), lt_min (by linarith) (by norm_num), fun x hx hpos hsmall => ?_⟩
  have hmin1 := min_le_left (δ0 / 2) (1 / 2)
  have hmin2 := min_le_right (δ0 / 2) (1 / 2)
  have hne : {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : X.firstMinimumSq x = 0 := by rw [Data.firstMinimumSq, hemp, Real.sInf_empty]
    linarith
  obtain ⟨t, ⟨v, hvΛ, hv0, rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt hne (show X.firstMinimumSq x < 2 * X.firstMinimumSq x by linarith)
  have hsum_lt : ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) < δ0 := by linarith
  have hherm := hiso x hx v hvΛ hsum_lt
  have hterm : ∀ τ, hf X v x τ ≤ ∑ τ', X.c τ' * X.maj x τ' (Data.emb τ'.1 v) := fun τ =>
    Finset.single_le_sum (f := fun τ' => X.c τ' * X.maj x τ' (Data.emb τ'.1 v))
      (fun τ' _ => (hf_pos X hv0 hx τ').le) (Finset.mem_univ τ)
  refine ⟨v, ⟨hvΛ, hherm, hv0⟩, fun τ => ?_, fun τ => ?_⟩
  · rw [← guard_iff X hv0 hx τ]
    linarith [hterm τ]
  · rw [tt_eq X v x τ]
    exact one_div_le_one_div_of_le (hf_pos X hv0 hx τ) (by linarith [hterm τ])

theorem bdd_add_log (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : cfwM X ps a) (ha : 0 < a)
    (K : ℝ) : ∃ B : ℝ, ∀ x ∈ X.dom, ps x + K * Real.log (1 + 1 / X.la1 x) ≤ B := by
  obtain ⟨⟨C1, A1, h1⟩, h2⟩ := h
  obtain ⟨C2, A2, h2'⟩ := h2 (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨ε, hε, hshort⟩ := exists_short X
  have hM : 0 ≤ |A1| + |K| + |A2| := by positivity
  have hpa : 0 < 8 * Real.pi * a := by positivity
  refine ⟨max (C1 + (|A1| + |K| + |A2|) / Real.sqrt ε)
    (C2 + (|A1| + |K| + |A2|) ^ 2 / (8 * Real.pi * a)), fun x hx => ?_⟩
  have hL0 := logTerm_nonneg X x
  have hy0 : 0 ≤ 1 / X.la1 x := div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hLy : Real.log (1 + 1 / X.la1 x) ≤ 1 / X.la1 x := by
    have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / X.la1 x by linarith)
    linarith
  have hK := mul_le_mul_of_nonneg_right (le_abs_self K) hL0
  have hA1 := mul_le_mul_of_nonneg_right (le_abs_self A1) hL0
  have hA2 := mul_le_mul_of_nonneg_right (le_abs_self A2) hL0
  have hA1' := mul_nonneg (abs_nonneg A1) hL0
  have hA2' := mul_nonneg (abs_nonneg A2) hL0
  by_cases hs : 0 < X.firstMinimumSq x ∧ X.firstMinimumSq x < ε
  · obtain ⟨v, hv, hv1, hv2⟩ := hshort x hx hs.1 hs.2
    have hb := h2' x hx v hv hv1
    have := nonempty_cmType X
    have hinf : 1 / (2 * X.firstMinimumSq x) ≤ ⨅ τ, X.tt v x τ := le_ciInf hv2
    have hla : X.la1 x ^ 2 = X.firstMinimumSq x := Real.sq_sqrt hs.1.le
    have hyy : 1 / (2 * X.firstMinimumSq x) = (1 / X.la1 x) ^ 2 / 2 := by
      rw [div_pow, one_pow, hla]; ring
    rw [hyy] at hinf
    have hcoef : (0 : ℝ) ≤ 8 * Real.pi * (1 - 2 * (1 / 4)) * a := by nlinarith [Real.pi_pos]
    have hI := mul_le_mul_of_nonneg_left hinf hcoef
    have hMy := mul_le_mul_of_nonneg_left hLy hM
    have hq : (|A1| + |K| + |A2|) * (1 / X.la1 x) - 2 * Real.pi * a * (1 / X.la1 x) ^ 2 ≤
        (|A1| + |K| + |A2|) ^ 2 / (8 * Real.pi * a) := by
      rw [le_div_iff₀ hpa]
      nlinarith [sq_nonneg (4 * Real.pi * a * (1 / X.la1 x) - (|A1| + |K| + |A2|))]
    refine le_trans ?_ (le_max_right _ _)
    linarith
  · have hLe : Real.log (1 + 1 / X.la1 x) ≤ 1 / Real.sqrt ε := by
      rcases le_or_gt (X.firstMinimumSq x) 0 with h0 | h0
      · have hz : X.la1 x = 0 := Real.sqrt_eq_zero'.2 h0
        rw [hz, div_zero, add_zero, Real.log_one]
        positivity
      · have hge : ε ≤ X.firstMinimumSq x := by
          by_contra hlt
          exact hs ⟨h0, not_le.1 hlt⟩
        exact hLy.trans (one_div_le_one_div_of_le (Real.sqrt_pos.2 hε) (Real.sqrt_le_sqrt hge))
    have hb := h1 x hx
    have hMe := mul_le_mul_of_nonneg_left hLe hM
    have he : (|A1| + |K| + |A2|) * (1 / Real.sqrt ε) = (|A1| + |K| + |A2|) / Real.sqrt ε := by ring
    refine le_trans ?_ (le_max_left _ _)
    linarith

theorem cfwM_of_extraBounds (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (h : ExtraBounds X ps a) :
    cfwM X ps a := by
  obtain ⟨A, h1, C, h2⟩ := h
  refine ⟨⟨C, A, h2⟩, fun η hη _ => ?_⟩
  obtain ⟨C', hC'⟩ := h1 η hη
  exact ⟨C', A, fun x hx ξ hξ htt => hC' x hx ξ hξ fun τ => (guard_iff X hξ.2.2 hx τ).2 (htt τ)⟩

theorem extraBounds_of_cfwM (X : Data E r) {ps : Frame X.Ψ r → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h : cfwM X ps a) : ExtraBounds X ps a := by
  rcases ha.eq_or_lt with ha0 | hapos
  · subst ha0
    obtain ⟨⟨C, A, hC⟩, -⟩ := h
    refine ⟨A, fun η _ => ⟨C, fun x hx ξ _ _ => ?_⟩, C, hC⟩
    have h1 := hC x hx
    simp only [mul_zero, zero_mul, sub_zero]
    exact h1
  · obtain ⟨B0, hB0⟩ := bdd_add_log X h hapos 0
    have := nonempty_cmType X
    refine ⟨0, fun η hη => ?_, B0, fun x hx => by linarith [hB0 x hx]⟩
    rcases lt_or_ge η (1 / 2) with hη2 | hη2
    · obtain ⟨C', A', hC'⟩ := h.2 (η / 2) (by linarith) (by linarith)
      obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 - 2 * η) / (1 - η) := ⟨_, rfl⟩
      have h1η : 0 < 1 - η := by linarith
      have hθ0 : 0 < θ := by rw [hθ]; exact div_pos (by linarith) h1η
      have hθ1 : θ < 1 := by rw [hθ, div_lt_one h1η]; linarith
      have hθη : θ * (1 - η) = 1 - 2 * η := by rw [hθ]; field_simp
      obtain ⟨K, hK⟩ : ∃ K : ℝ, (1 - θ) * K = θ * |A'| :=
        ⟨θ * |A'| / (1 - θ), by field_simp [(sub_pos.2 hθ1).ne']⟩
      obtain ⟨BK, hBK⟩ := bdd_add_log X h hapos K
      refine ⟨θ * C' + (1 - θ) * BK, fun x hx ξ hξ hg => ?_⟩
      have htt : ∀ τ, 1 ≤ X.tt ξ x τ := fun τ => (guard_iff X hξ.2.2 hx τ).1 (hg τ)
      have hL0 := logTerm_nonneg X x
      have e1 := mul_le_mul_of_nonneg_left (hC' x hx ξ hξ htt) hθ0.le
      have e2 := mul_le_mul_of_nonneg_left (hBK x hx) (sub_pos.2 hθ1).le
      have hKL : (1 - θ) * K * Real.log (1 + 1 / X.la1 x) =
          θ * |A'| * Real.log (1 + 1 / X.la1 x) := by rw [hK]
      have hA : θ * A' * Real.log (1 + 1 / X.la1 x) ≤ θ * |A'| * Real.log (1 + 1 / X.la1 x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self A') hθ0.le) hL0
      have h3 : θ * (8 * Real.pi * (1 - 2 * (η / 2)) * a * ⨅ τ, X.tt ξ x τ) =
          8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ := by
        rw [← hθη]; ring
      linarith
    · refine ⟨B0, fun x hx ξ hξ hg => ?_⟩
      have htt : ∀ τ, 1 ≤ X.tt ξ x τ := fun τ => (guard_iff X hξ.2.2 hx τ).1 (hg τ)
      have hI : 1 ≤ ⨅ τ, X.tt ξ x τ := le_ciInf htt
      have h2 := hB0 x hx
      have hpI : 0 ≤ 8 * Real.pi * a * ⨅ τ, X.tt ξ x τ :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith

theorem extraBounds_iff (X : Data E r) (ps : Frame X.Ψ r → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ExtraBounds X ps a ↔ cfwM X ps a := ⟨fun h => cfwM_of_extraBounds X h, extraBounds_of_cfwM X ha⟩

end

end GlobalTheory.FlatCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SmoothWtContDiffOn
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegrandAemeasurable
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ContDiff ENNReal

namespace GlobalTheory.SkodaIter

noncomputable section

variable {n : ℕ} {U : Set (V n)}

def integrand (s : Fin n → V n → ℂ) (ph : V n → ℝ) (t : ℝ) (G : V n → ℂ) (z : V n) : ℝ≥0∞ :=
  ENNReal.ofReal (‖G z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-t) * Real.exp (-ph z))

theorem holo_val {f : V n → ℂ} (hf : DifferentiableOn ℂ f U) :
    Holo n (Subtype.val : U → V n) (fun x => f x.1) := by
  intro e he
  exact (hf.mono (HE.target_sub he)).congr (HE.comp_symm_eqOn f he)

theorem normSq_continuousOn {s : Fin n → V n → ℂ} (hs : ∀ k, DifferentiableOn ℂ (s k) U) :
    ContinuousOn (fun z => ∑ k, ‖s k z‖ ^ 2) U := by
  exact continuousOn_finsetSum _ (fun k _ => ((hs k).continuousOn.norm).pow 2)

theorem normSq_pos {s : Fin n → V n → ℂ} {z : V n} {k : Fin n} (h : s k z ≠ 0) :
    0 < ∑ k, ‖s k z‖ ^ 2 := by
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) 2)
    (Finset.single_le_sum (f := fun j => ‖s j z‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k))

theorem extend (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    {ph : V n → ℝ} (hph : ContinuousOn ph U) {t : ℝ} (ht : 0 ≤ t) {G : V n → ℂ}
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ s k0 y ≠ 0})
    (hI : ∫⁻ z in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G z < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ s k0 y ≠ 0} ∧
      ∫⁻ z in U, integrand s ph t G' z < ⊤ := by
  have hM : IsOpen {y | y ∈ U ∧ s k0 y ≠ 0} := HE.isOpen_punct hU (hs k0)
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤ := by
    intro p hp
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
    have hKU : closedBall p (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hbU : ball p (ε / 2) ⊆ U := ball_subset_closedBall.trans hKU
    have hK : IsCompact (closedBall p (ε / 2)) := isCompact_closedBall p _
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((normSq_continuousOn hs).mono hKU)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hph.mono hKU)
    refine ⟨ε / 2, half_pos hε, hbU, ?_⟩
    have hAM : ball p (ε / 2) \ {y | s k0 y = 0} ⊆ {y | y ∈ U ∧ s k0 y ≠ 0} :=
      fun y hy => ⟨hbU hy.1, hy.2⟩
    have hAeq : ball p (ε / 2) \ {y | s k0 y = 0} = ball p (ε / 2) ∩ {y | y ∈ U ∧ s k0 y ≠ 0} := by
      ext y
      exact ⟨fun h => ⟨h.1, hbU h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    have hAm : MeasurableSet (ball p (ε / 2) \ {y | s k0 y = 0}) := by
      rw [hAeq]; exact (isOpen_ball.inter hM).measurableSet
    have hpt : ∀ y ∈ ball p (ε / 2) \ {y | s k0 y = 0},
        ENNReal.ofReal (‖G y‖ ^ 2) ≤ ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y := by
      intro y hy
      have hyK : y ∈ closedBall p (ε / 2) := ball_subset_closedBall hy.1
      have hpos : 0 < ∑ k, ‖s k y‖ ^ 2 := normSq_pos (k := k0) hy.2
      have hfB : ∑ k, ‖s k y‖ ^ 2 ≤ B := (Real.le_norm_self _).trans (hB y hyK)
      have hB0 : 0 < B := hpos.trans_le hfB
      have hphC : ph y ≤ C := (Real.le_norm_self _).trans (hC y hyK)
      have h1 : 1 ≤ (∑ k, ‖s k y‖ ^ 2) ^ (-t) * B ^ t := by
        rw [Real.rpow_neg hpos.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hpos t)]
        exact Real.rpow_le_rpow hpos.le hfB ht
      have h2 : 1 ≤ Real.exp C * Real.exp (-ph y) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      have h3 := mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
      simp only [integrand]
      rw [← ENNReal.ofReal_mul (mul_pos (Real.rpow_pos_of_pos hB0 t) (Real.exp_pos C)).le]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖G y‖)]
    calc ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, ENNReal.ofReal (‖G y‖ ^ 2)
        ≤ ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0},
            ENNReal.ofReal (B ^ t * Real.exp C) * integrand s ph t G y :=
          lintegral_mono_ae (ae_restrict_of_forall_mem hAm hpt)
      _ = ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in ball p (ε / 2) \ {y | s k0 y = 0}, integrand s ph t G y :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (B ^ t * Real.exp C) *
            ∫⁻ y in {y | y ∈ U ∧ s k0 y ≠ 0}, integrand s ph t G y :=
          mul_le_mul (le_refl _) (lintegral_mono_set hAM) zero_le zero_le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI
  obtain ⟨G', hG'd, hG'eq⟩ := HE.ext_glue hU (s k0) G (hs k0) hgn hG hloc
  refine ⟨G', hG'd, hG'eq, ?_⟩
  have hnull : volume {y | y ∈ U ∧ s k0 y = 0} = 0 := HE.zeros_null hU (hs k0) hgn
  have hae : (U : Set (V n)) =ᵐ[volume] {y | y ∈ U ∧ s k0 y ≠ 0} := by
    have e1 : volume (U \ {y | y ∈ U ∧ s k0 y ≠ 0}) = 0 :=
      measure_mono_null (fun y (hy : y ∈ U \ {y | y ∈ U ∧ s k0 y ≠ 0}) =>
        (⟨hy.1, Classical.byContradiction fun h => hy.2 ⟨hy.1, h⟩⟩ : y ∈ {y | y ∈ U ∧ s k0 y = 0})) hnull
    have e2 : volume ({y | y ∈ U ∧ s k0 y ≠ 0} \ U) = 0 :=
      measure_mono_null (fun y hy => (hy.2 hy.1.1).elim) measure_empty
    exact (ae_eq_set (μ := volume)).2 ⟨e1, e2⟩
  rw [Measure.restrict_congr_set hae]
  rw [lintegral_congr_ae (ae_restrict_of_forall_mem hM.measurableSet
    (fun y hy => show integrand s ph t G' y = integrand s ph t G y by simp only [integrand, hG'eq hy]))]
  exact hI

theorem step (hn : 2 ≤ n) (hU : IsOpen U) {s : Fin n → V n → ℂ} (k0 : Fin n)
    (hs : ∀ k, DifferentiableOn ℂ (s k) U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, s k0 y ≠ 0)
    (hS : ∃ S : EtaleStein n {z | z ∈ U ∧ s k0 z ≠ 0}, S.z = Subtype.val)
    {ph : V n → ℝ} (hph : ContDiffOn ℝ ∞ ph U)
    (hl : ∀ z ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => ((ph w : ℝ) : ℂ)) z ξ).re)
    {t : ℝ} (ht : (n : ℝ) - 1 < t) {F : V n → ℂ} (hF : DifferentiableOn ℂ F U)
    (hI : ∫⁻ z in U, integrand s ph (t + 1) F z < ⊤) :
    ∃ h : Fin n → V n → ℂ, (∀ i, DifferentiableOn ℂ (h i) U ∧
      ∫⁻ z in U, integrand s ph t (h i) z < ⊤) ∧ ∀ z ∈ U, F z = ∑ i, s i z * h i z := by
  obtain ⟨S, hSz⟩ := hS
  have hM : IsOpen {z | z ∈ U ∧ s k0 z ≠ 0} := HE.isOpen_punct hU (hs k0)
  have ht0 : 0 ≤ t := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hint : ∫⁻ x, ENNReal.ofReal (‖F x.1‖ ^ 2 * (∑ i, ‖s i x.1‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph x.1))
      ∂(vol n S.z) < ⊤ := by
    rw [hSz]
    refine (HE.lintegral_val hM (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖s i y‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-ph y)))).trans_lt ?_
    exact lt_of_le_of_lt (lintegral_mono_set (fun y hy => hy.1)) hI
  obtain ⟨hh, hhh, hdec, hbound⟩ := ReciprocityTheory.L2DbarEstimates.skoda n _ S n (fun i x => s i x.1) (fun x => ph x.1) t
    (fun x => F x.1) hn
    (fun i => by rw [hSz]; exact holo_val ((hs i).mono (fun y hy => hy.1)))
    (fun x => ⟨k0, x.2.2⟩)
    (by rw [hSz]; exact HE.smoothR_val (hph.mono (fun y hy => hy.1)))
    (by rw [hSz]; intro x ξ; rw [HE.levi_val hM ph x ξ]; exact hl x.1 x.2.1 ξ)
    ht
    (by rw [hSz]; exact holo_val (hF.mono (fun y hy => hy.1)))
    hint
  have hfin := lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint)
  rw [hSz] at hfin
  have hhv : ∀ i, Holo n (Subtype.val : {z // z ∈ {z | z ∈ U ∧ s k0 z ≠ 0}} → V n) (hh i) := by
    intro i; rw [← hSz]; exact hhh i
  have hGd : ∀ i, DifferentiableOn ℂ (HE.ext0 (hh i)) {z | z ∈ U ∧ s k0 z ≠ 0} :=
    fun i => HE.differentiableOn_extendByZero hM (hhv i)
  have hGi : ∀ i, ∫⁻ y in {z | z ∈ U ∧ s k0 z ≠ 0}, integrand s ph t (HE.ext0 (hh i)) y < ⊤ := by
    intro i
    refine ((HE.lintegral_val hM (fun y => integrand s ph t (HE.ext0 (hh i)) y)).symm.trans_le ?_).trans_lt hfin
    refine lintegral_mono (fun x => ?_)
    simp only [integrand, HE.extendByZeroOnSubset_apply_coe]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun j => ‖hh j x‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
      (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le
  choose H hHd hHeq hHint using fun i => extend hU k0 hs hgn hph.continuousOn ht0 (hGd i) (hGi i)
  refine ⟨H, fun i => ⟨hHd i, hHint i⟩, ?_⟩
  have hDc : ContinuousOn (fun z => F z - ∑ i, s i z * H i z) U :=
    hF.continuousOn.sub (continuousOn_finsetSum _ (fun i _ => (hs i).continuousOn.mul (hHd i).continuousOn))
  intro z hz
  by_contra hne
  have hW := hDc.isOpen_inter_preimage hU (isOpen_compl_singleton (x := (0:ℂ)))
  obtain ⟨y, ⟨hyU, hyD⟩, hy0⟩ := hgn _ hW Set.inter_subset_left ⟨z, hz, by simpa [sub_eq_zero] using hne⟩
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hyD
  apply hyD
  have hd := hdec ⟨y, hyU, hy0⟩
  dsimp only at hd
  rw [sub_eq_zero, hd]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hHeq i ⟨hyU, hy0⟩]
  exact (congrArg (fun w => s i y * w) (HE.extendByZeroOnSubset_apply_coe (hh i) ⟨y, hyU, hy0⟩)).symm

end

end GlobalTheory.SkodaIter
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivUpPf

noncomputable section

theorem logSum_contDiffAt {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖g k y‖ ^ 2)) z := by
  have h : ContDiffAt ℝ ∞ (fun y => ∑ k, ‖g k y‖ ^ 2) z := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hg k) hz)
  exact h.log (sum_normSq_pos hne).ne'

theorem logSum_levi_nonneg {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0)
    (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((Real.log (∑ k, ‖g k y‖ ^ 2) : ℝ) : ℂ)) z ξ).re := by
  obtain ⟨k, hk⟩ := hne
  have hne' : (fun i => g i z) ≠ 0 := fun h => hk (congrFun h k)
  have h := leviLogNormSq n N g z ξ
    (fun i => (HE.contDiffAt_of_punct hU (hg i) hz).of_le HE.two_le_inf) hne'
  simp only [← Complex.normSq_eq_norm_sq]
  have e : (fun y => ((Real.log (∑ k, Complex.normSq (g k y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ) := rfl
  rw [e, h, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem w_diffOn (Xa : ArchInM X) (x0 : Frame X.Ψ r) (k : Fin Xa.N) :
    DifferentiableOn ℂ (fun z => Xa.w k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Xa.w_van k).1.1.1.1

theorem s_diffOn {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k : Fin (nd X)) :
    DifferentiableOn ℂ (fun z => Fl.s k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Fl.s_van k).1.1.1.1

theorem logw_contDiffAt (Xa : ArchInM X) (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖Xa.w k (cpt X x0 y)‖ ^ 2)) z :=
  logSum_contDiffAt (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz)

end

end GlobalTheory.Up.DivUpPf

namespace GlobalTheory.Up

open DivUpPf

end GlobalTheory.Up
end
