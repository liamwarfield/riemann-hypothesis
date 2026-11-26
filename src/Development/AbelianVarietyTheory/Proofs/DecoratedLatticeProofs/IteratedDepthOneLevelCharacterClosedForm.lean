module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem iter_lam_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : (P.iter t μ hμ j).J), ∃ (g₀ : P.J) (D : Fin j → GL t k), (g₀ : GL r k).val = (g : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (∀ i, D i ∈ KO k t ∧ (D i).val = Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val i) ∧ (P.iter t μ hμ j).lam g = P.lam g₀ * ∏ i : Fin j, μ (i.val + 1) (Matrix.GeneralLinearGroup.det (D i)) := by
  intro k _ _ _ _ r t _ _ _ _ P μ hμ j
  induction j with
  | zero =>
    intro g
    refine ⟨⟨(reGL (ixZero r t)).symm (g : GL (Ix r t 0) k), g.2⟩, fun i => i.elim0, rfl, fun i => i.elim0, ?_⟩
    rw [Fin.prod_univ_zero, mul_one]
    rfl
  | succ j ih =>
    intro g
    let h : (P.iter t μ hμ j).stepJ t := ⟨(reGL (ixSucc r t j)).symm g, g.2⟩
    obtain ⟨D, hD, eD⟩ := h.2.2.2.2.2
    have eu := TypeDatum.corner_val _ h
    have e := TypeDatum.step_lam_eq _ (μ (j + 1)) (hμ _) h _ eu D eD
    obtain ⟨g₀, D', e0, hD', el⟩ := ih (TypeDatum.corner _ h)
    refine ⟨g₀, Fin.snoc (α := fun _ => GL t k) D' D, ?_, ?_, ?_⟩
    · rw [e0, eu]; rfl
    · intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact ⟨hD, by rw [eD]; rfl⟩
      | cast i =>
        simp only [Fin.snoc_castSucc]
        refine ⟨(hD' i).1, ?_⟩
        rw [(hD' i).2, eu]; rfl
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
      rw [← mul_assoc, ← el]
      exact e

end GlobalTheory.SymBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedFormStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDepthOneLevel_character_closed_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : (P.iter t μ hμ j).J), ∃ (g₀ : P.J) (D : Fin j → GL t k), (g₀ : GL r k).val = (g : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (∀ i, D i ∈ KO k t ∧ (D i).val = Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val i) ∧ (P.iter t μ hμ j).lam g = P.lam g₀ * ∏ i : Fin j, μ (i.val + 1) (Matrix.GeneralLinearGroup.det (D i)) := by
  first | exact @GlobalTheory.SymBridge.iter_lam_closed | exact GlobalTheory.SymBridge.iter_lam_closed | (intros; apply GlobalTheory.SymBridge.iter_lam_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToLocEqMapToMatrix
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem toLoc_eq_map_toMatrix' {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) (x : Sp E N →ₗ[E] Sp E N) :
    toLoc ι e e x = ((LinearMap.toMatrix' x).submatrix e e).map ι := by
  ext i j
  simp only [toLoc, Matrix.map_apply, Matrix.submatrix_apply, LinearMap.toMatrix'_apply]

theorem toLoc_comp_square {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) (x y : Sp E N →ₗ[E] Sp E N) :
    toLoc ι e e (x ∘ₗ y) = toLoc ι e e x * toLoc ι e e y := by
  rw [toLoc_eq_map_toMatrix', toLoc_eq_map_toMatrix', toLoc_eq_map_toMatrix', LinearMap.toMatrix'_comp,
    ← Matrix.submatrix_mul_equiv _ _ _ e _, Matrix.map_mul]

theorem toLoc_id_square {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A]
    {N : ℕ} (e : A ≃ Fin N) :
    toLoc ι e e (LinearMap.id : Sp E N →ₗ[E] Sp E N) = 1 := by
  rw [toLoc_eq_map_toMatrix', LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv,
    Matrix.map_one _ ι.map_zero ι.map_one]

end GlobalTheory.SymBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralPeriodicCompactSupportEqFiniteSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralPeriodicCompactSupportEqFiniteSum
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.PeriodicIntegral

theorem exists_irreducible_of_isUnif {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ϖ : kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) :
    ∃ p : 𝒪[k], Irreducible p ∧ (p : k) = ϖ := by
  have hmem : (ϖ : k) ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff]; exact ((h ϖ).2 le_rfl).le
  refine ⟨⟨ϖ, hmem⟩, ?_, rfl⟩
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext y
  rw [Ideal.mem_span_singleton, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one, h]
  exact Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k)) (x := y) (y := ⟨(ϖ : k), hmem⟩)

theorem integral_eq_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (A B : ℕ) (T : Finset k), (∀ t ∈ T, valuation k t ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x : k, valuation k x ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) → ∃! t, t ∈ T ∧ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B)) → ∀ (I : Type) [Fintype I] [DecidableEq I] (F : (I → k) → ℂ), (∀ x, F x ≠ 0 → ∀ i, valuation k (x i) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x y, (∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) → F (x + y) = F x) → ∫ x, F x ∂(Measure.pi fun _ : I => ν) = (((resCard k : ℂ) ^ B)⁻¹) ^ Fintype.card I * ∑ t ∈ Fintype.piFinset (fun _ : I => T), F t := by
  intro k _ _ _ _ _ _ ν hν ϖ hϖ A B T hT hU I _ _ F hF hper
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨p, hp, hpϖ⟩ := exists_irreducible_of_isUnif hϖ
  have hnabs : nabs k ϖ = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp hpϖ.symm
  set u : kˣ := ϖ ^ B with hu
  let S : k → Set k := fun t => (fun x => -t + x) ⁻¹' cball u
  let box : (I → k) → Set (I → k) := fun t => Set.univ.pi fun i => S (t i)
  let P := Fintype.piFinset fun _ : I => T
  have hmemS : ∀ t x, x ∈ S t ↔ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B) := by
    intro t x; simp [S, cball, u, sub_eq_neg_add]
  have hmemBox : ∀ t x, x ∈ box t ↔ ∀ i, valuation k (x i - t i) ≤ valuation k ((ϖ : k) ^ B) := by
    intro t x; simp only [box, Set.mem_univ_pi, hmemS]
  have hshift : ∀ x t, x ∈ box t → F t = F x := by
    intro x t hx
    have := hper x (t - x) (fun i => by
      rw [Pi.sub_apply, ← Valuation.map_neg, neg_sub]; exact (hmemBox t x).1 hx i)
    simpa using this
  have hdec : ∀ x, F x = ∑ t ∈ P, (box t).indicator (fun _ => F t) x := by
    intro x
    by_cases h0 : F x = 0
    · rw [h0]; symm
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases hx : x ∈ box t
      · rw [Set.indicator_of_mem hx, hshift x t hx, h0]
      · rw [Set.indicator_of_notMem hx]
    · have hbig := hF x h0
      have hex := fun i => hU (x i) (hbig i)
      choose s hs hsu using hex
      have hsP : s ∈ P := Fintype.mem_piFinset.2 fun i => (hs i).1
      have hxs : x ∈ box s := (hmemBox s x).2 fun i => (hs i).2
      rw [Finset.sum_eq_single s, Set.indicator_of_mem hxs, hshift x s hxs]
      · intro t htP hts
        rw [Set.indicator_of_notMem]
        intro hxt
        apply hts
        funext i
        exact hsu i (t i) ⟨Fintype.mem_piFinset.1 htP i, (hmemBox t x).1 hxt i⟩
      · intro h; exact absurd hsP h
  have hmeasS : ∀ t, MeasurableSet (S t) := fun t =>
    measurable_const_add (-t) (isOpen_cball u).measurableSet
  have hmeasBox : ∀ t, MeasurableSet (box t) := fun t => MeasurableSet.univ_pi fun i => hmeasS (t i)
  have hνS : ∀ t, ν (S t) = (distribHaarChar k u : ℝ≥0∞) := by
    intro t; simp only [S]; rw [measure_preimage_add, measure_cball, hν.2, mul_one]
  have hμbox : ∀ t, (Measure.pi fun _ : I => ν) (box t) = (distribHaarChar k u : ℝ≥0∞) ^ Fintype.card I := by
    intro t; simp only [box]; rw [Measure.pi_pi]; simp [hνS]
  have hnu : nabs k u = nabs k ϖ ^ B := by simp [u, nabs, map_pow]
  have hreal : ∀ t, (Measure.pi fun _ : I => ν).real (box t) = ((resCard k : ℝ)⁻¹ ^ B) ^ Fintype.card I := by
    intro t
    rw [Measure.real, hμbox, ENNReal.toReal_pow, ENNReal.coe_toReal, ← hnabs, ← hnu]
    rfl
  calc ∫ x, F x ∂(Measure.pi fun _ : I => ν)
        = ∫ x, ∑ t ∈ P, (box t).indicator (fun _ => F t) x ∂(Measure.pi fun _ : I => ν) := by
          congr 1; funext x; exact hdec x
    _ = ∑ t ∈ P, ∫ x, (box t).indicator (fun _ => F t) x ∂(Measure.pi fun _ : I => ν) := by
          refine integral_finsetSum P fun t _ => ?_
          refine IntegrableOn.integrable_indicator ?_ (hmeasBox t)
          exact integrableOn_const (by rw [hμbox]; simp)
    _ = ∑ t ∈ P, (Measure.pi fun _ : I => ν).real (box t) • F t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          exact integral_indicator_const (F t) (hmeasBox t)
    _ = _ := by
          simp only [hreal, Complex.real_smul, ← Finset.mul_sum]
          push_cast
          rw [inv_pow]

end GlobalTheory.PeriodicIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralPeriodicCompactSupportEqFiniteSumStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_periodic_compactSupport_eq_finiteSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (A B : ℕ) (T : Finset k), (∀ t ∈ T, valuation k t ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x : k, valuation k x ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) → ∃! t, t ∈ T ∧ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B)) → ∀ (I : Type) [Fintype I] [DecidableEq I] (F : (I → k) → ℂ), (∀ x, F x ≠ 0 → ∀ i, valuation k (x i) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x y, (∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) → F (x + y) = F x) → ∫ x, F x ∂(Measure.pi fun _ : I => ν) = (((resCard k : ℂ) ^ B)⁻¹) ^ Fintype.card I * ∑ t ∈ Fintype.piFinset (fun _ : I => T), F t := by
  first | exact @GlobalTheory.PeriodicIntegral.integral_eq_sum | exact GlobalTheory.PeriodicIntegral.integral_eq_sum | (intros; apply GlobalTheory.PeriodicIntegral.integral_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelCharacterByResidueCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelCharacterByResidueCharacter
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymResidue

theorem dsum_shift {R : Type} [AddCommMonoid R] (n : ℕ) (f : ℕ → ℕ → R) :
    (∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = (i : ℕ) + 1 then f i j else 0) =
      ∑ i ∈ Finset.range (n - 1), f i (i + 1) := by
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if (j : ℕ) = (i : ℕ) + 1 then f i j else 0) =
      if (i : ℕ) + 1 < n then f i ((i : ℕ) + 1) else 0 := by
    intro i
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = (i : ℕ) + 1 then f i j else 0) n]
    simp [Finset.sum_ite_eq', Finset.mem_range]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < n then f i (i + 1) else 0) n]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem intAt_sum {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (f : ℕ → E)
    (h : ∀ i < n, IntAt P (f i)) : IntAt P (∑ i ∈ Finset.range n, f i) := by
  refine Finset.sum_induction f (IntAt P) (fun a b ha hb => IntAt.add ha hb) ?_ ?_
  · simpa using IntAt.coe P 0
  · intro i hi
    exact h i (Finset.mem_range.mp hi)

end GlobalTheory.SymResidue

open GlobalTheory.SymResidue in
theorem GlobalTheory.symLevel_lam_residue : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + s + 1 → p' < κ + s + 1 → IntAt P (M p p')) → ∀ (g : S.P.J), (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b))) → ((S.P.lam g : ℂˣ) : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT M hM g hg
  have hent : ∀ a b, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val a b =
      ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b)) := by
    intro a b; rw [hg]; rfl
  set A : E := ∑ i ∈ Finset.range (κ - 1), M i (i + 1) with hA
  set B : E := ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1) with hB
  have hAi : IntAt P A := intAt_sum P _ _ (fun i hi => hM _ _ (by omega) (by omega))
  have hBi : IntAt P B := intAt_sum P _ _ (fun i hi => hM _ _ (by omega) (by omega))
  have hsimple : GlobalTheory.RootEx.simpleSum (g : GL (Fin κ ⊕ Fin (s + 1)) k) = ι B := by
    unfold GlobalTheory.RootEx.simpleSum
    simp only [hent, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dsum_shift (s + 1) (fun i j => ι (M (κ + i) (κ + j))), hB, map_sum]
    have : κ + s + 1 - κ - 1 = s + 1 - 1 := by omega
    rw [this]
    rfl
  have hsuper : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (g : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ = ι A := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hent, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos, Sum.elim_inl]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dsum_shift κ (fun i j => ι (M i j)), hA, map_sum]
  have hdiv : ∀ X : E, ((S.ϖ⁻¹ : kˣ) : k) * ι X = ι (X / (q : E)) := by
    intro X
    rw [Units.val_inv_eq_inv_val, hT.compl.unif, ← map_inv₀, ← map_mul, div_eq_inv_mul]
  rw [S.sym.2 g, hsimple, hsuper, hdiv, hdiv, hT.psi B hBi, hT.psi A hAi, ← map_mul,
    ← AddChar.map_add_eq_mul, ← reduction_add hBi hAi, add_comm B A]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelCharacterByResidueCharacterStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symLevel_character_by_residueCharacter : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + s + 1 → p' < κ + s + 1 → IntAt P (M p p')) → ∀ (g : S.P.J), (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) a) (GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ (s + 1) b))) → ((S.P.lam g : ℂˣ) : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  first | exact @GlobalTheory.symLevel_lam_residue | exact GlobalTheory.symLevel_lam_residue | (intros; apply GlobalTheory.symLevel_lam_residue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedLevelPatternToFramePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedLevelPatternToFramePlaces
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.PatPlaces

theorem zPos_surj {κ τ l j p : ℕ} (hp : p < κ + l + j * τ) :
    ∃ a : Ix (Fin κ ⊕ Fin l) (Fin τ) j, zPos a = p := by
  by_cases h1 : p < κ
  · exact ⟨.inl (.inl ⟨p, h1⟩), rfl⟩
  by_cases h2 : p < κ + l
  · exact ⟨.inl (.inr ⟨p - κ, by omega⟩), by simp only [zPos]; omega⟩
  · have hτ : 0 < τ := by
      rcases Nat.eq_zero_or_pos τ with h | h
      · subst h; simp at hp; omega
      · exact h
    have hq : p - (κ + l) < τ * j := by rw [mul_comm]; omega
    refine ⟨.inr (⟨(p - (κ + l)) / τ, Nat.div_lt_of_lt_mul hq⟩, ⟨(p - (κ + l)) % τ, Nat.mod_lt _ hτ⟩), ?_⟩
    have := Nat.div_add_mod' (p - (κ + l)) τ
    simp only [zPos]; omega

theorem symIdx_cases (κ ρ i : ℕ) :
    (i < κ ∧ symIdx κ ρ i = i + ρ) ∨ (κ ≤ i ∧ i < κ + ρ ∧ symIdx κ ρ i = i - κ) ∨ (κ + ρ ≤ i ∧ symIdx κ ρ i = i) := by
  unfold symIdx; split_ifs <;> omega

theorem block_div {r τ i u : ℕ} (hu : u < τ) : (r + i * τ + u - r) / τ = i := by
  have : r + i * τ + u - r = u + τ * i := by rw [mul_comm]; omega
  rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hu, zero_add]

theorem pattern_to_places (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F) :
    (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) →
    ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) := by
  intro hR
  have key : ∀ a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, a ≠ b → ¬ FreeIx ρ a b → R (zPos a) (zPos b) = 0 :=
    fun a b hab h => by rw [hR a b h, if_neg hab]
  refine ⟨fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h1 h2 h3 h4 => ?_⟩
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    rw [hR b b ?_, if_pos rfl]
    rcases b with (i | i) | ⟨i, u⟩
    · simp [FreeIx, FreeTop]
    · simp [FreeIx, FreeTop]
    · simp only [zPos] at hp'; omega
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    obtain ⟨a, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)
    refine key a b (fun h => hne (h ▸ rfl)) ?_
    have c1 := symIdx_cases κ ρ (zPos a)
    have c2 := symIdx_cases κ ρ (zPos b)
    rcases a with (i | i) | ⟨i, u⟩ <;> rcases b with (i' | i') | ⟨i', u'⟩ <;>
      simp only [zPos, FreeIx, FreeTop, Fin.lt_def, not_lt, not_false_eq_true] at hp' hp hne hc c1 c2 ⊢ <;> omega
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    obtain ⟨a, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)
    rcases b with (i' | i') | ⟨i', u'⟩
    · simp only [zPos] at h1; omega
    · simp only [zPos] at h1; omega
    rcases a with (i | i) | ⟨i, u⟩
    · simp only [zPos] at h4; rw [show (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)
    · simp only [zPos] at h4; rw [show κ + (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)
    have e1 : κ + (s + 1) + (i' : ℕ) * τ + u' = κ + s + 1 + (i' : ℕ) * τ + u' := by omega
    have e2 : κ + (s + 1) + (i : ℕ) * τ + u = κ + s + 1 + (i : ℕ) * τ + u := by omega
    simp only [zPos] at h4
    rw [e1, e2, block_div u'.isLt, block_div u.isLt] at h4
    refine key _ _ (fun h => ?_) ?_
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at h; rw [h.1] at h4; exact lt_irrefl _ h4
    · simp only [FreeIx, Fin.le_def, not_le]; exact h4

end GlobalTheory.PatPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedLevelPatternToFramePlacesStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedLevelPattern_to_framePlaces : ∀ (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F), (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) → ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) := by
  first | exact @GlobalTheory.PatPlaces.pattern_to_places | exact GlobalTheory.PatPlaces.pattern_to_places | (intros; apply GlobalTheory.PatPlaces.pattern_to_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAddChar
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.SymTieExists
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] {F : Type} [CommRing F]

end Local

section Res
variable {E k : Type} [Field E] [NumberField E]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reduction_spec (P : HeightOneSpectrum (𝓞 E)) {a : E} (h : IntAt P a) :
    ∃ r, ∃ s ∉ P.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  obtain ⟨r, s, hs, e⟩ := h
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs' : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hex : ∃ c r, ∃ s ∉ P.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨(Ideal.Quotient.mk P.asIdeal s)⁻¹ * Ideal.Quotient.mk P.asIdeal r, r, s, hs, e, mul_inv_cancel_left₀ hs' _⟩
  unfold redP
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem exists_residue (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k) (hint : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a)
    (hd : DenseRange ι) :
    ∃ r : 𝒪[k] →+* 𝓞 E ⧸ P.asIdeal, Function.Surjective r ∧ (∀ x : 𝒪[k], r x = 0 ↔ valuation k (x : k) < 1) ∧
      ∀ a (h : ι a ∈ 𝒪[k]), r ⟨ι a, h⟩ = redP P a := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hlt : ∀ y : 𝒪[k], IsLocalRing.residue 𝒪[k] y = 0 ↔ valuation k (y : k) < 1 := fun y => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  let j : 𝓞 E →+* 𝒪[k] := (ι.comp (algebraMap (𝓞 E) E)).codRestrict _ fun r =>
    (hint _).2 ⟨r, 1, h1, by simp⟩
  have hj : ∀ r, (j r : k) = ι (algebraMap (𝓞 E) E r) := fun _ => rfl
  let φ : 𝓞 E →+* 𝓀[k] := (IsLocalRing.residue 𝒪[k]).comp j
  have hker : ∀ r ∈ P.asIdeal, φ r = 0 := by
    intro r hr
    refine (hlt _).2 ?_
    by_contra hlt'
    have hv : valuation k (j r : k) = 1 :=
      le_antisymm ((Valuation.mem_integer_iff _ _).1 (j r).2) (not_lt.1 hlt')
    have hr0 : algebraMap (𝓞 E) E r ≠ 0 := by
      intro h
      rw [hj, h] at hv
      simp at hv
    obtain ⟨t, s, hs, e⟩ := (hint (algebraMap (𝓞 E) E r)⁻¹).1 (by
      rw [Valuation.mem_integer_iff, map_inv₀, map_inv₀, ← hj, hv, inv_one])
    apply hs
    have : s = t * r := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [map_mul, ← e, inv_mul_cancel_right₀ hr0]
    rw [this]
    exact Ideal.mul_mem_left _ _ hr
  let φ' : 𝓞 E ⧸ P.asIdeal →+* 𝓀[k] := Ideal.Quotient.lift _ φ hker
  have hφ' : ∀ r, φ' (Ideal.Quotient.mk _ r) = IsLocalRing.residue 𝒪[k] (j r) := fun _ => rfl
  have hred : ∀ a (h : ι a ∈ 𝒪[k]), φ' (redP P a) = IsLocalRing.residue 𝒪[k] ⟨ι a, h⟩ := by
    intro a h
    obtain ⟨r, s, hs, e, e'⟩ := reduction_spec P ((hint a).1 h)
    have hs' : φ' (Ideal.Quotient.mk P.asIdeal s) ≠ 0 := by
      rwa [map_ne_zero, Ne, Ideal.Quotient.eq_zero_iff_mem]
    apply mul_left_cancel₀ hs'
    rw [← map_mul, e', hφ', hφ', ← map_mul]
    congr 1
    apply Subtype.ext
    change ι (algebraMap (𝓞 E) E r) = ι (algebraMap (𝓞 E) E s) * ι a
    rw [← map_mul, e]
  have hsurj : Function.Surjective φ' := by
    intro t
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective t
    have hn : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
      rw [IsValuativeTopology.mem_nhds_iff']
      exact ⟨1, by simp⟩
    obtain ⟨a, ha⟩ := hd.mem_nhds hn
    have ha' : valuation k (ι a - x) < 1 := ha
    have hm : ι a ∈ 𝒪[k] := by
      have := add_mem ((Valuation.mem_integer_iff _ _).2 ha'.le) x.2
      simpa using this
    refine ⟨redP P a, ?_⟩
    rw [hred a hm, ← sub_eq_zero, ← map_sub]
    exact (hlt _).2 ha'
  let e := RingEquiv.ofBijective φ' ⟨φ'.injective, hsurj⟩
  refine ⟨e.symm.toRingHom.comp (IsLocalRing.residue 𝒪[k]), e.symm.surjective.comp IsLocalRing.residue_surjective,
    fun x => ?_, fun a h => ?_⟩
  · rw [← hlt]
    exact map_eq_zero_iff _ e.symm.injective
  · change e.symm _ = _
    rw [RingEquiv.symm_apply_eq]
    exact (hred a h).symm

end Res

end GlobalTheory.SymTieExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionChainLatticeEntriesAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionChainLatticeEntriesAgree
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.EntryBases

section Frames
variable {k : Type*} [Field k] {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

def ordExp : n ⊕ Fin c → ℤ := Sum.elim (fun _ => 0) (fun i => (i.val : ℤ) + 1)

theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (fun y : n ⊕ Fin c => (ϖ : k) ^ ordExp y) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, GlobalTheory.SplitFlip.diagGL, ordExp, diagonal, fromBlocks, Matrix.one_apply]
  split_ifs <;> simp [← zpow_natCast]

theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val = diagonal (fun y : n ⊕ Fin c => (ϖ : k) ^ (-ordExp y)) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, GlobalTheory.SplitFlip.diagGL, ordExp, diagonal, fromBlocks, Matrix.one_apply]
  split_ifs <;> simp [← zpow_natCast]

theorem typeFrame_coords_apply (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (ord' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ ord).coords (typeFrame ϖ ord') x a b =
      (ϖ : k) ^ (ordExp (ord' b) - ordExp (ord a)) * x (ord a) (ord' b) := by
  simp only [LatFrame.coords, typeFrame_bas_val, typeFrame_bas_inv_val, submatrix_apply, diagonal_mul, mul_diagonal]
  dsimp only [typeFrame]
  rw [sub_eq_add_neg, zpow_add₀ (Units.ne_zero ϖ)]
  ring

end Frames

section Index

theorem fIdx_of_lt {κ c n v : ℕ} (h : v < κ) : LocE.fIdx κ c n v = v := by
  unfold LocE.fIdx; rw [if_pos h]

theorem fIdx_of_mid {κ c n v : ℕ} (h₁ : κ ≤ v) (h₂ : v < κ + c) : LocE.fIdx κ c n v = n + (v - κ) := by
  unfold LocE.fIdx; rw [if_neg (by omega), if_pos h₂]

theorem fIdx_of_ge {κ c n v : ℕ} (h : κ + c ≤ v) : LocE.fIdx κ c n v = v - c := by
  unfold LocE.fIdx; rw [if_neg (by omega), if_neg (by omega)]

theorem scE_of_lt {n v : ℕ} (ex : ℕ → ℕ) (h : v < n) : LocE.scE n ex v = 0 := by
  unfold LocE.scE; rw [if_pos h]

theorem scE_add (n i : ℕ) (ex : ℕ → ℕ) : LocE.scE n ex (n + i) = ex i := by
  unfold LocE.scE; rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem stdOrd_place {κ τ j c l n N : ℕ} (h : j + c = l) (hn : n = κ + j * (τ + 1))
    (e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin N) (he : IsOrd (yPos xPos n) e) (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) :
    (e (stdOrd (Fin κ) (Fin τ) j c h a)).val = LocE.fIdx κ c n (zPos a) ∧
      ordExp (stdOrd (Fin κ) (Fin τ) j c h a) = LocE.scE n (fun i => i + 1) (LocE.fIdx κ c n (zPos a)) := by
  have hn' : n = κ + j * τ + j := by rw [hn]; ring
  rcases a with (i | ⟨i, hi⟩) | p
  · rw [stdOrd_eps, he]
    have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inl i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = i.val := rfl
    rw [hz, fIdx_of_lt i.isLt, scE_of_lt _ (by omega)]
    exact ⟨rfl, rfl⟩
  · by_cases hic : i < c
    · have hs : stdOrd (Fin κ) (Fin τ) j c h (.inl (.inr ⟨i, hi⟩)) = .inr ⟨i, hic⟩ := standardOrderExtendedBasis_apply_low_block (Fin κ) (Fin τ) j c h ⟨i, hic⟩
      rw [hs, he]
      have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inr ⟨i, hi⟩) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + i := rfl
      rw [hz, fIdx_of_mid (by omega) (by omega), Nat.add_sub_cancel_left, scE_add]
      exact ⟨rfl, by simp [ordExp]⟩
    · obtain ⟨m, rfl⟩ : ∃ m, i = c + m := ⟨i - c, by omega⟩
      have hs : stdOrd (Fin κ) (Fin τ) j c h (.inl (.inr ⟨c + m, hi⟩)) = .inl (.inl (.inr ⟨m, by omega⟩)) :=
        stdOrd_f (Fin κ) (Fin τ) j c h ⟨m, by omega⟩
      rw [hs, he]
      have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inr ⟨c + m, hi⟩) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + (c + m) := rfl
      rw [hz, fIdx_of_ge (by omega), scE_of_lt _ (by omega)]
      exact ⟨by simp [yPos, xPos]; omega, rfl⟩
  · rw [stdOrd_d, he]
    have hp : p.1.val * τ + p.2.val < j * τ := by
      have h1 : p.1.val * τ + p.2.val < (p.1.val + 1) * τ := by rw [add_mul, one_mul]; omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right τ p.1.isLt)
    have hz : zPos (κ := κ) (τ := τ) (j := j) (.inr p : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + l + p.1.val * τ + p.2.val := rfl
    rw [hz, fIdx_of_ge (by omega), scE_of_lt _ (by omega)]
    exact ⟨by simp [yPos, xPos]; omega, rfl⟩

end Index

section Main
variable {E k : Type} [Field E] [Field k]

theorem atN_val {N : ℕ} (v : Fin N → E) (i : Fin N) : Loc.atN v i.val = v i := by
  unfold Loc.atN; rw [dite_eq_left i.isLt]

theorem eN_val {N : ℕ} (i : Fin N) : Loc.eN E N i.val = Pi.single i 1 := by
  funext l; unfold Loc.eN; rw [Pi.single_apply]; simp [Fin.ext_iff]

theorem typeFrame_coords_toLoc (ι : E →+* k) (q : ℕ) (ϖ : kˣ) (hϖ : (ϖ : k) = ι (q : E))
    {κ τ l j c j' c' n N n' N' : ℕ} (h : j + c = l) (h' : j' + c' = l) (hn : n = κ + j * (τ + 1)) (hn' : n' = κ + j' * (τ + 1))
    (e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin N) (e' : XIx (Fin κ) (Fin τ) j' ⊕ Fin c' ≃ Fin N')
    (he : IsOrd (yPos xPos n) e) (he' : IsOrd (yPos xPos n') e') (x : (Fin N' → E) →ₗ[E] (Fin N → E))
    (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) (b : Ix (Fin κ ⊕ Fin l) (Fin τ) j') :
    (typeFrame ϖ (stdOrd (Fin κ) (Fin τ) j c h)).coords (typeFrame ϖ (stdOrd (Fin κ) (Fin τ) j' c' h')) (toLoc ι e e' x) a b =
      ι (LocE.entB q κ c' n' c n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  rw [map_natCast] at hϖ
  rw [typeFrame_coords_apply]
  obtain ⟨ha1, ha2⟩ := stdOrd_place h hn e he a
  obtain ⟨hb1, hb2⟩ := stdOrd_place h' hn' e' he' b
  simp only [LocE.entB, toLoc]
  rw [← ha2, ← hb2, ← ha1, ← hb1, eN_val, atN_val, map_mul, map_zpow₀, map_natCast, ← hϖ]
  ring

end Main

theorem entries_agree : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (τ j c : ℕ) (h : j + c = s) (n' c' n c₂ : ℕ), n' = κ + j * (τ + 1) → n = κ + (j + 1) * (τ + 1) → c' = c + 1 → c₂ = c → ∀ (e' : XIx (Fin κ) (Fin τ) j ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : XIx (Fin κ) (Fin τ) (j + 1) ⊕ Fin c ≃ Fin (n + c₂)), IsOrd (yPos xPos n') e' → IsOrd (yPos xPos n) e → ∀ (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c₂) → E)) (a : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (j + 1) c (by omega))).coords (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) j (c + 1) (by omega))) (toLoc ι e e' x) a b = ι (LocE.entB q κ c' n' c₂ n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT τ j c h n' c' n c₂ hn' hn hc' hc₂ e' e he' he x a b
  subst hc' hc₂
  exact typeFrame_coords_toLoc ι q S.ϖ hT.compl.unif _ _ hn hn' e e' he he' x a b

end GlobalTheory.SymBridge.EntryBases
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionChainLatticeEntriesAgreeStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completionChain_lattice_entries_agree : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (τ j c : ℕ) (h : j + c = s) (n' c' n c₂ : ℕ), n' = κ + j * (τ + 1) → n = κ + (j + 1) * (τ + 1) → c' = c + 1 → c₂ = c → ∀ (e' : XIx (Fin κ) (Fin τ) j ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : XIx (Fin κ) (Fin τ) (j + 1) ⊕ Fin c ≃ Fin (n + c₂)), IsOrd (yPos xPos n') e' → IsOrd (yPos xPos n) e → ∀ (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c₂) → E)) (a : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (j + 1) c (by omega))).coords (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) j (c + 1) (by omega))) (toLoc ι e e' x) a b = ι (LocE.entB q κ c' n' c₂ n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  first | exact @GlobalTheory.SymBridge.EntryBases.entries_agree | exact GlobalTheory.SymBridge.EntryBases.entries_agree | (intros; apply GlobalTheory.SymBridge.EntryBases.entries_agree <;> assumption)
end
end
