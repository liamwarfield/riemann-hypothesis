module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeNotJointShapeSmallerPairs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

noncomputable section

namespace GlobalTheory.CoverKGen

open GlobalTheory.RealPar GlobalTheory.RealPar.KStabLie GlobalTheory.RealPar.TorusWt Matrix

variable {p q : ℕ}

theorem blockOrd_std (p q : ℕ) :
    BlockOrd (p := p) (q := q) finSumFinEquiv (fun i => (finSumFinEquiv.symm i).isLeft) := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · have hlt : a < b := hab
    simp only [finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd]
    exact Fin.lt_def.mp hlt
  · simp [posC] at hab
  · simp [posC] at hab
  · have hlt : a < b := hab
    have := Fin.lt_def.mp hlt
    simp only [finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd]
    omega

theorem exists_log (T : GrpData p q) {k : T.G} (hk : k ∈ T.Kset) :
    ∃ X, X ∈ upq p q ∧ IsKC X ∧ T.cov (T.expt X) = T.cov k := by
  have hB := blockOrd_std p q
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exponential_surjective _ _ _ (mem_Kset hB T hk)
  letI : NormedRing (Mat p q) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Mat p q) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Mat p q) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Mat p q) := FiniteDimensional.complete ℂ (Mat p q)
  letI : NormedRing (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℚ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) := Matrix.linftyOpNormedSpace
  letI : CompleteSpace (Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :=
    FiniteDimensional.complete ℂ (Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := p) (n := q))
  have hφc : Continuous φ := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact continuous_id.matrix_reindex _ _
  have hφX : φ (φ.symm Y) = Y := φ.apply_symm_apply Y
  have hJ : φ (Jm p q) = Formalism.REAL.Jm (fun i => (finSumFinEquiv.symm i).isLeft) := by
    rw [Matrix.coe_reindexAlgEquiv]
    exact hB.reindex_Jm
  have hstar : ∀ M : Mat p q, φ Mᴴ = (φ M)ᴴ := fun M =>
    (Matrix.conjTranspose_reindex _ _ M).symm
  have hX : φ.symm Y ∈ upq p q := by
    show (φ.symm Y)ᴴ * Jm p q + Jm p q * φ.symm Y = 0
    apply φ.injective
    rw [map_add (f := _), map_mul, map_mul, hstar, hJ, hφX, map_zero]
    exact hY.1
  refine ⟨φ.symm Y, hX, ?_, ?_⟩
  · rw [isKC_iff]
    apply φ.injective
    rw [map_mul, map_mul, hJ, hφX]
    exact hY.2
  · apply Units.ext
    rw [T.expt_cov _ hX]
    apply φ.injective
    have hm : φ (NormedSpace.exp (φ.symm Y)) = NormedSpace.exp (φ (φ.symm Y)) :=
      NormedSpace.map_exp φ hφc _
    rw [hm, hφX, hexp]
    rfl

theorem torX_isKC (θ : Ix p q → ℝ) : IsKC (torX θ) := by
  intro a b hab
  have hne : a ≠ b := by
    rintro rfl
    exact hab (by cases a <;> trivial)
  simp [torX, Matrix.diagonal_apply_ne _ hne]

theorem cov_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.cov (T.expt (torX θ)) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
  rw [T.expt_cov _ (torX_mem θ)]
  unfold torX
  rw [Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]

private theorem sq_expt_torX_sq_eq_exp (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) ^ 2 =
      Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) ^ 2 := by
  rw [T.sq_sq, cov_expt_torX, Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_nat_mul]
  congr 1
  rw [← Finset.sum_mul]
  push_cast
  ring

theorem sq_expt_torX (T : GrpData p q) (θ : Ix p q → ℝ) :
    ((T.sq (T.expt (torX θ)) : ℂˣ) : ℂ) = Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) := by
  let f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • torX θ)) : ℂˣ) : ℂ)
  let g : ℝ → ℂ := fun t => Complex.exp ((∑ a, ((t * θ a : ℝ) : ℂ)) * Complex.I / 2)
  have hsq : ∀ t, f t ^ 2 = g t ^ 2 := fun t => by
    simp only [f, g]
    rw [smul_torX]
    exact sq_expt_torX_sq_eq_exp T _
  have hg : ∀ t, g t ≠ 0 := fun t => Complex.exp_ne_zero _
  have hfc : Continuous f := by
    have h1 : Continuous fun t : ℝ => T.expt (t • torX θ) :=
      T.expt_cont.comp_continuous (continuous_id.smul continuous_const)
        (fun t => smul_mem_upq (torX_mem θ) t)
    have h2 : Continuous fun x : T.G => T.sq x := continuous_snd.comp T.emb.continuous
    exact Units.continuous_val.comp (h2.comp h1)
  have hgc : Continuous g := by fun_prop
  have hh : ∀ t, f t / g t = 1 ∨ f t / g t = -1 := fun t => by
    have h2 : (f t / g t) ^ 2 = 1 := by
      rw [div_pow, hsq t, div_self (pow_ne_zero 2 (hg t))]
    exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
  have h0 : f 0 / g 0 = 1 := by
    simp [f, g, T.expt_zero]
  have hcont : Continuous fun t => f t / g t := hfc.div hgc hg
  have h1 : f 1 / g 1 = 1 := by
    rcases hh 1 with h1 | h1
    · exact h1
    exfalso
    have hre : Continuous fun t => (f t / g t).re := Complex.continuous_re.comp hcont
    have hmem : (0 : ℝ) ∈ Set.Icc ((f 1 / g 1).re) ((f 0 / g 0).re) := by
      rw [h0, h1]
      norm_num
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' zero_le_one hre.continuousOn hmem
    rcases hh t with h2 | h2 <;> simp only [h2] at ht <;> norm_num at ht
  have hfg : f 1 = g 1 := (div_eq_one_iff_eq (hg 1)).mp h1
  simpa [f, g] using hfg

theorem kset_gen : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q), ∀ k ∈ T.Kset,
    k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) := by
  intro p q hpq T k hk
  have mem : ∀ X, X ∈ upq p q → IsKC X →
      T.expt X ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) :=
    fun X h1 h2 => Subgroup.subset_closure ⟨X, ⟨h1, h2⟩, rfl⟩
  obtain ⟨a0⟩ : Nonempty (Ix p q) := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
    · exact ⟨Sum.inl ⟨0, hp⟩⟩
  have hc := mem _ (torX_mem (Pi.single a0 (2 * Real.pi))) (torX_isKC (Pi.single a0 (2 * Real.pi)))
  have hcov : T.cov (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = 1 := by
    apply Units.ext
    rw [cov_expt_torX, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext a
    by_cases ha : a = a0
    · subst ha
      simp only [Pi.single_eq_same]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [Pi.single_eq_of_ne ha]
  have hsqc : T.sq (T.expt (torX (Pi.single a0 (2 * Real.pi)))) = -1 := by
    apply Units.ext
    rw [sq_expt_torX]
    have hs : (∑ a, (((Pi.single a0 (2 * Real.pi) : Ix p q → ℝ) a : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) := by
      rw [Finset.sum_eq_single a0 (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp
    have hpi : 2 * (Real.pi : ℂ) * Complex.I / 2 = Real.pi * Complex.I := by ring
    rw [hs, hpi, Complex.exp_pi_mul_I]
    simp
  obtain ⟨X, hX, hXK, hcovX⟩ := exists_log T hk
  have hy := mem X hX hXK
  have huniq : ∀ x : T.G, T.cov x = T.cov k → T.sq x = T.sq k → x = k := fun x h1 h2 =>
    (T.bij (T.cov k) (T.cov_mem k) (T.sq k) (T.sq_sq k)).unique ⟨h1, h2⟩ ⟨rfl, rfl⟩
  have hsq2 : ((T.sq (T.expt X) : ℂˣ) : ℂ) ^ 2 = ((T.sq k : ℂˣ) : ℂ) ^ 2 := by
    rw [T.sq_sq, T.sq_sq, hcovX]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h | h
  · rw [← huniq _ hcovX (Units.ext h)]
    exact hy
  · have hk' : T.expt X * T.expt (torX (Pi.single a0 (2 * Real.pi))) = k := by
      apply huniq
      · rw [map_mul, hcov, mul_one, hcovX]
      · apply Units.ext
        rw [map_mul, hsqc]
        simp [h]
    rw [← hk']
    exact Subgroup.mul_mem _ hy hc

end GlobalTheory.CoverKGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExpStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoverUpq_Kset_generated_by_exp : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q), ∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y}) := by
  first | exact @GlobalTheory.CoverKGen.kset_gen | exact GlobalTheory.CoverKGen.kset_gen | (intros; apply GlobalTheory.CoverKGen.kset_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompat
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.RealPar

theorem flow_pair_mem_range {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : E →ₗ[ℂ] H₁) (j₂ : E →ₗ[ℂ] H₂) (a : E →ₗ[ℂ] E)
    (U₁ : ℝ → H₁ →L[ℂ] H₁) (U₂ : ℝ → H₂ →L[ℂ] H₂) (h₁ : U₁ 0 = 1) (h₂ : U₂ 0 = 1)
    (a₁ : ∀ s t, U₁ (s + t) = U₁ s * U₁ t) (a₂ : ∀ s t, U₂ (s + t) = U₂ s * U₂ t)
    (d₁ : ∀ v, HasDerivAt (fun t : ℝ => U₁ t (j₁ v)) (j₁ (a v)) 0)
    (d₂ : ∀ v, HasDerivAt (fun t : ℝ => U₂ t (j₂ v)) (j₂ (a v)) 0) (t : ℝ) (w : E) :
    ∃ w' : E, U₁ t (j₁ w) = j₁ w' ∧ U₂ t (j₂ w) = j₂ w' := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂
  let ι : E →ₗ[ℂ] WithLp 2 (H₁ × H₂) := e.symm.toLinearEquiv.toLinearMap ∘ₗ j₁.prod j₂
  let U : ℝ → WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) := fun s =>
    (e.symm : H₁ × H₂ →L[ℂ] WithLp 2 (H₁ × H₂)) ∘L ((U₁ s).prodMap (U₂ s)) ∘L
      (e : WithLp 2 (H₁ × H₂) →L[ℂ] H₁ × H₂)
  have hU : ∀ s x, U s x = e.symm (U₁ s (e x).1, U₂ s (e x).2) := fun s x => rfl
  have hι : ∀ v, ι v = e.symm (j₁ v, j₂ v) := fun v => rfl
  have key := flow_mem_map ι a ⊤ (fun _ _ => trivial) U
    (by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [hU, h₁, h₂]
      exact e.symm_apply_apply x)
    (fun s r => by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [ContinuousLinearMap.mul_apply, hU, hU, hU, a₁, a₂, e.apply_symm_apply]
      rfl)
    (fun v => by
      have h := ((e.symm : H₁ × H₂ →L[ℂ] WithLp 2 (H₁ × H₂)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) ((d₁ v).prodMk (d₂ v))
      exact h) t (ι w) ⟨w, trivial, rfl⟩
  obtain ⟨w', -, hw'⟩ := key
  rw [hU, hι, hι, e.apply_symm_apply] at hw'
  have h := e.symm.injective hw'
  exact ⟨w', (congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

theorem pair_kEquivariant_of_lie : ∀ (p q : ℕ) (T : GrpData p q), (∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y})) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (a : Mat p q → E →ₗ[ℂ] E) (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, IsKC Y → ∀ w, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ w)) (j₁ (a Y w)) 0 ∧ HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ w)) (j₂ (a Y w)) 0) → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') := by
  intro p q T hgen π₁ π₂ E _ _ _ a j₁ j₂ hder k hk
  have hflow : ∀ Y ∈ upq p q, IsKC Y → ∀ (t : ℝ) (w : E), ∃ w' : E,
      π₁.π (T.expt (t • Y)) (j₁ w) = j₁ w' ∧ π₂.π (T.expt (t • Y)) (j₂ w) = j₂ w' := by
    intro Y hY hK t w
    exact flow_pair_mem_range j₁ j₂ (a Y) (fun t => π₁.π (T.expt (t • Y))) (fun t => π₂.π (T.expt (t • Y)))
      (by simp [T.expt_zero]) (by simp [T.expt_zero])
      (fun s t => by simp only [T.expt_add Y hY, map_mul])
      (fun s t => by simp only [T.expt_add Y hY, map_mul])
      (fun v => (hder Y hY hK v).1) (fun v => (hder Y hY hK v).2) t w
  refine Subgroup.closure_induction'' (p := fun k _ => ∀ w : E, ∃ w' : E,
    π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') ?_ ?_ ?_ ?_ (hgen k hk)
  · rintro _ ⟨Y, ⟨hY, hK⟩, rfl⟩ w
    simpa using hflow Y hY hK 1 w
  · rintro _ ⟨Y, ⟨hY, hK⟩, rfl⟩ w
    have h : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have := T.expt_add Y hY (-1) 1
      rw [neg_add_cancel, zero_smul, one_smul, T.expt_zero] at this
      exact (eq_inv_of_mul_eq_one_left this.symm).symm
    rw [h]
    exact hflow Y hY hK (-1) w
  · intro w
    exact ⟨w, by simp, by simp⟩
  · intro x y _ _ hx hy w
    obtain ⟨w', h1, h2⟩ := hy w
    obtain ⟨w'', h3, h4⟩ := hx w'
    exact ⟨w'', by rw [map_mul, ContinuousLinearMap.mul_apply, h1, h3],
      by rw [map_mul, ContinuousLinearMap.mul_apply, h2, h4]⟩

end GlobalTheory.RealPar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompatStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_kEquivariant_of_lieAlgebra_compat : ∀ (p q : ℕ) (T : GrpData p q), (∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y})) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (a : Mat p q → E →ₗ[ℂ] E) (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, IsKC Y → ∀ w, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ w)) (j₁ (a Y w)) 0 ∧ HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ w)) (j₂ (a Y w)) 0) → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') := by
  first | exact @GlobalTheory.RealPar.pair_kEquivariant_of_lie | exact GlobalTheory.RealPar.pair_kEquivariant_of_lie | (intros; apply GlobalTheory.RealPar.pair_kEquivariant_of_lie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeries
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.SmallerSource

theorem discrete_series_gk_admissible_irreducible (X : ProvA) (h5 : admQ5 X) {r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) :
    AdmGK (X.ds r s lam).HK ∧ IrrGK (X.ds r s lam).HK := by
  obtain ⟨hU, -, -⟩ := h5 r s hrs
  set D := X.ds r s lam
  exact (hU D.U ⟨D.nontriv, D.irred⟩).2.2 D.HK D.ι ⟨D.ι_inj, D.ι_range, D.der⟩

theorem cPair_sub {p q i : ℕ} (hp : i ≤ p) (hq : i ≤ q) : cPair (p - i) (q - i) = cPair p q := by
  unfold cPair
  rw [Nat.cast_sub hp, Nat.cast_sub hq]
  ring

theorem intw_eq_zero (X : ProvA) (h2 : admH2 X) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam))
    (MM : GKMod p q) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam).HK.V)
    (hf : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK f) : f = 0 := by
  by_contra hf0

  have hAI := discrete_series_gk_admissible_irreducible X h5 hrs lam
  have hI : Intw MM (X.ds r s lam).HK f := (isIntw_iff (X.fock p q r s) MM _ f).1 hf
  obtain ⟨hfin, -, hcone⟩ := hD r s lam hlam

  have hex : ∃ v, IsHW (X.ds r s lam).HK.act (blattner lam) v := by
    have hne : hwSub (X.ds r s lam).HK.act (blattner lam) ≠ ⊥ := by
      intro h
      rw [h] at hfin
      simp at hfin
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨v, hv0, hv⟩

  have hmin : ∀ ν w, IsHW (X.ds r s lam).HK.act ν w →
      degW (cPair p q) (blattner lam) ≤ degW (cPair p q) ν :=
    GlobalTheory.T.degW_blattner_le_of_blattnerCone r s (X.ds r s lam).HK lam (cPair p q) θ hcone hsign

  obtain ⟨⟨μ, P, hPJ, hP1, hP2, hfP⟩, -⟩ :=
    GlobalTheory.T.fock_minimal_KType_second_member p q r s MM (X.ds r s lam).HK f hAI.2 hAI.1 hI hf0 (blattner lam) hex hmin

  have hbot := ((h2 p q r s).2.2.2.2.1 μ (blattner lam)).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 μ ⊓ hwSub (X.fock p q r s).act2 (blattner lam) ⊓
      Submodule.span ℂ (X.fock p q r s).J := by
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hP1.2, hP2.2⟩, ?_⟩
    rw [J_eq (X.fock p q r s)]
    exact Submodule.subset_span hPJ
  rw [hbot] at hmem
  exact hP1.1 ((Submodule.mem_bot ℂ).1 hmem)

theorem no_map_smaller_source :
    ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  intro X _ h2 hD h5
  unfold ArchimedeanRallisFifth ARv DataAR DataARm
  constructor
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, -, hlam', -, hs'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).1
    refine intw_eq_zero X h2 hD h5 (by omega) (lamA' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'
  ·
    intro t al be ga de hd hne i hi1 hip hiq MM f hf
    have hA := hd.1
    have ht : 1 ≤ t := by
      unfold HypA at hA
      exact hA.1
    obtain ⟨-, hlam', -, hs'⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
    have hno := ((GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi1).2.2 hne hip hiq).2
    refine intw_eq_zero X h2 hD h5 (by omega) (lamM' t al be ga de) hlam' ((t : ℚ) / 2) ?_ hno MM f hf
    rw [cPair_sub hip hiq]
    exact hs'

end GlobalTheory.SmallerSource
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoIntertwinerSmallerFockToDiscreteSeriesStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_intertwiner_smaller_fock_to_discrete_series : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.SmallerSource.no_map_smaller_source | exact GlobalTheory.SmallerSource.no_map_smaller_source | (intros; apply GlobalTheory.SmallerSource.no_map_smaller_source <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobBdSeminorm
noncomputable section

open Formalism.L2.Theta Formalism.MainNotions.S GlobalTheory.SmoothGlob

namespace GlobalTheory.FactorExtension

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sobNorm_nonneg (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (w : H) : 0 ≤ sobNorm σ S w :=
  List.sum_nonneg fun x hx => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _

theorem sobNorm_append (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' : List (List (Matrix (Fin n) (Fin n) ℂ)))
    (w : H) : sobNorm σ (S ++ S') w = sobNorm σ S w + sobNorm σ S' w := by
  simp [sobNorm, List.map_append, List.sum_append]

theorem sob_max {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S S' : List (List (Matrix (Fin n) (Fin n) ℂ))}
    {C C' a a' : ℝ} {w : H} (h : a ≤ C * sobNorm σ S w) (h' : a' ≤ C' * sobNorm σ S' w) :
    a + a' ≤ max |C| |C'| * sobNorm σ (S ++ S') w ∧ max a a' ≤ max |C| |C'| * sobNorm σ (S ++ S') w := by
  have h0 := sobNorm_nonneg σ S w
  have h0' := sobNorm_nonneg σ S' w
  have e1 : C * sobNorm σ S w ≤ max |C| |C'| * sobNorm σ S w :=
    mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_max_left _ _)) h0
  have e2 : C' * sobNorm σ S' w ≤ max |C| |C'| * sobNorm σ S' w :=
    mul_le_mul_of_nonneg_right ((le_abs_self C').trans (le_max_right _ _)) h0'
  have hm : 0 ≤ max |C| |C'| := (abs_nonneg C).trans (le_max_left _ _)
  rw [sobNorm_append, mul_add]
  refine ⟨by linarith, max_le ?_ ?_⟩
  · nlinarith [mul_nonneg hm h0']
  · nlinarith [mul_nonneg hm h0]

variable {E : Type} [AddCommGroup E] [Module ℂ E]

def sobBd (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : ℕ → Seminorm ℂ E) :
    Submodule ℂ (H →ₗ[ℂ] E) where
  carrier := {L | ∀ i, ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧
      ∀ w, SmoothVec (lieSet ε) σ w → p i (L w) ≤ C * sobNorm σ S w}
  zero_mem' := fun i => ⟨[], 0, by simp, fun w _ => by simp⟩
  add_mem' := by
    intro L L' hL hL' i
    obtain ⟨S, C, hS, h⟩ := hL i
    obtain ⟨S', C', hS', h'⟩ := hL' i
    refine ⟨S ++ S', max |C| |C'|, fun l hl => ?_, fun w hw => ?_⟩
    · rcases List.mem_append.1 hl with hl | hl
      · exact hS l hl
      · exact hS' l hl
    · exact (map_add_le_add (p i) _ _).trans (sob_max (h w hw) (h' w hw)).1
  smul_mem' := by
    intro c L hL i
    obtain ⟨S, C, hS, h⟩ := hL i
    refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
    rw [LinearMap.smul_apply, map_smul_eq_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h w hw) (norm_nonneg c)

theorem sobBd_congr {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : ℕ → Seminorm ℂ E}
    {L L' : H →ₗ[ℂ] E} (hL : L ∈ sobBd ε σ p) (h : ∀ w, SmoothVec (lieSet ε) σ w → L' w = L w) :
    L' ∈ sobBd ε σ p := fun i => by
  obtain ⟨S, C, hS, hb⟩ := hL i
  exact ⟨S, C, hS, fun w hw => by rw [h w hw]; exact hb w hw⟩

theorem sobBd_seminorm [TopologicalSpace E] {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) {L : H →ₗ[ℂ] E} (hL : L ∈ sobBd ε σ p) (q : Seminorm ℂ E)
    (hq : Continuous q) : ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧
      ∀ w, SmoothVec (lieSet ε) σ w → q (L w) ≤ C * sobNorm σ S w := by
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hp q hq
  have key : ∀ t : Finset ℕ, ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ),
      (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧ ∀ w, SmoothVec (lieSet ε) σ w → (t.sup p) (L w) ≤ C * sobNorm σ S w := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨[], 0, by simp, fun w _ => by simp⟩
    | insert i t _ ih =>
      obtain ⟨S, C, hS, h⟩ := ih
      obtain ⟨S', C', hS', h'⟩ := hL i
      refine ⟨S' ++ S, max |C'| |C|, fun l hl => ?_, fun w hw => ?_⟩
      · rcases List.mem_append.1 hl with hl | hl
        · exact hS' l hl
        · exact hS l hl
      · rw [Finset.sup_insert, Seminorm.sup_apply]
        exact (sob_max (h' w hw) (h w hw)).2
  obtain ⟨S, C', hS, h⟩ := key s
  refine ⟨S, C * C', hS, fun w hw => ?_⟩
  calc q (L w) ≤ (C • s.sup p) (L w) := hC _
    _ = C * (s.sup p) (L w) := rfl
    _ ≤ C * (C' * sobNorm σ S w) := mul_le_mul_of_nonneg_left (h w hw) C.2
    _ = C * C' * sobNorm σ S w := by ring

theorem sobBd_comp [TopologicalSpace E] [IsTopologicalAddGroup E] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {p : ℕ → Seminorm ℂ E} (hp : WithSeminorms p) {L : H →ₗ[ℂ] E}
    (hL : L ∈ sobBd ε σ p) (e : E →L[ℂ] E) : (e : E →ₗ[ℂ] E) ∘ₗ L ∈ sobBd ε σ p := fun i =>
  sobBd_seminorm hp hL ((p i).comp (e : E →ₗ[ℂ] E))
    ((hp.continuous_seminorm i).comp e.continuous)

theorem dRep_comm [TopologicalSpace E] [T2Space E] {ε : Fin n → Bool} {p : ℕ → Seminorm ℂ E}
    {π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)} (h : IsSmoothModRep ε p π dπ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) (e : E →L[ℂ] E)
    (he : ∀ t : ℝ, e.comp (π (NormedSpace.exp (t • X))) = (π (NormedSpace.exp (t • X))).comp e) :
    e.comp (dπ X) = (dπ X).comp e := by
  ext v
  have h1 := h.hasDRep X hX (e v)
  have h0 := h.hasDRep X hX v
  unfold HasDRep at h1 h0
  have h2 := (e.continuous.tendsto _).comp h0
  have h3 : Filter.Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (π (NormedSpace.exp (t • X)) (e v) - e v))
      (nhdsWithin 0 {0}ᶜ) (nhds (e (dπ X v))) := by
    refine h2.congr fun t => ?_
    have := congrArg (fun f : E →L[ℂ] E => f v) (he t)
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [Function.comp, map_smul, map_sub, this]
  exact tendsto_nhds_unique h3 h1

end GlobalTheory.FactorExtension

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorFockOnePlaceIsoUnitaryFock
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorFockOnePlaceIsoUnitaryFock
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum Kronecker Matrix

namespace GlobalTheory.OneFunctional.FockTensor

theorem linSub_prod {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] (M : ι → Matrix σ σ ℂ)
    (f : ι → MvPolynomial (ι × σ) ℂ) : linSub M (∏ τ, f τ) = ∏ τ, linSub M (f τ) := by
  simp only [linSub, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, map_prod]

theorem linSub_rename {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] (M : ι → Matrix σ σ ℂ)
    (τ : ι) (f : MvPolynomial σ ℂ) :
    linSub M (rename (Prod.mk τ) f) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.sub (M τ)ᵀ f) := by
  unfold Formalism.GradedWeylDivisibility.sub
  simp only [linSub, MonoidHom.coe_mk, OneHom.coe_mk, AlgHom.toLinearMap_apply, aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  congr 1
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Function.comp_apply, map_sum, Matrix.transpose_apply]

theorem fockOne_apply (a b : ℕ) (α β : ℤ) (h : U a) (g : U b) (f : MvPolynomial (Fin b × Fin a) ℂ) :
    fockOne a b α β (h, g) f =
      ((detU a h ^ α * detU b g ^ β : ℂˣ) : ℂ) • Formalism.GradedWeylDivisibility.sub (g.1 ⊗ₖ (star h.1)ᵀ)ᵀ f := rfl

theorem fock_apply {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ) (h : UG ι a) (g : UG ι b)
    (f : Pol ι a b) :
    fock a b α β (h, g) f =
      (((∏ τ, detU a (h τ) ^ α τ) * ∏ τ, detU b (g τ) ^ β τ : ℂˣ) : ℂ) •
        linSub (fun τ => (g τ).1 ⊗ₖ (star (h τ).1)ᵀ) f := rfl

theorem outer₂_fockOne_iso : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ),
    Iso (outer₂ fun τ => fockOne a b (α τ) (β τ)) (fock a b α β) := by
  intro ι _ _ a b α β
  obtain ⟨e, he⟩ := GlobalTheory.PolyTensor.exists_piTensor_equiv ι (Fin b × Fin a)
  refine ⟨e, ?_⟩
  rintro ⟨h, g⟩ x
  have key : e.toLinearMap ∘ₗ outer₂ (fun τ => fockOne a b (α τ) (β τ)) (h, g) =
      fock a b α β (h, g) ∘ₗ e.toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro f
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      outer₂_apply, PiTensorProduct.map_tprod, he, fockOne_apply, fock_apply, linSub_prod, linSub_rename]
    simp only [map_smul]
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, ← map_prod, Units.coe_prod, Units.val_mul]
  exact LinearMap.congr_fun key x

end GlobalTheory.OneFunctional.FockTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorFockOnePlaceIsoUnitaryFockStatement
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.outerTensor_fockOnePlace_iso_unitaryFock : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (α β : ι → ℤ), Iso (outer₂ fun τ => fockOne a b (α τ) (β τ)) (fock a b α β) := by
  first | exact @GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | exact GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso | (intros; apply GlobalTheory.OneFunctional.FockTensor.outer₂_fockOne_iso <;> assumption)
end
end
