module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqIsMulRightInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
open Formalism.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompactDualUnique

theorem isOmegaLeb_unique {P Q : ℕ} {lam lam' : Measure (lieU P Q)}
    (h : IsOmegaLeb lam) (h' : IsOmegaLeb lam') : lam = lam' := by
  haveI : BorelSpace (lieU P Q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  haveI : LocallyCompactSpace (lieU P Q) :=
    (Submodule.closed_of_finiteDimensional (lieU P Q)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (lieU P Q) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, lam = t • lam' := ⟨_, Measure.isAddLeftInvariant_eq_smul lam lam'⟩
  have hp : lam.prod lam = (t * t) • lam'.prod lam' := by
    rw [ht, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hf : AEMeasurable (fun ab : lieU P Q × lieU P Q =>
      entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))
      (lam'.prod lam') := by
    apply Continuous.aemeasurable
    apply continuous_pi fun ij => ?_
    simp only [entries, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have hc : Continuous (fun x : lieU P Q =>
        (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) ij.1 ij.2) :=
      (continuous_apply ij.2).comp ((continuous_apply ij.1).comp continuous_subtype_val)
    exact (hc.comp continuous_fst).add (continuous_const.mul (hc.comp continuous_snd))
  rw [hp, Measure.map_smul _ hf, h2'] at h2
  have h3 := congrArg (fun m : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) =>
    m (Metric.ball 0 1)) h2
  simp only [Measure.smul_apply] at h3
  have hpos : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hfin : (volume : Measure ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ)) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have h4 : ((t * t : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.smul_def, smul_eq_mul] at h3
    exact (ENNReal.mul_left_inj hpos hfin).1 (h3.trans (one_mul _).symm)
  have h5 : t * t = 1 := by exact_mod_cast h4
  have h6 : t = 1 := by
    have h7 : (t : ℝ) * t = 1 := by exact_mod_cast h5
    have h8 : (0 : ℝ) ≤ t := t.2
    have : (t : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [ht, h6, one_smul]

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ℝ≥0∞}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, h1, h2⟩ := h
  obtain ⟨lam', h1', h2'⟩ := h'
  obtain rfl := isOmegaLeb_unique h1 h1'
  exact tendsto_nhds_unique h2 h2'

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ℝ≥0∞} (t : ℝ≥0)
    (h : OmegaDensity μ c) : OmegaDensity (t • μ) (t * c) := by
  obtain ⟨lam, h1, h2⟩ := h
  refine ⟨lam, h1, ?_⟩
  have := ENNReal.Tendsto.const_mul (a := (t : ℝ≥0∞)) h2 (Or.inr ENNReal.coe_ne_top)
  refine this.congr fun r => ?_
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc]

theorem exists_eq_smul {P Q : ℕ} (μ ν : Measure (UpqT P Q)) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    ∃ t : ℝ≥0, μ = t • ν := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI : LocallyCompactSpace (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.secondCountableTopology
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul μ ν⟩

theorem eq_cd (cd : CDHaar) (P Q : ℕ) (ν : Measure (UpqT P Q)) (νc : Measure (UpqT (P + Q) 0))
    (c : ENNReal) (hν : ν.IsHaarMeasure) (hνc : νc.IsHaarMeasure) (hp : IsProbabilityMeasure νc)
    (_h0 : c ≠ 0) (_ht : c ≠ ⊤) (h1 : OmegaDensity ν c) (h2 : OmegaDensity νc c) :
    ν = cd.cd P Q := by
  haveI := cd.haar P Q
  haveI := cd.haar (P + Q) 0
  haveI := cd.prob (P + Q)
  obtain ⟨c', h0', ht', h1', h2'⟩ := cd.trick P Q
  obtain ⟨s, hs⟩ := exists_eq_smul νc (cd.cd (P + Q) 0)
  have hs1 : s = 1 := by
    have := congrArg (fun m : Measure (UpqT (P + Q) 0) => m Set.univ) hs
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this.symm
  rw [hs1, one_smul] at hs
  rw [hs] at h2
  obtain rfl := omegaDensity_unique h2 h2'
  obtain ⟨t, ht⟩ := exists_eq_smul ν (cd.cd P Q)
  have h3 := omegaDensity_smul t h1'
  rw [← ht] at h3
  have h4 := omegaDensity_unique h3 h1
  have h5 : (t : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj h0' ht').1 (h4.trans (one_mul _).symm)
  have h6 : t = 1 := by exact_mod_cast h5
  rw [ht, h6, one_smul]

end GlobalTheory.CompactDualUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealPar.KStabLie

variable {p q n : ℕ}

theorem Jm_eq (p q : ℕ) : Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem isKC_iff (X : Mat p q) : IsKC X ↔ X * Jm p q = Jm p q * X := by
  rw [Jm_eq]
  constructor
  · intro h
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases a with a | a <;> rcases b with b | b
    · simp
    · simp [h (.inl a) (.inr b) (by simp [sameBlock])]
    · simp [h (.inr a) (.inl b) (by simp [sameBlock])]
    · simp
  · intro h a b hab
    have := congrFun (congrFun h a) b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    rcases a with a | a <;> rcases b with b | b
    · simp [sameBlock] at hab
    · simp only [Sum.elim_inl, Sum.elim_inr] at this
      linear_combination (-1 / 2 : ℂ) * this
    · simp only [Sum.elim_inl, Sum.elim_inr] at this
      linear_combination (1 / 2 : ℂ) * this
    · simp [sameBlock] at hab

theorem Jm_sq (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  cases a <;> simp

theorem Jm_ct (p q : ℕ) : (Jm p q)ᴴ = Jm p q := by
  rw [Jm_eq, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  cases a <;> simp

theorem mem_Kset {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) {x : T.G}
    (hx : x ∈ T.Kset) :
    Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ Formalism.REAL.Kset ε := by
  have h1 : Formalism.REAL.inUJ ε _ := h.cov_mem T x
  have h2 := (isKC_iff _).1 hx
  have h3 : Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := by
    rw [← h.reindex_Jm]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, h2]
  refine ⟨?_, h3⟩
  generalize Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g at h1 h3
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold Formalism.REAL.inUJ at h1
  rw [Matrix.mul_assoc, ← h3, ← Matrix.mul_assoc] at h1
  have h4 := congrArg (· * Formalism.REAL.Jm ε) h1
  simpa only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] using h4

theorem smul_mem_upq {X : Mat p q} (hX : X ∈ upq p q) (t : ℝ) : t • X ∈ upq p q := by
  have h : Xᴴ * Jm p q + Jm p q * X = 0 := hX
  change (t • X)ᴴ * Jm p q + Jm p q * (t • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h, smul_zero]

theorem expt_mem (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) (hK : IsKC X) (t : ℝ) :
    T.expt (t • X) ∈ T.Kset := by
  change IsKC _
  rw [T.expt_cov _ (smul_mem_upq hX t), isKC_iff]
  have h : Commute (t • X) (Jm p q) := Commute.smul_left ((isKC_iff X).1 hK) t
  exact h.exp_left.eq

theorem deriv_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H)
    [FiniteDimensional ℂ S] {f : ℝ → H} {y : H} (hf : HasDerivAt f y 0) (hS : ∀ t, f t ∈ S) : y ∈ S := by
  have hc : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  refine hc.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hf) (Filter.Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  exact S.smul_of_tower_mem _ (S.sub_mem (hS t) (hS 0))

theorem exists_decomp {Z : Mat p q} (hZ : IsKC Z) :
    ∃ X Y : Mat p q, X ∈ upq p q ∧ IsKC X ∧ Y ∈ upq p q ∧ IsKC Y ∧ Z = X + Complex.I • Y := by
  have hc : IsKC Zᴴ := by
    intro a b hab
    rw [Matrix.conjTranspose_apply, hZ b a (by cases a <;> cases b <;> simp_all [sameBlock]), star_zero]
  have h1 := (isKC_iff _).1 hZ
  have h2 := (isKC_iff _).1 hc
  refine ⟨(1 / 2 : ℂ) • (Z - Zᴴ), (-Complex.I / 2) • (Z + Zᴴ), ?_, ?_, ?_, ?_, ?_⟩
  · change _ + _ = 0
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_add]
    simp
  · intro a b hab
    simp only [Matrix.smul_apply, Matrix.sub_apply, hZ a b hab, hc a b hab, sub_zero, smul_zero]
  · change _ + _ = 0
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h1, h2]
    rw [show star (-Complex.I / 2) = Complex.I / 2 by simp]
    module
  · intro a b hab
    simp only [Matrix.smul_apply, Matrix.add_apply, hZ a b hab, hc a b hab, add_zero, smul_zero]
  · rw [smul_smul, show Complex.I * (-Complex.I / 2) = 1 / 2 by
      rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]
    module

theorem kstable_lie : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → (∀ S : Submodule ℂ R.U.H, FiniteDimensional ℂ S → IsKStableOn ε σ S → S ≤ LinearMap.range R.ι) ∧ ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → IsKStableOn ε σ (W.map R.ι) → KStable R.HK.act W := by
  intro p q n e ε T R σ h hσ
  refine ⟨fun S hS hK v hv => ?_, fun W hW hK => ?_⟩
  · have : KFin T R.U.π v := by
      unfold KFin
      refine Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      change R.U.π k v ∈ S
      rw [hσ]
      exact hK _ (mem_Kset h T k.2) v hv
    exact (R.ι_range v).2 this
  · have key : ∀ X ∈ upq p q, IsKC X → ∀ w ∈ W, R.HK.act X w ∈ W := by
      intro X hX hXK w hw
      have : R.ι (R.HK.act X w) ∈ W.map R.ι := by
        refine deriv_mem _ (R.der X hX w) fun t => ?_
        rw [hσ]
        exact hK _ (mem_Kset h T (expt_mem T hX hXK t)) _ (Submodule.mem_map_of_mem hw)
      obtain ⟨u, hu, hu'⟩ := this
      rw [← R.ι_inj hu']
      exact hu
    intro Z hZ w hw
    obtain ⟨X, Y, hX, hXK, hY, hYK, rfl⟩ := exists_decomp hZ
    rw [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact W.add_mem (key X hX hXK w hw) (W.smul_mem _ (key Y hY hYK w hw))

end GlobalTheory.RealPar.KStabLie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLieStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDim_kStable_subspace_kFinite_lie : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → (∀ S : Submodule ℂ R.U.H, FiniteDimensional ℂ S → IsKStableOn ε σ S → S ≤ LinearMap.range R.ι) ∧ ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → IsKStableOn ε σ (W.map R.ι) → KStable R.HK.act W := by
  first | exact @GlobalTheory.RealPar.KStabLie.kstable_lie | exact GlobalTheory.RealPar.KStabLie.kstable_lie | (intros; apply GlobalTheory.RealPar.KStabLie.kstable_lie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDim
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDim
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar

theorem flow_mem_map {V H : Type*} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : V →ₗ[ℂ] H) (a : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, a w ∈ W)
    (U : ℝ → H →L[ℂ] H) (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (hder : ∀ v, HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) 0) (t : ℝ) :
    ∀ x ∈ W.map ι, U t x ∈ W.map ι := by
  classical
  have hd : ∀ v s, HasDerivAt (fun t : ℝ => U t (ι v)) (U s (ι (a v))) s := by
    intro v s
    have h1 : HasDerivAt (fun t : ℝ => U (t - s) (ι v)) (ι (a v)) s := by
      have := (show HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) (s - s) by
        rw [sub_self]; exact hder v)
      exact this.comp_sub_const s s
    have h2 := ((U s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : (fun t : ℝ => U t (ι v)) = ((U s).restrictScalars ℝ) ∘ fun t : ℝ => U (t - s) (ι v) := by
      ext r
      have := hadd s (r - s)
      rw [add_sub_cancel] at this
      simp [this]
    rw [h3]
    exact h2
  rintro _ ⟨w, hw, rfl⟩
  rw [← (W.map ι).orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro y hy
  let b := Module.finBasis ℂ W
  let f : ℝ → Fin (Module.finrank ℂ W) → ℂ := fun s i => inner ℂ y (U s (ι (b i)))
  have hf : ∀ s (u : W), inner ℂ y (U s (ι u)) = ∑ j, b.repr u j * f s j := by
    intro s u
    have h3 : (u : V) = ∑ j, b.repr u j • (b j : V) := by
      have := congrArg W.subtype (b.sum_repr u)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      exact this.symm
    rw [h3]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, map_sum, map_smul, inner_sum, inner_smul_right]
  let M : Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
    fun i j => b.repr ⟨a (b i), hW _ (b i).2⟩ j
  let L := LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  have hfd : ∀ s, HasDerivAt f (L (f s)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have h2 := ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hd (b i) s)
    have := hf s ⟨a (b i), hW _ (b i).2⟩
    have h4 : L (f s) i = ∑ j, b.repr ⟨a (b i), hW _ (b i).2⟩ j * f s j := by
      simp only [L, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
      rfl
    rw [h4, ← this]
    exact h2
  have hf0 : f 0 = 0 := by
    ext i
    simp only [f, h0]
    exact Submodule.inner_left_of_mem_orthogonal (K := W.map ι) ⟨b i, (b i).2, rfl⟩ hy
  have hz : f = fun _ => 0 := by
    refine ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊) (t₀ := 0)
      (fun _ => L.lipschitz.lipschitzOnWith) (fun s => ⟨hfd s, trivial⟩) (fun s => ⟨?_, trivial⟩) hf0
    simpa using hasDerivAt_const s (0 : Fin (Module.finrank ℂ W) → ℂ)
  rw [hf t ⟨w, hw⟩, hz]
  simp

theorem isKStableOn_of_kStable : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → KStable R.HK.act W → IsKStableOn ε σ (W.map R.ι) := by
  intro p q n e ε T R σ hb hF W hfin hK k hk
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective Y
  have hX : X ∈ upq p q := by
    have h1 := hY.1
    unfold Formalism.REAL.inG at h1
    rw [← hb.reindex_Jm, Matrix.conjTranspose_reindex] at h1
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_add]
    exact h1
  have hKC : IsKC X := by
    intro a b hab
    rw [hb.sameBlock_iff] at hab
    have h2 := congrFun (congrFun hY.2 (e a)) (e b)
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at h2
    cases h3 : ε (e a) <;> cases h4 : ε (e b) <;> rw [h3, h4] at hab h2
    · exact (hab rfl).elim
    · simp only [if_true, Bool.false_eq_true, if_false] at h2
      linear_combination (1/2 : ℂ) * h2
    · simp only [if_true, Bool.false_eq_true, if_false] at h2
      linear_combination (-1/2 : ℂ) * h2
    · exact (hab rfl).elim
  have hk' : σ k = R.U.π (T.expt ((1 : ℝ) • X)) := by
    rw [hF, one_smul, T.expt_cov X hX, ← hexp]
    congr 1
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
      exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X).symm
  rw [hk']
  exact flow_mem_map R.ι (R.HK.act X) W (hK X hKC) (fun t => R.U.π (T.expt (t • X)))
    (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add X hX, map_mul]) (R.der X hX) 1

end GlobalTheory.RealPar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDimStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKStableOn_of_lieStable_finiteDim : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → KStable R.HK.act W → IsKStableOn ε σ (W.map R.ι) := by
  first | exact @GlobalTheory.RealPar.isKStableOn_of_kStable | exact GlobalTheory.RealPar.isKStableOn_of_kStable | (intros; apply GlobalTheory.RealPar.isKStableOn_of_kStable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVector
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVector
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.TorusWt

variable {p q n : ℕ}

def torX (θ : Ix p q → ℝ) : Mat p q := Matrix.diagonal fun a => (θ a : ℂ) * Complex.I

theorem torX_mem (θ : Ix p q → ℝ) : torX θ ∈ upq p q := by
  change _ = _
  ext a b
  have hJ : TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  rw [hJ, torX, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add]
  by_cases h : a = b
  · subst h; simp; ring
  · simp [h]

theorem smul_torX (t : ℝ) (θ : Ix p q → ℝ) : t • torX θ = torX fun a => t * θ a := by
  ext a b
  by_cases h : a = b
  · subst h; simp [torX, mul_assoc]
  · simp [torX, h]

theorem torX_eq_sum (θ : Ix p q → ℝ) : torX θ = ∑ a, ((θ a : ℂ) * Complex.I) • Eab a a := by
  ext a b
  simp only [torX, Eab, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · simp

theorem reindex_cov_expt (T : GrpData p q) (e : Ix p q ≃ Fin n) (θ : Fin n → ℝ) :
    Matrix.reindex e e ((T.cov (T.expt (torX fun a => θ (e a))) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
  rw [T.expt_cov _ (torX_mem _), torX, Matrix.exp_diagonal]
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp [Matrix.diagonal_apply, Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem diag_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem flow_eq {T : GrpData p q} (R : DSRep T) {X : Mat p q} (hX : X ∈ upq p q) {v : R.HK.V} {c : ℂ}
    (hv : R.HK.act X v = c • v) : R.U.π (T.expt X) (R.ι v) = Complex.exp c • R.ι v := by
  set f : ℝ → R.U.H := fun t => R.U.π (T.expt (t • X)) (R.ι v) with hf
  have hd : ∀ t, HasDerivAt f (c • f t) t := by
    intro t
    have h0 := R.der X hX v
    rw [hv, map_smul] at h0
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) (c • R.ι v) t := by
      have := HasDerivAt.comp_sub_const t t (f := f) (f' := c • R.ι v) (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((R.U.π (T.expt (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    convert (preTransparency := .reducible) h2 using 1
    · funext s
      simp only [hf, Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    · simp [hf]
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    convert h1.fun_smul (hd t) using 1
    rw [smul_smul, ← add_smul]; simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, ContinuousLinearMap.one_apply] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem isWtOn_iff : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (μ : Fin n → ℝ) (v : R.HK.V), IsWtOn (Formalism.REAL.Kset ε) σ μ (R.ι v) ↔ ∀ a, R.HK.act (Eab a a) v = ((μ (e a) : ℝ) : ℂ) • v := by
  intro p q n e ε T R σ _ hF μ v
  have key : ∀ θ : Fin n → ℝ, R.U.π (T.expt (torX fun a => θ (e a))) =
      σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := fun θ => by
    rw [hF, reindex_cov_expt]
  constructor
  · intro h a
    set θ : Fin n → ℝ := Pi.single (e a) 1 with hθ
    have h0 := R.der _ (torX_mem fun b => θ (e b)) v
    have h1 : (fun t : ℝ => R.U.π (T.expt (t • torX fun b => θ (e b))) (R.ι v)) =
        fun t : ℝ => Complex.exp ((μ (e a) * Complex.I) * t) • R.ι v := by
      funext t
      rw [smul_torX, key fun b => t * θ b, h _ (diag_mem_Kset ε _)]
      congr 2
      rw [Finset.sum_eq_single (e a)]
      · simp [hθ]; ring
      · intro c _ hc; simp [hθ, hc]
      · simp
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((μ (e a) * Complex.I) * t) • R.ι v)
        ((μ (e a) * Complex.I) • R.ι v) 0 := by
      have : HasDerivAt (fun t : ℝ => ((μ (e a) * Complex.I) * (t : ℂ))) (μ (e a) * Complex.I) 0 := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (μ (e a) * Complex.I))
      simpa using this.cexp.smul_const (R.ι v)
    rw [h1] at h0
    have h3 := h0.unique h2
    rw [← map_smul] at h3
    have h4 := R.ι_inj h3
    have h5 : (torX fun b => θ (e b)) = Complex.I • Eab a a := by
      rw [torX_eq_sum, Finset.sum_eq_single a]
      · simp [hθ]
      · intro c _ hc; simp [hθ, hc]
      · simp
    rw [h5, map_smul, LinearMap.smul_apply, mul_comm, mul_smul] at h4
    exact smul_right_injective _ Complex.I_ne_zero h4
  · intro h θ _
    rw [← key]
    apply flow_eq R (torX_mem _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [torX_eq_sum, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, h, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [← e.sum_comp]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.RealPar.TorusWt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusWeightVector_iff_cartanWeightVector : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (μ : Fin n → ℝ) (v : R.HK.V), IsWtOn (Formalism.REAL.Kset ε) σ μ (R.ι v) ↔ ∀ a, R.HK.act (Eab a a) v = ((μ (e a) : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.RealPar.TorusWt.isWtOn_iff | exact GlobalTheory.RealPar.TorusWt.isWtOn_iff | (intros; apply GlobalTheory.RealPar.TorusWt.isWtOn_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealPar.SqInt

variable {p q n : ℕ}

def reixHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b) :
    Matrix a a ℂ →* Matrix b b ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom

theorem reixHom_apply {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b)
    (g : Matrix a a ℂ) : reixHom e g = Matrix.reindex e e g := rfl

theorem continuous_reixHom {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (e : a ≃ b) :
    Continuous (reixHom e) :=
  continuous_id.matrix_reindex e e

def covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) : T.G →* Formalism.REAL.UJ ε :=
  ((Units.map (reixHom e)).comp T.cov).codRestrict (Formalism.REAL.UJ ε) fun x => h.cov_mem T x

theorem umat_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    umat (covU h T x) = Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := rfl

theorem continuous_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    Continuous (covU h T) :=
  Continuous.subtype_mk (((continuous_reixHom e).units_map _).comp (continuous_fst.comp T.emb.continuous)) _

theorem surjective_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    Function.Surjective (covU h T) := by
  intro g
  obtain ⟨x, hx⟩ := h.cov_surj T (g := umat g) g.2
  exact ⟨x, Subtype.ext (Units.ext hx)⟩

theorem isClosedEmbedding_emb (T : GrpData p q) :
    Topology.IsClosedEmbedding (fun x : T.G => (T.cov x, T.sq x)) := by
  refine ⟨T.emb, ?_⟩
  have : Set.range (fun x : T.G => (T.cov x, T.sq x)) =
      {z : GL (Ix p q) ℂ × ℂˣ | (z.1 : Mat p q)ᴴ * Jm p q * z.1 = Jm p q} ∩
        {z | (z.2 : ℂ) ^ 2 = (z.1 : Mat p q).det} := by
    ext ⟨g, w⟩
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact ⟨T.cov_mem x, T.sq_sq x⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨x, hx, -⟩ := T.bij g h1 w h2
      exact ⟨x, Prod.ext hx.1 hx.2⟩
  rw [this]
  have c1 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.1 : Mat p q) := Units.continuous_val.comp continuous_fst
  have c2 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.2 : ℂ) := Units.continuous_val.comp continuous_snd
  exact (isClosed_eq ((c1.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul c1) continuous_const).inter
    (isClosed_eq (c2.pow 2) c1.matrix_det)

theorem norm_sq_eq_one {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    ‖(T.sq x : ℂ)‖ = 1 := by
  have h1 := (mem_Upq _).1 (T.cov_mem x)
  have hJ : (Jm p q).det ≠ 0 := by
    have : (Matrix.reindex e e (Jm p q)).det * (Matrix.reindex e e (Jm p q)).det = 1 := by
      rw [h.reindex_Jm, ← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
    rw [Matrix.det_reindex_self] at this
    exact left_ne_zero_of_mul_eq_one this
  have h2 := congrArg (fun A => ‖Matrix.det A‖) h1
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, ← T.sq_sq x, norm_pow] at h2
  have h3 : ‖(T.sq x : ℂ)‖ ^ 4 = 1 := by
    apply mul_right_cancel₀ (norm_ne_zero_iff.2 hJ)
    rw [one_mul]
    conv_rhs => rw [← h2]
    ring
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h3

theorem isProperMap_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    IsProperMap (covU h T) := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨continuous_covU h T, fun K hK => ?_⟩
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hK' : IsCompact ((fun g : Formalism.REAL.UJ ε => (Units.map (reixHom e.symm) g.1 : GL (Ix p q) ℂ)) '' K) :=
    hK.image (((continuous_reixHom e.symm).units_map _).comp continuous_subtype_val)
  refine ((isClosedEmbedding_emb T).isCompact_preimage (hK'.prod hS)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_covU h T)) fun x hx => ⟨⟨covU h T x, hx, Units.ext ?_⟩, ?_⟩
  · change Matrix.reindex e.symm e.symm (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q)) = _
    simp
  · simpa using norm_sq_eq_one h T x

theorem isHaarMeasure_map_covU {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) :
    (T.haar.map (covU h T)).IsHaarMeasure :=
  Measure.isHaarMeasure_map T.haar (covU h T) (continuous_covU h T) (surjective_covU h T)
    (isProperMap_iff_tendsto_cocompact.1 (isProperMap_covU h T)).2

theorem isSqIntOn_of_factors : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T)
    (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → IsSqIntOn ε σ := by
  intro p q n e ε T R σ h hF v w
  have hc : coefOn (ε := ε) σ v w ∘ covU h T = fun g => inner ℂ w (R.U.π g v) := by
    funext x
    simp only [Function.comp, coefOn, umat_covU, hF x]
  have hc1 : Continuous fun g => (inner ℂ w (R.U.π g v) : ℂ) := continuous_const.inner (R.U.cont v)
  have hq := (isProperMap_covU h T).isClosedMap.isQuotientMap (continuous_covU h T) (surjective_covU h T)
  have hc2 : Continuous (coefOn (ε := ε) σ v w) := hq.continuous_iff.2 (hc ▸ hc1)
  haveI := isHaarMeasure_map_covU h T
  rw [Measure.isMulLeftInvariant_eq_smul (Formalism.REAL.muG ε) (T.haar.map (covU h T))]
  refine MemLp.smul_measure ?_ ENNReal.coe_ne_top
  rw [memLp_map_measure_iff hc2.aestronglyMeasurable (continuous_covU h T).measurable.aemeasurable, hc,
    memLp_two_iff_integrable_sq_norm hc1.aestronglyMeasurable]
  exact (R.schur v w).1

end GlobalTheory.RealPar.SqInt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.BlockOrderedSquareIntegrableStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_ordered_square_integrable : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → IsSqIntOn ε σ := by
  first | exact @GlobalTheory.RealPar.SqInt.isSqIntOn_of_factors | exact GlobalTheory.RealPar.SqInt.isSqIntOn_of_factors | (intros; apply GlobalTheory.RealPar.SqInt.isSqIntOn_of_factors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoverIrreducibleUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoverIrreducibleUnitary
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.CoverURep

variable {p q n : ℕ}

theorem gl_isEmbedding_val :
    Topology.IsEmbedding (Units.val : (Mat p q)ˣ → Mat p q) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Mat p q => A⁻¹) (fun A hA => ?_) (fun u => ?_)
  · have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    exact (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd)).continuousWithinAt
  · simp

theorem inducing_pair (T : GrpData p q) (e : Ix p q ≃ Fin n) :
    Topology.IsInducing (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) := by
  have h1 : Topology.IsInducing (fun A : Mat p q => Matrix.reindex e e A) := by
    refine Topology.IsInducing.of_comp (g := fun B : Matrix (Fin n) (Fin n) ℂ => Matrix.reindex e.symm e.symm B)
      (continuous_id.matrix_reindex e e) (continuous_id.matrix_reindex e.symm e.symm) ?_
    convert Topology.IsInducing.id using 1
    funext A i j
    simp [Matrix.reindex_apply]
  exact ((h1.comp gl_isEmbedding_val.isInducing).prodMap Units.isEmbedding_val₀.isInducing).comp T.emb.isInducing

theorem det_Jm_ne_zero {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) : (Jm p q).det ≠ 0 := by
  have : (Matrix.reindex e e (Jm p q)).det * (Matrix.reindex e e (Jm p q)).det = 1 := by
    rw [h.reindex_Jm, ← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
  rw [Matrix.det_reindex_self] at this
  exact left_ne_zero_of_mul_eq_one this

theorem norm_sq_eq_one {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    ‖((T.sq x : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg Matrix.det ((mem_Upq _).1 (T.cov_mem x))
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, ← T.sq_sq x] at h1
  have h2 := congrArg norm h1
  rw [norm_mul, norm_mul, norm_star, norm_pow] at h2
  have h3 : ‖(Jm p q).det‖ ≠ 0 := norm_ne_zero_iff.2 (det_Jm_ne_zero h)
  have h4 : ‖((T.sq x : ℂˣ) : ℂ)‖ ^ 4 = 1 := by
    apply mul_left_cancel₀ h3
    linear_combination h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4

theorem continuousOn_of_cover {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q)
    {Y : Type*} [TopologicalSpace Y] (f : Matrix (Fin n) (Fin n) ℂ → Y)
    (hf : Continuous fun x : T.G => f (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))) :
    ContinuousOn f (UJset ε) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  obtain ⟨C, hC, hCe⟩ := (inducing_pair T e).isClosed_iff.1 (ht.preimage hf)
  have hK : CompactSpace (Metric.closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  have hD : IsClosed {z : Matrix (Fin n) (Fin n) ℂ × Metric.closedBall (0 : ℂ) 1 |
      (z.1, (z.2 : ℂ)) ∈ C ∧ (z.2 : ℂ) ^ 2 = z.1.det} := by
    refine IsClosed.inter (hC.preimage (by fun_prop)) (isClosed_eq (by fun_prop) ?_)
    exact continuous_fst.matrix_det
  refine ⟨_, isClosedMap_fst_of_compactSpace _ hD, ?_⟩
  ext g
  constructor
  · rintro ⟨hg, hU⟩
    refine ⟨?_, hU⟩
    obtain ⟨x, rfl⟩ := h.cov_surj T hU
    have hx : x ∈ (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C := by
      rw [hCe]; exact hg
    refine ⟨(_, ⟨((T.sq x : ℂˣ) : ℂ), by simp [norm_sq_eq_one h T x]⟩), ⟨hx, ?_⟩, rfl⟩
    simp only [Matrix.det_reindex_self]
    exact T.sq_sq x
  · rintro ⟨⟨⟨g', w, hw⟩, ⟨h1, h2⟩, rfl⟩, hU⟩
    refine ⟨?_, hU⟩
    obtain ⟨x, hx⟩ := h.cov_surj T hU
    simp only at hx h1 h2
    subst hx
    rw [Matrix.det_reindex_self] at h2
    have hw0 : w ≠ 0 := by
      rintro rfl
      have := T.sq_sq x
      rw [← h2] at this
      simp at this
    obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := T.bij (T.cov x) (T.cov_mem x) (Units.mk0 w hw0) h2
    have hy : y ∈ (fun x : T.G =>
      (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q), ((T.sq x : ℂˣ) : ℂ))) ⁻¹' C := by
      simp only [Set.mem_preimage, hy1, hy2]
      exact h1
    rw [hCe] at hy
    simp only [Set.mem_preimage, hy1] at hy
    exact hy

theorem urep_irred : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T)
    (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ →
      IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ := by
  intro p q n e ε T R σ h hF
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · have := hF 1
    rw [map_one, map_one] at this
    rw [this]
    simp
  · intro a ha b hb
    obtain ⟨x, rfl⟩ := h.cov_surj T ha
    obtain ⟨y, rfl⟩ := h.cov_surj T hb
    have := hF (x * y)
    rw [map_mul, map_mul, hF x, hF y] at this
    rw [← ContinuousLinearMap.mul_def, this]
    simp [Matrix.submatrix_mul_equiv]
  · intro g hg v
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    rw [← hF x]
    exact R.U.isom x v
  · intro v
    refine continuousOn_of_cover h T _ ?_
    simpa only [← hF _] using R.U.cont v
  · intro S hS hst
    refine R.irred S hS fun x v hv => ?_
    rw [hF x]
    exact hst _ (h.cov_mem T x) v hv

end GlobalTheory.RealPar.CoverURep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoverIrreducibleUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_cover_irreducibleUnitary : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ := by
  first | exact @GlobalTheory.RealPar.CoverURep.urep_irred | exact GlobalTheory.RealPar.CoverURep.urep_irred | (intros; apply GlobalTheory.RealPar.CoverURep.urep_irred <;> assumption)
end
end
