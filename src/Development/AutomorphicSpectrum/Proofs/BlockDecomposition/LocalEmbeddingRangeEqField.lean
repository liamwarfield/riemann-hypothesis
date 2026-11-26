module

public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.RightWhit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTHodge.CompletionRange

theorem isClosed_finExt {l : ℕ} [Fact l.Prime] (K : FinExt l) : IsClosed (K.1 : Set (Om l)) := by
  haveI : FiniteDimensional ℚ_[l] K.1.toSubmodule := K.2
  exact Submodule.closed_of_finiteDimensional K.1.toSubmodule

theorem valued_le_one_of_norm_le_one {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : ‖φ x‖ ≤ 1) : Valued.v x ≤ 1 := by
  by_contra hv
  have hv' : 1 < Valued.v x := not_le.1 hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv'
  have hy : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hv'
  have ht : Filter.Tendsto (fun n : ℕ => x⁻¹ ^ n) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one hy
  have ht' : Filter.Tendsto (fun n : ℕ => φ (x⁻¹ ^ n)) Filter.atTop (nhds 0) := by
    have h := (hφ.tendsto 0).comp ht
    rw [map_zero] at h
    exact h
  have hge : ∀ n : ℕ, 1 ≤ ‖φ (x⁻¹ ^ n)‖ := fun n => by
    have hφ0 : φ x ≠ 0 := (map_ne_zero φ).2 hx0
    rw [map_pow, map_inv₀, norm_pow, norm_inv]
    exact one_le_pow₀ ((one_le_inv₀ (norm_pos_iff.2 hφ0)).2 hx)
  have hn := ht'.norm
  rw [norm_zero] at hn
  have := ge_of_tendsto' hn hge
  linarith

theorem isClosed_image_integers {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ) :
    IsClosed (φ '' (w.adicCompletionIntegers E : Set (w.adicCompletion E))) := by
  have hc : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (w.adicCompletionIntegers E)))
  exact (hc.image hφ).isClosed

theorem range_eq_Kw : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l), Continuous φ →
    (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    Set.range φ = (Bw.Kw.1 : Set (Om l)) := by
  intro l _ E Ω _ _ _ _ Gw O _ _ _ Bw w φ hφ hE
  have hcl := isClosed_finExt Bw.Kw

  have key : ∀ k ∈ (Bw.Kw.1 : Set (Om l)), ‖k‖ ≤ 1 → k ∈ Set.range φ := by
    intro k hk hk1
    have hden : k ∈ closure (Set.range φ) := by
      refine closure_mono ?_ (Bw.j_dense hk)
      rintro _ ⟨y, rfl⟩
      exact ⟨algebraMap E _ y, hE y⟩
    have hS : IsOpen (Metric.closedBall (0 : Om l) 1) :=
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero
    have hk' : k ∈ Metric.closedBall (0 : Om l) 1 := by simpa using hk1
    have h2 : k ∈ closure (Metric.closedBall (0 : Om l) 1 ∩ Set.range φ) :=
      hS.inter_closure ⟨hk', hden⟩
    have h3 : Metric.closedBall (0 : Om l) 1 ∩ Set.range φ ⊆
        φ '' (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
      rintro _ ⟨hb, x, rfl⟩
      refine ⟨x, ?_, rfl⟩
      exact valued_le_one_of_norm_le_one w φ hφ x (by simpa using hb)
    have h4 := closure_minimal h3 (isClosed_image_integers w φ hφ) h2
    obtain ⟨x, -, rfl⟩ := h4
    exact ⟨x, rfl⟩
  refine Set.Subset.antisymm ?_ fun k hk => ?_
  · rintro _ ⟨x, rfl⟩
    refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on
      (p := fun x => φ x ∈ (Bw.Kw.1 : Set (Om l))) x (hcl.preimage hφ) fun y => ?_
    rw [hE y]
    exact Bw.j_E y
  · rcases le_total ‖k‖ 1 with h | h
    · exact key k hk h
    · have hinv : k⁻¹ ∈ (Bw.Kw.1 : Set (Om l)) := inv_mem hk
      obtain ⟨a, ha⟩ := key k⁻¹ hinv (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
      exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_inv]⟩

end GlobalTheory.CompanionTheory.LTHodge.CompletionRange
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqFieldStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embedding_range_eq_field : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l), Continuous φ →
    (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    Set.range φ = (Bw.Kw.1 : Set (Om l)) := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw | exact GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw | (intros; apply GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.InjHw

variable {n : ℕ}

theorem exp_mem_unitary (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

theorem single_negI (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

def expU (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem_unitary X hX s⟩

section V

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem deriv_expU (h : IsDerivK σ Kf) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (w : V) :
    HasDerivAt (fun s : ℝ => σ (expU X hX s) w) (∑ a, ∑ b, X a b • Kf a b w) 0 := by
  obtain ⟨S, _, hw, _, _, hd⟩ := h.2 w
  exact hd X (expU X hX) (fun _ => rfl) w hw

theorem sum_mem_of_stable (h : IsDerivK σ Kf) (R : Submodule ℂ V) [FiniteDimensional ℂ R]
    (hR : ∀ k, ∀ w ∈ R, σ k w ∈ R) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) {w : V} (hw : w ∈ R) :
    ∑ a, ∑ b, X a b • Kf a b w ∈ R := by
  have hd := deriv_expU h X hX w
  have hcl : IsClosed (R : Set V) := Submodule.closed_of_finiteDimensional R
  have ht := hasDerivAt_iff_tendsto_slope_zero.1 hd
  refine hcl.mem_of_tendsto ht (Filter.Eventually.of_forall fun s => ?_)
  have : s⁻¹ • (σ (expU X hX (0 + s)) w - σ (expU X hX 0) w) ∈ R.restrictScalars ℝ :=
    Submodule.smul_mem _ _ (sub_mem (hR _ _ hw) (hR _ _ hw))
  exact this

theorem sum_single (w : V) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w = c • Kf a b w := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

theorem entry_mem (h : IsDerivK σ Kf) (R : Submodule ℂ V) [FiniteDimensional ℂ R]
    (hR : ∀ k, ∀ w ∈ R, σ k w ∈ R) (a b : Fin n) {w : V} (hw : w ∈ R) : Kf a b w ∈ R := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_negI, single_negI, neg_add,
      add_comm]
  have m1 := sum_mem_of_stable h R hR _ h1 hw
  have m2 := sum_mem_of_stable h R hR _ h2 hw
  have e1 : ∑ x, ∑ y, (Matrix.single a b (1 : ℂ) - Matrix.single b a 1 : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w =
      Kf a b w - Kf b a w := by
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, sum_single, one_smul]
  have e2 : ∑ x, ∑ y, (Matrix.single a b Complex.I + Matrix.single b a Complex.I : Matrix (Fin n) (Fin n) ℂ) x y • Kf x y w =
      Complex.I • Kf a b w + Complex.I • Kf b a w := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, sum_single]
  rw [e1] at m1
  rw [e2] at m2
  have m3 := R.smul_mem (-Complex.I) m2
  have m4 := R.smul_mem (1 / 2 : ℂ) (R.add_mem m1 m3)
  have e3 : (1 / 2 : ℂ) • (Kf a b w - Kf b a w + -Complex.I • (Complex.I • Kf a b w + Complex.I • Kf b a w)) = Kf a b w := by
    rw [smul_add (-Complex.I), smul_smul, smul_smul]
    have : -Complex.I * Complex.I = 1 := by simp
    rw [this, one_smul, one_smul, sub_add_add_cancel, ← two_smul ℂ, smul_smul]
    norm_num
  rwa [e3] at m4

theorem weight_of_torus (h : IsDerivK σ Kf) (μ : Fin n → ℤ) {v : V}
    (hv : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → σ k v = (∏ a, z a ^ μ a) • v)
    (a : Fin n) : Kf a a v = ((μ a : ℝ) : ℂ) • v := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  have hd := deriv_expU (Kf := Kf) h _ hX v
  rw [sum_single] at hd
  have hk : ∀ s : ℝ, (expU _ hX s).1 = diagonal (fun c => if c = a then Complex.exp (s * Complex.I) else 1) := by
    intro s
    have e : (s : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
        diagonal (fun c => if c = a then (s : ℂ) * Complex.I else 0) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hc : i = a
        · subst hc
          simp
        · simp [Matrix.single_apply, hc, Ne.symm hc]
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
          if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
    show NormedSpace.exp _ = _
    rw [e, Matrix.exp_diagonal]
    congr 1
    funext c
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  have hf : (fun s : ℝ => σ (expU _ hX s) v) =
      fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v := by
    funext s
    rw [hv _ _ (hk s), Finset.prod_eq_single a]
    · simp only [if_true]
      rw [← Complex.exp_int_mul]
      congr 2
      push_cast
      ring
    · intro c _ hc
      simp [hc]
    · simp
  rw [hf] at hd
  have h2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) • v)
      ((Complex.I * ((μ a : ℝ) : ℂ)) • v) 0 := by
    have h3 : HasDerivAt (fun y : ℂ => Complex.exp (y * (Complex.I * ((μ a : ℝ) : ℂ))))
        (Complex.exp ((0 : ℂ) * (Complex.I * ((μ a : ℝ) : ℂ))) * (1 * (Complex.I * ((μ a : ℝ) : ℂ)))) 0 :=
      ((hasDerivAt_id (0 : ℂ)).mul_const _).cexp
    have h4 := (h3.comp_ofReal).smul_const v
    simpa using h4
  have e := hd.unique h2
  calc Kf a a v = (-Complex.I) • (Complex.I • Kf a a v) := by rw [smul_smul]; simp
    _ = ((μ a : ℝ) : ℂ) • v := by rw [e, smul_smul, ← mul_assoc]; simp

end V

section Main

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem gl_kF {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have c1 := h.comm a b c d
  have c2 := h.comm c d a b
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [c1, c2]
    abel
  rw [e, h1, h2]
  simp only [kF]
  split_ifs <;> abel

theorem weight_shift {K : Fin n → Fin n → Module.End ℂ V} (hg : Formalism.REAL.GlRel K) (μ : Fin n → ℤ) {v : V}
    (hv : ∀ c, K c c v = ((μ c : ℝ) : ℂ) • v) {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    K c c (K a b v) =
      (((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℤ) : ℝ) : ℂ) • K a b v := by
  have e : K c c (K a b v) = K a b (K c c v) +
      ((if c = a then K c b else 0) - (if b = c then K a c else 0)) v := by
    rw [← hg c c a b]
    simp [Module.End.mul_apply]
  rw [e, hv c, map_smul]
  by_cases h1 : c = a
  · subst h1
    have h2 : ¬ b = c := fun h => hab h.symm
    have h3 : ¬ c = b := hab
    simp only [↓reduceIte, h2, h3, LinearMap.sub_apply, LinearMap.zero_apply]
    push_cast
    module
  · by_cases h2 : c = b
    · subst h2
      simp only [↓reduceIte, h1, LinearMap.sub_apply, LinearMap.zero_apply]
      push_cast
      module
    · have h3 : ¬ b = c := fun h => h2 h.symm
      simp only [↓reduceIte, h1, h2, h3, sub_zero, LinearMap.zero_apply, add_zero]

def jt (K : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ) : Submodule ℂ V :=
  ⨅ c, (K c c).maxGenEigenspace (χ c)

theorem mem_jt {K : Fin n → Fin n → Module.End ℂ V} {χ : Fin n → ℂ} {v : V} (hv : ∀ c, K c c v = χ c • v) :
    v ∈ jt K χ := by
  refine (Submodule.mem_iInf _).2 fun c => ?_
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by simp [hv c]⟩

theorem jt_indep {K : Fin n → Fin n → Module.End ℂ V} (hg : Formalism.REAL.GlRel K) : iSupIndep (jt K) := by
  have hc : ∀ i j, Commute (K i i) (K j j) := by
    intro i j
    have h := hg i i j j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · have h' : ¬ j = i := fun h => hij h.symm
      rw [if_neg hij, if_neg h', sub_zero] at h
      exact sub_eq_zero.1 h
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun c => K c c)
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)

def wtC (μ : Fin n → ℤ) : Fin n → ℂ := fun a => ((μ a : ℝ) : ℂ)

theorem wtC_injective : Function.Injective (wtC (n := n)) := by
  intro x y h
  funext c
  have := congrFun h c
  simpa [wtC] using this

end Main

end GlobalTheory.CompanionTheory.RealCount.InjHw
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHGPIffParabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHGPIffParabolic
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.GPMem

theorem mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (g : Mir k (m + j)) :
    g ∈ MirabolicParabolic k m j ↔ mirabolicProjection k (m + j) g ∈ parab k (two (stdSum (rfl : m + j = m + j))) := by
  have hlast : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
      (Fin.last (m + j)) = GlobalTheory.BZMir.eLast k (m + j) :=
    (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (m + j + 1)) k)).1 g.2
  have hproj : ∀ a b : Fin (m + j),
      ((GlobalTheory.BZMir.mirabolicProjection k (m + j) g : GL (Fin (m + j)) k) : Matrix (Fin (m + j)) (Fin (m + j)) k) a b =
        ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (Fin.castSucc a) (Fin.castSucc b) := fun _ _ => rfl
  simp only [GlobalTheory.BZMir.Leib.MirabolicParabolic, GlobalTheory.BZMir.Leib.eGP, Subgroup.mem_comap,
    Subgroup.coe_subtype, GlobalTheory.SmGL.mem_parab_two, hproj]
  constructor
  · intro h b a
    convert h (Fin.castSucc b) a using 2 <;> apply Fin.ext <;>
      simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
  · intro h b a
    induction b using Fin.lastCases with
    | last =>
      have h0 : ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
          (Fin.last (m + j))
          (Fin.castSucc (GlobalTheory.SmGL.stdSum (rfl : m + j = m + j) (Sum.inl a))) = 0 := by
        rw [hlast]
        simp only [GlobalTheory.BZMir.eLast, Pi.single_apply]
        rw [if_neg (Fin.castSucc_lt_last _).ne]
      convert h0 using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]
    | cast b =>
      convert h b a using 2 <;> apply Fin.ext <;>
        simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr]

end GlobalTheory.CompanionTheory.GPMem
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHGPIffParabolicStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_mirabolicParabolic_iff_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (g : Mir k (m + j)), g ∈ MirabolicParabolic k m j ↔ mirabolicProjection k (m + j) g ∈ parab k (two (stdSum (rfl : m + j = m + j))) := by
  first | exact @GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic | exact GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic | (intros; apply GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerCharEqOneOfMemUnipRad
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirJac

section Abstract

variable {M V X Y : Type} [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

theorem ker_comp_mkQ (K₁ K : Submodule ℂ V) (q : (V ⧸ K₁) →ₗ[ℂ] X) (e : LinearMap.ker q = K.map K₁.mkQ)
    (hle : K₁ ≤ K) : LinearMap.ker (q ∘ₗ K₁.mkQ) = K := by
  rw [LinearMap.ker_comp, e, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 hle]

end Abstract

section Iter

variable (k : Type) [Field k]

noncomputable def embedding₂ (n : ℕ) : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (embedding₂ n j)

end Iter

section IterRep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem iterPhi_quotient (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)),
    ∃ q : τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) ∧
      ∀ g v, q (τ.ρ (embedding₂ k n j g) v) = psiMinus k (iterPhi k ψ j τ).ρ g (q v) := by
  intro j
  induction j with
  | zero =>
    intro τ
    exact ⟨Submodule.mkQ _, Submodule.mkQ_surjective _,
      (Submodule.ker_mkQ _).trans (GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ n τ.V τ.ρ), fun _ _ => rfl⟩
  | succ j ih =>
    intro τ
    obtain ⟨q', hs, hk, hi⟩ := ih (MRep.phiM k ψ τ)
    have hnm : n ≤ n + j := Nat.le_add_right n j
    let N₁ := MirUin k (n + j + 1)
    let θ₁ := mirChar k ψ (n + j)
    let N₂ := derUnipM k (n + j) n
    let θ₂ := derCharM k ψ (n + j) n
    let N := derUnipM k (n + j + 1) n
    let θ := derCharM k ψ (n + j + 1) n
    let s := (levi k (n + j + 1)).comp (Mir k (n + j)).subtype
    let K₁ := twKer τ.ρ N₁ θ₁
    let K := twKer τ.ρ N θ
    let L : Submodule ℂ (τ.V ⧸ K₁) :=
      twKer (twAct τ.ρ N₁ θ₁ s (levi_stab ψ (n + j))) N₂ θ₂
    have hle : K₁ ≤ K := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨hu, hθ⟩ := GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm u
      exact Submodule.subset_span ⟨⟨u, hu⟩, v, by rw [hθ]⟩
    have e : L = K.map K₁.mkQ := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro w ⟨a, x, rfl⟩
        induction x using Submodule.Quotient.induction_on with
        | H v =>
          obtain ⟨ha, hθ⟩ := GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm a
          refine ⟨τ.ρ (s a) v - (θ ⟨s a, ha⟩ : ℂ) • v,
            Submodule.subset_span ⟨⟨s a, ha⟩, v, rfl⟩, ?_⟩
          change K₁.mkQ (τ.ρ (s a) v - (θ ⟨s a, ha⟩ : ℂ) • v) =
            K₁.mkQ (τ.ρ (s a) v) - (θ₂ a : ℂ) • K₁.mkQ v
          rw [map_sub, map_smul, hθ]
      · rw [Submodule.map_le_iff_le_comap]
        refine Submodule.span_le.2 ?_
        rintro w ⟨u, v, rfl⟩
        obtain ⟨u₁, a, hu⟩ := GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm u
        obtain ⟨hu₁, hθ₁⟩ := GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm u₁
        obtain ⟨ha, hθ₂⟩ := GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm a
        have hθ : θ u = θ₁ u₁ * θ₂ a := by
          have hu' : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
          rw [hu', map_mul, hθ₁, hθ₂]
        have hdec : τ.ρ (u : Mir k (n + j + 1)) v - (θ u : ℂ) • v =
            (τ.ρ u₁ (τ.ρ (s a) v) - (θ₁ u₁ : ℂ) • τ.ρ (s a) v) +
              (θ₁ u₁ : ℂ) • (τ.ρ (s a) v - (θ₂ a : ℂ) • v) := by
          rw [hθ, hu, map_mul, mul_apply_eq_comp, Units.val_mul, smul_sub, mul_smul]
          abel
        have hz : τ.ρ u₁ (τ.ρ (s a) v) - (θ₁ u₁ : ℂ) • τ.ρ (s a) v ∈ K₁ :=
          Submodule.subset_span ⟨u₁, _, rfl⟩
        have hzero : K₁.mkQ (τ.ρ u₁ (τ.ρ (s a) v) - (θ₁ u₁ : ℂ) • τ.ρ (s a) v) = 0 :=
          (Submodule.Quotient.mk_eq_zero K₁).2 hz
        change K₁.mkQ _ ∈ L
        rw [hdec, map_add, hzero, zero_add, map_smul]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, K₁.mkQ v, ?_⟩)
        change K₁.mkQ (τ.ρ (s a) v - (θ₂ a : ℂ) • v) =
          K₁.mkQ (τ.ρ (s a) v) - (θ₂ a : ℂ) • K₁.mkQ v
        rw [map_sub, map_smul]
    refine ⟨q' ∘ₗ K₁.mkQ, hs.comp K₁.mkQ_surjective, ?_, fun g v => ?_⟩
    · exact ker_comp_mkQ K₁ K q' (hk.trans e) hle
    · exact hi g (K₁.mkQ v)

end IterRep

section Concrete

variable {k : Type} [Field k]

theorem emb_inl_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inl j)) =
      (g.1 : Matrix (Fin n) (Fin n) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inl_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin n) (j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inl {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i : Fin t) (j : Fin n) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem emb_inr_inr {n t N : ℕ} (h : n + t = N) (g : GL (Fin n) k × GL (Fin t) k) (i j : Fin t) :
    (emb₂ k (stdSum h) g : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (g.2 : Matrix (Fin t) (Fin t) k) i j := by
  rw [val_emb₂]
  simp [reindex_apply, submatrix_apply]

theorem one_inr_inr {n t N : ℕ} (h : n + t = N) (i j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inr j)) =
      (1 : Matrix (Fin t) (Fin t) k) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  simp only [Equiv.apply_eq_iff_eq, Sum.inr.injEq]

theorem one_inl_inr {n t N : ℕ} (h : n + t = N) (i : Fin n) (j : Fin t) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inl i)) (stdSum h (Sum.inr j)) = 0 := by
  simp

theorem one_inr_inl {n t N : ℕ} (h : n + t = N) (i : Fin t) (j : Fin n) :
    (1 : Matrix (Fin N) (Fin N) k) (stdSum h (Sum.inr i)) (stdSum h (Sum.inl j)) = 0 := by
  simp

end Concrete

section ConcreteChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end ConcreteChar

section Entries

variable {k : Type} [Field k]

theorem glEmbMat_block_apply {n m : ℕ} (hnm : n ≤ m) (g : Matrix (Fin n) (Fin n) k) (A : Matrix (Fin m) (Fin m) k)
    (hA : ∀ r s : Fin m, A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin m) (Fin m) k) r s) (r s : Fin (m + 1)) :
    glEmbMat k m A r s = if h : (r : ℕ) < n ∧ (s : ℕ) < n then g ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r s := by
  induction r using Fin.lastCases with
  | last =>
    rw [dite_eq_right (fun h => by have := h.1; simp at this; omega)]
    induction s using Fin.lastCases with
    | last => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_last, one_apply_eq]
    | cast s => rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_last_castSucc, one_apply_ne (Fin.castSucc_ne_last s).symm]
  | cast r =>
    induction s using Fin.lastCases with
    | last =>
      rw [dite_eq_right (fun h => by have := h.2; simp at this; omega), GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_last,
        one_apply_ne (Fin.castSucc_ne_last r)]
    | cast s =>
      rw [GlobalTheory.CompanionTheory.BZMirStep.glEmbMat_castSucc_castSucc, hA r s]
      by_cases h : (r : ℕ) < n ∧ (s : ℕ) < n
      · rw [dite_eq_left h, dite_eq_left (by simpa using h)]
        rfl
      · rw [dite_eq_right h, dite_eq_right (by simpa using h)]
        rw [Matrix.one_apply, Matrix.one_apply]
        simp only [Fin.castSucc_inj]

theorem iotaM_apply (n : ℕ) (g : GL (Fin n) k) : ∀ (j : ℕ) (r s : Fin (n + j + 1)),
    (((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s =
      if h : (r : ℕ) < n ∧ (s : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨r, h.1⟩ ⟨s, h.2⟩
      else (1 : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) r s
  | 0, r, s => glEmbMat_block_apply le_rfl (g : Matrix (Fin n) (Fin n) k) (g : Matrix (Fin n) (Fin n) k)
      (fun r s => by rw [dite_eq_left ⟨r.2, s.2⟩]) r s
  | j + 1, r, s => glEmbMat_block_apply (by omega) (g : Matrix (Fin n) (Fin n) k) _ (iotaM_apply n g j) r s

theorem iotaM_eq_emb (n j : ℕ) (g : GL (Fin n) k) :
    ((embedding₂ k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      emb₂ k (stdSum (rfl : n + (j + 1) = n + j + 1)) (g, 1) := by
  apply Units.ext
  ext r s
  rw [iotaM_apply]
  obtain ⟨x, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective r
  obtain ⟨y, rfl⟩ := (stdSum (rfl : n + (j + 1) = n + j + 1)).surjective s
  rcases x with x | x <;> rcases y with y | y
  · rw [emb_inl_inl, dite_eq_left (by simp)]
    congr 1
  · rw [emb_inl_inr, dite_eq_right (by simp), one_inl_inr]
  · rw [emb_inr_inl, dite_eq_right (by simp), one_inr_inl]
  · rw [emb_inr_inr, dite_eq_right (by simp), one_inr_inr]
    rfl

end Entries

end GlobalTheory.CompanionTheory.BZMirJac

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuous
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.BZMir

theorem continuous_gpProj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  intro k _ _ _ _ m j
  have hincl : Continuous (GlobalTheory.BZMir.Leib.hgpIncl k m j) := by
    apply continuous_induced_rng.2
    have hv : Continuous (fun h : GlobalTheory.BZMir.Leib.MirabolicParabolic k m j =>
        ((h : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) := by
      first
        | exact continuous_subtype_val.comp continuous_subtype_val
        | fun_prop
    exact hv
  have hlevi := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ _ _
    (GlobalTheory.BZMir.Leib.eGP m j)).2.2.2.2.2.1
  have hblock := hlevi.comp hincl
  unfold GlobalTheory.BZMir.Leib.gpProj
  rw [MonoidHom.coe_prod]
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_apply false).comp hblock
  · apply continuous_induced_rng.2
    exact (continuous_apply true).comp hblock

end GlobalTheory.CompanionTheory.BZMir
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuousStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_continuous : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | exact GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | (intros; apply GlobalTheory.CompanionTheory.BZMir.continuous_gpProj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightAntitoneOfFiniteDimensionalStable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightAntitoneOfFiniteDimensionalStable
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount

theorem highestWeight_antitone_of_finiteDimensional_stable :
    ∀ {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V)
    (ν : Fin n → ℝ) (v : V), Formalism.REAL.GlRel Kf → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) → v ∈ S → v ≠ 0 →
    Formalism.REAL.KHighest (fun _ => true) Kf ν v → Antitone ν := by
  intro n V _ _ Kf S ν v hG hfd hS hv hv0 hK a b hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.HW.exists_nat_weight_sub_eq_of_highest_vector_in_stable (ε := fun _ => true) (F := Kf)
      (Formalism.REAL.glRel_kRel (fun _ => true) Kf hG) (ne_of_lt hlt) rfl S (fun y hy => hS b a y hy)
      hv hv0 (hK.1 a) (hK.1 b) (hK.2 a b hlt rfl)
    have hm' : ν a - ν b = (m : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact hm
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith

end GlobalTheory.CompanionTheory.RealCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightAntitoneOfFiniteDimensionalStableStatement
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_antitone_alt : ∀ {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V] (Kf : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V)
    (ν : Fin n → ℝ) (v : V), Formalism.REAL.GlRel Kf → FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, Kf a b w ∈ S) → v ∈ S → v ≠ 0 →
    Formalism.REAL.KHighest (fun _ => true) Kf ν v → Antitone ν := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable | exact GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable | (intros; apply GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPow
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPow
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.CentralExp

theorem continuous_scalarGL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ →* GL (Fin n) k) := by
  have hs : Continuous (fun a : k => Matrix.scalar (Fin n) a) := by
    have : (fun a : k => Matrix.scalar (Fin n) a) = fun a => Matrix.diagonal (fun _ => a) := by
      funext a; rfl
    rw [this]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hs.comp Units.continuous_val
  · exact hs.comp (Units.continuous_val.comp continuous_inv)

theorem norm_scalarBy_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), 0 < x.1 → ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy x t c → ‖c‖ = nabs k t ^ ((x.1 : ℝ) * s) := by
  intro k _ _ _ _ x hx
  have hirr := x.2.rep.irr
  obtain ⟨v, hv⟩ : ∃ v : x.2.rep.V, v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI : Subsingleton x.2.rep.V := ⟨fun a b => by rw [hcon a, hcon b]⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Subrepresentation x.rep)
    exact hab (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have huniq : ∀ (t : kˣ) (c c' : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy x t c' → c = c' := by
    intro t c c' h h'
    exact smul_left_injective ℂ hv ((h v).symm.trans (h' v))
  choose f hf using GlobalTheory.T.central_character_exists k x
  have hmul : ∀ a b : kˣ, f (a * b) = f a * f b := by
    intro a b
    refine huniq (a * b) _ _ (hf _) fun w => ?_
    rw [map_mul, map_mul, Module.End.mul_apply, hf b w, map_smul, hf a w, smul_smul, mul_comm]
  have hone : f 1 = 1 := by
    refine huniq 1 _ _ (hf _) fun w => ?_
    simp
  let χ₀ : kˣ →* ℂ := { toFun := f, map_one' := hone, map_mul' := hmul }
  let χ : kˣ →* ℂˣ := χ₀.toHomUnits
  have hχ : ∀ t, ((χ t : ℂˣ) : ℂ) = f t := fun t => rfl
  have hsm : IsSmoothChar χ := by
    have hset : (χ.ker : Set kˣ) = (Matrix.GeneralLinearGroup.scalar (Fin x.1) : kˣ →* GL (Fin x.1) k) ⁻¹'
        {g | x.rep g v = v} := by
      ext t
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq]
      rw [hf t v]
      constructor
      · intro h
        have : f t = 1 := by rw [← hχ, h]; rfl
        rw [this, one_smul]
      · intro h
        have : f t = 1 := smul_left_injective ℂ hv (by simpa using h)
        exact Units.ext (by rw [hχ, this]; rfl)
    show IsOpen (χ.ker : Set kˣ)
    rw [hset]
    exact (x.2.rep.smooth v).preimage (continuous_scalarGL k x.1)
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k χ hsm
  have hn : (x.1 : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  refine ⟨s / x.1, fun t c hc => ?_⟩
  rw [huniq t c (f t) hc (hf t), ← hχ, hs t, mul_div_cancel₀ _ hn]

end GlobalTheory.CompanionTheory.CentralExp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPowStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_norm_eq_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), 0 < x.1 → ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy x t c → ‖c‖ = nabs k t ^ ((x.1 : ℝ) * s) := by
  first | exact @GlobalTheory.CompanionTheory.CentralExp.norm_scalarBy_eq_nabs_rpow | exact GlobalTheory.CompanionTheory.CentralExp.norm_scalarBy_eq_nabs_rpow | (intros; apply GlobalTheory.CompanionTheory.CentralExp.norm_scalarBy_eq_nabs_rpow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotent
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.GpUnip

theorem mirUin_entry (k : Type) [Field k] (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n)
    (a b : Fin (n + 1)) (hb : b ≠ Fin.last n) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b := by
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hu)
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) a b = _
  simp [GlobalTheory.BZMir.colMat, hb]

theorem gpProj_unip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (u : MirabolicParabolic k m j), (u : Mir k (m + j)) ∈ MirUin k (m + j) →
      (gpProj k m j u).1 = 1 ∧ (gpProj k m j u).2 ∈ MirUin k j := by
  intro k _ _ _ _ m j u hu
  have key : ∀ a b : Fin (m + j + 1), b ≠ Fin.last (m + j) →
      (((u : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) a b =
        (1 : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) a b :=
    fun a b hb => GlobalTheory.CompanionTheory.GpUnip.mirUin_entry k (m + j) _ hu a b hb
  have e_inj := (GlobalTheory.BZMir.Leib.eGP m j).injective
  constructor
  · ext i i'
    have h := GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j u) false i i'
    refine h.trans ((key _ _ (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j i')).trans ?_)
    simp only [Matrix.one_apply, e_inj.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Units.val_one]
  · have mem_of_proj (n : ℕ) (y : Mir k n) (hblock : ∀ i j : Fin n,
          ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
            (1 : Matrix (Fin n) (Fin n) k) i j) :
        y ∈ MirUin k n := by
      have hrow : ∀ j, ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
          GlobalTheory.BZMir.eLast k n j :=
        fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (y : GL (Fin (n + 1)) k)).1 y.2) j
      rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
        MonoidHom.mem_range]
      refine ⟨Multiplicative.ofAdd fun i =>
        ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
      apply Units.ext
      ext i j
      change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
        ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
        ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
      rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow,
          GlobalTheory.BZMir.eLast]
      · simp [hrow, GlobalTheory.BZMir.eLast]
    apply mem_of_proj j _
    intro i i'
    have h := GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j u) true (Fin.castSucc i) (Fin.castSucc i')
    have hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i'⟩ ≠ Fin.last (m + j) :=
      fun hl => Fin.castSucc_ne_last i' ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j _).mp hl)
    refine h.trans ((key _ _ hne).trans ?_)
    simp only [Matrix.one_apply, e_inj.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Fin.castSucc_inj, Units.val_one]

end GlobalTheory.CompanionTheory.GpUnip
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (u : MirabolicParabolic k m j), (u : Mir k (m + j)) ∈ MirUin k (m + j) → (gpProj k m j u).1 = 1 ∧ (gpProj k m j u).2 ∈ MirUin k j := by
  first | exact @GlobalTheory.CompanionTheory.GpUnip.gpProj_unip | exact GlobalTheory.CompanionTheory.GpUnip.gpProj_unip | (intros; apply GlobalTheory.CompanionTheory.GpUnip.gpProj_unip <;> assumption)
end
end
