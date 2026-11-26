module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompareIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TypeChangeInjectiveCoefficients
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepOfTraceNondegenerateStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
open Filter Topology

namespace GlobalTheory.ProdThetaConj

theorem exists_ringHom_extend (R K : Type) [Field R] [Countable R] [Field K]
    (hK : Cardinal.mk K ≤ Cardinal.mk ℂ) (i : R →+* K) (j : R →+* ℂ) :
    ∃ s : K →+* ℂ, ∀ x, s (i x) = j x := by
  letI : Algebra R K := i.toAlgebra
  letI : Algebra R ℂ := j.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hct := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht
    Cardinal.mk_le_aleph0 hC
  have hle : Cardinal.mk s ≤ Cardinal.mk t :=
    le_trans (Cardinal.mk_set_le s) (hct ▸ hK)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hle
  have hw : AlgebraicIndependent R (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let S := Algebra.adjoin R (Set.range ((↑) : s → K))
  let φ : S →ₐ[R] ℂ :=
    (MvPolynomial.aeval (((↑) : t → ℂ) ∘ e)).comp hs.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ :=
    (algebraicIndependent_iff_injective_aeval.1 hw).comp hs.1.aevalEquiv.symm.injective
  let _ : Algebra S ℂ := φ.toRingHom.toAlgebra
  have : IsScalarTower R S ℂ := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : FaithfulSMul S ℂ := (faithfulSMul_iff_algebraMap_injective S ℂ).2 hφ
  have : Algebra.IsAlgebraic S K := hs.isAlgebraic
  let ψ : K →ₐ[R] ℂ := (IsAlgClosed.lift : K →ₐ[S] ℂ).restrictScalars R
  exact ⟨ψ.toRingHom, fun x => ψ.commutes x⟩

section General

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
theorem summable_prod_half_pow : Summable fun α : σ →₀ ℕ => ∏ j, (1 / 2 : ℝ) ^ α j := by
  have h : Summable fun α : σ → ℕ => ∏ j, (1 / 2 : ℝ) ^ α j := by
    classical
    refine summable_of_sum_le (c := ∏ _j : σ, (2 : ℝ)) (fun α => by positivity) fun u => ?_
    let n : ℕ := u.sup fun α => Finset.univ.sup α
    have hsub : u ⊆ Fintype.piFinset fun _ : σ => Finset.range (n + 1) := by
      intro α hα
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (Finset.le_sup (f := α) (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun α => Finset.univ.sup α) hα)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
    rw [← Finset.prod_univ_sum (fun _ : σ => Finset.range (n + 1)) (fun _ k => (1 / 2 : ℝ) ^ k)]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun _ _ => sum_geometric_two_le _
  exact h.comp_injective (i := fun α : σ →₀ ℕ => (α : σ → ℕ)) DFunLike.coe_injective

theorem tsum_of_entire {f : (σ → ℂ) → ℂ} (hf : Differentiable ℂ f) (c : (σ →₀ ℕ) → ℂ)
    (hc : ∀ α, (∏ j, ((α j).factorial : ℂ)) * c α = pderivIter α f 0)
    (hc' : ∀ α, c α = MvPowerSeries.coeff α (GlobalTheory.taylor f)) (z : σ → ℂ) :
    ∑' α : σ →₀ ℕ, c α * ∏ j, z j ^ α j = f z := by
  have hb : ∀ R : ℝ, 0 < R → ∃ u : (σ →₀ ℕ) → ℝ, Summable u ∧ ∀ α, ∀ w ∈ Metric.ball (0 : σ → ℂ) R,
      ‖c α * ∏ j, w j ^ α j‖ ≤ u α := by
    intro R hR
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : σ → ℂ) (2 * R)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Metric.mem_closedBall_self (by positivity)))
    refine ⟨fun α => C * ∏ j, (1 / 2 : ℝ) ^ α j, summable_prod_half_pow.mul_left C, fun α w hw => ?_⟩
    have h1 := norm_pderivIter_le_of_differentiable (F := f) (a := 0) (r := fun _ => 2 * R) (M := C) α
      (fun _ => by positivity) (fun _ _ => by positivity) hf (fun y hy => hC y (by
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
        intro k
        simpa using (hy k).le))
    rw [← hc, norm_mul, norm_prod, mul_div_assoc] at h1
    simp only [Complex.norm_natCast] at h1
    have h2 := le_of_mul_le_mul_left h1 (Finset.prod_pos fun k _ => by
      exact_mod_cast Nat.factorial_pos _)
    rw [norm_mul, norm_prod]
    calc ‖c α‖ * ∏ j, ‖w j ^ α j‖ ≤ (C / ∏ k, (2 * R) ^ α k) * ∏ j, R ^ α j := by
          refine mul_le_mul h2 (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_)
            (by positivity) (by positivity)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _)
            ((norm_le_pi_norm w j).trans (mem_ball_zero_iff.1 hw).le) _
      _ = C * ∏ j, (1 / 2 : ℝ) ^ α j := by
          rw [div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib]
          congr 1
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← div_pow]
          congr 1
          field_simp
  have hsum : ∀ w : σ → ℂ, Summable fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j := fun w => by
    obtain ⟨u, hu, h⟩ := hb (‖w‖ + 1) (by positivity)
    exact Summable.of_norm_bounded hu fun α => h α w (by simp)
  have hd : DifferentiableOn ℂ (fun w : σ → ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, w j ^ α j) Set.univ := by
    refine SCV.differentiableOn_tsum_of_locally_normal isOpen_univ (fun α => ?_) fun x _ => ?_
    · apply Differentiable.differentiableOn
      fun_prop
    · obtain ⟨u, hu, h⟩ := hb (‖x‖ + 1) (by positivity)
      exact ⟨_, Metric.isOpen_ball.mem_nhds (by simp), u, hu, h⟩
  have han := SCV.analyticOnNhd_of_differentiableOn isOpen_univ hd 0 (Set.mem_univ _)
  have hfa := SCV.analyticOnNhd_of_differentiable hf Set.univ 0 (Set.mem_univ _)
  have heq := (taylor_eq_iff han hfa).1 (by
    ext α
    rw [← hc']
    exact ConjSeries.coeff_taylor_of_hasSum _ han (Eventually.of_forall fun w => (hsum w).hasSum) α
      (Nat.lt_succ_self _))
  exact SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hd hf.differentiableOn
    (Set.mem_univ 0) heq (Set.mem_univ z)

end General

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped BigOperators

theorem tsum_taylor_mono (D : D7) {N N' : ℕ} {F : VC D N N' → ℂ} (hF : Differentiable ℂ F)
    (z : VC D N N') : ∑' α, Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z = F z := by
  let L := LinearMap.toContinuousLinearMap (GaussCauchy.curry D N N')
  have hc : coordV D = fun k => L (Pi.single k 1) := by
    funext k
    exact (GaussCauchy.curry_single D N N' k).symm
  have han := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)
  have h := tsum_of_entire (f := fun w => F (L w)) (hF.comp L.differentiable)
    (Formalism.MainNotions.TaylorLogMetric.taylor D F) (fun α => by
      have := GaussCauchy.factorial_mul_taylor D N N' F hF α
      rwa [Finsupp.prod_fintype _ _ (by simp)] at this)
    (fun α => by rw [ConjSeries.taylor_eq_coeff, hc, ← taylor_comp_clm L han])
    (fun k => z k.1 k.2.1 k.2.2)
  refine Eq.trans ?_ h
  refine tsum_congr fun α => ?_
  rw [mono, Finsupp.prod_fintype _ _ (by simp)]

theorem exists_endo_eq_cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {S : Set ℂ} (hS : S.Countable) :
    ∃ s : ℂ →+* ℂ, ∀ x ∈ S, x ∈ M → cj M ρ x = s x := by
  let R := IntermediateField.adjoin ℚ (S ∩ (M : Set ℂ))
  have hle : R ≤ M := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  have : Countable R := by
    have h1 : (S ∩ (M : Set ℂ)).Countable := hS.mono Set.inter_subset_left
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le ℚ _).trans ?_
    simp only [sup_le_iff, le_refl, and_true]
    exact ⟨Cardinal.mk_le_aleph0, Cardinal.le_aleph0_iff_set_countable.2 h1⟩
  obtain ⟨s, hs⟩ := exists_ringHom_extend R ℂ le_rfl R.val.toRingHom
    (ρ.comp (IntermediateField.inclusion hle)).toRingHom
  refine ⟨s, fun x hx hM => ?_⟩
  have := hs ⟨x, IntermediateField.subset_adjoin ℚ _ ⟨hx, hM⟩⟩
  simp only [cj, TaylorLogMetric.liftM, dif_pos hM]
  exact this.symm

def ConjPair (D : D7) {N N' : ℕ} (s : ℂ →+* ℂ) (F F' : VC D N N' → ℂ) : Prop :=
  Differentiable ℂ F ∧ Differentiable ℂ F' ∧
    MvPowerSeries.map s (taylorDir (coordV D) F) = taylorDir (coordV D) F'

variable {D : D7} {N N' : ℕ} {s : ℂ →+* ℂ}

theorem an0 {F : VC D N N' → ℂ} (h : Differentiable ℂ F) : AnalyticAt ℂ F 0 :=
  SCV.analyticOnNhd_of_differentiable h Set.univ 0 (Set.mem_univ _)

theorem ConjPair.taylor_eq {F F' : VC D N N' → ℂ} (h : ConjPair D s F F') (α : Mono D N N') :
    s (Formalism.MainNotions.TaylorLogMetric.taylor D F α) = Formalism.MainNotions.TaylorLogMetric.taylor D F' α := by
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← h.2.2, MvPowerSeries.coeff_map]

theorem ConjPair.fnConj_eq {F F' : VC D N N' → ℂ} (h : ConjPair D s F F')
    {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
    (hs : ∀ α, cj M ρ (Formalism.MainNotions.TaylorLogMetric.taylor D F α) = s (Formalism.MainNotions.TaylorLogMetric.taylor D F α)) :
    fnConj D M ρ F = F' := by
  funext z
  rw [← tsum_taylor_mono D h.2.1 z, fnConj]
  refine tsum_congr fun α => ?_
  rw [← h.taylor_eq, ← hs, cj]

theorem taylor_const_mul {F : VC D N N' → ℂ} (h : Differentiable ℂ F) (a : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => a * F z) α = a * Formalism.MainNotions.TaylorLogMetric.taylor D F α := by
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff]
  have := taylorDir_smul (coordV D) a (an0 h)
  rw [show (fun z => a * F z) = a • F from rfl, this, MvPowerSeries.coeff_smul]

theorem ConjPair.const_mul {F F' : VC D N N' → ℂ} (h : ConjPair D s F F') (a : ℂ) :
    ConjPair D s (fun z => a * F z) (fun z => s a * F' z) := by
  refine ⟨h.1.const_mul a, h.2.1.const_mul _, ?_⟩
  ext α
  rw [MvPowerSeries.coeff_map, ← ConjSeries.taylor_eq_coeff, ← ConjSeries.taylor_eq_coeff,
    taylor_const_mul h.1, taylor_const_mul h.2.1, map_mul, h.taylor_eq]

theorem ConjPair.sum {κ : Type*} [Fintype κ] {F F' : κ → VC D N N' → ℂ}
    (h : ∀ i, ConjPair D s (F i) (F' i)) :
    ConjPair D s (fun z => ∑ i, F i z) (fun z => ∑ i, F' i z) := by
  refine ⟨Differentiable.fun_sum fun i _ => (h i).1, Differentiable.fun_sum fun i _ => (h i).2.1, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [taylorDir_sum _ _ fun i _ => an0 (h i).1, taylorDir_sum _ _ fun i _ => an0 (h i).2.1, map_sum]
  exact Finset.sum_congr rfl fun i _ => (h i).2.2

theorem ConjPair.prod {κ : Type*} [Fintype κ] {F F' : κ → VC D N N' → ℂ}
    (h : ∀ i, ConjPair D s (F i) (F' i)) :
    ConjPair D s (fun z => ∏ i, F i z) (fun z => ∏ i, F' i z) := by
  have hp : ∀ G : κ → VC D N N' → ℂ, (∀ i, Differentiable ℂ (G i)) →
      Differentiable ℂ fun z => ∏ i, G i z := fun G hG z =>
    (HasFDerivAt.finsetProd (u := Finset.univ) fun i _ => (hG i z).hasFDerivAt).differentiableAt
  refine ⟨hp _ fun i => (h i).1, hp _ fun i => (h i).2.1, ?_⟩
  rw [taylorDir_prod _ _ fun i _ => an0 (h i).1, taylorDir_prod _ _ fun i _ => an0 (h i).2.1, map_prod]
  exact Finset.prod_congr rfl fun i _ => (h i).2.2

theorem lineDerivList_comp_form {κ : Type*} (u : κ → VC D N N') (ℓ : VC D N N' →ₗ[ℂ] ℂ) (g : ℂ → ℂ)
    (l : List κ) : lineDerivList ℂ (l.map u) (fun z => g (ℓ z)) 0 =
      (l.map fun k => ℓ (u k)).prod * iteratedDeriv l.length g 0 := by
  rw [lineDerivList_comp_linearMap, List.map_map]
  have h1 := lineDerivList_map_smul (fun k => ℓ (u k)) (fun _ => (1 : ℂ)) l g
  have h2 := lineDerivList_replicate l.length (1 : ℂ) g 0 (0 : ℂ)
  simp only [smul_eq_mul, mul_one, List.map_const', zero_add] at h1 h2
  simp only [map_zero, Function.comp_def, h1, h2]

theorem ConjPair.comp_form {g g' : ℂ → ℂ} (hg : Differentiable ℂ g) (hg' : Differentiable ℂ g')
    (hc : ∀ n, s (coef1 g n) = coef1 g' n) (ℓ ℓ' : VC D N N' →ₗ[ℂ] ℂ)
    (hℓ : ∀ k, s (ℓ (coordV D k)) = ℓ' (coordV D k)) :
    ConjPair D s (fun z => g (ℓ z)) (fun z => g' (ℓ' z)) := by
  have h1 : Differentiable ℂ fun z => g (ℓ z) :=
    hg.comp (LinearMap.toContinuousLinearMap ℓ).differentiable
  have h2 : Differentiable ℂ fun z => g' (ℓ' z) :=
    hg'.comp (LinearMap.toContinuousLinearMap ℓ').differentiable
  refine ⟨h1, h2, ?_⟩
  ext α
  have hd : ∀ n, s (iteratedDeriv n g 0) = iteratedDeriv n g' 0 := fun n => by
    have := hc n
    rw [coef1, coef1, map_div₀, map_natCast] at this
    exact (div_left_inj' (by exact_mod_cast n.factorial_ne_zero)).1 this
  rw [MvPowerSeries.coeff_map,
    coeff_taylorDir_eq_lineDerivList _ (an0 h1) (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList _ (an0 h2) (Multiset.coe_toList _),
    lineDerivList_comp_form, lineDerivList_comp_form, map_mul, map_mul, map_inv₀, map_natCast, hd,
    map_list_prod, List.map_map]
  simp only [Function.comp_def, hℓ]

end GlobalTheory.ProdThetaConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLattice
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.MovedTheta

open Matrix GlobalTheory.NormSum.AdLattice

variable {D : D7} {N N' : ℕ}

def mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    Matrix (Fin N') (Fin N) (AE D) :=
  ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
    (g : Matrix (Fin N) (Fin N) (AE D))

theorem mv_zero (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) : mv g g' 0 = 0 := by
  unfold mv
  rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]

theorem mv_add (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (z + w) = mv g g' z + mv g g' w := by
  unfold mv
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]

theorem mv_smul (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (e : D.host.E)
    (z : Matrix (Fin N') (Fin N) D.host.E) : mv g g' (e • z) = inc D e • mv g g' z := by
  unfold mv
  have : (e • z).map (inc D) = inc D e • z.map (inc D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem inc_int (o : 𝓞 D.host.E) : inc D (o : D.host.E) ∈ OhE D :=
  Formalism.UG.P.adelstab_incl_int (F := ℚ) o

theorem mulVec_mem_of_span {R m n : Type} [CommRing R] [Fintype n] {S : Subring R} (M : Matrix m n R) (i : m)
    {T : Set (n → R)} (hT : ∀ u ∈ T, (M *ᵥ u) i ∈ S) {u : n → R} (hu : u ∈ Submodule.span S T) :
    (M *ᵥ u) i ∈ S := by
  induction hu using Submodule.span_induction with
  | mem u hu => exact hT u hu
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mulVec_add]; exact add_mem hu hv
  | smul s u _ hu =>
    have e : s • u = (s : R) • u := rfl
    rw [e, mulVec_smul]
    exact mul_mem s.2 hu

theorem mv_int_of_maps {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : ∀ x ∈ L, A.mulVec x ∈ L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  let Λ := Formalism.UG.stdLat (n := Fin N) (A := D.host.E) (𝓞 D.host.E)
  have hstd (v : Fin N → AE D) :
      v ∈ Formalism.UG.latS (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) (OhE D) Λ ↔
        ∀ i, v i ∈ OhE D := by
    dsimp [Λ, OhE]
    rw [Formalism.UG.P.easyc_latS_std]
    exact Formalism.UG.P.adelstab_mem_stdLat (F := ℚ) (E := D.host.E) v
  have hL : L = Formalism.UG.CS.globLat g Λ := by
    ext x
    exact (h x).trans (hstd _).symm
  have h1 := (Formalism.UG.P.span_recovery_of_integral_adelic_approx
    Formalism.UG.P.csGlob_intAdApprox ℚ D.host.E (Fin N) Λ
    (Formalism.UG.P.standard_lattice_full_holds D.host.E (Fin N)).1
    (Formalism.UG.P.standard_lattice_full_holds D.host.E (Fin N)).2
    g ((g : Matrix (Fin N) (Fin N) (AE D)) *ᵥ Pi.single j 1)).2 (hstd _ |>.2 (by
    intro k
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _))
  have h3 := mulVec_mem_of_span
    (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * A.map (inc D)) i (by
      rintro _ ⟨x, hx, rfl⟩
      have h2 := (h' _).1 (hA x (hL ▸ hx)) i
      have e : (fun j => inc D ((A *ᵥ x) j)) = A.map (inc D) *ᵥ (fun j => inc D (x j)) := by
        ext k; rw [RingHom.map_mulVec]; rfl
      rw [e, mulVec_mulVec] at h2
      exact h2) h1
  rw [mulVec_mulVec, mulVec_single_one] at h3
  exact h3

theorem mv_int_of_hom {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ homL D L L') (i : Fin N') (j : Fin N) : mv g g' A i j ∈ OhE D := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact mv_int_of_maps h h' hA i j
  | zero => rw [mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, mv_smul]
    exact mul_mem (inc_int o) hu

theorem mul_mem_IhE {cc : Ideal (𝓞 D.host.K)} {s y : AE D} (hs : s ∈ OhE D) (hy : y ∈ IhE D cc) :
    s * y ∈ IhE D cc := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * t, mul_mem hs ht, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
  | neg u _ hu => rw [mul_neg]; exact neg_mem hu

theorem mv_mem_IhE {cc : Ideal (𝓞 D.host.K)} {g : GL (Fin N) (AE D)} {g' : GL (Fin N') (AE D)}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L) (h' : Moves D g' L') {c : 𝓞 D.host.K} (hc : c ∈ cc)
    {B : Matrix (Fin N') (Fin N) D.host.E} (hB : B ∈ YYl D L L') (i : Fin N') (j : Fin N) :
    mv g g' (((c : D.host.K) : D.host.E) • B) i j ∈ IhE D cc := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    rw [smul_smul, mv_smul]
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, _, mv_int_of_hom h h' hA i j, rfl⟩
  | zero => rw [smul_zero, mv_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [smul_add, mv_add]; exact add_mem hu hv
  | smul o u _ hu =>
    have e : o • u = (o : D.host.E) • u := rfl
    rw [e, smul_comm, mv_smul]
    exact mul_mem_IhE (inc_int o) hu

theorem pt_zero (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + w) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w := by
  funext τ i j
  simp [pt, embV, tor0, mul_add]

theorem pt_neg (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (-z) = -pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp [pt, embV, tor0]

theorem mv_neg (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mv g g' (-z) = -mv g g' z := by
  rw [← neg_one_smul D.host.E z, mv_smul, map_neg, map_one, neg_one_smul]

end GlobalTheory.NormSum.MovedTheta


open GlobalTheory.NormSum.MovedTheta in
theorem GlobalTheory.NormSum.exists_pt_of_mem_La_moved : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  intro D hG cc δ _ N N' g g' L L' h h' x hx
  let P : VC D N N' → Prop := fun x => ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧
    ∀ i j, mv (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) z i j ∈ IhE D cc
  have h0 : P 0 := ⟨0, (pt_zero cc δ).symm, fun i j => by rw [mv_zero]; exact zero_mem _⟩
  have hadd : ∀ u v, P u → P v → P (u + v) := by
    rintro _ _ ⟨z, rfl, hz⟩ ⟨w, rfl, hw⟩
    exact ⟨z + w, (pt_add cc δ z w).symm, fun i j => by rw [mv_add]; exact add_mem (hz i j) (hw i j)⟩
  have hneg : ∀ u, P u → P (-u) := by
    rintro _ ⟨z, rfl, hz⟩
    exact ⟨-z, (pt_neg cc δ z).symm, fun i j => by rw [mv_neg]; exact neg_mem (hz i j)⟩
  show P x
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    change w ∈ lamOf D cc δ at hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      refine ⟨((c : D.host.K) : D.host.E) • A, ?_, mv_mem_IhE h h' hc hA⟩
      funext τ i j
      have e := hG.1 τ (c : D.host.K)
      simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [e, mul_assoc]
    | zero => rw [zero_smul]; exact h0
    | add u v _ _ hu hv => rw [add_smul]; exact hadd _ _ hu hv
    | neg u _ hu => rw [neg_smul]; exact hneg _ hu
  | zero => exact h0
  | add u v _ _ hu hv => exact hadd _ _ hu hv
  | neg u _ hu => exact hneg _ hu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc := by
  first | exact @GlobalTheory.NormSum.exists_pt_of_mem_La_moved | exact GlobalTheory.NormSum.exists_pt_of_mem_La_moved | (intros; apply GlobalTheory.NormSum.exists_pt_of_mem_La_moved <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Nat

namespace GlobalTheory.IdealIdele

theorem pow_factorial_mul {M : Type} [Monoid M] [Fintype M] (a : M) (t : ℕ) (ht : 0 < t) :
    a ^ ((Fintype.card M)! * t) = a ^ (Fintype.card M)! := by
  obtain ⟨i, j, hij, hj, e⟩ : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card M ∧ a ^ i = a ^ j := by
    obtain ⟨i, j, hne, e⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card M + 1) => a ^ (i : ℕ)) (by simp)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, Nat.lt_succ_iff.1 j.2, e⟩
    · exact ⟨j, i, h, Nat.lt_succ_iff.1 i.2, e.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  have hd : 0 < d := by omega
  have key : ∀ u : ℕ, a ^ (i + d * u) = a ^ i := by
    intro u
    induction u with
    | zero => simp
    | succ u ih => rw [Nat.mul_succ, ← add_assoc, pow_add, ih, ← pow_add, ← e]
  obtain ⟨c, hc⟩ : d ∣ (Fintype.card M)! := Nat.dvd_factorial hd (by omega)
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le
    (show i ≤ (Fintype.card M)! from le_trans (by omega) (Nat.self_le_factorial _))
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  have : (Fintype.card M)! * t.succ = i + d * (c * t) + s := by
    rw [Nat.mul_succ, ← mul_assoc, ← hc]; omega
  rw [this, pow_add, key, ← pow_add, ← hs]

theorem int_dvd_pow_sub (m N t : ℕ) (hN : 0 < N) (ht : 0 < t) :
    ∃ c : ℤ, (m : ℤ) ^ (N ! * t) = (m : ℤ) ^ N ! + N * c := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h := pow_factorial_mul (m : ZMod N) t ht
  rw [ZMod.card] at h
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((m : ℤ) ^ (N ! * t) - (m : ℤ) ^ N !) N).1
    (by push_cast; rw [h, sub_self])
  exact ⟨c, by linear_combination hc⟩

section Abstract

variable {A : Type} [CommRing A] (S : Subring A)

theorem exists_idem
    (hsep : ∀ y : A, (∀ N : ℕ, 0 < N → ∃ w ∈ S, y = (N : A) * w) → y = 0)
    (hcpl : ∀ x : ℕ → A, (∀ N, x N ∈ S) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ S, x (N * m) = x N + (N : A) * w) →
      ∃ y ∈ S, ∀ N : ℕ, 0 < N → ∃ w ∈ S, y = x N + (N : A) * w)
    (m : ℕ) (hm : 0 < m) :
    ∃ f ∈ S, f * f = f ∧ (∃ w ∈ S, f = (m : A) * w) ∧
      ∀ n : ℕ, 0 < n → m.Coprime n → ∃ w ∈ S, 1 - f = (n : A) * w := by
  have hc : ∀ N t : ℕ, 0 < N → 0 < t →
      ∃ c : ℤ, (m : A) ^ (N ! * t) = (m : A) ^ N ! + N * c := fun N t hN ht => by
    obtain ⟨c, h⟩ := int_dvd_pow_sub m N t hN ht
    refine ⟨c, ?_⟩
    have := congrArg (Int.cast : ℤ → A) h
    push_cast at this
    exact this
  have hx : ∀ k : ℕ, (m : A) ^ k ∈ S := fun k => pow_mem (natCast_mem S m) k
  obtain ⟨f, hf, h⟩ := hcpl (fun N => (m : A) ^ N !) (fun N => hx _) (by
    intro N k hN hk
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right N hk)
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by
      rintro rfl
      exact (Nat.factorial_ne_zero _) (by simpa using ht))
    obtain ⟨c, hc⟩ := hc N t hN ht0
    exact ⟨c, intCast_mem S c, by simp only [ht, hc]⟩)
  refine ⟨f, hf, ?_, ?_, fun n hn hmn => ?_⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨c, hc⟩ := hc N 2 hN two_pos
    refine ⟨c + (2 * (m : A) ^ N ! * w + N * w * w - w), ?_, ?_⟩
    · exact add_mem (intCast_mem S c) (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (hx _)) hw)
        (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
    · rw [pow_mul] at hc
      rw [hh]; linear_combination hc
  · obtain ⟨w, hw, hh⟩ := h m hm
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero m)
    refine ⟨(m : A) ^ s + w, add_mem (hx s) hw, ?_⟩
    rw [hh, hs, pow_succ]; ring
  · obtain ⟨w, hw, hh⟩ := h n hn
    obtain ⟨t, ht⟩ := Nat.dvd_factorial (Nat.totient_pos.2 hn) (Nat.totient_le n)
    have h1 : m ^ n ! ≡ 1 [MOD n] := by
      have := (Nat.ModEq.pow_totient hmn).pow t
      rwa [← pow_mul, ← ht, one_pow] at this
    obtain ⟨c, hc⟩ := h1.dvd
    have hc' := congrArg (Int.cast : ℤ → A) hc
    push_cast at hc'
    refine ⟨c - w, sub_mem (intCast_mem S c) hw, ?_⟩
    rw [hh]; linear_combination hc'

end Abstract

theorem exists_local_generator {E : Type} [Field E] [NumberField E] (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    ∃ (m n : ℕ) (β : 𝓞 E), 0 < m ∧ 0 < n ∧ m.Coprime n ∧ (m : 𝓞 E) ∈ B ∧ β ∈ B ∧ β ≠ 0 ∧
      ∀ b ∈ B, β ∣ (n : 𝓞 E) * b := by
  set m := 2 * Ideal.absNorm B with hm
  have hN : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hB)
  have hm2 : 2 ≤ m := by omega
  have hmB : (m : 𝓞 E) ∈ B := by
    rw [hm, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem B)
  have hm0 : (m : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨β, hβ⟩ := IsDedekindDomain.exists_sup_span_eq (I := B * Ideal.span {(m : 𝓞 E)}) (J := B)
    Ideal.mul_le_left (mul_ne_zero hB (by simpa using hm0))
  have hβB : β ∈ B := hβ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self β)
  obtain ⟨C, hC⟩ : B ∣ Ideal.span {β} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hβB)
  have hsup : Ideal.span {(m : 𝓞 E)} ⊔ C = ⊤ := by
    apply mul_left_cancel₀ hB
    rw [Ideal.mul_sup, ← hC, hβ, Ideal.mul_top]
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq, Ideal.span_singleton_eq_top] at hsup
    have h1 := Ideal.absNorm_eq_one_iff.2 (Ideal.span_singleton_eq_top.2 hsup)
    rw [Ideal.absNorm_span_natCast] at h1
    have h2 := (Nat.pow_eq_one.1 h1).resolve_left (by omega)
    exact Module.finrank_pos.ne' h2
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hB hC0 (by rw [← hC]; simp)
  haveI : Finite (𝓞 E ⧸ C) := Ideal.finiteQuotientOfFreeOfNeBot C hC0
  have hu : IsUnit (Ideal.Quotient.mk C (m : 𝓞 E)) := by
    obtain ⟨x, hx, c, hc, e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk C a) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk C), Ideal.Quotient.eq]
    rw [show (m : 𝓞 E) * a - 1 = -c by linear_combination e]
    exact neg_mem hc
  obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hu.unit)
  have e' : (m : 𝓞 E) ^ k - 1 ∈ C := by
    rw [← Ideal.Quotient.eq, map_pow, map_one]
    simpa using congrArg Units.val e
  have h1 : 1 < m ^ k := Nat.one_lt_pow hk.ne' (by omega)
  refine ⟨m, m ^ k - 1, β, by omega, by omega, ?_, hmB, hβB, hβ0, fun b hb => ?_⟩
  · refine Nat.Coprime.of_dvd_left (dvd_pow_self m hk.ne') ?_
    exact (Nat.coprime_self_sub_right h1.le).2 (Nat.coprime_one_right _)
  · rw [← Ideal.mem_span_singleton, hC, mul_comm (((m ^ k - 1 : ℕ)) : 𝓞 E)]
    refine Ideal.mul_mem_mul hb ?_
    rw [Nat.cast_sub h1.le]
    push_cast
    exact e'

theorem exists_idele_generator : ∀ (D : D7) (B : Ideal (𝓞 D.host.E)), B ≠ ⊥ → ∃ y : (AE D)ˣ, (∀ b ∈ B, ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (b : D.host.E) ∈ OhE D) ∧ ∃ (k : ℕ) (b : Fin k → 𝓞 D.host.E) (w : Fin k → AE D), (∀ i, b i ∈ B) ∧ (∀ i, w i ∈ OhE D) ∧ (y : AE D) = ∑ i, inc D (b i : D.host.E) * w i := by
  intro D B hB
  obtain ⟨m, n, β, hm, hn, hmn, hmB, hβB, hβ0, hdvd⟩ := exists_local_generator B hB
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := exists_idem (OhE D) hsep hcpl m hm
  obtain ⟨v, hv, hfv⟩ := h3 n hn hmn
  have hint : ∀ b : 𝓞 D.host.E, inc D (b : D.host.E) ∈ OhE D := fun b =>
    (GlobalTheory.HeckeVal.inc_mem_iff D _).2 b.isIntegral_coe
  have hβE : (β : D.host.E) ≠ 0 := by simpa using hβ0
  have hinv : inc D (β : D.host.E) * inc D (β : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hβE, map_one]
  have hy : ((1 - f) * inc D (β : D.host.E) + f) * ((1 - f) * inc D (β : D.host.E)⁻¹ + f) = 1 := by
    linear_combination (1 - f) ^ 2 * hinv +
      (2 - inc D (β : D.host.E) - inc D (β : D.host.E)⁻¹) * hff
  refine ⟨⟨_, _, hy, by rw [mul_comm, hy]⟩, fun b hb => ?_, 2, ![β, m], ![1 - f, w], ?_, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hdvd b hb
    have hd' : (n : AE D) * inc D (b : D.host.E) = inc D (β : D.host.E) * inc D (d : D.host.E) := by
      rw [← map_natCast (inc D), ← map_mul, ← map_mul]
      congr 1
      exact_mod_cast congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hd
    change ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) ∈ OhE D
    rw [show ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) =
      v * inc D (d : D.host.E) + f * inc D (b : D.host.E) by
        rw [hfv]
        linear_combination v * inc D (β : D.host.E)⁻¹ * hd' + v * inc D (d : D.host.E) * hinv]
    exact add_mem (mul_mem hv (hint d)) (mul_mem hf (hint b))
  · intro i
    fin_cases i
    · exact hβB
    · exact hmB
  · intro i
    fin_cases i
    · exact sub_mem (one_mem _) hf
    · exact hw
  · have : inc D (((m : 𝓞 D.host.E)) : D.host.E) = (m : AE D) := by
      rw [← map_natCast (inc D)]; congr 1
    change (1 - f) * inc D (β : D.host.E) + f = _
    rw [Fin.sum_univ_two]
    change _ = inc D (β : D.host.E) * (1 - f) + inc D (((m : 𝓞 D.host.E)) : D.host.E) * w
    rw [this, ← hfw]; ring

end GlobalTheory.IdealIdele
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormSpanRepNondegenerateMapRepIff
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormSpanRepNondegenerateMapRepIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory

section TraceFormSpan

variable {ι K L : Type} [Field K] [Field L] [Algebra K L] {a : ℕ}

theorem map_mem_span_map_of_mem_span (A : ι → Matrix (Fin a) (Fin a) K)
    {x : Matrix (Fin a) (Fin a) K} (hx : x ∈ Submodule.span K (Set.range A)) :
    x.map (algebraMap K L) ∈
      Submodule.span L (Set.range fun g => (A g).map (algebraMap K L)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    rw [Matrix.map_zero _ (map_zero _)]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have : (c • y).map (algebraMap K L) = algebraMap K L c • y.map (algebraMap K L) := by
      ext i j; simp
    rw [this]
    exact Submodule.smul_mem _ _ hy

theorem map_linearForm_mem_span_of_mem_span_map (A : ι → Matrix (Fin a) (Fin a) K)
    {y : Matrix (Fin a) (Fin a) L}
    (hy : y ∈ Submodule.span L (Set.range fun g => (A g).map (algebraMap K L)))
    (φ : L →ₗ[K] K) : y.map φ ∈ Submodule.span K (Set.range A) := by
  induction hy using Submodule.span_induction generalizing φ with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    have : ((A g).map (algebraMap K L)).map φ = φ 1 • A g := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
      rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm]
    beta_reduce
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _)]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact Submodule.add_mem _ (hy φ) (hz φ)
  | smul c y _ hy =>
    have : (c • y).map φ = y.map (φ ∘ₗ LinearMap.mulLeft K c) := by
      ext i j; simp
    rw [this]
    exact hy _

theorem trace_map_linearForm_mul (φ : L →ₗ[K] K) (y : Matrix (Fin a) (Fin a) L)
    (m : Matrix (Fin a) (Fin a) K) :
    (y.map φ * m).trace = φ ((y * m.map (algebraMap K L)).trace) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (y i j), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem traceForm_span_nondegenerate_map_iff (A : ι → Matrix (Fin a) (Fin a) K) :
    (∀ x ∈ Submodule.span L (Set.range fun g => (A g).map (algebraMap K L)),
      (∀ g, (x * (A g).map (algebraMap K L)).trace = 0) → x = 0) ↔
    (∀ x ∈ Submodule.span K (Set.range A), (∀ g, (x * A g).trace = 0) → x = 0) := by
  constructor
  · intro h x hx htr
    have h0 := h _ (map_mem_span_map_of_mem_span A hx) fun g => by
      rw [← Matrix.map_mul, ← AddMonoidHom.map_trace, htr g, map_zero]
    ext i j
    have := congrFun (congrFun h0 i) j
    simpa using this
  · intro h y hy htr
    ext i j
    refine (Module.forall_dual_apply_eq_zero_iff K _).1 fun φ => ?_
    have h0 := h _ (map_linearForm_mem_span_of_mem_span_map A hy φ) fun g => by
      rw [trace_map_linearForm_mul, htr g, map_zero]
    simpa using congrFun (congrFun h0 i) j

end TraceFormSpan

theorem traceForm_span_rep_nondegenerate_mapRep_iff :
    ∀ (Γ K L : Type) [Group Γ] [Field K] [Field L] (f : K →+* L) (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span L (Set.range fun g => ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)), (∀ g, (x * ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)).trace = 0) → x = 0) ↔ (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  intro Γ K L _ _ _ f a ρ
  letI := f.toAlgebra
  exact traceForm_span_nondegenerate_map_iff (L := L)
    (fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormSpanRepNondegenerateMapRepIffStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff : ∀ (Γ K L : Type) [Group Γ] [Field K] [Field L] (f : K →+* L) (a : ℕ) (ρ : Γ →* GL (Fin a) K), (∀ x ∈ Submodule.span L (Set.range fun g => ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)), (∀ g, (x * ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)).trace = 0) → x = 0) ↔ (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  first | exact @GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff | exact GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff | (intros; apply GlobalTheory.traceForm_span_rep_nondegenerate_mapRep_iff <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions

namespace GlobalTheory.TwistedSelmerCompare

theorem isSSRep_map_iff {Γ K L : Type} [Group Γ] [Field K] [Field L] [CharZero K] [CharZero L] (f : K →+* L)
    {a : ℕ} (ρ : Γ →* GL (Fin a) K) : IsSSRep (mapRep f ρ) ↔ IsSSRep ρ :=
  ⟨fun h => GlobalTheory.T.isSSRep_of_trace_nondegenerate' Γ K a ρ ((GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff Γ K L f a ρ).1 (GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep Γ L a _ h)),
    fun h => GlobalTheory.T.isSSRep_of_trace_nondegenerate' Γ L a _ ((GlobalTheory.T.traceForm_nondegenerate_span_mapRep_iff Γ K L f a ρ).2 (GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep Γ K a ρ h))⟩

section Param

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem speh_twist (p : Part A.CG) (χ : A.CG 1) (w : PlE H) (c : ℂ) (hp : A.unr (A.locG p.π w))
    (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (spehLoc N A p w) ∧ A.unr (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) ∧
      A.frobEig (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) = (A.frobEig (spehLoc N A p w)).map (· * c) := by
  have hd := A.locG_dim χ w
  have hp' : A.unr (A.locG (A.tw p.π χ) w) := by rw [A.locG_tw]; exact A.unr_char _ _ hd hp hχ
  have he : A.frobEig (A.locG (A.tw p.π χ) w) = (A.frobEig (A.locG p.π w)).map (· * c) := by
    rw [A.locG_tw]; exact A.frobEig_char _ _ c hp hχ hd hc
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    simp only [List.foldr_cons]
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp, i1⟩, (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 hp', i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp') i2, A.frobEig_sum _ _ ((A.unr_tw _ _).2 hp) i1, i3,
      A.frobEig_tw _ _ hp, A.frobEig_tw _ _ hp', he, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    congr 2
    funext x
    simp only [Function.comp_apply]
    ring

theorem iso_twist (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) (c : ℂ)
    (hS : ∀ p ∈ S, A.unr (A.locG p.π w)) (hχ : A.unr (A.locG χ w)) (hc : A.frobEig (A.locG χ w) = {c}) :
    A.unr (isoLoc N A S w) ∧ A.unr (isoLoc N A (twistIso N A S χ) w) ∧
      A.frobEig (isoLoc N A (twistIso N A S χ) w) = (A.frobEig (isoLoc N A S w)).map (· * c) := by
  induction S with
  | nil => exact ⟨A.lpZero_unr w, A.lpZero_unr w, by simp [isoLoc, twistIso, A.frobEig_zero]⟩
  | cons p S ih =>
    obtain ⟨i1, i2, i3⟩ := ih fun q hq => hS q (List.mem_cons_of_mem _ hq)
    obtain ⟨j1, j2, j3⟩ := speh_twist N A p χ w c (hS p List.mem_cons_self) hχ hc
    change A.unr (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) ∧
      A.unr (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) ∧
      A.frobEig (A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w)) =
        (A.frobEig (A.lpSum (spehLoc N A p w) (isoLoc N A S w))).map (· * c)
    refine ⟨(A.unr_sum _ _).2 ⟨j1, i1⟩, (A.unr_sum _ _).2 ⟨j2, i2⟩, ?_⟩
    rw [A.frobEig_sum _ _ j2 i2, A.frobEig_sum _ _ j1 i1, i3, j3, Multiset.map_add (f := _)]

theorem galPol_twist (S : List (Part A.CG)) (t : ℝ) : ∀ᶠ w in Filter.cofinite,
    galPol A (A.lpTw (A.lpChar (isoLoc N A S w) (A.locG A.etaTinv w)) t) =
      galPol A (A.lpTw (isoLoc N A (twistIso N A S A.etaTinv) w) t) := by
  have h : ∀ᶠ w in Filter.cofinite, ∀ p ∈ {p | p ∈ S}, A.unr (A.locG p.π w) :=
    (Filter.eventually_all_finite (List.finite_toSet S)).2 fun p _ => A.locG_unr_ae p.π
  filter_upwards [h] with w hw
  have hχ := (A.etaTinv_def w).1
  have hd := A.locG_dim A.etaTinv w
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 ((A.frobEig_card _ hχ).trans hd)
  obtain ⟨i1, i2, i3⟩ := iso_twist N A S _ w c hw hχ hc
  unfold galPol
  rw [A.frobEig_tw _ _ i2, A.frobEig_tw _ _ (A.unr_char _ _ hd i1 hχ), i3, A.frobEig_char _ _ c i1 hχ hd hc]

theorem splitOut_ae (a : N.Loc) : ∀ᶠ w in Filter.cofinite, (SplitOut N a w ↔ IsSplitPl H w) := by
  have h1 : (placesOver H.E (N.l a)).Finite := by
    have h0 : Ideal.span {((N.l a : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (N.lPrime a).out.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    simpa [Ideal.dvd_span_singleton, placesOver] using hv
  filter_upwards [h1.compl_mem_cofinite, (N.S a).eventually_cofinite_notMem,
    (N.Q a).eventually_cofinite_notMem] with w a1 a2 a3
  exact ⟨fun h => h.1, fun h => ⟨h, a1, a2, a3⟩⟩

end Param

variable (D : D7)

theorem triple_iff (a : D.nd.Loc) (σ : D.what₂.FT) (Sg : List (Part D.naut.CG))
    (h : HasParamW D.nd D.naut a σ Sg) (s : TwistedTriples.Trip D a) : TwistedTriples.IsTripleOf D a σ s ↔ IsTriple D a s Sg := by
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · have : CharZero (FractionRing (D.nd.O a)) :=
      ((D.nd.embK a).charZero_iff (D.nd.embK a).injective).1 inferInstance
    have : CharZero (FractionRing (D.ntw.O0 (D.ntw.twOf a))) :=
      ((D.ntw.emb0 _).charZero_iff (D.ntw.emb0 _).injective).1 inferInstance
    rw [← isSSRep_map_iff (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a))]
    have : mapRep (algebraMap (D.nd.O a) (Kf D.nd a)) (TwistedTriples.rhoTrip D a s) =
        mapRep (fracMap (D.ntw.twist₂ a) (twO_inj D.ntw a)) (mapRep (algebraMap (D.ntw.O0 (D.ntw.twOf a))
          (FractionRing (D.ntw.O0 (D.ntw.twOf a)))) (D.ntw.rhoS _ s)) := by
      ext g i j
      exact (fracMap_alg _ (twO_inj D.ntw a) _).symm
    rw [this]
  · refine Filter.eventually_congr ?_
    filter_upwards [galPol_twist D.nd D.naut Sg ((1 - (D.R.nV : ℝ)) / 2), splitOut_ae D.nd a] with w h1 h2
    rw [h2]
    refine forall_congr' fun hw => forall_congr' fun B => forall_congr' fun g => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    rw [← h1, h.2.2 w hw, ← Polynomial.map_map, ← Matrix.charpoly_map _ (D.ntw.twist₂ a)]
    rfl

theorem allTriples_of_tripAll (h : TwistedTriples.TripAll D) : AllTriples D := fun a σ Sg hg hp =>
  (h a σ hg.symm).imp fun s hs => (triple_iff D a σ Sg hp s).1 hs

end GlobalTheory.TwistedSelmerCompare

end
end
