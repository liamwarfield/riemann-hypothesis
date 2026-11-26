module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatOpen

open GlobalTheory.LatVac Topology

theorem isOpen_of_nhds {G G' : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [AddCommGroup G'] (φ : G →+ G') (L : AddSubgroup G) (N : ℕ) (U : Set G) (hU : U ∈ 𝓝 0)
    (h : ∀ x ∈ U, ∃ l ∈ L, φ (x - N • l) = 0) : IsOpen {x : G | ∃ l ∈ L, φ (x - N • l) = 0} := by
  let H : AddSubgroup G :=
    { carrier := {x : G | ∃ l ∈ L, φ (x - N • l) = 0}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨l, hl, e⟩ ⟨l', hl', e'⟩
        refine ⟨l + l', L.add_mem hl hl', ?_⟩
        rw [show x + y - N • (l + l') = (x - N • l) + (y - N • l') by rw [nsmul_add]; abel, map_add (f := _), e, e', add_zero]
      neg_mem' := by
        rintro x ⟨l, hl, e⟩
        refine ⟨-l, L.neg_mem hl, ?_⟩
        rw [show -x - N • (-l) = -(x - N • l) by rw [neg_nsmul]; abel, map_neg, e, neg_zero] }
  exact H.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU h)

theorem isOpen_intAf (F : Type) [Field F] [NumberField F] : IsOpen (intAf F) :=
  RestrictedProduct.isOpen_forall_mem (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun v => Valued.isOpen_valuationSubring _

theorem zero_mem_intAf (F : Type) [Field F] [NumberField F] : (0 : Af F) ∈ intAf F :=
  fun v => zero_mem (v.adicCompletionIntegers F)

variable {D : D7}

theorem finPart_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι D.host.F D.host.E) (z : AE D) :
    finPart D z = ∑ k, sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) b).coord k z) ⊗ₜ[D.host.F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) b).sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show ∀ y, finPart D y = (finPart D).toAddMonoidHom y from fun _ => rfl, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show finPart D _ = _
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem nsmul_tmul_cancel {F A E : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [AddCommGroup E] [Module F E]
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (a : A) (e : E) :
    N • ((algebraMap F A ((N * M : ℕ) : F)⁻¹ * a) ⊗ₜ[F] (M • e)) = a ⊗ₜ[F] e := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', smul_smul, smul_smul, Nat.cast_mul, mul_inv_cancel₀ (mul_ne_zero hN' hM'), one_smul]

private theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := fun V Λ hΛ => _root_.DedupShared.selfDual_isFullLattice V Λ hΛ


theorem isOpen_nsmul_latO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N → IsOpen {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - N • l).map (finPart D) = 0} := by
  intro D S T ΛS ΛT hS hT N hN
  classical
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  choose M hM hMl using fun p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) =>
    GlobalTheory.T.scaled_matrix_mem_rational_lattice D S T ΛS ΛT (selfDual_isFullLattice S ΛS hS) (selfDual_isFullLattice T ΛT hT) (Matrix.single p.1 p.2.1 (b p.2.2))
  let f : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) → WO S T → Af D.host.F := fun p x =>
    algebraMap D.host.F (Af D.host.F) ((N * M p : ℕ) : D.host.F)⁻¹ * sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1))
  have hf : ∀ p, Continuous (f p) := fun p => by
    have h1 : Continuous (B.coord p.2.2) := IsModuleTopology.continuous_of_linearMap _
    have h2 : Continuous (sndA D.host.F) := continuous_snd
    exact continuous_const.mul (h2.comp (h1.comp ((continuous_apply p.2.1).comp (continuous_apply p.1))))
  have hf0 : ∀ p, f p 0 = 0 := fun p => by
    show _ * sndA D.host.F (B.coord p.2.2 0) = 0
    rw [LinearMap.map_zero, map_zero, mul_zero]
  let φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finPart D).toAddMonoidHom.mapMatrix
  refine isOpen_of_nhds φ _ N (⋂ p, f p ⁻¹' intAf D.host.F) ?_ ?_
  · refine Filter.iInter_mem.2 fun p => ((isOpen_intAf _).preimage (hf p)).mem_nhds ?_
    show f p 0 ∈ intAf D.host.F
    rw [hf0]; exact zero_mem_intAf _
  · intro x hx
    refine ⟨∑ p, finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)),
      AddSubgroup.sum_mem _ fun p _ => finTens_mem_latO (Set.mem_iInter.1 hx p) (hMl p), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AddMonoidHom.map_sub, AddMonoidHom.map_nsmul, sub_eq_zero, map_sum, ← Finset.sum_nsmul]
    ext i j
    rw [Matrix.sum_apply]
    have e : ∀ p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E),
        (N • φ (finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)))) i j =
        sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1)) ⊗ₜ[D.host.F] (Matrix.single p.1 p.2.1 (b p.2.2) i j) :=
      fun p => nsmul_tmul_cancel hN (hM p) _ _
    rw [Finset.sum_congr rfl fun p _ => e p, Fintype.sum_prod_type, Finset.sum_eq_single i, Fintype.sum_prod_type,
      Finset.sum_eq_single j]
    · simp only [Matrix.single_apply_same]
      exact finPart_eq_sum b (x i j)
    · intro j' _ hj
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_col_ne _ _ hj, TensorProduct.tmul_zero]
    · simp
    · intro i' _ hi
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_row_ne hi, TensorProduct.tmul_zero]
    · simp

end GlobalTheory.LatOpen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_nsmul_completedHomLattice_finiteAdelic : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N → IsOpen {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - N • l).map (finPart D) = 0} := by
  first | exact @GlobalTheory.LatOpen.isOpen_nsmul_latO | exact GlobalTheory.LatOpen.isOpen_nsmul_latO | (intros; apply GlobalTheory.LatOpen.isOpen_nsmul_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology ENNReal

namespace GlobalTheory.WeilVacMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Filter

section Abstract

theorem ae_zero_of_lintegral_eq {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (a b : ℕ → X → ℂ) (c : X → ℂ) (C : ℝ) (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (hc : Measurable c) (hC : ∀ n x, ‖a n x‖ ≤ C) (ha0 : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 0))
    (hbc : ∀ x, Tendsto (fun n => b n x) atTop (𝓝 (c x)))
    (he : ∀ n, ∫⁻ x, ‖b n x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν) : ∀ᵐ x ∂ν, c x = 0 := by
  have hq : Continuous fun z : ℂ => ‖z‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp continuous_enorm
  have h1 : Tendsto (fun n => ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν) atTop (𝓝 (∫⁻ _, 0 ∂ν)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal C ^ 2)
      (fun n => hq.measurable.comp (ha n)) (fun n => Eventually.of_forall fun x => ?_) ?_
      (Eventually.of_forall fun x => ?_)
    · refine pow_le_pow_left' ?_ 2
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC n x)
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
    · simpa [Function.comp_def] using (hq.tendsto 0).comp (ha0 x)
  rw [lintegral_zero] at h1
  have h2 : ∫⁻ x, ‖c x‖ₑ ^ 2 ∂ν ≤ 0 := by
    have e : ∀ x, ‖c x‖ₑ ^ 2 = liminf (fun n => ‖b n x‖ₑ ^ 2) atTop := fun x =>
      ((hq.tendsto _).comp (hbc x)).liminf_eq.symm
    simp_rw [e]
    refine (lintegral_liminf_le fun n => hq.measurable.comp (hb n)).trans ?_
    have e2 : (fun n => ∫⁻ x, ((fun z : ℂ => ‖z‖ₑ ^ 2) ∘ b n) x ∂ν) = fun n => ∫⁻ x, ‖a n x‖ₑ ^ 2 ∂ν := funext he
    rw [e2]
    exact h1.liminf_eq.le
  have h3 := (lintegral_eq_zero_iff (hq.measurable.comp hc)).1 (le_antisymm h2 zero_le')
  filter_upwards [h3] with x hx
  simpa using hx

theorem eq_zero_of_ae_fundamentalDomain {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (c : G → ℂ)
    (hc : Continuous c) (hp : ∀ γ ∈ Γ, ∀ w, ‖c (γ + w)‖ = ‖c w‖) (h0 : ∀ᵐ x ∂μ.restrict 𝓕, c x = 0) : c = 0 := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have ho : IsOpen {x | c x ≠ 0} := isOpen_ne_fun hc continuous_const
  have h1 : μ {x | c x ≠ 0} = 0 := by
    refine h𝓕.measure_zero_of_invariant _ (fun g => ?_) ?_
    · ext x
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      show c (((-g : Γ) : G) + x) ≠ 0 ↔ c x ≠ 0
      rw [← norm_ne_zero_iff, hp _ (-g).2, norm_ne_zero_iff]
    · rw [← Measure.restrict_apply ho.measurableSet]
      exact h0
  funext x
  by_contra hx
  exact (ho.measure_pos μ ⟨x, hx⟩).ne' h1

theorem tendsto_diffQuot {F : ℝ → ℂ} {d : ℂ} (h : HasDerivAt F d 0) :
    Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ * (F (1 / ((n : ℝ) + 1)) - F 0)) atTop (𝓝 d) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n =>
      (Nat.one_div_pos_of_nat (n := n)).ne'⟩
  refine (h.tendsto_slope_zero.comp h1).congr fun n => ?_
  simp only [Function.comp_apply, zero_add, Complex.real_smul, Complex.ofReal_inv]

theorem norm_diffQuot_le {F F' : ℝ → ℂ} {C : ℝ} (h : ∀ s, HasDerivAt F (F' s) s) (hC : ∀ s, ‖F' s‖ ≤ C) (t : ℝ)
    (ht : t ≠ 0) : ‖(t : ℂ)⁻¹ * (F t - F 0)‖ ≤ C := by
  have h1 := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F) (f' := F') (C := C)
    (fun s _ => (h s).hasDerivWithinAt) (fun s _ => hC s) (Set.mem_univ 0) (Set.mem_univ t)
  rw [sub_zero] at h1
  rw [norm_mul, norm_inv, Complex.norm_real, inv_mul_le_iff₀ (norm_pos_iff.2 ht), mul_comm]
  exact h1

end Abstract

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem norm_periodic (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
  rintro _ ⟨γ, rfl⟩ w
  have := hf.quasi γ w
  exact (congrArg norm this).trans (by rw [norm_mul, hψ.1.2.1, one_mul])

theorem exists_bound (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, hγ, h⟩ := hKc w
  rw [← norm_periodic hψ hf γ hγ w]
  exact hC _ h

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_dLine (hW : IsWeilDatumO ψ S T χS χT om) (g : GA D S) (h : GA D T) {L L' : ℝ →+ WO S T}
    (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) (hL' : Continuous L')
    (hL0' : ∀ t, (L' t).map (finPart D) = 0) (e : ∀ t, L' t = actO S T g h (L t)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : om (g, h) (dLine ψ S T L f) = dLine ψ S T L' (om (g, h) f) := by
  have hψ := hW.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hF := hW.om_pres (g, h) f hf
  obtain ⟨hd, hdt⟩ := hasDerivAt_zero_and_isTheta hψ hL hL0 hf
  obtain ⟨hd', hdt'⟩ := hasDerivAt_zero_and_isTheta hψ hL' hL0' hF
  obtain ⟨C, hC⟩ := exists_bound hψ hdt
  let a : ℕ → WO S T → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ •
    (heisO ψ S T (L (1 / ((n : ℝ) + 1))) f - f) - dLine ψ S T L f
  have hat : ∀ n, IsThetaFunO ψ S T (a n) := fun n =>
    isTheta_sub (isTheta_smul _ (isTheta_sub (isTheta_heisO_real hψ (hL0 _) hf) hf)) hdt
  have hct : IsThetaFunO ψ S T (dLine ψ S T L' (om (g, h) f) - om (g, h) (dLine ψ S T L f)) :=
    isTheta_sub hdt' (hW.om_pres _ _ hdt)
  have ha : ∀ n x, a n x = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
      (heisO ψ S T (L (1 / ((n : ℝ) + 1))) f x - heisO ψ S T (L 0) f x) - dLine ψ S T L f x := by
    intro n x
    rw [map_zero L, heisO_zero]
    rfl
  have hb : ∀ n x, om (g, h) (a n) x = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)⁻¹ *
      (heisO ψ S T (L' (1 / ((n : ℝ) + 1))) (om (g, h) f) x - heisO ψ S T (L' 0) (om (g, h) f) x) -
        om (g, h) (dLine ψ S T L f) x := by
    intro n x
    rw [map_zero L', heisO_zero, e, ← hW.om_heis g h _ f hf, map_sub, map_smul, map_sub]
    rfl
  have key := ae_zero_of_lintegral_eq (μ.restrict 𝓕) a (fun n => om (g, h) (a n)) _ (C + C)
    (fun n => (hat n).cont.measurable) (fun n => (hW.om_pres _ _ (hat n)).cont.measurable) hct.cont.measurable
    (fun n x => by
      rw [ha]
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hC x))
      refine norm_diffQuot_le (hasDerivAt_line hψ hL hL0 hf x) (fun s => ?_) _ (Nat.one_div_pos_of_nat (n := n)).ne'
      rw [heisO, norm_mul, hψ.1.2.1, one_mul]
      exact hC _)
    (fun x => by
      have := (tendsto_diffQuot (hd x)).sub_const (dLine ψ S T L f x)
      rw [sub_self] at this
      exact this.congr fun n => (ha n x).symm)
    (fun x => ((tendsto_diffQuot (hd' x)).sub_const (om (g, h) (dLine ψ S T L f) x)).congr fun n => (hb n x).symm)
    (fun n => hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hat n))
  exact (sub_eq_zero.1 (eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ hct.cont (norm_periodic hψ hct) key)).symm

variable {θ : InfFam D}

theorem compAt_mul (θ : InfFam D) (τ : D.what₂.Tau) {k m n : ℕ} (x : Mx D k m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D k n) = compAt θ τ x * compAt θ τ y :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_one (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 :=
  Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))

theorem mt_mul (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by simp [Formalism.L2.Theta.mt]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem compAt_mt_mul_inv (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g) * compAt θ τ (mt V g⁻¹) = 1 := by
  rw [← compAt_mul, ← mt_mul, mul_inv_cancel, mt_one, compAt_one]

theorem compAt_mt_inv_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g : GA D V) :
    compAt θ τ (mt V g⁻¹) * compAt θ τ (mt V g) = 1 := by
  rw [← compAt_mul, ← mt_mul, inv_mul_cancel, mt_one, compAt_one]

theorem compAt_actO (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T) (x : WO S T) :
    compAt θ τ (actO S T g h x) = compAt θ τ (mt T h) * compAt θ τ x * compAt θ τ (mt S g⁻¹) := by
  unfold actO
  rw [compAt_mul, compAt_mul]

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem lineAt_actO (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) t = actO S T g h (lineAt θ τ z t) := by
  obtain ⟨h1, h2, h3⟩ := isLineAt_lineAt hθ τ z
  let M : ℝ →+ WO S T := AddMonoidHom.mk' (fun t => actO S T g h (lineAt θ τ z t)) fun s t => by
    rw [map_add (f := _), actO_add]
  have hM : IsLineAt θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) M := by
    refine ⟨(continuous_const.matrix_mul h1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (actO S T g h (lineAt θ τ z t)).map (finPart D) = 0
      unfold actO
      rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (actO S T g h (lineAt θ τ z t)) = _
      rw [compAt_actO, h3]
      split_ifs with hτ
      · rw [hτ, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hM]
  rfl

theorem om_dRho (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (g : GA D S) (h : GA D T) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) (om (g, h) f) :=
  om_dLine hW g h (isLineAt_lineAt hθ τ z).1 (isLineAt_lineAt hθ τ z).2.1 (isLineAt_lineAt hθ τ _).1
    (isLineAt_lineAt hθ τ _).2.1 (lineAt_actO hθ τ g h z) hf

theorem cplxO_move (θ : InfFam D) (τ : D.what₂.Tau) (g : GA D S) (h : GA D T)
    {sS sS' : Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT sT' : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : sS' * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS)
    (hT : sT' * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    cplxO sS' sT' (compAt θ τ (mt T h) * z * compAt θ τ (mt S g⁻¹)) =
      compAt θ τ (mt T h) * cplxO sS sT z * compAt θ τ (mt S g⁻¹) := by
  have h1 : compAt θ τ (mt S g⁻¹) * sS' = sS * compAt θ τ (mt S g⁻¹) := by
    calc _ = compAt θ τ (mt S g⁻¹) * (sS' * compAt θ τ (mt S g)) * compAt θ τ (mt S g⁻¹) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, compAt_mt_mul_inv, Matrix.mul_one]
      _ = _ := by rw [hS, ← Matrix.mul_assoc, compAt_mt_inv_mul, Matrix.one_mul]
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = (sT' * compAt θ τ (mt T h)) * z * (compAt θ τ (mt S g⁻¹) * sS') := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hT, h1]; simp only [Matrix.mul_assoc]

end GlobalTheory.WeilVacMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.OrientedChar

theorem map_inv_field {E : Type} [Field E] (τ : E →+* ℂ) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (h : G.det ≠ 0) :
    (G.map τ)⁻¹ = G⁻¹.map τ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h),
    Matrix.map_one _ τ.map_zero τ.map_one]

theorem ringHom_map_quadrupleSum_products {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {m n : ℕ}
    (P : Fin n → Fin n → A) (y : Fin m → Fin n → A) (Q : Fin m → Fin m → A) (x : Fin m → Fin n → A) :
    φ (∑ a, ∑ b, ∑ c, ∑ d, P a b * y c b * Q c d * x d a) =
      ∑ a, ∑ b, ∑ c, ∑ d, φ (P a b) * φ (y c b) * φ (Q c d) * φ (x d a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul]

theorem trace_four {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (y : Matrix (Fin m) (Fin n) ℂ)
    (Q : Matrix (Fin m) (Fin m) ℂ) (x : Matrix (Fin m) (Fin n) ℂ) :
    (P * yᴴ * Q * x).trace = ∑ a, ∑ b, ∑ c, ∑ d, P a b * starRingEnd ℂ (y c b) * Q c d * x d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Complex.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

variable {D : D7}

theorem comp_hO {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau) (x y : WO S T) :
    θ τ (infPart D (hO S T x y)) = hAt S T τ (piW θ T S x τ) (piW θ T S y τ) := by
  have hi : ∀ e, ((θ τ).comp (infPart D)) (incA D e) = tauE D τ e := comp_incA hθ τ
  have hc : ∀ z, ((θ τ).comp (infPart D)) (cA D z) = starRingEnd ℂ (((θ τ).comp (infPart D)) z) := comp_cA hθ τ
  have hg : (gramAt D S τ)⁻¹ = S.gram⁻¹.map (tauE D τ) := map_inv_field _ _ (Formalism.L2.Theta.gram_det_ne S)
  unfold hO hAt
  refine (ringHom_map_quadrupleSum_products ((θ τ).comp (infPart D)) (fun a b => incA D (S.gram⁻¹ a b)) (fun c b => cA D (y c b))
    (fun c d => incA D (T.gram c d)) x).trans ?_
  rw [hg]
  refine Eq.trans ?_ (trace_four _ _ _ _).symm
  simp only [hi, hc]
  rfl

theorem valTau_symplO {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau) (x y : WO S T) :
    valTau θ τ (symplO S T x y) = omAt S T τ (piW θ T S x τ) (piW θ T S y τ) := by
  unfold valTau symplO omAt
  rw [SymplVal.trace_AE, RingHom.map_add (f := _), RingHom.map_add (f := _), comp_cA hθ, RingHom.map_mul, RingHom.map_mul,
    comp_incA hθ, comp_hO hθ, Complex.add_re, Complex.conj_re, two_mul]

theorem finPart_cA_eq_zero {z : AE D} (hz : finPart D z = 0) : finPart D (cA D z) = 0 := by
  have h : ∀ w : AE D, finPart D (cA D w) = sigR (Af D.host.F) D.sp.cm.sig (finPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a e => rfl
  rw [h, hz, map_zero]

theorem finPart_hO (S T : HSp D) {x y : WO S T} (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    finPart D (hO S T x y) = 0 := by
  unfold hO
  refine (ringHom_map_quadrupleSum_products (finPart D) (fun a b => incA D (S.gram⁻¹ a b)) (fun c b => cA D (y c b))
    (fun c d => incA D (T.gram c d)) x).trans ?_
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases h with h | h
  · have e : finPart D (x d a) = 0 := congrFun (congrFun h d) a
    rw [e, mul_zero]
  · have e : finPart D (y c b) = 0 := congrFun (congrFun h c) b
    rw [finPart_cA_eq_zero e, mul_zero, zero_mul, zero_mul]

theorem sndA_symplO (S T : HSp D) {x y : WO S T} (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    sndA D.host.F (symplO S T x y) = 0 := by
  have h0 : finPart D (incA D D.host.xi0 * hO S T x y) = 0 := by
    rw [RingHom.map_mul, finPart_hO S T h, mul_zero]
  have h1 : finPart D (algebraMap (AF D.host.F) (AE D) (symplO S T x y)) = 0 := by
    unfold symplO
    rw [SymplVal.trace_AE, RingHom.map_add (f := _), h0, finPart_cA_eq_zero h0, add_zero]
  have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F)
    (B := D.host.E) (algebraMap D.host.F D.host.E).injective
  apply hinj
  rw [map_zero]
  exact h1

theorem char_symplOH : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (x y : WO S T), (x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) →
      ψ (symplOH S T x y) =
        Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  intro D θ ψ hθ hψ S T x y h
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (real_adele_ext_and_char D θ σ hσ _ (sndA_symplO S T h)).2 ψ hψ
  rw [Finset.sum_congr rfl fun τ _ => valTau_symplO hθ S T τ x y] at e
  exact e

end GlobalTheory.OrientedChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x y : WO S T), (x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) → ψ (symplOH S T x y) = Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  first | exact @GlobalTheory.OrientedChar.char_symplOH | exact GlobalTheory.OrientedChar.char_symplOH | (intros; apply GlobalTheory.OrientedChar.char_symplOH <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.RealSymplForm

section Mat

open scoped ComplexOrder MatrixOrder

variable {k m n : ℕ}

theorem cartan_swap {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : sᴴ * G = G * s := by
  calc sᴴ * G = sᴴ * G * (s * s) := by rw [h.1, Matrix.mul_one]
    _ = G * s := by rw [← Matrix.mul_assoc, h.2.1]

theorem cartan_herm {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : Gᴴ = G := by
  have h1 : (G * s)ᴴ = G * s := h.2.2.1
  have h2 : sᴴ * sᴴ = 1 := by rw [← conjTranspose_mul, h.1, conjTranspose_one]
  rw [conjTranspose_mul, ← cartan_swap h] at h1
  calc Gᴴ = sᴴ * (sᴴ * Gᴴ) := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    _ = G := by rw [h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem cartanInvolution_inv_eq_self {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : s⁻¹ = s :=
  Matrix.inv_eq_left_inv h.1

theorem cartan_inv_mul {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : (G * s)⁻¹ = s * G⁻¹ := by
  rw [Matrix.mul_inv_rev, cartanInvolution_inv_eq_self h]

theorem cartan_inv_conj {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : s * G⁻¹ * sᴴ = G⁻¹ := by
  conv_rhs => rw [← h.2.1]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, cartanInvolution_inv_eq_self h, Matrix.mul_assoc]

theorem trace_pos {P : Matrix (Fin n) (Fin n) ℂ} {Q : Matrix (Fin m) (Fin m) ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    {x : Matrix (Fin m) (Fin n) ℂ} (hx : x ≠ 0) : 0 < (P * xᴴ * Q * x).trace.re := by
  obtain ⟨B, hB, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hP.isStrictlyPositive
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hQ.isStrictlyPositive
  have e : (star B * B * xᴴ * (star C * C) * x).trace = ((C * x * Bᴴ)ᴴ * (C * x * Bᴴ)).trace := by
    simp only [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hy : C * x * Bᴴ ≠ 0 := by
    intro h0
    apply hx
    have hB' : IsUnit (Bᴴ).det := (Matrix.isUnit_iff_isUnit_det _).1 hB.star
    have hC' : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det _).1 hC
    calc x = C⁻¹ * (C * x * Bᴴ) * (Bᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hB',
            Matrix.nonsing_inv_mul_cancel_left _ _ hC']
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
  rw [e]
  have h1 := (posSemidef_conjTranspose_mul_self (C * x * Bᴴ)).trace_nonneg
  have h2 : ((C * x * Bᴴ)ᴴ * (C * x * Bᴴ)).trace ≠ 0 := fun h0 =>
    hy (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0)
  exact (Complex.pos_iff.1 (lt_of_le_of_ne h1 h2.symm)).1

theorem cplxO_cplxO {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s * s = 1) (ht : t * t = 1)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (cplxO s t x) = -x := by
  have e : t * (t * x * s) * s = x := by
    calc _ = (t * t) * x * (s * s) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hs, ht, Matrix.one_mul, Matrix.mul_one]
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, e, Complex.I_mul_I, neg_smul, one_smul]

theorem tr_conj {G : Matrix (Fin n) (Fin n) ℂ} {H : Matrix (Fin m) (Fin m) ℂ} (hG : Gᴴ = G) (hH : Hᴴ = H)
    (x y : Matrix (Fin m) (Fin n) ℂ) : (G⁻¹ * xᴴ * H * y).trace = star (G⁻¹ * yᴴ * H * x).trace := by
  rw [← Matrix.trace_conjTranspose]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hG, hH, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem tr_J_left {G s : Matrix (Fin n) (Fin n) ℂ} {H t : Matrix (Fin m) (Fin m) ℂ} (hG : IsCartanInv G s)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (G⁻¹ * yᴴ * H * cplxO s t x).trace = Complex.I * ((G * s)⁻¹ * yᴴ * (H * t) * x).trace := by
  rw [cplxO, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, cartan_inv_mul hG, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem tr_J_J {G s : Matrix (Fin n) (Fin n) ℂ} {H t : Matrix (Fin m) (Fin m) ℂ} (hG : IsCartanInv G s)
    (hH : IsCartanInv H t) (x y : Matrix (Fin m) (Fin n) ℂ) :
    (G⁻¹ * (cplxO s t y)ᴴ * H * cplxO s t x).trace = (G⁻¹ * yᴴ * H * x).trace := by
  have e : (G * s)⁻¹ * (t * y * s)ᴴ * (H * t) * x = G⁻¹ * yᴴ * H * x := by
    calc _ = (s * G⁻¹ * sᴴ) * yᴴ * (tᴴ * H * t) * x := by
          simp only [cartan_inv_mul hG, conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [cartan_inv_conj hG, hH.2.1]
  rw [tr_J_left hG, cplxO, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, e,
    smul_eq_mul, ← mul_assoc]
  simp

end Mat

theorem realPlace_imaginaryGenerator_re_eq_zero (D : D7) (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, tauE_sqrtMinusD, Complex.div_re]
  simp

theorem omAt_zero_right {D : D7} (S T : HSp D) (τ : D.what₂.Tau) (x : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {y : Matrix (Fin T.rank) (Fin S.rank) ℂ} (h : y = 0) : omAt S T τ x y = 0 := by
  simp [omAt, hAt, h]

open scoped ComplexOrder in
theorem omAt_J_neg {D : D7} (S T : HSp D) (τ : D.what₂.Tau) {s : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {t : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hs : IsCartanInv (gramAt D S τ) s) (ht : IsCartanInv (gramAt D T τ) t)
    {x : Matrix (Fin T.rank) (Fin S.rank) ℂ} (hx : x ≠ 0) : omAt S T τ (cplxO s t x) x < 0 := by
  have e : hAt S T τ (cplxO s t x) x = Complex.I *
      ((gramAt D S τ * s)⁻¹ * xᴴ * (gramAt D T τ * t) * x).trace := tr_J_left hs _ _
  have p := mul_pos (xi_zero_im_pos D τ) (trace_pos hs.2.2.inv ht.2.2 hx)
  simp only [omAt, e, Complex.mul_re, Complex.mul_im, realPlace_imaginaryGenerator_re_eq_zero, Complex.I_re, Complex.I_im]
  linarith

theorem form_alt_inv_def : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ x, jO S T sS sT (jO S T sS sT x) = -x) ∧ (∀ x y, omO S T x y = -omO S T y x) ∧ (∀ x y, omO S T (jO S T sS sT x) (jO S T sS sT y) = omO S T x y) ∧ ∀ x, x ≠ 0 → omO S T (jO S T sS sT x) x < 0 := by
  intro D S T sS sT hS hT
  refine ⟨fun x => ?_, fun x y => ?_, fun x y => ?_, fun x hx => ?_⟩
  · funext τ
    exact cplxO_cplxO (hS τ).1 (hT τ).1 _
  · rw [omO_apply, omO_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e : hAt S T τ (y τ) (x τ) = star (hAt S T τ (x τ) (y τ)) :=
      tr_conj (cartan_herm (hS τ)) (cartan_herm (hT τ)) _ _
    simp only [omAt, e, Complex.mul_re, realPlace_imaginaryGenerator_re_eq_zero, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  · rw [omO_apply, omO_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e : hAt S T τ (jO S T sS sT x τ) (jO S T sS sT y τ) = hAt S T τ (x τ) (y τ) :=
      tr_J_J (hS τ) (hT τ) _ _
    simp only [omAt, e]
  · obtain ⟨τ₀, h0⟩ := Function.ne_iff.1 hx
    rw [omO_apply]
    refine Finset.sum_neg' (fun τ _ => ?_) ⟨τ₀, Finset.mem_univ _, omAt_J_neg S T τ₀ (hS τ₀) (hT τ₀) h0⟩
    by_cases h : x τ = 0
    · exact (omAt_zero_right S T τ _ h).le
    · exact (omAt_J_neg S T τ (hS τ) (hT τ) h).le

end GlobalTheory.RealSymplForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realSymplecticForm_alternating_invariant_definite : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ x, jO S T sS sT (jO S T sS sT x) = -x) ∧ (∀ x y, omO S T x y = -omO S T y x) ∧ (∀ x y, omO S T (jO S T sS sT x) (jO S T sS sT y) = omO S T x y) ∧ ∀ x, x ≠ 0 → omO S T (jO S T sS sT x) x < 0 := by
  first | exact @GlobalTheory.RealSymplForm.form_alt_inv_def | exact GlobalTheory.RealSymplForm.form_alt_inv_def | (intros; apply GlobalTheory.RealSymplForm.form_alt_inv_def <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ImportsBis
namespace GlobalTheory.NatMulIntegralNsmul

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ M : ℕ, 0 < M ∧ IsIntegral ℤ ((M : E) * a) := by
  have halg : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]; exact hint
  · have h2 : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h2, Int.cast_neg, neg_mul]
    exact hint.neg

theorem exists_nsmul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (h : Submodule.IsFullLattice E Λ)
    (v : Fin n → E) : ∃ (N : ℕ), (0 : ℕ) < N ∧ N • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    rw [h.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hy⟩ := hy
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_smul]; exact nsmul_mem hx M
    · rw [mul_comm, mul_smul]; exact nsmul_mem hy N
  | smul a x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, hint⟩ := exists_nat_mul_integral a
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E r = (M : E) * a := ⟨⟨(M : E) * a, hint⟩, rfl⟩
    have hmem := Λ.smul_mem r hx
    have e : (M * N) • a • x = r • N • x := by
      rw [← algebraMap_smul E r (N • x), hr]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Pi.mul_apply,
        Pi.natCast_apply]
      ring
    rw [e]; exact hmem

end GlobalTheory.NatMulIntegralNsmul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.VacUnique.Den

theorem exists_nsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (h : Submodule.IsFullLattice E Λ) (v : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • v ∈ Λ := by
  exact _root_.GlobalTheory.NatMulIntegralNsmul.exists_nsmul_mem Λ h v

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

theorem exists_nsmul_finRat_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D S T ΛS ΛT hS hT γ
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ D.host.AA, a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact AA_ne_zero D (FractionalIdeal.eq_zero_iff.2 hc)
  rw [Matrix.matrix_eq_sum_single γ]
  simp_rw [← Finset.sum_product']
  refine Finset.sum_induction _ (fun γ => ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ?_ ?_ ?_
  · rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    rw [AddMonoidHom.map_add (f := _), nsmul_add]
    refine add_mem ?_ ?_
    · rw [mul_nsmul]; exact nsmul_mem hx M
    · rw [mul_nsmul']; exact nsmul_mem hy N
  · exact ⟨1, one_pos, by rw [AddMonoidHom.map_zero, nsmul_zero]; exact zero_mem _⟩
  · rintro ⟨i, j⟩ -
    obtain ⟨N, hN, ht⟩ := exists_nsmul_mem_lattice ΛT hT (Pi.single i (γ i j / a))
    obtain ⟨M, hM, hs⟩ := exists_nsmul_mem_lattice ΛS hS (fun k => star (S.gram⁻¹ j k))
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    refine AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, fun v hv => absurd trivial hv,
      a, ha, _, hs, _, ht, ?_⟩
    rw [← map_nsmul]
    funext i' j'
    show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] _ = (pairA D.host.F 0 1) ⊗ₜ[D.host.F] _
    congr 1
    have hG : ∑ k, S.gram⁻¹ j k * S.gram k j' = (1 : Matrix _ _ D.host.E) j j' := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (Formalism.L2.Theta.gram_det_ne S).isUnit]
    have h2 : ∑ k, star ((M • fun k => star (S.gram⁻¹ j k)) k) * S.gram k j' =
        (M : D.host.E) * (1 : Matrix _ _ D.host.E) j j' := by
      rw [← hG, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, star_nsmul, star_star, nsmul_eq_mul, mul_assoc]
    rw [h2]
    simp only [Matrix.smul_apply, Pi.smul_apply, nsmul_eq_mul, Matrix.single_apply, Pi.single_apply, Matrix.one_apply,
      Nat.cast_mul]
    by_cases h1 : i = i' <;> by_cases h3 : j = j'
    · subst h1 h3; simp; field_simp
    · simp [h3]
    · simp [h1, Ne.symm h1]
    · simp [h1, h3]

end GlobalTheory.VacUnique.Den
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_finite_matrix_mem_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first
  | exact GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem
  | intro D S T ΛS ΛT hS hT γ
    exact GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT
      hS.toIsLattice hT.toIsLattice γ
end
end
