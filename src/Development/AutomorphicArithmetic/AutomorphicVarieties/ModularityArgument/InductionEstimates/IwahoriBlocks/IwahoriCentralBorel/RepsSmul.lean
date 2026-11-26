module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RepsSmul
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AeFundamentalDomain
theorem UpperTheory.ae_fundamental_domain :
    ∀ {G Q : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace Q]
        (Γ : Subgroup G) [Countable Γ] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] (D : Set G) (π : G → Q),
        Measurable π → (∀ (γ : Γ) (g : G), π ((γ : G) * g) = π g) → (∀ g : G, ∃ γ : Γ, (γ : G) * g ∈ D) →
        ∀ p : Q → Prop, (∀ᵐ q ∂(MeasureTheory.Measure.map π (μ.restrict D)), p q) → ∀ᵐ y ∂μ, p (π y) := by
  intro G Q _ _ _ _ Γ _ μ _ D π hπ hinv hcov p hp
  rw [MeasureTheory.ae_iff] at hp ⊢
  obtain ⟨N, hsub, hNm, hN0⟩ := MeasureTheory.exists_measurable_superset_of_null hp
  rw [MeasureTheory.Measure.map_apply hπ hNm,
    MeasureTheory.Measure.restrict_apply (hπ hNm)] at hN0
  have hcover : {y | ¬ p (π y)} ⊆
      ⋃ γ : Γ, (fun g : G => (γ : G) * g) ⁻¹' (π ⁻¹' N ∩ D) := by
    intro y hy
    obtain ⟨γ, hγ⟩ := hcov y
    refine Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩
    show π ((γ : G) * y) ∈ N
    rw [hinv]
    exact hsub hy
  refine MeasureTheory.measure_mono_null hcover (MeasureTheory.measure_iUnion_null fun γ => ?_)
  rw [MeasureTheory.measure_preimage_mul]
  exact hN0
end

open MeasureTheory GroundTheory.Automorphic

private theorem UpperTheory.Reformulated.B.Glb3.ae_pull {G : Type} [Group G] (Γ : Subgroup G) [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [DiscreteTopology ↥Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (p : RightCosetSpace Γ → Prop)
    (hp : ∀ᵐ q ∂(RightCosetSpace.quotientMeasure Γ μ), p q) :
    ∀ᵐ y ∂μ, p (RightCosetSpace.mk Γ y) := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  refine UpperTheory.ae_fundamental_domain Γ μ (RightCosetSpace.fundamentalDomain Γ) (RightCosetSpace.mk Γ)
    measurable_quotient_mk'' (fun γ g => Quotient.sound ⟨γ, rfl⟩) (fun g => ?_) p hp
  exact (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain Γ g).exists

private theorem UpperTheory.Reformulated.B.Glb3.reps_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (μ : Measure (PositivityTheory.Rg.Tf.Core.G1 K n)) [μ.IsHaarMeasure] (v : PositivityTheory.Rg.Tf.Core.L2 μ)
    (φ : PositivityTheory.Rg.Tf.Core.G1 K n → ℂ) (c : ℂ) (h : PositivityTheory.Rg.Tf.Adel.Reps μ v φ) :
    PositivityTheory.Rg.Tf.Adel.Reps μ (c • v) (c • φ) := by
  have h1 := UpperTheory.Reformulated.B.Glb3.ae_pull (PositivityTheory.Rg.Tf.Core.Gam K n) μ _ (Lp.coeFn_smul c v)
  filter_upwards [h, h1] with y hy hy1
  exact hy1.trans (congrArg (c • ·) hy)

theorem UpperTheory.Reformulated.B.Glb3.sec_add :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] {μ₂ : MeasureTheory.Measure (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ))}
      [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (PositivityTheory.Rg.Tf.Core.L2 μ₂)}
      {f f' : PositivityTheory.Rg.Tf.Core.G1 K ((2 : ℕ) + (2 : ℕ)) → ℂ},
      PositivityTheory.Rg.Tf.Adel.IsSec τ₁ τ₂ f →
        PositivityTheory.Rg.Tf.Adel.IsSec τ₁ τ₂ f' → ∀ (c : ℂ), PositivityTheory.Rg.Tf.Adel.IsSec τ₁ τ₂ (f + c • f') := by
  intro K _ _ μ _ τ₁ τ₂ f f' hf hf' c
  obtain ⟨h1, ⟨C, h2⟩, h3, h4, h5⟩ := hf
  obtain ⟨h1', ⟨C', h2'⟩, h3', h4', h5'⟩ := hf'
  refine ⟨h1.add (h1'.const_smul c), ⟨C + ‖c‖ * C', fun g => ?_⟩, fun X g => ?_,
    fun r x g hx => ?_, fun g => ?_⟩
  · refine (norm_add_le (f g) (c • f' g)).trans (add_le_add (h2 g) ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h2' g) (norm_nonneg c)
  · simp only [Pi.add_apply, Pi.smul_apply, h3 X g, h3' X g]
  · simp only [Pi.add_apply, Pi.smul_apply, h4 r x g hx, h4' r x g hx]
  · obtain ⟨d, φ, ψ, hφ, hψ, hs⟩ := h5 g
    obtain ⟨d', φ', ψ', hφ', hψ', hs'⟩ := h5' g
    refine ⟨d + d', Fin.append φ (fun i => c • φ' i), Fin.append ψ ψ', fun i => ?_, fun i => ?_,
      fun m₁ m₂ x hx => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hφ j
      · rw [Fin.append_right]
        obtain ⟨hc, v, hv, hr⟩ := hφ' j
        exact ⟨hc.const_smul c, c • v, τ₁.smul_mem c hv, UpperTheory.Reformulated.B.Glb3.reps_smul μ v _ c hr⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hψ j
      · rw [Fin.append_right]; exact hψ' j
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hs m₁ m₂ x hx, hs' m₁ m₂ x hx, Finset.mul_sum, mul_assoc]
end

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

private theorem reps_smul {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) (φ : G1 K n → ℂ) (c : ℂ)
    (h : ∃ v ∈ τ, Reps μ v φ) : ∃ v ∈ τ, Reps μ v (fun y => c * φ y) := by
  obtain ⟨w, hw, hq⟩ := h
  refine ⟨c • w, τ.smul_mem _ hw, ?_⟩
  filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_smul c w), hq] with y e2 e4
  rw [e2, Pi.smul_apply, e4, smul_eq_mul]

private theorem zt_zero' : zt K 0 = 1 := by
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext (by simp)
  rw [zt, this, map_one]

private theorem lv_zero' (m₁ m₂ : G1 K 2) :
    ((lv m₁ m₂ 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (m₁ : AdelicGLn.AdelicGL K 2) (m₂ : AdelicGLn.AdelicGL K 2) := by
  rw [blkLaws.1, neg_zero, zt_zero', mul_one, mul_one]

private theorem lv_ray' (r : {r : ℝ // 0 < r}) :
    ((lv 1 1 (Real.log r.1) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (centralSection K 2 r) (centralSection K 2 r⁻¹) := by
  have h := Real.exp_log r.2
  have h1 : (⟨Real.exp (Real.log r.1), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = r := Subtype.ext h
  have h2 : (⟨Real.exp (-Real.log r.1), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = r⁻¹ := by
    apply Subtype.ext
    change Real.exp (-Real.log r.1) = r.1⁻¹
    rw [Real.exp_neg, h]
  rw [blkLaws.1, zt, zt, h1, h2]
  simp

private theorem nn_zero : nn (K := K) 0 = 1 := unipOne_zero 2

private theorem hh_lv (m₁ m₂ : G1 K 2) (t : ℝ) (g : G1 K (2 + 2)) : HH (lv m₁ m₂ t * g) = t + HH g := by
  have := (hpSpec (K := K)).1 0 m₁ m₂ t g
  rwa [nn_zero, one_mul] at this

private theorem hh_nn (X : UPos (2 + 2) 2 → AdeleRing (𝓞 K) K) (g : G1 K (2 + 2)) : HH (nn X * g) = HH g := by
  have := (hpSpec (K := K)).1 X 1 1 0 g
  rwa [blkLaws.2.2.1, mul_one, zero_add] at this

private theorem arc_mem {n : ℕ} (k : archCompact K n) : arc1 k ∈ KG K n := by
  have hk : infEmb K n k ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) := k.2
  have h := congrArg Subtype.val (retractOne_coe (⟨_, maxCompact_le_normOneGL hk⟩ : normOneGL (K := K) (n := n)))
  change ((retractOne (infEmb K n k) : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact
  exact h ▸ hk

private theorem fin_mem {n : ℕ} {u : FA K n} (hu : u ∈ AdelicGLn.integralFiniteGL K n) : fin1 u ∈ KG K n := by
  unfold fin1
  rw [MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu))]
  exact finEmb_mem_maxCompact hu

private theorem flat_k (f : G1 K (2 + 2) → ℂ) (g : G1 K (2 + 2)) {k : G1 K (2 + 2)} (hk : k ∈ KG K (2 + 2)) :
    flat 0 f (g * k) = Complex.exp ((0 + 2) * (HP 2 2 g : ℂ)) * f (g * k) := by
  have : HP 2 2 (g * k) = HP 2 2 g := ((hpSpec (K := K)).2.1 k hk).2 g
  rw [flat, this]

private theorem fixA_flat (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) (f : G1 K (2 + 2) → ℂ) :
    FixA κ e (flat 0 f) ↔ FixA κ e f := by
  refine forall_congr' fun g => ?_
  simp only [flat_k f g (arc_mem _), mul_left_comm (e _)]
  rw [integral_const_mul, flat, mul_right_inj' (Complex.exp_ne_zero _)]

private theorem sec_tr {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {f : G1 K (2 + 2) → ℂ}
    (hf : IsSec τ₁ τ₂ f) (y : G1 K (2 + 2)) :
    IsSec τ₁ τ₂ fun x => Complex.exp (2 * ((HH (x * y) - HH x : ℝ) : ℂ)) * f (x * y) := by
  obtain ⟨-, -, -, hc, hb⟩ := hpSpec (K := K)
  refine ⟨?_, ?_, fun X g => ?_, fun r x g hx => ?_, fun g => ?_⟩
  · exact ((continuous_const.mul (Complex.continuous_ofReal.comp ((hc.comp (continuous_mul_const y)).sub hc))).cexp).mul
      (hf.cont.comp (continuous_mul_const y))
  · obtain ⟨R, hR⟩ := hb {y} isCompact_singleton
    obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨Real.exp (2 * R) * C, fun g => ?_⟩
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul (Real.exp_le_exp.2 ?_) (hC _) (norm_nonneg _) (Real.exp_pos _).le
    have := (le_abs_self _).trans (hR g y rfl)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    linarith
  · rw [mul_assoc, hh_nn, hh_nn, hf.unip]
  · have e : x = lv 1 1 (Real.log r.1) * g := Subtype.ext (by rw [hx, Subgroup.coe_mul, lv_ray'])
    have e2 : f (x * y) = f (g * y) := hf.ray r _ _ (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, mul_assoc])
    beta_reduce
    rw [e2, e, mul_assoc, hh_lv, hh_lv, add_sub_add_left_eq_sub]
  · obtain ⟨d, φ, ψ, hφ, hψ, hx⟩ := hf.levi (g * y)
    refine ⟨d, fun i m => Complex.exp (2 * ((HH (g * y) - HH g : ℝ) : ℂ)) * φ i m, ψ,
      fun i => ⟨continuous_const.mul (hφ i).1, reps_smul _ _ _ _ (hφ i).2⟩, hψ, fun m₁ m₂ x h => ?_⟩
    have e : x = lv m₁ m₂ 0 * g := Subtype.ext (by rw [h, Subgroup.coe_mul, lv_zero'])
    have e2 := hx m₁ m₂ (x * y) (by rw [Subgroup.coe_mul, Subgroup.coe_mul, h, mul_assoc])
    beta_reduce
    rw [e2, e, mul_assoc, hh_lv, hh_lv, add_sub_add_left_eq_sub, Finset.mul_sum]
    simp only [mul_assoc]

private theorem sec_add {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {f f' : G1 K (2 + 2) → ℂ}
    (hf : IsSec τ₁ τ₂ f) (hf' : IsSec τ₁ τ₂ f') (c : ℂ) : IsSec τ₁ τ₂ (f + c • f') :=
  _root_.UpperTheory.Reformulated.B.Glb3.sec_add hf hf' c

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ), IdemA κ e → (IsSec τ₁ τ₂ 0 ∧ ∀ f f', IsSec τ₁ τ₂ f → IsSec τ₁ τ₂ f' → ∀ c : ℂ, IsSec τ₁ τ₂ (f + c • f')) ∧
      (∀ f : G1 K (2 + 2) → ℂ, Continuous f → (FixA κ e (flat 0 f) ↔ FixA κ e f) ∧
        ∀ U : Subgroup (FA K (2 + 2)), U ≤ AdelicGLn.integralFiniteGL K (2 + 2) → (FixF U (flat 0 f) ↔ FixF U f)) ∧
      (∀ f f' : G1 K (2 + 2) → ℂ, flat 0 f = flat 0 f' → f = f') ∧
      ∀ f (h : FA K (2 + 2)), IsSec τ₁ τ₂ f → FixA κ e f → ∃ f', IsSec τ₁ τ₂ f' ∧ FixA κ e f' ∧ ∀ x, flat 0 f' x = flat 0 f (x * fin1 h) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e _
  refine ⟨⟨⟨continuous_const, ⟨0, fun g => by simp⟩, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun g => ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ _ _ _ => by simp⟩⟩,
    fun f f' hf hf' c => sec_add hf hf' c⟩, fun f _ => ⟨fixA_flat κ e f, fun U hU => ?_⟩, fun f f' h => ?_, fun f h hf hA => ?_⟩
  · refine forall₂_congr fun u hu => forall_congr' fun g => ?_
    rw [flat_k f g (fin_mem (hU hu)), flat, mul_right_inj' (Complex.exp_ne_zero _)]
  · funext x
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) (congrFun h x)
  · have key : ∀ x, flat 0 (fun x => Complex.exp (2 * ((HH (x * fin1 h) - HH x : ℝ) : ℂ)) * f (x * fin1 h)) x =
        flat 0 f (x * fin1 h) := fun x => by
      simp only [flat]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    refine ⟨_, sec_tr hf (fin1 h), (fixA_flat κ e _).1 fun g => ?_, key⟩
    have hc : ∀ k : archCompact K (2 + 2), g * arc1 k * fin1 h = g * fin1 h * arc1 k := fun k => by
      rw [mul_assoc, mul_assoc]
      exact congrArg (g * ·) (MultiplicityOne.finProj_mul_archProj_comm h _).symm
    simp only [key, hc]
    exact (fixA_flat κ e f).2 hA _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.OpenStab
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsXTranslate
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AeTranslateEq
theorem UpperTheory.ae_translate_eq :
    ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace X]
        (μ : MeasureTheory.Measure G) [μ.IsMulRightInvariant] (ν : MeasureTheory.Measure X) (q : G → X) (ρ : X → X) (g : G)
        (v v' : X → ℂ) (φ : G → ℂ), MeasureTheory.Measure.QuasiMeasurePreserving q μ ν → (∀ y, ρ (q y) = q (y * g)) →
        (v' =ᵐ[ν] fun x => v (ρ x)) → (∀ᵐ y ∂μ, v (q y) = φ y) → ∀ᵐ y ∂μ, v' (q y) = φ (y * g) := by
  intro G X _ _ _ _ μ _ ν q ρ g v v' φ hq hρ hv hφ
  have h1 : ∀ᵐ y ∂μ, v' (q y) = v (ρ (q y)) := MeasureTheory.Measure.QuasiMeasurePreserving.ae hq hv
  have h2 : ∀ᵐ y ∂μ, v (q (y * g)) = φ (y * g) :=
    (MeasureTheory.measurePreserving_mul_right μ g).quasiMeasurePreserving.ae hφ
  filter_upwards [h1, h2] with y a b
  rw [a, hρ, b]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MeanValueUniqueness
theorem UpperTheory.mean_value_uniqueness :
    ∀ {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace K] [CompactSpace K]
        [MeasurableSpace K] [OpensMeasurableSpace K] (κ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure κ]
        (a : K → G) (p : K → ℂ), Continuous a → Continuous p → ∀ φ ψ : G → ℂ, Continuous φ → Continuous ψ →
        (∀ g, ∫ k, p k * φ (g * a k) ∂κ = φ g) → (∀ g, ∫ k, p k * ψ (g * a k) ∂κ = ψ g) →
        ∀ g, ∫ k, p k * (φ + ψ) (g * a k) ∂κ = (φ + ψ) g := by
  intro G K _ _ _ _ _ _ _ κ _ a p ha hp φ ψ hφ hψ h1 h2 g
  have key : ∀ f : G → ℂ, Continuous f →
      MeasureTheory.Integrable (fun k => p k * f (g * a k)) κ := by
    intro f hf
    have hc : Continuous (fun k => p k * f (g * a k)) :=
      hp.mul (hf.comp (continuous_const.mul ha))
    exact (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable κ
  simp only [Pi.add_apply, mul_add]
  rw [MeasureTheory.integral_add (key φ hφ) (key ψ hψ), h1 g, h2 g]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenRightInvariance
theorem UpperTheory.isOpen_right_invariance :
    ∀ {H F G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group F] [TopologicalSpace F] [Group G]
        (ι : H →* F) (f : F →* G) (U : Subgroup F) (φ : G → ℂ), Continuous ι → IsOpen (U : Set F) →
        (∀ u ∈ U, ∀ g, φ (g * f u) = φ g) → IsOpen {h : H | (fun x => φ (x * f (ι h))) = φ} := by
  intro H F G _ _ _ _ _ _ ι f U φ hι hU hφ
  let S : Subgroup H :=
    { carrier := {h : H | (fun x => φ (x * f (ι h))) = φ}
      one_mem' := by
        funext x
        simp
      mul_mem' := by
        intro a b ha hb
        funext x
        have h1 : φ (x * f (ι a) * f (ι b)) = φ (x * f (ι a)) := congrFun hb (x * f (ι a))
        have h2 : φ (x * f (ι a)) = φ x := congrFun ha x
        rw [map_mul, map_mul, ← mul_assoc, h1, h2]
      inv_mem' := by
        intro a ha
        funext x
        have h1 : φ (x * f (ι a⁻¹) * f (ι a)) = φ (x * f (ι a⁻¹)) := congrFun ha (x * f (ι a⁻¹))
        rw [← h1]
        simp }
  have hle : U.comap ι ≤ S := by
    intro h hh
    funext x
    exact hφ (ι h) hh x
  have hopen : IsOpen ((U.comap ι : Subgroup H) : Set H) := hU.preimage hι
  exact Subgroup.isOpen_mono hle hopen
end

section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem UpperTheory.Reformulated.B.Gul4.lev_top :
    Lev (fun w : Pl K => (GLnLocal.integralGL (w.adicCompletion K) n : Subgroup (Gw n w))) := fun w =>
  ⟨⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩, le_rfl⟩

private theorem UpperTheory.Reformulated.B.Gul4.mem_iff (μ : Measure (G1 K n)) (τ : Submodule ℂ (L2 μ))
    (κ : Measure (archCompact K n)) (p : archCompact K n → ℂ) (hp : IdemA κ p) (hμ : μ.IsHaarMeasure)
    (S : Finset (Pl K)) (φ : G1 K n → ℂ) : φ ∈ Xs μ τ κ p S ↔ IsX μ τ κ p S φ := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  obtain ⟨-, hinf, -, harc, hcpt, -⟩ := levLaws (K := K) n S
  have hq := RightCosetSpace.quasiMeasurePreserving_mk (Gam K n) μ
  have := hp.haar.prob
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨continuous_const, ⟨0, τ.zero_mem, ?_⟩, fun g => by simp, _, UpperTheory.Reformulated.B.Gul4.lev_top, fun u _ g => rfl⟩
    exact MeasureTheory.QuasiMeasurePreserving.ae hq (Lp.coeFn_zero ℂ 2 _)
  | add x y _ _ hx hy =>
    obtain ⟨cx, ⟨v, hv, rv⟩, ax, U, hU, fx⟩ := hx
    obtain ⟨cy, ⟨v', hv', rv'⟩, ay, U', hU', fy⟩ := hy
    obtain ⟨hL, hE⟩ := hinf U U' hU hU'
    refine ⟨cx.add cy, ⟨v + v', τ.add_mem hv hv', ?_⟩, UpperTheory.mean_value_uniqueness κ arc1 p harc hp.cont x y cx cy ax ay,
      _, hL, fun u hu g => ?_⟩
    · filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae hq (Lp.coeFn_add v v'), rv, rv'] with z h1 h2 h3
      rw [Pi.add_apply, ← h2, ← h3]
      exact h1
    · rw [hE] at hu
      rw [Pi.add_apply, Pi.add_apply, fx u hu.1, fy u hu.2]
  | smul c x _ hx =>
    obtain ⟨cx, ⟨v, hv, rv⟩, ax, U, hU, fx⟩ := hx
    refine ⟨cx.const_smul c, ⟨c • v, τ.smul_mem c hv, ?_⟩, fun g => ?_, U, hU, fun u hu g => ?_⟩
    · filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae hq (Lp.coeFn_smul c v), rv] with z h1 h2
      rw [Pi.smul_apply, ← h2]
      exact h1
    · rw [Pi.smul_apply, ← ax g, smul_eq_mul, ← integral_const_mul]
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    · rw [Pi.smul_apply, Pi.smul_apply, fx u hu]

private theorem UpperTheory.Reformulated.B.Gul4.isX_translate (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ))
    (κ : Measure (archCompact K n)) (p : archCompact K n → ℂ) (hτ : CuspIrr μ τ)
    {r : ℕ} (w : Fin r → Pl K) (ι : GS n w →* FA K n) (hw : Function.Injective w) (hι : IsEmb w ι)
    (φ : G1 K n → ℂ) (hφ : IsX μ τ κ p (im w) φ) (g : GS n w) :
    IsX μ τ κ p (im w) fun x => φ (x * fin1 (ι g)) := by
  obtain ⟨-, -, hcomm, -, -, hconj⟩ := levLaws (K := K) n (im w)
  obtain ⟨cφ, ⟨v, hv, rv⟩, aφ, U, hU, fφ⟩ := hφ
  obtain ⟨U', hU', hc⟩ := hconj w ι hw hι rfl U hU g
  obtain ⟨-, -, -, hst, -⟩ := hτ
  refine ⟨cφ.comp (continuous_id.mul continuous_const), ⟨_, hst (fin1 (ι g)) v hv, ?_⟩, fun x => ?_, U', hU',
    fun u hu x => ?_⟩
  · exact UpperTheory.ae_translate_eq μ _ (RightCosetSpace.mk (Gam K n)) (RightCosetSpace.rightMul (Gam K n) (fin1 (ι g))) _ v _ φ
      (RightCosetSpace.quasiMeasurePreserving_mk (Gam K n) μ) (fun y => RightCosetSpace.rightMul_mk _ _)
      (RightCosetSpace.coeFn_rightRegularRep (Gam K n) μ _ v) rv
  · beta_reduce
    rw [← aφ (x * fin1 (ι g))]
    simp only [mul_assoc, fun k => (hcomm k (ι g)).eq]
  · have h := fφ _ (hc u hu) (x * fin1 (ι g))
    beta_reduce
    rw [← h]
    simp only [fin1, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]

end

theorem UpperTheory.Reformulated.B.Gul4.xMem :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] [NumberField.IsTotallyComplex K]
      (μ : MeasureTheory.Measure (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ))) [inst_3 : μ.IsHaarMeasure]
      (τ : Submodule ℂ (PositivityTheory.Rg.Tf.Core.L2 μ))
      (κ : MeasureTheory.Measure ↥(GroundTheory.Automorphic.AutomorphicForm.archCompact K (2 : ℕ)))
      (p : ↥(GroundTheory.Automorphic.AutomorphicForm.archCompact K (2 : ℕ)) → ℂ),
      UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IdemA κ p →
        (∀ (S : Finset (UpperTheory.ConvolutionTheory.Pl K)) (φ : PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ),
            φ ∈ UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.Xs μ τ κ p S ↔ UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IsX μ τ κ p S φ) ∧
          (PositivityTheory.Rg.Tf.Adel.CuspIrr μ τ →
            ∀ {r : ℕ} (w : Fin r → UpperTheory.ConvolutionTheory.Pl K) (ι : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w →* UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.FA K (2 : ℕ)),
              Function.Injective w →
                UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.IsEmb w ι →
                  ∀ φ ∈ UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.Xs μ τ κ p (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.im w),
                    IsOpen
                        {g : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w |
                          ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.rS ι :
                                          UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w →
                                            (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ) →ₗ[ℂ] PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ)
                                        g :
                                (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ) → PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ)
                              φ =
                            φ} ∧
                      ∀ (g : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w),
                        ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.rS ι :
                                        UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.GS (2 : ℕ) w →
                                          (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ) →ₗ[ℂ] PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ)
                                      g :
                              (PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ) → PositivityTheory.Rg.Tf.Core.G1 K (2 : ℕ) → ℂ)
                            φ ∈
                          UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.Xs μ τ κ p (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.im w)) := by
  intro K _ _ _ μ hμ τ κ p hp
  refine ⟨UpperTheory.Reformulated.B.Gul4.mem_iff μ τ κ p hp hμ, fun hτ r w ι hw hι φ hφ => ?_⟩
  rw [UpperTheory.Reformulated.B.Gul4.mem_iff μ τ κ p hp hμ] at hφ
  refine ⟨?_, fun g => Submodule.subset_span (UpperTheory.Reformulated.B.Gul4.isX_translate μ τ κ p hτ w ι hw hι φ hφ g)⟩
  obtain ⟨-, -, -, U, hU, fφ⟩ := hφ
  exact UpperTheory.isOpen_right_invariance ι (GroundTheory.Automorphic.MultiplicityOne.finProj K 2) _ φ
    ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.embEx 2 w hw).2 ι hι).1 ((UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levLaws 2 _).1 U hU).1.2 fφ
end

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.xMem :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), IdemA κ p → (∀ S φ, φ ∈ Xs μ τ κ p S ↔ IsX μ τ κ p S φ) ∧ (CuspIrr μ τ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι → ∀ φ ∈ Xs μ τ κ p (im w), IsOpen {g | rS ι g φ = φ} ∧ ∀ g, rS ι g φ ∈ Xs μ τ κ p (im w)) :=
  _root_.UpperTheory.Reformulated.B.Gul4.xMem
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.HopEmb
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem cosets_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {W : Subgroup G}
    (hW : CO W) (g : G) : {c : G ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}.Finite := by
  haveI : DiscreteTopology (G ⧸ W) := QuotientGroup.discreteTopology hW.2
  have hc : Continuous fun u : G => (QuotientGroup.mk (u * g) : G ⧸ W) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hW.1.image hc).finite_of_discrete).subset ?_
  rintro c ⟨u, hu, rfl⟩
  exact ⟨u, hu, rfl⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.hopEmb :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) {r : ℕ} (w : Fin r → Pl K) (ι : GS n w →* FA K n), Function.Injective w → IsEmb w ι → ∀ U, Lev U → ∀ φ : G1 K n → ℂ, FixF (levOn (im w) U) φ →
      ∀ g, hop (levOn (im w) U) (ι g) φ = hopR (rS ι) (Subgroup.pi Set.univ fun i => U (w i)) g φ := by
  intro K _ _ n r w ι hw hι U hU φ hφ g
  obtain ⟨hcf, hoff, -, hcomm, hmem⟩ := ((embEx n w hw).2 ι hι).2
  have hcf' : ∀ (v : Pl K), GM.cf v (1 : FA K n) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    intro v
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      have := hcf 1 i
      rw [map_one] at this
      rw [this]
      exact Subgroup.one_mem _
    · have := hoff 1 v hv
      rw [map_one] at this
      rw [this]
      exact Subgroup.one_mem _
  have hcf1 : ∀ i, GM.cf (w i) (1 : FA K n) = 1 := by
    intro i
    have := hcf 1 i
    rwa [map_one] at this
  set L := levOn (im w) U with hL
  set W : Subgroup (GS n w) := Subgroup.pi Set.univ fun i => U (w i) with hWdef
  have hWL : ∀ a ∈ W, ι a ∈ L := fun a ha =>
    (hmem U _).2 ⟨a, 1, (mul_one _).symm, fun i => ha i trivial, hcf1, hcf'⟩
  have hLW : ∀ x, ι x ∈ L → x ∈ W := by
    intro x hx
    obtain ⟨a, h', e, ha, h1, -⟩ := (hmem U _).1 hx
    have e' : h' = ι (a⁻¹ * x) := by rw [map_mul, map_inv, e, inv_mul_cancel_left]
    have e1 : a⁻¹ * x = 1 := funext fun i => by
      rw [← hcf (a⁻¹ * x) i, ← e', h1]
      rfl
    rw [(inv_mul_eq_one.1 e1).symm]
    exact fun i _ => ha i
  have hW : CO W :=
    ⟨isCompact_univ_pi fun j => (hU (w j)).1.1, isOpen_set_pi Set.finite_univ fun j _ => (hU (w j)).1.2⟩
  let e : GS n w ⧸ W → FA K n ⧸ L := fun c => QuotientGroup.mk (ι c.out)
  have he : ∀ y, e (QuotientGroup.mk y) = QuotientGroup.mk (ι y) := by
    intro y
    refine QuotientGroup.eq.2 ?_
    have := hWL _ (QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk y : GS n w ⧸ W)))
    rwa [map_mul, map_inv] at this
  have hbij : Set.BijOn e {c : GS n w ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}
      {c : FA K n ⧸ L | ∃ u ∈ L, c = QuotientGroup.mk (u * ι g)} := by
    refine ⟨?_, ?_, ?_⟩
    · rintro c ⟨u, hu, rfl⟩
      exact ⟨ι u, hWL u hu, by rw [he, map_mul]⟩
    · intro c _ d _ hcd
      have h1 := QuotientGroup.eq.1 hcd
      rw [← map_inv, ← map_mul] at h1
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
      exact QuotientGroup.eq.2 (hLW _ h1)
    · rintro c ⟨u, hu, rfl⟩
      obtain ⟨a, h', e', ha, h1, h2⟩ := (hmem U _).1 hu
      have hh' : h' ∈ L := (hmem U _).2 ⟨1, h', by simp, fun i => Subgroup.one_mem _, h1, h2⟩
      refine ⟨QuotientGroup.mk (a * g), ⟨a, fun i _ => ha i, rfl⟩, ?_⟩
      rw [he, map_mul, e']
      refine QuotientGroup.eq.2 ?_
      have : (ι a * ι g)⁻¹ * (ι a * h' * ι g) = h' := by
        rw [mul_assoc (ι a) h', (hcomm g h' h1).symm.eq]
        group
      rwa [this]
  have hfin := cosets_finite hW g
  funext x
  have hR : hopR (rS ι) W g φ x = ∑ᶠ c ∈ {c : GS n w ⧸ W | ∃ u ∈ W, c = QuotientGroup.mk (u * g)}, φ (x * fin1 (ι c.out)) := by
    unfold hopR
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_apply]
    rfl
  rw [hR]
  unfold hop
  symm
  refine finsum_mem_eq_of_bijOn e hbij fun c _ => ?_
  have hl : (ι c.out)⁻¹ * (e c).out ∈ L := QuotientGroup.eq.1 (QuotientGroup.out_eq' (e c)).symm
  have := hφ _ hl (x * fin1 (ι c.out))
  rw [← this, mul_assoc, ← map_mul, mul_inv_cancel_left]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevBlock
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

private theorem bval (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (PositivityTheory.Rg.Tf.Adel.blk x y).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 y.val) := rfl

private def bHom : GL (Fin a) R × GL (Fin b) R →* GL (Fin (a + b)) R where
  toFun p := PositivityTheory.Rg.Tf.Adel.blk p.1 p.2
  map_one' := by
    apply Units.ext
    simp only [bval, Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.fromBlocks_one, Matrix.reindex_apply,
      Matrix.submatrix_one_equiv]
  map_mul' p q := by
    apply Units.ext
    simp only [Units.val_mul, Prod.fst_mul, Prod.snd_mul, bval, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem bHom_map (f : R →+* S) (x : GL (Fin a) R) (y : GL (Fin b) R) :
    Matrix.GeneralLinearGroup.map f (bHom (x, y)) =
      bHom (Matrix.GeneralLinearGroup.map f x, Matrix.GeneralLinearGroup.map f y) := by
  apply Units.ext
  ext i j
  change f ((PositivityTheory.Rg.Tf.Adel.blk x y).val i j) = (PositivityTheory.Rg.Tf.Adel.blk _ _).val i j
  simp only [bval, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

private theorem bHom_cont [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (bHom : GL (Fin a) R × GL (Fin b) R → GL (Fin (a + b)) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

private theorem bHom_ent (O : Subring S) (x : GL (Fin a) S) (y : GL (Fin b) S) (hx : ∀ i j, x i j ∈ O)
    (hy : ∀ i j, y i j ∈ O) (i j : Fin (a + b)) : bHom (x, y) i j ∈ O := by
  change (PositivityTheory.Rg.Tf.Adel.blk x y).val i j ∈ O
  simp only [bval, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [hx, hy]

end SlopeTestRemainingChoices

section Glob

variable {K : Type} [Field K] [NumberField K] {a b : ℕ}

private theorem bHom_int (v : Pl K) {x : Gw a v} {y : Gw b v} (hx : x ∈ GLnLocal.integralGL (v.adicCompletion K) a)
    (hy : y ∈ GLnLocal.integralGL (v.adicCompletion K) b) :
    bHom (x, y) ∈ GLnLocal.integralGL (v.adicCompletion K) (a + b) := by
  rw [GLnLocal.mem_integralGL_iff, ← map_inv]
  have h1 := (GLnLocal.mem_integralGL_iff _ _).1 hx
  have h2 := (GLnLocal.mem_integralGL_iff _ _).1 hy
  exact ⟨bHom_ent _ _ _ h1.1 h2.1, bHom_ent _ _ _ h1.2 h2.2⟩

private theorem finAt_bHom (v : Pl K) (x : AdelicGLn.AdelicGL K a) (y : AdelicGLn.AdelicGL K b) :
    finAt v (bHom (x, y)) = bHom (finAt v x, finAt v y) :=
  bHom_map (finEval v) x y

private theorem finEmb_bHom (x : FA K a) (y : FA K b) :
    finEmb K (a + b) (bHom (x, y)) = bHom (finEmb K a x, finEmb K b y) := by
  apply (AdelicGLn.prodEquiv K (a + b)).injective
  rw [prodEquiv_finEmb]
  have e1 : ∀ {c : ℕ} (p : AdelicGLn.AdelicGL K c), (AdelicGLn.prodEquiv K c p).1 =
      Matrix.GeneralLinearGroup.map (show AdeleRing (𝓞 K) K →+* InfiniteAdeleRing K from RingHom.fst _ _) p :=
    fun p => Units.ext (Matrix.ext fun _ _ => rfl)
  have e2 : ∀ {c : ℕ} (p : AdelicGLn.AdelicGL K c), (AdelicGLn.prodEquiv K c p).2 =
      Matrix.GeneralLinearGroup.map (show AdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 K) K from RingHom.snd _ _) p :=
    fun p => Units.ext (Matrix.ext fun _ _ => rfl)
  have h1 : ∀ (p : AdelicGLn.AdelicGL K a) (q : AdelicGLn.AdelicGL K b),
      (AdelicGLn.prodEquiv K (a + b) (bHom (p, q))).1 =
        bHom ((AdelicGLn.prodEquiv K a p).1, (AdelicGLn.prodEquiv K b q).1) := by
    intro p q
    rw [e1, e1, e1, bHom_map]
  have h2 : ∀ (p : AdelicGLn.AdelicGL K a) (q : AdelicGLn.AdelicGL K b),
      (AdelicGLn.prodEquiv K (a + b) (bHom (p, q))).2 =
        bHom ((AdelicGLn.prodEquiv K a p).2, (AdelicGLn.prodEquiv K b q).2) := by
    intro p q
    rw [e2, e2, e2, bHom_map]
  refine Prod.ext ?_ ?_
  · rw [h1, prodEquiv_finEmb, prodEquiv_finEmb]
    exact (map_one bHom).symm
  · rw [h2, prodEquiv_finEmb, prodEquiv_finEmb]

private theorem coe_finite_adele_inclusion {n : ℕ} {u : FA K n} (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    ((fin1 u : G1 K n) : AdelicGLn.AdelicGL K n) = finEmb K n u :=
  congrArg Subtype.val (MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu)))

private theorem zt0 : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

end Glob

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.levBlock :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v), Lev U → ∀ g, ∃ U₂ : ∀ v : Pl K, Subgroup (Gw 2 v), Lev U₂ ∧ ∀ u₁ ∈ levOn (im w) U₂, ∀ u₂ ∈ levOn (im w) U₂,
        ∃ u ∈ levOn (im w) U, ∀ k : archCompact K (2 + 2), lv (fin1 u₁) (fin1 u₂) 0 * arc1 k * fin1 (ι₄ g) = arc1 k * fin1 (ι₄ g) * fin1 u := by
  intro K _ _ r w ι hw hι U hU g
  obtain ⟨h4, -, hcomm, -, -, hconj⟩ := levLaws (K := K) (2 + 2) (im w)
  obtain ⟨U', hU', hc⟩ := hconj w ι hw hι rfl U hU g
  let U₂ : ∀ v : Pl K, Subgroup (Gw 2 v) := fun v =>
    GLnLocal.integralGL (v.adicCompletion K) 2 ⊓
      ((U' v).comap (bHom.comp (MonoidHom.inl _ _)) ⊓ (U' v).comap (bHom.comp (MonoidHom.inr _ _)))
  have hU₂ : Lev U₂ := by
    intro v
    have ho : IsOpen (U₂ v : Set (Gw 2 v)) :=
      (GLnLocal.isOpen_integralGL _ _).inter
        (((hU' v).1.2.preimage (bHom_cont.comp (continuous_id.prodMk continuous_const))).inter
          ((hU' v).1.2.preimage (bHom_cont.comp (continuous_const.prodMk continuous_id))))
    exact ⟨⟨(GLnLocal.isCompact_integralGL _ _).of_isClosed_subset ((U₂ v).isClosed_of_isOpen ho)
      (fun x hx => hx.1), ho⟩, inf_le_left⟩
  refine ⟨U₂, hU₂, fun u₁ h₁ u₂ h₂ => ?_⟩
  have hm : bHom (u₁, u₂) ∈ levOn (im w) U' := by
    intro v
    have e₁ := h₁ v
    have e₂ := h₂ v
    rw [finEmb_bHom, finAt_bHom]
    by_cases hv : v ∈ im w
    · simp only [hv, if_true] at e₁ e₂ ⊢
      have := (U' v).mul_mem e₁.2.1 e₂.2.2
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul] at this
      simpa using this
    · simp only [hv, if_false] at e₁ e₂ ⊢
      exact bHom_int v e₁ e₂
  have hl : lv (fin1 u₁) (fin1 u₂) 0 = fin1 (bHom (u₁, u₂)) := by
    have h2 := ((levLaws (K := K) 2 (im w)).1 U₂ hU₂).2
    apply Subtype.ext
    rw [blkLaws.1, neg_zero, zt0, mul_one, mul_one, coe_finite_adele_inclusion (h2 h₁), coe_finite_adele_inclusion (h2 h₂), coe_finite_adele_inclusion ((h4 U' hU').2 hm),
      finEmb_bHom]
    rfl
  refine ⟨_, hc _ hm, fun k => ?_⟩
  rw [hl, ← (hcomm k _).eq, mul_assoc, mul_assoc, ← map_mul, ← map_mul]
  congr 2
  group
end
