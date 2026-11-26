module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExponentialGluing.ExpNegGlueHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UnipotentVanishing.InfAtUnipInvEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoExpMulPoly
noncomputable section

open NumberField MeasureTheory Filter Topology
open scoped ENNReal
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E.E3

namespace GlobalTheory.CompanionTheory.LocExponent

theorem tendsto_exp_mul_poly (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (M : ℕ) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * ε * t)) * (1 + B * (1 + t)) ^ M) atTop (𝓝 0) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop M (show 0 < 2 * ε by positivity)).tendsto_div_nhds_zero
  have h2 := h.const_mul ((1 + 2 * B) ^ M)
  rw [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have h0 : 0 ≤ 1 + B * (1 + t) := by nlinarith
    positivity
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have h1 : 1 + B * (1 + t) ≤ (1 + 2 * B) * t := by nlinarith
    have h0 : 0 ≤ 1 + B * (1 + t) := by nlinarith
    have hp := pow_le_pow_left₀ h0 h1 M
    rw [Real.exp_neg, mul_comm (Real.exp (2 * ε * t))⁻¹, ← div_eq_mul_inv, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by rwa [mul_pow] at hp) (Real.exp_pos _).le

theorem re_lt_of_dec {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (μ : Measure G) [μ.IsHaarMeasure] (ρ : ℝ) (a : ℝ → G)
    {F : G → ℂ} (hdecF : PositivityTheory.Rg.Rs.JExpNegGlue.Dec μ ρ a F) (hF0 : F ≠ 0) {c : ℂ}
    (hFeq : ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g) : c.re < ρ := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, F g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (funext h)
  obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds g₀
  have hFc := hdecF.1
  set I := ∫ g in Q, ‖F g‖ ^ 2 ∂μ with hI
  have hIpos : 0 < I := by
    have hint : IntegrableOn (fun g => ‖F g‖ ^ 2) Q μ := (hFc.norm.pow 2).continuousOn.integrableOn_compact hQc
    rw [hI, setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun g => by show (0 : ℝ) ≤ ‖F g‖ ^ 2; positivity) hint]
    have hopen : IsOpen (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q) :=
      (hFc.norm.pow 2).isOpen_support.inter isOpen_interior
    have hne : (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q).Nonempty :=
      ⟨g₀, by simp [Function.mem_support, hg₀], mem_interior_iff_mem_nhds.2 hQn⟩
    exact lt_of_lt_of_le (hopen.measure_pos μ hne)
      (measure_mono (Set.inter_subset_inter_right _ interior_subset))
  have hval : ∀ t : ℝ, Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖F (a t * g)‖ ^ 2 ∂μ =
      Real.exp (2 * (c.re - ρ) * t) * I := by
    intro t
    have hre : (c * (t : ℂ)).re = c.re * t := by simp
    have hpt : ∀ g, ‖F (a t * g)‖ ^ 2 = Real.exp (c.re * t) ^ 2 * ‖F g‖ ^ 2 := by
      intro g
      rw [hFeq, norm_mul, Complex.norm_exp, mul_pow, hre]
    simp_rw [hpt]
    rw [integral_const_mul, ← mul_assoc, sq, ← Real.exp_add, ← Real.exp_add]
    congr 2; ring
  have hlim := hdecF.2 Q hQc
  rw [tendsto_congr hval] at hlim
  by_contra hge
  push Not at hge
  have hev : ∀ᶠ t in atTop, I ≤ Real.exp (2 * (c.re - ρ) * t) * I := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h1 : 1 ≤ Real.exp (2 * (c.re - ρ) * t) :=
      Real.one_le_exp (by nlinarith [mul_nonneg (sub_nonneg.2 hge) ht])
    nlinarith
  have := ge_of_tendsto hlim hev
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}


omit [IsCMField E] in
theorem mult_of_lat {S : Set (GA E N)} {n : ℕ}
    (h : ∀ x, {γ : An.lat E N | (γ : GA E N) * x ∈ S}.encard ≤ n) : Mult S n := by
  intro x
  have hle : (ratGL E N).range ≤ An.lat E N := le_sup_left
  refine le_trans ?_ (h x)
  have hinj : Set.InjOn (Subgroup.inclusion hle) {γ : (ratGL E N).range | (γ : GA E N) * x ∈ S} :=
    (Subgroup.inclusion_injective hle).injOn
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨γ, hγ, rfl⟩
  exact hγ

omit [IsCMField E] in
theorem rho_nonneg {r : ℕ} (hrN : r < N) : 0 ≤ An.rho E N r := by
  unfold An.rho
  have : (r : ℝ) ≤ N := by exact_mod_cast hrN.le
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 this)) two_pos.le)

theorem integral_ctn_le (hSize : SizeT) {φ : GA E N → ℂ} (hφ : Continuous φ) (hLoc : Loc φ) {r : ℕ}
    (hr : 0 < r) (hrN : r < N) (μ : Measure (GA E N)) [hμ : μ.IsHaarMeasure] {Q : Set (GA E N)} (hQ : IsCompact Q) :
    ∃ (K B : ℝ) (M : ℕ), 0 ≤ K ∧ 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      ∫ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ ^ 2 ∂μ ≤
        K * (Real.exp (2 * An.rho E N r * t) * (1 + B * (1 + t)) ^ M) := by
  obtain ⟨D, hD, hD0⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_isCompact_superset_unipFundamentalDomain
    (K := E) (n := N) (r := r)
  obtain ⟨C₁, hC₁⟩ := l2glue.count_le count_holds hr hrN hD hQ
  obtain ⟨C, M, hCM⟩ := hLoc μ hμ
  obtain ⟨B, hB, hsz⟩ := hSize E N (GroundTheory.Automorphic.AutomorphicForm.unipGL '' D) Q
    (hD.image GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL) hQ
  have hρ : 0 ≤ An.rho E N r := rho_nonneg hrN
  refine ⟨max C 0 * (max C₁ 0 + 1), B, M, by positivity, hB, fun t ht => ?_⟩
  set e := Real.exp (2 * An.rho E N r * t) with he
  set n : ℕ := ⌈C₁ * e⌉₊ with hn
  set R : ℝ := B * (1 + t) with hR
  have hR0 : 0 ≤ R := by positivity
  have hS := l2glue.isCompact_sset r t hD hQ
  have hmult : Mult (l2glue.sset E N r t D Q) n := mult_of_lat (hC₁ t ht)
  have hlog : ∀ g ∈ l2glue.sset E N r t D Q, logSize g ≤ R := by
    rintro _ ⟨⟨X, q⟩, ⟨hX, hq⟩, rfl⟩
    have hx := hsz _ ⟨X, hX, rfl⟩ q hq (fun i : Fin N => if (i : ℕ) < r then t else 0)
    refine hx.trans (mul_le_mul_of_nonneg_left ?_ hB)
    have : ‖fun i : Fin N => if (i : ℕ) < r then t else 0‖ ≤ t := by
      refine (pi_norm_le_iff_of_nonneg ht).2 fun i => ?_
      split_ifs
      · rw [Real.norm_of_nonneg ht]
      · simpa using ht
    linarith
  have h3 := hCM _ hS n R hR0 hmult hlog
  have h2 := l2glue.swap μ φ hφ r t hD hD0 hQ
  have h1 := l2glue.integral_le_toReal (μ.restrict Q) (fun g => An.ctn r φ (An.aR E N r t * g))
  have hP : 0 ≤ (1 + R) ^ M := by positivity
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  have hnle : (n : ℝ) ≤ (max C₁ 0 + 1) * e := by
    have h6 : (n : ℝ) ≤ ⌈max C₁ 0 * e⌉₊ := by
      exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by linarith))
    have h7 := (Nat.ceil_lt_add_one (show 0 ≤ max C₁ 0 * e by positivity)).le
    nlinarith
  have h4 : ENNReal.ofReal (C * n * (1 + R) ^ M) ≤ ENNReal.ofReal (max C 0 * n * (1 + R) ^ M) := by
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hP)
  have h5 : (∫⁻ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ₑ ^ 2 ∂μ).toReal ≤ max C 0 * n * (1 + R) ^ M := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h2.trans (h3.trans h4))
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  calc _ ≤ _ := h1
    _ ≤ _ := h5
    _ ≤ max C 0 * ((max C₁ 0 + 1) * e) * (1 + R) ^ M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnle (by positivity)) hP
    _ = _ := by ring

theorem tendsto_ctn (hSize : SizeT) {φ : GA E N → ℂ} (hφ : Continuous φ) (hLoc : Loc φ) {r : ℕ}
    (hr : 0 < r) (hrN : r < N) (μ : Measure (GA E N)) [hμ : μ.IsHaarMeasure] {ε : ℝ} (hε : 0 < ε)
    {Q : Set (GA E N)} (hQ : IsCompact Q) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * (An.rho E N r + ε) * t)) *
      ∫ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, B, M, hK, hB, hb⟩ := integral_ctn_le hSize hφ hLoc hr hrN μ hQ
  have hlim := (tendsto_exp_mul_poly B ε hB hε M).const_mul K
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => by positivity)) ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  have h := mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos (-(2 * (An.rho E N r + ε) * t))).le
  refine h.trans (le_of_eq ?_)
  have hee : Real.exp (-(2 * (An.rho E N r + ε) * t)) * Real.exp (2 * An.rho E N r * t) = Real.exp (-(2 * ε * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hee]; ring

end GlobalTheory.CompanionTheory.LocExponent

namespace GlobalTheory.CompanionTheory.LocExponent


open PositivityTheory.Rg.Rs.JExpNegGlue in
theorem locNonPosGlue_holds : LocNonPosGlue := by
  intro hSize E _ _ _ N φ hA hLoc r hr0 hrN c hc
  have : LocallyCompactSpace (GA E N) := by
    set_option synthInstance.maxHeartbeats 400000 in
      exact inferInstance
  have : T2Space (GA E N) := by
    set_option synthInstance.maxHeartbeats 400000 in
      exact inferInstance
  obtain ⟨haR, -, -, hct⟩ := dict_holds E N
  have hctn := (hct φ hA r hr0 hrN).2
  obtain ⟨F₀, hF₀, F, hFspan, hF0, hFeq⟩ := hc
  obtain ⟨c₀, -, hF₀eq⟩ := hctn F₀ hF₀
  subst hF₀eq
  have hφc : Continuous φ.1 := GlobalTheory.CompanionTheory.ConstTerm.continuous_of_isOpen_stab φ hA.level
  let μ : Measure (GA E N) := Measure.haar
  have : μ.IsHaarMeasure := inferInstance
  set a : ℝ → GA E N := aT E N r with ha
  have hcomm : ∀ s t, a s * a t = a t * a s := aT_comm E N r
  have hlt : ∀ ε : ℝ, 0 < ε → c.re < An.rho E N r + ε := by
    intro ε hε
    have hdec_ctn : Dec μ (An.rho E N r + ε) a (An.ctn r φ.1) := by
      have hctc : Continuous (An.ctn r φ.1) := by
        have : SecondCountableTopology (GA E N) := by
          set_option synthInstance.maxHeartbeats 400000 in
            exact inferInstance
        have : FirstCountableTopology (GA E N) := by
          set_option synthInstance.maxHeartbeats 400000 in
            exact inferInstance
        obtain ⟨C, hC, hDC⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)
        have : IsFiniteMeasure ((GroundTheory.Automorphic.AutomorphicForm.unipMeasure E N r).restrict (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r)) :=
          isFiniteMeasure_restrict.2 (by rw [GroundTheory.Automorphic.AutomorphicForm.unipMeasure_unipFundamentalDomain]; exact ENNReal.one_ne_top)
        have hf : Continuous (Function.uncurry fun (g : GA E N) (X : GroundTheory.Automorphic.AutomorphicForm.UPos N r → AdeleRing (𝓞 E) E) =>
            φ.1 (GroundTheory.Automorphic.AutomorphicForm.unipGL X * g)) :=
          hφc.comp ((GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL.comp continuous_snd).mul continuous_fst)
        have h := continuous_parametric_integral_of_continuous
          (μ := (GroundTheory.Automorphic.AutomorphicForm.unipMeasure E N r).restrict (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r)) hf hC
        have e : ∀ g : GA E N, GroundTheory.Automorphic.AutomorphicForm.constantTerm r φ.1 g = ∫ X in C, φ.1 (GroundTheory.Automorphic.AutomorphicForm.unipGL X * g)
            ∂((GroundTheory.Automorphic.AutomorphicForm.unipMeasure E N r).restrict (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r)) := by
          intro g
          rw [Measure.restrict_restrict' GroundTheory.Automorphic.AutomorphicForm.measurableSet_unipFundamentalDomain, Set.inter_eq_right.2 hDC]
          rfl
        unfold An.ctn
        exact continuous_const.mul (h.congr fun g => (e g).symm)
      refine ⟨hctc, fun Q hQ => ?_⟩
      have h := tendsto_ctn hSize hφc hLoc hr0 hrN μ hε hQ
      simp only [ha, haR]
      exact h
    have hdecF : Dec μ (An.rho E N r + ε) a F := by
      refine Submodule.span_induction (p := fun H _ => Dec μ (An.rho E N r + ε) a H) ?_ (dec_zero μ _ a)
        (fun x y _ _ hx hy => dec_add μ _ a hx hy) (fun b x _ hx => dec_smul μ _ a b hx) hFspan
      rintro _ ⟨s, rfl⟩
      convert dec_smul μ _ a c₀ (dec_translate μ _ a hcomm s hdec_ctn) using 1
    exact re_lt_of_dec μ _ a hdecF hF0 hFeq
  have hle : c.re ≤ An.rho E N r := le_of_forall_pos_le_add fun ε hε => (hlt ε hε).le
  have hd : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  rw [An.rho] at hle
  unfold pE
  have : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 := by
    rw [div_le_iff₀ hd]; linarith
  linarith

end GlobalTheory.CompanionTheory.LocExponent

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEquivariantForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEquivariantForm
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.EqForm

section LinAlg

theorem exists_form_of_faithful {k Q : Type} [Field k] [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]
    (R : Type) [CommRing R] [Algebra k R] [Module R Q] [IsScalarTower k R Q]
    (hf : ∀ r : R, (∀ x : Q, r • x = 0) → r = 0) (q₀ : Q) (h0 : q₀ ≠ 0) :
    ∃ μ : Module.Dual k Q, μ ≠ 0 ∧ ∀ (r : R) (c : k), r • q₀ = c • q₀ → ∀ x, μ (r • x) = c * μ x := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R Q q₀)
  have hI : ∀ r : R, r ∈ I ↔ r • q₀ = 0 := fun r => by simp [I, LinearMap.mem_ker]
  haveI : Module.Finite R Q := Module.Finite.of_restrictScalars_finite k R Q
  have hne : I • (⊤ : Submodule R Q) ≠ ⊤ := by
    intro htop
    obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I (⊤ : Submodule R Q)
      Module.Finite.fg_top (by rw [htop])
    have hr0 : r = 0 := hf r fun x => hr2 x trivial
    rw [hr0, zero_sub, hI] at hr1
    apply h0
    simpa using hr1
  let M : Submodule k Q := (I • (⊤ : Submodule R Q)).restrictScalars k
  have hM : M < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne ?_
    apply Submodule.restrictScalars_injective k
    simpa [M] using h
  obtain ⟨μ, hμ0, hμ⟩ := Submodule.exists_le_ker_of_lt_top M hM
  refine ⟨μ, hμ0, fun r c hr x => ?_⟩
  have hmem : r - algebraMap k R c ∈ I := by
    rw [hI, sub_smul, hr, algebraMap_smul, sub_self]
  have hx : (r - algebraMap k R c) • x ∈ M := by
    have h2 : (r - algebraMap k R c) • x ∈ I • (⊤ : Submodule R Q) :=
      Submodule.smul_mem_smul hmem (Submodule.mem_top)
    exact (Submodule.restrictScalars_mem k _ _).2 h2
  have h1 : μ ((r - algebraMap k R c) • x) = 0 := hμ hx
  rw [sub_smul, algebraMap_smul, map_sub, μ.map_smul c x, smul_eq_mul, sub_eq_zero] at h1
  exact h1

theorem exists_eigenform_of_commute {Q : Type} [AddCommGroup Q] [Module ℂ Q] [FiniteDimensional ℂ Q] {ι : Type}
    (A : ι → Module.End ℂ Q) (hc : ∀ i j, Commute (A i) (A j))
    (ξ : ι → ℂ) (q₀ : Q) (h0 : q₀ ≠ 0) (hq : ∀ i, A i q₀ = ξ i • q₀) :
    ∃ μ : Module.Dual ℂ Q, μ ≠ 0 ∧ ∀ i x, μ (A i x) = ξ i * μ x := by
  have hcomm : ∀ a ∈ Set.range A, ∀ b ∈ Set.range A, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hc i j
  letI : IsMulCommutative (Algebra.adjoin ℂ (Set.range A)) :=
    Algebra.isMulCommutative_adjoin ℂ (fun a ha b hb _ => hcomm a ha b hb)
  letI : CommRing (Algebra.adjoin ℂ (Set.range A)) := by
    open scoped IsMulCommutative in exact inferInstance
  obtain ⟨μ, hμ0, hμ⟩ := exists_form_of_faithful (k := ℂ) (Q := Q) (Algebra.adjoin ℂ (Set.range A))
    (fun r hr => Subtype.ext (LinearMap.ext fun x => by
      change (r : Module.End ℂ Q) x = 0 at *
      exact hr x)) q₀ h0
  refine ⟨μ, hμ0, fun i x => ?_⟩
  exact hμ ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ (ξ i) (hq i) x

end LinAlg

section Smooth

variable {Γ W : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup W] [Module ℂ W]

theorem mem_fixed_iff (ρ : Representation ℂ Γ W) (K : Subgroup Γ) (v : W) :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have h1 := h ⟨k, hk⟩
    simpa using h1
  · intro h k
    have h1 := h k k.2
    simpa using h1

theorem exists_eigenform_of_smooth [IsTopologicalGroup Γ] (ρ : Representation ℂ Γ W) (hρ : IsSmooth ρ)
    (K : Subgroup Γ) (hK : IsCompact (K : Set Γ)) (hcomm : ∀ a b : Γ, a * b = b * a)
    (hfin : FiniteDimensional ℂ (fixed ρ K)) (ξ : Γ → ℂ) (w₀ : W) (h0 : w₀ ≠ 0)
    (hw : ∀ t, ρ t w₀ = ξ t • w₀) (hξ : ∀ k ∈ K, ξ k = 1) :
    ∃ lam : Module.Dual ℂ W, lam ≠ 0 ∧ ∀ t w, lam (ρ t w) = ξ t * lam w := by
  have hst : ∀ t, ∀ v ∈ fixed ρ K, ρ t v ∈ fixed ρ K := by
    intro t v hv
    refine (mem_fixed_iff ρ K _).2 fun k hk => ?_
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply,
      (mem_fixed_iff ρ K v).1 hv k hk]
  let A : Γ → Module.End ℂ (fixed ρ K) := fun t => (ρ t).restrict (hst t)
  have hA : ∀ t (s : fixed ρ K), ((A t s : fixed ρ K) : W) = ρ t s := fun t s => rfl
  have hAc : ∀ a b, Commute (A a) (A b) := by
    intro a b
    refine LinearMap.ext fun s => Subtype.ext ?_
    show ρ a (ρ b s) = ρ b (ρ a s)
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
  have hw₀ : w₀ ∈ fixed ρ K := (mem_fixed_iff ρ K _).2 fun k hk => by rw [hw, hξ k hk, one_smul]
  obtain ⟨μ, hμ0, hμ⟩ := exists_eigenform_of_commute A hAc ξ ⟨w₀, hw₀⟩
    (fun h => h0 (congrArg Subtype.val h)) (fun t => Subtype.ext (hw t))
  have hnorm : ∀ t : Γ, t ∈ Subgroup.normalizer (K : Set Γ) := by
    intro t
    refine Subgroup.mem_normalizer_iff.2 fun h => ?_
    have e : t * h * t⁻¹ = h := by rw [hcomm t h, mul_inv_cancel_right]
    rw [e]
  have hE : ∀ t w, GlobalTheory.LocGL.idem hρ hK (ρ t w) = ρ t (GlobalTheory.LocGL.idem hρ hK w) := by
    intro t w
    have h1 : w - GlobalTheory.LocGL.idem hρ hK w ∈ twKer ρ K 1 := by
      rw [← GlobalTheory.LocGL.idem_eq_zero_iff hρ hK, map_sub,
        GlobalTheory.LocGL.idem_of_mem hρ hK (GlobalTheory.LocGL.idem_mem hρ hK w), sub_self]
    have h2 := twKer_le_comap ρ K t (hnorm t) h1
    rw [Submodule.mem_comap, ← GlobalTheory.LocGL.idem_eq_zero_iff hρ hK, map_sub, map_sub,
      GlobalTheory.LocGL.idem_of_mem hρ hK (hst t _ (GlobalTheory.LocGL.idem_mem hρ hK w)), sub_eq_zero] at h2
    exact h2
  let e : W →ₗ[ℂ] fixed ρ K := (GlobalTheory.LocGL.idem hρ hK).codRestrict _ (GlobalTheory.LocGL.idem_mem hρ hK)
  refine ⟨μ ∘ₗ e, ?_, ?_⟩
  · intro h
    apply hμ0
    refine LinearMap.ext fun s => ?_
    have h1 : e (s : W) = s := Subtype.ext (GlobalTheory.LocGL.idem_of_mem hρ hK s.2)
    have h2 := LinearMap.congr_fun h (s : W)
    simpa [h1] using h2
  · intro t w
    have h1 : e (ρ t w) = A t (e w) := Subtype.ext (hE t w)
    simp only [LinearMap.comp_apply]
    rw [h1, hμ]

end Smooth

section Diag

variable {L : Type} [Field L]

theorem isDiagM_commute {n : ℕ} {g h : GL (Fin n) L} (hg : IsDiagM g) (hh : IsDiagM h) : g * h = h * g := by
  have key : ∀ a : GL (Fin n) L, IsDiagM a →
      (a : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (a : Matrix (Fin n) (Fin n) L) i i := by
    intro a ha
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [ha i j hij, Matrix.diagonal_apply_ne _ hij]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, key g hg, key h hh, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [mul_comm]

end Diag

theorem eqFormU_of (hA4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], A4 G)
    (hIw : IwahoriU) (hDom : DomU) (hKU : KUFacts) : EqFormU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ hu hadm ξ y hy hyt hyk
  obtain ⟨D, hJ, hN, hNm, hT⟩ := hIw L ϖ σ q hu n
  obtain ⟨-, -, hIK, t, htD, htS⟩ := hKU L ϖ σ q n hu
  have hdom : D.IsStrDom ⟨t, (hT t).2 htD⟩ := (hDom L ϖ σ q hu n D hJ hN hNm hT ⟨t, (hT t).2 htD⟩).2 htS
  have a4 := (hA4 (GU σ n) D V ρ hadm ⟨_, hdom⟩).2
  have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
  haveI hfJ : FiniteDimensional ℂ (fixed ρ D.J) := hadm.2 D.J D.isOpen_J D.isCompact_J
  have hfin : FiniteDimensional ℂ (fixed (D.piN ρ) D.JT) := by
    let f : fixed ρ D.J →ₗ[ℂ] Jacquet ρ D.N := (twKer ρ D.N 1).mkQ ∘ₗ (fixed ρ D.J).subtype
    have hle : fixed (D.piN ρ) D.JT ≤ LinearMap.range f := by
      intro w hw
      obtain ⟨v, hv⟩ := a4 w hw
      exact ⟨v, hv⟩
    exact Submodule.finiteDimensional_of_le hle
  have hsm : IsSmooth (D.piN ρ) := by
    intro w
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    let Sg : Subgroup D.T :=
      { carrier := {g | D.piN ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    have hop : IsOpen {g : D.T | ρ (g : GU σ n) v = v} := (hadm.1 v).preimage continuous_subtype_val
    refine Sg.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hop.mem_nhds (by simp)) ?_)
    intro g hg
    show D.piN ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
    have hp : D.piN ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ (g : GU σ n) v) := rfl
    rw [hp, show ρ (g : GU σ n) v = v from hg]
  have hcpt : IsCompact (D.JT : Set D.T) := by
    rw [Subtype.isCompact_iff]
    have e : Subtype.val '' (D.JT : Set D.T) = (D.J : Set (GU σ n)) ∩ D.T := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨ha, a.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, h2⟩, h1, rfl⟩
    rw [e]
    exact D.isCompact_J.inter_right D.isClosed_alt
  have hcomm : ∀ a b : D.T, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact isDiagM_commute ((hT _).1 a.2) ((hT _).1 b.2)
  have hmk : ∀ x : V, x ∈ jacU ρ ↔ (Submodule.Quotient.mk x : Jacquet ρ D.N) = 0 := by
    intro x
    rw [Submodule.Quotient.mk_eq_zero, hker]
  obtain ⟨lam₀, hlam0, hlam⟩ := exists_eigenform_of_smooth (D.piN ρ) hsm D.JT hcpt hcomm hfin
    (fun a => ξ (a : GU σ n)) (Submodule.Quotient.mk y) (fun h => hy ((hmk y).2 h))
    (fun a => by
      have hp : D.piN ρ a (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρ (a : GU σ n) y) := rfl
      rw [hp, ← Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
      exact (hmk _).1 (hyt _ ((hT _).1 a.2)))
    (fun k hk => hyk _ (hIK (hJ ▸ hk)) ((hT _).1 k.2))
  refine ⟨lam₀ ∘ₗ (twKer ρ D.N 1).mkQ, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : (twKer ρ D.N 1).mkQ x = 0 := (hmk x).1 hx
    simp [h1]
  · intro h
    apply hlam0
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact LinearMap.congr_fun h v
  · intro s hs v
    exact hlam ⟨s, (hT s).2 hs⟩ (Submodule.Quotient.mk v)

theorem eqFormU : EqFormU :=
  eqFormU_of (fun G _ _ _ => GlobalTheory.T.jacquet_lemma_holds G) GlobalTheory.T.iwahori_unipotent_datum GlobalTheory.CompanionTheory.DomUnitary.domU GlobalTheory.CompanionTheory.KUFactsU.kuFacts

end GlobalTheory.CompanionTheory.EqForm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEquivariantFormStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_equivariant_form : PositivityTheory.SphericalProduct.EqFormU := by
  first | exact @GlobalTheory.CompanionTheory.EqForm.eqFormU | exact GlobalTheory.CompanionTheory.EqForm.eqFormU | (intros; apply GlobalTheory.CompanionTheory.EqForm.eqFormU <;> assumption)
end
end
