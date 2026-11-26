module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.RevTop
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SpanLevel
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ThetaPhi
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UnfOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.FacOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.WhittakerLieDerivativeLinear
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ShiftM
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ContInfGL2
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ContOn
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.DvMulIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.CardHeckeT1Cosets
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.PairCases
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.OneAddXNe
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ExistsBad
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.UnitCharacterOfCentral
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.WeilEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.MeasEx
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.InnerInt
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

private theorem cont_em : Continuous (em E) := by
  have hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap
  exact Continuous.units_map _ hM

private theorem sc_idele : SecondCountableTopology (IdeleGroup ℚ) := by
  haveI : SecondCountableTopology (A ℚ) := GroundTheory.Automorphic.secondCountableTopology_adeleRing ℚ
  haveI : SecondCountableTopology (A ℚ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem cont_in {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) (t : (A ℚ)ˣ) :
    Continuous fun g : G1 ℚ => φ (em E (gl g * dM t)) :=
  hc.comp (cont_em.comp (Matrix.SpecialLinearGroup.continuous_toGL.mul continuous_const))

private theorem inner_int (M : Meas ℚ) {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) {B : ℝ}
    (hB : ∀ g, ‖φ g‖ ≤ B) (t : (A ℚ)ˣ) :
    IntegrableOn (fun g : G1 ℚ => φ (em E (gl g * dM t))) M.D M.μ := by
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  exact Integrable.of_bound (cont_in hc t).aestronglyMeasurable B (ae_of_all _ fun g => hB _)

private theorem outer_int (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) {B : ℝ} (hB : ∀ g, ‖φ g‖ ≤ B) :
    Integrable (fun t => ((χ.1 t : ℂˣ) : ℂ) * ∫ g in M.D, φ (em E (gl g * dM t)) ∂M.μ) U.υ := by
  haveI := U.prob
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  haveI := sc_idele
  have hF : Continuous fun t : IdeleGroup ℚ => ∫ g in M.D, φ (em E (gl g * dM t)) ∂M.μ := by
    refine continuous_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
    · exact fun t => (cont_in hc t).aestronglyMeasurable
    · exact fun t => ae_of_all _ fun g => hB _
    · exact ae_of_all _ fun g =>
        hc.comp (cont_em.comp (continuous_const.mul UpperTheory.ConvolutionTheory.R2.continuous_dM))
  have hχc : Continuous fun t : IdeleGroup ℚ => ((χ.1 t : ℂˣ) : ℂ) :=
    Units.continuous_val.comp χ.2.1
  refine Integrable.of_bound (hχc.mul hF).aestronglyMeasurable (B * (M.μ.restrict M.D).real Set.univ)
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, hχ, one_mul]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun g => hB _)

private theorem per_add (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1)
    {φ₁ φ₂ : GL (Fin 2) (A E) → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) {B₁ B₂ : ℝ}
    (b₁ : ∀ g, ‖φ₁ g‖ ≤ B₁) (b₂ : ∀ g, ‖φ₂ g‖ ≤ B₂) :
    Per M U χ (φ₁ + φ₂) = Per M U χ φ₁ + Per M U χ φ₂ := by
  unfold Per
  rw [← integral_add (outer_int M U χ hχ h₁ b₁) (outer_int M U χ hχ h₂ b₂)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [Pi.add_apply]
  rw [integral_add (inner_int M h₁ b₁ t) (inner_int M h₂ b₂ t), mul_add]

private theorem per_smul (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) (c : ℂ) (φ : GL (Fin 2) (A E) → ℂ) :
    Per M U χ (c • φ) = c * Per M U χ φ := by
  unfold Per
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  ring

private theorem per_zero (M : Meas ℚ) (U : UMeas) (χ : HChar ℚ) :
    Per M U χ (0 : GL (Fin 2) (A E) → ℂ) = 0 := by
  simp [Per]

end UpperTheory.ConvolutionTheory.RankTwoDescent

open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.perTr_of :
    PerTr := by
  intro E _ _ _ D P ω χ _ hω hχω hAdm M U hNo φ hφ
  have hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
    intro a
    have h := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (hχω a)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, hω a, mul_one,
      Units.val_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, h, rfl⟩ := hx
    exact hNo f hf h
  | zero => exact per_zero M U χ
  | add x y hx hy ihx ihy =>
    obtain ⟨B₁, b₁⟩ := (hAdm x hx).bdd
    obtain ⟨B₂, b₂⟩ := (hAdm y hy).bdd
    rw [per_add M U χ hχ (hAdm x hx).cont (hAdm y hy).cont b₁ b₂, ihx, ihy, add_zero]
  | smul c x hx ih =>
    rw [per_smul, ih, mul_zero]

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.ExtOf
open UpperTheory.ConvolutionTheory.RankTwoDescent
open Filter Topology

private theorem glue_aux (A : ℂ → ℂ)
    (h : ∀ s₀ : ℂ, ∃ (r : ℝ) (H m : ℂ → ℂ), r < s₀.re ∧
      DifferentiableOn ℂ H {s | r < s.re} ∧ DifferentiableOn ℂ m {s | r < s.re} ∧ m s₀ ≠ 0 ∧
      ∀ s : ℂ, 4 < s.re → H s = A s * m s) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 4 < s.re → F s = A s := by
  choose r H m hr hH hm hne hA using h
  have hopen : ∀ ρ : ℝ, IsOpen {z : ℂ | ρ < z.re} := fun ρ =>
    isOpen_lt continuous_const Complex.continuous_re
  have key : ∀ a b s : ℂ, r a < s.re → r b < s.re → H a s * m b s = H b s * m a s := by
    intro a b s ha hb
    have hUc : IsPreconnected {z : ℂ | max (r a) (r b) < z.re} :=
      (convex_halfSpace_re_gt (max (r a) (r b))).isPreconnected
    have hsa : {z : ℂ | max (r a) (r b) < z.re} ⊆ {z | r a < z.re} :=
      fun z hz => show r a < z.re from lt_of_le_of_lt (le_max_left _ _) hz
    have hsb : {z : ℂ | max (r a) (r b) < z.re} ⊆ {z | r b < z.re} :=
      fun z hz => show r b < z.re from lt_of_le_of_lt (le_max_right _ _) hz
    have d1 : DifferentiableOn ℂ (fun z => H a z * m b z) {z : ℂ | max (r a) (r b) < z.re} :=
      ((hH a).mono hsa).mul ((hm b).mono hsb)
    have d2 : DifferentiableOn ℂ (fun z => H b z * m a z) {z : ℂ | max (r a) (r b) < z.re} :=
      ((hH b).mono hsb).mul ((hm a).mono hsa)
    have hz₀ : ((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ) ∈ {z : ℂ | max (r a) (r b) < z.re} := by
      show max (r a) (r b) < (((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]
      linarith [le_max_left (max (r a) (r b)) 4]
    have h4 : ((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ) ∈ {z : ℂ | (4 : ℝ) < z.re} := by
      show (4 : ℝ) < (((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ)).re
      rw [Complex.ofReal_re]
      linarith [le_max_right (max (r a) (r b)) 4]
    have hev : (fun z => H a z * m b z) =ᶠ[𝓝 ((max (max (r a) (r b)) 4 + 1 : ℝ) : ℂ)]
        fun z => H b z * m a z := by
      filter_upwards [(hopen 4).mem_nhds h4] with z hz
      rw [hA a z hz, hA b z hz]
      ring
    exact (d1.analyticOnNhd (hopen _)).eqOn_of_preconnected_of_eventuallyEq
      (d2.analyticOnNhd (hopen _)) hUc hz₀ hev (show max (r a) (r b) < s.re from max_lt ha hb)
  refine ⟨fun s => H s s / m s s, ?_, ?_⟩
  · intro s₀
    have hU : {z : ℂ | r s₀ < z.re} ∈ 𝓝 s₀ := (hopen _).mem_nhds (hr s₀)
    have hdH : DifferentiableAt ℂ (H s₀) s₀ := (hH s₀).differentiableAt hU
    have hdm : DifferentiableAt ℂ (m s₀) s₀ := (hm s₀).differentiableAt hU
    have hne' : ∀ᶠ z in 𝓝 s₀, m s₀ z ≠ 0 := hdm.continuousAt.eventually_ne (hne s₀)
    have heq : (fun s => H s s / m s s) =ᶠ[𝓝 s₀] fun z => H s₀ z / m s₀ z := by
      filter_upwards [hU, hne'] with z hz hz'
      rw [div_eq_div_iff (hne z) hz']
      exact (key s₀ z z hz (hr z)).symm
    exact heq.differentiableAt_iff.mpr (hdH.div hdm (hne s₀))
  · intro s hs
    show H s s / m s s = A s
    rw [hA s s hs, mul_div_assoc, div_self (hne s), mul_one]

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.ext_of :
    TrAdm → PerTr → Ent → Unf → PhiMem → Fac → ShiftM → Hol → NonZ → Ext := by
  intro hTr hPer hEnt hUnf hPhi hFac hSh hHol hNZ
  intro E _ _ _ D P ω χ hC hU hχ M U hNo L N φ hCh hG hW a ha hsum
  have hA := hTr E D P ω χ hC hU hχ
  have hPz := hPer E D P ω χ hC hU hχ hA M U hNo
  obtain ⟨c₁, hc₁, hZ⟩ := hUnf E D P ω χ hC hU hχ M U
  obtain ⟨c₂, hc₂, hF⟩ := hFac E D P ω χ hC hU hχ M L N hCh
  have hN := hG.pos
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine glue_aux (LSeries a) ?_
  intro s₀
  obtain ⟨k, hk⟩ := exists_nat_gt (1 - s₀.re)
  have hk' : 1 - (k : ℝ) < s₀.re := by linarith
  obtain ⟨φ', e, p, hG', hp, hne⟩ := hNZ E D P ω χ hC hU hχ hA L N φ hG hW k s₀ hk'
  obtain ⟨n, f, q, hfq, hsumM⟩ := hSh E D P ω χ hC hU hχ L N k φ' e p hG' hp
  have hAf : ∀ i, admitted D ω (f i) := fun i => hA _ (hfq i).1.mem
  have hdZ : Differentiable ℂ fun s => ∑ i, Zs M U χ (f i) (PhiN N (q i)) s :=
    Differentiable.fun_sum fun i _ =>
      hEnt E D P ω χ hC hU hχ M U (f i) (hAf i) (hPz _ (hfq i).1.mem) _ (hPhi N (q i) hN)
  have hdP : Differentiable ℂ fun s : ℂ => (Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) :=
    (differentiable_id.add_const _).const_cpow (Or.inl hπ0)
  have hdG : Differentiable ℂ fun s : ℂ => (Complex.Gamma (s + ((e + k : ℕ) : ℂ)))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _)
  have hdH : Differentiable ℂ fun s : ℂ => (c₁ * c₂)⁻¹ *
      ((Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) * ((Complex.Gamma (s + ((e + k : ℕ) : ℂ)))⁻¹)) *
        ∑ i, Zs M U χ (f i) (PhiN N (q i)) s :=
    ((differentiable_const _).mul (hdP.mul hdG)).mul hdZ
  refine ⟨1 - k, _, Mk D χ k φ' p, hk', hdH.differentiableOn,
    hHol E D P ω χ hC hU hχ k φ' p (hA _ hG'.mem), hne, ?_⟩
  intro s hs
  have h1 : ∀ i, Zs M U χ (f i) (PhiN N (q i)) s =
      c₁ * (c₂ * ((Real.pi : ℂ) ^ (-(s + ((e + k : ℕ) : ℂ))) * Complex.Gamma (s + ((e + k : ℕ) : ℂ))) *
        LSeries a s * Mk D χ 0 (f i) (q i) s) := fun i => by
    rw [hZ (f i) (hAf i) _ (hPhi N (q i) hN) s hs,
      hF (f i) (hAf i) (hfq i).1 a ha (e + k) (q i) (hfq i).2 s hs (hsum s hs)]
  have hsM := hsumM s hs
  simp only [h1]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← hsM]
  have hre : 0 < (s + ((e + k : ℕ) : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ ((e + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hΓ := Complex.Gamma_ne_zero_of_re_pos hre
  have hXY : (Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) * (Real.pi : ℂ) ^ (-(s + ((e + k : ℕ) : ℂ))) = 1 := by
    rw [← Complex.cpow_add _ _ hπ0, add_neg_cancel, Complex.cpow_zero]
  have hc : c₁ * c₂ ≠ 0 := mul_ne_zero hc₁ hc₂
  generalize (Real.pi : ℂ) ^ (s + ((e + k : ℕ) : ℂ)) = X at hXY ⊢
  generalize (Real.pi : ℂ) ^ (-(s + ((e + k : ℕ) : ℂ))) = Y at hXY ⊢
  generalize Complex.Gamma (s + ((e + k : ℕ) : ℂ)) = G at hΓ ⊢
  calc (c₁ * c₂)⁻¹ * (X * G⁻¹) * (c₁ * (c₂ * (Y * G) * LSeries a s * Mk D χ k φ' p s))
      = (X * Y) * ((c₁ * c₂)⁻¹ * (c₁ * c₂)) * (G⁻¹ * G) * (LSeries a s * Mk D χ k φ' p s) := by
        ring
    _ = LSeries a s * Mk D χ k φ' p s := by
        rw [hXY, inv_mul_cancel₀ hc, inv_mul_cancel₀ hΓ]
        ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitOfNormalised
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.NormCentral
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharSel
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

section Abs
open GroundTheory.Automorphic.CompactAbelianFourier
open scoped Pointwise

variable {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

private lemma intF (μ : Measure G) [μ.IsHaarMeasure] {F : Set G} (hc : IsCompact (closure F)) {f : G → ℂ}
    (hf : Continuous f) : IntegrableOn f F μ :=
  (hf.continuousOn.integrableOn_compact hc).mono_set subset_closure

private theorem char_integral_ne (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) [Countable N] [DiscreteTopology N]
    (F : Set G) (hF : IsFundamentalDomain N.op F μ) (hc : IsCompact (closure F))
    (hs : ∀ u : G, ∃ k ∈ N, u * k ∈ F)
    (b : G → ℂ) (hb : Continuous b) (hi : ∀ k ∈ N, ∀ x, b (x * k) = b x) (x₀ : G) (h0 : b x₀ ≠ 0) :
    ∃ χ : G →ₜ* Circle, (∀ k ∈ N, χ k = 1) ∧ ∫ x in F, (χ x : ℂ) * b x ∂μ ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  haveI hcl : IsClosed (N : Set G) := Subgroup.isClosed_of_discrete
  haveI : CompactSpace (G ⧸ N) := ⟨by
    have : (Set.univ : Set (G ⧸ N)) = QuotientGroup.mk '' closure F := by
      symm
      refine Set.eq_univ_of_forall fun q => ?_
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk, hu⟩ := hs u
      exact ⟨u * k, subset_closure hu, QuotientGroup.mk_mul_of_mem u hk⟩
    rw [this]
    exact hc.image QuotientGroup.continuous_mk⟩
  let π : G →ₜ* G ⧸ N := ⟨QuotientGroup.mk' N, continuous_quotient_mk'⟩
  have hπc : Continuous fun x => π x := π.continuous
  obtain ⟨M₀, hM₀⟩ := hc.exists_bound_of_continuousOn hb.continuousOn
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ closure F, ‖b x‖ ≤ M := ⟨M₀, hM₀⟩
  have hfin : μ F < ⊤ := (measure_mono subset_closure).trans_lt hc.measure_lt_top
  have hint : ∀ f : C(G ⧸ N, ℂ), IntegrableOn (fun x => f (π x) * b x) F μ := fun f =>
    intF μ hc ((f.continuous.comp hπc).mul hb)
  let L0 : C(G ⧸ N, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x in F, f (π x) * b x ∂μ
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul _ _ }
  have hbd : ∀ f, ‖L0 f‖ ≤ (M * μ.real F) * ‖f‖ := by
    intro f
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := F) (f := fun x => f (π x) * b x) (C := ‖f‖ * M) hfin
      (fun x hx => by
        rw [norm_mul]
        exact mul_le_mul (f.norm_coe_le_norm _) (hM x (subset_closure hx)) (norm_nonneg _) (norm_nonneg _))
    calc ‖L0 f‖ ≤ ‖f‖ * M * μ.real F := this
      _ = _ := by ring
  let L : C(G ⧸ N, ℂ) →L[ℂ] ℂ := L0.mkContinuous _ hbd
  have hL : ∀ f, L f = ∫ x in F, f (π x) * b x ∂μ := fun f => rfl
  have hspan : (Submodule.span ℂ (Set.range (charCM (C := G ⧸ N)))).topologicalClosure ≤ LinearMap.ker (L : C(G ⧸ N, ℂ) →ₗ[ℂ] ℂ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker L)
    rw [Submodule.span_le]
    rintro _ ⟨ψ, rfl⟩
    have := hcon (ψ.comp π) (fun k hk => by
      change ψ (QuotientGroup.mk k) = 1
      rw [(QuotientGroup.eq_one_iff k).2 hk, map_one])
    exact this
  have hall : ∀ f, L f = 0 := fun f => hspan (by rw [span_charCM_dense]; trivial)
  let bq : C(G ⧸ N, ℂ) := ⟨fun q => Quotient.liftOn' q b (fun x y h => by
      have h' : x⁻¹ * y ∈ N := QuotientGroup.leftRel_apply.1 h
      have := hi _ h' x
      rw [mul_inv_cancel_left] at this
      exact this.symm), hb.quotient_liftOn' _⟩
  have hbq : ∀ x, bq (π x) = b x := fun x => rfl
  have h1 := hall (star bq)
  rw [hL] at h1
  have h2 : ∫ x in F, ((‖b x‖ ^ 2 : ℝ) : ℂ) ∂μ = 0 := by
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ContinuousMap.star_apply, hbq]
    rw [RCLike.star_def, Complex.conj_mul']
    simp
  have h3 : ∫ x in F, ‖b x‖ ^ 2 ∂μ = 0 := by
    have h := integral_ofReal (μ := μ.restrict F) (𝕜 := ℂ) (f := fun x => ‖b x‖ ^ 2)
    have h' : ((∫ x in F, ‖b x‖ ^ 2 ∂μ : ℝ) : ℂ) = 0 := by
      rw [← h2]
      exact h.symm
    exact_mod_cast h'
  have hc2 : Continuous fun x => ‖b x‖ ^ 2 := by fun_prop
  have h4 := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => by positivity) (by
    exact (hc2.continuousOn.integrableOn_compact hc).mono_set subset_closure)).1 h3
  have hT : IsOpen {x | b x ≠ 0} := isOpen_ne_fun hb continuous_const
  have hTF : μ ({x | b x ≠ 0} ∩ F) = 0 := by
    rw [← Measure.restrict_apply hT.measurableSet]
    refine measure_mono_null ?_ (ae_iff.1 h4)
    intro x hx
    simp only [Set.mem_setOf_eq, Pi.zero_apply] at hx ⊢
    simpa using hx
  have hinv : ∀ g : N.op, g • {x | b x ≠ 0} = {x | b x ≠ 0} := by
    rintro ⟨g, hg⟩
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have hg' : g.unop ∈ N := Subgroup.mem_op.1 hg
    have : ((⟨g, hg⟩ : N.op)⁻¹ • x) = x * g.unop⁻¹ := rfl
    simp only [Set.mem_setOf_eq, this]
    rw [hi _ (N.inv_mem hg')]
  have hz := hF.measure_zero_of_invariant _ hinv hTF
  exact (hT.measure_pos μ ⟨x₀, h0⟩).ne' hz

private lemma transl (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) [Countable N]
    (F : Set G) (hF : IsFundamentalDomain N.op F μ) (f : G → ℂ) (hi : ∀ k ∈ N, ∀ x, f (x * k) = f x) (d : G) :
    ∫ t in F, f (t * d) ∂μ = ∫ t in F, f t ∂μ := by
  have hD' := hF.smul_of_comm d
  have hI : ∀ (γ : N.op) (x : G), f (γ • x) = f x := by
    rintro ⟨γ, hγ⟩ x
    exact hi _ (Subgroup.mem_op.1 hγ) x
  have h1 := hF.setIntegral_eq hD' hI
  have h2 := (measurePreserving_mul_left μ d).setIntegral_image_emb
    (MeasurableEquiv.mulLeft d).measurableEmbedding f F
  rw [h1]
  simp_rw [mul_comm _ d]
  exact h2.symm

end Abs

section AbsB
variable {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

private theorem char_sel (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) [Countable N] [DiscreteTopology N]
    (F : Set G) (hF : IsFundamentalDomain N.op F μ) (hc : IsCompact (closure F))
    (hs : ∀ u : G, ∃ k ∈ N, u * k ∈ F)
    (c : G →* G) (hcc : Continuous c) (hcN : ∀ k ∈ N, c k ∈ N)
    (β : G → ℂ) (hβ : Continuous β) (hβi : ∀ k ∈ N, ∀ x, β (x * k) = β x)
    (h : ∫ z in F, β (c z) ∂μ ≠ 0) :
    ∃ χ : G →ₜ* Circle, (∀ k ∈ N, χ k = 1) ∧ (∀ z, χ (c z) = 1) ∧ ∫ t in F, (χ t : ℂ) * β t ∂μ ≠ 0 := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x, ‖β x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hβ.continuousOn
    refine ⟨B, fun x => ?_⟩
    obtain ⟨k, hk, hx⟩ := hs x
    have := hB _ (subset_closure hx)
    rwa [hβi k hk] at this
  have hfin : μ F < ⊤ := (measure_mono subset_closure).trans_lt hc.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict F) := ⟨by simpa using hfin⟩
  let b : G → ℂ := fun t => ∫ z in F, β (t * c z) ∂μ
  have hbc : Continuous b := by
    refine continuous_of_dominated (bound := fun _ => B) (fun t => ?_)
      (fun t => ae_of_all _ fun z => hB _) (integrable_const _) (ae_of_all _ fun z => ?_)
    · exact (hβ.comp (continuous_const.mul hcc)).aestronglyMeasurable
    · exact hβ.comp (continuous_id.mul continuous_const)
  have hbN : ∀ k ∈ N, ∀ x, b (x * k) = b x := by
    intro k hk x
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    change β (x * k * c z) = β (x * c z)
    rw [mul_right_comm, hβi k hk]
  have hbw : ∀ w t, b (t * c w) = b t := by
    intro w t
    have h1 := transl μ N F hF (fun z => β (t * c z)) (fun k hk x => by
      simp only [map_mul]
      rw [← mul_assoc, hβi _ (hcN k hk)]) w
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun z => ?_)) h1
    change β (t * c w * c z) = β (t * c (z * w))
    rw [map_mul, mul_assoc, mul_comm (c w)]
  have hb1 : b 1 ≠ 0 := by simpa [b] using h
  obtain ⟨χ, hχN, hχ⟩ := char_integral_ne μ N F hF hc hs b hbc hbN 1 hb1
  have hχc : Continuous fun x => (χ x : ℂ) := continuous_subtype_val.comp χ.continuous
  have hχw : ∀ z, χ (c z) = 1 := by
    intro w
    have h1 := transl μ N F hF (fun t => (χ t : ℂ) * b t) (fun k hk x => by
      simp only [map_mul, hχN k hk, mul_one]
      rw [hbN k hk]) (c w)
    have h2 : ∫ t in F, (χ (t * c w) : ℂ) * b (t * c w) ∂μ = (χ (c w) : ℂ) * ∫ t in F, (χ t : ℂ) * b t ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [hbw, map_mul, Circle.coe_mul]
      ring
    rw [h2] at h1
    have h3 : (χ (c w) : ℂ) = 1 := mul_right_cancel₀ hχ (h1.trans (one_mul _).symm)
    exact Circle.coe_injective (by simpa using h3)
  refine ⟨χ, hχN, hχw, ?_⟩
  have hint : Integrable (Function.uncurry fun t z => (χ t : ℂ) * β (t * c z))
      ((μ.restrict F).prod (μ.restrict F)) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) B (ae_of_all _ fun p => ?_)
    · exact (hχc.comp continuous_fst).mul (hβ.comp (continuous_fst.mul (hcc.comp continuous_snd)))
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, one_mul]
      exact hB _
  have e1 : ∫ t in F, (χ t : ℂ) * b t ∂μ = ∫ t in F, ∫ z in F, (χ t : ℂ) * β (t * c z) ∂μ ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    exact (integral_const_mul _ _).symm
  have e3 : ∀ z, ∫ t in F, (χ t : ℂ) * β (t * c z) ∂μ = ∫ t in F, (χ t : ℂ) * β t ∂μ := by
    intro z
    have h1 := transl μ N F hF (fun t => (χ t : ℂ) * β t) (fun k hk x => by
      simp only [map_mul, hχN k hk, mul_one]
      rw [hβi k hk]) (c z)
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun t => ?_)) h1
    simp only [map_mul, hχw, mul_one]
  intro hJ
  apply hχ
  rw [e1, integral_integral_swap hint]
  simp_rw [e3, hJ]
  simp

end AbsB

section Conc
open GroundTheory.Automorphic.Reduction GroundTheory.Automorphic GroundTheory.Global.AdeleBaseChange

variable (E : Type) [Field E] [NumberField E]

private noncomputable def rho : {r : ℝ // 0 < r} →* IdeleGroup E :=
  (posIdeleHom E).comp (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹)

private lemma continuous_rho : Continuous (rho E) :=
  continuous_posIdeleHom.comp (continuous_rpowHom _)

private lemma module_rho (r : {r : ℝ // 0 < r}) : IdeleGroup.ideleModule E (rho E r) = r := by
  refine Subtype.ext ?_
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h := ideleModule_posIdele (K := E) (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ r).1
    (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ r).2
  refine h.trans ?_
  change (r.1 ^ ((Module.finrank ℚ E : ℝ))⁻¹) ^ Module.finrank ℚ E = r.1
  rw [← Real.rpow_natCast, ← Real.rpow_mul r.2.le, inv_mul_cancel₀ hd, Real.rpow_one]

private lemma rho_rpow (s : {r : ℝ // 0 < r}) : rho E s = posIdeleHom E (rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ s) := rfl

private noncomputable def proj : IdeleGroup E →* IdeleGroup.normOneSubgroup E where
  toFun x := ⟨x * (rho E (IdeleGroup.ideleModule E x))⁻¹, by
    refine MonoidHom.mem_ker.2 ?_
    rw [map_mul, map_inv, module_rho, mul_inv_cancel]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    simp only [map_mul, Subgroup.coe_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)

private lemma continuous_proj : Continuous (proj E) :=
  (continuous_id.mul ((continuous_rho E).comp IdeleGroup.continuous_ideleModule).inv).subtype_mk _

private lemma proj_coe (z : IdeleGroup.normOneSubgroup E) : proj E (z : IdeleGroup E) = z := by
  refine Subtype.ext ?_
  have hz : IdeleGroup.ideleModule E (z : IdeleGroup E) = 1 := z.2
  change (z : IdeleGroup E) * (rho E (IdeleGroup.ideleModule E z))⁻¹ = z
  rw [hz, map_one, inv_one, mul_one]

private theorem ext_char (χ₁ : IdeleGroup.normOneSubgroup E →ₜ* Circle)
    (h : ∀ k : Eˣ, χ₁ (diagonalToNormOne E k) = 1) :
    ∃ χ : HChar E, (∀ z : IdeleGroup.normOneSubgroup E, ((χ.1 (z : IdeleGroup E) : ℂˣ) : ℂ) = (χ₁ z : ℂ)) ∧
      (∀ x, ((χ.1 x : ℂˣ) : ℂ) = (χ₁ (proj E x) : ℂ)) := by
  let f : IdeleGroup E →* ℂˣ := Circle.toUnits.comp ((χ₁ : _ →* Circle).comp (proj E))
  have hfv : ∀ x, ((f x : ℂˣ) : ℂ) = (χ₁ (proj E x) : ℂ) := fun x => rfl
  have hc : Continuous f := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_subtype_val.comp (χ₁.continuous.comp (continuous_proj E))
    · have h1 : Continuous fun x => (((χ₁ (proj E x))⁻¹ : Circle) : ℂ) :=
        continuous_subtype_val.comp (χ₁.continuous.comp (continuous_proj E)).inv
      exact h1
  have hd : ∀ k : Eˣ, f (IdeleGroup.diagonal E k) = 1 := by
    intro k
    have e : proj E (IdeleGroup.diagonal E k) = diagonalToNormOne E k := proj_coe E (diagonalToNormOne E k)
    refine Units.ext ?_
    rw [hfv, e, h]
    simp
  refine ⟨⟨f, hc, hd⟩, fun z => ?_, hfv⟩
  change ((f (z : IdeleGroup E) : ℂˣ) : ℂ) = _
  rw [hfv, proj_coe]

private lemma rpow_pow (t : {r : ℝ // 0 < r}) :
    rpowHom ((Module.finrank ℚ E : ℝ))⁻¹ (t ^ Module.finrank ℚ E) = t := by
  refine Subtype.ext ?_
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  change ((t ^ Module.finrank ℚ E : {r : ℝ // 0 < r}) : ℝ) ^ ((Module.finrank ℚ E : ℝ))⁻¹ = t.1
  rw [Positive.val_pow, ← Real.rpow_natCast, ← Real.rpow_mul t.2.le, mul_inv_cancel₀ hd, Real.rpow_one]

private lemma pos_rho (t : {r : ℝ // 0 < r}) : posIdeleHom E t = rho E (t ^ Module.finrank ℚ E) := by
  rw [rho_rpow, rpow_pow]

private lemma proj_rho (r : {r : ℝ // 0 < r}) : proj E (rho E r) = 1 := by
  refine Subtype.ext ?_
  change rho E r * (rho E (IdeleGroup.ideleModule E (rho E r)))⁻¹ = 1
  rw [module_rho, mul_inv_cancel]

private lemma gal_fix_pos (σ : E ≃ₐ[ℚ] E) (t : {r : ℝ // 0 < r}) : σ • posIdeleHom E t = posIdeleHom E t := by
  have h := UpperTheory.centralSection_baseChange ℚ E 1 t
  have e : rpowHom (((1 : ℕ) * Module.finrank ℚ E : ℝ))⁻¹ (t ^ Module.finrank ℚ E) = t := by
    rw [Nat.cast_one, one_mul]
    exact rpow_pow E t
  have h2 : centralSection E 1 (t ^ Module.finrank ℚ E) = diagUnits 1 fun _ => posIdeleHom E t := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, e, scalarUnits_apply]
  rw [h2] at h
  have h3 := congrArg (fun g : AdelicGLn.AdelicGL E 1 => g.val 0 0) h
  beta_reduce at h3
  rw [coe_diagUnits, Matrix.diagonal_apply_eq] at h3
  have h4 : adeleMap ℚ E ((centralSection ℚ 1 t).val 0 0) = ((posIdeleHom E t : IdeleGroup E) : A E) := h3
  refine Units.ext ?_
  rw [coe_smul_idele, ← h4, smul_adeleMap]

end Conc

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.charSel :
    CharSel := by
  intro E _ _ D β hc hinv h
  have hbar : ∀ z : (A E)ˣ, Units.map (D.bar : A E →* A E) z = D.σ • (z : IdeleGroup E) := fun z => Units.ext rfl
  let c : IdeleGroup.normOneSubgroup E →* IdeleGroup.normOneSubgroup E :=
    { toFun := fun z => ⟨(z : IdeleGroup E) * (D.σ • (z : IdeleGroup E))⁻¹, by
        refine MonoidHom.mem_ker.2 ?_
        rw [map_mul, map_inv, ← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ) (D.σ • (z : IdeleGroup E)),
          ideleNorm_smul, GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm, mul_inv_cancel]⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        simp only [Subgroup.coe_mul, smul_mul', mul_inv]
        exact mul_mul_mul_comm _ _ _ _) }
  have hcv : ∀ z, ((c z : IdeleGroup.normOneSubgroup E) : IdeleGroup E) =
      (z : IdeleGroup E) * (D.σ • (z : IdeleGroup E))⁻¹ := fun z => rfl
  have hcc : Continuous c :=
    (continuous_subtype_val.mul ((continuous_const_smul D.σ).comp continuous_subtype_val).inv).subtype_mk _
  have hcN : ∀ k ∈ diagonalNormOne E, c k ∈ diagonalNormOne E := by
    intro k hk
    obtain ⟨e, he⟩ := Subgroup.mem_subgroupOf.1 hk
    refine Subgroup.mem_subgroupOf.2 ⟨e * (D.σ • e)⁻¹, ?_⟩
    rw [hcv, ← he, map_mul, map_inv, smul_diagonal]
  have hs : ∀ u : IdeleGroup.normOneSubgroup E, ∃ k ∈ diagonalNormOne E, u * k ∈ normOneFundamentalDomain E := by
    intro u
    obtain ⟨e, he, -⟩ := existsUnique_mul_mem_normOneFundamentalDomain E u
    exact ⟨_, ⟨e, rfl⟩, he⟩
  have hβc : Continuous fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E) := hc.comp continuous_subtype_val
  have hβi : ∀ k ∈ diagonalNormOne E, ∀ x : IdeleGroup.normOneSubgroup E,
      β ((x * k : IdeleGroup.normOneSubgroup E) : IdeleGroup E) = β (x : IdeleGroup E) := by
    intro k hk x
    obtain ⟨e, he⟩ := Subgroup.mem_subgroupOf.1 hk
    rw [Subgroup.coe_mul, ← he, mul_comm]
    exact hinv e _
  obtain ⟨χ₁, h1N, h1c, h1⟩ := char_sel (normOneMeasure E) (diagonalNormOne E) (normOneFundamentalDomain E)
    (isFundamentalDomain_normOneFundamentalDomain E _) (isCompact_closure_normOneFundamentalDomain E) hs
    c hcc hcN _ hβc hβi (by
      intro h0
      apply h
      rw [← h0]
      unfold UI
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hbar, hcv])
  obtain ⟨χ, hχ1, hχp⟩ := ext_char E χ₁ (fun k => h1N _ ⟨k, rfl⟩)
  refine ⟨χ, fun z => ?_, fun z hz => ?_, ?_⟩
  · have hfix : D.σ • rho E (IdeleGroup.ideleModule E z) = rho E (IdeleGroup.ideleModule E z) := gal_fix_pos E D.σ _
    have e : z * (Units.map (D.bar : A E →* A E) z)⁻¹ = ((c (proj E z) : IdeleGroup.normOneSubgroup E) : IdeleGroup E) := by
      rw [hbar, hcv]
      change _ = z * (rho E (IdeleGroup.ideleModule E z))⁻¹ * (D.σ • (z * (rho E (IdeleGroup.ideleModule E z))⁻¹))⁻¹
      rw [smul_mul', smul_inv', hfix]
      have key : ∀ a b r : IdeleGroup E, a * b⁻¹ = a * r⁻¹ * (b * r⁻¹)⁻¹ := fun a b r => by
        rw [mul_inv, inv_inv, mul_assoc, ← mul_assoc r⁻¹, mul_comm r⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      exact key _ _ _
    refine Units.ext ?_
    rw [e, hχ1, h1c]
    simp
  · obtain ⟨s, hs'⟩ := hz
    have h2 : GroundTheory.Automorphic.Reduction.centralSection E 2 s = GroundTheory.Automorphic.Reduction.diagUnits 2 fun _ =>
        GroundTheory.Automorphic.Reduction.posIdeleHom E (GroundTheory.Automorphic.Reduction.rpowHom ((2 * Module.finrank ℚ E : ℝ))⁻¹ s) := by
      rw [GroundTheory.Automorphic.Reduction.centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, GroundTheory.Automorphic.Reduction.scalarUnits_apply]
      simp
    rw [h2] at hs'
    have h3 := congrArg (fun g : GL (Fin 2) (A E) => g.val 0 0) hs'
    beta_reduce at h3
    rw [GroundTheory.Automorphic.Reduction.coe_diagUnits, Matrix.diagonal_apply_eq] at h3
    have h4 : z = GroundTheory.Automorphic.Reduction.posIdeleHom E (GroundTheory.Automorphic.Reduction.rpowHom ((2 * Module.finrank ℚ E : ℝ))⁻¹ s) := by
      refine Units.ext ?_
      rw [← h3]
      simp
    refine Units.ext ?_
    rw [hχp, h4, pos_rho, proj_rho]
    simp
  · intro h0
    apply h1
    rw [← h0]
    unfold UI
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [hχ1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharDown
open NumberField IsDedekindDomain
open Formalism.L2.Host GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem charDown : CharDown := by
  intro E _ _ _ D χ h
  have hE : Module.finrank ℚ E = 2 := by
    rw [Module.finrank_eq_card_basis D.b]
    simp
  have hθ : D.θ ≠ 0 := by
    rw [← D.b1]
    exact D.b.ne_zero 1
  have hσ : D.σ ≠ 1 := by
    intro h1
    have h2 := D.conj
    rw [h1] at h2
    have h3 : D.θ = -D.θ := by simpa using h2
    have h4 : (2 : E) * D.θ = 0 := by linear_combination h3
    exact hθ (by simpa using h4)
  refine A.normChar_of_inv hE χ fun c z => ?_
  rcases GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two D.σ hE hσ c with rfl | rfl
  · rw [one_smul]
  · have h1 := h z
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    have h2 : Units.map (D.bar : A E →* A E) z = D.σ • z := Units.ext (coe_smul_idele D.σ z).symm
    rw [← h2]
    exact h1.symm

end UpperTheory.ConvolutionTheory.RankTwoDescent
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem aE_dM_eq (z w : (A E)ˣ) : aE z * dM w⁻¹ = gl (mD w) * aE (z * w⁻¹) := by
  refine Units.ext ?_
  have e : (gl (mD w)).val = !![(w : A E), 0; 0, ((w⁻¹ : (A E)ˣ) : A E)] := rfl
  rw [Units.val_mul, Units.val_mul, e, aE_val, aE_val, dM_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_left_comm]

private theorem scal_eq {K : Type} [Field K] [NumberField K] (u : (A K)ˣ) :
    GroundTheory.Automorphic.Reduction.scalarUnits K 2 u = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  ext i j
  rw [GroundTheory.Automorphic.Reduction.scalarUnits_apply, GroundTheory.Automorphic.Reduction.coe_diagUnits]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]

private theorem norm_central (s : {r : ℝ // 0 < r}) :
    ∃ z : (A E)ˣ, GroundTheory.Automorphic.Reduction.centralSection E 2 s = Matrix.GeneralLinearGroup.scalar (Fin 2) z ∧
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z) = GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s := by
  have hd : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : {r : ℝ // 0 < r}, s₀ ^ Module.finrank ℚ E = s := by
    refine ⟨⟨s.1 ^ ((Module.finrank ℚ E : ℝ))⁻¹, Real.rpow_pos_of_pos s.2 _⟩, Subtype.ext ?_⟩
    rw [Positive.val_pow]
    exact Real.rpow_inv_natCast_pow s.2.le hd
  obtain ⟨y, hy⟩ : ∃ y : (A ℚ)ˣ, GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s₀ = Matrix.GeneralLinearGroup.scalar (Fin 2) y :=
    ⟨_, (rfl : _ = GroundTheory.Automorphic.Reduction.scalarUnits ℚ 2 _).trans (scal_eq _)⟩
  refine ⟨ideleEmbedding ℚ E y, ?_, ?_⟩
  · rw [← hs₀, ← UpperTheory.centralSection_baseChange ℚ E 2 s₀, hy]
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]
  · rw [ideleNorm_ideleEmbedding, map_pow, ← hy, ← map_pow, hs₀]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.toII :
    ToII := by
  intro E _ _ _ D W M N P hP π hπ ⟨f, hf, ph, hph, φ, hφ, hne⟩
  obtain ⟨Φ, hΦ⟩ := UpperTheory.ConvolutionTheory.R2.smooth ℚ E D W M π f hf ph hph
  have hm : Φ ∈ span W M π := Submodule.subset_span ⟨f, hf, ph, hph, hΦ⟩
  have hBd : Bd fun x => Φ.1 x * φ.1 x := (UpperTheory.ConvolutionTheory.RankTwoDescent.prodBd E D W M N P π Φ hm φ hφ).1
  obtain ⟨-, hcont, hgl, hrat⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.meanLaws E N _ hBd
  let β : (A E)ˣ → ℂ := fun t => mean N fun x => Φ.1 (x * aE t) * φ.1 (x * aE t)
  have hβc : Continuous β := hcont.comp continuous_aE
  have hβi : ∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t := fun e t => by
    obtain ⟨γ, hγ⟩ := exists_ratGL_aE (F := E) e
    have h := hrat γ (aE t)
    simp only [β]
    rw [aE_mul, ← hγ]
    exact h
  have hJ : (J1 D N fun x => lift W M f.1 ph x * φ.1 x) =
      UI fun z => β (z * (Units.map (D.bar : A E →* A E) z)⁻¹) := by
    rw [← hΦ]
    refine congrArg UI (funext fun z => ?_)
    have h := hgl (mD (Units.map (D.bar : A E →* A E) z)) (aE (z * (Units.map (D.bar : A E →* A E) z)⁻¹))
    simp only [β, sZ]
    rw [aE_dM_eq]
    exact h
  obtain ⟨χ, h1, h2, h3⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.charSel E D β hβc hβi (by rw [← hJ]; exact hne)
  obtain ⟨χ₀, hχ₀⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.charDown E D χ h1
  have hdet : ∀ (g : G1 ℚ) (n : (A ℚ)ˣ), chiDet 2 χ₀ (gl g * dM n) = χ₀.1 n := fun g n => by
    have e : chiDet 2 χ₀ (gl g * dM n) = χ₀.1 (Matrix.GeneralLinearGroup.det (gl g * dM n)) := rfl
    rw [e, map_mul, det_gl, det_dM, one_mul]
  have hcs : ∀ s, chiDet 2 χ₀ (GroundTheory.Automorphic.Reduction.centralSection ℚ 2 s) = 1 := fun s => by
    obtain ⟨z, hz, hn⟩ := norm_central (E := E) s
    have hz1 : χ₀.1 (ideleNorm ℚ E z) = 1 := by rw [← hχ₀ z]; exact h2 z ⟨s, hz.symm⟩
    have e : chiDet 2 χ₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z)) =
        χ₀.1 (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleNorm ℚ E z))) := rfl
    rw [← hn, e, det_scalar, map_pow, hz1, one_pow]
  have hlift : ∀ x, lift W M (TR.mulChi 2 χ₀ f).1 ph x = ((χ₀.1 (nu ℚ x) : ℂˣ) : ℂ) * lift W M f.1 ph x := fun x => by
    simp only [lift]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [TR.mulChi_apply, hdet]
    ring
  refine ⟨π.twist χ₀, ?_, TR.mulChi 2 χ₀ f, ⟨f, hf, rfl⟩, ph, hph, φ, hφ, ?_⟩
  · rintro _ ⟨f₁, hf₁, rfl⟩ s g
    change f₁.1 _ * _ = f₁.1 g * _
    rw [hπ f₁ hf₁ s g, map_mul, hcs, one_mul]
  · have e : (II N fun x => lift W M (TR.mulChi 2 χ₀ f).1 ph x * φ.1 x) =
        UI fun t => ((χ.1 t : ℂˣ) : ℂ) * β t := by
      refine congrArg UI (funext fun t => ?_)
      simp only [mean, β]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      simp only [hlift, nu_mul, nu_gl, nu_aE, one_mul, hχ₀ t, hΦ]
      ring
    rw [e]
    exact h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.AsaiNV
namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem trAdm : TrAdm := trAdm_of decE

theorem asaiNV : AsaiNV :=
  asai_of trAdm exGd_of chEx_of (asEx_of satU_of)
    (ext_of trAdm perTr_of ent_of unf_of phiMem_of fac_of (shiftM_of trAdm (shift_of trAdm)) hol_of nonZ_of) (lan_of satU_of landau_of)

end UpperTheory.ConvolutionTheory.RankTwoDescent
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeasEEx
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.measEEx :
    MeasEEx := by
  intro E _ _
  let μ : Measure (G1 E) := Measure.haar
  obtain ⟨D, hD, -, hf⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Gam E)
  exact ⟨⟨μ, D, inferInstance, M.unimod E μ, hD, hf μ⟩⟩
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem unit_of_normalised {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (hfr : Module.finrank ℚ E = 2)
    {P : CuspSub E 2} {ω : HChar ℚ} (hN : GlobalTheory.DiscSpec.IsNormalised P) (hC : CenN P ω) (a : (A ℚ)ˣ) :
    ‖((ω.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have hu : P.IsUnitary := GlobalTheory.SpehPair.isUnitary_of_isNormalised hN
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 P.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
  have h1 := hC φ hφ (ideleEmbedding ℚ E a) g
  have h2 := hu.norm_eq hφ (ideleEmbedding ℚ E a) g
  rw [h1, norm_mul, ideleNorm_ideleEmbedding, hfr, map_pow, Units.val_pow_eq_pow_val, norm_pow] at h2
  have h3 : ‖((ω.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := (mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.downN :
    DownN := by
  intro E _ _ _ hfr P hN hC
  obtain ⟨D⟩ := datEx ℚ E hfr
  obtain ⟨W⟩ := weilEx ℚ E D
  obtain ⟨M⟩ := measEx ℚ
  obtain ⟨N⟩ := measEEx E
  obtain ⟨U⟩ := uMeasEx_of
  obtain ⟨ω, hω⟩ := cenEx_of E hfr P hC
  have hnv := asaiNV E D M U P ω W.η hC hω (unit_of_normalised hfr hN hω) W.quad
  have hper : ∃ φ ∈ P.V, ∃ h : G1 E, (UPer D M fun x => φ.1 (x * gl h)) ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hnv (perU_of E D W M N P U ω hN hω hno)
  obtain ⟨π, hπ, hJ⟩ := rev_holds E D W M N P hper
  obtain ⟨π', hπ', hI⟩ := toII E D W M N P hN π hπ hJ
  exact finS E D W M N P hN π' hπ' hI
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem absQ_unrAt {F : Type} [Field F] [NumberField F] (s : ℂ) (w : HeightOneSpectrum (𝓞 F)) :
    (GlobalTheory.CuspRep.Model.absC F s).UnrAt w := by
  intro x hx
  apply Units.ext
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm F (GlobalTheory.Mem.Chr.localIdele F w x)) = 1
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x 0 (by simpa [IsUnitAt] using hx)]
  simp

open ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.UnitaryBC GlobalTheory.DiscSpec in
private theorem absQ_val {F : Type} [Field F] [NumberField F] (s : ℂ) (w : HeightOneSpectrum (𝓞 F)) :
    (((GlobalTheory.CuspRep.Model.absC F s).val w : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) := by
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm F (GlobalTheory.Mem.Chr.localIdele F w (atFin w (unif w)))) = _
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w _ 1 (unif_spec w), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
    ← Complex.natCast_log]
  congr 1; push_cast; ring

open scoped Pointwise in
private theorem absNorm_conj {M : Type} [Field M] [NumberField M] (h2 : Module.finrank ℚ M = 2)
    {w w' : HeightOneSpectrum (𝓞 M)} (h : w'.under (𝓞 ℚ) = w.under (𝓞 ℚ)) :
    Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal := by
  haveI : Algebra.IsQuadraticExtension ℚ M := { finrank_eq_two' := h2 }
  haveI : IsGalois ℚ M := inferInstance
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 ℚ) (𝓞 M) (M ≃ₐ[ℚ] M) w.asIdeal w'.asIdeal
    (congrArg HeightOneSpectrum.asIdeal h.symm)
  rw [hg, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv w.asIdeal (g • w.asIdeal) (MulSemiringAction.toRingEquiv _ _ g) rfl).toEquiv.symm

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.descS :
    UpperTheory.V.Z.Bc.DescS := by
  intro M _ _ h2 hM sat' inf' hc _ _ hi
  haveI := hM
  rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hR, -⟩
  swap
  · exfalso
    obtain ⟨v⟩ : Nonempty (InfinitePlace M) := inferInstance
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v) (IsTotallyReal.isReal v)
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised M 2 (by norm_num) P
    fun τ => ⟨_, ParLaws.hasInfChar_infChar (CG.mk P) τ⟩
  have hval : ∀ w w' : HeightOneSpectrum (𝓞 M), Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal →
      (GlobalTheory.CuspRep.Model.absC M s).val w' = (GlobalTheory.CuspRep.Model.absC M s).val w := fun w w' e =>
    Units.ext (by rw [PositivityTheory.Rg.Rs.StrStepB.absC_val, PositivityTheory.Rg.Rs.StrStepB.absC_val, e])
  have hcon : ConjInv (P.twist (GlobalTheory.CuspRep.Model.absC M s)) := hi.mono fun w h w' e => by
    obtain ⟨B, h1, h3⟩ := h w' e
    refine ⟨B.map (· * (GlobalTheory.CuspRep.Model.absC M s).val w), PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC P h1 s, ?_⟩
    have := PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC P h3 s
    rwa [hval w w' (absNorm_conj h2 e)] at this
  obtain ⟨π', h3, h4⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.downN M h2 _ hs hcon
  refine ⟨(π'.twist (GlobalTheory.CuspRep.Model.absC ℚ (-s))).HasSat,
    fun τ => (π'.twist (GlobalTheory.CuspRep.Model.absC ℚ (-s))).HasInfChar (InfinitePlace.mk τ),
    Or.inr ⟨inferInstance, _, rfl, rfl⟩, ?_, ?_⟩
  · filter_upwards [hi, h3] with w a b e
    obtain ⟨B', c, d⟩ := b e
    obtain ⟨B, h1, -⟩ := a w rfl
    have h5 := PositivityTheory.Rg.Rs.StrStepB.hasSat_twist_absC P h1 s
    have hB : B' = B.map (· * (GlobalTheory.CuspRep.Model.absC M s).val w) := GlobalTheory.LFun.HasSatGL.unique d h5
    subst hB
    refine ⟨B, ?_, h1⟩
    have h6 := c.twist (absQ_unrAt (-s) (w.under (𝓞 ℚ)))
    have h7 : (GlobalTheory.CuspRep.Model.absC M s).val w * (GlobalTheory.CuspRep.Model.absC ℚ (-s)).val (w.under (𝓞 ℚ)) = 1 := by
      apply Units.ext
      have hn : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 ℚ)).asIdeal := by
        simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using e
      have h0 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
      rw [Units.val_mul, PositivityTheory.Rg.Rs.StrStepB.absC_val, absQ_val, ← hn, neg_neg, Units.val_one,
        ← Complex.cpow_add _ _ h0]
      simp
    convert h6 using 1
    rw [Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id B]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [mul_assoc, h7]
  · intro τ m hm
    have h5 := hm.twist (GlobalTheory.CuspRep.Model.absC M s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at h5
    have h6 := (h4 τ _ h5).twist (GlobalTheory.CuspRep.Model.absC ℚ (-s))
    rw [UpperTheory.V.TR.SS.expo_absC, Multiset.map_map] at h6
    convert h6 using 1
    conv_lhs => rw [← Multiset.map_id m]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
