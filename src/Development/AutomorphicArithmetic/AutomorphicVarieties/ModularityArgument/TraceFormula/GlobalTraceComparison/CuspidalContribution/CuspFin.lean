module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalOfNonIsomorphic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelSumBoundUniform
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.ReproOf
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscriminantIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscriminantIdentity
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscP

theorem isoV_symm {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {V V' : Submodule ℂ (Sm E N)}
    (hV : _root_.GlobalTheory.CuspRep.IsStable V) (h : IsoV V V') : IsoV V' V := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun o φ ψ e => ?_⟩
  have hm : act o (T.symm φ).1 ∈ V := hV o _ (T.symm φ).2
  have h1 := hT o (T.symm φ) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply, ← e] at h1
  have h2 : T ⟨_, hm⟩ = ψ := Subtype.ext h1
  rw [← h2, LinearEquiv.symm_apply_apply]

theorem main : FinDisc := by
  intro E _ _ _ N _ _ μ _ K W R ε hK hW hε hRep
  set D : Submodule ℂ (Sm E N) → Prop := fun V => IsDiscrete V ∧ HasType K W V ∧ InfBdd R V ∧
    ∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r)) with hD
  by_cases hne : ∃ V, D V
  swap
  · exact ⟨∅, fun V h1 h2 h3 h4 => (hne ⟨V, h1, h2, h3, h4⟩).elim⟩
  obtain ⟨V₁, h₁⟩ := hne
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_fundamental_domain_GL E N μ _ (h₁.1.sqInt 0 (zero_mem _))
  obtain ⟨α, δ, hαc, hαs, hδ, hα⟩ := hRep
  obtain ⟨Ω, hΩ, hconc⟩ := GlobalTheory.T.typed_space_approximation E N μ K W R ε δ α F hK hW hε hαc hαs hδ hF
  obtain ⟨B, hB, hbes⟩ := GlobalTheory.T.kernel_sum_bound_uniform E N μ δ α F Ω hαc hαs hδ hF hΩ

  have key : ∀ (n : ℕ) (Vs : Fin n → Submodule ℂ (Sm E N)), (∀ i, D (Vs i)) →
      (∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j)) → (n : ENNReal) ≤ 2 * B := by
    intro n Vs hVs hne
    have hsel : ∀ i, ∃ ψ : Sm E N, ψ ∈ Vs i ∧ TypeB K W ψ ∧ (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 := by
      intro i
      obtain ⟨hd, ⟨φ, hφ, h0, hty⟩, -, -⟩ := hVs i
      obtain ⟨hT, hZ⟩ := GlobalTheory.T.automorphic_norm_finite_nonzero E N μ F hF φ (hd.aut φ hφ) (hd.sqInt φ hφ) h0
      set L := ∫⁻ x in F, ‖φ.1 x‖ₑ ^ 2 ∂μ with hL
      have hLr : 0 < L.toReal := ENNReal.toReal_pos hZ hT
      set c : ℝ := (Real.sqrt L.toReal)⁻¹ with hc
      have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hLr)
      refine ⟨(c : ℂ) • φ, (Vs i).smul_mem _ hφ, ⟨fun u hu g => ?_, fun g => ?_⟩, ?_⟩
      · have := hty.1 u hu g
        simp only [Submodule.coe_smul, Pi.smul_apply, this]
      · exact W.smul_mem (c : ℂ) (hty.2 g)
      · have e : ∀ x, ‖(((c : ℂ) • φ : Sm E N)).1 x‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖φ.1 x‖ₑ ^ 2 := by
          intro x
          have h2 : ((((c : ℂ) • φ : Sm E N)).1 x) = (c : ℂ) * φ.1 x := rfl
          rw [h2, enorm_mul, mul_pow]
          congr 1
          rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0,
            ENNReal.ofReal_pow hc0.le]
        simp only [e]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hL]
        have : c ^ 2 = (L.toReal)⁻¹ := by
          rw [hc, inv_pow, Real.sq_sqrt hLr.le]
        rw [this, ENNReal.ofReal_inv_of_pos hLr, ENNReal.ofReal_toReal hT]
        exact ENNReal.inv_mul_cancel hZ hT
    choose ψ hψV hψT hψ1 using hsel
    have hcont : ∀ i, Continuous (ψ i).1 := fun i =>
      ContAut.continuous_of_isOpen_stab E N (ψ i) ((hVs i).1.aut _ (hψV i)).level
    have hleft : ∀ i, ∀ γ ∈ latticeGL E N, ∀ x, (ψ i).1 (γ * x) = (ψ i).1 x := by
      intro i γ hγ x
      obtain ⟨ρ, m, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ
      have h1 := ((hVs i).1.sqInt _ (hψV i)).1
      rw [mul_assoc, ((hVs i).1.aut _ (hψV i)).left, ← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_intCast, h1]
    have hs : ∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * (ψ i).1 (x * y) ∂μ = s * (ψ i).1 x := by
      intro i
      refine hα (ψ i) ((hVs i).1.aut _ (hψV i)) (hψT i) fun τ => ?_
      obtain ⟨m, hm, hb⟩ := (hVs i).2.2.1 τ
      refine ⟨m, ⟨hm.1, fun u φ hφ => ?_⟩, hb⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
      rw [map_smul, hm.2 u _ (hψV i), smul_comm]
    have hcB := hbes n (fun i => (ψ i).1) hcont hleft hs hψ1 (fun i j hij =>
      GlobalTheory.T.orthogonal_of_non_isomorphic E N μ F hF (Vs i) (Vs j) (hVs i).1 (hVs j).1 (hne i j hij) _ (hψV i) _ (hψV j))
    have h1 : ∀ i, 1 ≤ 2 * ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := fun i =>
      hconc (Vs i) (ψ i) (hVs i).1 (hψV i) (hψT i) (hVs i).2.2.1 (hVs i).2.2.2 (hs i) (hψ1 i)
    calc (n : ENNReal) = ∑ _i : Fin n, (1 : ENNReal) := by simp
      _ ≤ ∑ i : Fin n, 2 * ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := Finset.sum_le_sum fun i _ => h1 i
      _ = 2 * ∑ i : Fin n, ∫⁻ x in Ω, ‖(ψ i).1 x‖ₑ ^ 2 ∂μ := by rw [Finset.mul_sum]
      _ ≤ 2 * B := by gcongr
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 2 * B ≤ (n₀ : ENNReal) := by
    have h2B : 2 * B ≠ ⊤ := ENNReal.mul_ne_top (by simp) hB
    exact ENNReal.exists_nat_gt h2B |>.imp fun _ h => h.le
  set P : ℕ → Prop := fun n => ∃ Vs : Fin n → Submodule ℂ (Sm E N), (∀ i, D (Vs i)) ∧
    ∀ i j, i ≠ j → ¬ IsoV (Vs i) (Vs j) with hP
  have hbd : ∀ n, P n → n ≤ n₀ := by
    rintro n ⟨Vs, h1, h2⟩
    exact_mod_cast (key n Vs h1 h2).trans hn₀
  have hP0 : P 0 := ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  set n := Nat.findGreatest P n₀ with hn
  obtain ⟨Vs, hVs, hpw⟩ : P n := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  refine ⟨Finset.univ.image Vs, fun V h1 h2 h3 h4 => ?_⟩
  by_contra hno
  have hDV : D V := ⟨h1, h2, h3, h4⟩
  have hno' : ∀ i, ¬ IsoV V (Vs i) := fun i hi => hno ⟨Vs i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩
  have hnext : P (n + 1) := by
    refine ⟨Fin.cons V Vs, fun i => ?_, fun i j hij => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hDV
      · simpa using hVs i
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => simpa using hno' j
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact fun h => hno' i (isoV_symm (hVs i).1.stable h)
        | succ j =>
          simpa using hpw i j fun e => hij (by rw [e])
  have := Nat.le_findGreatest (hbd _ hnext) hnext
  omega

end GlobalTheory.CompanionTheory.FinDiscP

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiscriminantIdentityStatement
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_discriminant_identity : PositivityTheory.Rg.BcB.SpectralAccumulation.FinDisc := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscP.main | exact GlobalTheory.CompanionTheory.FinDiscP.main | (intros; apply GlobalTheory.CompanionTheory.FinDiscP.main <;> assumption)
end PositivityTheory.Rg.BcB.SpectralAccumulation
end
end

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.Rs MeasureTheory

private theorem expV_cusp {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (π : CuspSub E N)
    {r : ℕ} (hr : 0 < r) (hrN : r < N) : ExpV r π.V = ∅ := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := _root_.borel _
  refine Set.eq_empty_of_forall_notMem ?_
  rintro c ⟨φ, hφ, F₀, ⟨μ, 𝓕, hμ, h𝓕, e⟩, F, hF, hF0, -⟩
  have h0 : F₀ = 0 := by
    funext g
    have hc := (π.cusp φ hφ).2
    have h := @hc r hr hrN (_root_.borel _) ⟨rfl⟩ μ 𝓕 hμ h𝓕 g
    rw [e]
    simpa [PositivityTheory.Affgl.CT.ct] using h
  subst h0
  refine hF0 ((Submodule.mem_bot ℂ).1 ((Submodule.span_le (p := ⊥)).2 ?_ hF))
  rintro _ ⟨t, rfl⟩
  exact (Submodule.mem_bot ℂ).2 rfl

private theorem iso_of_isoV {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {π π' : CuspSub E N}
    {V : Submodule ℂ (Sm E N)} (h : IsoV π.V V) (h' : IsoV π'.V V) : π.Iso π' := by
  obtain ⟨T₁, e₁⟩ := h
  obtain ⟨T₂, e₂⟩ := h'
  refine ⟨T₁.trans T₂.symm, fun o φ => ?_⟩
  have a := e₁ o φ (π.op o φ) rfl
  have b := e₂ o (T₂.symm (T₁ φ)) (π'.op o (T₂.symm (T₁ φ))) rfl
  rw [LinearEquiv.apply_symm_apply] at b
  simp only [LinearEquiv.trans_apply]
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext (a.trans b.symm)

private theorem isDiscrete_of_norm' {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} {π : CuspSub E N}
    (hn : GlobalTheory.DiscSpec.IsNormalised π) : IsDiscrete π.V :=
  isDiscrete_of_cuspSub π fun φ hφ => by
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_invariant (π.cusp φ hφ) (hn φ hφ)
    exact GlobalTheory.DiscChar.isSqInt_of_bounded (hn φ hφ) (C := C) fun g => by simpa using hC g

private theorem cuspFin_of (hF : FinDisc) : CuspFin := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro E _ _ _ N hN K W R hK hW
    letI : MeasurableSpace (GA E N) := _root_.borel _
    haveI : BorelSpace (GA E N) := ⟨rfl⟩
    let μ : Measure (GA E N) := Measure.haar
    obtain ⟨V₀, hV₀⟩ := hF E N μ K W R 1 hK hW one_pos (PositivityTheory.Rg.BcB.CG.reproEx_holds E N μ K W R hK hW)
    have hex : ∀ π : {π : CuspSub E N | GlobalTheory.DiscSpec.IsNormalised π ∧ HasType K W π.V ∧ InfBdd R π.V},
        ∃ V' ∈ V₀, IsoV π.1.V V' := fun π =>
      hV₀ _ (isDiscrete_of_norm' π.2.1) π.2.2.1 π.2.2.2 fun r hr hrN c hc => by
        rw [expV_cusp π.1 hr hrN] at hc
        exact hc.elim
    choose f hf hfi using hex
    let g : {π : CuspSub E N | GlobalTheory.DiscSpec.IsNormalised π ∧ HasType K W π.V ∧ InfBdd R π.V} → V₀ :=
      fun π => ⟨f π, hf π⟩
    have hg : Function.Injective g := fun a b hab => by
      have e : f a = f b := congrArg Subtype.val hab
      have h := iso_of_isoV (hfi a) (e ▸ hfi b)
      exact Subtype.ext ((UpperTheory.ConvolutionTheory.Dp.isoEq E N _ _).1 h)
    haveI := Finite.of_injective g hg
    exact Set.toFinite _

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.cuspFin :
    CuspFin :=
  cuspFin_of GlobalTheory.T.finite_discriminant_identity
