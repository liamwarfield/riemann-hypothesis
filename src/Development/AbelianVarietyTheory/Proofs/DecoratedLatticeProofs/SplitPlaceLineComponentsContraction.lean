module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHeisenbergActionLineModulationTranslat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiUnfoldingHeisenbergExchange
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HeisExchange

open GlobalTheory.Unf.ContrHeis

variable {D : D7}

theorem kappa_mul {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D) (g : GA D S)
    (w : WO S B'.L) : l.κ S (w ⬝ mt S g⁻¹) = mt S g ⬝ l.κ S w := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.2.2.1 g w

theorem sympl_resT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c d : WO S L) :
    symplOH S T ((o.resT S).symm (0, c)) ((o.resT S).symm (0, d)) = symplOH S L c d := by
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem sympl_resS {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c d : WO L S) :
    symplOH T S ((o.resS S).symm (0, c)) ((o.resS S).symm (0, d)) = symplOH L S c d := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem act_resT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (g : GA D S) (a : GA D A) (c : WO S L) :
    actO S T g (o.emb (a, 1)) ((o.resT S).symm (0, c)) = (o.resT S).symm (0, c ⬝ mt S g⁻¹) := by
  rw [AddEquiv.eq_symm_apply, o.resT_actO, AddEquiv.apply_symm_apply]
  simp only [actO_eq, mt_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul]

theorem act_resS {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (g : GA D S) (a : GA D A) (c : WO L S) :
    actO T S (o.emb (a, 1)) g ((o.resS S).symm (0, c)) = (o.resS S).symm (0, mt S g ⬝ c) := by
  rw [AddEquiv.eq_symm_apply, o.resS_actO, AddEquiv.apply_symm_apply]
  simp only [actO_eq, inv_one, mt_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]

theorem quasi_resT {ψ : AddChar (AF D.host.F) ℂ} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {γ : WO S L} (hγ : γ ∈ ratMx D L.rank S.rank) (v : WO S L) :
    f ((o.resT S).symm (0, γ + v)) = ψ (-symplOH S L γ v) * f ((o.resT S).symm (0, v)) := by
  have r : (o.resT S).symm (0, γ) ∈ ratMx D T.rank S.rank := by
    refine (o.mem_ratL_resT S _).2 ?_
    simpa only [AddEquiv.apply_symm_apply, Prod.fst, Prod.snd] using (show (0 : WO S A) ∈ ratL A S ∧ γ ∈ ratL L S from ⟨zero_mem _, hγ⟩)
  obtain ⟨γ₂, hγ₂⟩ := r
  have q := hf.quasi γ₂ ((o.resT S).symm (0, v))
  have e : ratW T S γ₂ = (o.resT S).symm (0, γ) := hγ₂
  rwa [e, ← map_add, Prod.mk_add_mk, zero_add, sympl_resT] at q

theorem quasi_resS {ψ : AddChar (AF D.host.F) ℂ} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {f : WO T S → ℂ}
    (hf : IsThetaFunO ψ T S f) {γ : WO L S} (hγ : γ ∈ ratMx D S.rank L.rank) (v : WO L S) :
    f ((o.resS S).symm (0, γ + v)) = ψ (-symplOH L S γ v) * f ((o.resS S).symm (0, v)) := by
  have r : (o.resS S).symm (0, γ) ∈ ratMx D S.rank T.rank := by
    refine (o.mem_ratL_resS S _).2 ?_
    simpa only [AddEquiv.apply_symm_apply, Prod.fst, Prod.snd] using (show (0 : WO A S) ∈ ratL S A ∧ γ ∈ ratL S L from ⟨zero_mem _, hγ⟩)
  obtain ⟨γ₂, hγ₂⟩ := r
  have q := hf.quasi γ₂ ((o.resS S).symm (0, v))
  have e : ratW S T γ₂ = (o.resS S).symm (0, γ) := hγ₂
  rwa [e, ← map_add, Prod.mk_add_mk, zero_add, sympl_resS] at q

theorem integral_exchange {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} (vL : VolM D L.rank S.rank) (T Y : WO S L → ℂ)
    (hT : ∀ γ ∈ ratMx D L.rank S.rank, ∀ v, T (γ + v) = ψ (-symplOH S L γ v) * T v)
    (hY : ∀ γ ∈ ratMx D L.rank S.rank, ∀ v, Y (γ + v) = ψ (symplOH S L γ v) * Y v) (x : WO S L) :
    ∫ v in vL.𝓕, T v * (ψ (-symplOH S L v x) * Y (v + x)) ∂vL.μ =
      ∫ v in vL.𝓕, ψ (symplOH S L v (-x)) * T (v + -x) * Y v ∂vL.μ := by
  have neg : ∀ v y : WO S L, symplOH S L v (-y) = -symplOH S L v y := by
    intro v y
    have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := L) v y (-y)
    rw [add_neg_cancel, symplOH_zero_right] at h
    linear_combination -h
  rw [← covolOne_integral_add vL.covol (fun v => ψ (symplOH S L v (-x)) * T (v + -x) * Y v) ?_ x]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show _ = ψ (symplOH S L (v + x) (-x)) * T (v + x + -x) * Y (v + x)
    rw [add_neg_cancel_right, neg, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_self, add_zero]
    ring
  · intro γ hγ a
    show ψ (symplOH S L (γ + a) (-x)) * T (γ + a + -x) * Y (γ + a) = ψ (symplOH S L a (-x)) * T (a + -x) * Y a
    rw [add_assoc, hT γ hγ, hY γ hγ, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right,
      AddChar.map_add_eq_mul]
    have e : ψ (symplOH S L γ (-x)) * ψ (-(symplOH S L γ a + symplOH S L γ (-x))) * ψ (symplOH S L γ a) = 1 := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_zero_eq_one ψ]
      congr 1
      ring
    linear_combination (ψ (symplOH S L a (-x)) * T (a + -x) * Y a) * e

theorem besselFourierJacobi_unfolding_heisenberg_exchange : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), IsContAut B.A φ →
    ∀ (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ J.W₀ B'.V₀ Θ → ∀ w₀ : WO J.W₀ B'.L,
      hand0 s₁ s₂ l vL φ (heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) Ξ) Θ =
        hand0 s₁ s₂ l vL φ Ξ (heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) Θ) := by
  intro D ψ σ B J B' s₁ s₂ l vL φ _ Ξ Θ hΞ hΘ w₀
  funext h₁
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
  have key := integral_exchange (ψ := ψ) vL
    (fun v => s₂.om₀ (h₀, B'.o.emb (h₁, 1)) Θ ((B'.o.resT J.W₀).symm (0, v)))
    (fun v => liftA B.o s₁.om₀ B.vA φ Ξ h₀ (l.κ J.W₀ v))
    (fun γ hγ v => quasi_resT B'.o J.W₀ (s₂.weil₀.om_pres _ _ hΘ) hγ v)
    (fun γ hγ v => by
      simp only [liftA]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      beta_reduce
      rw [kappa_add, quasi_resS B.o J.W₀ (s₁.weil₀.om_pres _ _ hΞ) (kappa_rat l _ γ hγ), symplOH_kappa, neg_neg]
      ring) (w₀ ⬝ mt J.W₀ h₀⁻¹)
  simp only [pairKer, contractT, thPair, handBF_eq, RCLike.star_def, Complex.conj_conj]
  refine Eq.trans ?_ (key.trans ?_)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce
    congr 1
    simp only [liftA]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    beta_reduce
    rw [s₁.weil₀.om_heis _ _ _ _ hΞ, act_resS, ← kappa_mul, heisO, sympl_resS, symplOH_kappa, ← map_add (f := _),
      Prod.mk_add_mk, add_zero, ← kappa_add]
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce
    rw [s₂.weil₀.om_heis _ _ _ _ hΘ, act_resT, heisO, sympl_resT, ← map_add (f := _), Prod.mk_add_mk, add_zero, Matrix.neg_mul]

end GlobalTheory.FinPl.HeisExchange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiDoubleUnfoldingBilinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DoubleStepLin

theorem besselFourierJacobi_doubleUnfolding_bilinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), IsContAut B.A φ →
    (∀ (Ξ Ξ' : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ B.V₀ J.W₀ Ξ' → IsThetaFunO ψ J.W₀ B'.V₀ Θ →
      hand0 s₁ s₂ l vL φ (Ξ + Ξ') Θ = hand0 s₁ s₂ l vL φ Ξ Θ + hand0 s₁ s₂ l vL φ Ξ' Θ) ∧
    (∀ (c : ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), hand0 s₁ s₂ l vL φ (c • Ξ) Θ = c • hand0 s₁ s₂ l vL φ Ξ Θ) ∧
    (∀ (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ Θ' : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ J.W₀ B'.V₀ Θ → IsThetaFunO ψ J.W₀ B'.V₀ Θ' →
      hand0 s₁ s₂ l vL φ Ξ (Θ + Θ') = hand0 s₁ s₂ l vL φ Ξ Θ + hand0 s₁ s₂ l vL φ Ξ Θ') ∧
    (∀ (c : ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), hand0 s₁ s₂ l vL φ Ξ (c • Θ) = c • hand0 s₁ s₂ l vL φ Ξ Θ) := by
  intro D ψ σ B J B' s₁ s₂ l vL φ hφ
  refine ⟨fun Ξ Ξ' Θ hΞ hΞ' hΘ => ?_, fun c Ξ Θ => ?_, fun Ξ Θ Θ' hΞ hΘ hΘ' => ?_, fun c Ξ Θ => ?_⟩
  · have e := GlobalTheory.FinPl.Comm.doubleThetaUnfolding_linear_first_datum s₁ s₂ l vL (Ξ₂ := Θ) hφ hΞ hΞ' hΘ 1
    simpa only [one_smul] using e
  · funext h₁
    simp only [hand0, handFB, pairKer, contractT, thPair, handBF, map_smul, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (φ _) c, integral_const_mul, star_mul', star_star]
    simp_rw [show ∀ x y : ℂ, x * (c * y) = c * (x * y) from fun x y => by ring, integral_const_mul]
  · have e := GlobalTheory.FinPl.Comm.doubleThetaUnfolding_linear_second_datum s₁ s₂ l vL hφ hΞ hΘ hΘ' 1
    simpa only [one_smul] using e
  · funext h₁
    simp only [hand0, handFB, pairKer, contractT, thPair, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul]

end GlobalTheory.DoubleStepLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharDotProductTrivialOnTsupportNhds
open GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
open scoped Topology

noncomputable section
namespace GlobalTheory.HeisLine

open GlobalTheory.SplitWeil.FourierPi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]

def boxSub (s : kˣ) : OpenAddSubgroup (n → k) where
  carrier := box n s
  add_mem' ha hb := fun i _ => add_mem_cball (ha i trivial) (hb i trivial)
  zero_mem' := fun i _ => by simp [cball]
  neg_mem' ha := fun i _ => neg_mem_cball (ha i trivial)
  isOpen' := isOpen_box s

theorem nonarch : NonarchimedeanAddGroup (n → k) where
  is_nonarchimedean := fun U hU => by
    obtain ⟨s, hs⟩ := exists_box_subset hU
    exact ⟨boxSub s, hs⟩

variable [MeasurableSpace k] [BorelSpace k]

theorem measureReal_box_ne (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (s : kˣ) :
    (μ.real (box n s) : ℂ) ≠ 0 := by
  have h1 : μ (box n s) ≠ 0 := ((isOpen_box s).measure_pos μ ⟨0, fun i _ => by simp [cball]⟩).ne'
  have h2 : μ (box n s) ≠ ⊤ := (isCompact_box s).measure_lt_top.ne
  exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨h1, h2⟩

theorem decomp_integral (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (s : kˣ) {φ : (n → k) → ℂ}
    (hφ : φ ∈ SB (n → k)) (hinv : ∀ t ∈ box n s, ∀ x, φ (x + t) = φ x) :
    ∃ S : Finset (n → k), (∀ y, φ y = ∑ x ∈ S, φ x * (box n s).indicator (fun _ => (1:ℂ)) (y - x)) ∧
      ∀ F : (n → k) → ℂ, (∀ t ∈ box n s, ∀ x, F (x + t) = F x) →
        ∫ y, φ y * F y ∂μ = (μ.real (box n s) : ℂ) * ∑ x ∈ S, φ x * F x := by
  classical
  haveI := secondCountable k
  obtain ⟨S, hS⟩ := GlobalTheory.WeilM.HaarUniq.exists_decomp (boxSub (n := n) s) hφ.2 hinv
  have hinj : ∀ q ∈ S, ∀ q' ∈ S, Quotient.out q = Quotient.out q' → q = q' := fun q _ q' _ h => by
    simpa using congrArg (QuotientAddGroup.mk (s := (boxSub (n := n) s).toAddSubgroup)) h
  have hpt : ∀ y, φ y = ∑ x ∈ S.image Quotient.out, φ x * (box n s).indicator (fun _ => (1:ℂ)) (y - x) := by
    intro y
    rw [Finset.sum_image hinj]
    have := congrFun hS y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [sub_eq_add_neg]
    rfl
  refine ⟨S.image Quotient.out, hpt, fun F hF => ?_⟩
  have h1 : ∀ y, φ y * F y = ∑ x ∈ S.image Quotient.out,
      (φ x * F x) * (box n s).indicator (fun _ => (1:ℂ)) (y - x) := by
    intro y
    rw [hpt y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hy : y - x ∈ box n s
    · have := hF (y - x) hy x
      rw [add_sub_cancel] at this
      rw [this]; ring
    · simp [Set.indicator_of_notMem hy]
  have hint : ∀ x : n → k, Integrable (fun y => (box n s).indicator (fun _ => (1:ℂ)) (y - x)) μ := by
    intro x
    have : Integrable ((box n s).indicator (fun _ => (1:ℂ))) μ :=
      (integrable_indicator_iff (isOpen_box _).measurableSet).mpr
        (integrableOn_const (isCompact_box _).measure_lt_top.ne)
    exact this.comp_sub_right x
  rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
  have h2 : ∀ x : n → k, ∫ y, (box n s).indicator (fun _ => (1:ℂ)) (y - x) ∂μ = (μ.real (box n s) : ℂ) := by
    intro x
    rw [integral_sub_right_eq_self (fun y => (box n s).indicator (fun _ => (1:ℂ)) y) x,
      integral_indicator_const _ (isOpen_box _).measurableSet]
    simp
  rw [integral_finsetSum _ fun x _ => (hint x).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_const_mul, h2, mul_comm]

variable {χ : AddChar k Circle} {c : kˣ}

omit [MeasurableSpace k] [BorelSpace k] in
theorem addChar_dotProduct_trivial_on_tsupport_nhds (hχ : HasConductor χ c) {g : (n → k) → ℂ} (hg : g ∈ SB (n → k)) :
    {t : n → k | ∀ η ∈ tsupport g, χ (η ⬝ᵥ t) = 1} ∈ 𝓝 (0 : n → k) := by
  have h1 : ∀ᶠ t in 𝓝 (0 : n → k), ∀ η ∈ tsupport g, χ (η ⬝ᵥ t) = 1 := by
    refine IsCompact.eventually_forall_of_forall_eventually hg.2 fun η _ => ?_
    have h2 : IsLocallyConstant fun q : (n → k) × (n → k) => χ (q.2 ⬝ᵥ q.1) :=
      hχ.isLocallyConstant.comp_continuous (continuous_snd.dotProduct continuous_fst)
    filter_upwards [h2.eventually_eq ((0 : n → k), η)] with q hq
    simpa using hq
  exact h1

omit [MeasurableSpace k] [BorelSpace k] in
theorem box_nhds (s : kˣ) : box n s ∈ 𝓝 (0 : n → k) :=
  (isOpen_box s).mem_nhds fun i _ => by simp [cball]

omit [MeasurableSpace k] [BorelSpace k] in
theorem invariant_nhds {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    {t : n → k | ∀ x, f (x + t) = f x} ∈ 𝓝 (0 : n → k) := by
  classical
  obtain ⟨s, hs⟩ := exists_box_invariant hf
  exact Filter.mem_of_superset (box_nhds s) fun t ht => hs t ht

omit [MeasurableSpace k] [BorelSpace k] in
theorem tr_mem {a : (n → k) → ℂ} (ha : a ∈ SB (n → k)) (x : n → k) :
    (fun y => a (y - x)) ∈ SB (n → k) :=
  ⟨ha.1.comp_continuous (continuous_id.sub continuous_const), ha.2.comp_homeomorph (Homeomorph.subRight x)⟩

omit [MeasurableSpace k] [BorelSpace k] in
theorem mc_mem (hχ : HasConductor χ c) {b : (n → k) → ℂ} (hb : b ∈ SB (n → k)) (x : n → k) :
    (fun η => (χ (η ⬝ᵥ x) : ℂ) * b η) ∈ SB (n → k) := by
  refine ⟨?_, hb.2.mul_left⟩
  have h1 : IsLocallyConstant fun η : n → k => (χ (η ⬝ᵥ x) : ℂ) :=
    (hχ.isLocallyConstant.comp_continuous (continuous_id.dotProduct continuous_const)).comp _
  exact h1.mul hb.1

theorem law_integrated (hχ : HasConductor χ c) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (h2 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) →
      (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b')
    (a b φ a' b' : SB (n → k)) (ha' : ∀ y, a'.1 y = ∫ t, φ.1 t * a.1 (y - t) ∂μ)
    (hb' : ∀ η, b'.1 η = (∫ t, φ.1 t * (χ (η ⬝ᵥ t) : ℂ) ∂μ) * b.1 η) : B a' b = B a b' := by
  classical
  obtain ⟨s, hs⟩ := exists_box_subset (Filter.inter_mem (invariant_nhds φ.2)
    (Filter.inter_mem (invariant_nhds a.2) (addChar_dotProduct_trivial_on_tsupport_nhds hχ b.2)))
  obtain ⟨S, -, hint⟩ := decomp_integral μ s φ.2 fun t ht x => (hs ht).1 x
  set m : ℂ := (μ.real (box n s) : ℂ)
  have hnegmem : ∀ t ∈ box n s, -t ∈ box n s := fun t ht i _ => neg_mem_cball (ht i trivial)
  have ea : a' = ∑ x ∈ S, (m * φ.1 x) • (⟨_, tr_mem a.2 x⟩ : SB (n → k)) := by
    apply Subtype.ext
    funext y
    rw [Submodule.coe_sum, Finset.sum_apply, ha' y]
    rw [hint (fun t => a.1 (y - t)) fun t ht x => by
      have := (hs (hnegmem t ht)).2.1 (y - x)
      rw [← this]; abel_nf]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have eb : b' = ∑ x ∈ S, (m * φ.1 x) • (⟨_, mc_mem hχ b.2 x⟩ : SB (n → k)) := by
    apply Subtype.ext
    funext η
    rw [Submodule.coe_sum, Finset.sum_apply, hb' η]
    by_cases hη : η ∈ tsupport b.1
    · rw [hint (fun t => (χ (η ⬝ᵥ t) : ℂ)) fun t ht x => by
        rw [dotProduct_add, AddChar.map_add_eq_mul, (hs ht).2.2 η hη, mul_one]]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
      ring
    · have h0 : b.1 η = 0 := image_eq_zero_of_notMem_tsupport hη
      simp [h0]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ea, eb, map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_smul]
  congr 1
  exact h2 a _ b _ x (fun y => rfl) (fun η => rfl)

omit [MeasurableSpace k] [BorelSpace k] in
theorem box_mono {s s' : kˣ} (h : valuation k (s : k) ≤ valuation k (s' : k)) : box n s ⊆ box n s' :=
  fun x hx i _ => show valuation k (x i) ≤ valuation k (s' : k) from le_trans (hx i trivial) h

omit [MeasurableSpace k] [BorelSpace k] in
theorem box_total (s s' : kˣ) : box n s ⊆ box n s' ∨ box n s' ⊆ box n s :=
  (le_total (valuation k (s : k)) (valuation k (s' : k))).imp box_mono box_mono

omit [MeasurableSpace k] [BorelSpace k] in
theorem ind_add (s : kˣ) {t : n → k} (ht : t ∈ box n s) (z : n → k) :
    (box n s).indicator (fun _ => (1 : ℂ)) (z + t) = (box n s).indicator (fun _ => (1 : ℂ)) z := by
  have h : z + t ∈ box n s ↔ z ∈ box n s :=
    add_mem_cancel_right (H := (boxSub (n := n) s).toAddSubgroup) ht
  by_cases hz : z ∈ box n s
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (h.2 hz)]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz (h.1 h'))]

omit [MeasurableSpace k] [BorelSpace k] in
theorem ind_mem (s : kˣ) : (box n s).indicator (fun _ => (1 : ℂ)) ∈ SB (n → k) := by
  haveI := t2Space k
  exact GlobalTheory.WeilM.HaarUniq.indicator_mem (boxSub (n := n) s) (isCompact_box s)

def ind (s : kˣ) : SB (n → k) := ⟨_, ind_mem (n := n) s⟩

theorem conv_ind (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (s : kˣ) {φ : (n → k) → ℂ}
    (hφ : φ ∈ SB (n → k)) (hinv : ∀ t ∈ box n s, ∀ x, φ (x + t) = φ x) (y : n → k) :
    ∫ t, φ t * (box n s).indicator (fun _ => (1 : ℂ)) (y - t) ∂μ = (μ.real (box n s) : ℂ) * φ y := by
  obtain ⟨S, hpt, hint⟩ := decomp_integral μ s hφ hinv
  rw [hint _ fun t ht x => by
    rw [show y - (x + t) = (y - x) + -t by abel, ind_add s (show -t ∈ box n s from fun i _ => neg_mem_cball (ht i trivial))],
    hpt y]

def admitted (χ : AddChar k Circle) (s : kˣ) (g : (n → k) → ℂ) : Prop :=
  ∀ η, g η ≠ 0 → ∀ t ∈ box n s, χ (η ⬝ᵥ t) = 1

omit [MeasurableSpace k] [BorelSpace k] in
theorem isAdmissibleBoxForCharacter_of_subset {s : kˣ} {g : (n → k) → ℂ}
    (h : box n s ⊆ {t : n → k | ∀ η ∈ tsupport g, χ (η ⬝ᵥ t) = 1}) : admitted χ s g :=
  fun η hη t ht => h ht η (subset_tsupport _ hη)


theorem ratio_indep (hχ : HasConductor χ c) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (h2 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) →
      (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b')
    {s s' : kˣ} (g : SB (n → k)) (hs : admitted χ s g.1) (hss : box n s' ⊆ box n s) :
    (μ.real (box n s) : ℂ)⁻¹ * B (ind s) g = (μ.real (box n s') : ℂ)⁻¹ * B (ind s') g := by
  haveI := secondCountable k
  have key := law_integrated hχ μ B h2 (ind s') g (ind s) ((μ.real (box n s') : ℂ) • ind s)
    ((μ.real (box n s) : ℂ) • g) (fun y => by
      show (μ.real (box n s') : ℂ) * (box n s).indicator (fun _ => (1 : ℂ)) y =
        ∫ t, (box n s).indicator (fun _ => (1 : ℂ)) t * (box n s').indicator (fun _ => (1 : ℂ)) (y - t) ∂μ
      rw [conv_ind μ s' (ind_mem s) (fun t ht x => ind_add s (hss ht) x) y]) (fun η => by
      show (μ.real (box n s) : ℂ) * g.1 η = _
      by_cases hη : g.1 η = 0
      · simp [hη]
      · congr 1
        have : ∀ t, (ind s).1 t * (χ (η ⬝ᵥ t) : ℂ) = (box n s).indicator (fun _ => (1 : ℂ)) t := by
          intro t
          by_cases ht : t ∈ box n s
          · rw [hs η hη t ht]; simp [ind]
          · simp [ind, Set.indicator_of_notMem ht]
        simp only [this]
        rw [integral_indicator_const _ (isOpen_box _).measurableSet]
        simp)
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at key
  have h1 := measureReal_box_ne μ s
  have h1' := measureReal_box_ne μ s'
  field_simp
  linear_combination key

omit [MeasurableSpace k] [BorelSpace k] in
theorem exists_adm (hχ : HasConductor χ c) (g : SB (n → k)) : ∃ s : kˣ, admitted χ s g.1 := by
  obtain ⟨s, hs⟩ := exists_box_subset (addChar_dotProduct_trivial_on_tsupport_nhds hχ g.2)
  exact ⟨s, isAdmissibleBoxForCharacter_of_subset hs⟩


open scoped Classical in
open Classical in
def ell (χ : AddChar k Circle) (μ : Measure (n → k)) (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (g : SB (n → k)) : ℂ :=
  if h : ∃ s : kˣ, admitted χ s g.1 then (μ.real (box n h.choose) : ℂ)⁻¹ * B (ind h.choose) g else 0

section Form
variable (hχ : HasConductor χ c) (μ : Measure (n → k)) [μ.IsAddHaarMeasure]
    (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ)
    (h2 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) →
      (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b')
include hχ h2

theorem ell_eq {s : kˣ} (g : SB (n → k)) (hs : admitted χ s g.1) :
    ell χ μ B g = (μ.real (box n s) : ℂ)⁻¹ * B (ind s) g := by
  have h : ∃ s : kˣ, admitted χ s g.1 := ⟨s, hs⟩
  rw [ell, dite_eq_left h]
  rcases box_total (n := n) h.choose s with h1 | h1
  · exact (ratio_indep hχ μ B h2 g hs h1).symm
  · exact ratio_indep hχ μ B h2 g h.choose_spec h1

def ellL : SB (n → k) →ₗ[ℂ] ℂ where
  toFun := ell χ μ B
  map_add' g g' := by
    obtain ⟨s, hs⟩ := exists_box_subset (Filter.inter_mem (addChar_dotProduct_trivial_on_tsupport_nhds hχ g.2) (addChar_dotProduct_trivial_on_tsupport_nhds hχ g'.2))
    have a1 : admitted χ s g.1 := isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).1
    have a2 : admitted χ s g'.1 := isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).2
    have a3 : admitted χ s (g + g').1 := fun η hη t ht => by
      by_cases h : g.1 η = 0
      · have : g'.1 η ≠ 0 := by
          intro h'
          apply hη
          simp [h, h']
        exact a2 η this t ht
      · exact a1 η h t ht
    rw [ell_eq hχ μ B h2 _ a1, ell_eq hχ μ B h2 _ a2, ell_eq hχ μ B h2 _ a3, map_add (f := _)]
    ring
  map_smul' z g := by
    obtain ⟨s, hs⟩ := exists_adm hχ g
    have a3 : admitted χ s (z • g).1 := fun η hη t ht => hs η (fun h => hη (by simp [h])) t ht
    rw [ell_eq hχ μ B h2 _ hs, ell_eq hχ μ B h2 _ a3, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul]
    ring

theorem ell_translate
    (h1 : ∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = (χ (t ⬝ᵥ y) : ℂ) * a.1 y) →
      (∀ η, b'.1 η = b.1 (η - t)) → B a' b = B a b')
    (g : SB (n → k)) (u : n → k) (hg' : (fun x => g.1 (x + u)) ∈ SB (n → k)) :
    ell χ μ B ⟨_, hg'⟩ = ell χ μ B g := by
  have hloc : {y : n → k | χ ((-u) ⬝ᵥ y) = 1} ∈ 𝓝 (0 : n → k) := by
    have h3 : IsLocallyConstant fun y : n → k => χ ((-u) ⬝ᵥ y) :=
      hχ.isLocallyConstant.comp_continuous (continuous_const.dotProduct continuous_id)
    filter_upwards [h3.eventually_eq 0] with y hy
    simpa using hy
  obtain ⟨s, hs⟩ := exists_box_subset
    (Filter.inter_mem (addChar_dotProduct_trivial_on_tsupport_nhds hχ g.2) (Filter.inter_mem (addChar_dotProduct_trivial_on_tsupport_nhds hχ hg') hloc))
  have a1 : admitted χ s g.1 := isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).1
  have a2 : admitted χ s (fun x => g.1 (x + u)) := isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).2.1
  rw [ell_eq hχ μ B h2 ⟨_, hg'⟩ a2, ell_eq hχ μ B h2 g a1]
  congr 1
  refine (h1 (ind s) (ind s) g ⟨_, hg'⟩ (-u) (fun y => ?_) (fun η => ?_)).symm
  · by_cases hy : y ∈ box n s
    · show (box n s).indicator (fun _ => (1 : ℂ)) y = _ * (box n s).indicator (fun _ => (1 : ℂ)) y
      rw [(hs hy).2.2]
      simp
    · show (box n s).indicator (fun _ => (1 : ℂ)) y = _ * (box n s).indicator (fun _ => (1 : ℂ)) y
      simp [Set.indicator_of_notMem hy]
  · show g.1 (η + u) = g.1 (η - -u)
    rw [sub_neg_eq_add]

theorem form_eq_ell (a b : SB (n → k))
    (hm : (fun η => (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η) ∈ SB (n → k)) :
    B a b = ell χ μ B ⟨_, hm⟩ := by
  haveI := secondCountable k
  obtain ⟨s, hs⟩ := exists_box_subset (Filter.inter_mem (invariant_nhds a.2) (addChar_dotProduct_trivial_on_tsupport_nhds hχ hm))
  have a1 : admitted χ s (fun η => (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η) :=
    isAdmissibleBoxForCharacter_of_subset fun t ht => (hs ht).2
  rw [ell_eq hχ μ B h2 ⟨_, hm⟩ a1]
  have key := law_integrated hχ μ B h2 (ind s) b a ((μ.real (box n s) : ℂ) • a) ⟨_, hm⟩
    (fun y => by
      show (μ.real (box n s) : ℂ) * a.1 y = ∫ t, a.1 t * (box n s).indicator (fun _ => (1 : ℂ)) (y - t) ∂μ
      rw [conv_ind μ s a.2 (fun t ht x => (hs ht).1 x) y]) (fun η => rfl)
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at key
  rw [← key]
  field_simp [measureReal_box_ne μ s]

end Form

theorem heis_invariant_form : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] (χ : AddChar k Circle), Continuous χ → χ ≠ 1 → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (B : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ), (∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = (χ (t ⬝ᵥ y) : ℂ) * a.1 y) → (∀ η, b'.1 η = b.1 (η - t)) → B a' b = B a b') → (∀ (a a' b b' : SB (n → k)) (t : n → k), (∀ y, a'.1 y = a.1 (y - t)) → (∀ η, b'.1 η = (χ (η ⬝ᵥ t) : ℂ) * b.1 η) → B a' b = B a b') → ∃ c : ℂ, ∀ a b : SB (n → k), B a b = c * ∫ η, (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η ∂μ := by
  intro k _ _ _ _ _ _ n _ χ hc hne μ _ B hL1 hL2
  classical
  obtain ⟨c, hχ⟩ := exists_hasConductor_of_continuous χ hc hne
  haveI := secondCountable k
  haveI := t2Space k
  haveI := nonarch (k := k) (n := n)
  have hm : ∀ a b : SB (n → k), (fun η => (∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) * b.1 η) ∈ SB (n → k) := by
    intro a b
    have h3 := fourier_mem_SB μ hχ a.2
    have h4 : (fun η => ∫ y, a.1 y * (χ (η ⬝ᵥ y) : ℂ) ∂μ) = fun η => ∫ x, a.1 x * (χ (x ⬝ᵥ η) : ℂ) ∂μ := by
      funext η
      simp only [dotProduct_comm η]
    rw [← h4] at h3
    exact ⟨h3.1.mul b.2.1, b.2.2.mul_left⟩
  obtain ⟨M, hM⟩ := LinearMap.exists_extend (ellL hχ μ B hL2)
  have hMe : ∀ g : SB (n → k), M g.1 = ell χ μ B g := fun g => LinearMap.congr_fun hM g
  obtain ⟨C, hC⟩ := GlobalTheory.WeilM.HaarUniq.exists_eq_mul_integral (n → k) μ M (fun φ hφ u => by
    have hmem : (fun x => φ (x + u)) ∈ SB (n → k) :=
      ⟨hφ.1.comp_continuous (continuous_id.add continuous_const), hφ.2.comp_homeomorph (Homeomorph.addRight u)⟩
    rw [hMe ⟨_, hmem⟩, ell_translate hχ μ B hL2 hL1 ⟨φ, hφ⟩ u hmem]
    exact (hMe ⟨φ, hφ⟩).symm)
  refine ⟨C, fun a b => ?_⟩
  rw [form_eq_ell hχ μ B hL2 a b (hm a b), ← hMe, hC _ (hm a b)]

end GlobalTheory.HeisLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineComponentsContraction
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem contraction_all : ∀ D : D7, GlobalTheory.FinPl.Contraction D := by
  intro D k _ _ _ _ _ _ p ψ χ hχ
  obtain ⟨ε, hε, hloc⟩ := GlobalTheory.T.splitPlace_heisenbergAction_line_modulation_translation D k p ψ χ hχ
  refine ⟨ε, hε, ?_⟩
  intro n n' n'' _ _ _ _ _ _ σ B J B' s₁ s₂ l vL α α₀ β γ γ₀ hα hγ μ _ L₁ L₂ L₂' L₃ f₁ Ξ₁ Ξ₁' f₂ Ξ₂ Ξ₂' Ψ₁ Ψ₂
    a a' b b' ha ha' hb hb' h1 h1' h2 h2' φ hφ
  by_cases hA0 : a = 0 ∧ a' = 0
  · obtain ⟨rfl, rfl⟩ := hA0
    simp
  by_cases hB0 : b = 0 ∧ b' = 0
  · obtain ⟨rfl, rfl⟩ := hB0
    simp
  have hstd : IsStdChar D ψ (-1) := s₁.weil.std
  obtain ⟨sbC, sbC', sbR, sbR'⟩ := GlobalTheory.FinPl.tens_SB_iff k n n'
  obtain ⟨sbC2, sbC2', sbR2, sbR2'⟩ := GlobalTheory.FinPl.tens_SB_iff k n n''
  have hΨ₁ : Ψ₁ ∈ SB (Matrix n n' k) := by
    by_cases h0 : a = 0
    · exact sbC' Ψ₁ a' h1'.2.2.2.1 (fun h => hA0 ⟨h0, h⟩)
    · exact sbC' Ψ₁ a h1.2.2.2.1 h0
  have hΨ₂ : Ψ₂ ∈ SB (Matrix n'' n k) := by
    by_cases h0 : b = 0
    · exact sbR2' Ψ₂ b' h2'.2.2.2.1 (fun h => hB0 ⟨h0, h⟩)
    · exact sbR2' Ψ₂ b h2.2.2.2.1 h0
  obtain ⟨⟨T₁, hT₁⟩, -⟩ := h1.2.2.2.2
  obtain ⟨⟨T₂, hT₂⟩, -⟩ := h2.2.2.2.2
  let A : ((n → k) → ℂ) → (WO B.V₀ J.W₀ → ℂ) := fun a => T₁ (extFun α₀ β (tensCol Ψ₁ a))
  let Bb : ((n → k) → ℂ) → (WO J.W₀ B'.V₀ → ℂ) := fun b => T₂ (extFun β γ₀ (tensRow Ψ₂ b))
  have hA_eq : ∀ a₀ Ξ, Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a₀) Ξ → Ξ = A a₀ := fun a₀ Ξ h => h.2.2.2.2.2 T₁ hT₁
  have hB_eq : ∀ b₀ Ξ, Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b₀) Ξ → Ξ = Bb b₀ := fun b₀ Ξ h => h.2.2.2.2.2 T₂ hT₂
  have OB1 := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hstd B.V₀ J.W₀ α₀ β L₁ L₂ h1.1 h1.2.1 f₁ h1.2.2.1
  have OB2 := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p (n'' ⊕ Fin 1) n ψ hstd J.W₀ B'.V₀ β γ₀ L₂' L₃ h2.1 h2.2.1 f₂ h2.2.2.1
  have hA_over : ∀ a₀ ∈ SB (n → k), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a₀) (A a₀) := by
    intro a₀ ha₀
    obtain ⟨f, hf, -⟩ := OB1.1 _ (sbC Ψ₁ a₀ hΨ₁ ha₀)
    rwa [← hA_eq a₀ f hf]
  have hB_over : ∀ b₀ ∈ SB (n → k), Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b₀) (Bb b₀) := by
    intro b₀ hb₀
    obtain ⟨f, hf, -⟩ := OB2.1 _ (sbR2 Ψ₂ b₀ hΨ₂ hb₀)
    rwa [← hB_eq b₀ f hf]
  have hA_th : ∀ a₀ ∈ SB (n → k), IsThetaFunO ψ B.V₀ J.W₀ (A a₀) := fun a₀ h => (OB1.2.1 _ _ (hA_over a₀ h)).1
  have hB_th : ∀ b₀ ∈ SB (n → k), IsThetaFunO ψ J.W₀ B'.V₀ (Bb b₀) := fun b₀ h => (OB2.2.1 _ _ (hB_over b₀ h)).1
  have hA_add : ∀ a₀ a₁, A (a₀ + a₁) = A a₀ + A a₁ := by
    intro a₀ a₁
    show T₁ _ = T₁ _ + T₁ _
    rw [← map_add (f := _)]; congr 1; funext x
    simp only [extFun, tensCol, Pi.add_apply]
    split_ifs <;> ring
  have hA_smul : ∀ (c : ℂ) a₀, A (c • a₀) = c • A a₀ := by
    intro c a₀
    show T₁ _ = c • T₁ _
    rw [← map_smul]; congr 1; funext x
    simp only [extFun, tensCol, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  have hB_add : ∀ b₀ b₁, Bb (b₀ + b₁) = Bb b₀ + Bb b₁ := by
    intro b₀ b₁
    show T₂ _ = T₂ _ + T₂ _
    rw [← map_add (f := _)]; congr 1; funext x
    simp only [extFun, tensRow, Pi.add_apply]
    split_ifs <;> ring
  have hB_smul : ∀ (c : ℂ) b₀, Bb (c • b₀) = c • Bb b₀ := by
    intro c b₀
    show T₂ _ = c • T₂ _
    rw [← map_smul]; congr 1; funext x
    simp only [extFun, tensRow, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  obtain ⟨add₁, smul₁, add₂, smul₂⟩ := GlobalTheory.DoubleStepLin.besselFourierJacobi_doubleUnfolding_bilinear D ψ σ B J B' s₁ s₂ l vL φ hφ
  obtain ⟨hχc, hχ1⟩ := GlobalTheory.FinPl.SplitChar.cont_ne_one D k p ψ χ hχ hstd
  let χε : AddChar k Circle := χ.compAddMonoidHom (AddMonoidHom.mulLeft ε)
  have hχε : ∀ x, χε x = χ (ε * x) := fun x => rfl
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> simp [h]
  have hχεc : Continuous χε := hχc.comp (continuous_const.mul continuous_id)
  have hχε1 : χε ≠ 1 := by
    intro h
    apply hχ1
    ext x
    have := congrArg (fun f : AddChar k Circle => f (ε * x)) h
    simp only [hχε, AddChar.one_apply] at this
    rw [← mul_assoc, hε2, one_mul] at this
    simp [this]
  have key : ∀ h₁ : GA D B'.A, ∃ c : ℂ, ∀ a₀ b₀ : SB (n → k), hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₀.1) h₁ =
      c * ∫ η, (∫ y, a₀.1 y * (χε (η ⬝ᵥ y) : ℂ) ∂μ) * b₀.1 η ∂μ := by
    intro h₁
    let Bf : SB (n → k) →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun a₀ b₀ => hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₀.1) h₁)
      (fun m₁ m₂ n₀ => by
        simp only [Submodule.coe_add, hA_add]
        rw [add₁ _ _ _ (hA_th _ m₁.2) (hA_th _ m₂.2) (hB_th _ n₀.2)]; rfl)
      (fun c m n₀ => by
        simp only [Submodule.coe_smul, hA_smul]
        rw [smul₁]; rfl)
      (fun m n₁ n₂ => by
        simp only [Submodule.coe_add, hB_add]
        rw [add₂ _ _ _ (hA_th _ m.2) (hB_th _ n₁.2) (hB_th _ n₂.2)]; rfl)
      (fun c m n₀ => by
        simp only [Submodule.coe_smul, hB_smul]
        rw [smul₂]; rfl)
    obtain ⟨c, hc⟩ := GlobalTheory.HeisLine.heis_invariant_form k n χε hχεc hχε1 μ Bf
      (fun a₀ a₁ b₀ b₁ t ha₁ hb₁ => by
        obtain ⟨⟨w₀, hw₁, hw₂⟩, -⟩ := hloc n n' n'' σ B B' J.W₀ l α α₀ β γ γ₀ hα hγ hstd t
        have e1 : A a₁.1 = heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) (A a₀.1) := by
          have hfun : a₁.1 = fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a₀.1 y := funext fun y => by rw [ha₁ y, hχε]
          rw [hfun]
          exact (hA_eq _ _ (hw₁ L₁ L₂ f₁ Ψ₁ a₀.1 _ (hA_over _ a₀.2))).symm
        have e2 : Bb b₁.1 = heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) (Bb b₀.1) := by
          have hfun : b₁.1 = fun η => b₀.1 (η - t) := funext hb₁
          rw [hfun]
          exact (hB_eq _ _ (hw₂ L₂' L₃ f₂ Ψ₂ b₀.1 _ (hB_over _ b₀.2))).symm
        show hand0 s₁ s₂ l vL φ (A a₁.1) (Bb b₀.1) h₁ = hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₁.1) h₁
        rw [e1, e2, GlobalTheory.FinPl.HeisExchange.besselFourierJacobi_unfolding_heisenberg_exchange D ψ σ B J B' s₁ s₂ l vL φ hφ _ _ (hA_th _ a₀.2) (hB_th _ b₀.2) w₀])
      (fun a₀ a₁ b₀ b₁ t ha₁ hb₁ => by
        obtain ⟨-, ⟨w₀, hw₁, hw₂⟩⟩ := hloc n n' n'' σ B B' J.W₀ l α α₀ β γ γ₀ hα hγ hstd t
        have e1 : A a₁.1 = heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) (A a₀.1) := by
          have hfun : a₁.1 = fun y => a₀.1 (y - t) := funext ha₁
          rw [hfun]
          exact (hA_eq _ _ (hw₁ L₁ L₂ f₁ Ψ₁ a₀.1 _ (hA_over _ a₀.2))).symm
        have e2 : Bb b₁.1 = heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) (Bb b₀.1) := by
          have hfun : b₁.1 = fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b₀.1 η := funext fun η => by rw [hb₁ η, hχε]
          rw [hfun]
          exact (hB_eq _ _ (hw₂ L₂' L₃ f₂ Ψ₂ b₀.1 _ (hB_over _ b₀.2))).symm
        show hand0 s₁ s₂ l vL φ (A a₁.1) (Bb b₀.1) h₁ = hand0 s₁ s₂ l vL φ (A a₀.1) (Bb b₁.1) h₁
        rw [e1, e2, GlobalTheory.FinPl.HeisExchange.besselFourierJacobi_unfolding_heisenberg_exchange D ψ σ B J B' s₁ s₂ l vL φ hφ _ _ (hA_th _ a₀.2) (hB_th _ b₀.2) w₀])
    exact ⟨c, fun a₀ b₀ => hc a₀ b₀⟩
  have eΞ₁ := hA_eq a Ξ₁ h1
  have eΞ₁' := hA_eq a' Ξ₁' h1'
  have eΞ₂ := hB_eq b Ξ₂ h2
  have eΞ₂' := hB_eq b' Ξ₂' h2'
  funext h₁
  obtain ⟨c, hc⟩ := key h₁
  have k1 := hc ⟨a, ha⟩ ⟨b, hb⟩
  have k2 := hc ⟨a', ha'⟩ ⟨b', hb'⟩
  simp only [hχε] at k1 k2
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [eΞ₁, eΞ₁', eΞ₂, eΞ₂', k1, k2]
  ring

end GlobalTheory.FinPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineComponentsContractionStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_lineComponents_contraction : ∀ D : D7, GlobalTheory.FinPl.Contraction D := by
  first | exact @GlobalTheory.FinPl.contraction_all | exact GlobalTheory.FinPl.contraction_all | (intros; apply GlobalTheory.FinPl.contraction_all <;> assumption)
end
