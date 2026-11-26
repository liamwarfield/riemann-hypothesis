module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsIsCayleyUIff
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CircleIntegralInvSubEqZeroOfOutside
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset Filter Topology
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace GlobalTheory.DerivedAction

open PI.UpqRep PI.UnitaryGroupMassFormula.CapelliEig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)}

theorem exp_mem {X : Mx k r} (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  refine CCRuleCW.exp_mem_UH (Hpk k r) _ ?_
  have hL : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hL, smul_zero]

theorem one_mem : (1 : Mx k r) ∈ UH (Hpk k r) := by
  show (1 : Mx k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem lie_conj {X g : Mx k r} (hX : InLieHpk k r X) (hg : g ∈ UH (Hpk k r)) :
    InLieHpk k r (g⁻¹ * X * g) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (unitary_Hecke_group k r g hg).1
  have hi1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  have hL : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have A : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
    calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hU]
      _ = (g * g⁻¹)ᴴ * Hpk k r * g := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [hi1, conjTranspose_one, Matrix.one_mul]
  have B : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hU]
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, hi1, Matrix.mul_one]
  show (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g)
        = gᴴ * (Xᴴ * ((g⁻¹)ᴴ * Hpk k r)) + (Hpk k r * g⁻¹) * X * g := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = gᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * g := by
          rw [A, B]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hL]; simp

theorem lie_conj' {X g : Mx k r} (hX : InLieHpk k r X) (hg : g ∈ UH (Hpk k r)) :
    InLieHpk k r (g * X * g⁻¹) := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (unitary_Hecke_group k r g hg).1
  have := lie_conj hX (unitary_Hecke_group k r g hg).2.1
  rwa [Matrix.nonsing_inv_nonsing_inv _ hu] at this

theorem hasDerivAt_local {X g : Mx k r} (hX : InLieHpk k r X) {f F : Mx k r → H} {U : Set (Mx k r)}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUH (Hpk k r) h → f h = F h)
    (hg : g ∈ UH (Hpk k r)) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ h0.symm
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU.mem_nhds hgU)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with t ht
  exact hfF _ ht ((unitary_Hecke_group k r g hg).2.2 _ (exp_mem hX t))

theorem exists_lin {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    ∃ L : Mx k r →L[ℝ] H, ∀ X, InLieHpk k r X → dsig (k := k) (r := r) σ X v = L X ∧
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) σ X v) 0 := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 one_mem
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have h := hasDerivAt_local hX hU h1 hF hfF one_mem
  simp only [Matrix.one_mul] at h
  have e : dsig (k := k) (r := r) σ X v = fderiv ℝ F 1 X := h.deriv
  exact ⟨e, e ▸ h⟩

theorem hasDerivAt_dsig {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) (dsig (k := k) (r := r) σ X v) 0 := by
  obtain ⟨L, hL⟩ := exists_lin hv
  exact (hL X hX).2

theorem hasDerivAt_apply {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    (T : H →L[ℂ] H) :
    HasDerivAt (fun t : ℝ => T (σ (NormedSpace.exp ((t : ℂ) • X)) v)) (T (dsig (k := k) (r := r) σ X v)) 0 :=
  (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dsig hX hv)

theorem dsig_zero (X : Mx k r) : dsig (k := k) (r := r) σ X (0 : H) = 0 := by
  simp [dsig]

theorem dsig_add {X : Mx k r} (hX : InLieHpk k r X) {v w : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ)
    (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (v + w) = dsig (k := k) (r := r) σ X v + dsig (k := k) (r := r) σ X w := by
  have h := (hasDerivAt_dsig hX hv).add (hasDerivAt_dsig hX hw)
  rw [← h.deriv]
  unfold dsig
  congr 1
  funext t
  simp

theorem dsig_smul {X : Mx k r} (hX : InLieHpk k r X) (a : ℂ) {v : H} (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X (a • v) = a • dsig (k := k) (r := r) σ X v := by
  have h := (hasDerivAt_dsig hX hv).const_smul a
  rw [← h.deriv]
  unfold dsig
  congr 1
  funext t
  simp

theorem dsig_smooth (hσ : IsDSHpk k r ε mu σ) {X : Mx k r} (hX : InLieHpk k r X) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ X v ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hv g₀ hg₀
  let L : Mx k r →L[ℝ] Mx k r := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hL : ∀ x, L x = x * X := by intro x; simp [L]
  refine ⟨U, fun g => fderiv ℝ F g (L g), hU, hgU, ?_, ?_⟩
  · exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  · intro g hg hgH
    have h1 := hasDerivAt_local hX hU hg hF hfF hgH
    have h2 := hasDerivAt_apply hX hv (σ g)
    have e : (fun u : ℝ => σ (g * NormedSpace.exp ((u : ℂ) • X)) v) =
        fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v) := by
      funext t
      rw [Hecke_multiplication k r ε mu H σ hσ g hgH _ (exp_mem hX t)]
      rfl
    rw [e] at h1
    simp only [hL]
    exact h2.unique h1

theorem dsig_conj (hσ : IsDSHpk k r ε mu σ) {X g : Mx k r} (hX : InLieHpk k r X) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hg : g ∈ UH (Hpk k r)) :
    σ g (dsig (k := k) (r := r) σ X v) = dsig (k := k) (r := r) σ (g * X * g⁻¹) (σ g v) := by
  rw [← (hasDerivAt_apply hX hv (σ g)).deriv]
  unfold dsig
  congr 1
  funext t
  obtain ⟨hu, hi, hm⟩ := unitary_Hecke_group k r g hg
  have hi1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have e1 : σ g (σ (NormedSpace.exp ((t : ℂ) • X)) v) = σ (g * NormedSpace.exp ((t : ℂ) • X)) v := by
    rw [Hecke_multiplication k r ε mu H σ hσ g hg _ (exp_mem hX t)]; rfl
  have e2 : σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g v) =
      σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g) v := by
    rw [Hecke_multiplication k r ε mu H σ hσ _ (exp_mem (lie_conj' hX hg) t) g hg]; rfl
  have e3 : (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, e2, e3, Matrix.exp_conj _ _ hu, Matrix.mul_assoc _ g⁻¹ g, hi1, Matrix.mul_one]

theorem dsig_kfin [CompleteSpace H] (hK : PI.KFinSmooth) (hmu : IsHCParam mu) (hσ : IsDSHpk k r ε mu σ)
    {X : Mx k r} (hX : InLieHpk k r X) {v : H} (hv : IsKFinHpk (k := k) (r := r) σ v) :
    IsKFinHpk (k := k) (r := r) σ (dsig (k := k) (r := r) σ X v) := by
  obtain ⟨S, hfd, hvS, hS⟩ := hv
  have hsm : ∀ x ∈ S, x ∈ smoothVecs (k := k) (r := r) σ := fun x hx =>
    hK k r ε mu H σ hmu hσ x ⟨S, hfd, hx, hS⟩
  refine ⟨Submodule.span ℂ {y | ∃ Y, InLieHpk k r Y ∧ ∃ s ∈ S, y = dsig (k := k) (r := r) σ Y s}, ?_,
    Submodule.subset_span ⟨X, hX, v, hvS, rfl⟩, ?_⟩
  · obtain ⟨fs, hfs⟩ := (Submodule.fg_iff_finiteDimensional S).2 hfd
    have hfsS : ∀ x : fs, (x : H) ∈ S := fun x => hfs ▸ Submodule.subset_span x.2
    choose L hL using fun x : fs => exists_lin (hsm x (hfsS x))
    let b := Module.finBasis ℝ (Mx k r)
    let T : Submodule ℂ H := Submodule.span ℂ (Set.range fun p : fs × Fin (Module.finrank ℝ (Mx k r)) =>
      L p.1 (b p.2))
    haveI : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    refine Submodule.finiteDimensional_of_le (S₂ := T) (Submodule.span_le.2 ?_)
    rintro _ ⟨Y, hY, s, hs, rfl⟩
    rw [← hfs] at hs hsm
    show dsig (k := k) (r := r) σ Y s ∈ T
    induction hs using Submodule.span_induction with
    | mem y hy =>
      set_option synthInstance.maxHeartbeats 100000 in
        rw [(hL ⟨y, hy⟩ Y hY).1, ← b.sum_repr Y, map_sum]
      refine T.sum_mem fun j _ => ?_
      rw [map_smul]
      exact T.smul_of_tower_mem _ (Submodule.subset_span ⟨(⟨y, hy⟩, j), rfl⟩)
    | zero => rw [dsig_zero]; exact T.zero_mem
    | add x y hx hy ihx ihy => rw [dsig_add hY (hsm x hx) (hsm y hy)]; exact T.add_mem ihx ihy
    | smul a x hx ih => rw [dsig_smul hY a (hsm x hx)]; exact T.smul_mem a ih
  · intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨Y, hY, s, hs, rfl⟩ := hy
      rw [dsig_conj hσ hY (hsm s hs) hg.1]
      exact Submodule.subset_span ⟨_, lie_conj' hY hg.1, _, hS g hg s hs, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [map_add (f := _)]; exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih => rw [map_smul]; exact Submodule.smul_mem _ a ih

theorem dsig_skew (hσ : IsDSHpk k r ε mu σ) {X : Mx k r} (hX : InLieHpk k r X) {v w : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    ⟪dsig (k := k) (r := r) σ X v, w⟫_ℂ = -⟪v, dsig (k := k) (r := r) σ X w⟫_ℂ := by
  obtain ⟨h1, hunit⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hσ
  have h := (hasDerivAt_dsig hX hv).inner ℂ (hasDerivAt_dsig hX hw)
  have e : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) v, σ (NormedSpace.exp ((t : ℂ) • X)) w⟫_ℂ) =
      fun _ => ⟪v, w⟫_ℂ := by
    funext t
    exact (LinearMap.norm_map_iff_inner_map_map
      ((σ (NormedSpace.exp ((t : ℂ) • X)) : H →L[ℂ] H) : H →ₗ[ℂ] H)).1 (hunit _ (exp_mem hX t)) v w
  rw [e] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, h1, ContinuousLinearMap.one_apply] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem dsig_TK (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDS ε mu) {X : Mx k r} (hX : InLieHpk k r X) :
    ∀ v ∈ R.TK, v ∈ R.sm ∧ dsig (k := k) (r := r) R.σ X v ∈ R.TK := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, v₀, hv₀, rfl⟩ := hy
    have hs := hK k r ε mu R.H R.σ hR.1 hR.2 v₀ hv₀
    refine ⟨smooth_right_action k r ε mu R.H R.σ hR.2 v₀ hs g hg, ?_⟩
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (unitary_Hecke_group k r g hg).1
    have hi1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    have h := dsig_conj hR.2 (lie_conj hX hg) hs hg
    have e : g * (g⁻¹ * X * g) * g⁻¹ = X := by
      calc g * (g⁻¹ * X * g) * g⁻¹ = (g * g⁻¹) * X * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hi1, Matrix.one_mul, Matrix.mul_one]
    rw [e] at h
    rw [← h]
    exact Submodule.subset_span ⟨g, hg, _, dsig_kfin hK hR.1 hR.2 (lie_conj hX hg) hv₀, rfl⟩
  | zero => exact ⟨R.smSub.zero_mem, by rw [dsig_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    exact ⟨R.smSub.add_mem ihx.1 ihy.1, by rw [dsig_add hX ihx.1 ihy.1]; exact Submodule.add_mem _ ihx.2 ihy.2⟩
  | smul a x _ ih =>
    exact ⟨R.smSub.smul_mem a ih.1, by rw [dsig_smul hX a ih.1]; exact Submodule.smul_mem _ a ih.2⟩

theorem derived_action : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ X, PI.UpqRep.InLieHpk k r X → (∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧ HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) 0) ∧ (∀ v ∈ R.sm, ∀ g ∈ GG k r, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (g * X * g⁻¹) (R.σ g v)) ∧ (∀ v, R.KFin v → R.KFin (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) ∧ (∀ v ∈ R.TK, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.TK) ∧ (∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, PI.UpqRep.dsig (k := k) (r := r) R.σ X w⟫_ℂ) :=
  fun hK _ _ _ _ R hR _ hX =>
    ⟨fun _ hv => ⟨dsig_smooth hR.2 hX hv, hasDerivAt_dsig hX hv⟩, fun _ hv _ hg => dsig_conj hR.2 hX hv hg,
      fun _ hv => dsig_kfin hK hR.1 hR.2 hX hv, fun v hv => (dsig_TK hK R hR hX v hv).2,
      fun _ hv _ hw => dsig_skew hR.2 hX hv hw⟩

end GlobalTheory.DerivedAction
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesPropertiesStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedAction_discreteSeries_properties : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ X, PI.UpqRep.InLieHpk k r X → (∀ v ∈ R.sm, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.sm ∧ HasDerivAt (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) 0) ∧ (∀ v ∈ R.sm, ∀ g ∈ GG k r, R.σ g (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = PI.UpqRep.dsig (k := k) (r := r) R.σ (g * X * g⁻¹) (R.σ g v)) ∧ (∀ v, R.KFin v → R.KFin (PI.UpqRep.dsig (k := k) (r := r) R.σ X v)) ∧ (∀ v ∈ R.TK, PI.UpqRep.dsig (k := k) (r := r) R.σ X v ∈ R.TK) ∧ (∀ v ∈ R.sm, ∀ w ∈ R.sm, ⟪PI.UpqRep.dsig (k := k) (r := r) R.σ X v, w⟫_ℂ = -⟪v, PI.UpqRep.dsig (k := k) (r := r) R.σ X w⟫_ℂ) := by
  first | exact @GlobalTheory.DerivedAction.derived_action | exact GlobalTheory.DerivedAction.derived_action | (intros; apply GlobalTheory.DerivedAction.derived_action <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CayleyChoice

open PI.UpqRep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem _root_.GlobalTheory.CayleyChoice.Kset_sub {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ _root_.PI.UpqRep.Kset ε) : g ∈ _root_.PI.UpqRep.UJset ε := by
  have hg' : g ∈ unitaryGroup (Fin n) ℂ ∧ g * _root_.PI.UpqRep.Jm ε = _root_.PI.UpqRep.Jm ε * g := hg
  obtain ⟨hu, hc⟩ := hg'
  show gᴴ * _root_.PI.UpqRep.Jm ε * g = _root_.PI.UpqRep.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← star_eq_conjTranspose,
    (mem_unitaryGroup_iff').mp hu, Matrix.one_mul]

private theorem mul_mem_UJset_jet_harmonics {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ _root_.PI.UpqRep.UJset ε) (hb : b ∈ _root_.PI.UpqRep.UJset ε) : a * b ∈ _root_.PI.UpqRep.UJset ε := by
  have ha' : aᴴ * _root_.PI.UpqRep.Jm ε * a = _root_.PI.UpqRep.Jm ε := ha
  have hb' : bᴴ * _root_.PI.UpqRep.Jm ε * b = _root_.PI.UpqRep.Jm ε := hb
  show (a * b)ᴴ * _root_.PI.UpqRep.Jm ε * (a * b) = _root_.PI.UpqRep.Jm ε
  rw [conjTranspose_mul, show bᴴ * aᴴ * _root_.PI.UpqRep.Jm ε * (a * b) = bᴴ * (aᴴ * _root_.PI.UpqRep.Jm ε * a) * b by
    simp only [Matrix.mul_assoc], ha', hb']

private theorem isKTypeOf_map_of_intertwining {σ₁ σ₂ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (e : H ≃ₗ[ℂ] H)
    (he : ∀ k ∈ _root_.PI.UpqRep.Kset ε, ∀ x, σ₂ k (e x) = e (σ₁ k x)) {μ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : _root_.PI.UpqRep.IsKTypeOf ε σ₁ μ S) : _root_.PI.UpqRep.IsKTypeOf ε σ₂ μ (S.map (e : H →ₗ[ℂ] H)) := by
  obtain ⟨hfin, hinv, hirr, ⟨v, hvS, hv0, hvw⟩, hmax⟩ := hS
  have inv_map : ∀ T : Submodule ℂ H, _root_.PI.UpqRep.IsKStableOn ε σ₁ T →
      _root_.PI.UpqRep.IsKStableOn ε σ₂ (T.map (e : H →ₗ[ℂ] H)) := by
    intro T hT k hk y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨σ₁ k x, hT k hk x hx, (he k hk x).symm⟩
  have inv_comap : ∀ T : Submodule ℂ H, _root_.PI.UpqRep.IsKStableOn ε σ₂ T →
      _root_.PI.UpqRep.IsKStableOn ε σ₁ (T.comap (e : H →ₗ[ℂ] H)) := by
    intro T hT k hk x hx
    show e (σ₁ k x) ∈ T
    rw [← he k hk x]
    exact hT k hk _ hx
  have wt : ∀ (ν : Fin n → ℝ) (x : H), _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₁ ν x →
      _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₂ ν (e x) := by
    intro ν x hx θ hθ
    rw [he _ hθ, hx θ hθ, map_smul]
  have wt' : ∀ (ν : Fin n → ℝ) (x : H), _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₂ ν (e x) →
      _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₁ ν x := by
    intro ν x hx θ hθ
    apply e.injective
    rw [← he _ hθ, hx θ hθ, map_smul]
  refine ⟨?_, inv_map S hinv, ?_, ⟨e v, ⟨v, hvS, rfl⟩, by simpa using hv0, wt μ v hvw⟩, ?_⟩
  · haveI := hfin
    infer_instance
  · intro T hT hTinv
    have hle : T.comap (e : H →ₗ[ℂ] H) ≤ S := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hT hx
      rwa [← e.injective hxy]
    rcases hirr _ hle (inv_comap T hTinv) with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have hy' : e.symm y ∈ T.comap (e : H →ₗ[ℂ] H) := by simpa using hy
      rw [h, Submodule.mem_bot] at hy'
      simpa using congrArg e hy'
    · right
      refine le_antisymm hT ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [← h] at hx
      exact hx
  · intro ν y hy hy0 hyw
    obtain ⟨x, hx, rfl⟩ := hy
    exact hmax ν x hx (by rintro rfl; simp at hy0) (wt' ν x hyw)

theorem _root_.GlobalTheory.CayleyChoice.isDS_conj {lam : Fin n → ℝ} (hσ : _root_.PI.UpqRep.IsDS ε lam σ)
    {u u' : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ _root_.PI.UpqRep.UJset ε) (hu' : u' ∈ _root_.PI.UpqRep.UJset ε) (h1 : u * u' = 1) :
    _root_.PI.UpqRep.IsDS ε lam (fun g => σ (u' * g * u)) := by
  obtain ⟨hc, hnt, ⟨⟨h1σ, hmul⟩, hiso, hcont⟩, hirr, hL2, ⟨S, hS⟩, hmin⟩ := hσ
  have hu'u : u' * u = 1 := mul_eq_one_comm.mp h1
  have conj_mem : ∀ {g}, g ∈ _root_.PI.UpqRep.UJset ε → u' * g * u ∈ _root_.PI.UpqRep.UJset ε := fun hg =>
    mul_mem_UJset_jet_harmonics (mul_mem_UJset_jet_harmonics hu' hg) hu
  have hAB : ∀ x, σ u (σ u' x) = x := by
    intro x
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hu _ hu', h1, h1σ]
    rfl
  have hBA : ∀ x, σ u' (σ u x) = x := by
    intro x
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hu' _ hu, hu'u, h1σ]
    rfl
  have hconj : ∀ g ∈ _root_.PI.UpqRep.UJset ε, ∀ x, σ (u' * g * u) x = σ u' (σ g (σ u x)) := by
    intro g hg x
    rw [hmul _ (mul_mem_UJset_jet_harmonics hu' hg) _ hu, hmul _ hu' _ hg]
    rfl
  have hinner : ∀ x y, ⟪σ u x, σ u y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro x y
    let L : H →ₗᵢ[ℂ] H := ⟨(σ u : H →ₗ[ℂ] H), hiso u hu⟩
    exact L.inner_map_map x y
  let e : H ≃ₗ[ℂ] H :=
    { toLinearMap := (σ u' : H →ₗ[ℂ] H)
      invFun := σ u
      left_inv := hAB
      right_inv := hBA }
  have he : ∀ k ∈ _root_.PI.UpqRep.Kset ε, ∀ x, σ (u' * k * u) (e x) = e (σ k x) := by
    intro k hk x
    show σ (u' * k * u) (σ u' x) = σ u' (σ k x)
    rw [hconj k (_root_.GlobalTheory.CayleyChoice.Kset_sub hk), hAB]
  have he' : ∀ k ∈ _root_.PI.UpqRep.Kset ε, ∀ x, σ k (e.symm x) = e.symm (σ (u' * k * u) x) := by
    intro k hk x
    show σ k (σ u x) = σ u (σ (u' * k * u) x)
    rw [hconj k (_root_.GlobalTheory.CayleyChoice.Kset_sub hk), hAB]
  refine ⟨hc, hnt, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ⟨_, isKTypeOf_map_of_intertwining e he hS⟩, ?_⟩
  · show σ (u' * 1 * u) = 1
    rw [Matrix.mul_one, hu'u, h1σ]
  · intro a ha b hb
    show σ (u' * (a * b) * u) = σ (u' * a * u) ∘SL σ (u' * b * u)
    rw [← hmul _ (conj_mem ha) _ (conj_mem hb)]
    congr 1
    rw [show u' * a * u * (u' * b * u) = u' * a * (u * u') * b * u by
      simp only [Matrix.mul_assoc], h1, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  · intro g hg v
    exact hiso _ (conj_mem hg) v
  · intro v
    exact (hcont v).comp ((continuous_const.mul continuous_id).mul continuous_const).continuousOn
      (fun g hg => conj_mem hg)
  · intro T hTc hTinv
    have hT'c : IsClosed (↑(T.comap (σ u' : H →ₗ[ℂ] H)) : Set H) :=
      hTc.preimage (σ u').continuous
    have hT'inv : ∀ g ∈ _root_.PI.UpqRep.UJset ε, ∀ x ∈ T.comap (σ u' : H →ₗ[ℂ] H),
        σ g x ∈ T.comap (σ u' : H →ₗ[ℂ] H) := by
      intro g hg x hx
      have hx' : σ u' x ∈ T := hx
      show σ u' (σ g x) ∈ T
      have := hTinv g hg (σ u' x) hx'
      rw [show σ u' (σ g x) = σ (u' * g * u) (σ u' x) by rw [hconj g hg, hAB]]
      exact this
    rcases hirr _ hT'c hT'inv with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have hmem : σ u y ∈ T.comap (σ u' : H →ₗ[ℂ] H) := by
        show σ u' (σ u y) ∈ T
        rwa [hBA]
      rw [h, Submodule.mem_bot] at hmem
      rw [Submodule.mem_bot, ← hBA y, hmem, map_zero]
    · right
      rw [eq_top_iff]
      intro y _
      have hmem : σ u y ∈ T.comap (σ u' : H →ₗ[ℂ] H) := by
        rw [h]
        exact Submodule.mem_top
      have hmem' : σ u' (σ u y) ∈ T := hmem
      rwa [hBA] at hmem'
  · intro v w
    have key := hL2 (σ u v) (σ u w)
    convert key using 1
    funext g
    have hg : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ _root_.PI.UpqRep.UJset ε := g.2
    show ⟪w, σ (u' * _ * u) v⟫_ℂ = ⟪σ u w, σ _ (σ u v)⟫_ℂ
    rw [hconj _ hg, ← hinner, hAB]
  · intro μ T hT
    exact hmin μ _ (isKTypeOf_map_of_intertwining e.symm he' hT)

theorem _root_.GlobalTheory.CayleyChoice.cayley_exists_and_any : ∀ (k r : ℕ),
    (1 ≤ k → ∃ Q, _root_.PI.UpqRep.IsCayleyU k r (_root_.PI.BesselPeriodGGP.eps48 k r) Q) ∧
    ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ)
      (R : _root_.BranchingSupport.Rep k r),
      R.IsDS ε mu → ∀ Q, _root_.PI.UpqRep.IsCayleyU k r ε Q →
        _root_.PI.UpqRep.IsDS ε mu (fun g => R.σ (Q⁻¹ * g * Q)) := by
  intro k r
  refine ⟨fun hk => ?_, ?_⟩
  · rw [_root_.GlobalTheory.UnitaryCayley.exists_isCayleyU_iff]
    have hcount : ∀ m : ℕ, (∑ x ∈ range (2 * m + 2), if x % 2 = 0 then 1 else 0) = m + 1 := by
      intro m
      induction m with
      | zero => decide
      | succ m ih =>
        rw [show 2 * (m + 1) + 2 = 2 * m + 2 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
        have h1 : (2 * m + 2) % 2 = 0 := by omega
        have h2 : (2 * m + 2 + 1) % 2 ≠ 0 := by omega
        simp [h1, h2]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [card_filter]
    simp only [_root_.PI.BesselPeriodGGP.eps48, Nat.add_sub_cancel]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => if (if i < j then true else decide ((i - j) % 2 = 0)) = true then 1 else 0)]
    rw [show 2 * r + (j + 1) + 1 = j + (2 * r + 2) by ring, sum_range_add]
    have e1 : (∑ x ∈ range j,
        if (if x < j then true else decide ((x - j) % 2 = 0)) = true then 1 else 0) = j := by
      rw [sum_congr rfl (g := fun _ => 1) (fun x hx => by simp [mem_range.mp hx])]
      simp
    have e2 : (∑ x ∈ range (2 * r + 2),
        if (if j + x < j then true else decide ((j + x - j) % 2 = 0)) = true then 1 else 0)
          = r + 1 := by
      rw [← hcount r]
      refine sum_congr rfl (fun x _ => ?_)
      simp
    rw [e1, e2]
    ring
  · intro ε mu R hR Q hQ
    obtain ⟨_, P, hP, hDS⟩ := hR
    have hPd : IsUnit P ∧ Pᴴ * _root_.PI.UpqRep.Jm ε * P = _root_.PI.UpqRep.Hpk k r := hP.1
    have hQd : IsUnit Q ∧ Qᴴ * _root_.PI.UpqRep.Jm ε * Q = _root_.PI.UpqRep.Hpk k r := hQ.1
    have hPi : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).mp hPd.1)
    have hPi' : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).mp hPd.1)
    have hQi : Q * Q⁻¹ = 1 := mul_nonsing_inv Q ((isUnit_iff_isUnit_det Q).mp hQd.1)
    have mem : ∀ {A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ},
        Aᴴ * _root_.PI.UpqRep.Jm ε * A = _root_.PI.UpqRep.Hpk k r → Bᴴ * _root_.PI.UpqRep.Jm ε * B = _root_.PI.UpqRep.Hpk k r →
          B * B⁻¹ = 1 → A * B⁻¹ ∈ _root_.PI.UpqRep.UJset ε := by
      intro A B hA hB hBB
      show (A * B⁻¹)ᴴ * _root_.PI.UpqRep.Jm ε * (A * B⁻¹) = _root_.PI.UpqRep.Jm ε
      rw [conjTranspose_mul, show (B⁻¹)ᴴ * Aᴴ * _root_.PI.UpqRep.Jm ε * (A * B⁻¹)
          = (B⁻¹)ᴴ * (Aᴴ * _root_.PI.UpqRep.Jm ε * A) * B⁻¹ by simp only [Matrix.mul_assoc], hA, ← hB,
        show (B⁻¹)ᴴ * (Bᴴ * _root_.PI.UpqRep.Jm ε * B) * B⁻¹ = (B * B⁻¹)ᴴ * _root_.PI.UpqRep.Jm ε * (B * B⁻¹) by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc],
        hBB, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    have hprod : Q * P⁻¹ * (P * Q⁻¹) = 1 := by
      rw [show Q * P⁻¹ * (P * Q⁻¹) = Q * (P⁻¹ * P) * Q⁻¹ by simp only [Matrix.mul_assoc], hPi',
        Matrix.mul_one, hQi]
    have key := _root_.GlobalTheory.CayleyChoice.isDS_conj hDS (mem hQd.2 hPd.2 hPi)
      (mem hPd.2 hQd.2 hQi) hprod
    convert key using 2 with g
    rw [show P⁻¹ * (P * Q⁻¹ * g * (Q * P⁻¹)) * P = (P⁻¹ * P) * Q⁻¹ * g * Q * (P⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPi', Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.CayleyChoice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsCoordLeOfLOneNormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GapSubsetOfSetBoundIntegral
open Finset
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompareIterDegree

open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms

theorem fdeg_ratio_abs {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) (t : ℝ) (hinj : Function.Injective μ) :
    fdegHC (μ + Pi.single s t) / fdegHC μ = ∏ c ∈ univ.erase s, |(μ s + t - μ c) / (μ s - μ c)| := by
  set μ' : Fin n → ℝ := μ + Pi.single s t with hμ'
  have hμ'a : ∀ a, μ' a = μ a + if a = s then t else 0 := by
    intro a; simp [hμ', Pi.single_apply]
  set r : Fin n → ℝ := fun c => |(μ s + t - μ c) / (μ s - μ c)| with hr
  have hfac : ∀ a b : Fin n, a < b →
      |μ' a - μ' b| / |μ a - μ b| = (if a = s then r b else 1) * (if b = s then r a else 1) := by
    intro a b hab
    have hne : a ≠ b := ne_of_lt hab
    by_cases has : a = s
    · subst has
      have hbs : b ≠ a := fun h => hne h.symm
      rw [hμ'a, hμ'a, if_pos rfl, if_neg hbs, if_pos rfl, if_neg hbs]
      simp [hr, abs_div]
    · by_cases hbs : b = s
      · subst hbs
        rw [hμ'a, hμ'a, if_neg has, if_pos rfl, if_neg has, if_pos rfl]
        simp only [hr, one_mul, add_zero, abs_div]
        rw [abs_sub_comm (μ a) (μ b + t), abs_sub_comm (μ a) (μ b)]
      · rw [hμ'a, hμ'a, if_neg has, if_neg hbs, if_neg has, if_neg hbs]
        have h0 : μ a - μ b ≠ 0 := sub_ne_zero.2 (fun h => hne (hinj h))
        simp only [add_zero, mul_one]
        exact div_self (abs_ne_zero.2 h0)
  have hden : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ≠ 0 := by
    refine prod_ne_zero_iff.2 fun a _ => prod_ne_zero_iff.2 fun b hb => ?_
    have hab : a < b := (mem_filter.1 hb).2
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  unfold fdegHC
  rw [div_div_div_cancel_right₀ hden, ← prod_div_distrib]
  simp_rw [← prod_div_distrib]
  rw [prod_congr rfl (fun a _ => prod_congr rfl (fun b hb => hfac a b (mem_filter.1 hb).2))]
  simp_rw [prod_mul_distrib]
  have h1 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if a = s then r b else 1)) = ∏ b ∈ univ.filter (fun b : Fin n => s < b), r b := by
    rw [prod_eq_single s]
    · simp
    · intro a _ has; simp [has]
    · intro h; exact absurd (mem_univ s) h
  have h2 : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
      (if b = s then r a else 1)) = ∏ a ∈ univ.filter (fun a : Fin n => a < s), r a := by
    rw [prod_filter]
    refine prod_congr rfl fun a _ => ?_
    rw [prod_ite_eq']
    simp
  rw [h1, h2, ← prod_filter_mul_prod_filter_not (univ.erase s) (fun c => s < c)]
  congr 1
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega
  · congr 1; ext c
    simp only [mem_filter, mem_erase, mem_univ, and_true, true_and, ne_eq, Fin.lt_def, Fin.ext_iff]
    constructor <;> intro h <;> omega

end GlobalTheory.CompareIterDegree
end
end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FamilyDegreeRatio

theorem gap_lam {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ} {b bv ga h : ℝ} {q0 : ℕ}
    (H : Num k r lam u b bv ga h q0) (a c : Fin (2 * r + k + 1)) (hac : a < c) :
    100 * ((q0 : ℝ) + 1) ≤ lam a - lam c := by
  obtain ⟨hk, ⟨hanti, -⟩, -, -, -, hcl, hnd, -, -, hga, hh, -, hq1, hq2, -⟩ := H
  by_cases hc : c.val + 1 < k
  · linarith [hga a c hac hc]
  by_cases ha : a.val + 1 < k
  ·
    have hp : k - 1 < 2 * r + k + 1 := by omega
    have hq : k < 2 * r + k + 1 := by omega
    have hpq : PI.BesselPeriodGGP.eps48 k r ⟨k - 1, hp⟩ ≠ PI.BesselPeriodGGP.eps48 k r ⟨k, hq⟩ := by
      have h1 : ¬ (k < k - 1) := by omega
      have h2 : (k - (k - 1)) % 2 = 1 := by omega
      simp [PI.BesselPeriodGGP.eps48, h1, h2]
    have hgpq := hh _ _ hpq
    have ⟨p1, p2⟩ := hnd ⟨k - 1, hp⟩ (by show k ≤ k - 1 + 1; omega)
    have ⟨q1, q2⟩ := hnd ⟨k, hq⟩ (by show k ≤ k + 1; omega)
    have habs : |lam ⟨k - 1, hp⟩ - lam ⟨k, hq⟩| ≤ bv := abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 := (hcl a ha).1
    have h2 := (hnd c (by omega)).2
    linarith
  ·
    have hac' : a.val < c.val := hac
    have hd : a.val + 1 < 2 * r + k + 1 := by have := c.isLt; omega
    have had : a < ⟨a.val + 1, hd⟩ := by rw [Fin.lt_def]; simp
    have hdc : (⟨a.val + 1, hd⟩ : Fin (2 * r + k + 1)) ≤ c := by rw [Fin.le_iff_val_le_val]; simp; omega
    have hne : PI.BesselPeriodGGP.eps48 k r a ≠ PI.BesselPeriodGGP.eps48 k r ⟨a.val + 1, hd⟩ := by
      have h1 : ¬ (a.val < k - 1) := by omega
      have h2 : ¬ (a.val + 1 < k - 1) := by omega
      rcases Nat.mod_two_eq_zero_or_one (a.val - (k - 1)) with h3 | h3
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 1 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
      · have h4 : (a.val + 1 - (k - 1)) % 2 = 0 := by omega
        simp [PI.BesselPeriodGGP.eps48, h1, h2, h3, h4]
    have hg := hh _ _ hne
    have hlt := hanti had
    have hle := hanti.antitone hdc
    rw [abs_of_pos (by linarith)] at hg
    linarith

theorem abs_coord_le_of_lOneNorm_le {n : ℕ} {ν : Fin n → ℤ} {q : ℕ} (hν : n1 ν ≤ q) (a : Fin n) : |(ν a : ℝ)| ≤ q := by
  have h1 : (ν a).natAbs ≤ n1 ν :=
    Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
  have h2 : |(ν a : ℝ)| = ((ν a).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h2]
  exact_mod_cast h1.trans hν

theorem degree_ratios : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) ∧ (∀ I : Finset (Fin (2 * r + k + 1)), Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν + eZ I) a : ℝ)) ≤ ((2 * r + k + 1) : ℝ) ^ I.card * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ))) ∧ ∀ s, Formalism.QuantumDeterminants.fdegHC (fun a => lam a + ((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) / Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) = ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| / |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))| := by
  intro k r lam u b bv ga h q0 H ν hν
  have hgl := fun a c (hac : a < c) => gap_lam H a c hac
  have hνb := fun a => abs_le.mp (abs_coord_le_of_lOneNorm_le hν a)
  have hint := H.2.1.2
  have hq : (0 : ℝ) ≤ q0 := Nat.cast_nonneg _
  have hgap : ∀ a c : Fin (2 * r + k + 1), a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
    intro a c hac
    have := hgl a c hac
    have := hνb a
    have := hνb c
    linarith
  have hanti : StrictAnti (fun a => lam a + (ν a : ℝ)) := fun a c hac => by
    have := hgap a c hac
    simp only
    linarith
  have hinj := hanti.injective
  have hZ : ∀ a c, ∃ m : ℤ, (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) = (m : ℝ) := by
    intro a c
    obtain ⟨m1, hm1⟩ := hint a
    obtain ⟨m2, hm2⟩ := hint c
    exact ⟨m1 - m2 + ν a - ν c, by push_cast; linarith⟩
  have hpos : 0 < Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := Formalism.QuantumDeterminants.formal_degree_pos_holds _ _ hinj
  refine ⟨hpos, ?_, ?_⟩
  · intro I
    have hb := (Formalism.HermitianLatticeCounting.P.degree_set_cardinality_bound (2 * r + k + 1) (fun a => lam a + (ν a : ℝ)) I hanti hZ hgap).2
    have hfun : (fun a => lam a + (((ν + eZ I) a : ℤ) : ℝ)) =
        (fun a => (lam a + (ν a : ℝ)) + if a ∈ I then 1 else 0) := by
      funext a
      simp only [Pi.add_apply, eZ]
      split_ifs <;> push_cast <;> ring
    rw [hfun]
    rw [div_le_iff₀ hpos] at hb
    push_cast at hb
    exact hb
  · intro s
    have hfun : (fun a => lam a + (((ν - Pi.single s (1 : ℤ) : Fin (2 * r + k + 1) → ℤ) a : ℤ) : ℝ)) =
        (fun a => lam a + (ν a : ℝ)) + Pi.single s (-1 : ℝ) := by
      funext a
      by_cases has : a = s
      · subst has
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Int.cast_sub, Int.cast_one]
        ring
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne has, sub_zero, add_zero]
    rw [hfun, GlobalTheory.CompareIterDegree.fdeg_ratio_abs _ s (-1) hinj]
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [abs_div]
    congr 2

end GlobalTheory.FamilyDegreeRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNonneg
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselDecay

theorem gN_mul_le' {k r : ℕ} (a b : Mx k r) : B.gN (a * b) ≤ B.gN a * B.gN b := by
  exact PI.PolynomialProperness.GN.gN_mul_le a b

theorem gN_pos' {k r : ℕ} {a : Mx k r} (ha : a ∈ GG k r) : 0 < B.gN a := by
  exact PI.PolynomialProperness.GN.gN_pos ha

theorem sum_nonneg' {α : Type} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (L : List α) : 0 ≤ (L.map f).sum := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp ha
  exact hf w

theorem one_le_aOf {k r : ℕ} {h : ℝ} (hg : GapOK k r h) : 1 ≤ aOf r h := by
  have h4 := hg.2.2.2
  have : 0 ≤ AG k r := by unfold AG; positivity
  have : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem decay_TK : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → ∀ v ∈ R.TK, ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧ ∀ w ∈ R.sm, ∀ x ∈ GG k r, ‖⟪v, R.σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum * B.gN x ^ (1 - aOf r h) := by
  intro H k r ε mu h R hR hgap hok v hv
  have hdec : DecInf := H.1.2.1
  have ha := one_le_aOf hok
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, hg, v₀, hv₀, rfl⟩ := hv
    obtain ⟨C, Ws, hWs, hb⟩ := hdec k r ε mu h R.H R.σ hR.1 hR.2 hgap hok v₀ hv₀
    refine ⟨|C| * B.gN g ^ (aOf r h - 1), Ws, hWs, fun w hw x hx => ?_⟩
    obtain ⟨hi, hgi, hig⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    have hy : g⁻¹ * x ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hi hx
    have hx' : x = g * (g⁻¹ * x) := by rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
    have hunit := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2
    have hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
      (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 (hunit g hg)
    have e : ⟪R.σ g v₀, R.σ x w⟫_ℂ = ⟪v₀, R.σ (g⁻¹ * x) w⟫_ℂ := by
      rw [← hiso v₀]
      congr 1
      conv_lhs => rw [hx', Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hR.2 hg hy]
      rfl
    rw [e]
    have h1 := hb w hw _ hy
    set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS
    have hS0 : 0 ≤ S := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have pg := gN_pos' hg
    have px := gN_pos' hx
    have py := gN_pos' hy
    have hle : B.gN x ≤ B.gN g * B.gN (g⁻¹ * x) := by
      conv_lhs => rw [hx']
      exact gN_mul_le' _ _
    have h2 : (B.gN g * B.gN (g⁻¹ * x)) ^ (1 - aOf r h) ≤ B.gN x ^ (1 - aOf r h) :=
      Real.rpow_le_rpow_of_nonpos px hle (by linarith)
    rw [Real.mul_rpow pg.le py.le] at h2
    have h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1 := by
      rw [← Real.rpow_add pg]; simp
    have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos pg _
    have h4 : B.gN (g⁻¹ * x) ^ (1 - aOf r h) ≤ B.gN g ^ (aOf r h - 1) * B.gN x ^ (1 - aOf r h) := by
      calc B.gN (g⁻¹ * x) ^ (1 - aOf r h)
          = B.gN g ^ (aOf r h - 1) * (B.gN g ^ (1 - aOf r h) * B.gN (g⁻¹ * x) ^ (1 - aOf r h)) := by
            rw [← mul_assoc, h3, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 pg'.le
    calc _ ≤ C * S * B.gN (g⁻¹ * x) ^ (1 - aOf r h) := h1
      _ ≤ |C| * S * B.gN (g⁻¹ * x) ^ (1 - aOf r h) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)
            (Real.rpow_pos_of_pos py _).le
      _ ≤ |C| * S * (B.gN g ^ (aOf r h - 1) * B.gN x ^ (1 - aOf r h)) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg (abs_nonneg C) hS0)
      _ = _ := by ring
  | zero => exact ⟨0, [], by simp, fun w _ x _ => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨C, Ws, hWs, hb⟩ := hu
    obtain ⟨C', Ws', hWs', hb'⟩ := hv
    refine ⟨|C| + |C'|, Ws ++ Ws', fun W hW => (List.mem_append.1 hW).elim (hWs W) (hWs' W),
      fun w hw x hx => ?_⟩
    have h1 := hb w hw x hx
    have h2 := hb' w hw x hx
    rw [List.map_append, List.sum_append, inner_add_left]
    set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS
    set S' := (Ws'.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS'
    have hS0 : 0 ≤ S := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have hS0' : 0 ≤ S' := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have px : 0 ≤ B.gN x ^ (1 - aOf r h) := (Real.rpow_pos_of_pos (gN_pos' hx) _).le
    have h3 : C * S + C' * S' ≤ (|C| + |C'|) * (S + S') := by
      have a1 := mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      have a2 := mul_le_mul_of_nonneg_right (le_abs_self C') hS0'
      have a3 := mul_nonneg (abs_nonneg C) hS0'
      have a4 := mul_nonneg (abs_nonneg C') hS0
      nlinarith
    calc _ ≤ ‖⟪u, R.σ x w⟫_ℂ‖ + ‖⟪v, R.σ x w⟫_ℂ‖ := norm_add_le _ _
      _ ≤ (C * S + C' * S') * B.gN x ^ (1 - aOf r h) := by rw [add_mul]; exact add_le_add h1 h2
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 px
  | smul c v _ hv =>
    obtain ⟨C, Ws, hWs, hb⟩ := hv
    refine ⟨‖c‖ * C, Ws, hWs, fun w hw x hx => ?_⟩
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc, mul_assoc, ← mul_assoc C]
    exact mul_le_mul_of_nonneg_left (hb w hw x hx) (norm_nonneg c)

end GlobalTheory.BesselDecay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLe
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLe
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomNum

theorem mom_num : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (T : ℝ), Num k r lam u b bv ga h q0 → 0 < T → (((2 * r + k + 1) : ℝ) ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * (b ^ 2) ^ (2 * r) ≤ Hsq r T b := by
  intro k r lam u b bv ga h q0 T hN hT
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩ := hN
  have ha := (h7 ⟨k, by omega⟩ (by simp)).2
  have hb := (abs_le.mp (h8 ⟨k, by omega⟩)).1
  have hbv : bv ≤ b := by linarith
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hn7 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ hn1 (by norm_num)
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = ((2 * r + k + 1) : ℝ) := by push_cast; ring
  rw [hcast] at hn1 hn7 h15
  set n : ℝ := (2 * r + k + 1 : ℝ) with hn
  have hnb : n ≤ b := by linarith
  have hbv6 : 6 ≤ bv := by linarith
  have hb6 : 6 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have h6 : 6 * bv ≤ b ^ 2 := by nlinarith
  have hb0 : 0 ≤ b := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hbv0 : 0 ≤ 6 * bv := by linarith
  have hTm : T ≤ max 1 T := le_max_right _ _
  have hm0 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
  unfold Hsq
  calc n ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2)) * (b ^ 2) ^ (2 * r)
      ≤ b ^ 2 * (max 1 T * b ^ 4) * (b ^ 2) ^ (2 * (2 * r + 2)) * (b ^ 2) ^ (2 * r) := by
        gcongr
    _ = max 1 T * b ^ (12 * r + 14) := by ring
    _ ≤ max 1 T * b ^ (20 * (r + 1)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by omega)) hm0

end GlobalTheory.MomNum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLeStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numericalFamily_productBound_constant_le : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (T : ℝ), Num k r lam u b bv ga h q0 → 0 < T → (((2 * r + k + 1) : ℝ) ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * (b ^ 2) ^ (2 * r) ≤ Hsq r T b := by
  first | exact @GlobalTheory.MomNum.mom_num | exact GlobalTheory.MomNum.mom_num | (intros; apply GlobalTheory.MomNum.mom_num <;> assumption)
end
end
