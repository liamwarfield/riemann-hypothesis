module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LamIsoOfDoublingPullbackEqDiagonalSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidue
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDerivAt0CompLinearIff
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.PullbackSections
noncomputable section

namespace GlobalTheory.ThetaWitness

theorem isDerivAt0_comp_linear_iff {g g' : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (he : IsHolTo Set.univ e) (L : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin g' → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 →
      ∀ (U : X.Opens) (_ : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := by
    intro h0 U hU f
    have hmem : (0 : Fin g → ℂ) ∈ {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ e b ⁻¹ᵁ U} := by
      refine ⟨trivial, ?_⟩
      rw [← h0]
      intro x _
      exact hU (Set.mem_univ _)
    have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) 0 :=
      ((he U f).2 0 hmem).differentiableAt ((he U f).1.mem_nhds hmem)
    let L' := LinearMap.toContinuousLinearMap L
    have hd' : HasFDerivAt (fun z => valAt' (e z) U f) (fderiv ℂ (fun z => valAt' (e z) U f) 0) (L' 0) := by
      rw [map_zero]; exact hd.hasFDerivAt
    have := (hd'.comp (0 : Fin g' → ℂ) L'.hasFDerivAt).fderiv
    exact DFunLike.congr_fun this w
  unfold IsDerivAt0
  simp only [map_zero]
  exact and_congr_right fun h0 => forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => by
    rw [key h0 U hU f]

theorem ex_eq_of_der {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {t : SAB H S}
    {y₁ y₂ : Sp ℂ ⟶ S} (hy : y₁ = y₂) {D : Datum H} {g₁ g₂ : ℕ} {ty : Fin g₁ → (E →+* ℂ)}
    {P : D.La →+ (Fin g₁ → ℂ)} (hP : IsPeriod D ty P) {e₁ : (Fin g₁ → ℂ) → (Over.mk y₁ ⟶ t.G)}
    (he₁ : GlobalTheory.UnifPoint.IsExp e₁) (hk₁ : ∀ z, e₁ z = 1 ↔ z ∈ P.range)
    {e₂ : (Fin g₂ → ℂ) → (Over.mk y₂ ⟶ t.G)} (he₂ : GlobalTheory.UnifPoint.IsExp e₂) (hc₂ : {z | e₂ z = 1}.Countable)
    (L : (Fin g₁ → ℂ) ≃ₗ[ℂ] (Fin g₂ → ℂ))
    (huniq : ∀ w w' v, IsDerivAt0 (fun z => (e₁ z).left) w v → IsDerivAt0 (fun z => (e₁ z).left) w' v → w = w')
    (hb : ∀ a, ∃ v, IsDerivAt0 (fun z => (e₁ z).left) (Pi.single a 1) v ∧
      IsDerivAt0 (fun z => (e₂ z).left) (L (Pi.single a 1)) v) :
    ∀ z, (e₁ z).left = (e₂ (L z)).left := by
  subst hy
  have hL : Continuous L := L.toLinearMap.continuous_of_finiteDimensional
  have hLd : Differentiable ℂ L := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hhol : IsHolTo Set.univ (fun z => (e₂ (L z)).left) := fun U f => by
    obtain ⟨h1, h2⟩ := he₂.2.2.1 U f
    refine ⟨?_, ?_⟩
    · exact h1.preimage hL
    · refine h2.comp hLd.differentiableOn ?_
      intro z hz; exact ⟨trivial, hz.2⟩
  obtain ⟨h, hh⟩ := GlobalTheory.UnifPoint.exists_linearEquiv_of_period hP he₁ hk₁ (e₀ := fun z => e₂ (L z))
    (fun z w => by simp only [map_add (f := _)]; exact he₂.1 _ _) (he₂.2.1.comp L.surjective) hhol
    (by
      refine (hc₂.preimage_of_injOn L.injective.injOn).mono ?_
      intro z hz; exact hz)
  have hid : ∀ a, h (Pi.single a 1) = Pi.single a 1 := fun a => by
    obtain ⟨v, h1, h2⟩ := hb a
    have d2 := (isDerivAt0_comp_linear_iff _ he₂.2.2.1 L.toLinearMap _ v).2 h2
    have d3 : IsDerivAt0 (fun z => (e₁ (h z)).left) (Pi.single a 1) v := by
      convert d2 using 2 with z
      rw [hh]; rfl
    have d4 := (isDerivAt0_comp_linear_iff _ he₁.2.2.1 h.toLinearMap _ v).1 d3
    exact huniq _ _ v d4 h1
  have hlin : h.toLinearMap = LinearMap.id :=
    LinearMap.pi_ext' fun a => LinearMap.ext_ring (by simpa using hid a)
  have hid' : ∀ z, h z = z := fun z => LinearMap.congr_fun hlin z
  intro z
  rw [← hh z, hid']

end GlobalTheory.ThetaWitness

namespace GlobalTheory.ThetaWitness

theorem theta_value_indep : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W₁ W₂ : UnfAt U k x)
    (Y₁ : UnitAt W₁) (Y₂ : UnitAt W₂) (v : Fin r → E),
    Complex.exp (-(Real.pi / 2 * hermForm Y₁.Hm (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2)
        (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2))) *
        Y₁.θ (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) =
      Complex.exp (-(Real.pi / 2 * hermForm Y₂.Hm (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2)
        (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2))) *
        Y₂.θ (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W₁ W₂ Y₁ Y₂ v
  let L : (Fin W₁.g → ℂ) ≃ₗ[ℂ] (Fin W₂.g → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ (W₂.e.trans W₁.e.symm)
  have hL : ∀ z j, L z j = z (W₁.e.symm (W₂.e j)) := fun z j => rfl
  have hLd : Differentiable ℂ L := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hp : (fun j => perFr (U.X k) x.1 v (relab c σ (W₂.e j).1) (W₂.e j).2) =
      L (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) := by
    funext j
    rw [hL]
    generalize hs : W₁.e (W₁.e.symm (W₂.e j)) = s
    rw [Equiv.apply_symm_apply] at hs
    subst hs; rfl
  rw [hp]
  generalize (fun j => perFr (U.X k) x.1 v (relab c σ (W₁.e j).1) (W₁.e j).2) = z

  have hPL : ∀ a, L (W₁.Pm a) = W₂.Pm ((W₂.φ k).symm (W₁.φ k a)) := fun a => by
    funext j
    rw [hL, W₁.pm_eq, W₂.pm_eq, LinearEquiv.apply_symm_apply]
    generalize hs : W₁.e (W₁.e.symm (W₂.e j)) = s
    rw [Equiv.apply_symm_apply] at hs
    subst hs; rfl
  have hEF : ∀ a b, (W₂.F.Di (W₂.ik k)).EF ((W₂.φ k).symm (W₁.φ k a)) ((W₂.φ k).symm (W₁.φ k b)) =
      (W₁.F.Di (W₁.ik k)).EF a b := fun a b => by
    have h1 := W₂.isom k ((W₂.φ k).symm (W₁.φ k a)) ((W₂.φ k).symm (W₁.φ k b))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← W₁.isom k a b] at h1
    exact_mod_cast h1

  have hspan : Submodule.span ℝ (Set.range W₁.Pm) = ⊤ := W₁.per.2.2.2.1
  have hHH : ∀ z w, hermForm Y₂.Hm (L z) (L w) = hermForm Y₁.Hm z w := fun z w => by
    have := GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im Y₂.Hm L.toLinearMap Y₁.Hm LinearMap.id hspan (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp only [LinearEquiv.coe_coe, LinearMap.id_coe, id_eq]
      rw [hPL, hPL, Y₂.c1, Y₁.c1, hEF]) z w
    simpa using this

  have hexp : ∀ W : UnfAt U k x, GlobalTheory.UnifPoint.IsExp (W.F.ex (W.ik k) W.Pm) := fun W =>
    ⟨W.F.ex_add _ _ W.per, W.F.ex_onto _ _ W.per, GlobalTheory.ClassUniq.isHolTo_ex W.F _ _ W.per,
      (W.F.ex_diff _ _ W.per).1, (W.F.ex_diff _ _ W.per).2⟩
  have hLs : ∀ a, L (Pi.single a 1) = Pi.single (W₂.e.symm (W₁.e a)) 1 := fun a => by
    funext j
    rw [hL]
    simp only [Pi.single_apply]
    exact if_congr (by rw [Equiv.symm_apply_eq, Equiv.eq_symm_apply]) rfl rfl
  have hex : ∀ z, (W₁.F.ex (W₁.ik k) W₁.Pm z).left = (W₂.F.ex (W₂.ik k) W₂.Pm (L z)).left :=
    ex_eq_of_der (t := Xo.univ.t) (W₁.pt.symm.trans W₂.pt) W₁.per (hexp W₁) (W₁.F.ex_ker _ _ W₁.per) (hexp W₂)
      ((GlobalTheory.UnifPoint.countable_periods W₂.per).mono fun z hz => (W₂.F.ex_ker _ _ W₂.per z).1 hz) L
      (fun w w' v h h' => by
        have tn := GlobalTheory.isDerivAt0_ex_isTanAt _ _ _ _ Xo _ _ _ W₁.F (W₁.ik k) W₁.Pm W₁.per
        exact (tn.2.2 v (tn.1 w v h)).unique h h')
      (fun a => ⟨(U.un k x).u (W₁.e a).1 (W₁.e a).2, by simpa using W₁.der (W₁.e a).1 (W₁.e a).2, by
        rw [hLs]; simpa using W₂.der (W₁.e a).1 (W₁.e a).2⟩)

  have hper1 : ∀ a ∈ W₁.Pm.range, ∀ z, W₁.F.ex (W₁.ik k) W₁.Pm (z + a) = W₁.F.ex (W₁.ik k) W₁.Pm z :=
    fun a ha z => by
      rw [W₁.F.ex_add _ _ W₁.per, (W₁.F.ex_ker _ _ W₁.per a).2 ha]
      exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hcov : ∀ z, ∃ j, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z =>
    GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB _
  have tr : ∀ j z, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ (W₂.F.ex (W₂.ik k) W₂.Pm (L z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by rw [← hex]; exact hz
  have hspan' : Submodule.span ℝ (W₁.Pm.range : Set (Fin W₁.g → ℂ)) = ⊤ := by
    rw [AddMonoidHom.coe_range]; exact hspan
  have hfr : ∀ j z, ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Y₂.fr j (L z) = Y₁.fr j z :=
    GlobalTheory.UnitFrameGen.frames_eq W₁.Pm.range hspan' (fun j => {z | ⊤ ≤ (W₁.F.ex (W₁.ik k) W₁.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
      (fun j => GlobalTheory.FamilyUnif_isOpen_ex W₁.F _ _ W₁.per _) hcov
      (fun j a ha z hz => by rw [Set.mem_setOf_eq, hper1 a ha]; exact hz)
      Y₁.fr (fun j z => Y₂.fr j (L z))
      (fun j j' z => valAt' (W₁.F.ex (W₁.ik k) W₁.Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val)
      (fun a z => Real.exp (Real.pi * (hermForm Y₁.Hm z a).re + Real.pi / 2 * (hermForm Y₁.Hm a a).re))
      Y₁.c2 (fun j => (Y₂.c2 j).comp hLd.differentiableOn fun z hz => tr j z hz) Y₁.c3
      (fun j j' z h1 h2 => Y₁.c4 j j' z ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨h1, h2⟩))
      (fun j j' z h1 h2 => by
        have e2 := Y₂.c4 j j' (L z) ((GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨tr _ _ h1, tr _ _ h2⟩)
        rw [← hex] at e2
        exact e2)
      (fun j hz => by
        have t0 := tr j 0 hz
        simp only [map_zero] at t0 ⊢
        rw [Y₁.c5 j hz, Y₂.c5 j t0])
      (by
        rintro j _ ⟨a, rfl⟩ z hz
        exact GlobalTheory.UnitFrameGen.norm_factor Y₁.Hm _ _ _ _ _ (Y₁.c6 a j z).1 ((Y₁.c6 a j z).2 hz))
      (by
        rintro j _ ⟨a, rfl⟩ z hz
        have := GlobalTheory.UnitFrameGen.norm_factor Y₂.Hm _ _ _ _ _ (Y₂.c6 ((W₂.φ k).symm (W₁.φ k a)) j (L z)).1
          ((Y₂.c6 ((W₂.φ k).symm (W₁.φ k a)) j (L z)).2 (tr j z hz))
        rw [← hPL, hHH, hHH, ← map_add (f := _)] at this
        exact this)

  have hθ : Y₂.θ (L z) = Y₁.θ z := by
    obtain ⟨j, hj⟩ := hcov z
    have hw0 : (W₁.F.ex (W₁.ik k) W₁.Pm z).left ≫ Xo.univ.t.G.hom = (U.un k x).x :=
      (Over.w (W₁.F.ex (W₁.ik k) W₁.Pm z)).trans W₁.pt.symm
    let p : Over.mk (U.un k x).x ⟶ Xo.univ.t.G := Over.homMk (W₁.F.ex (W₁.ik k) W₁.Pm z).left hw0
    have e1 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 _) p)
    have e2 := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 _) p)
    have v1 := Y₁.c7 j z _ e1 e2 hj
    have v2 := Y₂.c7 j (L z) _ (e1.trans (hex z)) e2 (tr j z hj)
    rw [hfr j z hj] at v2
    exact mul_right_cancel₀ (Y₁.c3 j z hj) (v2.symm.trans v1)
  rw [hHH, hθ]

end GlobalTheory.ThetaWitness
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionRealPlaceFockVacuaScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionRealPlaceFockVacuaScalar
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCompress

open GlobalTheory.WeilVacMove

theorem gauss_ode (c : ℝ → ℂ) (a : ℂ) (h : ∀ s : ℝ, HasDerivAt c ((s : ℂ) * a * c s) s) :
    c 1 = Complex.exp (a / 2) * c 0 := by
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(a * ((t : ℂ) * (t : ℂ)) / 2)) * c t) 0 s := by
    intro s
    have e1 : HasDerivAt (fun x : ℂ => -(a * (x * x) / 2)) (-(a * (1 * (s : ℂ) + (s : ℂ) * 1) / 2)) (s : ℂ) :=
      ((((hasDerivAt_id (s : ℂ)).mul (hasDerivAt_id (s : ℂ))).const_mul a).div_const 2).neg
    have e3 := (e1.cexp.comp_ofReal).mul (h s)
    exact e3.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (key s).differentiableAt) (fun s => (key s).deriv) 1 0
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_div, neg_zero,
    Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add]
  simp

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem wAt_eq_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (w : Mx D m n) :
    wAt (.inr τ) w = lineAt θ τ (compAt θ τ w) 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  obtain ⟨-, -, -, -, hfi, -, hth⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  ext i j
  rw [← sub_eq_zero]
  apply hσ.ext
  · have h1 : finPart D (lineAt θ τ (compAt θ τ w) 1 i j) = 0 := by
      have := congrFun (congrFun (hfin 1) i) j
      simpa only [Matrix.map_apply, Matrix.zero_apply] using this
    simp [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, hfi τ, h1]
  · intro τ'
    have h2 := congrFun (congrFun (hcomp 1 τ') i) j
    by_cases hτ : τ' = τ
    · subst hτ
      rw [if_pos rfl, Complex.ofReal_one, one_smul] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ' (compAt θ τ' w) 1 i j)) = θ τ' (infPart D (w i j)) := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, (hth θ hθ τ').1, one_mul, h2']
      exact sub_self _
    · have h3 := (hth θ hθ τ').2 τ (Ne.symm hτ)
      rw [if_neg hτ] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ (compAt θ τ w) 1 i j)) = 0 := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, h3, zero_mul, zero_sub, neg_eq_zero, h2']

theorem dLine_heisO (hψ : IsStdChar D ψ (-1)) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (v : WO S T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    dLine ψ S T L (heisO ψ S T v f) x =
      -2 * phase lam S T (L 1) v * heisO ψ S T v f x + ψ (symplOH S T x v) * dLine ψ S T L f (x + v) := by
  have hG : (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) =
      fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        heisO ψ S T (L t) f (x + v) := by
    funext t
    have e1 := GlobalTheory.WeilVacMove.psi_sympl_line hl hlam hL hL0 v t
    have hX : Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) =
        (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ * (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      ring
    have hE := Complex.exp_ne_zero ((t : ℂ) * phase lam S T (L 1) v)
    show ψ (symplOH S T x (L t)) * (ψ (symplOH S T (x + L t) v) * f (x + L t + v)) =
      ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        (ψ (symplOH S T (x + v) (L t)) * f (x + v + L t))
    rw [GlobalTheory.WeilVacMove.symplOH_add_left, GlobalTheory.WeilVacMove.symplOH_add_left,
      GlobalTheory.WeilVacMove.symplOH_skew S T v (L t), AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, e1, add_right_comm x (L t) v, hX]
    field_simp
  have hH := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hL hL0 hf).1 (x + v)
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)))
      (Complex.exp (((0 : ℝ) : ℂ) * (-2 * phase lam S T (L 1) v)) * (1 * (-2 * phase lam S T (L 1) v))) 0 :=
    (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const _).cexp).comp_ofReal
  have hD := (hexp.const_mul (ψ (symplOH S T x v))).mul hH
  show deriv (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) 0 = _
  have hD' : HasDerivAt (fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
      heisO ψ S T (L t) f (x + v)) _ 0 := hD
  rw [hG, hD'.deriv]
  have hv : heisO ψ S T v f x = ψ (symplOH S T x v) * f (x + v) := rfl
  rw [hv, map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  ring

private theorem flow_lemma {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) (τ : D.what₂.Tau)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (hvf : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f)
    (hvg : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g) :
    ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z 1) f) g =
      Complex.exp (-(phase lam S T (lineAt θ τ z 1) (lineAt θ τ z 1) +
        Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * z * sS)) 1) (lineAt θ τ z 1)) / 2) *
        ipO μ 𝓕 f g := by
  have U := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  set J := Complex.I • (sT * z * sS) with hJ
  obtain ⟨hLc, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨hLc', hL0', -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ J
  set L := lineAt θ τ z with hLeq
  set L' := lineAt θ τ J with hLJeq
  set Dz := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z with hDz
  set DJ := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ J with hDJ
  have vf : Dz f + Complex.I • DJ f = 0 := hvf z
  have vg : Dz g + Complex.I • DJ g = 0 := hvg z
  have hp : ∀ (u : WO S T) (s : ℝ), phase lam S T u (L s) = (s : ℂ) * phase lam S T u (L 1) := by
    intro u s
    have hc : Continuous ((phase lam S T u).comp L) :=
      hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hLc continuous_const)
    exact GlobalTheory.WeilVacMove.additive_real _ hc s
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L t) f) g)
      ((s : ℂ) * -(phase lam S T (L 1) (L 1) + Complex.I * phase lam S T (L' 1) (L 1)) *
        ipO μ 𝓕 (heisO ψ S T (L s) f) g) s := by
    intro s
    set h := heisO ψ S T (L s) f with hheq
    have hh : IsThetaFunO ψ S T h := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 s) hf
    obtain ⟨hder, hXs⟩ := GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ z
    have hYs := (GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ J).2
    have h0 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g) (ipO μ 𝓕 (Dz h) g) (s - s) := by
      rw [sub_self]
      refine hder.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      show ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g = ipO μ 𝓕 (heisO ψ S T (L t) h) g
      rw [hheq, GlobalTheory.WeilVacMove.heisO_line_add hψ hLc hL0 t s f]
    have hd := (h0.comp_sub_const s s)
    simp only [sub_add_cancel] at hd
    refine hd.congr_deriv ?_
    have hDzh := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hh
    have hDJh : IsThetaFunO ψ S T (DJ h) := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hh
    have hDJg := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hg
    have cA : Dz h + Complex.I • DJ h =
        (-2 * (phase lam S T (L 1) (L s) + Complex.I * phase lam S T (L' 1) (L s))) • h := by
      funext x
      have c1 : Dz h x = -2 * phase lam S T (L 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * Dz f (x + L s) := dLine_heisO hψ hl hlam hLc hL0 (L s) hf x
      have c2 : DJ h x = -2 * phase lam S T (L' 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * DJ f (x + L s) := dLine_heisO hψ hl hlam hLc' hL0' (L s) hf x
      have c3 := congrFun vf (x + L s)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at c3 ⊢
      rw [c1, c2]
      linear_combination ψ (symplOH S T x (L s)) * c3
    have e3 : ipO μ 𝓕 h (Dz g) = Complex.I * ipO μ 𝓕 h (DJ g) := by
      have hz : Dz g = (-Complex.I) • DJ g := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left vg
      rw [hz, ((U h (DJ g) hh hDJg).2.2.1 (-Complex.I)).2]
      simp [Complex.conj_I]
    have e4 : ipO μ 𝓕 (Dz h + Complex.I • DJ h) g = ipO μ 𝓕 (Dz h) g + Complex.I * ipO μ 𝓕 (DJ h) g := by
      have hsmul : IsThetaFunO ψ S T (Complex.I • DJ h) := by
        refine { quasi := ?_, level := ?_, cont := ?_, smooth := ?_ }
        · intro γ w
          rw [Pi.smul_apply, Pi.smul_apply, hDJh.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        · obtain ⟨U, hU, h1⟩ := hDJh.level
          refine ⟨U, hU, fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu h0) w
          change ψ (symplOH S T w u) * DJ h (w + u) = DJ h w at e1
          unfold heisO
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
        · exact hDJh.cont.const_smul Complex.I
        · intro k L h1 h2 w
          exact contDiff_const.mul (hDJh.smooth k L h1 h2 w)
      rw [((U (Dz h) g hDzh hg).2.2.2.1 _ hsmul).1,
        ((U (DJ h) g hDJh hg).2.2.1 Complex.I).1]
    rw [cA, ((U h g hh hg).2.2.1 _).1, hp (L 1) s, hp (L' 1) s] at e4
    linear_combination (-1 / 2 : ℂ) * e4 + (1 / 2 : ℂ) * hXs - (Complex.I / 2) * hYs - (1 / 2 : ℂ) * e3
  have hfin := gauss_ode _ _ key
  simp only [map_zero, GlobalTheory.WeilVacMove.heisO_zero] at hfin
  exact hfin

theorem compress : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ), IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT → ∀ w : WO S T, ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inr τ) w) f) = γ * ipO μ 𝓕 g f := by
  intro D ψ θ S T μ 𝓕 hψ hθ hμ τ sS sT _ _ w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  refine ⟨starRingEnd ℂ (Complex.exp (-(phase lam S T (lineAt θ τ (compAt θ τ w) 1) (lineAt θ τ (compAt θ τ w) 1) +
      Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * compAt θ τ w * sS)) 1)
        (lineAt θ τ (compAt θ τ w) 1)) / 2)), ?_⟩
  intro f g hf hg hvf hvg
  have U := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  obtain ⟨-, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  have h1 := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 1) hf
  rw [wAt_eq_lineAt hθ τ w, (U _ g h1 hg).2.1, (U f g hf hg).2.1,
    flow_lemma hψ hθ hμ hl hlam τ sS sT (compAt θ τ w) hf hg hvf hvg, map_mul]

end GlobalTheory.VacCompress

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionRealPlaceFockVacuaScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_compression_real_place_fock_vacua_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ), IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT → ∀ w : WO S T, ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inr τ) w) f) = γ * ipO μ 𝓕 g f := by
  first | exact @GlobalTheory.VacCompress.compress | exact GlobalTheory.VacCompress.compress | (intros; apply GlobalTheory.VacCompress.compress <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KMeanMemKFinOfCoefFam
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift


open Formalism.REAL in
theorem kMean_translate {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {n : ℕ}
    (c : Fin n → KG (M.ε τ) → ℂ) (hc : IsCoefFam c) (w : M.H τ) (i : Fin n) (k₀ : KG (M.ε τ)) :
    ∃ d : Fin n → ℂ, M.σ τ (toMK k₀) (kMean M τ (c i) w) = ∑ j, d j • kMean M τ (c j) w := by
  have hds := M.ds τ
  have : CompleteSpace (M.H τ) := hds.1
  obtain ⟨⟨-, hmul⟩, -, hcont⟩ := hds.2.2.1
  have hmem : ∀ k : KG (M.ε τ), toMK k ∈ Formalism.MainNotions.S.UJset (M.ε τ) := fun k => (k : UJ (M.ε τ)).2
  have hcK : Continuous fun k : KG (M.ε τ) => M.σ τ (toMK k) w :=
    (hcont w).comp_continuous (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)) hmem
  have hint : ∀ j, Integrable (fun k => c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j =>
    ((hc.1 j).smul hcK).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have hm : ∀ k : KG (M.ε τ), M.σ τ (toMK (k₀ * k)) = (M.σ τ (toMK k₀)).comp (M.σ τ (toMK k)) :=
    fun k => hmul _ (hmem k₀) _ (hmem k)
  obtain ⟨d, hd⟩ := hc.2 k₀⁻¹ i
  refine ⟨d, ?_⟩
  unfold kMean
  calc M.σ τ (toMK k₀) (∫ k, c i k • M.σ τ (toMK k) w ∂muK (M.ε τ))
      = ∫ k, M.σ τ (toMK k₀) (c i k • M.σ τ (toMK k) w) ∂muK (M.ε τ) :=
        (ContinuousLinearMap.integral_comp_comm _ (hint i)).symm
    _ = ∫ k, (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) (k₀ * k) ∂muK (M.ε τ) := by
        congr 1
        funext k
        simp only [map_smul, inv_mul_cancel_left]
        rw [hm]
        rfl
    _ = ∫ k, c i (k₀⁻¹ * k) • M.σ τ (toMK k) w ∂muK (M.ε τ) :=
        integral_mul_left_eq_self (μ := muK (M.ε τ)) (fun x => c i (k₀⁻¹ * x) • M.σ τ (toMK x) w) k₀
    _ = ∑ j, d j • ∫ k, c j k • M.σ τ (toMK k) w ∂muK (M.ε τ) := by
        simp only [hd, Finset.sum_smul, mul_smul]
        have hs : ∀ j ∈ (Finset.univ : Finset (Fin n)),
            Integrable (fun k => d j • c j k • M.σ τ (toMK k) w) (muK (M.ε τ)) := fun j _ => (hint j).smul (d j)
        rw [integral_finsetSum _ hs]
        simp only [integral_smul]

theorem kMean_mem_kFin_of_coefFam : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (n : ℕ) (c : Fin n → Formalism.REAL.KG (M.ε τ) → ℂ), IsCoefFam c → ∀ (w : M.H τ) (i : Fin n),
    kMean M τ (c i) w ∈ kFin M τ := by
  intro D V S M τ n c hc w i
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin
  rw [GlobalTheory.KFiniteVectors.mem_kFiniteVectors]
  refine ⟨Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w),
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _), Submodule.subset_span ⟨i, rfl⟩, ?_⟩
  intro g hg x hx
  rw [← Formalism.REAL.range_toMK] at hg
  obtain ⟨k₀, rfl⟩ := hg
  have hle : Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w) ≤
      (Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)).comap
        (M.σ τ (Formalism.REAL.toMK k₀) : M.H τ →ₗ[ℂ] M.H τ) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd⟩ := kMean_translate M τ c hc w j k₀
    change M.σ τ (Formalism.REAL.toMK k₀) (kMean M τ (c j) w) ∈ Submodule.span ℂ (Set.range fun j => kMean M τ (c j) w)
    rw [hd]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  exact hle hx

end GlobalTheory.Chain.IoLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKerOfCoverKer
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.KerTransfer

theorem locKer_of_coverKer (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ → R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (ha : IsKAct M' τ a') (hC : CoverKer p q R₂.HK) :
    LocKer M M' τ aS aT a' := by
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm (R₂.ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : R₂.HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm (R₂.ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = R₂.ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  have key : ∀ (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
      (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z), IsLocPair M M' τ aS aT a' B →
      ∃ B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z, IsCoverPair R₂.HK B' ∧
        ∀ P v, B' (κ P) v = B P (j v) := by
    intro Z _ _ B hB
    let B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z :=
      { toFun := fun P => (B (κ.symm P)).comp j
        map_add' := fun P Q => by ext v; simp
        map_smul' := fun c P => by ext v; simp }
    have hB' : ∀ P v, B' (κ P) v = B P (j v) := fun P v => by simp [B']
    refine ⟨B', ⟨fun X hX P P' y y' => ?_, fun Y hY P y => ?_⟩, hB'⟩
    · obtain ⟨P, rfl⟩ := κ.surjective P
      obtain ⟨P', rfl⟩ := κ.surjective P'
      have hX' : toFrame M τ (barMat e X) ∈ lieAt V τ := h₁.lie ▸ ⟨X, hX, rfl⟩
      have h3 : (barMat e X).map (starRingEnd ℂ) = Matrix.reindex e e X := by ext a b; simp [barMat]
      have h4 : (barMat e X).trace = -X.trace := by
        rw [barMat, trace_reindex', ← trace_conj hX]
        simp [Matrix.trace]
      have h := hB.skew _ hX' P P' (j y) (j y')
      simp only [sOp, fr_toFrame, trace_toFrame, h3, h4, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, map_neg, map_mul, map_ratCast, trace_conj hX] at h
      rw [← hκ.1, ← hκ.1, hB', hB', hB', hB']
      linear_combination h
    · obtain ⟨P, rfl⟩ := κ.surjective P
      have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
      have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
      have h5 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j (R₂.HK.act Y y) - ((aS : ℂ) * Y.trace) • j y := by
        have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
            j (R₂.HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
          refine Subtype.ext (U'.injective ?_)
          rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
        rw [h6, map_add (f := _), LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
          sub_eq_add_neg, ← neg_smul]
        congr 2
        ring
      have h := hB.inv _ hY' P (j y)
      rw [h5, tOp, fr_toFrame, trace_toFrame, h4] at h
      rw [← hκ.2, hB', hB', ← h]
      simp [plainMat]
  intro Z₁ Z₂ _ _ _ _ B₁ B₂ hB₁ hB₂ hne n a b hs
  obtain ⟨C₁, hC₁, e₁⟩ := key Z₁ B₁ hB₁
  obtain ⟨C₂, hC₂, e₂⟩ := key Z₂ B₂ hB₂
  choose g hg using hsurj
  have hne' : C₁ ≠ 0 := fun h0 => hne (LinearMap.ext fun P => LinearMap.ext fun y => by
    rw [← hg y, ← e₁, h0]; rfl)
  have h := hC Z₁ Z₂ C₁ C₂ hC₁ hC₂ hne' n (fun i => κ (a i)) (fun i => g (b i)) (by simpa [e₁, hg] using hs)
  simpa [e₂, hg] using h

end GlobalTheory.Chain.IoLift.KerTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfContr
noncomputable section

open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift.TensorFormProof

open GlobalTheory.Chain.IoLift

variable {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]

theorem contr_tmul (ι : V →ₗ[ℂ] H) (y : V) (a : A) (v : V) :
    contr ι y (a ⊗ₜ[ℂ] v) = ⟪ι y, ι v⟫_ℂ • a := by
  unfold contr
  rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.comp_apply, innerₛₗ_apply_apply]
  exact TensorProduct.rid_tmul _ _

theorem dual_contr (ι : V →ₗ[ℂ] H) (y : V) (l : A →ₗ[ℂ] ℂ) (t : A ⊗[ℂ] V) :
    l (contr ι y t) = ⟪ι y, ι (TensorProduct.lid ℂ V (LinearMap.rTensor V l t))⟫_ℂ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [contr_tmul, map_smul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, inner_smul_right,
      smul_eq_mul, mul_comm]
  | add s u hs hu => simp only [map_add (f := _), inner_add_right, hs, hu]

theorem eq_zero_of_contr (ι : V →ₗ[ℂ] H) (hι : Function.Injective ι) (t : A ⊗[ℂ] V)
    (h : ∀ y, contr ι y t = 0) : t = 0 := by

  have hl : ∀ l : A →ₗ[ℂ] ℂ, LinearMap.rTensor V l t = 0 := by
    intro l
    set w := TensorProduct.lid ℂ V (LinearMap.rTensor V l t) with hw
    have h0 : ⟪ι w, ι w⟫_ℂ = 0 := by
      have := dual_contr ι w l t
      rw [h w, map_zero] at this
      exact this.symm
    have hw0 : w = 0 := hι ((inner_self_eq_zero.mp h0).trans (map_zero ι).symm)
    rw [hw] at hw0
    exact (LinearEquiv.map_eq_zero_iff _).mp hw0

  let e := (Module.Basis.ofVectorSpace ℂ A).repr
  have hs : TensorProduct.finsuppScalarLeft ℂ V _ (LinearMap.rTensor V e.toLinearMap t) = 0 := by
    ext i
    rw [TensorProduct.finsuppScalarLeft_apply, ← LinearMap.rTensor_comp_apply, hl, map_zero]
    rfl
  have h2 : LinearMap.rTensor V e.toLinearMap t = 0 := (LinearEquiv.map_eq_zero_iff _).mp hs
  have h3 := congrArg (LinearMap.rTensor V e.symm.toLinearMap) h2
  rwa [← LinearMap.rTensor_comp_apply, LinearEquiv.symm_comp, LinearMap.rTensor_id_apply, map_zero] at h3

theorem exists_tensor (ι : V →ₗ[ℂ] H) (β : V →ₛₗ[starRingEnd ℂ] A) (E : Submodule ℂ V) [FiniteDimensional ℂ E]
    (h : ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → β y = 0) : ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = β y := by

  set F : Submodule ℂ H := E.map ι with hF
  haveI : FiniteDimensional ℂ F := by rw [hF]; infer_instance
  let b := stdOrthonormalBasis ℂ F
  have hpre : ∀ k, ∃ e : V, e ∈ E ∧ ι e = (b k : H) := fun k => Submodule.mem_map.mp (b k).2
  choose e heE he using hpre
  refine ⟨∑ k, β (e k) ⊗ₜ[ℂ] e k, fun y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [contr_tmul, he]

  set z : V := ∑ k, ⟪(b k : H), ι y⟫_ℂ • e k with hz
  have hperp : ∀ x ∈ E, ⟪ι (y - z), ι x⟫_ℂ = 0 := by
    intro x hx
    have hxF : ι x ∈ F := Submodule.mem_map_of_mem hx
    have hx' : ι x = ∑ j, ⟪(b j : H), ι x⟫_ℂ • (b j : H) := by
      have := congrArg Subtype.val (b.sum_repr' ⟨ι x, hxF⟩)
      simpa [Submodule.coe_inner] using this.symm
    have key : ⟪ι y, ι x⟫_ℂ = ∑ j, ⟪ι y, (b j : H)⟫_ℂ * ⟪(b j : H), ι x⟫_ℂ := by
      conv_lhs => rw [hx']
      rw [inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_smul_right, mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hz, map_sub, map_sum, map_smul, he, inner_sub_left, sum_inner, inner_smul_left, inner_conj_symm]
    rw [key, sub_self]
  have hyz := h (y - z) hperp
  rw [map_sub, sub_eq_zero] at hyz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hyz, hz, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, inner_conj_symm]

theorem tensorForm : TensorForm := by
  intro U A V H _ _ _ _ _ _ _ _ ι hι
  have sep : ∀ s u : A ⊗[ℂ] V, (∀ y, contr ι y s = contr ι y u) → s = u := fun s u hsu =>
    sub_eq_zero.mp (eq_zero_of_contr ι hι _ fun y => by rw [map_sub, hsu, sub_self])
  refine ⟨fun t ht => eq_zero_of_contr ι hι t ht, fun B hB => ?_⟩
  have hex : ∀ P, ∃ t : A ⊗[ℂ] V, ∀ y, contr ι y t = B P y := by
    intro P
    obtain ⟨E, hE, hk⟩ := hB P
    exact exists_tensor ι (B P) E hk
  choose g hg using hex
  exact ⟨{ toFun := g
           map_add' := fun P Q => sep _ _ fun y => by simp [hg]
           map_smul' := fun c P => sep _ _ fun y => by simp [hg] }, hg⟩

end GlobalTheory.Chain.IoLift.TensorFormProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKEquivariantGraphGoursat
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKEquivariantGraphGoursat
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.KStableGraph

theorem exists_partner {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S S' U : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKStableOn ε ρ S) (hS' : Formalism.MainNotions.S.IsKStableOn ε ρ S')
    (hU : Formalism.MainNotions.S.IsKStableOn ε ρ U)
    (irr : ∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S)
    (hle : U ≤ S ⊔ S') (hUS' : U ⊓ S' = ⊥) (hU0 : U ≠ ⊥) :
    ∀ s ∈ S, ∃ s' ∈ S', s + s' ∈ U := by
  have hT : Formalism.MainNotions.S.IsKStableOn ε ρ (S ⊓ (U ⊔ S')) := by
    intro g hg v hv
    obtain ⟨hvS, hvU⟩ := Submodule.mem_inf.mp hv
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp hvU
    refine Submodule.mem_inf.mpr ⟨hS g hg _ hvS, ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hU g hg u hu) (hS' g hg t ht)
  rcases irr _ inf_le_left hT with h | h
  · exfalso
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (hle hu)
    have hsT : s ∈ S ⊓ (U ⊔ S') := by
      refine Submodule.mem_inf.mpr ⟨hs, ?_⟩
      have : s = u - t := by rw [← hst]; abel
      rw [this]
      exact Submodule.sub_mem_sup hu ht
    rw [h] at hsT
    have hs0 : s = 0 := (Submodule.mem_bot ℂ).mp hsT
    have hut : u = t := by rw [← hst, hs0, zero_add]
    have : u ∈ U ⊓ S' := Submodule.mem_inf.mpr ⟨hu, hut ▸ ht⟩
    rw [hUS'] at this
    exact hu0 ((Submodule.mem_bot ℂ).mp this)
  · intro s hs
    have hs' : s ∈ S ⊓ (U ⊔ S') := h.symm ▸ hs
    obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.mp (Submodule.mem_inf.mp hs').2
    refine ⟨-t, S'.neg_mem ht, ?_⟩
    have : s + -t = u := by rw [← hut]; abel
    rw [this]; exact hu

theorem exists_kMap_onto : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' U : Submodule ℂ H), Formalism.MainNotions.S.IsKStableOn ε ρ S → Formalism.MainNotions.S.IsKStableOn ε ρ S' → Formalism.MainNotions.S.IsKStableOn ε ρ U → (∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S) → (∀ T : Submodule ℂ H, T ≤ S' → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S') → S ⊓ S' = ⊥ → U ≤ S ⊔ S' → U ⊓ S = ⊥ → U ⊓ S' = ⊥ → U ≠ ⊥ → ∃ φ : H →ₗ[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u ∈ S, φ (ρ k u) = ρ k (φ u)) ∧ S.map φ = S' := by
  intro n ε H _ _ ρ S S' U hS hS' hU irrS irrS' hSS' hle hUS hUS' hU0
  have ex := exists_partner hS hS' hU irrS hle hUS' hU0
  have ex' := exists_partner hS' hS hU irrS' (by rwa [sup_comm]) hUS hU0
  have uniq : ∀ s ∈ S, ∀ a ∈ S', ∀ b ∈ S', s + a ∈ U → s + b ∈ U → a = b := by
    intro s _ a ha b hb h1 h2
    have h3 := U.sub_mem h1 h2
    rw [add_sub_add_left_eq_sub] at h3
    have : a - b ∈ U ⊓ S' := Submodule.mem_inf.mpr ⟨h3, S'.sub_mem ha hb⟩
    rw [hUS'] at this
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp this)
  choose g hg using ex
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun x => ⟨g x x.2, (hg x x.2).1⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show g ((x + y : S) : H) (x + y).2 = g x x.2 + g y y.2
        refine uniq _ (x + y).2 _ (hg _ _).1 _ (S'.add_mem (hg x x.2).1 (hg y y.2).1) (hg _ _).2 ?_
        have := U.add_mem (hg x x.2).2 (hg y y.2).2
        rw [Submodule.coe_add]
        convert this using 1
        abel
      map_smul' := fun c x => by
        apply Subtype.ext
        show g ((c • x : S) : H) (c • x).2 = c • g x x.2
        refine uniq _ (c • x).2 _ (hg _ _).1 _ (S'.smul_mem c (hg x x.2).1) (hg _ _).2 ?_
        have := U.smul_mem c (hg x x.2).2
        rw [Submodule.coe_smul]
        convert this using 1
        rw [smul_add] }
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  let φ : H →ₗ[ℂ] H := S'.subtype ∘ₗ f ∘ₗ S.projectionOnto C hC
  have hφ : ∀ u (hu : u ∈ S), φ u = g u hu := by
    intro u hu
    have := Submodule.linearProjOfIsCompl_apply_left hC ⟨u, hu⟩
    change ((f (S.projectionOnto C hC ((⟨u, hu⟩ : S) : H)) : S') : H) = _
    rw [this]
    rfl
  refine ⟨φ, ?_, ?_⟩
  · intro k hk u hu
    have hku : ρ k u ∈ S := hS k hk u hu
    rw [hφ _ hku, hφ u hu]
    refine uniq _ hku _ (hg _ hku).1 _ (hS' k hk _ (hg u hu).1) (hg _ hku).2 ?_
    rw [← map_add (f := _)]
    exact hU k hk _ (hg u hu).2
  · apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [hφ u hu]
      exact (hg u hu).1
    · intro s' hs'
      obtain ⟨s, hs, hsU⟩ := ex' s' hs'
      refine Submodule.mem_map.mpr ⟨s, hs, ?_⟩
      rw [hφ s hs]
      exact uniq s hs _ (hg s hs).1 s' hs' (hg s hs).2 (by rwa [add_comm])

end GlobalTheory.KStableGraph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKEquivariantGraphGoursatStatement
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kEquivariant_graph_goursat : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' U : Submodule ℂ H), Formalism.MainNotions.S.IsKStableOn ε ρ S → Formalism.MainNotions.S.IsKStableOn ε ρ S' → Formalism.MainNotions.S.IsKStableOn ε ρ U → (∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S) → (∀ T : Submodule ℂ H, T ≤ S' → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S') → S ⊓ S' = ⊥ → U ≤ S ⊔ S' → U ⊓ S = ⊥ → U ⊓ S' = ⊥ → U ≠ ⊥ → ∃ φ : H →ₗ[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u ∈ S, φ (ρ k u) = ρ k (φ u)) ∧ S.map φ = S' := by
  first | exact @GlobalTheory.KStableGraph.exists_kMap_onto | exact GlobalTheory.KStableGraph.exists_kMap_onto | (intros; apply GlobalTheory.KStableGraph.exists_kMap_onto <;> assumption)
end
end
