module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvOneSplitStab
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators

theorem theta_eq_zero_of_orth {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {F : Type} [AddCommGroup F] [Module K F]
    {σ : K →+* ℂ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {j : F →ₛₗ[σ] V} {r : Representation K G F} {ρ : G → V →ₗ[ℂ] V} {gE : Representation ℂ G E} {Θ : V →ₗ[ℂ] E}
    (H : Hyp σ j r ρ gE Θ)
    (hRZ : Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint Θ)).comap j : Set F)) =
      LinearMap.range (LinearMap.adjoint Θ))
    (e a : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e)
    (hfix : ∀ y ∈ LinearMap.range Θ, opV σ (fun g => gE g) a y = y) (f : F) (hea : opF r e f = opF r a f)
    (horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint Θ)).comap j ⊓ LinearMap.range (opF r e) : Submodule K F),
      ⟪j z, j f⟫_ℂ = 0) : Θ (j f) = 0 := by
  have h1 : Θ (j (opF r e f)) = Θ (j f) := by
    rw [hea, j_opF H.jr, theta_opV H.sp H.jr H.eq, hfix _ ⟨_, rfl⟩]
  have h2 : j (opF r e f) ∈ LinearMap.range (opV σ ρ e) := ⟨j f, (j_opF H.jr e f).symm⟩
  obtain ⟨u', hu', hθ⟩ := H.dn e he h2
  have hu'' : u' ∈ Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
      LinearMap.range (opF r e) : Submodule K F) : Set F)) := by
    rw [H.ratLev hRZ e he]
    exact hu'
  have h3 : ⟪u', j f⟫_ℂ = 0 := by
    have hle : Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓
        LinearMap.range (opF r e) : Submodule K F) : Set F)) ≤ (Submodule.span ℂ {j f})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact horth z hz
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu'')
  obtain ⟨⟨w, rfl⟩, -⟩ := hu'
  have h4 : Θ (LinearMap.adjoint Θ w - j f) = 0 := by
    rw [map_sub, hθ, h1, sub_self]
  have h5 : ⟪LinearMap.adjoint Θ w, LinearMap.adjoint Θ w - j f⟫_ℂ = 0 := by
    rw [LinearMap.adjoint_inner_left, h4, inner_zero_right]
  rw [inner_sub_right, h3, sub_zero, inner_self_eq_zero] at h5
  rw [← h1, ← hθ, h5, map_zero]

theorem opF_lvlIdem_fix {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (H : Subgroup G) (ψ : H →* Kˣ) (v : V)
    (hv : ∀ a : H, ρ a.1 v = ((ψ a : Kˣ) : K) • v) : opF ρ (lvlIdem H ψ) v = v := by
  classical
  rw [opF_eq_lift]
  unfold lvlIdem
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  have : ∀ h : H, MonoidAlgebra.lift K (V →ₗ[K] V) G ρ
      (MonoidAlgebra.single (h : G) ((Nat.card H : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K))) v = (Nat.card H : K)⁻¹ • v := by
    intro h
    rw [MonoidAlgebra.lift_single, LinearMap.smul_apply, hv, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, mul_one]
  rw [Finset.sum_congr rfl fun h _ => this h, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne'), one_smul]

end GlobalTheory.Mem.ThOrth

namespace GlobalTheory.Mem.ThOrth

open Formalism.IndefR.CxPass.LevelOperators


set_option maxHeartbeats 4000000 in
theorem thG_eq_zero_of_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y _Z hP hH i t x hx
  have hok := hH.ok
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak hP.char hH.aux.ex
  have hM := hc.models
  have hCore : GlobalTheory.Hk3.Core R.toRealDat F.lv2 := ⟨hc.lev, hc.grp, hc.fam, hc.models, hc.chain, hc.thP⟩
  have hL := GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hCore hok.ok2.irr i
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hM
  have hJ : (R.toCx3 F).JIsoL F.cv := Formalism.IndefR.Links.RealDat3.jIsoL_of (F := F) hM
  have hRZ : (R.toCx3 F).RatZ := (complex_data_conditions_base_level_of_primitive_links hok hH.sep hP.char hH.prim).ratZ
  have hjr (g : G) (v : A3.fam3.amb3.FL i t) :
      (R.toCx3 F).jL i t ((A3.A.fam.L i t).r g v) =
        (R.toCx3 F).opLC i t (Sum.inr g) ((R.toCx3 F).jL i t v) := by
    have hb := hK i t
    have key : ∀ k : Module.Basis.ofVectorSpaceIndex D.what₂.LL (A3.fam3.amb3.FL i t),
        (R.toCx3 F).opLC i t (Sum.inr g) ((R.toCx3 F).jL i t (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t) k)) =
        (R.toCx3 F).jL i t ((A3.A.fam.L i t).r g (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t) k)) := by
      intro k
      unfold Formalism.IndefR.Cx.CxData.opLC
      rw [dite_eq_left hb]
      have e : (R.toCx3 F).jL i t (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t) k) = Module.Basis.mk hb.1 hb.2.ge k :=
        (Module.Basis.mk_apply hb.1 hb.2.ge k).symm
      rw [e, Module.Basis.constr_basis]
      rfl
    have hh := Module.Basis.ext (Module.Basis.ofVectorSpace D.what₂.LL (A3.fam3.amb3.FL i t))
      (f₁ := ((R.toCx3 F).jL i t).comp ((A3.A.fam.L i t).r g))
      (f₂ := ((R.toCx3 F).opLC i t (Sum.inr g)).comp ((R.toCx3 F).jL i t))
      (fun k => (key k).symm)
    exact LinearMap.congr_fun hh v
  have H : Hyp A3.fam3.base3.v0.embedding ((R.toCx3 F).jL i t) (A3.A.fam.L i t).r
      (fun g => (R.toCx3 F).opLC i t (Sum.inr g)) (R.gWx F i) ((R.toCx3 F).θ' i t) := by
    refine ⟨Formalism.IndefR.CxPass.lift_embeddings_span hK i t, hjr, ?_, hH.prim.gEquiv.2 i t, hH.prim.gUnit.2 i⟩
    intro g a b
    rw [hJ i t, hJ i t]
    change A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _) =
      A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _)
    set_option backward.isDefEq.respectTransparency false in
      rw [CSDForm.csumForm_apply, CSDForm.csumForm_apply]
    exact congrArg A3.fam3.base3.v0.embedding ((hok.ok2.lifts i t).act.unitary g a b)
  have hB : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1 := ⟨hok.ok2.conj, hok.ok2.irr, hok.ok2.lifts i t⟩

  have hopE : opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) := by
    let mA : ((R.HW i (sg0 D A3.A)).H →ₗ[ℂ] (R.HW i (sg0 D A3.A)).H) →+
        (Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H →ₗ[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H) :=
      { toFun := Tw.map (twAt D.what₂.embLL A3.A.v0), map_zero' := LinearMap.ext fun _ => rfl,
        map_add' := fun _ _ => LinearMap.ext fun _ => rfl }
    rw [show Tw.map (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i) = mA (GlobalTheory.Hk3.eH R.toRealDat i) from rfl]
    unfold opV GlobalTheory.Hk3.eH
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => LinearMap.ext fun y => ?_
    show cj (twAt D.what₂.embLL A3.A.v0) (A3.A.v0.embedding ((idemOf A3.A.X).coeff g)) •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y) =
      RealDat.eC (A := A3.A) (sg0 D A3.A) g •
        R.gW i (sg0 D A3.A) g (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) y)
    rw [Formalism.IndefR.Links.emb_eq D.what₂.embLL A3.A.v0, Formalism.IndefR.Links.cj_cj]
    rfl
  have hθ : ∀ (u : (R.toCx3 F).FLC i t),
      Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u) =
        cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HV i t).H) u) :=
    fun u => rfl
  have hfix : ∀ y ∈ LinearMap.range ((R.toCx3 F).θ' i t),
      opV A3.fam3.base3.v0.embedding (fun g => R.gWx F i g) (idemOf A3.A.X) y = y := by
    rintro _ ⟨u, rfl⟩
    rw [hopE]
    change Tw.mk (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Hk3.eH R.toRealDat i
      (Tw.out (s := (twAt D.what₂.embLL A3.A.v0)) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).θ' i t u))) =
      (R.toCx3 F).θ' i t u
    rw [hθ, map_smul, hL.2.2.2, ← hθ]
    rfl

  set ℓ := A3.A.fam.lvlA F.P0 F.ψ0 with hℓ
  set f0 := liftForm A3.A F.P0 F.ψ0 i t x with hf0
  have hf0l : f0 = GlobalTheory.Mem.LiftForms.lvlForm (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ x := rfl
  have hlev : f0 ∈ lvlForms (A3.A.fam.L i t).S (A3.A.fam.L i t).r ℓ.P ℓ.ψ := by
    rw [← GlobalTheory.Mem.LiftForms.range_lvlForm]
    exact ⟨x, hf0l.symm⟩
  have hfix0 : opF (A3.A.fam.L i t).r (lvlIdem ℓ.P ℓ.ψ) f0 = f0 := by
    exact opF_lvlIdem_fix (A3.A.fam.L i t).r ℓ.P ℓ.ψ f0 hlev
  have hea : opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ) f0 = opF (A3.A.fam.L i t).r (idemOf A3.A.X) f0 := by
    rw [goodAt, opF_mul, LinearMap.comp_apply, hfix0]
    rfl
  have horth : ∀ z ∈ ((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t) ⊓
      LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _),
      ⟪(R.toCx3 F).jL i t z, (R.toCx3 F).jL i t f0⟫_ℂ = 0 := by
    intro z hz
    have hZeq : (((LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' i t))).comap ((R.toCx3 F).jL i t)) ⊓
        LinearMap.range (opF (A3.A.fam.L i t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) : Submodule _ _) =
        LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := by
      refine Eq.trans ?_ (Formalism.IndefR.CxPass.LevelOperators.range_toF (A3.A.fam.L i t) ℓ _).symm
      rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq]
      rfl
    have hz' : z ∈ LinearMap.range ((A3.A.fam.L i t).toF ℓ ((R.toCx3 F).Zl i t)) := hZeq ▸ hz
    obtain ⟨c, rfl⟩ := hz'
    rw [← GlobalTheory.Mem.LiftForms.lvlForm_lE hB c]
    refine (hJ i t _ _).trans ?_
    have h0 : Formalism.DivisionValues.hform ((A3.A.fam.L i t).S.lvlH (A3.A.fam.L i t).r ℓ.P ℓ.ψ)
        ((A3.A.fam.L i t).lE ℓ ((R.toCx3 F).Zl i t) *ᵥ c) x = 0 := hx c
    show A3.fam3.base3.v0.embedding (CSDForm.csumForm (A3.A.fam.L i t).S _ _) = 0
    rw [CSDForm.csumForm_apply, hf0l, GlobalTheory.Mem.LiftForms.csum_lvlForm, h0, mul_zero, map_zero]
  have key := theta_eq_zero_of_orth H (hRZ.2 i t) (goodAt ℓ.X ℓ.P ℓ.ψ) (idemOf A3.A.X)
    (opF_goodAt_idem _ _ hok.ok2.irr _ _) hfix f0 hea horth
  have h2 := congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) key
  rw [hθ, hP.phs i, map_one, one_smul] at h2
  exact h2

end GlobalTheory.Mem.ThOrth

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLevelForm_orthogonal_killed_by_thetaMap : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0 := by
  first | exact @GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth | exact GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth | (intros; apply GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOn
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOn
open MeasureTheory GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartGlue

theorem glueMeas_add_of_compat_on : ∀ {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] {n : ℕ} {κ : Type} (e : κ → OpenPartialHomeomorph Y (V n)),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) →
    (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ (ρ ρ' : κ → Y → ℝ≥0∞),
    (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) →
    (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ' j y) →
    (∀ i, AEMeasurable (fun v => ρ i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))) →
    glueMeas e (fun i y => ρ i y + ρ' i y) S = glueMeas e ρ S + glueMeas e ρ' S := by
  intro Y _ _ _ _ n κ e hd hcov S hS ρ ρ' hρ hρ' hAE

  have same : ∀ (τ τ' : κ → Y → ℝ≥0∞), (∀ i y, y ∈ S → τ i y = τ' i y) →
      glueMeas e τ S = glueMeas e τ' S := by
    intro τ τ' h
    have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := τ) (ρ' := τ') (c := 1) ENNReal.one_ne_top hS
      (fun i y _ hy => by rw [one_mul]; exact h i y hy)
    have := congrArg (fun μ : Measure Y => μ S) hm
    simpa only [Measure.smul_apply, smul_eq_mul, one_mul, Measure.restrict_apply_self] using this

  have compat : ∀ (τ : κ → Y → ℝ≥0∞), (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      τ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * τ j y) →
      ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (τ i) y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * S.indicator (τ j) y := by
    intro τ hτ i j y hi hj
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact hτ i j y hy hi hj
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  have cσ := compat ρ hρ
  have cσ' := compat ρ' hρ'
  have cs : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (ρ i) y + S.indicator (ρ' i) y =
        ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * (S.indicator (ρ j) y + S.indicator (ρ' j) y) := by
    intro i j y hi hj
    rw [mul_add, cσ i j y hi hj, cσ' i j y hi hj]

  have aem : ∀ i (A : Set Y), MeasurableSet A → A ⊆ (e i).source →
      AEMeasurable (fun v => S.indicator (ρ i) ((e i).symm v)) (volume.restrict ((e i) '' A)) := by
    intro i A hAm hA
    have hT : MeasurableSet ((e i).target ∩ (e i).symm ⁻¹' S) := by
      rw [← (e i).image_source_inter_eq']
      exact measurableSet_image (e i) ((e i).open_source.measurableSet.inter hS) Set.inter_subset_left
    have hg := ((aemeasurable_indicator_iff hT).2 (hAE i)).mono_measure
      (Measure.restrict_le_self (s := (e i) '' A))
    refine hg.congr ((ae_restrict_iff' (measurableSet_image (e i) hAm hA)).2
      (Filter.Eventually.of_forall ?_))
    rintro _ ⟨y, hy, rfl⟩
    have ht : (e i) y ∈ (e i).target := (e i).map_source (hA hy)
    show _ = S.indicator (ρ i) ((e i).symm ((e i) y))
    by_cases hs : (e i).symm ((e i) y) ∈ S
    · rw [Set.indicator_of_mem (show (e i) y ∈ (e i).target ∩ (e i).symm ⁻¹' S from ⟨ht, hs⟩),
        Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem (show (e i) y ∉ (e i).target ∩ (e i).symm ⁻¹' S from fun h => hs h.2),
        Set.indicator_of_notMem hs]
  have key : glueMeas e (fun i y => S.indicator (ρ i) y + S.indicator (ρ' i) y) =
      glueMeas e (fun i => S.indicator (ρ i)) + glueMeas e (fun i => S.indicator (ρ' i)) := by
    refine ext_of_cover (fun i => (e i).source) (fun i => (e i).open_source) hcov fun i A hA hAi => ?_
    rw [Measure.add_apply, glueMeas_apply e _ hd cs i hA hAi,
      glueMeas_apply e (fun i => S.indicator (ρ i)) hd cσ i hA hAi,
      glueMeas_apply e (fun i => S.indicator (ρ' i)) hd cσ' i hA hAi,
      chartMeas_apply_of_subset _ _ hA hAi, chartMeas_apply_of_subset _ _ hA hAi,
      chartMeas_apply_of_subset _ _ hA hAi]
    exact lintegral_add_left' (aem i A hA hAi) _
  rw [same (fun i y => ρ i y + ρ' i y) (fun i y => S.indicator (ρ i) y + S.indicator (ρ' i) y)
      (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    same ρ (fun i => S.indicator (ρ i)) (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    same ρ' (fun i => S.indicator (ρ' i)) (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    key, Measure.add_apply]

end GlobalTheory.ChartGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOnStatement
open MeasureTheory GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedChartDensityMeasure_add_of_compatible_on : ∀ {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] {n : ℕ} {κ : Type} (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ (ρ ρ' : κ → Y → ℝ≥0∞), (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ρ' i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ' j y) → (∀ i, AEMeasurable (fun v => ρ i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))) → glueMeas e (fun i y => ρ i y + ρ' i y) S = glueMeas e ρ S + glueMeas e ρ' S := by
  first | exact @GlobalTheory.ChartGlue.glueMeas_add_of_compat_on | exact GlobalTheory.ChartGlue.glueMeas_add_of_compat_on | (intros; apply GlobalTheory.ChartGlue.glueMeas_add_of_compat_on <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwaCell

theorem exists_mem_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ g : GL (Fin m) k, ∃ a : Fin m → ℤ, g ∈ GlobalTheory.IwaCell.cell ϖ a := by
  intro k _ _ _ _ m ϖ hϖ g
  obtain ⟨k₀, b, hb, hg⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k m g⁻¹
  have hg' : g = b⁻¹ * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← hg, inv_inv]
  set c := b⁻¹ with hc
  have hcT : c.val.BlockTriangular id := by
    have : c.val = b.val⁻¹ := by rw [hc, Matrix.coe_units_inv]
    rw [this]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hdet : c.val.det = ∏ i, c.val i i := Matrix.det_of_upperTriangular hcT
  have hd : ∀ i, c.val i i ≠ 0 := fun i h => by
    have := Matrix.GeneralLinearGroup.det_ne_zero c
    rw [hdet] at this
    exact this (Finset.prod_eq_zero (Finset.mem_univ i) h)
  let d : Fin m → kˣ := fun i => Units.mk0 _ (hd i)
  let a : Fin m → ℤ := fun i => ord k (d i)
  let e : Fin m → kˣ := fun i => d i / ϖ ^ a i
  have he : ∀ i, valuation k (e i : k) = 1 := fun i => by
    apply ord_eq_zero_iff.1
    simp only [e, div_eq_mul_inv, ← _root_.zpow_neg, ord_mul, ord_zpow, hϖ, a]
    ring
  have hde : d = (fun i => ϖ ^ a i) * e := by
    funext i; simp [e]
  let u := c * (diagT k (Fin m) d)⁻¹
  have hu : u ∈ unipB k (Fin m) := by
    rw [mem_unipB]
    have hval : u.val = c.val * diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) := by
      simp only [u, ← map_inv, Units.val_mul, val_diagT, Pi.inv_apply]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval, mul_diagonal, hcT hij, zero_mul]
    · rw [hval, mul_diagonal]; simp [d, mul_inv_cancel₀ (hd i)]
  refine ⟨a, u, hu, diagT k (Fin m) e * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹,
    mul_mem (GlobalTheory.LocalCartan.diagT_mem_KO he) (inv_mem ⟨k₀, rfl⟩), ?_⟩
  rw [hg', tD, ← mul_assoc, mul_assoc u, ← map_mul, ← hde]
  simp [u]

end GlobalTheory.IwaCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.RealGeo.Upd

section
open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section
variable (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (kap lam err)

abbrev upE : RealDat D A C.Q.c.F := { R.upd6 kap lam with err0 := err }


set_option maxHeartbeats 1600000 in
def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat C.toCore R i Tp tup) :
    OMDat C.toCore (upE C R kap lam err) i Tp tup := { O with }


set_option maxHeartbeats 1600000 in
def updFWT {κ v₀} (t : FWTie C R κ v₀) : FWTie C (upE C R kap lam err) κ v₀ :=
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

variable {C R}
variable {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (O : ∀ i, OMDat C.toCore R i Unit (fun _ => A.μ0))


set_option maxHeartbeats 1600000 in
theorem omPins_upE (i : Fin D.R.m) (h : OMPins C R κ v₀ O i) :
    OMPins C (upE C R kap lam err) κ v₀ (fun i => updO C R kap lam err (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

end

end

end GlobalTheory.RealGeo.Upd

namespace GlobalTheory.RealGeo


set_option maxHeartbeats 1600000 in
theorem geoHalf_upd : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (R : RealDat D A C.Q.c.F) (ph : Fin D.R.m → ℂ) kap lam err (g : GlobalTheory.RealGeo.GeoHalf C R ph), ∃ g' : GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph, g'.κ = g.κ ∧ HEq g'.v₀ g.v₀ ∧ (GlobalTheory.RealGeo.InGeo g → GlobalTheory.RealGeo.InGeo g') := by
  intro D G _ _ Pl0 T A C _ R ph kap lam err g
  refine ⟨⟨g.κ, g.v₀, Upd.updFWT C R kap lam err g.fw, g.bar, fun i => Upd.updO C R kap lam err (g.O i),
    fun i => Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩, rfl, HEq.rfl, ?_⟩
  intro h
  exact ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

end GlobalTheory.RealGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruence
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.CongConjugate

open ReciprocityTheory.Aut Formalism.AUTREP

theorem congConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), principalLevelFrame.CongConj L n := by
  intro L _ _ _ n h N hN
  obtain ⟨d, hd, hdh⟩ := GlobalTheory.FinTypCount.exists_denom_matrix
    (((h.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)))
  obtain ⟨e, he, heh⟩ := GlobalTheory.FinTypCount.exists_denom_matrix
    ((((h⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)))
  refine ⟨N * d * e, Nat.mul_pos (Nat.mul_pos hN hd) he, fun κ hκ => ?_⟩
  choose Y hY eY using hκ.2
  set H : Matrix (Fin n) (Fin n) (AL L) := ((h.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hH
  set Hi : Matrix (Fin n) (Fin n) (AL L) := (((h⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hHi
  have hHH : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hK : ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y := by
    ext a b
    have := eY a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hprod : (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      Hi * (1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y) * H := by
    rw [← hK]; simp [hHi, hH, Subgroup.coe_mul, Units.val_mul]
  set Z : Matrix (Fin n) (Fin n) (AL L) := ((e : AL L) • Hi) * Matrix.of Y * ((d : AL L) • H) with hZ
  have hZint : ∀ i j, Z i j ∈ ALint L := by
    intro i j
    rw [hZ, Matrix.mul_apply]
    refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ ?_
    · rw [Matrix.mul_apply]
      refine Subring.sum_mem _ fun a _ => Subring.mul_mem _ ?_ (hY a b)
      simpa [Matrix.smul_apply, smul_eq_mul] using heh i a
    · simpa [Matrix.smul_apply, smul_eq_mul] using hdh b j
  have hdiff : Hi * (1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y) * H - 1 = (N : AL L) • Z := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hHH, add_sub_cancel_left, hZ]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul]
    congr 1
    push_cast; ring
  have hentry : ∀ i j, (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * Z i j := by
    intro i j
    rw [hprod]
    have h2 := congrFun (congrFun hdiff i) j
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h2
    exact h2
  refine ⟨fun i j => ?_, fun i j => ⟨Z i j, hZint i j, hentry i j⟩⟩
  have h3 : (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j =
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j + (N : AL L) * Z i j := by
    rw [← hentry]; ring
  rw [h3]
  refine add_mem ?_ (Subring.mul_mem _ (natCast_mem _ _) (hZint i j))
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

end GlobalTheory.CongConjugate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruenceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_congruence_conj_contains_congruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), principalLevelFrame.CongConj L n := by
  first | exact @GlobalTheory.CongConjugate.congConj | exact GlobalTheory.CongConjugate.congConj | (intros; apply GlobalTheory.CongConjugate.congConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModel
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.ModelCharts

theorem exists_etale_coords_of_opens {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (D : ℕ)
    (W : X.Opens) [SmoothOfRelativeDimension D (W.ι ≫ p)] {z : X} (hz : z ∈ W) :
    ∃ (U : X.Opens) (x : Fin D → Γ(X, U)), IsAffineOpen U ∧ z ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  have hzr : z ∈ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]; exact hz
  obtain ⟨z', rfl⟩ := hzr
  obtain ⟨U', x', hU', hzU', hx'⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := W.ι ≫ p) (D := D) z'
  let e : Γ(X, W.ι ''ᵁ U') ≃+* Γ(W, U') := (W.ι.appIso U').commRingCatIsoToRingEquiv
  refine ⟨W.ι ''ᵁ U', fun a => e.symm (x' a), hU'.image_of_isOpenImmersion W.ι, ⟨z', hzU', rfl⟩, ?_⟩
  have h2 : (W.ι ≫ p).appLE ⊤ U' (by simp) =
      p.appLE ⊤ (W.ι ''ᵁ U') (by simp) ≫ (W.ι.appIso U').hom := by
    first
    | rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    | (rw [Scheme.Hom.appIso_hom']; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
    | simp [Scheme.Hom.appIso_hom, Scheme.Hom.appLE, Scheme.Hom.comp_app]
    | (simp only [Scheme.Hom.appIso_hom']; rw [Scheme.Hom.appLE_comp_appLE])
  have halg : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U' = (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) := by
    unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX
    rw [h2]
    rfl
  have heq : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (W.ι ≫ p) U') x' =
      (e : Γ(X, W.ι ''ᵁ U') →+* Γ(W, U')).comp
        (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (W.ι ''ᵁ U')) fun a => e.symm (x' a)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [halg]
    · intro i; simp
  rw [heq] at hx'
  have h3 := RingHom.Etale.respectsIso.left _ e.symm hx'
  convert h3 using 1
  ext <;> simp

set_option maxHeartbeats 1000000 in
private theorem exists_algChart_mem_source {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := by
  obtain ⟨a, ha⟩ := y
  obtain ⟨τ', hcomp⟩ : ∃ τ' : K →+* ℂ, τ'.comp (algebraMap R K) = τ :=
    ⟨IsFractionRing.lift hτ, RingHom.ext fun r => IsFractionRing.lift_algebraMap hτ r⟩
  have hsp : a ≫ p = Spec.map (CommRingCat.ofHom τ') ≫ spMap (algebraMap R K) := by
    rw [ha]; unfold spMap; rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  obtain ⟨b, hb⟩ : ∃ b, b ≫ j = a := ⟨h.lift a (Spec.map (CommRingCat.ofHom τ')) hsp, h.lift_fst _ _ _⟩
  haveI : Flat (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    rw [CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat K (nonZeroDivisors R)
  haveI : SurjectiveOnStalks (spMap (algebraMap R K)) := by
    unfold spMap
    refine (HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)).2 ?_
    rw [CommRingCat.hom_ofHom]
    exact RingHom.surjectiveOnStalks_of_isLocalization (nonZeroDivisors R) K
  obtain ⟨W, hW, hsm⟩ := GlobalTheory.GenSpread.exists_opens_smoothOfRelativeDimension_of_isPullback h D
    (b (IsLocalRing.closedPoint ℂ))
  haveI := hsm
  have hz : a (IsLocalRing.closedPoint ℂ) ∈ W := by
    rw [← hb]
    first | exact hW | simpa using hW
  obtain ⟨U, x, hU, hzU, hx⟩ := exists_etale_coords_of_opens p D W hz
  obtain ⟨c, hc, -⟩ := GlobalTheory.AlgChart.exists_of_etale (σ := τ) hU x hx (y := ⟨a, ha⟩)
    (GlobalTheory.CxPts.mem_ptsIn.2 hzU)
  exact ⟨c, hc⟩

theorem exists_chart {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {D : ℕ} {X Y : Scheme.{0}} {p : X ⟶ Sp R} {q : Y ⟶ Sp K} {j : Y ⟶ X}
    (h : IsPullback j q p (spMap (algebraMap R K))) [LocallyOfFinitePresentation p]
    [SmoothOfRelativeDimension D q] {τ : R →+* ℂ} (hτ : Function.Injective τ) (y : CxPts p τ) :
    ∃ c : AlgChart p τ D, y ∈ c.e.source := exists_algChart_mem_source h hτ y

end GlobalTheory.ModelCharts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts
open scoped ContDiff ENNReal

namespace GlobalTheory.ChernTransfer

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k'}
  {σ : k →+* ℂ} {σ' : k' →+* ℂ} {D : ℕ} {j : Y ⟶ X} {Φ : CxPts q σ' ≃ₜ CxPts p σ}
  (hΦ : ∀ z, (Φ z).1 = z.1 ≫ j) {B : LB X} {φ : Weight p σ B}

abbrev pullW (φ : Weight p σ B) : Weight q σ' (LB.LinComb B (K := PUnit) (fun _ => j) fun _ => 1) :=
  φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)

theorem pullW_φ (i : PUnit → B.ι) (z : CxPts q σ') :
    (pullW hΦ φ).φ i z = φ.φ (i PUnit.unit) (Φ z) :=
  (Fintype.sum_unique fun a : PUnit.{1} => ((1 : ℤ) : ℝ) * φ.φ (i a) (Φ z)).trans (by simp)


include hΦ in
theorem ev_app' (W : X.Opens) (g : Γ(X, W)) (z : CxPts q σ') :
    ev q σ' (j ⁻¹ᵁ W) (j.app W g) z = ev p σ W g (Φ z) := by
  rw [ev, ev, hΦ]
  exact (valR_comp z.1 j W g).symm


include hΦ in
theorem mem_preimage_iff (W : X.Opens) (z : CxPts q σ') :
    z ∈ ptsIn q σ' (j ⁻¹ᵁ W) ↔ Φ z ∈ ptsIn p σ W := by
  change _ ↔ ⊤ ≤ (Φ z).1 ⁻¹ᵁ W
  rw [hΦ]
  rfl

theorem isCInf_pullW (h : φ.IsCInf) : (pullW hΦ φ).IsCInf := fun i z hz => by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h _ _
    (mem_of_mem_linComb (m := fun _ => Φ z) (fun _ => hΦ z) hz PUnit.unit)
  refine ⟨j ⁻¹ᵁ W, ι, inferInstance, fun a => j.app W (g a), F, O, (mem_preimage_iff hΦ W z).2 h₁,
    h₂, ?_, h₄, ?_⟩
  · simpa only [ev_app' hΦ] using h₃
  · simp only [ev_app' hΦ]
    filter_upwards [Φ.continuous.continuousAt.eventually h₅] with w hw
    exact (pullW_φ hΦ i w).trans hw


include hΦ in
theorem holo_trans (c : AlgChart p σ D) (c' : AlgChart q σ' D) :
    DifferentiableOn ℂ (Φ.transOpenPartialHomeomorph c.e ∘ c'.e.symm)
      (c'.e.target ∩ c'.e.symm ⁻¹' (Φ.transOpenPartialHomeomorph c.e).source) :=
  differentiableOn_euclidean.2 fun a => ((c'.holo _ (j.app c.U (c.x a))).mono fun _ (hv : _ ∈ c'.e.target ∩ c'.e.symm ⁻¹' (Φ.transOpenPartialHomeomorph c.e).source) =>
    ⟨hv.1, (mem_preimage_iff hΦ _ _).2 (c.source_subset hv.2)⟩).congr fun _ hv =>
      (c.apply_eq _ hv.2 a).trans (ev_app' hΦ _ _ _).symm

theorem chernDens_pullW (h : φ.IsCInf) (c : AlgChart p σ D) (c' : AlgChart q σ' D)
    {z : CxPts q σ'} (hz : z ∈ c'.e.source) (hz' : Φ z ∈ c.e.source) :
    c'.chernDens (pullW hΦ φ) z =
      ‖transDet c'.e (Φ.transOpenPartialHomeomorph c.e) z‖ ^ 2 * c.chernDens φ (Φ z) := by
  set e := Φ.transOpenPartialHomeomorph c.e with he
  have ho := isOpen_over c'.e e.open_source
  have hm := mem_over c'.e hz (S := e.source) hz'
  have hi : z ∈ ptsIn q σ' ((LB.LinComb B (K := PUnit) (fun _ => j) fun _ => 1).U
      fun _ => pick φ.isLB (Φ z)) :=
    ptsIn_mono (fun _ hx => mem_iInter.2 fun _ => hx)
      ((mem_preimage_iff hΦ _ z).2 (mem_pick φ.isLB (Φ z)))
  have e₁ : (fun v => ((pullW hΦ φ).φ (fun _ => pick φ.isLB (Φ z)) (c'.e.symm v) : ℂ))
      =ᶠ[𝓝 (c'.e z)] (fun v => (φ.φ (pick φ.isLB (Φ z)) (c.e.symm v) : ℂ)) ∘ e ∘ c'.e.symm :=
    eventually_of_mem (ho.mem_nhds hm) fun v hv => by
      have : c.e.symm (e (c'.e.symm v)) = Φ (c'.e.symm v) := c.e.left_inv hv.2
      simp only [Function.comp_apply, this, pullW_φ]
  have e₂ : (e ∘ c'.e.symm) (c'.e z) = c.e (Φ z) := congrArg e (c'.e.left_inv hz)
  rw [c'.chernDens_eq (isCInf_pullW hΦ h) hz hi, AlgChart.chernDens]
  have e₃ : c'.hess (pullW hΦ φ) (fun _ => pick φ.isLB (Φ z)) z = _ :=
    ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e₁
  rw [e₃, AlgChart.hess,
    ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp ho hm (holo_trans hΦ c c') (e₂ ▸
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h.contDiffAt c hz' (mem_pick _ _))), e₂,
    Complex.re_ofReal_mul, transDet]
  ring

variable [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts q σ')]

theorem chernPart_pullW (R : AnRead p σ D) (R' : AnRead q σ' D) (h : φ.IsCInf) (ε : ℤˣ) :
    (pullW hΦ φ).chernPart D ε = (φ.chernPart D ε).map Φ.symm.toMeasurableEquiv := by
  refine ext_of_cover (fun a : R.ι × R'.ι => (R'.chart a.2).e.source ∩
    (Φ.transOpenPartialHomeomorph (R.chart a.1).e).source)
    (fun a => (R'.chart a.2).e.open_source.inter (OpenPartialHomeomorph.open_source _))
    (fun z => ?_) fun a A hA hs => ?_
  · obtain ⟨a, ha⟩ := R.cover (Φ z)
    obtain ⟨b, hb⟩ := R'.cover z
    exact ⟨(a, b), hb, ha⟩
  set c := R.chart a.1
  set c' := R'.chart a.2
  have h₁ : A ⊆ c'.e.source := hs.trans inter_subset_left
  have h₂ : A ⊆ (Φ.transOpenPartialHomeomorph c.e).source := hs.trans inter_subset_right
  have hA' : MeasurableSet (Φ.symm.toMeasurableEquiv ⁻¹' A) := Φ.symm.toMeasurableEquiv.measurable hA
  have h₃ : Φ.symm.toMeasurableEquiv ⁻¹' A ⊆ c.e.source := fun y hy => by
    have : Φ (Φ.symm y) ∈ c.e.source := h₂ hy
    rwa [Φ.apply_symm_apply] at this
  rw [MeasurableEquiv.map_apply, Weight.chernPart_apply (isCInf_pullW hΦ h) ε c' hA h₁,
    Weight.chernPart_apply h ε c hA' h₃,
    ← chartMeas_apply_of_subset c'.e
      (fun y => ENNReal.ofReal ((ε : ℤ) * c'.chernDens (pullW hΦ φ) y)) hA h₁,
    chartMeas_eq c'.e (Φ.transOpenPartialHomeomorph c.e)
      (ρ' := fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (Φ y))) (holo_trans hΦ c c') hA h₁ h₂
      (fun y hy => by
        rw [chernDens_pullW hΦ h c c' (h₁ hy) (h₂ hy), mul_left_comm,
          ENNReal.ofReal_mul (sq_nonneg _)]),
    chartMeas_apply_of_subset _ _ hA h₂]
  have him : Φ.transOpenPartialHomeomorph c.e '' A = c.e '' (Φ.symm.toMeasurableEquiv ⁻¹' A) := by
    rw [show Φ.symm.toMeasurableEquiv ⁻¹' A = Φ '' A from (Φ.image_eq_preimage_symm A).symm,
      image_image]
    rfl
  rw [him]
  refine lintegral_congr fun v => ?_
  rw [show Φ ((Φ.transOpenPartialHomeomorph c.e).symm v) = c.e.symm v from Φ.apply_symm_apply _]

end GlobalTheory.ChernTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfBearCommonFullFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfBearCommonFullFlag
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

theorem GlobalTheory.FlagBundle.eq_of_coBear : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p p' : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → p' ≫ f₁ = q ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p q → CoBear Eb S₁ φ₁ S₂ φ₂ (p' ≫ f₁) p' q → p = p' := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K _ p p' q hp hp' hc hc'
  obtain ⟨A, hA, h, hh, hAp, hAq⟩ := hc
  obtain ⟨B, hB, h', -, hBp', hBq⟩ := hc'
  have hA' : A ∈ Eb.S ((q ≫ f₂) (IsLocalRing.closedPoint K)) := hp ▸ hA
  have hB' : B ∈ Eb.S ((q ≫ f₂) (IsLocalRing.closedPoint K)) := hp' ▸ hB
  have hAp' : Bears S₁ φ₁ A h p' :=
    GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ K q p' hp'.symm A hA' B hB' h h' hAq hBq hBp'
  exact (hR₁.2.2 K (p ≫ f₁) A hA h hh).unique ⟨rfl, hAp⟩ ⟨hp'.trans hp.symm, hAp'⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfBearCommonFullFlagStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_bear_common_fullFlag : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p p' : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → p' ≫ f₁ = q ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p q → CoBear Eb S₁ φ₁ S₂ φ₂ (p' ≫ f₁) p' q → p = p' := by
  first | exact @GlobalTheory.FlagBundle.eq_of_coBear | exact GlobalTheory.FlagBundle.eq_of_coBear | (intros; apply GlobalTheory.FlagBundle.eq_of_coBear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetMulConjDet
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open GlobalTheory.Mem.Chr hiding Ideles HChar atFin
open Formalism.L2.Host (HChar atFin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.DetLift

theorem det_mul_conj_det {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (ι : B →+* A) {n : ℕ} {g : GL (Fin n) A}
    (hg : g ∈ Formalism.UG.UJ σ ((1 : Matrix (Fin n) (Fin n) B).map ι)) :
    (g : Matrix (Fin n) (Fin n) A).det * σ (g : Matrix (Fin n) (Fin n) A).det = 1 := by
  have h : Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * (1 : Matrix (Fin n) (Fin n) B).map ι * (g : Matrix (Fin n) (Fin n) A) =
      (1 : Matrix (Fin n) (Fin n) B).map ι := hg
  rw [Matrix.map_one _ (map_zero ι) (map_one ι), mul_one] at h
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, Matrix.det_one] at h2
  rw [mul_comm, RingHom.map_det]
  exact h2

theorem exists_isDetLift : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (g : GL (Fin n) (AfE H.F H.E)), g ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → ∃ a : Ideles H.E, IsDetLift (host_cmData R H) g a := by
  intro R H n g hg
  have hr := (DetClass.exists_detClass R H (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
    (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).1
  have hd : Matrix.GeneralLinearGroup.det g ∈ U1 (host_cmData R H).sig :=
    Units.ext (det_mul_conj_det _ _ hg)
  obtain ⟨x, hx⟩ := hr.ge hd
  obtain ⟨a, rfl⟩ := finAf_surjective H.F H.E x
  exact ⟨a, hx⟩

end GlobalTheory.Mem.DetLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurPairingInvariantUnderStandardGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurPairingInvariantUnderStandardGroup
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.SchurPairingInvariant

theorem left_inv_of_mem_Minf {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {n : ℕ}
    {P : principalLevelFrame.RowPsi V n} {x : MMap M} (hx : x ∈ principalLevelFrame.Minf θ P M) (v : M.Vec) :
    ∀ γ ∈ GQ V, ∀ g, x v (γ * g) = x v g := by
  unfold principalLevelFrame.Minf at hx
  refine Submodule.iSup_induction _ (motive := fun z : MMap M => ∀ γ ∈ GQ V, ∀ g, z v (γ * g) = z v g) hx ?_ ?_ ?_
  · intro N z hz
    exact (PeterssonHilbertSpace.mult_cont_left M θ _ _ hz v).2
  · intro γ _ g
    rfl
  · intro z w hz hw γ hγ g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hz γ hγ g, hw γ hγ g]

theorem ipM_congr_of_iff {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} {T T' U U' : MMap M} (h : ∀ c, IsMultIP M μ 𝓕 T T' c ↔ IsMultIP M μ 𝓕 U U' c) :
    ipM M μ 𝓕 T T' = ipM M μ 𝓕 U U' := by
  have e : IsMultIP M μ 𝓕 T T' = IsMultIP M μ 𝓕 U U' := funext fun c => propext (h c)
  unfold ipM
  rw [e]

theorem ipM_actM : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurAll D → V.SigOK → IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (h : Formalism.AUTREP.GAf D.host.E n), ∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ipM M μ 𝓕 (principalLevelFrame.actM P M h x) (principalLevelFrame.actM P M h y) = ipM M μ 𝓕 x y := by
  intro D V S θ M n P μ 𝓕 _ _ _ hμ h𝓕 h x hx y hy
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  apply ipM_congr_of_iff
  intro c
  have key : ∀ v v' : M.Vec, _ := fun v v' =>
    GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun g => star (x v g) * y v' g) (P.ψ h) h𝓕
      (fun γ hγ g => by simp only [left_inv_of_mem_Minf hx v γ hγ g, left_inv_of_mem_Minf hy v' γ hγ g])
  unfold IsMultIP
  simp only [principalLevelFrame.actM_apply]
  constructor
  · intro H v v'
    obtain ⟨k1, k2⟩ := key v v'
    exact ⟨k1.2 (H v v').1, k2 ▸ (H v v').2⟩
  · intro H v v'
    obtain ⟨k1, k2⟩ := key v v'
    exact ⟨k1.1 (H v v').1, k2.trans (H v v').2⟩

end GlobalTheory.SchurPairingInvariant
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurPairingInvariantUnderStandardGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_pairing_invariant_under_standard_group : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurAll D → V.SigOK → IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (h : Formalism.AUTREP.GAf D.host.E n), ∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ipM M μ 𝓕 (principalLevelFrame.actM P M h x) (principalLevelFrame.actM P M h y) = ipM M μ 𝓕 x y := by
  exact @GlobalTheory.SchurPairingInvariant.ipM_actM
end
end
