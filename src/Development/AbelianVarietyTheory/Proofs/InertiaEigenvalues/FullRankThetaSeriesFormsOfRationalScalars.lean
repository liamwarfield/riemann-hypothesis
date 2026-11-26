module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodModelVectorEqClassSumBaseLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsClassSumsOfProjectedLiftRange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormReadingEqGoodModelVectorEvaluation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormReadingEqGoodModelVectorEvaluation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SeriesTie.ModelGood

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)

def jH (j : Fin D.R.m) : S.WL ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H where
  toFun x := (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x)
  map_zero' := by rw [map_zero, map_zero]
  map_add' x y := by rw [map_add (f := _), map_add (f := _)]

theorem jH_smul (j : Fin D.R.m) (c : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    jH YS j (c • x) = D.what₂.embLL c • jH YS j x := by
  change (Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (c • x)) = _
  rw [map_smul, map_smulₛₗ, show sg0 D A3.A c = D.what₂.embLL c from
    congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)]
  rfl

section Read

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

def evH : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1) →+ (Rl.HW j (sg0 D A3.A)).H :=
  TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ρ.e i b a)).comp
        ((jH YS j).comp (S.A ((j : ℕ) + 1)).WK.subtype.toAddMonoidHom)
      map_zero' := by ext; simp [show ρ.e i b (0 : NX.KB S i b) = 0 from map_zero _]
      map_add' := fun x y => by
        ext; simp [show ρ.e i b (x + y : NX.KB S i b) = ρ.e i b x + ρ.e i b y from map_add _ _ _, add_smul] }
    fun c a f => by
      change ρ.e i b (sideEmb D.ntw i b (S.kKs c) * (show FractionRing (D.ntw.O i) from a)) • jH YS j (Subtype.val f) =
        ρ.e i b a • jH YS j (c • Subtype.val f)
      rw [← algebraMap_smul D.what₂.LL c, jH_smul, map_mul, hρ.e_LL0, smul_smul, mul_comm, ← S.kKs_spec]
      rfl

theorem evH_tmul (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (a ⊗ₜ f) = ρ.e i b a • jH YS j (Subtype.val f) := rfl

theorem evK_eq (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b t = (Rl.HW j (sg0 D A3.A)).e (evH YS hρ i j b t) (v₀ j _) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]; rfl
  | tmul a f => rw [evK_tmul, evH_tmul, map_smul]; rfl

theorem evH_smul (c : NX.KB S i b) (t : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    evH YS hρ i j b (c • t) = ρ.e i b c • evH YS hρ i j b t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul a f =>
    rw [TensorProduct.smul_tmul', evH_tmul, evH_tmul, smul_smul]
    exact congrArg (· • _) (map_mul (ρ.e i b) c a)

def mv (y : D.nexp.Fm i ((j : ℕ) + 1) b) : (Rl.HW j (sg0 D A3.A)).H :=
  evH YS hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 y)

theorem mv_act (hU : Rl.toRealDat.LUnif) (g : G0g D.nd) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (D.nexp.actG i _ b g y)) =
      postOn _ (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g))
        ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  unfold mv
  rw [YS.act]
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 y = t
  induction t using TensorProduct.induction_on with
  | zero =>
    erw [LinearEquiv.map_zero]
    simp only [map_zero]
    exact (congrArg (Rl.HW j (sg0 D A3.A)).e ((evH YS hρ i j b).map_zero)).trans (map_zero _)
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, map_add, hy, hz, map_add, map_add, map_add]
  | tmul a f0 =>
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evH_tmul, evH_tmul]
    have hgeq : Rl.eG ((YS.fi j).eG (S.eG.symm g)) = cG.symm g := by
      have h0 := YS.geq j (S.eG.symm g)
      rw [MulEquiv.apply_symm_apply] at h0
      exact ((MulEquiv.symm_apply_eq cG).2 h0.symm).symm
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
    change (Rl.HW j (sg0 D A3.A)).e (ρ.e i b _ • (Rl.FW j).j (sg0 D A3.A)
      ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)))) = _
    rw [map_smul, map_smul, map_smul, (YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi, hgeq, smul_smul]
    congr 1
    erw [map_mul, map_inv₀, he, hs]
    field_simp

theorem mv_smul (c : FractionRing (D.ntw.O i)) (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (c • y) = ρ.e i b c • mv YS hρ i j b y := by
  unfold mv
  rw [map_smul]
  exact evH_smul YS hρ i j b c _

theorem mv_sum {ι : Type} (s : Finset ι) (y : ι → D.nexp.Fm i ((j : ℕ) + 1) b) :
    mv YS hρ i j b (∑ k ∈ s, y k) = ∑ k ∈ s, mv YS hρ i j b (y k) := by
  unfold mv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact map_sum (evH YS hρ i j b) _ _

theorem postOn_eWf_sum (σ : D.what₂.LL →+* ℂ) (M : MMap (Rl.MW j σ)) :
    postOn (Rl.MW j σ) (Rl.toRealDat.eWf j σ) M = ∑ γ : Γ, RealDat.eC (A := A3.A) σ γ •
      postOn (Rl.MW j σ) (actL (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG γ)) M := by
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, postOn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.smul_apply]
  rfl

theorem mv_eG (hU : Rl.toRealDat.LUnif)
    (hid : ∀ γ : Γ, D.what₂.embLL ((idemOf A3.A.X).coeff γ) = D.ntypes.e0.coeff ((Rl.eG.trans cG) γ))
    (y : D.nexp.Fm i ((j : ℕ) + 1) b) :
    (Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y)) =
      postOn _ (Rl.toRealDat.eWf j (sg0 D A3.A)) ((Rl.HW j (sg0 D A3.A)).e (mv YS hρ i j b y)) := by
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Γ (Rl.eG.trans cG).toEquiv
  have h1 : Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b y = ∑ g, (D.nexp.eAlg i b).coeff g • D.nexp.actG i _ b g y := by
    unfold Formalism.MainNotions.IntegralHeckeForms.eG
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype]
    · rw [LinearMap.sum_apply]; rfl
    · intro; exact zero_smul _ _
  have hc : ∀ g, ρ.e i b ((D.nexp.eAlg i b).coeff g) = D.ntypes.e0.coeff g := fun g => by
    have h : (D.nexp.eAlg i b).coeff g = NX.readLL0 S i b (D.nexp.eLL0 g) := by rw [D.nexp.eAlg_def]; rfl
    rw [h]
    exact (hρ.e_LL0 i b _).trans (D.nStage_trivialCharacter_coeff_eq g)
  have hs : sg0 D A3.A = D.what₂.embLL := GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL Rl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, mv_sum, map_sum, postOn_eWf_sum]
  refine (Fintype.sum_equiv (Rl.eG.trans cG).toEquiv _ _ fun γ => ?_).symm
  rw [mv_smul, map_smul, mv_act YS hρ i j b hU, hc]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  congr 1
  exact (congrArg (fun f : D.what₂.LL →+* ℂ => f ((idemOf A3.A.X).coeff γ)) hs).trans (hid γ)

end Read
end GlobalTheory.SeriesTie.ModelGood

open GlobalTheory.SeriesTie.ModelGood in
theorem GlobalTheory.SeriesTie.rd_good_model : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∃ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      Y.Z.rd i j b x = (Y.Z.ν i j b)⁻¹ • (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) := by
  intro D X E Y i j b x hx
  obtain ⟨f, -, rfl⟩ := hx
  have hidem : ∀ z, Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b z) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j : ℕ) + 1) b z :=
    fun z => by rw [← Module.End.mul_apply, Formalism.MainNotions.IntegralHeckeForms.eG, ← map_mul, D.nexp.eAlg_idem]
  refine ⟨mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f), ⟨?_, ?_⟩, ?_⟩
  · have h := LinearMap.mem_range_self (X.R.HW j (sg0 D X.A3.A)).e
      (mv Y.YS Y.Z.good i j b (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i _ b f))
    rw [(X.char.models.HW j _).2.1] at h
    exact h
  · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply]
    rw [← mv_eG Y.YS Y.Z.good i j b X.unif X.idem, hidem]
  · change (Y.Z.ν i j b)⁻¹ • evK Y.YS X.geo.v₀ Y.Z.good i j b _ = _
    exact congrArg _ (evK_eq Y.YS Y.Z.good i j b X.geo.v₀ _)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormReadingEqGoodModelVectorEvaluationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_form_reading_eq_good_model_vector_evaluation : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∃ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      Y.Z.rd i j b x = (Y.Z.ν i j b)⁻¹ • (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) := by
  first | exact @GlobalTheory.SeriesTie.rd_good_model | exact GlobalTheory.SeriesTie.rd_good_model | (intros; apply GlobalTheory.SeriesTie.rd_good_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypeFormReadingRightTranslateLift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypeFormReadingRightTranslateLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TypeRead

theorem actG_eG (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (u : G0g D.nd) (y : D.nexp.Fm i j b) :
    D.nexp.actG i j b u (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b y) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b (D.nexp.actG i j b u y) := by
  have h := congrArg (fun z => MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) z y)
    (D.nexp.eAlg_central i b (MonoidAlgebra.single u 1))
  simp only [map_mul, MonoidAlgebra.lift_single, one_smul, Module.End.mul_apply] at h
  exact h.symm

theorem finite_group_acts_on_good_type_form_by_character (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (x : D.nexp.Fm i j b) (hx : x ∈ V0 D.nexp i j b)
    (u : G0g D.nd) (hu : u ∈ D.nexp.U) :
    D.nexp.actG i j b u x = ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x := by
  obtain ⟨f, hf, rfl⟩ := hx
  have hf' := (Submodule.mem_iInf _).1 hf ⟨u, hu⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf'
  rw [actG_eG]
  change Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b ((D.nexp.actG i j b (⟨u, hu⟩ : D.nexp.U) : _ ≃ₗ[_] _) f) = _
  erw [hf']
  simp

end GlobalTheory.TypeRead


open GlobalTheory.TypeRead in
theorem GlobalTheory.TypeRead.rd_mul_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  intro D X E Y i j b x hx u hu κ hκ g
  have hA : ActRead (Y.Z.rd i j b) :=
    actRead_realRd D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _ Y.Z.pin X.unif
      X.char.models.HW
  rw [← hA u κ hκ x g, finite_group_acts_on_good_type_form_by_character D i _ b x hx u hu, map_smulₛₗ]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypeFormReadingRightTranslateLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_type_form_reading_right_translate_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  first | exact @GlobalTheory.TypeRead.rd_mul_lift | exact GlobalTheory.TypeRead.rd_mul_lift | (intros; apply GlobalTheory.TypeRead.rd_mul_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsClassSumsOfProjectedLiftRange
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.RankOnto

theorem sumOnto_of_goodRange : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) → ∀ i, BaseTup Y i → SumOnto Y.Z.rd i := by
  intro D X E Y hG i hB j b x hx
  obtain ⟨w, hw, hrd⟩ := GlobalTheory.T.good_form_reading_eq_good_model_vector_evaluation D X E Y i j b x hx
  have hν : Y.Z.ν i j b ≠ 0 := (Y.Z.scalar i j b).ne
  have hT := GlobalTheory.T.good_type_form_reading_right_translate_lift D X E Y i j b x hx
  have hφ : (X.R.HW j (Formalism.IndefR.Links.sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ν i j b • Y.Z.rd i j b x := by
    rw [hrd, smul_smul, mul_inv_cancel₀ hν, one_smul]
  obtain ⟨F, hF, hsum⟩ := GlobalTheory.T.goodModelVector_eq_classSum_baseLevel D X E Y hG i hB j b w hw (fun u hu κ hκ g => by
    rw [hφ, Pi.smul_apply, Pi.smul_apply, hT u hu κ hκ g, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨(Y.Z.ν i j b)⁻¹ • F, Submodule.smul_mem _ _ hF, ?_⟩
  rw [map_smul, ← hsum, hrd]

end GlobalTheory.RankOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsClassSumsOfProjectedLiftRangeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForms_classSums_of_projectedLift_range : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) → ∀ i, BaseTup Y i → SumOnto Y.Z.rd i := by
  first | exact @GlobalTheory.RankOnto.sumOnto_of_goodRange | exact GlobalTheory.RankOnto.sumOnto_of_goodRange | (intros; apply GlobalTheory.RankOnto.sumOnto_of_goodRange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AveragedSeriesFullRankOfComplexSpanGood
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AveragedSeriesFullRankOfComplexSpanGood
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.RankDescent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem charZero_frac (i : X.Tw) : CharZero (FractionRing (X.O i)) :=
  (RingHom.charZero_iff ((IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
      (L := FractionRing (X.O i)) (X.O_inj i)).comp (X.emb0 i)).injective).1 inferInstance

theorem eG_eG (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b (Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x) = Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x := by
  have h := congrArg (MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b))) (Y.eAlg_idem i b)
  rw [map_mul] at h
  exact LinearMap.congr_fun h x

theorem good_idempotent_fixes_mem_good_type_space (i : X.Tw) (j : ℕ) (b : Bool) {x : Y.Fm i j b} (hx : x ∈ V0 Y i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x = x := by
  obtain ⟨y, -, rfl⟩ := hx
  exact eG_eG Y i j b y


open Formalism.MainNotions.IntegralHeckeForms in
theorem AO_eq (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • eG Y i j b x := by
  show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x = _
  rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), algebraMap_smul]


open Formalism.MainNotions.IntegralHeckeForms in
theorem thetaSeries_mem_goodTypeForms (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (a : Y.Dat i j b) (ha : a ∈ E.Dat0 i j b) :
    Y.th i j b a ∈ Fm0 Y i j b := by
  simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u
  have := E.theta_base_equivariant i j b a ha u
  simp [this]


open Formalism.MainNotions.IntegralHeckeForms in
theorem AO_Th_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) :
    ∀ x ∈ (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b), x ∈ V0 Y i j b := by
  rintro _ ⟨y, hy, rfl⟩
  rw [AO_eq]
  refine Submodule.smul_mem _ _ ⟨y, ?_, rfl⟩
  refine (Submodule.span_le (p := (Fm0 Y i j b).restrictScalars (X.O i))).2 ?_ hy
  rintro _ ⟨a, ha, rfl⟩
  exact thetaSeries_mem_goodTypeForms Y E i j b a ha


open Formalism.MainNotions.IntegralHeckeForms in
theorem fullRk_of_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool)
    (h : V0 Y i j b ≤ Submodule.span (FractionRing (X.O i)) (eG Y i j b '' (Y.th i j b '' E.Dat0 i j b))) :
    FullRk Y E i j b (SgJ Y E i j b) := by
  haveI := charZero_frac (X := X) i
  have hc : ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) ≠ 0 := Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'
  refine ⟨subset_rfl, AO_Th_le Y E i j b, le_antisymm (Submodule.span_le.2 (AO_Th_le Y E i j b)) (h.trans ?_)⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  have e1 : eG Y i j b (Y.th i j b a) = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i))⁻¹ • AO Y i j b (Y.th i j b a) := by
    rw [AO_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨a, ha, rfl⟩, rfl⟩)

section Descent

variable {ρ : Setup X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}

theorem rd_mem_span (rd : Rd ρ Y i j b) (S : Set (Y.Fm i ((j : ℕ) + 1) b)) {y : Y.Fm i ((j : ℕ) + 1) b}
    (hy : y ∈ Submodule.span (FractionRing (X.O i)) S) : rd y ∈ Submodule.span ℂ (rd '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem mem_span_of_faithful {rd : Rd ρ Y i j b} (hf : Faithful rd) (S : Set (Y.Fm i ((j : ℕ) + 1) b))
    {x : Y.Fm i ((j : ℕ) + 1) b} (hx : rd x ∈ Submodule.span ℂ (rd '' S)) :
    x ∈ Submodule.span (FractionRing (X.O i)) S := by
  set W := Submodule.span (FractionRing (X.O i)) S
  by_contra hxW
  let bW := Module.finBasis (FractionRing (X.O i)) W
  let v : Fin (Module.finrank (FractionRing (X.O i)) W) → Y.Fm i ((j : ℕ) + 1) b := fun k => (bW k : Y.Fm i ((j : ℕ) + 1) b)
  have hv : LinearIndependent (FractionRing (X.O i)) v := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span (FractionRing (X.O i)) (Set.range v) = W := by
    have := congrArg (Submodule.map W.subtype) bW.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hli : LinearIndependent (FractionRing (X.O i)) (Fin.cons x v : Fin _ → Y.Fm i ((j : ℕ) + 1) b) :=
    linearIndependent_finCons.2 ⟨hv, by rw [hspan]; exact hxW⟩
  have hC := hf _ _ hli
  have hC' : LinearIndependent ℂ (Fin.cons (rd x) (fun k => rd (v k)) : Fin _ → (GA D (Wc D j) → ℂ)) := by
    convert hC using 1
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  refine (linearIndependent_finCons.1 hC').2 ?_
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨s, hs, rfl⟩
  have hsW : s ∈ Submodule.span (FractionRing (X.O i)) (Set.range v) := by
    rw [hspan]; exact Submodule.subset_span hs
  have := rd_mem_span Y rd _ hsW
  rw [← Set.range_comp] at this
  exact this

end Descent

theorem fullRk_of_spanGood : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), Comparison₂ hρ rd → (∀ i j b, Faithful (rd i j b)) → ∀ (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw), (∀ j b, RatBase (rd i j b)) → (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b) → SpanGood rd i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro D ρ hρ rd T hF E i hR hall hS j hj b
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine fullRk_of_le D.nexp E i _ b ?_
  intro x hx
  have h1 : rd i j' b x ∈ Submodule.span ℂ (rd i j' b '' (D.nexp.th i _ b '' E.Dat0 i _ b)) := by
    refine Submodule.span_mono ?_ (hS j' b x hx)
    rintro _ ⟨s, h, P, hd, rfl⟩
    obtain ⟨d, -, hc, hp⟩ := (T i j' b).dat_onto s h P hd (hR j' b s h P hd)
    refine ⟨D.nexp.th i _ b d, ⟨d, hall _ hj b d, rfl⟩, ?_⟩
    rw [(T i j' b).th_eq d, hc, hp]
  have h2 := mem_span_of_faithful D.nexp (hF i j' b) _ h1
  rw [← good_idempotent_fixes_mem_good_type_space D.nexp i _ b hx]
  have h3 := Submodule.mem_map_of_mem (f := Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j' : ℕ) + 1) b) h2
  rwa [Submodule.map_span] at h3

end GlobalTheory.RankDescent

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AveragedSeriesFullRankOfComplexSpanGoodStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.averaged_series_full_rank_of_complex_span_good : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), Comparison₂ hρ rd → (∀ i j b, Faithful (rd i j b)) → ∀ (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw), (∀ j b, RatBase (rd i j b)) → (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b) → SpanGood rd i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  first | exact @GlobalTheory.RankDescent.fullRk_of_spanGood | exact GlobalTheory.RankDescent.fullRk_of_spanGood | (intros; apply GlobalTheory.RankDescent.fullRk_of_spanGood <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullRankThetaSeriesFormsOfRationalScalars
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.MainNotions.IntegralHeckeForms
open Formalism.IndefR.Links
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TieRank
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin
variable {O O' V : Type} [CommRing O] [IsDomain O] [CommRing O'] [Algebra O O'] [AddCommGroup V]
  [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]


end Lin

section Onto
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

end Onto

section Comparison₂
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Comparison₂

section Tie2
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Tie2

section Main
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} {YS : NX.NExpRealS Rl cG S}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

open GlobalTheory.SeriesTie

end Main

section Target
open GlobalTheory.TwInputs GlobalTheory.SeriesTie Formalism.MainNotions

theorem faithful_serSide {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m)
    (b : Bool) : Faithful (Y.Z.rd i j b) :=
  realRd_faithful D X.Γ X.Pl0 X.I0 X.T X.A3 _ X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b (Y.Z.ν i j b)
    (Y.Z.scalar i j b).ne X.unif X.char.models.HW (Y.Z.vec j) ((GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).1 _ (Nat.le_add_left _ _) j.2)

theorem rank_of_ties : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ i,
    BaseTup Y i → (∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b,
    FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro hP D X E Y i hB hR
  have hG : ∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t :=
    GlobalTheory.AdSpan.goodRangeAt X.R.toRealDat hP X.size X.char.lev X.char.grp.record X.char.fam X.char.models X.char.thP
  exact GlobalTheory.T.averaged_series_full_rank_of_complex_span_good D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.tie (faithful_serSide X Y) E i (fun j b => (Y.Z.rat (hR j b)).1)
    (fun j hj b a => Y.all i j hj b a) (GlobalTheory.T.goodForms_spanned_by_thetaSeries_of_classSums D Y.Z.ρ Y.Z.good Y.Z.rd i (GlobalTheory.T.goodForms_classSums_of_projectedLift_range D X E Y hG i hB))

end Target

end GlobalTheory.TieRank

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullRankThetaSeriesFormsOfRationalScalarsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullRank_thetaSeries_forms_of_rational_scalars : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ i, BaseTup Y i → (∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  first | exact @GlobalTheory.TieRank.rank_of_ties | exact GlobalTheory.TieRank.rank_of_ties | (intros; apply GlobalTheory.TieRank.rank_of_ties <;> assumption)
end
