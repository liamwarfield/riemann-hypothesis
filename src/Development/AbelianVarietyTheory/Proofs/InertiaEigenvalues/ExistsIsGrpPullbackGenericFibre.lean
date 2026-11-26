module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsGrpPullbackGenericFibre
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

noncomputable section

open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericFibreUnif

theorem exists_isGrpPullback_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (χ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t) (z : Sp (FractionRing R) ⟶ Xo.XF c), z ≫ Y.j = jK R ≫ χ → letI := H.starRing; ∃ ψ : P.A.A.left ⟶ Y.oF.t.G.left, IsGrpPullback P.A.A Y.oF.t.G z ψ ∧ LBIso P.A.L (Y.oF.t.PP.L.pull ψ) ∧ (∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ = ψ ≫ (Y.oF.t.act.act a).left) ∧ ψ ≫ Y.m.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y R _ _ I χ t m P z hz
  letI := H.starRing
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  set k : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hk
  have gpG : IsGrpPullback P.A.A t.G (jK R) k :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  have n₀ : IsGrpPullback P.A.A Y.t.G (jK R ≫ χ) (k ≫ m.φ) := gpG.comp m.cart
  have hw : (k ≫ m.φ) ≫ Y.t.G.hom = (P.A.A.hom ≫ z) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    refine n₀.1.w.trans ?_
    rw [← hz, Category.assoc]; rfl
  let ψ : P.A.A.left ⟶ Y.oF.t.G.left := Y.m.cart.1.lift (k ≫ m.φ) (P.A.A.hom ≫ z) hw
  have hψ₁ : ψ ≫ Y.m.φ = k ≫ m.φ := Y.m.cart.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ Y.oF.t.G.hom = P.A.A.hom ≫ z := Y.m.cart.1.lift_snd _ _ _
  have n : IsGrpPullback P.A.A Y.t.G (z ≫ (Y.jQ ≫ pullback.fst _ _)) (ψ ≫ Y.m.φ) :=
    n₀.congr hz.symm hψ₁.symm
  have cart : IsGrpPullback P.A.A Y.oF.t.G z ψ := Y.m.cart.cancel n hψ₂
  have actA : ∀ x, (P.oA.act x).left ≫ k = k ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [hk, ← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have B₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull k) :=
    LBIso.chartPull (chartPullSame P.A.L (fun _ => 𝟙 _) (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left
        (fun _ => hgi.symm))
      (chartPullSame P.U.LG.L (fun _ => k) (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left
        (fun _ => rfl)) P.U.ext
  have B₁' : LBIso P.A.L (t.PP.L.pull k) := by
    rw [← P.bundle]
    exact LBIso.chartPull (chartPullUnpull P.A.L (𝟙 _) rfl) (chartPullId _) B₁
  obtain ⟨w₂, -, g₂, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have B₂ : LBIso (t.PP.L.pull k) (Y.t.PP.L.pull (ψ ≫ Y.m.φ)) :=
    LBIso.chartPull (chartPullPull t.PP.L k k rfl)
      (chartPullSame Y.t.PP.L (fun _ => ψ ≫ Y.m.φ) (fun _ => m.φ) _ k (fun _ => hψ₁.trans (Category.assoc _ _ _)))
      ⟨w₂, g₂⟩
  obtain ⟨w₃, -, g₃, -⟩ := rigIso_congr rfl Y.m.cm Y.m.lin rfl rfl
  have B₃ : LBIso (Y.oF.t.PP.L.pull ψ) (Y.t.PP.L.pull (ψ ≫ Y.m.φ)) :=
    LBIso.chartPull (chartPullPull Y.oF.t.PP.L ψ ψ rfl)
      (chartPullSame Y.t.PP.L (fun _ => ψ ≫ Y.m.φ) (fun _ => Y.m.φ) _ ψ (fun _ => rfl)) ⟨w₃, g₃⟩
  have BL : LBIso P.A.L (Y.oF.t.PP.L.pull ψ) :=
    LBIso.trans P.A.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB Y.oF.t.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) B₁' B₂) (LBIso.symm B₃)
  refine ⟨ψ, cart, BL, fun a => ?_, hψ₁.trans (Category.assoc _ _ _)⟩
  apply Y.m.cart.1.hom_ext
  · calc ((P.oA.act a).left ≫ ψ) ≫ Y.m.φ = (P.oA.act a).left ≫ k ≫ m.φ := by rw [Category.assoc, hψ₁]
      _ = k ≫ m.φ ≫ (Y.t.act.act a).left := by rw [← Category.assoc, actA, Category.assoc, m.act a]
      _ = (ψ ≫ (Y.oF.t.act.act a).left) ≫ Y.m.φ := by
        rw [Category.assoc ψ, Y.m.act a, ← Category.assoc ψ, hψ₁]; exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (P.oA.act a), Category.assoc, Over.w (Y.oF.t.act.act a), hψ₂]

end GlobalTheory.GenericFibreUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQVal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQVal
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

noncomputable section

namespace GlobalTheory.TauTwist

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out

theorem psiUnitOn_rescale_of_qVal : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V) (ϖ : T.V), Irreducible ϖ → ∀ (y : D.X) (n : ℤ), QVal D ϖ y n → ∀ q : D.X → (FractionRing T.V)ˣ, (q y : FractionRing T.V) = algebraMap T.V (FractionRing T.V) ϖ ^ (-n) → PsiUnitOn (GlobalTheory.TauTwist.rescale D q) y Set.univ := by
  intro T D ϖ hϖ y n hQ q hq j V hV hU hc h
  obtain ⟨e, -, c, ⟨u, hu⟩, hC⟩ := genHasVal_units _ _ _ _ _ _ hQ
  obtain ⟨C, hCv, hCt⟩ := hC j
  have hW : V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c y).left) j :=
    fun x hx => Set.mem_iInter.2 fun k => by cases k; exact hc hx
  have hπ : algebraMap T.V (FractionRing T.V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).mpr hϖ.ne_zero
  have hqc : (q y : FractionRing T.V) * c = algebraMap T.V (FractionRing T.V) (u : T.V) := by
    rw [hq, hu, ← _root_.mul_assoc, ← zpow_add₀ hπ, neg_add_cancel, zpow_zero, _root_.one_mul]
  have hconst : (res (X := Spec (CommRingCat.of (FractionRing T.V)))
      (le_top : LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j ≤ ⊤) (unitOn (q y))).val * C.val =
      (res (X := Spec (CommRingCat.of (FractionRing T.V))) le_top
        (unitOn (Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom u))).val := by
    rw [hCv]
    show ((Spec (CommRingCat.of (FractionRing T.V))).presheaf.map (homOfLE le_top).op).hom _ *
      ((Spec (CommRingCat.of (FractionRing T.V))).presheaf.map (homOfLE le_top).op).hom _ =
      ((Spec (CommRingCat.of (FractionRing T.V))).presheaf.map (homOfLE le_top).op).hom _
    rw [← map_mul]
    congr 1
    simp only [scal, unitOn, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.id_appTop]
    change (Scheme.ΓSpecIso (CommRingCat.of (FractionRing T.V))).inv.hom (q y : FractionRing T.V) *
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing T.V))).inv.hom c =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing T.V))).inv.hom (algebraMap T.V (FractionRing T.V) (u : T.V))
    rw [← map_mul, hqc]
  refine ⟨(res (le_top : V ≤ ⊤) (unitOn u)).val * (res hW (e.s j)).val, (Units.isUnit _).mul (Units.isUnit _), ?_⟩
  have hval : (((rescale D q).psi y).s j).val = (res (X := Spec (CommRingCat.of (FractionRing T.V)))
      (le_top : LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j ≤ ⊤)
        (unitOn (Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom u))).val *
      (res (wchart_le_preimage D.P.L (jK T.V) (fun _ => (D.c y).left) (fun _ => ptK (D.c y))
        (fun _ => QForm.ptK_eq D y) j) (pullU (jK T.V) _ (e.s j))).val := by
    show (HMul.hMul (α := (Γ(Spec (CommRingCat.of (FractionRing T.V)), LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j))ˣ)
      (β := (Γ(Spec (CommRingCat.of (FractionRing T.V)), LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j))ˣ)
      (res le_top (unitOn (q y))) ((D.psi y).s j)).val = _
    rw [hCt, ← _root_.mul_assoc, Units.val_mul, Units.val_mul, hconst]
  rw [hval]
  apply fn_ext
  intro x hx
  refine (gs_pull (𝟙 _) (jK T.V) x V hx _).trans (Eq.trans ?_ (gs_res (𝟙 _) x h hx _).symm)
  rw [gs_mul (𝟙 _ ≫ jK T.V) x V hx]
  refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (gs_mul (𝟙 _) x _ (h hx) _ _).symm
  · refine (gs_res _ x le_top hx _).trans (Eq.trans ?_ (gs_res _ x le_top (h hx) _).symm)
    exact (unitAt_val (𝟙 _ ≫ jK T.V) x u).symm.trans ((congrArg Units.val
      (unitAt_spMap (𝟙 _) (algebraMap T.V (FractionRing T.V)) x u)).trans (unitAt_val _ x _))
  · refine (gs_res _ x hW hx _).trans (Eq.trans ?_ (gs_res _ x _ (h hx) _).symm)
    exact (gs_pull (𝟙 _) (jK T.V) x _ (hW hx) _).symm

end GlobalTheory.TauTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQValStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiUnitOn_rescale_uniformizer_of_qVal : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V) (ϖ : T.V), Irreducible ϖ → ∀ (y : D.X) (n : ℤ), QVal D ϖ y n → ∀ q : D.X → (FractionRing T.V)ˣ, (q y : FractionRing T.V) = algebraMap T.V (FractionRing T.V) ϖ ^ (-n) → PsiUnitOn (GlobalTheory.TauTwist.rescale D q) y Set.univ := by
  first | exact @GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal | exact GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal | (intros; apply GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolys
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesMemOfFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesMemOfFinset
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.CoefField

theorem entries_mem_of_finset : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → ∃ S : Finset (Qbar l), ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, z ∈ K) → ∀ g s t, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ E Ω _ _ _ _ _ a ρ hρ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a ρ hρ
    ⟨⊥, inferInstance⟩
  haveI := L.2
  let B := Module.finBasis ℚ_[l] ↥L.1
  classical
  refine ⟨Finset.univ.image (fun i => ((B i : ↥L.1) : Qbar l)), fun K hK g s t => ?_⟩
  have key : ∀ x : ↥L.1, (x : Qbar l) ∈ K := by
    intro x
    have hx : x ∈ Submodule.span ℚ_[l] (Set.range B) := B.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => simpa using K.zero_mem
    | add y z _ _ hy hz => simpa using K.add_mem hy hz
    | smul c y _ hy => simpa using K.smul_mem hy (x := c)
  exact key ⟨_, hL g s t⟩

end GlobalTheory.CoefField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesMemOfFinsetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRep_entries_mem_of_finset : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → ∃ S : Finset (Qbar l), ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, z ∈ K) → ∀ g s t, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  first | exact @GlobalTheory.CoefField.entries_mem_of_finset | exact GlobalTheory.CoefField.entries_mem_of_finset | (intros; apply GlobalTheory.CoefField.entries_mem_of_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolys
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.FrobSysCoef

theorem main : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ ρ₀ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l),
      Continuous (fun g => ((ρ₀ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep ρ₀ ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ)
  · obtain ⟨ρ₀, hc₀, hs₀, hp₀⟩ := hex
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.galoisRep_entries_mem_of_finset l E Ω a ρ₀ hc₀
    refine ⟨S₀.image ι, fun K hK ρ hc hs hp => ?_⟩
    have hK' : ∀ z ∈ S₀, z ∈ K := fun z hz => by
      simpa using hK (ι z) (Finset.mem_image_of_mem _ hz)
    have hU' : ∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
        ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := fun σ hσ =>
      Polynomial.map_injective ι.toRingHom ι.injective ((hp₀ σ hσ).trans (hp σ hσ).symm)
    have hall := GlobalTheory.charpoly_eq_of_eqOn_dense _ _ hc₀ hc U hU hU'
    obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₀ ρ hs₀ hs hall
    refine ⟨Pm⁻¹, fun g s t => ?_⟩
    have : Pm⁻¹⁻¹ * ρ g * Pm⁻¹ = ρ₀ g := by
      rw [hPm g, inv_inv]; group
    rw [this]
    exact hS₀ K hK' g s t
  · refine ⟨∅, fun K _ ρ hc hs hp => ?_⟩
    exact absurd ⟨ρ, hc, hs, hp⟩ hex

end GlobalTheory.FrobSysCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolysStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  first | exact @GlobalTheory.FrobSysCoef.main | exact GlobalTheory.FrobSysCoef.main | (intros; apply GlobalTheory.FrobSysCoef.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDual1Dot
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.JumpDual

def matG {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

theorem isDual1_dot {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {k : ℕ} (T U : G →* Matrix (Fin k) (Fin k) LL)
    (hU : ∀ g, U g = ((cycLL PD LL g : LLˣ) : LL) • (T g⁻¹).transpose) :
    IsDual1 PD (matRep T) (matRep U) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (T g).mulVec x ⬝ᵥ ((U g).mulVec y) = ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [hU, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

theorem loc_cont (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (Br.loc D.nbr i w hw M) := by
  have hfc : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
    hM.comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact h1.matrix_map hfc

theorem loc_dual (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw (rDuO D.nd i r x) g =
      ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) •
        (Br.loc D.nbr i w hw (rTwO D.nd i r x) g⁻¹).transpose := by
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  let f := (D.nbr i w hw).toLL
  rw [← GlobalTheory.CycBridge.locChi_epsU D i w hw g]
  ext a b
  congr 1
  change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
    f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
  rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
  congr 1
  ring

theorem jump_dual : ∀ D : D7, DualJumpL D.loc → PotDRL D.loc → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ (x : ↥Xs) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ), IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rDuO D.nd i r x))) τ a ↔ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) τ (-a - 1) := by
  intro D hJ hP i r hr Xs w hw n hF x τ a
  obtain ⟨K', h, hN, hI, hS, Sig, Fr, -, -, -, -, hx⟩ := hF
  have hc := GlobalTheory.T.twisted_dual_families_continuous D i r hr x
  have cT := loc_cont D i w hw _ hc.1
  have cU := loc_cont D i w hw _ hc.2
  have hcr := (GlobalTheory.T.potentiallyCrystalline_module_eq_crystalline_restriction (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hI hS _
    (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))).2.1 (hx x).1
  have hdR := hP (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h
    (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cT) hcr
  exact hJ (D.nd.l i) (D.nbr i w hw).Kw (D.nbr i w hw).LL
    (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cT) (matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ cU)
    (dotProductBilin _ _) (isDual1_dot _ _ _ (loc_dual D i w hw r x)) hdR τ a

end GlobalTheory.JumpDual

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetPencilMemHeckeAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetPencilMemHeckeAlgebra
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem isHomogeneous_det_of_linear {σ R : Type} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) (h : ∀ i j, (M i j).IsHomogeneous 1) :
    M.det.IsHomogeneous n := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun τ _ => ?_
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => M (τ i) i) (fun _ => 1) (fun i _ => h (τ i) i)
  simpa using this

theorem coeff_aeval_of_isHomogeneous {R : Type} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin 2) R) (h : P.IsHomogeneous n) (j : ℕ) :
    (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1] P).coeff j =
      ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin 2)) n,
        if d 0 = j then AddMonoidAlgebra.coeff P d else 0 := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff]
  have hterm : ∀ d : Fin 2 →₀ ℕ,
      (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1]
        (MvPolynomial.monomial d (AddMonoidAlgebra.coeff P d))).coeff j =
        if d 0 = j then AddMonoidAlgebra.coeff P d else 0 := by
    intro d
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, eq_comm]
  simp_rw [hterm]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    have hd' : AddMonoidAlgebra.coeff P d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have := h hd'
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd]
    simp

theorem coeff_det_pencil_mem : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ a b : X → Matrix (Fin n) (Fin n) O, InRing T rep a → InRing T rep b → ∀ j : ℕ, (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) + (b x).map (Polynomial.C (R := O)))).coeff j) ∈ T := by
  intro Γ X O _ _ n T rep hT a b ha hb j
  set c : Fin 2 → X → Matrix (Fin n) (Fin n) O := ![a, b] with hc
  have hcR : ∀ k, InRing T rep (c k) := by
    intro k; fin_cases k
    · exact ha
    · exact hb
  have key := GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T rep hT 2 c hcR
  set P : X → MvPolynomial (Fin 2) O := fun x =>
    Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin 2) O) • (c k x).map MvPolynomial.C) with hP
  have hhom : ∀ x, (P x).IsHomogeneous n := by
    intro x
    refine isHomogeneous_det_of_linear _ fun i j => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
    simpa using (MvPolynomial.isHomogeneous_X O k).mul (MvPolynomial.isHomogeneous_C (Fin 2) (c k x i j))
  have hdet : ∀ x, Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) +
      (b x).map (Polynomial.C (R := O))) =
      MvPolynomial.aeval ![(Polynomial.X : Polynomial O), 1] (P x) := by
    intro x
    rw [hP, AlgHom.map_det]
    congr 1
    ext i j
    simp [hc, Fin.sum_univ_two, Matrix.map_apply]
  have hfun : (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) +
      (b x).map (Polynomial.C (R := O)))).coeff j) =
      ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin 2)) n,
        (fun x => if d 0 = j then AddMonoidAlgebra.coeff (P x) d else 0) := by
    funext x
    rw [hdet x, coeff_aeval_of_isHomogeneous _ (hhom x) j, Finset.sum_apply]
  rw [hfun]
  refine Subalgebra.sum_mem _ fun d _ => ?_
  by_cases hd : d 0 = j
  · simp only [hd, if_true]
    exact key d
  · simp only [hd, if_false]
    exact T.zero_mem

end GlobalTheory.SpanRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetPencilMemHeckeAlgebraStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_det_pencil_mem_heckeAlgebra : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ a b : X → Matrix (Fin n) (Fin n) O, InRing T rep a → InRing T rep b → ∀ j : ℕ, (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) + (b x).map (Polynomial.C (R := O)))).coeff j) ∈ T := by
  first | exact @GlobalTheory.SpanRing.coeff_det_pencil_mem | exact GlobalTheory.SpanRing.coeff_det_pencil_mem | (intros; apply GlobalTheory.SpanRing.coeff_det_pencil_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqBotOrTopOfSpanEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantAll
namespace GlobalTheory.InvariantBotOrTop

open Matrix

theorem invariant_all {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, (M g).map (algebraMap k K) *ᵥ x ∈ W) (A : Matrix (Fin r) (Fin r) k) :
    ∀ x ∈ W, A.map (algebraMap k K) *ᵥ x ∈ W := by
  have hA : A ∈ Submodule.span k (Set.range M) := by
    rw [hM]
    exact Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨g, rfl⟩ := hA
    exact hW g
  | zero =>
    intro x _
    rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
    exact W.zero_mem
  | add A B _ _ hA hB =>
    intro x hx
    rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]
    exact W.add_mem (hA x hx) (hB x hx)
  | smul c A _ hA =>
    intro x hx
    rw [Matrix.map_smul _ c (fun a => by rw [smul_eq_mul, map_mul, Algebra.smul_def])]
    first
      | rw [Matrix.smul_mulVec]
      | rw [Matrix.smul_mulVec_assoc]
    exact W.smul_of_tower_mem c (hA x hx)

theorem bot_or_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, (M g).map (algebraMap k K) *ᵥ x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)

  have he : ∀ i, (Pi.single i (1 : K) : Fin r → K) ∈ W := by
    intro i
    have h1 := invariant_all M hM W hW (Matrix.single i j 1) x hxW
    have h2 : (Matrix.single i j (1 : k)).map (algebraMap k K) *ᵥ x = x j • Pi.single i 1 := by
      ext a
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      by_cases hai : a = i
      · subst hai
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [Matrix.single_apply, hb, Ne.symm hb]) (by simp)]
        simp [Matrix.single_apply]
      · rw [Finset.sum_eq_zero (fun b _ => by simp [Matrix.single_apply, hai, Ne.symm hai])]
        simp [Pi.single_apply, hai]
    rw [h2] at h1
    have h3 := W.smul_mem (x j)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h3
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ i, y i • (Pi.single i (1 : K) : Fin r → K) := by
    ext a
    simp [Pi.single_apply]
  rw [hy]
  exact W.sum_mem fun i _ => W.smul_mem _ (he i)

theorem main : ∀ {Γ k K : Type} [inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K] {r : ℕ} (M : Γ → Matrix (Fin r) (Fin r) k), Submodule.span k (Set.range M) = ⊤ → ∀ (W : Submodule K (Fin r → K)), (∀ (g : Γ), ∀ x ∈ W, Matrix.mulVec (Matrix.map (M g) (⇑(Algebra.algebraMap k K) : k → K)) x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro Γ k K _ _ _ r M hM W hW
  exact bot_or_top M hM W hW

end GlobalTheory.InvariantBotOrTop
end

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.BurnsideIff

theorem eq_bot_or_top_of_span_eq_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (h : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, ((M g).map (algebraMap k K)).mulVec x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5; revert Γ k K h_3 h_4 h_5 r M h W hW; exact @_root_.GlobalTheory.InvariantBotOrTop.main)
  | exact @_root_.GlobalTheory.InvariantBotOrTop.main
  | exact _root_.GlobalTheory.InvariantBotOrTop.main
  | (apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantBotOrTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantBotOrTop.main ..)

end GlobalTheory.BurnsideIff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism

section SdClosed

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem lTo0_atTop {w : ℕ → Wq l a} : LTo0 l w ↔ ∀ r : ℕ, ∃ N, ∀ n ≥ N, (l : Wq l a) ^ r ∣ w n := by
  simp only [LTo0, Nat.cofinite_eq_atTop, eventually_atTop]

theorem sdSet_zero : (0 : ZMod a → K⟦X⟧) ∈ SdSet t K e :=
  ⟨0, fun r => Eventually.of_forall fun _ => dvd_zero _, fun τ n => by simp⟩

theorem sdSet_one : (1 : ZMod a → K⟦X⟧) ∈ SdSet t K e := by
  refine ⟨fun n => if n = 0 then 1 else 0, lTo0_atTop.2 fun r => ⟨1, fun n hn => ?_⟩, fun τ n => ?_⟩
  · rw [if_neg (by omega)]; exact dvd_zero _
  · rw [Pi.one_apply, coeff_one]
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]

theorem sdSet_neg {F : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) : -F ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨-w, fun r => (hw r).mono fun n hn => ?_, fun τ n => ?_⟩
  · simpa using hn
  · simp [hF τ n]

theorem sdSet_add {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F + G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  refine ⟨w + w', fun r => ((hw r).and (hw' r)).mono fun n hn => ?_, fun τ n => ?_⟩
  · exact dvd_add hn.1 hn.2
  · simp [mul_add, hF τ n, hG τ n]

theorem fact_div_dvd (e i j : ℕ) : (i / e).factorial * (j / e).factorial ∣ ((i + j) / e).factorial :=
  (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans
    (Nat.factorial_dvd_factorial (Nat.add_div_le_add_div i j e))

theorem sdSet_mul {F G : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) (hG : G ∈ SdSet t K e) :
    F * G ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  obtain ⟨w', hw', hG⟩ := hG
  let q : ℕ → ℕ → ℕ := fun i j => ((i + j) / e).factorial / ((i / e).factorial * (j / e).factorial)
  have hq : ∀ i j, ((i + j) / e).factorial = q i j * ((i / e).factorial * (j / e).factorial) := fun i j =>
    (Nat.div_mul_cancel (fact_div_dvd e i j)).symm
  refine ⟨fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, q p.1 p.2 • (w p.1 * w' p.2), ?_, fun τ n => ?_⟩
  · rw [lTo0_atTop] at hw hw' ⊢
    intro r
    obtain ⟨N, hN⟩ := hw r
    obtain ⟨N', hN'⟩ := hw' r
    refine ⟨N + N', fun n hn => Finset.dvd_sum fun p hp => ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [nsmul_eq_mul]
    apply Dvd.dvd.mul_left
    by_cases h1 : N ≤ p.1
    · exact (hN _ h1).mul_right _
    · exact (hN' _ (by omega)).mul_left _
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Pi.mul_apply, coeff_mul, Finset.mul_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [map_nsmul, map_nsmul, nsmul_eq_mul, map_mul, map_mul, ← hF τ p.1, ← hG τ p.2, ← hp, hq p.1 p.2]
      push_cast
      ring

theorem sd_sub_sdSet : ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  let S : Subring (ZMod a → K⟦X⟧) :=
    { carrier := SdSet t K e
      zero_mem' := sdSet_zero t e
      one_mem' := sdSet_one t e
      add_mem' := fun hF hG => sdSet_add t e hF hG
      mul_mem' := fun hF hG => sdSet_mul t e hF hG
      neg_mem' := fun hF => sdSet_neg t e hF }
  intro F hF
  exact (Subring.closure_le.2 (fun x hx => hx) : Sd t K e ≤ S) hF

end SdClosed

theorem sdSet_closed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t
  exact sd_sub_sdSet t e

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesSubringEqGeneratorSetStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_sdSet_of_mem_sd : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ Sd t K e, F ∈ SdSet t K e := by
  first | exact @GlobalTheory.CrysPrism.sdSet_closed | exact GlobalTheory.CrysPrism.sdSet_closed | (intros; apply GlobalTheory.CrysPrism.sdSet_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HatOfInvariantSeries
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.TwoMaps

theorem toHatS_eq_of_hat : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (f : invL l (S O K e)) (x : Ahat O K l e), hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) x → toHatS O K l e f = x := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ _ f x hfx
  let fR : Rpi O K l e := ⟨(f : K⟦X⟧), invL_S_le_Rpi l e f.2⟩
  have h0 : hat O l e (fR : K⟦X⟧) = algebraMap _ (AhatE O K l e) (toHat O K l e fR) := hat_coe_Rpi l e fR
  have h1 : toHatS O K l e f = toHat O K l e fR := rfl
  have h2 : hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) (toHatS O K l e f) := by
    rw [h1]; exact h0
  rw [h2] at hfx
  have hE0 : EIn l e (invL l (A O K)) ≠ 0 := fun h => by
    have h3 : E K l e = 0 := congrArg Subtype.val h
    exact (isUnit_E (K := K) l e).ne_zero h3
  have hreg : ∀ y : Ahat O K l e, Ehat O K l e * y = 0 → y = 0 := fun y hy =>
    GlobalTheory.MemLoc.FilPrincipal.regular_of_isDomain rfl hE0 y hy
  have hmem : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) := by
    rw [mem_nonZeroDivisors_iff]
    constructor <;> intro y hy <;> apply hreg <;> first | exact hy | (rw [mul_comm]; exact hy)
  have hinj : Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
    IsLocalization.injective (M := Submonoid.powers (Ehat O K l e)) (AhatE O K l e) (Submonoid.powers_le.2 hmem)
  exact hinj hfx

theorem iSD_eq_of_mem_invL_A : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) [CompleteSpace K] (f : invL l (S O K e)), (f : K⟦X⟧) ∈ invL l (A O K) → ϖ.iSD O K f = ϖ.iHat O K (toHatS O K l e f) := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ _ f hf
  obtain ⟨n, hn⟩ := hf
  have hlu : IsUnit ((l : OD l O) ^ n) := isUnit_l_OD.pow n
  have hg : ((l : A O K) : K⟦X⟧) ^ n * (f : K⟦X⟧) ∈ S O K e := A_le_S l e hn
  have e1 : (l : invL l (S O K e)) ^ n * f = algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩ :=
    Subtype.ext (by simp)
  have e2 : toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩) =
      ofA O K l e ⟨_, hn⟩ := toHat_eq_ofAl l e rfl
  refine hlu.mul_left_cancel ?_
  have h3 := congrArg (ϖ.iSD O K) e1
  have h4 := congrArg (fun y => ϖ.iHat O K (toHatS O K l e y)) e1
  simp only [map_mul, map_pow, map_natCast] at h3 h4
  rw [h3, h4, e2, ϖ.iHat_ofA O K]
  refine (ϖ.iSD_of_mem O K hg _).trans ?_
  rw [ϖ.iS_of_mem O K hn, crisToOD_toOCr]

theorem iSD_eq_iHat_of_hat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K], ∀ (f : invL l (S O K e)) (x : Ahat O K l e), hat O l e (f : K⟦X⟧) = algebraMap _ (AhatE O K l e) x → ϖ.iSD O K f = ϖ.iHat O K x := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ f x hfx
  obtain rfl := toHatS_eq_of_hat l e O K ϖ f x hfx
  have hlu : IsUnit (l : OD l O) := isUnit_l_OD
  set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ

  have hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) = crisToOD l O (ϖ.iS O K s) :=
    fun s => ϖ.iSD_of_mem O K s.2 _
  have key : ∀ s : S O K e, crisToOD l O (ϖ.iS O K s) =
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) := by
    intro s
    rw [← sub_eq_zero]
    set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) -
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD
    have hDadd : ∀ p q : S O K e, D (p + q) = D p + D q := fun p q => by
      simp only [hD, map_add (f := _)]; ring
    have hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q := fun k q => by
      simp only [hD, map_mul, map_pow, map_natCast]; ring
    have hdiv : ∀ m : ℕ, ξ ^ m ∣ D s := by
      intro m
      obtain ⟨N, hN⟩ := GlobalTheory.T.exists_pow_mul_crisToOD_sub_toOD_dvd l e O K ϖ m
      have hw : ∀ k : ℕ, ∃ y : OA l O, ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y := by
        intro k
        obtain ⟨N0, hN0⟩ := exists_sum_monomial_add l e s.2 k
        obtain ⟨h, hh, hs⟩ := hN0 N0 le_rfl
        set hS' : S O K e := ⟨h, hh⟩
        have hP : (s : K⟦X⟧) - (l : K⟦X⟧) ^ k * h ∈ S O K e :=
          sub_mem s.2 (mul_mem (pow_mem (natCast_mem _ l) k) hh)
        set P : S O K e := ⟨_, hP⟩
        have hsP : s = P + (l : S O K e) ^ k * hS' := Subtype.ext (by simp [P, hS'])
        have hPA : (P : K⟦X⟧) ∈ invL l (A O K) := by
          have : (P : K⟦X⟧) = ∑ n ∈ Finset.range N0, monomial n (coeff n (s : K⟦X⟧)) := by
            simp only [P]; linear_combination hs
          rw [this]
          exact sum_mem fun n _ => monomial_mem_invL l n _
        have hDP : D P = 0 := by
          simp only [hD, sub_eq_zero]
          rw [← hS]
          exact iSD_eq_of_mem_invL_A l e O K ϖ _ hPA
        obtain ⟨y1, hy1⟩ := hN (ϖ.iS O K hS')
        obtain ⟨y2, hy2⟩ := GlobalTheory.T.exists_pow_iHat_toHatS_sub_toOD_dvd l e O K ϖ m hS'
        refine ⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩
        have e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) =
            (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') - toOD l O y1) -
              (l : OD l O) ^ N * ((l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) hS')) - toOD l O y2)) := by
          rw [hsP, hDadd, hDP, zero_add, hDmul]
          simp only [hD, map_sub, map_mul, map_pow, map_natCast]
          ring
        rw [e1]
        exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _
      have h1 := GlobalTheory.T.dvd_of_forall_approx_toOD l e O K ϖ m _ hw
      rw [pow_add, mul_assoc] at h1
      exact (((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)
    have hc := ϖ.complete_OD O K
    exact hc.toIsHausdorff.haus' _ fun n => by
      simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]
      exact Ideal.mem_span_singleton.2 (hdiv n)
  have hext : ϖ.iSD O K = (ϖ.iHat O K).toRingHom.comp (toHatS O K l e) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) (RingHom.ext fun s => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      exact (hS s).trans (key s))
  exact RingHom.congr_fun hext f

end GlobalTheory.BKReal.TwoMaps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvLift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvLift
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.InvLift

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) (m : ℕ)

def InvSet : Subring bk.S where
  carrier := {x | ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev x) - bk.ev x}
  zero_mem' g := by simp
  one_mem' g := by simp
  neg_mem' {x} hx g := by
    have := (hx g).neg_right
    simpa [map_neg, neg_sub, sub_eq_add_neg, add_comm] using this
  add_mem' {x y} hx hy g := by
    have h := dvd_add (hx g) (hy g)
    rw [map_add (f := _), map_add (f := _)]
    convert h using 1
    ring
  mul_mem' {x y} hx hy g := by
    have h := dvd_add (dvd_mul_of_dvd_right (hy g) (Per.σA (g : GQ l) (bk.ev x)))
      (dvd_mul_of_dvd_left (hx g) (bk.ev y))
    rw [map_mul, map_mul]
    convert h using 1
    ring

theorem C_mem (w : Wq l bk.a) : (C w : bk.S) ∈ InvSet bk m := fun g => by
  rw [bk.ev_C, bk.gal_w, sub_self]
  exact dvd_zero _

omit hl in
theorem coe_sum_fin {R : Type} [CommRing R] {e : ℕ} (c : Fin e → R) :
    ((∑ i, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) : Polynomial R) : R⟦X⟧) = ∑ i, C (c i) * X ^ (i : ℕ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp [Polynomial.coeToPowerSeries.ringHom_apply]

theorem exists_div (s : bk.S) : ∃ (q : bk.S) (c : Fin bk.Ep.natDegree → Wq l bk.a),
    s = bk.E * q + ∑ i, C (c i) * X ^ (i : ℕ) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hdist : bk.Ep.IsDistinguishedAt (Ideal.span {(l : Wq l bk.a)}) :=
    { mem := fun {i} hi => Ideal.mem_span_singleton.2 (bk.dvd_coeff i hi)
      monic := bk.monic }
  have hI : Ideal.span {(l : Wq l bk.a)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (WittVector.irreducible l (k := Fq l bk.a)).not_isUnit
  obtain ⟨h1, h2⟩ := (hdist.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod s
  refine ⟨(hdist.isWeierstrassDivisorAt hI).div s, fun i => ((hdist.isWeierstrassDivisorAt hI).mod s).coeff i,
    h2.trans ?_⟩
  rw [← coe_sum_fin]
  congr 2
  have ho : bk.Ep.natDegree = _ := congr(ENat.toNat $(hdist.coe_natDegree_eq_order_map (bk.Ep : (Wq l bk.a)⟦X⟧) 1
    (by rwa [constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  rw [← ho] at h1
  rw [Polynomial.sum_fin (fun i a => Polynomial.C a * Polynomial.X ^ i) (by simp) h1,
    Polynomial.sum_C_mul_X_pow_eq]

variable {bk m} in
theorem cancel_pow_l (k : ℕ) (a : Ainf l) (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply (GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk m).1
    apply ih
    rwa [pow_succ, mul_assoc] at h

end GlobalTheory.BSP.InvLift


open GlobalTheory.BSP.InvLift in
theorem GlobalTheory.BSP.BK.exists_inv_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ k : ℕ, ∀ s : bk.S, ∃ γ : bk.S, bk.E ∣ γ - (l : bk.S) ^ k * s ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev γ) - bk.ev γ := by
  intro l hl K bk m
  obtain ⟨M, q, hq1, hq2⟩ := GlobalTheory.BSP.BK.exists_approx_root l K bk m
  have hqinv : q ∈ InvSet bk m := fun g => by
    obtain ⟨k, hk⟩ := GlobalTheory.BSP.approx_root_indep l K bk m M q hq1 hq2 (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)
    change bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * (bk.ev q - Per.σA (g : GQ l) (bk.ev q)) at hk
    rw [← neg_sub]
    exact (cancel_pow_l k _ hk).neg_right
  set e := bk.Ep.natDegree
  refine ⟨M * e, fun s => ?_⟩
  obtain ⟨q', c, hs⟩ := exists_div bk s
  refine ⟨∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ), ?_, fun g => ?_⟩
  · have key : ∀ i : Fin e, bk.E ∣ C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
        (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)) := by
      intro i
      have h1 : (l : bk.S) ^ (M * e) * X ^ (i : ℕ) = (l : bk.S) ^ (M * (e - i)) * ((l : bk.S) ^ M * X) ^ (i : ℕ) := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, ← Nat.mul_add]
        congr 3
        have := i.2
        omega
      rw [mul_left_comm, h1]
      have := (hq1.trans (sub_dvd_pow_sub_pow q ((l : bk.S) ^ M * X) i)).mul_left (C (c i) * (l : bk.S) ^ (M * (e - i)))
      convert this using 1
      ring
    have heq : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) - (l : bk.S) ^ (M * e) * s =
        (∑ i : Fin e, (C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ) -
          (l : bk.S) ^ (M * e) * (C (c i) * X ^ (i : ℕ)))) - bk.E * ((l : bk.S) ^ (M * e) * q') := by
      rw [hs, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
      ring
    rw [heq]
    exact dvd_sub (Finset.dvd_sum fun i _ => key i) (dvd_mul_right _ _)
  · have hmem : (∑ i : Fin e, C (c i) * (l : bk.S) ^ (M * (e - i)) * q ^ (i : ℕ)) ∈ InvSet bk m :=
      Subring.sum_mem _ fun i _ => Subring.mul_mem _ (Subring.mul_mem _ (C_mem bk m _)
        (Subring.pow_mem _ (natCast_mem _ _) _)) (Subring.pow_mem _ hqinv _)
    exact hmem g
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvLiftStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_lift_mod_E : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ k : ℕ, ∀ s : bk.S, ∃ γ : bk.S, bk.E ∣ γ - (l : bk.S) ^ k * s ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev γ) - bk.ev γ := by
  first | exact @GlobalTheory.BSP.BK.exists_inv_lift | exact GlobalTheory.BSP.BK.exists_inv_lift | (intros; apply GlobalTheory.BSP.BK.exists_inv_lift <;> assumption)
end
end
