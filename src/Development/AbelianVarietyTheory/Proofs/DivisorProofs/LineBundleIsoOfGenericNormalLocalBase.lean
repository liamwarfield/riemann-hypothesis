module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentDifference
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem lbIso_of_generic_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (H : Over (Sp R)) [Smooth H.hom] [GeometricallyIntegral H.hom] (e : Sp R ⟶ H.left), e ≫ H.hom = 𝟙 _ → ∀ L L' : LB H.left, L.IsLB → L'.IsLB → LBIso (L.pull (pullback.fst H.hom (jK R))) (L'.pull (pullback.fst H.hom (jK R))) → LBIso L L' := by
  intro R _ _ _ _ _ H _ _ e he L L' hL hL' h
  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have : IsDominant (jK R) := ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK
  have : QuasiCompact (jK R) := inferInstance
  refine (GlobalTheory.CechPic.cls_eq_iff hL hL').1 (GlobalTheory.ZH.EndoExtend.pic_ext (jK R) hn H e he ?_ ?_)
  · exact (GlobalTheory.DualOpen.pic_sp_local_eq_zero R _).trans
      (GlobalTheory.DualOpen.pic_sp_local_eq_zero R _).symm
  · exact (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB hL' _)).2 h

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_generic_normal_local_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (H : Over (Sp R)) [Smooth H.hom] [GeometricallyIntegral H.hom] (e : Sp R ⟶ H.left), e ≫ H.hom = 𝟙 _ → ∀ L L' : LB H.left, L.IsLB → L'.IsLB → LBIso (L.pull (pullback.fst H.hom (jK R))) (L'.pull (pullback.fst H.hom (jK R))) → LBIso L L' := by
  first | exact @GlobalTheory.Mum.lbIso_of_generic_local | exact GlobalTheory.Mum.lbIso_of_generic_local | (intros; apply GlobalTheory.Mum.lbIso_of_generic_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangent
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  unfold spMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isTanX_dir {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
    {ι : Type} [Fintype ι] (y : FrPt Xo c K) (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X)
    (h1 : X ≫ Xo.s = sOf c _) (h2 : spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x)
    (M : ι → K) : GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1]
    unfold sOf
    have e : (GlobalTheory.FlagTan.dir c M).toRingHom.comp (algebraMap c.F (TrivSqZeroExt K (ι → K))) =
        algebraMap c.F (DualNumber K) := (GlobalTheory.FlagTan.dir c M).comp_algebraMap
    rw [spMap_comp_spMap, ← RingHom.comp_assoc, e]
  · rw [← Category.assoc, spMap_comp_spMap, ← h2]
    congr 2
    ext z <;> simp

theorem ksIso_psiSet : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  obtain ⟨X, h1, h2, hks⟩ := GlobalTheory.T.universal_first_order_deformation hP hG E H Dw l Xo c K y hpq
  refine ⟨X, h1, h2, fun x' hx => ?_⟩
  have key : ∀ M, IsKS (psiSet H) y x' M ↔ x' = spMap (dir c M).toRingHom ≫ X := fun M =>
    ⟨fun k => GlobalTheory.T.kodaira_spencer_tangent_difference hP hG E H Dw l Xo c K y _ _ M hpq hx (isTanX_dir y X h1 h2 M) k (hks M),
      fun e => e ▸ hks M⟩
  obtain ⟨M, hM⟩ := GlobalTheory.T.kodaira_spencer_matrix_exists hP E H Dw l Xo c K y x' hpq hx
  exact ⟨⟨M, (key M).1 hM, fun M' e => GlobalTheory.T.kodaira_spencer_matrix_unique hP E H Dw l Xo c K y x' hpq hx M' M ((key M').2 e) hM⟩, key⟩

end GlobalTheory.FlagTan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangentStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_iso_flag_tangent : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y := by
  first | exact @GlobalTheory.FlagTan.ksIso_psiSet | exact GlobalTheory.FlagTan.ksIso_psiSet | (intros; apply GlobalTheory.FlagTan.ksIso_psiSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoSeq

section General

variable {O : Type} [CommRing O] {X T T' S : Scheme.{0}} {A B A' B' : X.Modules}

def sqIso {b : S ⟶ T} {a : T ⟶ X} {c : S ⟶ T'} {a' : T' ⟶ X} (w : b ≫ a = c ≫ a') :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b ≅ Scheme.Modules.pullback a' ⋙ Scheme.Modules.pullback c :=
  Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫ (Scheme.Modules.pullbackComp c a').symm

structure Datum (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ) where

  D : X.Modules

  ρ : O →+* End D

  a : A ⟶ D

  b : D ⟶ B

  u : A' ⟶ D

  v : D ⟶ B'
  w₁ : a ≫ b = 0
  w₂ : u ≫ v = 0
  isVB : IsVB D r
  exact₁ : (ShortComplex.mk a b w₁).ShortExact
  exact₂ : (ShortComplex.mk u v w₂).ShortExact
  equiv_a : IsEquivariant α ρ a
  equiv_b : IsEquivariant ρ β b
  equiv_u : IsEquivariant α' ρ u
  equiv_v : IsEquivariant ρ β' v

variable (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ)

variable {α β α' β' r}

def biprodAct (α : O →+* End A) (β : O →+* End B) : O →+* End (A ⊞ B) where
  toFun x := End.of (biprod.map (act α x) (act β x))
  map_one' := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act]
  map_mul' x y := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act, Category.assoc]
  map_zero' := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act]
  map_add' x y := by
    refine End.ext (biprod.hom_ext _ _ ?_ ?_) <;> simp [act]

def Datum.split (α : O →+* End A) (β : O →+* End B) {m n : ℕ} (hA : IsVB A m) (hB : IsVB B n) :
    Datum α β β α (m + n) where
  D := A ⊞ B
  ρ := biprodAct α β
  a := biprod.inl
  b := biprod.snd
  u := biprod.inr
  v := biprod.fst
  w₁ := by simp
  w₂ := by simp
  isVB := hA.biprod hB
  exact₁ := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
  exact₂ := (ShortComplex.Splitting.mk (S := ShortComplex.mk (biprod.inr : B ⟶ A ⊞ B) biprod.fst (by simp))
    biprod.snd biprod.inl (by simp) (by simp) (by rw [add_comm]; exact biprod.total)).shortExact
  equiv_a x := by simp [act, biprodAct]
  equiv_b x := by simp [act, biprodAct]
  equiv_u x := by simp [act, biprodAct]
  equiv_v x := by simp [act, biprodAct]

end General

section Dieu

variable {O : Type} [CommRing O] (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}}
  [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

end Dieu

end GlobalTheory.TwoSeq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

theorem endChar_exists_of_isMonHom (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (_hB : GlobalTheory.Mum.Base R)
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (_hG : IsSemiAbelian G) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G) (hfm : IsMonHom f) :
    ∃ m, EndChar U f m := by
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map f).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G.hom (spMap (residue R)) ≫ f.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map f) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp hp f _ e
  obtain ⟨m, hm⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp ≫ (Over.pullback (spMap (residue R))).map f) inferInstance
  refine ⟨m, fun κ _ a ha G₀ _ φ h f₀ hf => ?_⟩
  let σ : ResidueField R →+* κ := Ideal.Quotient.lift _ a fun x hx => ha x (by simpa using hx)
  have ea : a = σ.comp (residue R) := RingHom.ext fun _ => rfl
  have es : spMap a = spMap σ ≫ spMap (residue R) := by rw [← Spec.map_comp]; rfl
  let ψ : G₀.left ⟶ ((Over.pullback (spMap (residue R))).obj G).left :=
    pullback.lift φ (G₀.hom ≫ spMap σ) (by rw [Category.assoc, ← es, h.1.w])
  have hψ : ψ ≫ pullback.fst G.hom (spMap (residue R)) = φ := pullback.lift_fst _ _ _
  have k : IsGrpPullback G₀ ((Over.pullback (spMap (residue R))).obj G) (spMap σ) ψ :=
    hp.cancel (h.congr es hψ.symm) (pullback.lift_snd _ _ _)
  have e₀ : f₀.left ≫ ψ = ψ ≫ ((Over.pullback (spMap (residue R))).map f).left := hp.1.hom_ext
    (by rw [Category.assoc, hψ, hf, Category.assoc, e, ← Category.assoc, hψ])
    (by rw [Category.assoc, k.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, k.1.w])
  rw [← GlobalTheory.TorusPart.pullTorus_gtTorus (U.gt 0) hr ha hp h k ea hψ.symm,
    ← GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e₀, hm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

end GlobalTheory.Poinc.Eq8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadings
set_option autoImplicit false

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

namespace GlobalTheory.Unframe

theorem lUnif_moveR {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G) (hw : ∀ i σ, w i σ ∈ Subgroup.center G) (hU : R.LUnif) :
    (moveR R w).LUnif := by
  intro i σ
  obtain ⟨h1, h2, h3⟩ := hU i σ
  have hl : ∀ x, (R.FW i).ρ (w i σ)⁻¹ ((R.FW i).ρ (w i σ) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hr : ∀ x, (R.FW i).ρ (w i σ) ((R.FW i).ρ (w i σ)⁻¹ x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hc : ∀ g x, (R.FW i).ρ (w i σ) ((R.FW i).ρ g x) = (R.FW i).ρ g ((R.FW i).ρ (w i σ) x) := fun g x => by
    rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.1 (hw i σ) g, map_mul, Module.End.mul_apply]
  refine ⟨fun n b hb => ?_, ?_, fun g x => ?_⟩
  · have hinj : Function.Injective ((R.FW i).ρ (w i σ)) := Function.LeftInverse.injective hl
    exact h1 n (fun k => (R.FW i).ρ (w i σ) (b k)) (hb.map' _ (LinearMap.ker_eq_bot.2 hinj))
  · refine top_le_iff.1 (h2 ▸ Submodule.span_mono ?_)
    rintro _ ⟨x, rfl⟩
    exact ⟨(R.FW i).ρ (w i σ)⁻¹ x, congrArg ((R.FW i).j σ) (hr x)⟩
  · have h := h3 g ((R.FW i).ρ (w i σ) x)
    rw [← hc] at h
    exact h

end GlobalTheory.Unframe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadingsStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationLaws_centralMovedReadings : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G), (∀ i σ, w i σ ∈ Subgroup.center G) → R.LUnif → (moveR R w).LUnif := by
  first | exact @GlobalTheory.Unframe.lUnif_moveR | exact GlobalTheory.Unframe.lUnif_moveR | (intros; apply GlobalTheory.Unframe.lUnif_moveR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreNef

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y) :
    LBIso (L.pull (b ≫ a)) ((L.pull a).pull b) :=
  LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull hL _)))

theorem isProjOver_fibre {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (hp : IsProjOver p) (l : ℕ) [Fact l.Prime] {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Algebra (ZMod l) Γ(Z, ⊤)] : IsProjOver (strHom (ZMod l) (X := Z)) := by
  obtain ⟨N, e, he, -⟩ := hp
  have hb : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have P₀ := GlobalTheory.ProjSpace.isPullback_baseChange N (Int.castRingHom k)
  have hf : IsFinite (GlobalTheory.ProjSpace.baseChange N (Int.castRingHom k)) :=
    MorphismProperty.of_isPullback P₀.flip hb
  have hZ : IsProjOver ((i ≫ e ≫ GlobalTheory.ProjSpace.baseChange N (Int.castRingHom k)) ≫ PSpace.str ℤ N) :=
    GlobalTheory.isProjOver_comp_of_isFinite _ ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨M, φ, hφ, -⟩ := hZ
  have P := GlobalTheory.ProjSpace.isPullback_baseChange M (Int.castRingHom (ZMod l))
  have hc : IsClosedImmersion (spMap (Int.castRingHom (ZMod l))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  have hcb : IsClosedImmersion (GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))) :=
    MorphismProperty.of_isPullback P.flip hc
  let ψ := P.lift φ (strHom (ZMod l) Z) (specZIsTerminal.hom_ext _ _)
  have hψ : ψ ≫ PSpace.str (ZMod l) M = strHom (ZMod l) Z := P.lift_snd _ _ _
  have hψ' : ψ ≫ GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l)) = φ := P.lift_fst _ _ _
  have : IsClosedImmersion (ψ ≫ GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))) := by
    rw [hψ']; exact hφ
  exact ⟨M, ψ, IsClosedImmersion.of_comp_isClosedImmersion ψ
    (GlobalTheory.ProjSpace.baseChange M (Int.castRingHom (ZMod l))), hψ⟩

theorem isNef_pull_of_nefOver {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (l : ℕ)
    [Fact l.Prime] {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] [Algebra (ZMod l) Γ(Z, ⊤)]
    (L : HermLB p) (hL : NefOver L l) : IsNef (ZMod l) (L.B.pull i) := by
  have hLi := LB.isLB_pull L.isLB i
  refine isNef_iff_isClosedImmersion.2 ⟨hLi, fun C c hc hC hd _ => ?_⟩
  letI := algebraΓAlong (ZMod l) c
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have h := hL C (c ≫ i) (ZMod l) hd
  rw [interNumOn_eq_interNum_pull (fun r => rfl) (fun j => by fin_cases j; exact hLi)]
  rw [topSelfIntersection] at h
  refine h.trans_eq (interNum_congr_lbIso _ _ (fun _ => LB.isLB_pull L.isLB _)
    (fun j => by fin_cases j; exact LB.isLB_pull hLi c) fun j => ?_)
  fin_cases j
  exact lbIso_pull_comp L.isLB i c

end GlobalTheory.FibreNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem valR_comp_app {Y Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Y) (m : Y ⟶ Z) (O : Z.Opens)
    (f : Γ(Z, O)) : valR (z ≫ m) O f = valR z (m ⁻¹ᵁ O) ((m.app O).hom f) := by
  by_cases h : ⊤ ≤ z ⁻¹ᵁ (m ⁻¹ᵁ O)
  · rw [valR_eq_ev _ _ h, valR_eq_ev (z ≫ m) O h, ← GlobalTheory.FlagMod.ev_appLE z m le_rfl h h, Scheme.Hom.appLE_eq_app]
  · rw [valR, valR, dif_neg h]
    exact dif_neg h

theorem le_preimage_of_red {Y : Scheme.{0}} {B : Type} [CommRing B] {x : Sp B ⟶ Y} {w : Sp (DualNumber B) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) : ⊤ ≤ w ⁻¹ᵁ O := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap B (DualNumber B)) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap B (DualNumber B) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap B (DualNumber B) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap B (DualNumber B) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← hw] at this
  exact this

theorem valR_resG {Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Z) {U V : Z.Opens} (e : V ≤ U)
    (h : ⊤ ≤ z ⁻¹ᵁ V) (a : Γ(Z, U)) : valR z V (resG Z e a) = valR z U a := by
  calc
    valR z V (resG Z e a) = GlobalTheory.FlagMod.ev z V h (resG Z e a) := valR_eq_ev z V h _
    _ = GlobalTheory.FlagMod.ev z U (GlobalTheory.FlagMod.le_preimage_mono e h) a :=
      GlobalTheory.FlagMod.ev_res z e h _ a
    _ = valR z U a := (valR_eq_ev z U _ a).symm

theorem isAffineHom_of_field {K : Type} [Field K] {X : Scheme.{0}} (x0 : Sp K ⟶ X) : IsAffineHom x0 := by
  refine ⟨fun U _ => ?_⟩
  by_cases h : (default : PrimeSpectrum K) ∈ x0 ⁻¹ᵁ U
  · have e : x0 ⁻¹ᵁ U = ⊤ := eq_top_iff.2 fun p _ => by
      rwa [Subsingleton.elim (α := PrimeSpectrum K) p default]
    rw [e]
    exact isAffineOpen_top _
  · have e : x0 ⁻¹ᵁ U = ⊥ := eq_bot_iff.2 fun p hp => by
      rw [Subsingleton.elim (α := PrimeSpectrum K) p default] at hp
      exact (h hp).elim
    rw [e]
    exact isAffineOpen_bot _

theorem IsChartPt.of_le {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    {Z : Scheme.{0}} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} {W₀ : Z.Opens} {d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)}
    (hd : LogKS.IsField W₀ d) {Ω₀ Ω : Z.Opens} (h0 : Ω₀ ≤ Ω) (h1 : Ω ≤ W₀) {n : ℕ} {u : Fin n → (epsR K ⟶ A)}
    {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B]
    [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B))
    (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω₀)) (hut : ∀ a, IsTangent (u a)) (hl : IsChartPt A' m m' Ω₀ (d Ω₀) u θ Wo g x l) :
    IsChartPt A' m m' Ω (d Ω) u θ Wo g x l := by
  obtain ⟨h₁, h₂, h₃⟩ := hl
  refine ⟨h₁, GlobalTheory.FlagMod.le_preimage_mono h0 h₂, fun f => ?_⟩
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω₀ := hxΩ
  have hw : ∀ a, ⊤ ≤ (transl (baseMap K B) x (u a) ≫ m) ⁻¹ᵁ Ω₀ := fun a =>
    le_preimage_of_red ((isTransl_transl _ x hx (u a)).red (hut a)) hxΩ
  rw [← valR_resG _ h0 h₂, h₃, chartVal, chartVal, hd.2.2 Ω Ω₀ h0 h1, valR_resG _ h0 hxm, valR_resG _ h0 hxm]
  simp only [valR_resG _ h0 (hw _)]

end GlobalTheory.CechKS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.TauFormHom

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues GlobalTheory.TauForm

theorem isGrpPullback_genMap {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) : IsGrpPullback A.A G (jK R) (genMap U) := by
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
  exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr
    (Category.id_comp _) rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G), IsMonHom p → ∀ (ρ : D.toPre.X →+ D'.toPre.X) (s : D'.toPre.X →+ D.toPre.X), TorMatch U U' (RingHom.id R) p.left ρ → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), IsUnit (k : R) → ∀ (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := R) F ⟶ A'.A), QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a.left ≫ genMap U = a'.left ≫ genMap U' ≫ p.left → ∃ z, q.y = s q'.y + k • z) → ∀ (a' : D'.toPre.X) (b : D.toPre.X) (x x' : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre (s a') b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D'.toPre a' (ρ b) x' → ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) (u : R) * (x' : FractionRing R) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' P hP ρ s hM hlab a' b x x' hx hx'
  haveI := hdvr
  obtain ⟨hR, hR0⟩ := id hRb
  obtain ⟨-, -, -, hRc⟩ := id hR
  haveI := hRc
  haveI := hR0
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let F := AlgebraicClosure (FractionRing R)
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback_genMap U) (TFK (R := R) F)
    ((TFK (R := R) F).hom ≫ jK R) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback_genMap U') (TFK (R := R) F)
    ((TFK (R := R) F).hom ≫ jK R) rfl
  let Pm : (Over.mk ((TFK (R := R) F).hom ≫ jK R) ⟶ G') →* (Over.mk ((TFK (R := R) F).hom ≫ jK R) ⟶ G) :=
    { toFun := fun y => y ≫ P, map_one' := MonObj.one_comp P, map_mul' := fun y y' => MonObj.mul_comp y y' P }
  have hPm : ∀ y, (Pm y).left = y.left ≫ P.left := fun y => Over.comp_left (f := y) (g := P)
  have key : ∀ k : ℕ, IsUnit (k : R) → (k : ℤ) ∣ (ord_vw R).toFun x - (ord_vw R).toFun x' := by
    intro k hk
    obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_inertia_moves_tame_root R F ϖ hϖ k hk
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
    have hkO : IsUnit (k : O) := by simpa using hk.map φ
    obtain ⟨f, ⟨i₁, s₁, -, a₁, w₁⟩, p₁⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
    obtain ⟨f', ⟨i₂, s₂, -, a₂, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D' A' G' hG' U' F k hk1
    have wt₁ : ∀ (p p' : QkPt D.toPre F k) (τ : Multiplicative D.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
        WeilIs A.A A.L (k : ℤ) (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
      (w₁ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
    have c₁ : ∀ p p', QkExt σ.toRingHom p p' → (f p').left = spMap σ.toRingHom ≫ (f p).left := by
      intro p p' hpp'
      obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D A G hG U F F σ k hk1 p
      obtain ⟨y, hy⟩ := hx (f p)
      have : y = f p' := (i₁ p' y).1 ((hiff p' (f p) y hpp' hy).1 ((i₁ p (f p)).2 rfl))
      rw [← this, hy]
    have c₂ : ∀ p p', QkExt σ.toRingHom p p' → (f' p').left = spMap σ.toRingHom ≫ (f' p).left := by
      intro p p' hpp'
      obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D' A' G' hG' U' F F σ k hk1 p
      obtain ⟨y, hy⟩ := hx (f' p)
      have : y = f' p' := (i₂ p' y).1 ((hiff p' (f' p) y hpp' hy).1 ((i₂ p (f' p)).2 rfl))
      rw [← this, hy]
    have uniq : ∀ (u v : TFK (R := R) F ⟶ A.A) (c c' : Fˣ), WeilIs A.A A.L (k : ℤ) u v (unitOn c) →
        WeilIs A.A A.L (k : ℤ) u v (unitOn c') → c = c' := fun u v c c' h h' =>
      GlobalTheory.weilIs_unique_fieldPoint _ A.A A.L A.isLB F _ k u v c c' h h'

    obtain ⟨p', hp'⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB' hk0 a'
    obtain ⟨q, hq⟩ := s₁ (e.symm (Pm (e' (f' p')))) (by rw [← map_pow, ← map_pow, ← map_pow, p₂, map_one, map_one, map_one])
    have hqe : e (f q) = Pm (e' (f' p')) := by rw [hq, e.apply_symm_apply]
    have hql : (f q).left ≫ genMap U = (f' p').left ≫ genMap U' ≫ P.left := by
      rw [← he, hqe, hPm, he', Category.assoc]
    obtain ⟨z, hz⟩ := hlab F k hk q p' (f q) (f' p') ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl) hql
    rw [hp'] at hz

    obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σ.toRingHom (RingHom.ext σ.commutes) q
    obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
    obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB F O φ h₂ k σ q r hr
      (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB F O φ h₂ k hkO σ h₃ q)
    obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB' F O φ h₂ k σ p' r' hr'
      (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB' F O φ h₂ k hkO σ h₃ p')
    have hr₁ : e (f r) = Pm (e' (f' r')) := Over.OverMorphism.ext (by
      rw [he, hPm, he', c₁ q r hr, c₂ p' r' hr']
      simp only [Category.assoc, hql])
    have hq₁ : e (f q₁) = Pm (e' (f' q₂)) := by
      rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, map_mul, map_mul, hqe] at hr₁
      exact mul_left_cancel hr₁
    obtain ⟨qT, yT, tT⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (F := F)
      (τ₂.comp (AddMonoidHom.toMultiplicative ρ)) (MonoidHom.ext fun χ => DFunLike.congr_fun k₂ _)
    have hT := hM F (fun _ => rfl) k hk _ τ₂ qT q₂ (f qT) (f' q₂) k₂ (fun _ => rfl) yT tT y₂ t₂
      ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)
    have hfq : f qT = f q₁ := e.injective (by
      rw [hq₁]
      exact Over.OverMorphism.ext (by rw [he, hPm, he', hT, Category.assoc]))
    obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
    have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) := by
      have h := wt₁ qT pb _ yT tT
      rw [hfq] at h
      exact uniq _ _ _ _ (wt₁ q₁ pb τ₁ y₁ t₁) h

    obtain ⟨xq, hxq⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D.toPre q.y pb.y
    obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D.toPre z pb.y
    obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main R D.toPre hB (s a') z pb.y k x xz xq hx hxz (by rw [← hz]; exact hxq)
    obtain ⟨t, t0, tv, tσ⟩ := v₁ _ xq hxq
    obtain ⟨t', t0', tv', tσ'⟩ := v₂ _ x' (by rw [hp']; exact hx')
    have dv := GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord R F ϖ hϖ k O φ σ π hkO h₁ h₂ h₃ h₄ h₅ (t / t') (xq / x')
      (by rw [map_div₀, tσ, tσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
      (by rw [map_div₀, div_pow, tv, tv', Units.val_div_eq_div_val, map_div₀, map_div₀])
    rw [val_div, hu, (ord_vw R).map_mul, (ord_vw R).map_unit, (ord_vw R).map_mul, val_pow, zero_add,
      nsmul_eq_mul] at dv
    have e₀ : (ord_vw R).toFun x - (ord_vw R).toFun x' =
        ((ord_vw R).toFun x + (k : ℤ) * (ord_vw R).toFun xz - (ord_vw R).toFun x') - (k : ℤ) * (ord_vw R).toFun xz := by
      ring
    rw [e₀]
    exact dvd_sub dv (dvd_mul_right _ _)
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  exact GlobalTheory.TauForm.exists_unit_of_ord_eq (W := R) (x := x) (y := x') (by
    rw [← sub_eq_zero]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
      ((ord_vw R).toFun x - (ord_vw R).toFun x')) (by simpa using hl.pow _)) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega))

end GlobalTheory.TauFormHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesRationalityBackFromMovedReadings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesRationalityBackFromMovedReadings
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.UnframeForms

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ)

abbrev movedS : NX.RatDat D.ntw :=
  { S with
    A := fun n => moveForms (S.A n) fun σ => (YS.fi (NX.idxOf D n)).eG.symm (w (NX.idxOf D n) σ) }

def movedIso (i : Fin D.R.m) : NX.FormsIso ((movedS YS w).A ((i : ℕ) + 1)) ((fullHeckeRealDatMovedReadings Rl w).FW i) where
  eK := (YS.fi i).eK
  eK_LL := (YS.fi i).eK_LL
  e := (YS.fi i).e
  eG := (YS.fi i).eG
  eW := (YS.fi i).eW
  wk := (YS.fi i).wk
  mkK := (YS.fi i).mkK
  rho := (YS.fi i).rho
  chi := (YS.fi i).chi
  j σ x := by
    change (Rl.FW i).j σ ((Rl.FW i).ρ (w i σ) ((YS.fi i).e x)) =
      (YS.fi i).eW σ ((S.A _).j σ ((S.A _).ρ ((YS.fi (NX.idxOf D ((i : ℕ) + 1))).eG.symm
        (w (NX.idxOf D ((i : ℕ) + 1)) σ)) x))
    rw [NX.idxOf_succ, ← (YS.fi i).j, (YS.fi i).rho, MulEquiv.apply_symm_apply]

def movedYS : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG (movedS YS w) where
  fi := movedIso YS w
  geq := YS.geq
  rho := YS.rho
  chi := YS.chi
  eF := YS.eF
  bsup := YS.bsup
  act := YS.act

variable (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evW_moved (j : Fin D.R.m) (x : S.WL ((j : ℕ) + 1)) :
    evW (movedYS YS w) v₀ j x = evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A))) x) := by
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((Rl.FW j).ρ (w j (sg0 D A3.A)) ((YS.fi j).e x))) (v₀ j _) =
    (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A _).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A))) x)))
      (v₀ j _)
  rw [(YS.fi j).rho, MulEquiv.apply_symm_apply]

theorem evK_moved {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    ∃ y, evK (movedYS YS w) v₀ hρ i j b x = evK YS v₀ hρ i j b y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨x', ex⟩ := hx
    obtain ⟨y', ey⟩ := hy
    exact ⟨x' + y', (map_add _ _ _).trans ((congrArg₂ (· + ·) ex ey).trans (map_add _ _ _).symm)⟩
  | tmul a f =>
    refine ⟨a ⊗ₜ (⟨(S.A ((j : ℕ) + 1)).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A))) (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
      YS.rho _ (Nat.le_add_left _ _) j.2 _ _ (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ : ↥(S.A ((j : ℕ) + 1)).WK), ?_⟩
    exact congrArg (ρ.e i b a • ·) (evW_moved YS w v₀ j _)

theorem realRd_moved {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    ∃ f', realRd (movedYS YS w) v₀ hρ i j b ν f = realRd YS v₀ hρ i j b ν f' := by
  obtain ⟨y, hy⟩ := evK_moved YS w v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  refine ⟨(YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y, ?_⟩
  change ν⁻¹ • evK (movedYS YS w) v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) =
    ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y))
  rw [hy]
  exact congrArg (fun z => ν⁻¹ • evK YS v₀ hρ i j b z)
    ((YS.eF i _ b (Nat.le_add_left _ _) j.2).apply_symm_apply (show NX.Fm S i ((j : ℕ) + 1) b from y)).symm

end GlobalTheory.UnframeForms

namespace GlobalTheory.UnframeForms

open GlobalTheory.ExportSeries

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X} (hρ : ρ.Good)
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool} {rd rd' : Rd ρ Y i j b}

theorem rdK_sub (h : ∀ f, ∃ f', rd' f = rd f') (k : ℕ) (x : X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b) :
    ∃ x', rdK rd' hρ k x = rdK rd hρ k x' := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨x', ex⟩ := hx
    obtain ⟨y', ey⟩ := hy
    exact ⟨x' + y', (map_add _ _ _).trans ((congrArg₂ (· + ·) ex ey).trans (map_add _ _ _).symm)⟩
  | tmul a f =>
    obtain ⟨f', e⟩ := h f
    exact ⟨a ⊗ₜ f', by rw [rdK_tmul, rdK_tmul, e]⟩

theorem rat_of_sub (h : ∀ f, ∃ f', rd' f = rd f') (h' : Rat hρ rd') : Rat hρ rd := by
  obtain ⟨h1, h2, h3⟩ := h'
  refine ⟨fun s g P hd => ?_, fun k Q ψ hk hQ s g P hd x hx => ?_, fun Q M hQ s g P hd hs a => ?_⟩
  · obtain ⟨f, hf⟩ := h1 s g P hd
    obtain ⟨f', e⟩ := h f
    exact ⟨f', e.symm.trans hf⟩
  · obtain ⟨y, hy⟩ := h2 k Q ψ hk hQ s g P hd hx
    obtain ⟨y', e⟩ := rdK_sub hρ h k y
    exact ⟨y', e.symm.trans hy⟩
  · obtain ⟨f, hf⟩ := h3 Q M hQ s g P hd hs a
    obtain ⟨f', e⟩ := h f
    exact ⟨f', e.symm.trans hf⟩

end GlobalTheory.UnframeForms

theorem GlobalTheory.UnframeForms.ratRow_back : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ), (∀ i σ, w i σ ∈ Subgroup.center Γ) → ∃ (S' : NX.RatDat D.ntw) (YS' : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG S'), ∀ (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), RatRow YS' v₀ hρ i j b → RatRow YS v₀ hρ i j b :=
  fun Rl _ _ YS w _ => ⟨GlobalTheory.UnframeForms.movedS YS w, GlobalTheory.UnframeForms.movedYS YS w, fun v₀ _ hρ i j b ⟨ν, hn, hr⟩ =>
    ⟨ν, hn, GlobalTheory.UnframeForms.rat_of_sub hρ (GlobalTheory.UnframeForms.realRd_moved YS w v₀ hρ i j b ν) hr⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesRationalityBackFromMovedReadingsStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesRationality_back_from_movedReadings : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ), (∀ i σ, w i σ ∈ Subgroup.center Γ) → ∃ (S' : NX.RatDat D.ntw) (YS' : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG S'), ∀ (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), RatRow YS' v₀ hρ i j b → RatRow YS v₀ hρ i j b := by
  first | exact @GlobalTheory.UnframeForms.ratRow_back | exact GlobalTheory.UnframeForms.ratRow_back | (intros; apply GlobalTheory.UnframeForms.ratRow_back <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SemiAbFibre

theorem irreducibleSpace_fibre : ∀ (T : Scheme.{0}) (G : Over T) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T), IrreducibleSpace (pullback G.hom x : Scheme.{0}) := by
  intro T G _ hG Ω _ x
  have := hG.smooth
  have := hG.geomConnected
  have h : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral (pullback G.hom x : Scheme.{0}) :=
    h.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom x)
  infer_instance

end GlobalTheory.SemiAbFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleSpace_fibre_semiAbelian_fieldPoint : ∀ (T : Scheme.{0}) (G : Over T) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T), IrreducibleSpace (pullback G.hom x : Scheme.{0}) := by
  first | exact @GlobalTheory.SemiAbFibre.irreducibleSpace_fibre | exact GlobalTheory.SemiAbFibre.irreducibleSpace_fibre | (intros; apply GlobalTheory.SemiAbFibre.irreducibleSpace_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

variable {p : ℕ} [Fact p.Prime]

end Defs

def RegLocSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : GlobalTheory.Mean4O.Cover Y) (U W : V.X.Opens), (W : Set V.X).Nonempty →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (g : V.X.functionField),
    (∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U →
      below (z ≫ V.j) ∈ W → e.w (TrueGeo.valAt (z ≫ V.j) g) ≤ 1) →
    ∀ x ∈ U, (V.p x).asIdeal = v.asIdeal → RegAt x g

end GlobalTheory.DetHT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullback
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue.Pull

open GlobalTheory.Cartier GlobalTheory.TrueGeo.SmallSec

section
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
  (hη : j (genericPoint Y) ⤳ genericPoint X)

theorem fnMap_algebraMap (y : Y) (a : X.presheaf.stalk (j y)) :
    fnMap j hη (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (j.stalkMap y a) := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [algebraMap_germ hx s, fnMap_fnOf j hη _ (gen_mem hy), ← algebraMap_germ hy]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j U _ _ s).symm

theorem regAt_fnMap {y : Y} {t : X.functionField} (h : RegAt (j y) t) : RegAt y (fnMap j hη t) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨_, (fnMap_algebraMap j hη y a).symm⟩

theorem unitAt_fnMap {y : Y} {t : X.functionField} (h : UnitAt (j y) t) : UnitAt y (fnMap j hη t) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨_, ha.map _, (fnMap_algebraMap j hη y a).symm⟩

end

end GlobalTheory.FrameGlue.Pull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.HtGen

attribute [local instance] Over.cartesianMonoidalCategory

section Cover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

end Cover

section Chars

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

abbrev TorsK {K : Type} [Field K] (ξ : Sp K ⟶ X) (q : ℕ) : Subgroup (Over.mk ξ ⟶ t.G) := (powMonoidHom q).ker



variable {t} in
def InducedBy {K : Type} [Field K] {ξ : Sp K ⟶ X} {q : ℕ} (χ : TorsK t ξ q →* Kˣ) {R : Type} [CommRing R]
    (x : Sp R ⟶ X) (u : R →+* K) {O : Type} [CommRing O] (ψ : R →+* O) {z : Sp O ⟶ X} (c : TorsChar t z q) : Prop :=
  ∀ (σ : Over.mk x ⟶ t.G) (k : TorsK t ξ q) (a : R) (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G),
    σ ^ q = 1 → k.1.left = spMap u ≫ σ.left → w.left = spMap ψ ≫ σ.left → u a = χ k → (c.χ O w : O) = ψ a

end Chars

end GlobalTheory.HtGen
end
end
