module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionToG
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.WholeBaseFinitePart

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion

theorem exists_torsion_toG (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [CharZero R] (hR : AdmBase R (maximalIdeal R)) (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom ∧ Flat N.hom ∧ GtTors k g₀ ∧
      (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧
      x₀ ^ k = 1 ∧ FormalEq P.U.toUnifPre x₀ g₀ := by
  obtain ⟨_, -, -, hc⟩ := hR
  have hL := abelianSchemeLaws_all.1
  obtain ⟨Gt, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt P.D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  have hΦ : Represents Φ := hΦ
  have hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
    obtain ⟨h₁, h₂, -⟩ := hL.mulN _ P.D.toPre.P k hk
    have h₁' : IsFinite (𝟙 P.D.toPre.P.A ^ k).left := h₁
    have h₂' : Flat (𝟙 P.D.toPre.P.A ^ k).left := h₂
    rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
    have Q := MulEtaleDvr.isPullback_torsion P.D.toPre.P.A k
    exact isFinite_flat_torsion_of_isGt _ (splitExt P.D.toPre) Gt hH k hk
      (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')
  obtain ⟨hf, hl⟩ := hfin
  obtain ⟨J, hJ⟩ := exists_mulEquiv P.U.toUnifPre hL.globalFns hΦ
  have hN := isAdicColimit_of_isFinite hc (torsion Gt k)
  refine ⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl,
    (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_,
    (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    have hx := (tors_iff hΦ k x).1 hg
    refine ⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩
    rw [torsionLift_ι]
    exact (isPull_iff_comp hΦ _ _ _).1 hh
  · rw [← map_pow, torsionι_pow, map_one]

open GlobalTheory.FinitePartGeneric ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint

theorem generic (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    [IsDomain R] [IsLocalRing R] [CharZero R] (hR : AdmBase R (maximalIdeal R)) (t : SAB H (Sp R))
    (P : PELUnif (maximalIdeal R) t) (k : ℕ) (hk : 1 ≤ k) (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N)
    (x₀ : N ⟶ t.G) (hfin : IsFinite N.hom) (htors : x₀ ^ k = 1) (hform : FormalEq P.U.toUnifPre x₀ g₀)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left) (hx : OverGen F N x)
    (q : QkPt P.D.toPre F k) (hq : q.y = 0) (hg : GtPt.IsPullF F x g₀ q.g) : IsImage P F k q (x ≫ x₀.left) := by
  have hL := firstFiveLaws
  have := hfin
  obtain ⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩ := exists_normal_point R hR F N x hx
  have hφ : Function.Injective φ := fun a b e => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))
  obtain ⟨D', hD, A', U', hU⟩ := UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange
    hL.2.2.2.2.psiOnExists hR hR' φ hφ hI t.semi P.U
  have hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ := hξ.trans (Category.id_comp _).symm
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh g₀
  let x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj t.G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh))
      (pullback.lift_snd _ _ _)
  have e₁ : x₁.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj t.G)).hom.left ≫ pullback.fst t.G.hom (specOf φ) =
      ξ ≫ x₀.left := (congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁
  have gG := isGrpPullback_pullback t.G (spMap φ)
  have hk₁ : x₁ ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N := Over.homMk ξ hh
    have e : pushHom gG _ x₁ = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])
  have hp := isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)
  obtain ⟨g', hg'⟩ := FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp
  let y : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj t.G :=
    Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F)
      (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)
  have hy : (y ≫ P.U.gen.hom).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      ((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine ⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ P.D P.A t.G P.U _ (Iso.refl _)
    (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁
    (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩
  · let xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj
        (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj t.G)) :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩
  · rw [hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]
    exact Category.assoc _ _ _

end GlobalTheory.WholeBaseFinitePart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowBasisFromReferenceTupleQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowBasisFromReferenceTupleQuotient
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.RowBasis

theorem exists_basis_semi {E W : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup W] [Module ℂ W] {N : ℕ}
    (s : ℂ →+* ℂ) (hs : ∀ z, s (s z) = z) (g : (Fin N → ℂ) → W)
    (gadd : ∀ z z', g (z + z') = g z + g z') (gsmul : ∀ (a : ℂ) z, g (a • z) = s a • g z)
    (ginj : ∀ z, g z = 0 → z = 0) (jE : E →ₗ[ℂ] W) (hj : Function.Injective jE)
    (hmem : ∀ z, ∃ w, jE w = g z) (hsurj : ∀ w, ∃ z, jE w = g z) :
    ∃ c : Module.Basis (Fin N) ℂ E, ∀ z, jE (∑ i, s (z i) • c i) = g z := by
  choose c0 hc0 using fun i : Fin N => hmem (Pi.single i 1)
  let gA : (Fin N → ℂ) →+ W := AddMonoidHom.mk' g gadd
  have gsum : ∀ z, g z = ∑ i, s (z i) • g (Pi.single i 1) := by
    intro z
    have hz : z = ∑ i, z i • (Pi.single i (1 : ℂ) : Fin N → ℂ) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    calc g z = gA (∑ i, z i • (Pi.single i (1 : ℂ) : Fin N → ℂ)) := by rw [← hz]; rfl
      _ = ∑ i, gA (z i • (Pi.single i (1 : ℂ) : Fin N → ℂ)) := map_sum gA _ _
      _ = ∑ i, s (z i) • g (Pi.single i 1) := Finset.sum_congr rfl fun i _ => gsmul _ _
  have key : ∀ z, jE (∑ i, s (z i) • c0 i) = g z := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, gsum z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hc0 i]
  have hli : LinearIndependent ℂ c0 := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have h0 : g (fun k => s (a k)) = 0 := by
      rw [← key]
      simp only [hs, ha, map_zero]
    have h1 := congrFun (ginj _ h0) i
    have h2 : s (s (a i)) = s 0 := congrArg s h1
    rwa [hs, map_zero] at h2
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range c0) := by
    intro w _
    obtain ⟨z, hz⟩ := hsurj w
    have hw : w = ∑ i, s (z i) • c0 i := hj (by rw [key, hz])
    rw [hw]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨Module.Basis.mk hli hsp, fun z => ?_⟩
  simp only [Module.Basis.mk_apply]
  exact key z

end GlobalTheory.Mem.R3.Rw.RowBasis

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 2000000 in
theorem rrT_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (b : Bool) (E : Hs) (jE : E.T →ₗ[ℂ] (y.C F.lv2).Amb 0), Function.Injective jE → LinearMap.range jE = (y.C F.lv2).EEc b → ∃ n c Xo, RrT F y b jE n c Xo := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH y b E jE hinj hrange
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h2 : (R.toCx3 F).H2 F.cr b := (hCx.what₂ b).1
  have hW : (lv (F.fc (R.toCx3 F).zs) b).WF := hCx.wf b
  have hp : (R.toCx3 F).H4pos := hCx.h4pos
  have hE : R.models_HE := hP.char.base.models.HE
  have hEEc : (y.C F.lv2).EEc b = (R.EEat (R.toRealDat.levR F.lv2 b)).map
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap := rfl
  have hEEl : (R.toCx3 F).EEl b =
      Tw.sub _ ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)).comap R.HE.e) := rfl
  set s : Bool := twAt D.what₂.embLL A3.A.v0 with hs
  let g : (Fin ((R.toCx3 F).data F.cr b).D → ℂ) → (y.C F.lv2).Amb 0 := fun z =>
    PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z)))
  have gadd : ∀ z z', g (z + z') = g z + g z' := by
    intro z z'
    have h := map_add ((R.toCx3 F).iC F.cr b A3.A.μ0) z z'
    exact (congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) h).trans
      ((congrArg PiTensorProduct.lift (map_add R.HE.e _ _)).trans (map_add _ _ _))
  have gsmul : ∀ (a : ℂ) z, g (a • z) = Formalism.IndefR.Links.cj s a • g z := by
    intro a z
    have h := map_smul ((R.toCx3 F).iC F.cr b A3.A.μ0) a z
    exact (congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) h).trans
      ((congrArg PiTensorProduct.lift (map_smul R.HE.e (Formalism.IndefR.Links.cj s a) _)).trans (map_smul _ _ _))
  have ginj : ∀ z, g z = 0 → z = 0 := by
    intro z hz
    have h1 : R.HE.e (Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z)) = 0 :=
      (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).map_eq_zero_iff.1 hz
    have h3 : Tw.out (s := s) (E := R.HE.H) ((R.toCx3 F).iC F.cr b A3.A.μ0 z) = 0 :=
      hE.1 (h1.trans (map_zero R.HE.e).symm)
    have h4 : (R.toCx3 F).iC F.cr b A3.A.μ0 z = 0 := h3
    exact h2.1 (h4.trans (map_zero _).symm)
  have hmem : ∀ z, ∃ w, jE w = g z := by
    intro z
    have h1 : (R.toCx3 F).iC F.cr b A3.A.μ0 z ∈ (R.toCx3 F).EEl b := by
      rw [← h2.2.2]; exact LinearMap.mem_range_self _ z
    rw [hEEl] at h1
    have h5 : g z ∈ (y.C F.lv2).EEc b := by
      rw [hEEc]
      exact ⟨_, h1, rfl⟩
    rw [← hrange] at h5
    exact h5
  have hsurj : ∀ w, ∃ z, jE w = g z := by
    intro w
    have h1 : jE w ∈ (y.C F.lv2).EEc b := hrange ▸ LinearMap.mem_range_self jE w
    rw [hEEc] at h1
    obtain ⟨u, hu, hwu⟩ := h1
    have hu' : u ∈ LinearMap.range R.HE.e := by
      rw [hE.2.1]
      exact GlobalTheory.Mem.Th.EEat_le_triv R.toRealDat _ hu
    obtain ⟨h, rfl⟩ := hu'
    have hh : Tw.mk s h ∈ (R.toCx3 F).EEl b := by rw [hEEl]; exact hu
    rw [← h2.2.2] at hh
    obtain ⟨z, hz⟩ := hh
    refine ⟨z, ?_⟩
    rw [← hwu]
    exact (congrArg (fun u => (PiTensorProduct.lift (R.HE.e (Tw.out (s := s) (E := R.HE.H) u)) : (y.C F.lv2).Amb 0)) hz).symm
  obtain ⟨c, hc⟩ := RowBasis.exists_basis_semi (Formalism.IndefR.Links.cj s) (Formalism.IndefR.Links.cj_cj s) g gadd gsmul ginj jE hinj hmem hsurj
  have hsg : ∀ a : D.what₂.LL, Formalism.IndefR.Links.cj s (A3.A.v0.embedding a) = D.what₂.embLL a := by
    intro a
    rw [emb_eq D.what₂.embLL A3.A.v0 a, sgAt_mk D.what₂.embLL R.hv0, Formalism.IndefR.Links.cj_cj]
  refine ⟨((R.toCx3 F).data F.cr b).D, c,
    fun v => (((R.toCx3 F).data F.cr b).XE v).submatrix (Fin.cast rfl) (Fin.cast rfl), ?_⟩
  refine ⟨rfl, fun x => ?_, fun v => ⟨rfl, ?_⟩⟩
  · have := hc (cpt A3.A.v0.embedding x)
    simp only [cpt, hsg] at this
    exact this.trans rfl
  · have hdet := Formalism.IndefR.Cx.PrincipalLevelLattice.frames (R.toCx3 F) F.cr b hW h2 hp v
    have hs := Matrix.det_submatrix_equiv_self (finCongr (rfl : ((R.toCx3 F).data F.cr b).D = ((R.toCx3 F).data F.cr b).D))
      (((R.toCx3 F).data F.cr b).XE v)
    exact (congrArg IsUnit hs).mpr hdet

end GlobalTheory.Mem.R3.Rw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowBasisFromReferenceTupleQuotientStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowBasis_from_referenceTuple_quotient : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (b : Bool) (E : Hs) (jE : E.T →ₗ[ℂ] (y.C F.lv2).Amb 0), Function.Injective jE → LinearMap.range jE = (y.C F.lv2).EEc b → ∃ n c Xo, RrT F y b jE n c Xo := by
  first | exact @GlobalTheory.Mem.R3.Rw.rrT_exists | exact GlobalTheory.Mem.R3.Rw.rrT_exists | (intros; apply GlobalTheory.Mem.R3.Rw.rrT_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardBaseRowsLabelEqRowsPartFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardBaseRowsLabelEqRowsPartFinrank
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

noncomputable section

namespace GlobalTheory.Mem.R3.LabCount

theorem card_filter_eq_finrank {V Q ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Fintype ι] [Fintype Q] [DecidableEq Q] (x : ι → V) (hx : LinearIndependent ℂ x) (lab : ι → Q)
    (P : Q → Submodule ℂ V) (hmem : ∀ k, x k ∈ P (lab k))
    (hsum : ∑ q, Module.finrank ℂ (P q) ≤ Fintype.card ι) (p : Q) :
    (Finset.univ.filter (fun k => lab k = p)).card = Module.finrank ℂ (P p) := by
  have hle : ∀ q, (Finset.univ.filter (fun k => lab k = q)).card ≤ Module.finrank ℂ (P q) := by
    intro q
    let y : {k // lab k = q} → P q := fun k => ⟨x k.1, by have h := hmem k.1; rwa [k.2] at h⟩
    have hy : LinearIndependent ℂ y := by
      apply LinearIndependent.of_comp (P q).subtype
      exact hx.comp Subtype.val Subtype.val_injective
    have := hy.fintype_card_le_finrank
    rwa [Fintype.card_subtype] at this
  have htot : ∑ q, (Finset.univ.filter (fun k => lab k = q)).card = Fintype.card ι := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (lab k))]
  by_contra hne
  have hlt : (Finset.univ.filter (fun k => lab k = p)).card < Module.finrank ℂ (P p) := lt_of_le_of_ne (hle p) hne
  have : ∑ q, (Finset.univ.filter (fun k => lab k = q)).card < ∑ q, Module.finrank ℂ (P q) :=
    Finset.sum_lt_sum (fun q _ => hle q) ⟨p, Finset.mem_univ _, hlt⟩
  omega

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  let j : (Tw.sub s V) ≃+ V :=
    { toFun := fun x => ⟨Tw.out x.1, x.2⟩
      invFun := fun x => ⟨Tw.mk s x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hb : Function.Bijective (cj s) :=
    Function.bijective_iff_has_inverse.2 ⟨cj s, cj_cj s, cj_cj s⟩
  have h := rank_eq_of_equiv_equiv (cj s) j hb (fun _ _ => rfl)
  unfold Module.finrank
  rw [h]

theorem twSub_inf (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V W : Submodule ℂ E) :
    Tw.sub s (V ⊓ W) = Tw.sub s V ⊓ Tw.sub s W := Submodule.ext fun _ => Iff.rfl

theorem cnt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ cOf : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, HasLab Y σ (cOf σ)) → ∀ p : A3.fam3.base3.Ix, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  intro hWe hDs hHC hCu D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hHo hHost cOf hLab p
  have hR := complex_data_conditions_base_level_of_primitive_links hHo.ok hHo.sep hP.char hHo.prim
  have hRow := hR.rowHyp false
  have hE : (R.toCx3 F).PartsE false := hHo.prim.sumE false
  have hinj : Function.Injective R.HE.e := hP.char.base.models.HE.1
  set L : Submodule ℂ R.HE.H := (R.toRealDat.EEat (R.toRealDat.levR F.lv2 false)).comap R.HE.e with hL
  have hpart : ∀ q, Module.finrank ℂ ((R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) =
      Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H) := by
    intro q
    rw [← finrank_twSub (twAt D.what₂.embLL A3.A.v0) (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H), twSub_inf]
    rfl
  have hEp : Module.finrank D.what₂.LL ((s0Of R F).Ep p) = Module.finrank ℂ (R.EEp3 p ⊓ L : Submodule ℂ R.HE.H) := by
    rw [← hpart p]
    exact (R.toCx3 F).finrank_Ep F.cr false hRow.wf hRow.h2 hRow.h3 hE p
  let C := toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop
  let lf : Mult.MMap (R.MY 0) ≃ₗ[ℂ] C.Amb 0 := PiTensorProduct.lift
  let φ : R.HE.H →ₗ[ℂ] C.Amb 0 := lf.toLinearMap ∘ₗ R.HE.e
  have hφ : Function.Injective φ := lf.injective.comp hinj
  have hmemL : ∀ y : R.HE.H, φ y ∈ C.EEc false → y ∈ L := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 hy
    have : z = R.HE.e y := lf.injective hzy
    subst this
    exact hz
  choose x hxP hxe using fun k => (hLab (D.what₂.ft0 k)).2 k rfl
  have hxφ : ∀ k, φ (x k) = (Y.Iz.jE (D.what₂.onb0 k)).1 := fun k => (hxe k).symm
  have hli0 : LinearIndependent ℂ (fun k => ((Y.Iz.jE (D.what₂.onb0 k)).1 : C.Amb 0)) := by
    have h1 := D.what₂.onb0.toBasis.linearIndependent.map' Y.Iz.jE.toLinearMap Y.Iz.jE.ker
    have h2 := h1.map' (C.EEc false).subtype (Submodule.ker_subtype _)
    exact h2
  have hli : LinearIndependent ℂ x := by
    apply LinearIndependent.of_comp φ
    convert hli0 using 1
    funext k
    exact hxφ k
  have hxL : ∀ k, x k ∈ L := fun k => hmemL _ (by rw [hxφ k]; exact (Y.Iz.jE (D.what₂.onb0 k)).2)

  have hDim : Module.finrank ℂ L ≤ Fintype.card (Fin D.what₂.D0) := by
    let g0 : L →ₗ[ℂ] C.EEc false :=
      (φ.domRestrict L).codRestrict (C.EEc false) (fun y => Submodule.mem_map_of_mem (f := lf.toLinearMap) y.2)
    let g : L →ₗ[ℂ] D.what₂.EE0 := Y.Iz.jE.symm.toLinearMap ∘ₗ g0
    have hg : Function.Injective g := by
      intro a b h
      have h1 : g0 a = g0 b := Y.Iz.jE.symm.injective h
      have h2 : φ a = φ b := congrArg Subtype.val h1
      exact Subtype.ext (hφ h2)
    calc Module.finrank ℂ L ≤ Module.finrank ℂ D.what₂.EE0 := LinearMap.finrank_le_finrank_of_injective hg
      _ = Fintype.card (Fin D.what₂.D0) := Module.finrank_eq_card_basis D.what₂.onb0.toBasis
  have hsum : ∑ q, Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H) ≤ Fintype.card (Fin D.what₂.D0) := by
    calc ∑ q, Module.finrank ℂ (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H)
        = ∑ q, Module.finrank ℂ ((R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) :=
          Finset.sum_congr rfl fun q _ => (hpart q).symm
      _ = Module.finrank ℂ (⨆ q, (R.toCx3 F).EEp q ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) :=
          (Formalism.IndefR.Cx.finrank_iSup_eq_sum _ (CxData.indep_of_orth _ hE.1)).symm
      _ ≤ Module.finrank ℂ ((R.toCx3 F).EEl false) := Submodule.finrank_mono (iSup_le fun q => inf_le_right)
      _ = Module.finrank ℂ L := finrank_twSub _ L
      _ ≤ Fintype.card (Fin D.what₂.D0) := hDim
  have hcard := card_filter_eq_finrank x hli (fun k => cOf (D.what₂.ft0 k)) (fun q => (R.EEp3 q ⊓ L : Submodule ℂ R.HE.H))
    (fun k => ⟨hxP k, hxL k⟩) hsum p
  have hcount : ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ =
      (Finset.univ.filter (fun k => cOf (D.what₂.ft0 k) = p)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := D.what₂.ft0) (t := Finset.univ.filter (fun σ => cOf σ = p))
      (fun k hk => by simpa using hk)]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [Finset.mem_filter] at hσ
    rw [Formalism.BasicNotions.Rows.Data.nRows0, Fintype.card_subtype, Finset.filter_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ hσ.2, h⟩
    · intro h; exact h.2
  rw [hEp, ← hcard]
  exact hcount

end GlobalTheory.Mem.R3.LabCount

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardBaseRowsLabelEqRowsPartFinrankStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_baseRows_label_eq_rowsPart_finrank : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ cOf : D.what₂.FT → A3.fam3.base3.Ix, (∀ σ, HasLab Y σ (cOf σ)) → ∀ p : A3.fam3.base3.Ix, ∑ σ ∈ Finset.univ.filter (fun σ => cOf σ = p), D.what₂.nRows0 σ = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  first | exact @GlobalTheory.Mem.R3.LabCount.cnt | exact GlobalTheory.Mem.R3.LabCount.cnt | (intros; apply GlobalTheory.Mem.R3.LabCount.cnt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfMemISup
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointEigenMemISup
namespace GlobalTheory.JointEigenSupremum

theorem joint_eigen_mem_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M]
    (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (E : κ → Submodule ℂ M)
    (hE : ∀ (k : κ), ∀ y ∈ E k, ∀ (i : ι), (op i : M → M) y = χ k i • y)
    (ψ : ι → ℂ) (x : M) (hx0 : x ≠ (0 : M)) (hx : ∀ i, (op i : M → M) x = ψ i • x)
    (hmem : x ∈ ⨆ k, E k) : ∃ k, χ k = ψ := by
  classical
  by_contra hne
  push_neg at hne
  have hstab : ∀ (s : Finset κ) (i : ι), ∀ z ∈ ⨆ k ∈ s, E k, (op i : M → M) z ∈ ⨆ k ∈ s, E k := by
    intro s i z hz
    have hle : (⨆ k ∈ s, E k) ≤ (⨆ k ∈ s, E k).comap (op i) := by
      refine iSup₂_le fun k hk y hy => ?_
      rw [Submodule.mem_comap, hE k y hy i]
      exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun k (_ : k ∈ s) => E k) k hk) hy)
    exact hle hz
  have key : ∀ s : Finset κ, ∀ x : M, (∀ i, (op i : M → M) x = ψ i • x) →
      x ∈ ⨆ k ∈ s, E k → x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ h; simpa using h
    | insert k0 s hk0 ih =>
      intro x hx h
      rw [Finset.iSup_insert, Submodule.mem_sup] at h
      obtain ⟨y, hy, z, hz, rfl⟩ := h
      obtain ⟨i, hi⟩ : ∃ i, χ k0 i ≠ ψ i := by
        by_contra h'
        push_neg at h'
        exact hne k0 (funext h')
      have hw : (op i : M → M) z - χ k0 i • z ∈ ⨆ k ∈ s, E k :=
        Submodule.sub_mem _ (hstab s i z hz) (Submodule.smul_mem _ _ hz)
      have h1 := hx i
      rw [map_add (f := _), hE k0 y hy i, smul_add] at h1
      have h2 : (op i : M → M) z = ψ i • y + ψ i • z - χ k0 i • y := by
        rw [← h1]; abel
      have hw' : (op i : M → M) z - χ k0 i • z = (ψ i - χ k0 i) • (y + z) := by
        rw [h2]; module
      rw [hw'] at hw
      have heig : ∀ j, (op j : M → M) ((ψ i - χ k0 i) • (y + z)) = ψ j • ((ψ i - χ k0 i) • (y + z)) := by
        intro j
        rw [map_smul, hx j, smul_comm]
      have h0 := ih _ heig hw
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hi
      · exact h
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  exact hx0 (key s x hx hs)

end GlobalTheory.JointEigenSupremum

theorem GlobalTheory.JointEigenSupremum.target : ∀ {ι κ M : Type} [inst : AddCommGroup M] [inst_1 : Module ℂ M] (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (E : κ → Submodule ℂ M), (∀ (k : κ), ∀ y ∈ E k, ∀ (i : ι), (op i : M → M) y = χ k i • y) → ∀ (ψ : ι → ℂ) (x : M), x ≠ (0 : M) → (∀ (i : ι), (op i : M → M) x = ψ i • x) → x ∈ ⨆ (k : κ), E k → ∃ (k : κ), χ k = ψ :=
  fun op χ E hE ψ x hx0 hx hmem => GlobalTheory.JointEigenSupremum.joint_eigen_mem_iSup op χ E hE ψ x hx0 hx hmem
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.EigCarry

theorem exists_eq_of_mem_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M] (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ)
    (E : κ → Submodule ℂ M) (hE : ∀ k, ∀ y ∈ E k, ∀ i, op i y = χ k i • y) (ψ : ι → ℂ) (x : M) (hx0 : x ≠ 0)
    (hx : ∀ i, op i x = ψ i • x) (hmem : x ∈ ⨆ k, E k) : ∃ k, χ k = ψ := by
  first
  | (rename_i h_3 h_4; revert ι κ M h_3 h_4 op χ E hE ψ x hx0 hx hmem; exact @_root_.GlobalTheory.JointEigenSupremum.target)
  | exact @_root_.GlobalTheory.JointEigenSupremum.target
  | exact _root_.GlobalTheory.JointEigenSupremum.target
  | (apply _root_.GlobalTheory.JointEigenSupremum.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenSupremum.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenSupremum.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenSupremum.target ..)

theorem exists_part_eq {ι C H M : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup M] [Module ℂ M] (e : H →ₗ[ℂ] M)
    (op : ι → Module.End ℂ M) (χ : C → ι → ℂ) (N : Submodule ℂ M) (E : C → Submodule ℂ H)
    (hE : ∀ c y, y ∈ E c ↔ e y ∈ N ∧ ∀ i, op i (e y) = χ c i • e y) (S : C → Prop) (c : C) (x : H) (hx : x ∈ E c)
    (h0 : e x ≠ 0) (hs : x ∈ ⨆ (c' : C) (_ : S c'), E c') : ∃ c', S c' ∧ E c' = E c := by
  have hle : (⨆ (c' : C) (_ : S c'), E c') ≤ (⨆ k : {c' // S c'}, (E k.1).map e).comap e := by
    refine iSup₂_le fun c' hc' y hy => ?_
    exact (le_iSup (fun k : {c' // S c'} => (E k.1).map e) ⟨c', hc'⟩) ⟨y, hy, rfl⟩
  obtain ⟨k, hk⟩ := exists_eq_of_mem_iSup op (fun k : {c' // S c'} => χ k.1) (fun k => (E k.1).map e)
    (by rintro k _ ⟨y, hy, rfl⟩; exact ((hE _ y).1 hy).2) (χ c) (e x) h0 ((hE c x).1 hx).2 (hle hs)
  refine ⟨k.1, k.2, ?_⟩
  ext y
  rw [hE, hE]
  exact and_congr_right fun _ => forall_congr' fun q => by rw [congrFun hk q]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem ssetF_base {R : RealDat3 D A3 Ks} {F : Face3 D A3} (hC : R.WeakCharacterisation F) : SsetF R.toRealDat A3.A.μ0 = R.SF := by
  have hL := hC.base.lev
  have hQ : R.Q A3.A.μ0 = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun PP hP => ?_
    refine (hL.Q_ram A3.A.μ0 PP).2 (Or.inl hP) ?_
    rw [hL.xi_base]
    intro x hx
    rfl
  ext v
  rw [hC.inert.SF v]
  unfold SsetF
  rw [hQ]
  simp only [Finset.union_empty, Finset.mem_image]
  refine exists_congr fun PP => and_congr_right fun _ => ?_
  exact ⟨fun h => h ▸ rfl, fun h => HeightOneSpectrum.ext h⟩

abbrev RowOp (R : RealDat3 D A3 Ks) : Type :=
  {q : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D (Yc D 0)) //
    Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.SF q.1 q.2.1 q.2.2}

theorem mem_eEc_iff (R : RealDat3 D A3 Ks) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (x : R.HE.H) :
    x ∈ R.EEc c ↔ R.HE.e x ∈ Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) ∧
      ∀ q : RowOp R, heckeOn (R.MY 0) q.1.2.2 (R.HE.e x) = c q.1.1 (dualLab q.1.2.1) • R.HE.e x := by
  unfold RealDat3.EEc partDual partFull
  simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  exact and_congr_right fun _ => ⟨fun h q => h _ _ _ q.2, fun h P d S hS => h ⟨(P, d, S), hS⟩⟩

theorem carries_of_mem (R : RealDat3 D A3 Ks) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (x : R.HE.H)
    (hx : x ∈ R.EEc c) (h0 : R.HE.e x ≠ 0) (hs : x ∈ ⨆ p, R.EEp3 p) : ∃ p, R.Carries p c := by
  have hle : (⨆ p, R.EEp3 p) ≤ ⨆ (c') (_ : ∃ p, R.Carries p c'), R.EEc c' :=
    iSup_le fun p => iSup₂_le fun c' hc' =>
      le_iSup₂_of_le (f := fun c' (_ : ∃ p, R.Carries p c') => R.EEc c') c' ⟨p, hc'⟩ le_rfl
  obtain ⟨c', ⟨p, hp⟩, heq⟩ := exists_part_eq R.HE.e (fun q : RowOp R => heckeOn (R.MY 0) q.1.2.2)
    (fun c q => c q.1.1 (dualLab q.1.2.1)) _ R.EEc (mem_eEc_iff R) (fun c' => ∃ p, R.Carries p c') c x hx h0 (hle hs)
  exact ⟨p, heq ▸ hp.1, (Submodule.map_mono heq.ge).trans hp.2⟩

theorem mem_iSup_eEp3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool) (hP : (R.toCx3 F).PartsE b) (x : R.HE.H)
    (hx : R.HE.e x ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 b)) : x ∈ ⨆ p, R.EEp3 p := by
  have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) x ∈ (R.toCx3 F).EEl b := hx
  rw [← hP.2] at h1
  have h2 : (⨆ p, (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl b) ≤ Tw.sub (twAt D.what₂.embLL A3.A.v0) (⨆ p, R.EEp3 p) := by
    refine iSup_le fun p => inf_le_left.trans fun y hy => ?_
    exact (le_iSup (fun p => R.EEp3 p) p) hy
  exact h2 h1

theorem carries_of_hasEig : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ (π : D.what₂.FT) c, HasEig R F Y π c → ∃ p, R.Carries p c := by
  intro _ _ _ hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins hHolds _ π c hc
  obtain ⟨hCore, hSF, hEE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hPins.char hHolds.aux.ex
  have hμ : Y.tupT D.what₂.mu0 = A3.A.μ0 := by rw [← Y.tup0, Y.tupT_tup]
  unfold HasEig at hc
  rw [hμ, ssetF_base hPins.char] at hc
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT π)
  obtain ⟨U, hU, hU0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨x, hx, hxU⟩ := GlobalTheory.T.rowTypePart_le_eigensystemPart (s := 1) R.toRealDat F.lv2 hCore
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) R.SF hSF Y.hF Y.PY Y.PW Y.stdPsi.1 Y.stdPsi.2 _ _ c hc b U hU
  rw [← hEE] at hx
  refine carries_of_mem R c x hx (hxU ▸ hU0) (mem_iSup_eEp3 R F b (hHolds.prim.sumE b) x ?_)
  rw [hxU]
  exact hU.1

end GlobalTheory.Mem.EigCarry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRing
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.Dom

theorem mem_O_of_forall_dvr {F : Type} [Field F] (Y : Var F) (y : (ratOf Y).Z) (x : Y.Fn)
    (hx : ∀ V : ValuationSubring Y.Fn, IsDiscreteValuationRing V →
      LocalSubring.range (algebraMap ((ratOf Y).O y) Y.Fn) ≤ V.toLocalSubring → x ∈ V) :
    x ∈ (ratOf Y).O y := by
  haveI := (ratOf Y).lft
  haveI : IsLocallyNoetherian (ratOf Y).Z := LocallyOfFiniteType.isLocallyNoetherian (ratOf Y).s
  haveI : IsNoetherianRing ((ratOf Y).O y) :=
    isNoetherianRing_of_ringEquiv _ ((ratOf Y).stalkEquiv y)
  haveI : Algebra.EssFiniteType ((ratOf Y).O y) Y.Fn :=
    Algebra.EssFiniteType.of_isLocalization Y.Fn (nonZeroDivisors ((ratOf Y).O y))
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (ratOf Y).Z := fun z =>
    ⟨(Y.isNormalScheme).isDomain_stalk z, (Y.isNormalScheme).isIntegrallyClosed_stalk z⟩
  haveI := RatModel.isIntegrallyClosed_O hN y
  by_contra hn
  have hi : ¬ IsIntegral ((ratOf Y).O y) x := fun h => by
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    exact hn a.2
  obtain ⟨V, h1, h2, h3⟩ := GlobalTheory.exists_discreteValuationSubring_dominating_notMem hi
  exact h3 (hx V h1 h2)

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

theorem exists_pt_of_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z)
    (V : ValuationSubring Ω) (hV : LocalSubring.range (algebraMap (M.O z) Ω) ≤ V.toLocalSubring) :
    ∃ v : Sp V ⟶ M.Z, v (IsLocalRing.closedPoint V) = z ∧ spMap (algebraMap V Ω) ≫ v = M.pt ∧
      ∃ σ : IsLocalRing.ResidueField (M.Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V,
        spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ spMap (IsLocalRing.residue _) ≫ M.Z.fromSpecStalk z := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff _ V).1 hV
  let ι : M.O z →+* V := (algebraMap (M.O z) Ω).codRestrict V h1
  haveI hι : IsLocalHom ι := ⟨fun r hr => by
    by_contra hn
    obtain ⟨_, hm⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 (h2 r hn)
    exact hm hr⟩
  let g : M.Z.presheaf.stalk z →+* V := ι.comp (M.stalkEquiv z).toRingHom
  haveI : IsLocalHom g := ⟨fun a ha =>
    (isUnit_map_iff (M.stalkEquiv z) a).1 (IsLocalHom.map_nonunit (f := ι) _ ha)⟩
  refine ⟨spMap g ≫ M.Z.fromSpecStalk z, ?_, ?_, IsLocalRing.ResidueField.map g, ?_⟩
  · show M.Z.fromSpecStalk z (spMap g (IsLocalRing.closedPoint V)) = z
    rw [show spMap g (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _ from IsLocalRing.comap_closedPoint g]
    exact Scheme.fromSpecStalk_closedPoint
  · have e : (algebraMap V Ω).comp g = M.stalkHom z := rfl
    have e2 : spMap (M.stalkHom z) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
        Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) z)) := by
      rw [RatModel.stalkHom]
      show Spec.map _ = _
      rw [CommRingCat.ofHom_hom, Spec.map_comp]
      rfl
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    change spMap (M.stalkHom z) ≫ _ = _
    rw [e2, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo M.pt
  · rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.map_comp_residue]

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
  {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}

theorem coBear_swap {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ p₁' : Sp K ⟶ Y₁.X}
    {p₂ p₂' : Sp K ⟶ Y₂.X} (hx : x = x') (hp₁ : p₁ = p₁') (hp₂ : p₂ = p₂')
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂' p₁' := by
  subst hx hp₁ hp₂
  obtain ⟨A, hA, g, hg, b₁, b₂⟩ := h
  exact ⟨A, hA, g, hg, b₂, b₁⟩

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle


open GlobalTheory.FlagBundle.Dom in
theorem dominates_O (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F)
    (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X) (h₁ : Reps Eb S₁ φ₁ f₁)
    (h₂ : Reps Eb S₂ φ₂ f₂) (ψ : Y₂.Fn →ₐ[F] Y₁.Fn) (hψ : ψ.comp φ₂ = φ₁)
    (hg : CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt))
    (y : Y₁.X) : ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  let κ := IsLocalRing.ResidueField (Y₁.X.presheaf.stalk y)
  let py : Sp κ ⟶ Y₁.X := spMap (IsLocalRing.residue _) ≫ Y₁.X.fromSpecStalk y
  obtain ⟨A, hA, h, hh, hb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ h₁ κ py
  obtain ⟨s, ⟨hs, hsb⟩, -⟩ := h₂.2.2 κ (py ≫ f₁) A hA h hh
  refine ⟨s (IsLocalRing.closedPoint κ), fun a ha => ?_⟩
  refine mem_O_of_forall_dvr Y₁ y (ψ a) fun V _ hV => ?_
  obtain ⟨v, -, hv1, σ, hv2⟩ := exists_pt_of_le (ratOf Y₁) y V hV
  haveI : IsProper (f₂ ≫ X.str) := by
    rw [show f₂ ≫ X.str = Y₂.str from h₂.1.inducedModelMorphism_comp_structureMap]
    infer_instance
  haveI : IsProper f₂ := IsProper.of_comp f₂ X.str
  have hψ' : spMap ψ.toRingHom ≫ spMap φ₂.toRingHom = spMap φ₁.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψ]
    rfl
  have hq : (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁) := by
    have e1 : (ratOf Y₂).pt ≫ f₂ = spMap φ₂.toRingHom ≫ (ratOf X).pt := h₂.1
    have e2 : (ratOf Y₁).pt ≫ f₁ = spMap φ₁.toRingHom ≫ (ratOf X).pt := h₁.1
    erw [Category.assoc, e1, ← Category.assoc, hψ', ← e2, ← Category.assoc, hv1]
  obtain ⟨ℓ, ⟨hℓ1, hℓ2⟩, -⟩ :=
    GlobalTheory.ModelPoints.existsUnique_extension f₂ (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) (v ≫ f₁) hq
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v ℓ hℓ1.symm
    (by erw [hℓ2, ← Category.assoc, hv1]; exact hg)
  have hbc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ κ (IsLocalRing.ResidueField V) σ
    (py ≫ f₁) py s ⟨A, hA, h, hh, hb, hsb⟩
  have hpv : spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ py := hv2
  have E1 : (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hpv)))
  have E2 : (spMap σ ≫ s) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap σ ≫ ·) hs).trans (Category.assoc _ _ _).symm)
  have E3 : spMap (IsLocalRing.residue V) ≫ v ≫ f₁ = (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ :=
    (congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1.symm).trans (Category.assoc _ _ _).symm
  have E4 : spMap σ ≫ py ≫ f₁ = (spMap σ ≫ s) ≫ f₂ :=
    (congrArg (spMap σ ≫ ·) hs.symm).trans (Category.assoc _ _ _).symm
  have e : spMap (IsLocalRing.residue V) ≫ ℓ = spMap σ ≫ s :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ h₂ h₁ _ (spMap (IsLocalRing.residue V) ≫ ℓ)
      (spMap σ ≫ s) (spMap σ ≫ py) E1 E2 (coBear_swap E3 hpv rfl hinc) (coBear_swap E4 rfl rfl hbc)
  have hℓc : ℓ (IsLocalRing.closedPoint V) = s (IsLocalRing.closedPoint κ) := by
    have h3 : ℓ (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) =
        s (spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) :=
      congrArg (fun t : Sp (IsLocalRing.ResidueField V) ⟶ Y₂.X =>
        t (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) e
    have h4 : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
        IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
    have h5 : spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint κ :=
      Subsingleton.elim (α := PrimeSpectrum κ) _ _
    rw [h4, h5] at h3
    exact h3
  have hsp : ℓ (IsLocalRing.closedPoint V) ⤳ s (IsLocalRing.closedPoint κ) := hℓc ▸ specializes_rfl
  have k1 := RatModel.val_spMap_comp (M := ratOf Y₂) (algebraMap V Y₁.Fn) ℓ hsp ⟨a, ha⟩
  have k2 := RatModel.val_spMap_comp (M := ratOf Y₂) ψ.toRingHom (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, ha⟩
  have k4 := (RatModel.valLoc_eq_val (M := ratOf Y₂) (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩).trans
    (RatModel.val_pt (M := ratOf Y₂) a)
  have k3 : ψ a = algebraMap V Y₁.Fn (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩) := by
    calc ψ a = ψ.toRingHom (RatModel.valLoc (ratOf Y₂).pt _
          ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩) :=
          (congrArg ψ.toRingHom k4).symm
      _ = (ratOf Y₂).val (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) a := k2.symm
      _ = (ratOf Y₂).val (spMap (algebraMap V Y₁.Fn) ≫ ℓ) a :=
          congrArg (fun t : Sp Y₁.Fn ⟶ Y₂.X => (ratOf Y₂).val t a) hℓ2.symm
      _ = _ := k1
  rw [k3]
  exact (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩).2

end GlobalTheory.FlagBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRingStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundle_functionFieldMap_dominates_localRings : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ y : Y₁.X, ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  first | exact @GlobalTheory.FlagBundle.dominates_O | exact GlobalTheory.FlagBundle.dominates_O | (intros; apply GlobalTheory.FlagBundle.dominates_O <;> assumption)
end
end
