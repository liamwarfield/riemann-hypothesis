module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltration
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LieBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem card_frameIdx (Dw : Datum H) :
    Fintype.card (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
  have h := FlagTan.isHalf_psiSet H
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [h.sum_univ (fun σ => Dw.mult σ), ← h.card, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rcases FlagTan.mult_conj (Dw := Dw) τ with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
  exact add_comm _ _

theorem isSplitting_embK {l : Level H} (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => (algebraMap c.F K).comp (embK c σ) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  refine EigenSplit.isSplitting_of_isDomain (S := c.F) (σ := fun σ : E →+* ℂ => embK c σ) (fun σ σ' e => ?_)
    (NumberField.Embeddings.card E ℂ) _ (isUnit_iff_ne_zero.2 (by exact_mod_cast NumberField.discr_ne_zero E))
  have e' : embF c σ = embF c σ' := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e
  ext x
  have := congrArg (fun f : E →+* c.F => ((f x : c.F) : ℂ)) e'
  exact this

theorem finrank_quot_fil (P : GlobalTheory.Published.AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {g : ℕ}
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Module.Finite K (HdR A ⧸ Fil A) ∧ Module.finrank K (HdR A ⧸ Fil A) = g := by
  obtain ⟨-, -, hfin, -, hrk⟩ := P.2.1 K A g hA hg
  have hF : Module.finrank K (PrimitiveSubmodule A) = g := by
    have := hrk ⟨⊥, Ideal.isPrime_bot⟩
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  let e : (HdR A ⧸ Fil A) ≃ₗ[K] Module.Dual K (PrimitiveSubmodule A) := Subspace.quotAnnihilatorEquiv (PrimitiveSubmodule A)
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Subspace.dual_finrank_eq, hF]

theorem span_eq_top {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O]
    (a : OAct O A) {ι : Type} [Fintype ι] [DecidableEq ι] {χ : ι → O →+* K} (hχ : EigenSplit.IsSplitting χ)
    {m : ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hub : ∀ σ k, IsTangent (ub σ k))
    (hbasis : ∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) →
      ∃ cf, IsLieComb cf (ub σ) w) :
    Submodule.span K (Set.range fun k : Σ σ, Fin (m σ) => Serre.Lie.mk a (ub k.1 k.2) (hub _ _)) = ⊤ := by
  let ρ : O →+* Module.End K (Serre.Lie a) := Module.toModuleEnd K (S := O) (Serre.Lie a)
  rw [eq_top_iff]
  intro x _
  rw [← EigenSplit.sum_proj hχ ρ x]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hx := EigenSplit.proj_mem hχ ρ σ x
  obtain ⟨cf, hcf⟩ := hbasis σ (EigenSplit.proj hχ ρ σ x).hom (EigenSplit.proj hχ ρ σ x).isTangent fun z =>
    congrArg Serre.Lie.hom (EigenSplit.mem_eigenSub.1 hx z)
  have e : EigenSplit.proj hχ ρ σ x = ∑ i, cf i • Serre.Lie.mk a (ub σ i) (hub σ i) :=
    Serre.Lie.ext ((Serre.Lie.isLieComb_iff cf (fun i => Serre.Lie.mk a (ub σ i) (hub σ i)) _).1 hcf)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, i⟩, rfl⟩)

end GlobalTheory.LieBasis

namespace GlobalTheory.LieBasis

theorem lifts_basis_mod_fil : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
    (y : FrPt Xo c K) {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π →
    ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) →
    ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) →
    Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ ∧
      LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  intro P E _ _ _ H Dw l Xo c K _ _ y A _ π hπ ub hub hb hhb
  classical
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have : IsCommMonObj A := hA.comm
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  obtain ⟨ub', hub', htan, -, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  have e : ub' = ub := funext fun σ => funext fun k => Over.OverMorphism.ext
    (hπ.1.hom_ext ((hub' σ k).trans (hub σ k).symm) ((Over.w (ub' σ k)).trans (Over.w (ub σ k)).symm))
  subst e
  have L := (P.2.1 K A _ hA gA).1
  let v : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → Serre.Lie a := fun k => Serre.Lie.mk a (ub' k.1 k.2) (htan _ _)
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    span_eq_top a (isSplitting_embK c K) ub' htan hbasis
  obtain ⟨hfin, hdim⟩ := finrank_quot_fil P hA gA
  have hcard : Fintype.card (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) = Module.finrank K (Serre.Lie a) := by
    rw [← (L.quotEquiv a).finrank_eq, hdim, card_frameIdx]
  have hind : LinearIndependent K v := linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hcard
  have hv : (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = (L.quotEquiv a).symm ∘ v := by
    funext k
    rw [Function.comp_apply, LinearEquiv.eq_symm_apply, LieExact.quotEquiv_mk, L.toLie_eq_iff]
    exact hhb k
  refine ⟨?_, hv ▸ hind.map' _ (L.quotEquiv a).symm.ker⟩
  have h1 : Submodule.map (Fil A).mkQ (Submodule.span K (Set.range hb)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span K (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) = ⊤
    rw [hv, Set.range_comp, eq_top_iff]
    intro q _
    have hq : (L.quotEquiv a) q ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.mem_top
    simpa using hq
  have h2 := congrArg (Submodule.comap (Fil A).mkQ) h1
  rwa [Submodule.comap_map_mkQ, Submodule.comap_top, sup_comm] at h2

end GlobalTheory.LieBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltrationStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K) {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) → ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) → Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ ∧ LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  first | exact @GlobalTheory.LieBasis.lifts_basis_mod_fil | exact GlobalTheory.LieBasis.lifts_basis_mod_fil | (intros; apply GlobalTheory.LieBasis.lifts_basis_mod_fil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModifResidueFieldMapSurjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false
noncomputable section
open GlobalTheory.Vanishing.H0 GlobalTheory.CompHS

namespace GlobalTheory.HSApp

theorem modif_generic_map {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) [IrreducibleSpace M.X] (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ) :
    genericPoint M.X ∈ M.opn ∧ M.σ (genericPoint M.X) = η := by
  have := M.iso
  have hne : (M.opn : Set M.X).Nonempty := M.dense.nonempty
  have hm : genericPoint M.X ∈ M.opn :=
    ((genericPoint_spec M.X).mem_open_set_iff M.opn.isOpen).2 (by simpa using hne)
  refine ⟨hm, ?_⟩
  obtain ⟨x, hx⟩ := (M.σ ∣_ U).surjective ⟨η, hη⟩
  have hx' : M.σ x.1 = η := (morphismRestrict_base_coe M.σ U x).symm.trans (congrArg Subtype.val hx)
  have hcl : η ∈ closure {M.σ (genericPoint M.X)} := by
    rw [← hx', ← Set.image_singleton]
    exact image_closure_subset_closure_image M.σ.continuous
      ⟨x.1, by rw [(genericPoint_spec M.X).def]; trivial, rfl⟩
  have hgen : IsGenericPoint (M.σ (genericPoint M.X)) Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hcl) isClosed_closure
  exact hgen.eq hg

theorem modif_residueFieldMap_surjective {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) (z : M.X) (hz : z ∈ M.opn) : Function.Surjective (M.σ.residueFieldMap z).hom := by
  have := M.iso
  have : IsIso (M.σ.stalkMap z) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap M.σ U ⟨z, hz⟩)).1
      (((isIso_iff_isIso_stalkMap (M.σ ∣_ U)).1 M.iso).2 ⟨z, hz⟩)
  have hst : Function.Surjective (M.σ.stalkMap z).hom := (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨a, rfl⟩ := M.X.residue_surjective z y
  obtain ⟨b, rfl⟩ := hst a
  exact ⟨Y.residue _ b, congr($(Scheme.residue_residueFieldMap M.σ z).hom b)⟩

theorem modif_residueFieldMap_germ {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    (hnb : NoBase hB W U) (z : M.X) (hz : z ∈ M.opn) (i : B.ι) (hi : M.σ z ∈ B.U i) :
    ∃ c : M.X.residueField z, c ≠ 0 ∧ ∀ w : W,
      (M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (germ i (M.σ z) (memTop _) hi w.1)) =
        c * (M.sys Δ φ f abelian₂).toLinSys.val (Adelic.resPt z) (toSec (Δ.lift w)) := by
  set S := (M.sys Δ φ f abelian₂).toLinSys
  have hp : Adelic.ptOf (Adelic.resPt z) = z := Adelic.ptOf_resPt z
  have hj : z ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z))) :=
    (congrArg (fun y => y ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z)))) hp).mp
      (S.mem_chartAt (Adelic.ptOf (Adelic.resPt z)))
  set j := S.chartAt (Adelic.ptOf (Adelic.resPt z))
  have hi0 : M.σ z ∈ B.U (j.1 PUnit.unit) := mem_pull.1 hj.1
  have hu : IsUnit (ger z hj.2 (Δ.t.f j.2)) :=
    (isUnit_ger_iff _ hj.2).2 ((Δ.mem_nonzeroLocus z).2 (M.notMem_support hnb z (M.off_eq.ge hz)))
  refine ⟨(M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (tr B (M.σ z) i (j.1 PUnit.unit)).val) *
    (M.X.residue z).hom (ger z hj.2 (Δ.t.f j.2)), mul_ne_zero ?_ ?_, fun w => ?_⟩
  · exact (map_ne_zero _).2 (((tr B (M.σ z) i (j.1 PUnit.unit)).isUnit.map (Y.residue (M.σ z)).hom).ne_zero)
  · exact (hu.map (M.X.residue z).hom).ne_zero
  have hv : S.val (Adelic.resPt z) (toSec (Δ.lift w)) = (M.X.residue z).hom (germ j z (memTop z) hj (Δ.lift w)) := by
    rw [Adelic.LinSys.val, Adelic.projSys.valR_resPt z _ hj, ← ger_toSec]
    rfl
  rw [hv, germ_change i (j.1 PUnit.unit) (M.σ z) (memTop _) hi hi0, map_mul, map_mul, mul_assoc]
  congr 1
  rw [← map_mul (M.X.residue z).hom, Δ.germ_lift w j z hj]
  refine Eq.trans ?_ (congrArg (M.X.residue z).hom
    (GlobalTheory.Vanishing.H0.germ_pull (p := p) M.σ le_top j.1 z (memTop z) hj.1 w.1)).symm
  exact congr($(Scheme.residue_residueFieldMap M.σ z).hom _)

theorem sys_birational_of_ratField {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    [IsIntegral M.X] (hnb : NoBase hB W U) (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ)
    (hr : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) η hη = ⊤) :
    (M.sys Δ φ f abelian₂).toLinSys.Birational := by
  classical
  obtain ⟨hmem, hσ⟩ := modif_generic_map M η hη hg
  subst hσ
  set S := (M.sys Δ φ f abelian₂).toLinSys with hS
  set z := genericPoint M.X with hz
  have hsurj := modif_residueFieldMap_surjective M z hmem
  have hbpf : S.BasePointFree := Δ.iSup_nonzeroLocus (f.b.map φ).span_eq
  obtain ⟨j0, hj0⟩ := Function.ne_iff.1 (hbpf.coords_ne_zero (Adelic.resPt z))
  have key : ∀ w : W, S.val (Adelic.resPt z) (toSec (Δ.lift w)) / S.coords (Adelic.resPt z) j0 ∈
      S.ratioField (Adelic.resPt z) := fun w => by
    set u := f.b.equivFun (φ.symm w)
    have e : toSec (Δ.lift w) = S.comb u := by
      refine (bijective_ofSec_top (p := M.str)).1 ?_
      rw [ofSec_toSec]
      refine Eq.trans ?_ (M.ofSec_comb Δ φ f abelian₂ u).symm
      simp [u]
    rw [e, S.val_comb, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨j, j0, rfl⟩))
  have hgen : ∀ r ∈ {r | ∃ (i : B.ι) (hi : M.σ z ∈ B.U i) (s s' : H0 p B U),
      s ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      s' ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      r = (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s) / (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s')},
      (M.σ.residueFieldMap z).hom r ∈ S.ratioField (Adelic.resPt z) := by
    rintro r ⟨i, hi, _, _, ⟨w, rfl⟩, ⟨w', rfl⟩, rfl⟩
    obtain ⟨c, hc, hcw⟩ := modif_residueFieldMap_germ M Δ φ f abelian₂ hnb z hmem i hi
    rw [germ_restr, germ_restr, map_div₀, hcw, hcw, mul_div_mul_left _ _ hc,
      ← div_div_div_cancel_right₀ hj0]
    exact div_mem (key w) (key w')
  have hle : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) (M.σ z) hη ≤
      (S.ratioField (Adelic.resPt z)).comap (M.σ.residueFieldMap z).hom :=
    Subfield.closure_le.2 hgen
  refine ⟨z, genericPoint_spec M.X, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle (hr.symm ▸ Subfield.mem_top y)

theorem geo_second_birational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₂ → (h.geo f₁ f₂ th k).second.Birational := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hR
  obtain ⟨η, hη, hgen, hrat⟩ := hR
  have : IsIntegral R.X := (h.geo f₁ f₂ th k).isIntegral
  refine sys_birational_of_ratField R.toModif R.Δ₂ h.ext₂.equiv f₂ k.abelian₂ h.free₂ η hη hgen ?_
  convert hrat using 2
  ext s
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨h.ext₂.equiv.symm w, by rw [← h.ext₂.restr_equiv, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨h.ext₂.equiv g, h.ext₂.restr_equiv g⟩

end GlobalTheory.HSApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyReal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyReal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section

namespace GlobalTheory.AdelicFourierSch

open Filter GlobalTheory.WeylFourier GlobalTheory.RatWeilOp GlobalTheory.WeylBij


open scoped Classical in
theorem fourier_mem_schA_std (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F))
    [μ.IsAddHaarMeasure] : ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  have hunr := psiUnr_eventually ψ hψ
  letI mI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  letI mV : ∀ v : Pl (F := F), MeasurableSpace (κ → Fv F v) := fun _ => borel _
  haveI bV : ∀ v : Pl (F := F), BorelSpace (κ → Fv F v) := fun _ => ⟨rfl⟩
  obtain ⟨μi, hμi⟩ : ∃ μ : Measure (κ → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μv, hμv, hμv1⟩ : ∃ μv : ∀ v : Pl (F := F), Measure (κ → Fv F v), (∀ v, (μv v).IsAddHaarMeasure) ∧
      ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := by
    let K : ∀ v : Pl (F := F), TopologicalSpace.PositiveCompacts (κ → Fv F v) := fun v =>
      ⟨⟨Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)),
        isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v⟩, by
          show (interior (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))).Nonempty
          rw [(isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).interior_eq]
          exact ⟨0, fun i _ => (v.adicCompletionIntegers F).zero_mem⟩⟩
    refine ⟨fun v => Measure.addHaarMeasure (K v), fun v => inferInstance, fun v => ?_⟩
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = (K v : Set (κ → Fv F v)) := by
      ext x; simp [K]
    rw [e]
    exact Measure.addHaarMeasure_self
  haveI := hμv
  obtain ⟨c₀, hc₀, hpure⟩ := GlobalTheory.T.integral_adelic_pureTensor_eq_product_local F κ μ μi μv hμv1
  obtain ⟨ei', hei'bij, hei'⟩ := GlobalTheory.T.exists_archimedeanSchwartz_traceFourier_bijective F κ μi
  have hψc : ∀ v, Continuous (GlobalTheory.LatVac.psiAt ψ v) := fun v => GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v
  have hsub : ∀ v, ∀ φ ∈ SB (κ → Fv F v), φ ∈ intSub (GlobalTheory.LatVac.psiAt ψ v) (μv v) := fun v φ hφ y =>
    (hφ.1.continuous.mul ((hψc v).comp (continuous_id.dotProduct continuous_const))).integrable_of_hasCompactSupport
      hφ.2.mul_right
  let ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v => ftE (GlobalTheory.LatVac.psiAt ψ v) (μv v)
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = ft (GlobalTheory.LatVac.psiAt ψ v) (μv v) φ :=
    fun v φ hφ => ftE_eq _ _ (hsub v φ hφ)
  have hbij : ∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := fun v =>
    (GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace F v (GlobalTheory.LatVac.psiAt ψ v) (hψc v) (fun t => GlobalTheory.StdCharFromIsStd.norm_psi hψ _)
      (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) κ (μv v)).congr fun φ hφ => (hev v φ hφ).symm
  have hind : ∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v := by
    filter_upwards [hunr] with v hv
    rw [hev v (ind κ v) (GlobalTheory.StdVacuum.indicator_mem_SB v)]
    exact GlobalTheory.T.integralPointsIndicator_fourier_self_unramified F v (GlobalTheory.LatVac.psiAt ψ v) (fun x => hv x) κ (μv v) (hμv1 v)
  have hpureE : ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), IsFam φ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ intSub ψ μ ∧
      ft ψ μ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := by
    intro f φ hφ
    have hφ' : ∀ y, IsFam (finT ψ φ y) := finT_isFam ψ hψ φ hφ
    have hfun : ∀ y, (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        archT f (fun i => evI F (y i)) (fun i => evI F (x i)) * ∏ᶠ v, finT ψ φ y v (fun i => evFin F v (x i)) :=
      fun y => funext fun x => pure_mul_psi ψ hψ f φ hφ x y
    refine ⟨fun y => ?_, funext fun y => ?_⟩
    · rw [hfun y]
      exact (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).1
    · show ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y) ∂μ = _
      rw [hfun y, (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).2]
      have h2 : ∀ v, ev v (φ v) (fun i => evFin F v (y i)) = ∫ x, finT ψ φ y v x ∂(μv v) := fun v => by
        rw [hev v _ (hφ.1 v)]; rfl
      have h3 : (c₀ • ei' f) (fun i => evI F (y i)) = c₀ * ∫ x, archT f (fun i => evI F (y i)) x ∂μi := by
        have h4 := hei' f (fun i => evI F (y i))
        simp only [archT]
        rw [← h4]
        rfl
      show _ = (c₀ • ei' f) (fun i => evI F (y i)) * ∏ᶠ v, ev v (φ v) (fun i => evFin F v (y i))
      rw [h3, finprod_congr h2]
  let T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ := ftE ψ μ
  have hfam : ∀ φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ, IsFam φ → IsFam fun v => ev v (φ v) := fun φ hφ =>
    ⟨fun v => (hbij v).mapsTo (hφ.1 v), by filter_upwards [hφ.2, hind] with v h1 h2; rw [h1, h2]⟩
  have hTpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), IsFam φ →
      T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := fun f φ hφ =>
    (ftE_eq ψ μ (hpureE f φ hφ).1).trans (hpureE f φ hφ).2
  have hgen := schA_le_span_pure F κ
  have hT_schA : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ := by
    intro Φ hΦ
    refine (Submodule.span_le.2 ?_ : _ ≤ (schA F κ).comap T) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    show T _ ∈ schA F κ
    rw [hTpure f φ hφ]
    exact pure_mem_schA _ _ (hfam φ hφ)
  have hint : ∀ Φ ∈ schA F κ, Φ ∈ intSub ψ μ := fun Φ hΦ => by
    refine (Submodule.span_le.2 ?_ : _ ≤ intSub ψ μ) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    exact (hpureE f φ hφ).1
  intro Φ hΦ
  have h := hT_schA Φ hΦ
  rw [show T Φ = ft ψ μ Φ from ftE_eq ψ μ (hint Φ hΦ)] at h
  exact h

theorem dilate_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {a : F} (ha : a ≠ 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun y => Φ (algebraMap F (AF F) a • y)) ∈ schA F κ := by
  classical
  have hdet : IsUnit (Matrix.diagonal fun _ : κ => a⁻¹).det := by
    rw [Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero ha).isUnit
  have hinv : (Matrix.diagonal fun _ : κ => a⁻¹)⁻¹ = Matrix.diagonal fun _ : κ => a := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    simp [mul_inv_cancel₀ ha]
  have h := GlobalTheory.SympChangeBij.levi_mapsTo _ hdet Φ hΦ
  rw [hinv, Matrix.diagonal_map (map_zero _)] at h
  convert h using 2 with y
  rw [LinearMap.funLeft_apply]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

theorem fourier_mem_schA : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), μ.IsAddHaarMeasure → ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  intro F _ _ hF ψ hψ κ _ _ _ μ hμ Φ hΦ
  have h0 := GlobalTheory.SubstIntertw.isStd_stdChar F
  obtain ⟨a, ha, hψa⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F _ ψ (GlobalTheory.StdCharFromIsStd.isCharAF h0) hψ
  have h := dilate_mem_schA ha (fourier_mem_schA_std F _ h0 κ μ Φ hΦ)
  convert h using 4 with y x
  rw [hψa, dotProduct_smul, smul_eq_mul]

end GlobalTheory.AdelicFourierSch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierMemSchwartzTotallyRealStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFourier_mem_schwartz_totallyReal : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), μ.IsAddHaarMeasure → ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  first | exact @GlobalTheory.AdelicFourierSch.fourier_mem_schA | exact GlobalTheory.AdelicFourierSch.fourier_mem_schA | (intros; apply GlobalTheory.AdelicFourierSch.fourier_mem_schA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionNormComplexPointsEqTwoPiPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionNormComplexPointsEqTwoPiPow
noncomputable section

namespace GlobalTheory.KeyArchNorm

section Value

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth

theorem norm_rule_of_coord {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) (x : KeyIn ℂ) {g : ℕ}
    (hg : g = x.P.g) (u : HolUnif x.P.A x.P.L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {θ : (Fin g → ℂ) → ℂ} {Fd : Set (Fin g → ℂ)} {ξ : ℝ} (hξ : 0 < ξ) (p : Fin x.P.g ≃ Fin g)
    (hA : u.IsAH Hm χ) (hR : u.IsRig x.rig) (hF : u.IsFn x.th θ) (hD : ∀ i, u.IsDiff (Pi.single (p i) 1) (x.v i))
    (hFd : IsAddFundamentalDomain u.Λ Fd volume)
    (hN : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = 1)
    (hH : Hm = ((2 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) :
    ‖(κ ℂ x : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  subst hg
  obtain ⟨⟨Ef, hE, hb⟩, -⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u Hm χ hA
  have := u.discrete
  have hv := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 hE hb hFd
  have hd : Hm.det.re = (2 * ξ) ^ x.P.g := by
    rw [hH, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← Complex.ofReal_pow, Complex.ofReal_re]
  let W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := Matrix.of fun i => Pi.single (p i) 1
  have hW : ‖W.det‖ = 1 := by
    have e : W = (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ).submatrix p id := by
      ext i j
      simp [W, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [e, Matrix.det_permute, Matrix.det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]
  have key := hκ x u Hm W χ θ Fd 1 _ hA hR hF hD hFd hN.symm rfl
  rw [hd] at hv
  rw [hW, eq_inv_of_mul_eq_one_left hv] at key
  have hπ := Real.pi_pos
  simp only [mul_one, one_pow] at key
  rw [← key]
  simp only [mul_pow, pow_mul']
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem norm_rule_of_isOrtho {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {ξ : ℝ} (h0 : 0 < ξ)
    (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom) (hξ : ∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ)
    (hx : (U.X k).IsOrtho x.1) (Φ : FibKey Xo ℂ (U.un k x).x)
    (hΦ : Tied (S := ℂ) e (U.un k x).s (U.un k x).u Φ) :
    ‖(κ ℂ Φ.key : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  obtain ⟨ht, hg, hv⟩ := hΦ
  subst hg
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := OrthoHerm.hm_eq_smul_one E H Dw l Xo c σ r U ξ hσ hU k x W Wu hξ hx
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2
    Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have key := norm_rule_of_coord hκ Φ.key hg u h0 (e.trans W.e.symm) hA hR hF (fun i => by
    obtain ⟨w, hw, hd⟩ := hD _ _ ((U.un k x).tan (e i).1 (e i).2) (W.der (e i).1 (e i).2)
    have hwv : w = Φ.v i :=
      Over.OverMorphism.ext (Φ.m.cart.1.hom_ext (hw.trans (hv i).symm) ((Over.w w).trans (Over.w (Φ.v i)).symm))
    rw [hwv] at hd
    exact hd) hFd Wu.c9 hH
  rw [hg] at key
  exact key

end Value

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH _root_.Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wtOf_fst (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) : (wtOf Dw 0 (-4)).1 (τ, i) = 4 := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hp : i < Dw.p := by simpa [Datum.mult, h] using hi
    rw [wtOf_big _ _ ⟨τ, h⟩ i hp]
    simp
  · have hq : i < Dw.q := by simpa [Datum.mult, h] using hi
    have e := wtOf_small (Dw := Dw) 0 (-4) ⟨conjEmb τ, conj_mem h⟩ i hq
    simp only [AllWt.conjEmb_conjEmb] at e
    rw [e]
    simp

theorem exZ_wtOf : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · rfl
  · exact wtOf_fst τ i i.2

theorem lieFacZ_mul {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {x : ℝ} (hx : 0 < x) :
    lieFacZ Dw x (wtOf Dw 0 (-4)) * (2 * Real.pi * x) ^ (2 * g) = 1 := by
  have hg : ∑ τ : E →+* ℂ, Dw.mult τ = g := by
    have := Fintype.card_congr e
    simpa using this.symm
  have hs : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), ((wtOf Dw 0 (-4)).1 (τ, i) : ℝ)) = 4 * g := by
    rw [← hg, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl fun (i : Fin (Dw.mult τ)) _ => by rw [wtOf_fst τ i i.2]]
    simp [mul_comm]
  have hπ : 0 < 2 * Real.pi * x := by positivity
  rw [lieFacZ, hs, ← Real.exp_log (pow_pos hπ (2 * g)), ← Real.exp_add, Real.log_pow, Real.exp_eq_one_iff]
  push_cast
  ring

end Weight

theorem homN_key_const : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = x) → Nonempty (KeySec Xo c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ C : ℝ, 0 < C ∧ |Real.log C| ≤ 2 * (g : ℝ) * Real.log (2 * Real.pi) ∧ ∀ k, ∀ y ∈ (U.X k).dom, homN U x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C := by
  intro κ _ _ hκ E _ _ _ H Dw l Xo c g e σ r U x K hσ hU hx hS hpq hK hval
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨(2 * Real.pi) ^ (2 * g), by positivity, ?_, fun k y hy => ?_⟩
  · rw [abs_of_nonneg (Real.log_nonneg (one_le_pow₀ hπ)), Real.log_pow]
    push_cast
    exact le_rfl
  have hsec := GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU E H Dw l Xo c σ r U hS hσ hU hpq (wtOf Dw 0 (-4)) (even_wtOf _ _)
    (fun τ i j hij hj => by rw [wtOf_fst τ j hj, wtOf_fst τ i (hij.trans_lt hj)]) K (exZ_wtOf (Dw := Dw) ▸ hK) k
  have hb := FrameDegreeData.bOf_mem (U.X k) hy
  have hz := OrthogonalFrameDomain.rmul_mem_dom (U.X k) hy hb
  have ho := FrameDegreeData.ortho_bOf (U.X k) hy
  have hp := FrameDegreeData.pnorm_rmul (U.X k) _ _ hsec.2.1 y hy _ hb
  generalize rmul y (FrameDegreeData.bOf (U.X k) y) = z at hz ho hp
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : 0 < x := hx k τ₀ ▸ norm_pos_iff.2 ((map_ne_zero τ₀).2 (U.X k).ξ0_ne)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : FibKey Xo ℂ (U.un k ⟨z, hz⟩).x, Tied (S := ℂ) e (U.un k ⟨z, hz⟩).s (U.un k ⟨z, hz⟩).u Φ :=
    @GlobalTheory.KeyFourth.exists_tied E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) hpq
  have hv : rdU U (K : Rul Xo c) k z = (κ ℂ Φ.key : ℂ) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hz, dif_pos]
    exact @hval ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) Φ hΦ
  have hn : (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) z = ‖(κ ℂ Φ.key : ℂ)‖ := by
    simp [Data.pnorm, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho, hv]
  show lieFacZ Dw x _ * (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) y = _
  rw [← hp, hn, norm_rule_of_isOrtho hκ e h0 hσ hU k ⟨z, hz⟩ (hx k) ho Φ hΦ, mul_left_comm, lieFacZ_mul e h0, mul_one]

end GlobalTheory.KeyArchNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionNormComplexPointsEqTwoPiPowStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = x) → Nonempty (KeySec Xo c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ C : ℝ, 0 < C ∧ |Real.log C| ≤ 2 * (g : ℝ) * Real.log (2 * Real.pi) ∧ ∀ k, ∀ y ∈ (U.X k).dom, homN U x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C := by
  first | exact @GlobalTheory.KeyArchNorm.homN_key_const | exact GlobalTheory.KeyArchNorm.homN_key_const | (intros; apply GlobalTheory.KeyArchNorm.homN_key_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCompInfGLProd
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Petersson Formalism.L2.Host
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped ComplexConjugate

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem measurable_chart_prod {φ : GA E a → ℂ} (hφ : Continuous φ) :
    Measurable fun p : GA E a × Lie E a => chart φ p.1 p.2 := by
  classical
  have e : (fun p : GA E a × Lie E a => chart φ p.1 p.2) =
      (Set.univ ×ˢ invSet E a).piecewise (fun p : GA E a × Lie E a => chart φ p.1 p.2) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ Set.univ ×ˢ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      have hp' : ¬ IsUnit (Matrix.of p.2) := fun h => hp ⟨trivial, h⟩
      exact dif_neg hp'
  rw [e]
  exact (GlobalTheory.ConstTermSmooth.continuousOn_chart hφ).measurable_piecewise continuousOn_const
    (isOpen_univ.prod isOpen_invSet).measurableSet

theorem measurable_comp_infGL_prod {F : GA E a → ℂ} (hF : Continuous F) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun p : GA E a × X => F (p.1 * infGL E a (γ p.2)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun p : GA E a × X => F (p.1 * infGL E a (γ p.2))) =
      (fun p : GA E a × Lie E a => chart F p.1 p.2) ∘ fun p : GA E a × X => (p.1, toL (γ p.2).val) :=
    funext fun p => (chart_val F p.1 (γ p.2)).symm
  rw [e]
  exact (measurable_chart_prod hF).comp (measurable_fst.prodMk (h.comp measurable_snd))

theorem IsRapidInf.integrable_norm {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) : Integrable (fun x => ‖k x‖) ν := by
  simpa using hk.2.2 0

theorem kerInf_mem_bddForms {ω : HChar E} {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) {X : Type} [MeasurableSpace X]
    {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ bddForms E a ω := by
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · set_option synthInstance.maxHeartbeats 200000 in
    refine continuous_of_dominated (bound := fun x => ‖k x‖ * C)
      (fun g => (hk.1.mul (hm.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
      (fun g => .of_forall fun x => ?_) (hki.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_mul_const _)))
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · simp only [kerInf, mul_assoc, h.2.1]
  · rw [kerInf, kerInf, ← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, h.2.2.1]; ring
  · exact norm_integral_le_of_norm_le (hki.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

set_option synthInstance.maxHeartbeats 200000 in
theorem pet_kerInf_left {ω : HChar E} (hω : ω.IsUnitary) {F ψ : GA E a → ℂ} (h : F ∈ bddForms E a ω)
    (h' : ψ ∈ bddForms E a ω) {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    pet (latticeGL E a) μ (kerInf ν k γ F) ψ =
      ∫ x, k x * pet (latticeGL E a) μ (fun g => F (g * infGL E a (γ x))) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hki := hk.integrable_norm
  have hm := measurable_comp_infGL_prod h.1 hk.2.1
  have hi : Integrable (fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((integrable_const (C * D)).mul_prod hki).mono'
      (((hk.1.comp measurable_snd).mul hm).mul
        ((Complex.continuous_conj.comp h'.1).measurable.comp measurable_fst)).aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (kerInf_mem_bddForms h hk) h' hD).2]
  simp only [kerInf, ← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (mul_right_mem_bddForms h _) h' hD).2, ← integral_const_mul, mul_assoc]

theorem rspan_central {π : CuspSub E a} {ω : HChar E} (hπ : π.HasCentChar ω) {F : GA E a → ℂ} (hF : F ∈ rspan π)
    (z : Ideles E) (g : GA E a) :
    F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g := by
  have hc := CuspSub.hasCentral_iff.2 hπ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | ∀ (z : Ideles E) g, F (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * F g}
      add_mem' := fun {F F'} hF hF' z g => by simp only [Pi.add_apply, hF z g, hF' z g, mul_add]
      zero_mem' := fun z g => by simp
      smul_mem' := fun c F hF z g => by simp only [Pi.smul_apply, smul_eq_mul, hF z g]; ring }
  refine rspan_le (S := S) (fun φ hφ z g => hc.apply hφ z g) (fun F hF h z g => ?_)
    (fun F hF X _ ν _ k γ _ z g => ?_) hF z g
  · change F (GeneralLinearGroup.scalar (Fin a) z * g * h) = _ * F (g * h)
    rw [mul_assoc]; exact hF z _
  · change ∫ x, k x * F (GeneralLinearGroup.scalar (Fin a) z * g * infGL E a (γ x)) ∂ν =
      _ * ∫ x, k x * F (g * infGL E a (γ x)) ∂ν
    rw [← integral_const_mul]
    congr 1; funext x; rw [mul_assoc, hF z]; ring

theorem pet_rt_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {ψ : GA E a → ℂ}
    (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0) {φ : Sm E a} (hφ : φ ∈ π.V)
    (h : GA E a) : pet (latticeGL E a) μ (fun g => φ.1 (g * h)) ψ = 0 := by
  have hb : ∀ φ ∈ π.V, φ.1 ∈ bddForms E a ω := fun φ hφ =>
    mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
  rw [← infGL_mul_finGL h]
  have e : (fun g => φ.1 (g * (infGL E a (GeneralLinearGroup.map (pInf E) h) *
      finGL E a (GeneralLinearGroup.map (pFin E) h)))) =
      fun g => (finRep E a (GeneralLinearGroup.map (pFin E) h) φ).1 (g * infGL E a (GeneralLinearGroup.map (pInf E) h)) := by
    funext g
    change _ = φ.1 (g * infGL E a _ * finGL E a _)
    rw [mul_assoc]
  rw [e]
  exact GlobalTheory.KeepOrth.pet_translate_eq_zero μ hω hψ hb (fun X => π.stable (.lie X)) (fun φ hφ => (π.cusp φ hφ).1) h0
    (π.stable (.fin _) φ hφ) _

theorem rspan_bdd_pet_eq_zero {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω)
    {ψ : GA E a → ℂ} (hψ : ψ ∈ bddForms E a ω) (h0 : ∀ φ ∈ π.V, pet (latticeGL E a) μ φ.1 ψ = 0)
    {F : GA E a → ℂ} (hF : F ∈ rspan π) :
    F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0 := by
  have hψh : ∀ h : GA E a, (fun g => ψ (g * h)) ∈ bddForms E a ω := mul_right_mem_bddForms hψ
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ bddForms E a ω ∧ ∀ h : GA E a, pet (latticeGL E a) μ F (fun g => ψ (g * h)) = 0}
      add_mem' := fun {F F'} hF hF' => ⟨add_mem hF.1 hF'.1, fun h => by
        rw [pet_add_left μ hω hF.1 hF'.1 (hψh h), hF.2 h, hF'.2 h, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun h => by simp [pet, descend]⟩
      smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, fun h => by
        rw [pet_smul_left, hF.2 h, mul_zero]⟩ }
  have htr : ∀ F ∈ S, ∀ h' : GA E a, (fun g => F (g * h')) ∈ S := fun F hF h' =>
    ⟨mul_right_mem_bddForms hF.1 h', fun h => by
      rw [pet_mul_right_left μ hω hF.1 (hψh h) h']
      have := hF.2 (h'⁻¹ * h)
      simp only [mul_assoc] at this ⊢
      exact this⟩
  refine rspan_le (S := S) (fun φ hφ => ⟨mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ,
    fun h => ?_⟩) htr (fun F hF X _ ν _ k γ hk => ⟨kerInf_mem_bddForms hF.1 hk, fun h => ?_⟩) hF
  · have hb := mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ
    have e := pet_mul_right_left μ hω hb hψ h⁻¹
    rw [inv_inv] at e
    rw [← e]
    exact pet_rt_eq_zero μ hω hπ hψ h0 hφ h⁻¹
  · rw [pet_kerInf_left μ hω hF.1 (hψh h) ν hk]
    exact integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ((htr F hF _).2 h))

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentFrameOfFramedPointCommRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentFrameOfFramedPointCommRing
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

open FrameLift

theorem exists_frame_of_isGrpPullback_ring {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}
    (hπ : IsGrpPullback A Xo.univ.t.G y.x π)
    (a : OAct (𝓞 E) A) (ha : ∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) :
    ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧
      (∀ σ k, IsTangent (ub σ k)) ∧
      (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧
      ∀ σ (w : epsR S ⟶ A), IsTangent w →
        (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) →
        ∃ cf, IsLieComb cf (ub σ) w := by
  choose ub hub using fun σ k => exists_lift hπ (T := epsR S) (y.u σ k) (y.tan σ k).1
  refine ⟨ub, hub, fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k), fun σ k z => ?_, fun σ w ht he => ?_⟩
  · refine (eig_iff hπ (ha z) _ _).1 ?_
    rw [hub]
    exact y.eig σ k z
  · have e : y.u σ = fun i => (ub σ i).left ≫ π := funext fun i => (hub σ i).symm
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [e] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩

end GlobalTheory.KSExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentFrameOfFramedPointCommRingStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧ (∀ σ k, IsTangent (ub σ k)) ∧ (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ ub σ k) ∧ ∀ σ (w : epsR S ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F S (embK c σ z)) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w := by
  first | exact @GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring | exact GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring | (intros; apply GlobalTheory.KSExist.exists_frame_of_isGrpPullback_ring <;> assumption)
end
end
