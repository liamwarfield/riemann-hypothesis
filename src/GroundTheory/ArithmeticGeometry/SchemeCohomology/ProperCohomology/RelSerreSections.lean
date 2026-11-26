module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChange
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackCoherent
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CohFinite

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreAffine
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreLocal
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChangeEmbed
section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChangeTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MvPolynomial
open GroundTheory.Arith.Etale (pullbackUnitApp)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}


variable (A) in
abbrev cmap :
    C(ProjectiveSpectrum.top (grading B n), ProjectiveSpectrum.top (grading A n)) :=
  ProjectiveSpectrum.comap (gradedMap A B n) (irrelevant_le_map A B n)


variable (A) in
abbrev pt (y : ProjectiveSpectrum (grading B n)) : ProjectiveSpectrum (grading A n) :=
  ProjectiveSpectrum.comapFun (gradedMap A B n) (irrelevant_le_map A B n) y

def locMap (y : ProjectiveSpectrum (grading B n)) :
    ProjTwist.Loc (grading A n) (pt A y) →+* ProjTwist.Loc (grading B n) y :=
  Localization.localRingHom _ _
    (gradedMap A B n : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin (n + 1)) B) rfl

lemma locMap_mk (y : ProjectiveSpectrum (grading B n)) (r : MvPolynomial (Fin (n + 1)) A)
    (s : (pt A y).asHomogeneousIdeal.toIdeal.primeCompl) :
    locMap y (Localization.mk r s) =
      Localization.mk (gradedMap A B n r)
        (⟨gradedMap A B n s, s.2⟩ : y.asHomogeneousIdeal.toIdeal.primeCompl) :=
  Localization.localRingHom_mk _ _ _ _ _ _

variable (k : ℤ)

def twistPushSec {V : (projectiveSpace A n).Opens} (s : Γ(twistingSheaf (grading A n) k, V)) :
    Γ(twistingSheaf (grading B n) k, baseChangeMap A B n ⁻¹ᵁ V) :=
  ProjTwist.mkSection (fun y => locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩))
    (by
      intro y
      obtain ⟨W, hyW, iW, i, j, hij, r, t, hr, ht, htn, w⟩ :=
        ProjTwist.isLocallyFraction_val s ⟨pt A y.1, y.2⟩
      refine ⟨W.comap (cmap (B := B) A), hyW, homOfLE (fun z hz => (leOfHom iW) hz), i, j, hij,
        gradedMap A B n r, gradedMap A B n t, (gradedMap A B n).2 hr, (gradedMap A B n).2 ht,
        fun z => htn ⟨pt A z.1, z.2⟩, fun z => ?_⟩
      have e := w ⟨pt A z.1, z.2⟩
      change locMap z.1 (ProjTwist.val s ⟨pt A z.1, _⟩) = _
      change ProjTwist.val s ⟨pt A z.1, _⟩ = _ at e
      rw [e]
      exact locMap_mk _ _ _)

lemma val_app_apply {V : (projectiveSpace A n).Opens} (t : Γ(projectiveSpace A n, V))
    (y : baseChangeMap A B n ⁻¹ᵁ V) :
    ((((baseChangeMap A B n).app V t) : Γ(Proj (grading B n), _)).1 y).val =
      locMap y.1 ((t.1 ⟨pt A y.1, y.2⟩).val) := by
  have : y.1.asHomogeneousIdeal.toIdeal.IsPrime :=
    ProjectiveSpectrum.isPrime (y.1 : ProjectiveSpectrum (grading B n))
  show HomogeneousLocalization.val (HomogeneousLocalization.localRingHom (gradedMap A B n)
    (pt A y.1).asHomogeneousIdeal.toIdeal y.1.asHomogeneousIdeal.toIdeal rfl (t.1 ⟨pt A y.1, y.2⟩)) = _
  exact HomogeneousLocalization.val_localRingHom _

lemma twistPushSec_smul {V : (projectiveSpace A n).Opens} (t : Γ(projectiveSpace A n, V))
    (s : Γ(twistingSheaf (grading A n) k, V)) :
    twistPushSec (B := B) k (t • s) = (baseChangeMap A B n).app V t • twistPushSec (B := B) k s := by
  apply Subtype.ext
  funext y
  show locMap y.1 ((t.1 ⟨pt A y.1, y.2⟩).val * ProjTwist.val s ⟨pt A y.1, y.2⟩) =
    (((baseChangeMap A B n).app V t).1 y).val * locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩)
  exact (map_mul (locMap y.1) _ _).trans (congrArg (· * _) (val_app_apply t y).symm)

lemma twistPushSec_add {V : (projectiveSpace A n).Opens}
    (s s' : Γ(twistingSheaf (grading A n) k, V)) :
    twistPushSec (B := B) k (s + s') = twistPushSec k s + twistPushSec k s' := by
  apply Subtype.ext
  funext y
  show locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩ + ProjTwist.val s' ⟨pt A y.1, y.2⟩) =
    locMap y.1 (ProjTwist.val s ⟨pt A y.1, y.2⟩) + locMap y.1 (ProjTwist.val s' ⟨pt A y.1, y.2⟩)
  exact map_add _ _ _

def twistToPushforward :
    twistingSheaf (grading A n) k ⟶
      (Scheme.Modules.pushforward (baseChangeMap A B n)).obj (twistingSheaf (grading B n) k) :=
  ⟨{ app V := ModuleCat.ofHom (X := (twistingSheaf (grading A n) k).val.obj V)
      (Y := ((Scheme.Modules.pushforward (baseChangeMap A B n)).obj
        (twistingSheaf (grading B n) k)).val.obj V)
      { toFun := fun s => twistPushSec k (V := V.unop) s
        map_add' := fun s s' => twistPushSec_add k s s'
        map_smul' := fun t s => twistPushSec_smul k t s }
     naturality := fun {V V'} i => by
      ext s
      exact Subtype.ext (funext fun y => rfl) }⟩

def pullbackTwistingSheafMap :
    (Scheme.Modules.pullback (baseChangeMap A B n)).obj (twistingSheaf (grading A n) k) ⟶
      twistingSheaf (grading B n) k :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap A B n)).homEquiv _ _).symm
    (twistToPushforward k)

lemma pullbackTwistingSheafMap_unit {V : (projectiveSpace A n).Opens}
    (s : Γ(twistingSheaf (grading A n) k, V)) :
    (pullbackTwistingSheafMap (B := B) k).app _ (pullbackUnitApp (baseChangeMap A B n) _ V s) =
      twistPushSec k s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap A B n)).homEquiv_unit
    (twistingSheaf (grading A n) k) (twistingSheaf (grading B n) k)
    (pullbackTwistingSheafMap k))
  rw [pullbackTwistingSheafMap, Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun g => (Scheme.Modules.Hom.app g V) s) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h2
  exact h2.symm

lemma twistPushSec_upow {u : MvPolynomial (Fin (n + 1)) A} (hu : u ∈ grading A n 1) :
    twistPushSec (B := B) k (ProjTwist.upow (grading A n) hu k) =
      ProjTwist.upow (grading B n) ((gradedMap A B n).2 hu) k := by
  apply Subtype.ext
  funext y
  change locMap y.1 (ProjTwist.val (ProjTwist.upow (grading A n) hu k) ⟨pt A y.1, y.2⟩) =
    ProjTwist.val (ProjTwist.upow (grading B n) ((gradedMap A B n).2 hu) k) ⟨y.1, y.2⟩
  erw [ProjTwist.val_upow, ProjTwist.val_upow]
  unfold ProjTwist.twistFrac
  refine (locMap_mk _ _ _).trans ?_
  congr 1
  · exact map_pow (gradedMap A B n) u _
  · exact Subtype.ext (map_pow (gradedMap A B n) u _)

instance isIso_pullbackTwistingSheafMap :
    IsIso (pullbackTwistingSheafMap (A := A) (B := B) (n := n) k) := by
  apply isIso_of_isBasisOn
  intro y
  obtain ⟨j, hj⟩ := exists_mem_stdOpen_proj ((baseChangeMap A B n).base y)
  refine ⟨baseChangeMap A B n ⁻¹ᵁ stdOpen A n j, hj,
    pullbackUnitApp (baseChangeMap A B n) _ (stdOpen A n j)
      (ProjTwist.upow (grading A n) (X_mem j) k),
    isBasisOn_pullbackUnitApp _ (ProjTwist.isBasisOn_upow _ (X_mem j) k), ?_⟩
  have key : ((preMod _).map (pullbackTwistingSheafMap (B := B) k)).app _
      (pullbackUnitApp (baseChangeMap A B n) _ (stdOpen A n j)
        (ProjTwist.upow (grading A n) (X_mem j) k)) =
      ProjTwist.upow (grading B n) ((gradedMap A B n).2 (X_mem j)) k :=
    (pullbackTwistingSheafMap_unit k _).trans (twistPushSec_upow k _)
  rw [key]
  exact ProjTwist.isBasisOn_upow _ _ k


variable (A B n) in
def pullbackTwistingSheafIso :
    (Scheme.Modules.pullback (baseChangeMap A B n)).obj (twistingSheaf (grading A n) k) ≅
      twistingSheaf (grading B n) k :=
  asIso (pullbackTwistingSheafMap k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

universe u

noncomputable section

namespace ProjSpace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ} {Y : Scheme.{u}}


variable (A B n) in
def baseChangeIso :
    projectiveSpace B n ≅
      pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  (isPullback_baseChange A B n).isoPullback

lemma baseChangeIso_inv_baseChangeMap :
    (baseChangeIso A B n).inv ≫ baseChangeMap A B n = pullback.fst _ _ :=
  (isPullback_baseChange A B n).isoPullback_inv_fst

lemma baseChangeIso_inv_toSpecBase :
    (baseChangeIso A B n).inv ≫ toSpecBase B n = pullback.snd _ _ :=
  (isPullback_baseChange A B n).isoPullback_inv_snd

def toBaseChange (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    Y ⟶ projectiveSpace B n :=
  ι ≫ (baseChangeIso A B n).inv

instance (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [IsClosedImmersion ι] : IsClosedImmersion (toBaseChange ι) := by
  rw [toBaseChange]
  infer_instance

lemma toBaseChange_baseChangeMap
    (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    toBaseChange ι ≫ baseChangeMap A B n = ι ≫ pullback.fst _ _ := by
  rw [toBaseChange]
  calc
    _ = ι ≫ ((baseChangeIso A B n).inv ≫ baseChangeMap A B n) := by rw [Category.assoc]
    _ = _ := congrArg (fun f => ι ≫ f) (baseChangeIso_inv_baseChangeMap (A := A) (B := B) (n := n))

lemma toBaseChange_toSpecBase
    (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    toBaseChange ι ≫ toSpecBase B n = ι ≫ pullback.snd _ _ := by
  rw [toBaseChange]
  calc
    _ = ι ≫ ((baseChangeIso A B n).inv ≫ toSpecBase B n) := by rw [Category.assoc]
    _ = _ := congrArg (fun f => ι ≫ f) (baseChangeIso_inv_toSpecBase (A := A) (B := B) (n := n))


variable (A) in
def twistingSheafBaseChangeIso (g : Y ⟶ projectiveSpace B n) (k : ℤ) :
    ProjScheme.twistingSheaf (g ≫ baseChangeMap A B n) k ≅ ProjScheme.twistingSheaf g k :=
  ((Scheme.Modules.pullbackComp g (baseChangeMap A B n)).app _).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (pullbackTwistingSheafIso A B n k)


variable (A) in
def twistBaseChangeIso (g : Y ⟶ projectiveSpace B n) (F : Y.Modules) (k : ℤ) :
    ProjScheme.twist (g ≫ baseChangeMap A B n) F k ≅ ProjScheme.twist g F k :=
  whiskerLeftIso F (twistingSheafBaseChangeIso A g k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}


variable (A) in
def baseHom {V : X.Opens} (hV : IsAffineOpen V) : CommRingCat.of A ⟶ Γ(X, V) :=
  Spec.preimage (hV.fromSpec ≫ (X ↘ Spec (.of A)))


variable (A) in
abbrev baseAlgebra {V : X.Opens} (hV : IsAffineOpen V) : Algebra A Γ(X, V) :=
  (baseHom A hV).hom.toAlgebra

variable (A) in
lemma specMap_baseAlgebra {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, V))) = hV.fromSpec ≫ (X ↘ Spec (.of A)) := by
  change Spec.map (CommRingCat.ofHom (baseHom A hV).hom) = _
  rw [CommRingCat.ofHom_hom]
  exact Spec.map_preimage _

variable (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

abbrev graph : X' ⟶ pullback (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)) :=
  pullback.lift i ψ h

instance isClosedImmersion_graph [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))] :
    IsClosedImmersion (graph i ψ h) := by
  have : IsClosedImmersion (graph i ψ h ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst _ _)


variable (A) in
abbrev overV {V : X.Opens} (hV : IsAffineOpen V) :
    pullback (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) hV.fromSpec ⟶
      pullback (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)) :=
  pullback.fst _ _

lemma preimage_opensRange_overV {V : X.Opens} (hV : IsAffineOpen V) :
    graph i ψ h ⁻¹ᵁ (overV (N := N) A hV).opensRange = ψ ⁻¹ᵁ V := by
  have e1 : (overV (N := N) A hV).opensRange = (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) ⁻¹ᵁ hV.fromSpec.opensRange :=
    Scheme.Hom.opensRange_pullbackFst _ _
  rw [e1, hV.opensRange_fromSpec, ← Scheme.Hom.comp_preimage, pullback.lift_snd]

def restrictT {V : X.Opens} (hV : IsAffineOpen V) :
    pullback (graph i ψ h) (overV (N := N) A hV) ⟶
      pullback (graph i ψ h) (overV (N := N) A hV).opensRange.ι :=
  pullback.map _ _ _ _ (𝟙 _)
    (IsOpenImmersion.isoOfRangeEq (overV (N := N) A hV) (overV (N := N) A hV).opensRange.ι
      Subtype.range_coe.symm).hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id]; exact (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm)

instance {V : X.Opens} (hV : IsAffineOpen V) : IsIso (restrictT (N := N) i ψ h hV) := by
  unfold restrictT
  infer_instance

lemma inv_restrictT_fst {V : X.Opens} (hV : IsAffineOpen V) :
    inv (restrictT (N := N) i ψ h hV) ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [IsIso.inv_comp_eq, restrictT, pullback.lift_fst, Category.comp_id]

def restrictIso {V : X.Opens} (hV : IsAffineOpen V) :
    (ψ ⁻¹ᵁ V).toScheme ≅ pullback (graph i ψ h) (overV (N := N) A hV) :=
  X'.isoOfEq (preimage_opensRange_overV i ψ h hV).symm ≪≫
    (pullbackRestrictIsoRestrict (graph i ψ h) (overV (N := N) A hV).opensRange).symm ≪≫
    (asIso (restrictT i ψ h hV)).symm

lemma restrictIso_hom_fst {V : X.Opens} (hV : IsAffineOpen V) :
    (restrictIso (N := N) i ψ h hV).hom ≫ pullback.fst _ _ = (ψ ⁻¹ᵁ V).ι := by
  simp only [restrictIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    inv_restrictT_fst, pullbackRestrictIsoRestrict_inv_fst, Scheme.isoOfEq_hom_ι]


variable (A) in
def pasteIso {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    pullback (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) hV.fromSpec ≅
      pullback (ProjSpace.toSpecBase A N) (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, V)))) :=
  letI := baseAlgebra A hV
  pullbackLeftPullbackSndIso _ _ _ ≪≫ pullback.congrHom rfl (specMap_baseAlgebra A hV).symm

variable (A) in
lemma pasteIso_hom_fst {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    (pasteIso (N := N) A hV).hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [pasteIso, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.map]
  erw [pullback.lift_fst]
  rw [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

variable (A) in
lemma pasteIso_hom_snd {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    (pasteIso (N := N) A hV).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [pasteIso, Iso.trans_hom, Category.assoc, pullback.congrHom, asIso_hom, pullback.map]
  erw [pullback.lift_snd]
  rw [Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

def embed {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    (ψ ⁻¹ᵁ V).toScheme ⟶
      pullback (ProjSpace.toSpecBase A N) (Spec.map (CommRingCat.ofHom (algebraMap A Γ(X, V)))) :=
  (restrictIso i ψ h hV).hom ≫ pullback.snd _ _ ≫ (pasteIso A hV).hom

instance isClosedImmersion_embed [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))]
    {V : X.Opens} (hV : IsAffineOpen V) : IsClosedImmersion (embed i ψ h hV) := by
  unfold embed
  infer_instance

lemma embed_fst {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embed i ψ h hV ≫ pullback.fst _ _ = (ψ ⁻¹ᵁ V).ι ≫ i := by
  have hc : pullback.snd (graph i ψ h) (overV (N := N) A hV) ≫ overV A hV =
      pullback.fst _ _ ≫ graph i ψ h := pullback.condition.symm
  have hp := pasteIso_hom_fst (N := N) A hV
  simp only [embed, Category.assoc]
  rw [hp, ← Category.assoc (pullback.snd _ _) (pullback.fst _ _), show pullback.fst (pullback.snd
    (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A))) hV.fromSpec = overV A hV from rfl, hc,
    Category.assoc, pullback.lift_fst, ← Category.assoc, restrictIso_hom_fst]

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

theorem IsCoherent.of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (hM : IsCoherent M) :
    IsCoherent N := by
  obtain ⟨hq, hf⟩ := hM
  refine ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hq, fun U hU => ?_⟩
  have := hf U hU
  let φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    { toFun := e.hom.app U
      map_add' := map_add _
      map_smul' := fun r m => Scheme.Modules.Hom.app_smul e.hom r m }
  refine Module.Finite.of_surjective φ fun n => ⟨e.inv.app U n, ?_⟩
  change (e.inv ≫ e.hom).app U n = n
  rw [e.inv_hom_id]
  rfl

theorem IsCoherent.restrict {X U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] {G : X.Modules}
    (hG : IsCoherent G) : IsCoherent (G.restrict f) :=
  IsCoherent.of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app G).symm
    (isCoherent_pullback f hG)

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}
  (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

abbrev overBase {V : X.Opens} (hV : IsAffineOpen V) : (ψ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) :=
  letI := baseAlgebra A hV
  ⟨embed i ψ h hV ≫ pullback.snd _ _⟩

def embedProj {V : X.Opens} (hV : IsAffineOpen V) : (ψ ⁻¹ᵁ V).toScheme ⟶ projectiveSpace Γ(X, V) N :=
  letI := baseAlgebra A hV
  embed i ψ h hV ≫ (ProjSpace.isPullback_baseChange A Γ(X, V) N).isoPullback.inv

instance isClosedImmersion_embedProj [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))]
    {V : X.Opens} (hV : IsAffineOpen V) : IsClosedImmersion (embedProj i ψ h hV) := by
  letI := baseAlgebra A hV
  unfold embedProj
  infer_instance

lemma embedProj_isOver {V : X.Opens} (hV : IsAffineOpen V) :
    letI := overBase i ψ h hV
    (embedProj i ψ h hV).IsOver (Spec (.of Γ(X, V))) := by
  letI := baseAlgebra A hV
  letI := overBase i ψ h hV
  refine ⟨?_⟩
  change embedProj i ψ h hV ≫ ProjSpace.toSpecBase Γ(X, V) N =
    embed i ψ h hV ≫ pullback.snd _ _
  rw [embedProj, Category.assoc, IsPullback.isoPullback_inv_snd]

lemma embedProj_baseChangeMap {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embedProj i ψ h hV ≫ ProjSpace.baseChangeMap A Γ(X, V) N = (ψ ⁻¹ᵁ V).ι ≫ i := by
  letI := baseAlgebra A hV
  rw [embedProj, Category.assoc, IsPullback.isoPullback_inv_fst, embed_fst]

def twistRestrictIso {V : X.Opens} (hV : IsAffineOpen V) (G : X'.Modules) (k : ℤ) :
    ProjScheme.twist (embedProj i ψ h hV) (G.restrict (ψ ⁻¹ᵁ V).ι) k ≅
      (ProjScheme.twist i G k).restrict (ψ ⁻¹ᵁ V).ι :=
  letI := baseAlgebra A hV
  (ProjSpace.twistBaseChangeIso A (embedProj i ψ h hV) (G.restrict (ψ ⁻¹ᵁ V).ι) k).symm ≪≫
    eqToIso (congrArg (fun g => ProjScheme.twist g (G.restrict (ψ ⁻¹ᵁ V).ι) k)
      (embedProj_baseChangeMap i ψ h hV)) ≪≫
    restrictTwistIso (ψ ⁻¹ᵁ V).ι i G k

attribute [local instance] algebraOfOver

theorem exists_vanishing_finite [IsClosedImmersion i] [IsSeparated (X ↘ Spec (.of A))]
    {V : X.Opens} (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (G : X'.Modules)
    (hG : IsCoherent G) :
    letI := overBase i ψ h hV
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      (∀ q : ℕ, Subsingleton
        (Sheaf.H.{u} (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ V).ι)) (q + 1))) ∧
      Module.Finite Γ(X, V)
        (Sheaf.H.{u} (modulesAb ((ProjScheme.twist i G n).restrict (ψ ⁻¹ᵁ V).ι)) 0) := by
  letI := overBase i ψ h hV
  haveI := embedProj_isOver i ψ h hV
  have hGr : IsCoherent (G.restrict (ψ ⁻¹ᵁ V).ι) := hG.restrict _
  obtain ⟨q₀, hq₀⟩ := ProjScheme.exists_subsingleton_H_twist.{u} (embedProj i ψ h hV) _ hGr
  refine ⟨q₀, fun n hn => ⟨fun q => ?_, ?_⟩⟩
  · have h1 := hq₀ n hn (q + 1) (Nat.succ_pos q)
    exact (H.linearEquivOfIso.{u} Γ(X, V) (twistRestrictIso i ψ h hV G n) (q + 1)).toEquiv.subsingleton_congr.1
      h1
  · have hc : IsCoherent (ProjScheme.twist (embedProj i ψ h hV) (G.restrict (ψ ⁻¹ᵁ V).ι) n) :=
      isCoherent_tensor_of_invertible hGr (ProjScheme.isInvertibleSheaf_twistingSheaf _ _)
    have h2 := ProjScheme.finite_H.{u} (embedProj i ψ h hV) _ hc 0
    exact Module.Finite.equiv (H.linearEquivOfIso.{u} Γ(X, V) (twistRestrictIso i ψ h hV G n) 0)

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace RelSerre

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} [X.Over (Spec (.of A))] {N : ℕ}
  (i : X' ⟶ projectiveSpace A N) (ψ : X' ⟶ X)
  (h : i ≫ ProjSpace.toSpecBase A N = ψ ≫ (X ↘ Spec (.of A)))

lemma embed_snd {V : X.Opens} (hV : IsAffineOpen V) :
    letI := baseAlgebra A hV
    embed i ψ h hV ≫ pullback.snd _ _ = ψ ∣_ V ≫ hV.isoSpec.hom := by
  letI := baseAlgebra A hV
  rw [← cancel_mono hV.fromSpec, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι]
  have hc : pullback.snd (graph i ψ h) (overV (N := N) A hV) ≫ overV A hV =
      pullback.fst _ _ ≫ graph i ψ h := pullback.condition.symm
  have hp := pasteIso_hom_snd (N := N) A hV
  have hq : pullback.snd (pullback.snd (ProjSpace.toSpecBase A N) (X ↘ Spec (.of A)))
      hV.fromSpec ≫ hV.fromSpec = overV A hV ≫ pullback.snd _ _ := pullback.condition.symm
  simp only [embed, Category.assoc]
  rw [reassoc_of% hp, hq, reassoc_of% hc, pullback.lift_snd, ← Category.assoc, restrictIso_hom_fst]

lemma app_eqToHom_apply {X X' : Scheme.{u}} (ψ : X' ⟶ X) {U U' : X.Opens} (hU : U' = U)
    {W W' : X'.Opens} (h1 : W = ψ ⁻¹ᵁ U') (h2 : W' = W) (b : Γ(X, U)) :
    X'.presheaf.map (eqToHom h2).op (X'.presheaf.map (eqToHom h1).op
      (ψ.app U' (X.presheaf.map (eqToHom hU).op b))) =
      X'.presheaf.map (eqToHom (h2.trans (h1.trans (by rw [hU])))).op (ψ.app U b) := by
  subst hU
  subst h1
  subst h2
  simp

attribute [local instance] algebraOfOver

lemma algebraMap_overBase {V : X.Opens} (hV : IsAffineOpen V) (b : Γ(X, V)) :
    letI := overBase i ψ h hV
    X'.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((ψ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(X', (ψ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      ψ.app V b := by
  letI := overBase i ψ h hV
  have s1 : algebraMap Γ(X, V) Γ((ψ ⁻¹ᵁ V).toScheme, ⊤) b = (ψ ∣_ V).appTop (V.topIso.inv b) := by
    change (embed i ψ h hV ≫ pullback.snd _ _).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [embed_snd, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (app_eqToHom_apply ψ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp


omit [X.Over (Spec (.of A))] in
lemma smul_restrict_top (M : X'.Modules) (U : X'.Opens) (a : Γ(U.toScheme, ⊤))
    (y : Γ(M.restrict U.ι, ⊤)) :
    M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
      ((modulesAbMap (smulHom (M.restrict U.ι) a)).hom.app (op ⊤) y) =
      X'.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
        (a : Γ(X', U.ι ''ᵁ ⊤)) •
        M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top U).symm).op
          (y : Γ(M, U.ι ''ᵁ ⊤)) := by
  have e1 : (modulesAbMap (smulHom (M.restrict U.ι) a)).hom.app (op ⊤) y =
      restrictTop (X := U.toScheme) ⊤ a • y := rfl
  have e2 : restrictTop (X := U.toScheme) ⊤ a = a := by
    simp [restrictTop]; rfl
  have e3 : (a • y : Γ(M.restrict U.ι, ⊤)) =
      ((U.ι.appIso ⊤).inv a • (@id Γ(M, U.ι ''ᵁ ⊤) y) : Γ(M, U.ι ''ᵁ ⊤)) := rfl
  rw [e1, e2, e3, Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact Scheme.Modules.map_smul M (eqToHom (Scheme.Opens.ι_image_top U).symm) a y

def H0ToSections {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    letI := overBase i ψ h hV
    Sheaf.H.{u} (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward ψ).obj M, V) :=
  letI := overBase i ψ h hV
  { toFun := fun x => M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op
      (Sheaf.H.equiv₀ (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) isTerminalTop x :
        Γ(M, (ψ ⁻¹ᵁ V).ι ''ᵁ ⊤))
    map_add' := fun x y => by
      rw [map_add (f := _)]
      exact map_add _ _ _
    map_smul' := fun b x => by
      rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
      refine (smul_restrict_top M (ψ ⁻¹ᵁ V) _ _).trans ?_
      refine (congrArg (· • _) (algebraMap_overBase i ψ h hV b)).trans ?_
      exact (smul_pushforward ψ M b _).symm }

lemma H0ToSections_bijective {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    Function.Bijective (H0ToSections i ψ h hV M) := by
  letI := overBase i ψ h hV
  exact (ConcreteCategory.bijective_of_isIso (M.presheaf.map
    (eqToHom (Scheme.Opens.ι_image_top (ψ ⁻¹ᵁ V)).symm).op)).comp
    (Sheaf.H.equiv₀ (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) isTerminalTop).bijective

theorem finite_sections_pushforward {V : X.Opens} (hV : IsAffineOpen V) (M : X'.Modules) :
    letI := overBase i ψ h hV
    Module.Finite Γ(X, V) (Sheaf.H.{u} (modulesAb (M.restrict (ψ ⁻¹ᵁ V).ι)) 0) →
      Module.Finite Γ(X, V) Γ((Scheme.Modules.pushforward ψ).obj M, V) := by
  letI := overBase i ψ h hV
  intro hfin
  exact Module.Finite.of_surjective (H0ToSections i ψ h hV M) (H0ToSections_bijective i ψ h hV M).2

end RelSerre

end

end GroundTheory.Arith.SchemeCoh
