module

public import Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
public import Development.EtaleCohomology.EtaleSheaves.PropertyDescent.LeafPropsDescendOf
public import Development.EtaleCohomology.EtaleSheaves.EtStagePf
public import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoPf

def LeafSecInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), Injective F → ∀ U : Scheme.{0},
  Module.Injective (ULift.{1} R) (Sec F U)

def LeafZModInjFlat : Prop := ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M],
  Module.Injective (ULift.{1} (ZMod q)) M → Module.Flat (ULift.{1} (ZMod q)) M

def LeafTensQIsoGen : Prop := ∀ (R : Type) [CommRing R] {I I' J S T : Cx R} (f : I ⟶ I'), QuasiIso f →
  I.IsStrictlyGE 0 → I'.IsStrictlyGE 0 → J.IsStrictlyGE 0 →
  (∀ (n : ℤ) (U : Scheme.{0}), Module.Flat (ULift.{1} R) (Sec (J.X n) U)) →
  ∀ (σ : Pair I J S) (τ : Pair I' J T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map (f.f s) a) b) →
  QuasiIso ι

theorem resAug_quasiIso (R : Type) [CommRing R] (F : Shv R) : QuasiIso (resAug F) := by
  unfold resAug; exact @InjectiveResolution.instQuasiIsoIntι' _ _ _ _ _

theorem res_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (res R F).IsStrictlyGE 0 := by
  unfold res; infer_instance

theorem sgl_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (sgl F).IsStrictlyGE 0 := by
  infer_instance

theorem LeafTensQIso_of (hgen : LeafTensQIsoGen) (hinj : LeafSecInj) (hflat : LeafZModInjFlat) :
    LateralTheory.E.LeafExtTensPf.LeafTensQIso := by
  intro q _ i S T σ τ hσ hτ ι hι
  exact hgen (ZMod q) (resAug (tw q 0)) (resAug_quasiIso _ _) (sgl_strictlyGE _ _) (res_strictlyGE _ _)
    (res_strictlyGE _ _) (fun n U => hflat q _ (hinj _ _ (LateralTheory.E.LeafExtTensPf.res_injective _ _ n) U)) σ τ hσ hτ ι hι

end LateralTheory.E.LeafTensQIsoPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSHSysPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHSysPf
open LateralTheory.E.E4 LateralTheory.E.LeafVanBStalkPf

def Cof {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (_ : IsSepClosed Ω) (ω : c.pt →+* Ω),
    ∀ (j : J) (E : Type) (_ : CommRing E) (_ : Algebra (D.obj j) E) (_ : Algebra.Etale (D.obj j) E) (ψ : E →+* Ω),
      ψ.comp (algebraMap (D.obj j) E) = ω.comp (c.ι.app j).hom →
      ∃ (j' : J) (g : j ⟶ j') (φ : E →+* D.obj j'), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
        ω.comp ((c.ι.app j').hom.comp φ) = ψ

theorem unit_of_cof {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) {Ω : Type} [Field Ω] (ω : c.pt →+* Ω)
    (H : ∀ (j : J) (E : Type) (_ : CommRing E) (_ : Algebra (D.obj j) E) (_ : Algebra.Etale (D.obj j) E) (ψ : E →+* Ω),
      ψ.comp (algebraMap (D.obj j) E) = ω.comp (c.ι.app j).hom →
      ∃ (j' : J) (g : j ⟶ j') (φ : E →+* D.obj j'), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
        ω.comp ((c.ι.app j').hom.comp φ) = ψ)
    (a : c.pt) (ha : ω a ≠ 0) : IsUnit a := by
  obtain ⟨j, f, rfl⟩ := Limits.Concrete.isColimit_exists_rep D hc a
  have hu : IsUnit (ω ((c.ι.app j).hom f)) := isUnit_iff_ne_zero.2 ha
  have : Algebra.Etale (D.obj j) (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  obtain ⟨j', g, φ, h1, -⟩ := H j (Localization.Away f) inferInstance inferInstance this
    (IsLocalization.Away.lift f (g := ω.comp (c.ι.app j).hom) hu) (IsLocalization.Away.lift_comp f hu)
  have e1 : (c.ι.app j).hom f = (c.ι.app j').hom ((D.map g).hom f) := by
    rw [← CommRingCat.comp_apply, c.w g]
  rw [e1, ← h1, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit f).map ((c.ι.app j').hom.comp φ)

theorem isLocalRing_of_cof {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (hC : Cof D c) : IsLocalRing c.pt := by
  obtain ⟨Ω, _, _, ω, H⟩ := hC
  have key : ∀ a : c.pt, a ∈ nonunits c.pt → ω a = 0 := fun a ha => by
    by_contra h; exact ha (unit_of_cof D c hc ω H a h)
  have : Nontrivial c.pt := ω.domain_nontrivial
  refine IsLocalRing.of_nonunits_add (fun a b ha hb hab => ?_)
  have := hab.map ω
  rw [map_add (f := _), key a ha, key b hb, add_zero] at this
  exact not_isUnit_zero this

open Polynomial in
theorem poly_rep {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) (p : c.pt[X]) : ∃ (j : J) (P : (D.obj j)[X]), P.map (c.ι.app j).hom = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨j1, P1, rfl⟩ := hp
    obtain ⟨j2, P2, rfl⟩ := hq
    refine ⟨IsFiltered.max j1 j2, P1.map (D.map (IsFiltered.leftToMax j1 j2)).hom +
      P2.map (D.map (IsFiltered.rightToMax j1 j2)).hom, ?_⟩
    rw [Polynomial.map_add (f := _), Polynomial.map_map, Polynomial.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, c.w, c.w]
  | monomial n a =>
    obtain ⟨j, f, rfl⟩ := Limits.Concrete.isColimit_exists_rep D hc a
    exact ⟨j, monomial n f, by simp⟩

open Polynomial in
theorem monic_rep {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (hc : IsColimit c) [Nontrivial c.pt] (p : c.pt[X]) (hp : p.Monic) :
    ∃ (j : J) (P : (D.obj j)[X]), P.map (c.ι.app j).hom = p ∧ P.Monic := by
  obtain ⟨j, P, hP⟩ := poly_rep D c hc p
  haveI : Nontrivial (((Functor.const J).obj c.pt).obj j) := inferInstanceAs (Nontrivial c.pt)
  obtain ⟨Q, hQ, -, hm⟩ := lifts_and_degree_eq_and_monic (f := (c.ι.app j).hom) ⟨P, hP⟩ hp
  exact ⟨j, Q, hQ, hm⟩


open Polynomial in
theorem root_of_cof {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    {Ω : Type} [Field Ω] (ω : c.pt →+* Ω)
    (H : ∀ (j : J) (E : Type) (_ : CommRing E) (_ : Algebra (D.obj j) E) (_ : Algebra.Etale (D.obj j) E) (ψ : E →+* Ω),
      ψ.comp (algebraMap (D.obj j) E) = ω.comp (c.ι.app j).hom →
      ∃ (j' : J) (g : j ⟶ j') (φ : E →+* D.obj j'), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
        ω.comp ((c.ι.app j').hom.comp φ) = ψ)
    (j : J) (P : (D.obj j)[X]) (hP : P.Monic) (y : Ω) (hy : (P.map (ω.comp (c.ι.app j).hom)).eval y = 0)
    (hd : (P.derivative.map (ω.comp (c.ι.app j).hom)).eval y ≠ 0) :
    ∃ b : c.pt, (P.map (c.ι.app j).hom).eval b = 0 ∧ ω b = y := by
  let Q : StandardEtalePair (D.obj j) := ⟨P, hP, P.derivative, ⟨1, 0, 1, by ring⟩⟩
  let _ : Algebra (D.obj j) Ω := (ω.comp (c.ι.app j).hom).toAlgebra
  have hm : Q.HasMap y := by
    refine ⟨?_, ?_⟩
    · show aeval y P = 0
      rw [aeval_def, eval₂_eq_eval_map]; exact hy
    · show IsUnit (aeval y (derivative P))
      rw [aeval_def, eval₂_eq_eval_map]; exact isUnit_iff_ne_zero.2 hd
  obtain ⟨j', g, φ, h1, h2⟩ := H j Q.Ring inferInstance inferInstance inferInstance (Q.lift y hm).toRingHom
    (Q.lift y hm).comp_algebraMap
  refine ⟨(c.ι.app j').hom (φ Q.X), ?_, ?_⟩
  · have h0 : aeval Q.X Q.f = 0 := Q.hasMap_X.1
    have := congrArg ((c.ι.app j').hom.comp φ) h0
    rw [map_zero] at this
    rw [← this, aeval_def, hom_eval₂, RingHom.comp_assoc, h1, ← CommRingCat.hom_comp, c.w, Polynomial.eval_map]; rfl
  · have := RingHom.congr_fun h2 Q.X
    exact this.trans (Q.lift_X y hm)

structure NSys {B : Scheme.{0}} (U : B.Etale) (x : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  D : J ⥤ CommRingCat.{0}
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  e : ∀ j, (V j).left ≅ Spec (D.obj j)
  tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j
  tr_a : ∀ {j j' : J} (g : j ⟶ j'), tr g ≫ a j = a j'
  tr_spec : ∀ {j j' : J} (g : j ⟶ j'), (e j').inv ≫ (tr g).left ≫ (e j).hom = Spec.map (D.map g)
  hx : ∀ j, x ∈ Set.range (a j).left
  c : Cocone D
  hc : IsColimit c
  cof : Cof D c
  t : Spec c.pt ⟶ U.left
  ht : ∀ j, t = Spec.map (c.ι.app j) ≫ (e j).inv ≫ (a j).left

attribute [instance] NSys.cat NSys.filt

def LeafNSys : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left), Nonempty (NSys U x)

def LeafSHofCof : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
  IsColimit c → Cof D c → SH c.pt

open Polynomial IsLocalRing in
theorem SHofCof : LeafSHofCof := by
  intro J _ _ D c hc hC
  have hL := isLocalRing_of_cof D c hc hC
  obtain ⟨Ω, _, _, ω, H⟩ := hC
  have hmax : ∀ a : c.pt, a ∈ maximalIdeal c.pt ↔ ω a = 0 := fun a => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro h; by_contra h'; exact h (unit_of_cof D c hc ω H a h')
    · intro h hu; have := hu.map ω; rw [h] at this; exact not_isUnit_zero this
  have : Nontrivial c.pt := ω.domain_nontrivial
  have hH : HenselianLocalRing c.pt := by
    refine { toIsLocalRing := hL, is_henselian := ?_ }
    intro f hf a₀ h1 h2
    obtain ⟨j, P, hP, hPm⟩ := monic_rep D c hc f hf
    have e : P.map (ω.comp (c.ι.app j).hom) = f.map ω := by rw [← Polynomial.map_map, hP]
    obtain ⟨b, hb, hbω⟩ := root_of_cof D c ω H j P hPm (ω a₀)
      (by rw [e, Polynomial.eval_map, eval₂_at_apply, ← hmax]; exact h1)
      (by rw [← derivative_map, e, derivative_map, Polynomial.eval_map, eval₂_at_apply]
          intro h0; have := h2.map ω; rw [h0] at this; exact not_isUnit_zero this)
    refine ⟨b, ?_, ?_⟩
    · rw [hP] at hb; exact hb
    · rw [hmax, map_sub, hbω, sub_self]
  refine ⟨hH, ?_⟩
  have hk : RingHom.ker (residue c.pt) ≤ RingHom.ker ω := fun a ha => by
    rw [RingHom.mem_ker, residue_eq_zero_iff] at ha; exact (hmax a).1 ha
  let ωb : ResidueField c.pt →+* Ω := RingHom.liftOfSurjective (residue c.pt) residue_surjective ⟨ω, hk⟩
  have hωb : ωb.comp (residue c.pt) = ω := RingHom.liftOfRightInverse_comp _ _ _ _
  refine IsSepClosed.of_exists_root _ (fun p hpm hirr hsep => ?_)
  have hl : p ∈ lifts (residue c.pt) := (lifts_iff_coeff_lifts p).2 (fun n => residue_surjective _)
  obtain ⟨pt, hpt, -, hptm⟩ := lifts_and_degree_eq_and_monic hl hpm
  obtain ⟨j, P, hP, hPm⟩ := monic_rep D c hc pt hptm
  have e : P.map (ω.comp (c.ι.app j).hom) = p.map ωb := by
    rw [← Polynomial.map_map, hP, ← hpt, Polynomial.map_map, hωb]
  have hdeg : (p.map ωb).degree ≠ 0 := by
    rw [degree_map]; intro h0
    exact hirr.not_isUnit (by rw [hpm.natDegree_eq_zero.1 (natDegree_eq_zero_iff_degree_le_zero.2 h0.le)]; exact isUnit_one)
  obtain ⟨y, hy⟩ := IsSepClosed.exists_root (p.map ωb) hdeg hsep.map
  have hd := hsep.map (f := ωb) |>.aeval_derivative_ne_zero (x := y) (by rw [coe_aeval_eq_eval]; exact hy)
  rw [coe_aeval_eq_eval] at hd
  obtain ⟨b, hb, -⟩ := root_of_cof D c ω H j P hPm y (by rw [e]; exact hy)
    (by rw [← derivative_map, e]; exact hd)
  refine ⟨residue c.pt b, ?_⟩
  rw [← hpt, Polynomial.eval_map, eval₂_at_apply, ← hP, hb, map_zero]

theorem LeafSHSys_of (hN : LeafNSys) (hA : LeafSHofCof) : LeafSHSys := by
  intro B U x
  obtain ⟨S⟩ := hN U x
  exact ⟨{
    J := S.J
    D := S.D
    V := S.V
    a := S.a
    e := S.e
    tr := fun g => S.tr g
    tr_a := fun g => S.tr_a g
    tr_spec := fun g => S.tr_spec g
    hx := S.hx
    c := S.c
    hc := S.hc
    sh := hA S.D S.c S.hc S.cof
    t := S.t
    ht := S.ht }⟩

def LeafRingSys : Prop := ∀ (R : CommRingCat.{0}) (p : PrimeSpectrum R),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (u : ∀ j, R ⟶ D.obj j),
    (∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j') ∧ (∀ j, (u j).hom.Etale) ∧
    (∀ j, ∃ q : PrimeSpectrum (D.obj j), q.comap (u j).hom = p) ∧
    ∃ (c : Cocone D), Nonempty (IsColimit c) ∧ Cof D c

def LeafNSysGlue : Prop := LeafRingSys → LeafNSys

theorem LeafSHSys_of_glue (hR : LeafRingSys) (hG : LeafNSysGlue) : LeafSHSys :=
  LeafSHSys_of (hG hR) SHofCof

end LateralTheory.E.LeafSHSysPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafObjFPPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafObjFPPf

def Desc (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω) : Prop :=
  ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D : Scheme.{0}) (q : D ⟶ Sp R) (v : X ⟶ D),
    FP q ∧ IsPullback v f q (toR R)

def LeafObjAff : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), IsAffine X → FP f → Desc k f

def LeafObjGlue : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (f : X ⟶ Sp Ω), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
    Desc k (U.ι ≫ f) → Desc k (V.ι ≫ f) → Desc k ((U ⊓ V).ι ≫ f) → Desc k f

def LeafQCQSInduct : Prop := ∀ (S : Scheme.{0}) [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop),
    (∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f) →
    (∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f) →
    ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → P f

theorem objectDescent_of_affineDescent (hA : LeafObjAff) (hG : LeafObjGlue) (hI : LeafQCQSInduct) : LeafObjFP := by
  intro k _ Ω _ _ X f hf
  exact hI (Sp Ω) (fun g => Desc k g) (fun g hX hg => hA k Ω g hX hg)
    (fun g hg U V hUV h1 h2 h3 => hG k Ω g hg U V hUV h1 h2 h3) f hf

end LateralTheory.E.LeafObjFPPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGlueIsProperPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueIsProperPf

variable {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {A B : Subalgebra Ω L} {u : L}

def cov {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : G.C0.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Bool (fun b => cond b (Sp A) (Sp B))
    (fun | true => G.iA | false => G.iB)
    (by
      intro x
      have hx : x ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ x
      rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨true, z, rfl⟩
      · exact ⟨false, z, rfl⟩)
    (by intro b; cases b <;> [exact G.hiB; exact G.hiA])

set_option backward.isDefEq.respectTransparency false in
theorem lft (h : GH Ω L A B u) {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) :
    LocallyOfFiniteType G.c0 := by
  refine IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.LocallyOfFiniteType) (cov G) ?_
  intro b
  cases b
  · show LocallyOfFiniteType (G.iB ≫ G.c0)
    rw [G.hcB, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.2.1
  · show LocallyOfFiniteType (G.iA ≫ G.c0)
    rw [G.hcA, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.1

set_option backward.isDefEq.respectTransparency false in
theorem qc {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : QuasiCompact G.c0 := by
  rw [HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.QuasiCompact)]
  refine ⟨?_⟩
  rw [← G.cover]
  exact (isCompact_range G.iA.base.hom.continuous).union (isCompact_range G.iB.base.hom.continuous)

def LeafGlueSep : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsSeparated G.c0

def LeafGlueExistence : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ValuativeCriterion.Existence G.c0

theorem LeafGlueIsProper_of (hS : LeafGlueSep) (hE : LeafGlueExistence) : LeafGlueIsProper := by
  intro Ω L _ _ _ A B u h G
  have := hS Ω L A B u h G
  have := qc G
  have := lft h G
  have : UniversallyClosed G.c0 := UniversallyClosed.of_valuativeCriterion _ (hE Ω L A B u h G)
  exact {}

end LateralTheory.E.LeafGlueIsProperPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.QuotientFieldNonconstantLift
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.QuotientFieldNonconstantLift

def LeafCurveSmall : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  (Set.univ : Set C).Infinite ∧ ∀ Z : Set C, IsClosed Z → Z.Infinite → Z = Set.univ

def LeafLiftNonconst : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k)
  [IsProper p] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω], (∀ R : Subalgebra k Ω, R.FG → ringKrullDim R <
    topologicalKrullDim X) → ∀ {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    ∀ (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))), genericPoint X ∈ Set.range e →
    ∀ y : C0, ∃ a : C0, pullback.lift c0 e he.symm a ≠ pullback.lift c0 e he.symm y

theorem lqf_of_nonconst (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C Y : Scheme.{0}}
    (c : C ⟶ Sp Ω) (hc : IsCurve c) (g : C ⟶ Y) [LocallyOfFiniteType g] [UniversallyClosed g]
    (hn : ∀ y, ∃ a, g a ≠ g y) : LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace c
  refine GlobalTheory.locallyQuasiFinite_of_finite_fibres_closedPoints g fun y hy => ?_
  have hcl : IsClosed ({g y} : Set Y) := by
    have := g.isClosedMap _ hy
    simpa using this
  by_contra hinf
  have := (hC Ω c hc).2 _ (hcl.preimage g.continuous) hinf
  obtain ⟨a, ha⟩ := hn y
  have : a ∈ g ⁻¹' {g y} := this ▸ Set.mem_univ a
  exact ha this

theorem nonconst_of_surj (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hg : Surjective g) (y : C1) : ∃ a, g a ≠ g y := by
  obtain ⟨b, hb⟩ := ((hC Ω c0 hc).1.sdiff (Set.finite_singleton (g y))).nonempty
  obtain ⟨a, rfl⟩ := hg.surj b
  exact ⟨a, by simpa using hb.2⟩

theorem lqf_gamma (hC : LeafCurveSmall) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {C0 C1 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (hc : IsCurve c0) (g : C1 ⟶ C0) (hc1 : IsCurve (g ≫ c0)) (hg : Surjective g) :
    LocallyQuasiFinite g := by
  obtain ⟨_, _, _⟩ := id hc
  obtain ⟨_, _, _⟩ := id hc1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g c0
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g c0
  exact lqf_of_nonconst hC (g ≫ c0) hc1 g (nonconst_of_surj hC c0 hc g hg)

theorem LeafQFOmega_of (hC : LeafCurveSmall) (hL : LeafLiftNonconst) :
    LateralTheory.E.QuasiFiniteDescent.LeafQFOmega := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen C1 C2 γ1 γ2 h1 h2 s1 s2
  refine ⟨?_, lqf_gamma hC c0 hc0 γ1 h1 s1, lqf_gamma hC (γ1 ≫ c0) h1 γ2 h2 s2⟩
  obtain ⟨_, _, _⟩ := id hc0
  set g := pullback.lift c0 e he.symm with hgdef
  have hfst : g ≫ pullback.fst _ _ = c0 := pullback.lift_fst _ _ _
  have : LocallyOfFiniteType (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : UniversallyClosed (g ≫ pullback.fst _ _) := by rw [hfst]; infer_instance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (pullback.fst _ _)
  have : UniversallyClosed g := UniversallyClosed.of_comp_of_isSeparated g (pullback.fst _ _)
  exact lqf_of_nonconst hC c0 hc0 g (hL k p Ω hdim c0 e hc0 he hgen)

end LateralTheory.E.QuotientFieldNonconstantLift
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ProjectiveLineTwoAffineChartsPolynomialGenerated
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.GeometricData

namespace LateralTheory.E.ProjectiveLineCharts₂

def ProjectiveLineTwoAffineChartsPolynomialGenerated : Prop :=
  ∃ (U V : P1.Opens) (s : Γ(P1, U)) (s' : Γ(P1, V)), IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
    P1.basicOpen s = U ⊓ V ∧ P1.basicOpen s' = U ⊓ V ∧
    P1.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      P1.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, U)) s) ∧
    Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, V)) s')

def ChartBC : Prop := ∀ (A : Type) [CommRing A] {L : Scheme.{0}} (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P1),
  IsPullback f l (terminal.from P1) (terminal.from _) → ∀ (W : P1.Opens) (x : Γ(P1, W)), IsAffineOpen W →
  Function.Surjective (Polynomial.eval₂RingHom (Int.castRingHom Γ(P1, W)) x) →
  IsAffineOpen (f ⁻¹ᵁ W) ∧ Function.Surjective (Polynomial.eval₂RingHom (rA l (f ⁻¹ᵁ W)) (f.app W x))

theorem rA_comp {A : Type} [CommRing A] {Z L : Scheme.{0}} (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A))
    (W : L.Opens) : rA (u ≫ l) (u ⁻¹ᵁ W) = (u.app W).hom.comp (rA l W) := by
  simp only [rA]
  rw [← Scheme.Hom.appLE_comp_appLE u l ⊤ W (u ⁻¹ᵁ W) le_top le_rfl, u.appLE_eq_app]
  rfl

theorem res_app {X Y : Scheme.{0}} (g : X ⟶ Y) {W W' : Y.Opens} (h : W' ≤ W) (x : Γ(Y, W)) :
    X.presheaf.map (homOfLE (g.preimage_mono h)).op (g.app W x) = g.app W' (Y.presheaf.map (homOfLE h).op x) := by
  have := congrArg (fun φ => φ.hom x) (g.naturality (homOfLE h).op)
  exact this.symm

theorem transport {X Y : Scheme.{0}} (g : X ⟶ Y) {U V : Y.Opens} (s : Γ(Y, U)) (s' : Γ(Y, V))
    (h1 : U ⊔ V = ⊤) (h2 : Y.basicOpen s = U ⊓ V) (h3 : Y.basicOpen s' = U ⊓ V)
    (h4 : Y.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1) :
    g ⁻¹ᵁ U ⊔ g ⁻¹ᵁ V = ⊤ ∧ X.basicOpen (g.app U s) = g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ∧
    X.basicOpen (g.app V s') = g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ∧
    X.presheaf.map (homOfLE (inf_le_left : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)).op (g.app U s) *
      X.presheaf.map (homOfLE (inf_le_right : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)).op (g.app V s') = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Scheme.Hom.preimage_sup, h1]; rfl
  · rw [← Scheme.preimage_basicOpen, h2]; rfl
  · rw [← Scheme.preimage_basicOpen, h3]; rfl
  · erw [res_app g inf_le_left s, res_app g inf_le_right s', ← map_mul, h4]
    exact map_one _

theorem LineOpens_of (hP : ProjectiveLineTwoAffineChartsPolynomialGenerated) (hB : ChartBC) : LineOpens := by
  intro A _ _ Z p hIL hZ
  obtain ⟨L, u, l, hu, ⟨_, f, hf⟩, rfl⟩ := hIL
  obtain ⟨U0, V0, x, y, hU0, hV0, h1, h2, h3, h4, hsx, hsy⟩ := hP
  obtain ⟨hU1, hsU⟩ := hB A l f hf U0 x hU0 hsx
  obtain ⟨hV1, hsV⟩ := hB A l f hf V0 y hV0 hsy
  obtain ⟨k1, k2, k3, k4⟩ := transport f x y h1 h2 h3 h4
  obtain ⟨m1, m2, m3, m4⟩ := transport u _ _ k1 k2 k3 k4
  have hUa : IsAffineOpen (u ⁻¹ᵁ (f ⁻¹ᵁ U0)) := hU1.preimage u
  have hVa : IsAffineOpen (u ⁻¹ᵁ (f ⁻¹ᵁ V0)) := hV1.preimage u
  have hint : ∀ (W : L.Opens) (z : Γ(L, W)), IsAffineOpen W →
      Function.Surjective (Polynomial.eval₂RingHom (rA l W) z) →
      (Polynomial.eval₂RingHom (rA (u ≫ l) (u ⁻¹ᵁ W)) (u.app W z)).IsIntegral := by
    intro W z hW hs
    have he : Polynomial.eval₂RingHom (rA (u ≫ l) (u ⁻¹ᵁ W)) (u.app W z) =
        (u.app W).hom.comp (Polynomial.eval₂RingHom (rA l W) z) := by
      apply Polynomial.ringHom_ext
      · intro a; simp [rA_comp]
      · simp
    rw [he]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ hs) (u.isIntegral_app W hW)
  by_cases hne : ((u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊓ u ⁻¹ᵁ (f ⁻¹ᵁ V0) : Z.Opens) : Set Z).Nonempty
  · exact Or.inr ⟨_, _, _, _, hUa, hVa, m1, m2, m3, hne, m4, hint _ _ hU1 hsU, hint _ _ hV1 hsV⟩
  · left
    have : IsIntegral Z := hZ.1
    have hUV : ¬ (((u ⁻¹ᵁ (f ⁻¹ᵁ U0) : Z.Opens) : Set Z).Nonempty ∧
        ((u ⁻¹ᵁ (f ⁻¹ᵁ V0) : Z.Opens) : Set Z).Nonempty) := by
      rintro ⟨a, b⟩
      exact hne (nonempty_preirreducible_inter (u ⁻¹ᵁ (f ⁻¹ᵁ U0)).isOpen (u ⁻¹ᵁ (f ⁻¹ᵁ V0)).isOpen a b)
    rcases not_and_or.mp hUV with h | h
    · have : u ⁻¹ᵁ (f ⁻¹ᵁ V0) = ⊤ := by
        rw [eq_top_iff]; intro z _
        have hz : z ∈ u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊔ u ⁻¹ᵁ (f ⁻¹ᵁ V0) := m1 ▸ trivial
        rcases (TopologicalSpace.Opens.mem_sup.mp hz) with hz | hz
        · exact absurd ⟨z, hz⟩ h
        · exact hz
      exact this ▸ hVa
    · have : u ⁻¹ᵁ (f ⁻¹ᵁ U0) = ⊤ := by
        rw [eq_top_iff]; intro z _
        have hz : z ∈ u ⁻¹ᵁ (f ⁻¹ᵁ U0) ⊔ u ⁻¹ᵁ (f ⁻¹ᵁ V0) := m1 ▸ trivial
        rcases (TopologicalSpace.Opens.mem_sup.mp hz) with hz | hz
        · exact hz
        · exact absurd ⟨z, hz⟩ h
      exact this ▸ hUa

end LateralTheory.E.ProjectiveLineCharts₂
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTensMonoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensMonoPf
open LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
  simp [Sec.res]

theorem loc_trans {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let T : ∀ ⦃V : Scheme.{0}⦄ ⦃f : V ⟶ U⦄, S.arrows f → Sieve V := fun V f hf =>
    Classical.choose (hPQ V f (hP V f hf))
  refine ⟨Sieve.bind S.arrows T, (Scheme.etaleTopology.{0}).bind_covering hS
    (fun V f hf => (Classical.choose_spec (hPQ V f (hP V f hf))).1), ?_⟩
  rintro W _ ⟨V, k, f, hf, hk, rfl⟩
  exact (Classical.choose_spec (hPQ V f (hP V f hf))).2 W k hk

theorem eq_zero_of_loc {F : Shv R} {U : Scheme.{0}} (y : Sec F U) (h : Loc U fun _ g => Sec.res g y = 0) : y = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  let e : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have := F.property.hom_ext ⟨S, hS⟩ e 0 (fun I => by
    ext1; apply LinearMap.ext_ring
    have := hP _ I.f I.hf
    simpa [e] using this)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) 1
  simpa [e] using h2

theorem mono_of_loc {F G : Shv R} (f : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = 0 → Loc U fun _ g => Sec.res g y = 0) : Mono f := by
  have : Mono ((sheafToPresheaf _ _).map f) := by
    have hm : ∀ U, Mono (((sheafToPresheaf Scheme.etaleTopology (ModuleCat (ULift.{1, 0} R))).map f).app U) := by
      intro U
      rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro y hy
      exact eq_zero_of_loc y (h U.unop y hy)
    exact NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem lift_res {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  have : (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift, Tens.res]
    exact (μ.nat g _ _ _ p.2 a b).symm
  exact LinearMap.congr_fun this x

theorem lift_compat {I J K K' : Cx R} (σ : Pair I J K) (ν : Pair I J K') (ι : K ⟶ K')
    (h : ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (ι.f w) (σ.mul U s t w hw a b) = ν.mul U s t w hw a b) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map (ι.f w) (σ.lift U w x) = ν.lift U w x := by
  have : ((ι.f w).hom.app (op U)).hom.comp (σ.lift U w) = ν.lift U w := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift]
    exact h U _ _ _ p.2 a b
  exact LinearMap.congr_fun this x
end

def LeafTw0LocSplit : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (n : ℕ) (a : Fin n → Sec ((sgl (tw q 0)).X 0) U),
  Loc U fun V g => ∃ (e : Sec ((sgl (tw q 0)).X 0) V) (c : Fin n → ULift.{1} (ZMod q)),
    (∀ k, Sec.res g (a k) = c k • e) ∧
    (e = 0 ∨ ∃ r : Sec ((res _ (tw q 0)).X 0) V →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q),
      r (Sec.map ((resAug (tw q 0)).f 0) e) = 1)

def LeafPreTensLocInj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T),
  τ.IsTensor → ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens (sgl (tw q 0)) (res _ (tw q i)) U w),
  (pre τ (resAug (tw q 0))).lift U w x = 0 → Loc U fun _ g => Tens.res g w x = 0

theorem LeafTensMono_of (hL : LeafPreTensLocInj) : LateralTheory.E.LeafExtTensPf.LeafTensMono := by
  intro q _ i S T σ τ hσ hτ ι hι n
  apply mono_of_loc
  intro U y hy
  have hc := lift_compat σ (pre τ (resAug (tw q 0))) ι (fun U s t w hw a b => hι U s t w hw a b)
  refine loc_trans (hσ.1 U n y) ?_
  rintro V g ⟨x, hx⟩
  have h0 : (pre τ (resAug (tw q 0))).lift V n x = 0 := by
    rw [← hc, hx, ← res_map, hy]; simp
  obtain ⟨S', hS', hP'⟩ := hL q i τ hτ V n x h0
  exact ⟨S', hS', fun W k hk => by
    show Sec.res (k ≫ g) y = 0
    have hk' : Tens.res k n x = 0 := hP' W k hk
    rw [res_comp, ← hx, ← lift_res, hk', map_zero]⟩

end LateralTheory.E.LeafTensMonoPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpreadProperPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafSpreadProperPf

def LeafSpreadSeparated : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsSeparated c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → IsSeparated q'

end LateralTheory.E.LeafSpreadProperPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTripleFPPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.LeafTripleFPPf

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') :
    toR R' ≫ incl h = toR R := by
  rw [← Spec.map_comp]
  rfl

theorem pb_lift {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R')
    {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {f : D ⟶ Sp R} {v : C ⟶ D} (hs : IsPullback v c f (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w)) c
      (pullback.snd f (incl h)) (toR R') := by
  have e1 : pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫ pullback.fst f (incl h) = v :=
    pullback.lift_fst _ _ _
  have t : IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) ≫
      pullback.fst f (incl h)) c f (toR R' ≫ incl h) := by rw [e1, toR_incl]; exact hs
  exact IsPullback.of_right t (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (incl h))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def LeafPairRel : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0), FP (γ1 ≫ c0) →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), FP q → ∀ (hs : IsPullback v0 c0 q (toR R)),
    ∃ (R' : Subalgebra k Ω) (h : R ≤ R'), R'.FG ∧ ∃ (E1 : Scheme.{0}) (e1 : E1 ⟶ pullback q (incl h)) (w1 : C1 ⟶ E1),
      FP (e1 ≫ pullback.snd q (incl h)) ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ pullback.snd q (incl h)) (toR R') ∧
      γ1 ≫ pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs.w) = w1 ≫ e1

theorem tripleDescent_of_pairRelation (hR : LeafPairRel) : LeafTripleFP := by
  intro k _ Ω _ _ R hRfg C0 C1 C2 c0 γ1 γ2 h2 D0 D1 q d1 v0 v1 hq hq1 hs0 hs1 hc
  obtain ⟨R', h, hR', E2, e2, w2, hf2, hs2, hc2⟩ :=
    hR k Ω R hRfg (γ1 ≫ c0) γ2 h2 (d1 ≫ q) v1 hq1 hs1
  have hsnd : pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]) ≫
      pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR', _, _, _, pullback.snd q (incl h),
    pullback.map (d1 ≫ q) (incl h) q (incl h) d1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id]) (by rw [Category.id_comp, Category.comp_id]), e2,
    pullback.lift v0 (c0 ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs0.w),
    pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hs1.w), w2, ?_⟩
  refine ⟨fp_snd _ _ hq, ?_, ?_, pb_lift h hs0, ?_, ?_, ?_, hc2⟩
  · rw [hsnd]; exact fp_snd _ _ hq1
  · rw [hsnd]; exact hf2
  · rw [hsnd]; exact pb_lift h hs1
  · rw [hsnd]; exact hs2
  · apply pullback.hom_ext
    · simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hc]
    · simp only [pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]

end LateralTheory.E.LeafTripleFPPf

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSHPtPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHPtPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf

theorem germ (hH : Hyps) (q : ℕ) [NeZero q] (i : ℤ) {B : Scheme.{0}} (U : B.Etale) (x : U.left)
    {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left) (he : ∀ j, IsIso (e j)) (hy : ∀ j, (a j).left (y j) = x)
    (hq : ∀ j, IsUnit ((q : ℕ) : D.obj j))
    (hcomp : ∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left)
    (ht : ∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t)
    (s : Sec (tw q i) U.left) (hs : Sec.res t s = 0) :
    ∃ (U' : B.Etale) (a' : U' ⟶ U) (y' : U'.left), a'.left y' = x ∧ Sec.res a'.left s = 0 := by
  have hA9 : A9 := hH.2.2.2.2.2.2.2.1
  have hB1 : B1 := hH.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, eq, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  set z : Ht q (sp (D.obj j)) 0 i := eq _ (Sec.res (e j ≫ (a j).left) s) with hz
  have h0 : pull _ (spMap (c.ι.app j).hom) _ _ z = 0 := by
    rw [hz, spMap, hnat, ← res_comp, ht, hs, map_zero]
  obtain ⟨k, f, hk⟩ := (hB1 q D c hc 0 i).2 j z (hq j) h0
  rw [hz, spMap, hnat, ← res_comp, hcomp] at hk
  have hk' : Sec.res (e k ≫ (a k).left) s = 0 := (eq _).injective (by rw [hk, map_zero])
  refine ⟨V k, a k, y k, hy k, ?_⟩
  have := congrArg (Sec.res (inv (e k))) hk'
  rw [← res_comp, IsIso.inv_hom_id_assoc] at this
  simpa using this

def LeafSHNb : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ {B : Scheme.{0}}
  (U : B.Etale) (_ : U.left ⟶ Sp k) (x : U.left),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c)
    (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (y : ∀ j, (V j).left) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left), (∀ j, IsIso (e j)) ∧ (∀ j, (a j).left (y j) = x) ∧ (∀ j, IsUnit ((q : ℕ) : D.obj j)) ∧
    (∀ (j k : J) (f : j ⟶ k), Spec.map (CommRingCat.ofHom (D.map f).hom) ≫ e j ≫ (a j).left = e k ≫ (a k).left) ∧
    (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) ∧ SH c.pt ∧
    (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left)

def LeafSHTop : Prop := ∀ {B : Scheme.{0}} (U : B.Etale) (x : U.left) {J : Type} [SmallCategory J] [Nonempty J]
  (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
  (t : Sp c.pt ⟶ U.left), (∀ j, Spec.map (CommRingCat.ofHom (c.ι.app j).hom) ≫ e j ≫ (a j).left = t) →
  (∀ (U' : B.Etale) (b : U' ⟶ U) (y' : U'.left), b.left y' = x →
      ∃ (j : J) (g : (V j).left ⟶ U'.left), g ≫ b.left = (a j).left) →
  (∀ O : U.left.Opens, x ∈ O → Set.range t ⊆ O) ∧
  (∀ S ∈ (EtTop B) U, ∃ (U' : B.Etale) (a' : U' ⟶ U), S a' ∧ ∃ t' : Sp c.pt ⟶ U'.left, t' ≫ a'.left = t)

theorem LeafSHPt_of (hN : LeafSHNb) (hT : LeafSHTop) : LeafSHPt := by
  intro hH q _ k _ hq i B U s0 x
  obtain ⟨J, _, _, D, c, hc, V, a, y, e, t, he, hy, hqj, hcomp, ht, hSH, hcof⟩ := hN hH q k hq U s0 x
  have : Nonempty J := IsFiltered.nonempty
  obtain ⟨hO, hL⟩ := hT U x D c V a e t ht hcof
  exact ⟨c.pt, inferInstance, t, hSH, hO, hL, fun s hs => germ hH q i U x D c hc V a y e t he hy hqj hcomp ht s hs⟩

end LateralTheory.E.LeafSHPtPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DerivUnit
noncomputable section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC Polynomial IsLocalRing

namespace LateralTheory.E.LeafClosedSH0PfPrim
open LateralTheory.E.E4 LateralTheory.E.LeafClosedSH0Pf

theorem derivUnit {C : Type} [CommRing C] [Nontrivial C] (q : ℕ) (z : C) (hq : IsUnit (q : C))
    (hz : (cyclotomic q C).eval z = 0) : IsUnit ((derivative (cyclotomic q C)).eval z) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q C
  have hzq : z ^ q = 1 := by
    have := congrArg (eval z) hg
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, hz, zero_mul] at this
    exact sub_eq_zero.mp this
  have hzu : IsUnit z := IsUnit.of_pow_eq_one hzq hq0
  have hd := congrArg (fun p => (derivative p).eval z) hg
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_add, eval_mul,
    eval_C, eval_pow, eval_X, hz, zero_mul, add_zero] at hd
  have hu : IsUnit ((q : C) * z ^ (q - 1)) := hq.mul (hzu.pow _)
  have hu' : IsUnit ((derivative (cyclotomic q C)).eval z * g.eval z) := by
    rw [← hd]; simpa using hu
  exact isUnit_of_mul_isUnit_left hu'

theorem evalHom {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (p : B[X]) (x : B) :
    f (p.eval x) = (p.map f).eval (f x) := by
  rw [Polynomial.eval_map, eval₂_at_apply]

theorem primLift : LeafPrimLift := by
  intro q B C _ _ _ _ f hf ζ
  have hloc : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨z, hqC, hz⟩ := ζ
  have hz' : (cyclotomic q C).eval z = 0 := by
    rw [aeval_def, ← Polynomial.eval_map, map_cyclotomic] at hz; exact hz
  have hqB : IsUnit (q : B) := by
    have : IsUnit (f (q : B)) := by simpa using hqC
    exact (isUnit_map_iff f _).mp this
  obtain ⟨a0, rfl⟩ := hf z
  have hker : (cyclotomic q B).eval a0 ∈ maximalIdeal B := by
    rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
    have := hu.map f
    rw [evalHom, map_cyclotomic, hz'] at this
    exact not_isUnit_zero this
  have hder : IsUnit ((derivative (cyclotomic q B)).eval a0) := by
    apply (isUnit_map_iff f _).mp
    rw [evalHom, ← derivative_map, map_cyclotomic]
    exact derivUnit q (f a0) hqC hz'
  have : IsLocalRing C := IsLocalRing.of_surjective' f hf
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian (cyclotomic q B) (cyclotomic.monic q B) a0 hker hder
  have hfa : (cyclotomic q C).eval (f a) = 0 := by
    rw [← map_cyclotomic q f, ← evalHom, ha.eq_zero, map_zero]
  refine ⟨⟨a, hqB, ?_⟩, ?_⟩
  · rw [aeval_def, ← Polynomial.eval_map, map_cyclotomic]; exact ha.eq_zero
  · apply Subtype.ext
    change f a = f a0
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hfa hz' ?_ (derivUnit q (f a) hqC hfa)
    rw [← map_sub, isUnit_map_iff]
    exact (mem_maximalIdeal _).mp ham

end LateralTheory.E.LeafClosedSH0PfPrim
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.NeighbourhoodKilling
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.NeighbourhoodKilling
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd

structure Tri (J : Type) [SmallCategory J] where
  Rm : J ⥤ AddCommGrpCat.{1}
  Ym : J ⥤ AddCommGrpCat.{1}
  Yp : J ⥤ AddCommGrpCat.{1}
  Wp : J ⥤ AddCommGrpCat.{1}
  cR : Cocone Rm
  cYm : Cocone Ym
  cYp : Cocone Yp
  cWp : Cocone Wp
  fg : Rm ⟶ Ym
  fgL : cR.pt ⟶ cYm.pt
  fg_w : ∀ j, cR.ι.app j ≫ fgL = fg.app j ≫ cYm.ι.app j
  dl : Wp ⟶ Rm
  dlL : cWp.pt ⟶ cR.pt
  dl_w : ∀ j, cWp.ι.app j ≫ dlL = dl.app j ≫ cR.ι.app j
  rs : Yp ⟶ Wp
  rsL : cYp.pt ⟶ cWp.pt
  rs_w : ∀ j, cYp.ι.app j ≫ rsL = rs.app j ≫ cWp.ι.app j

  exR : ∀ j (x : Rm.obj j), (fg.app j).hom x = 0 → ∃ w, (dl.app j).hom w = x

  exWL : ∀ w : cWp.pt, dlL.hom w = 0 → ∃ y, rsL.hom y = w

  cx : ∀ j (y : Yp.obj j), (dl.app j).hom ((rs.app j).hom y) = 0

  injYm : ∀ j (y : Ym.obj j), (cYm.ι.app j).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (Ym.map f).hom y = 0

  surYp : ∀ y : cYp.pt, ∃ (j : J) (y' : Yp.obj j), (cYp.ι.app j).hom y' = y

  injWp : ∀ j (w : Wp.obj j), (cWp.ι.app j).hom w = 0 → ∃ (k : J) (f : j ⟶ k), (Wp.map f).hom w = 0

def PairFive : Prop := ∀ (J : Type) [SmallCategory J] [IsFiltered J] (T : Tri J) (j : J) (x : T.Rm.obj j),
  (T.cR.ι.app j).hom x = 0 → ∃ (k : J) (f : j ⟶ k), (T.Rm.map f).hom x = 0

def ObsExact : Prop := ∀ (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i m : ℤ) (y : Hrel (ZMod q) u (tw q i) (m + 1)),
  fgt (ZMod q) u (tw q i) (m + 1) y = 0 → ∃ w, LateralTheory.E.GlueRelPf.obs q u i m w = y

def ObsNat : Prop := ∀ (q : ℕ) [NeZero q] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
  (comm : f' ≫ e = u ≫ f) (i m : ℤ) (w : Ht q U m i),
  rpull (ZMod q) f f' u e comm (tw q i) (m + 1) (LateralTheory.E.GlueRelPf.obs q f i m w) =
    LateralTheory.E.GlueRelPf.obs q f' i m (pull (ZMod q) u (tw q i) m w)

def Bridge : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m) (u : U.left),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (T : Tri J) (j0 : J) (x0 : T.Rm.obj j0) (A : Type) (_ : CommRing A)
    (t : Sp A ⟶ U.left), SH A ∧
    (LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0 → (T.cR.ι.app j0).hom x0 = 0) ∧
    ∀ (j : J) (f : j0 ⟶ j), (T.Rm.map f).hom x0 = 0 →
      ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

theorem goal_of (hF : PairFive) (_hO : ObsExact) (_hN : ObsNat) (hB : Bridge) : LeafKillNbhd := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z hz u
  obtain ⟨J, _, _, T, j0, x0, A, _, t, hSH, hlim, hst⟩ := hB hH q k hq i toK ι p hp U m z u
  obtain ⟨j, f, hf⟩ := hF J T j0 x0 (hlim (hz A t hSH))
  exact hst j f hf

end LateralTheory.E.NeighbourhoodKilling
end
end
