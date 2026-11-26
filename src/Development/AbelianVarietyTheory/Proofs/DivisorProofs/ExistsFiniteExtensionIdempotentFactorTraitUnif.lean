module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyRepresentativeZariskiGlue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionTraitUniformisingMumfordBun
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmetricBundleDescends
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangePolarisationTranslateTwoTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangePolarisationTranslateTwoTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BaseTransl

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
  {g : G'.left ⟶ G.left}

theorem toBase_injective (hg : IsPullback g G'.hom G.hom f) {T : Over S'} {x x' : T ⟶ G'}
    (h : toBase hg.w x = toBase hg.w x') : x = x' := by
  have e : x.left ≫ g = x'.left ≫ g := congrArg (fun z => z.left) h
  ext
  exact hg.hom_ext e (by rw [Over.w x, Over.w x'])

theorem toBase_one (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    toBase hg.w (1 : T ⟶ G') = 1 := by
  have := hm T 1 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem isGrpPullback_of_toBase (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) :
    IsGrpPullback G' G f g := by
  refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have ex : x₀ = toBase hg.w x := by ext; exact hx
  have ey : y₀ = toBase hg.w y := by ext; exact hy
  rw [ex, ey, ← hm]
  rfl


open GlobalTheory.RigidTranslate in
theorem exists_baseChange_translate : ∀ (K K' : Type) [Field K] [Field K'] (io : K →+* K') (A : PolAV (Sp K)) (y : Over.mk (spMap io) ⟶ A.A), y * y = 1 → ∃ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (t : 𝟙_ (Over (Sp K')) ⟶ A₁.A), IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ t.left ≫ α₁ = y.left ∧ LBIso A₁.L (GlobalTheory.RigidTranslate.rigTransl (A.L.pull α₁) t) := by
  intro K K' _ _ io A y hy
  obtain ⟨P, g, hg, -, hm, w, hw⟩ := GlobalTheory.polBaseChange_holds (Sp K) (Sp K') (spMap io) A
  have hpb : IsGrpPullback P.A A.A (spMap io) g := isGrpPullback_of_toBase hg hm
  have := P.isAb.comm
  have := P.isAb.proper
  have := A.isAb.comm
  let t₀ : 𝟙_ (Over (Sp K')) ⟶ P.A := Over.homMk (hg.lift y.left (𝟙 _) (by rw [Over.w y, Category.id_comp]; rfl))
    (hg.lift_snd _ _ _)
  have ht₀ : t₀.left ≫ g = y.left := hg.lift_fst _ _ _
  let e : Over.mk ((𝟙_ (Over (Sp K'))).hom ≫ spMap io) ⟶ Over.mk (spMap io) := Over.homMk (𝟙 _) (Category.id_comp _)
  have hte : toBase hg.w t₀ = e ≫ y := by
    ext
    exact ht₀.trans (Category.id_comp _).symm
  have htt : t₀ * t₀ = 1 := by
    refine toBase_injective hg ?_
    rw [hm, hte, toBase_one hg hm, ← MonObj.comp_mul, hy, MonObj.comp_one]
  have hwL : LBIso (A.L.pull g) P.L := ⟨w, hw⟩
  obtain ⟨c, hc⟩ := GlobalTheory.Moduli.cube_of_isLB _ P P.L P.isLB
  let A₁ : PolAV (Sp K') :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := rigTransl P.L t₀
      isLB := DVR.linComb_isLB _ P.isLB _ _
      rigid := rigidified_rigTransl P.isLB
      sym := sym_rigTransl htt P.isLB P.sym
      ample := relAmple_rigTransl htt P.isLB P.ample
      ktriv := kTriv_rigTransl htt P.isLB P.ktriv }
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ A.A P.A g hpb
  have hLamA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLamP : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  have h3 := hlam A.L P.L _ (abelian₂ A.A A.L) (𝟙 _) A.isLB P.isLB hLamA hwL.symm (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamA).symm
  rw [Category.comp_id] at h3
  have h1 : LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ P.A P.L).pull (𝟙 _)) := lam_rigTransl P.isLB c hc
  refine ⟨A₁, g, β₂, t₀, hpb, hsq, ?_, ht₀, GlobalTheory.PelPrim.lbIso_linComb hwL.symm _ _⟩
  exact LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB hLamP _) (pull_isLB hLamA _) h1
    (LBIso.trans (pull_isLB hLamP _) hLamP (pull_isLB hLamA _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamP) h3)

end GlobalTheory.BaseTransl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangePolarisationTranslateTwoTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_polarisation_translate_two_torsion : ∀ (K K' : Type) [Field K] [Field K'] (io : K →+* K') (A : PolAV (Sp K)) (y : Over.mk (spMap io) ⟶ A.A), y * y = 1 → ∃ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (t : 𝟙_ (Over (Sp K')) ⟶ A₁.A), IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ t.left ≫ α₁ = y.left ∧ LBIso A₁.L (GlobalTheory.RigidTranslate.rigTransl (A.L.pull α₁) t) := by
  first | exact @GlobalTheory.BaseTransl.exists_baseChange_translate | exact GlobalTheory.BaseTransl.exists_baseChange_translate | (intros; apply GlobalTheory.BaseTransl.exists_baseChange_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionPointAbelianVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionPointAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TwoTorsionDescent

theorem exists_finite_ext_of_sq_eq_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (G : Over (Sp Ω)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A (spMap ga) α → ∀ x : 𝟙_ (Over (Sp Ω)) ⟶ G, x * x = 1 → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (l : K' →+* Ω) (y : Over.mk (spMap io) ⟶ A.A), io.Finite ∧ l.comp io = ga ∧ y * y = 1 ∧ spMap l ≫ y.left = x.left ≫ α := by
  intro K Ω _ _ _ ga A G _ α h x hx

  set T : Over (Sp K) := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ spMap ga) with hT
  let zo : T ⟶ A.A := pushHom h (𝟙_ (Over (Sp Ω))) x
  have hzo : zo * zo = 1 := by
    show pushHom h _ x * pushHom h _ x = 1
    rw [← map_mul, hx, map_one]
  have hzl : zo.left = x.left ≫ α := rfl
  have hmul : zo ≫ mulN A.A 2 = toUnit T ≫ η[A.A] := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq, hzo]
    rfl
  let t : T ⟶ torsion A.A 2 := pullback.lift zo (toUnit T) hmul
  have ht : t ≫ torsion.ι A.A 2 = zo := pullback.lift_fst _ _ _

  have h2 : IsUnit ((2 : ℕ) : Γ(Sp K, ⊤)) := by
    have e : ((2 : ℕ) : Γ(Sp K, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (2 : K) := by
      rw [map_ofNat]; rfl
    rw [e]
    exact (IsUnit.mk0 (2 : K) two_ne_zero).map _
  haveI := A.isAb
  have hfin : IsFinite (torsion A.A 2).hom := (GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A.A h2).2.1
  set X := (torsion A.A 2).left
  set p := (torsion A.A 2).hom
  let tl : Sp Ω ⟶ X := t.left
  let w : X := tl (IsLocalRing.closedPoint Ω)
  let φ : X.residueField w ⟶ CommRingCat.of Ω := X.descResidueField (Scheme.stalkClosedPointTo tl)
  have htl : Spec.map φ ≫ X.fromSpecResidueField w = tl :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X tl

  let s : Sp K := p w
  haveI : s.asIdeal.IsPrime := s.isPrime
  haveI : s.asIdeal.IsMaximal := by rw [Ideal.eq_bot_of_prime s.asIdeal]; exact Ideal.bot_isMaximal
  let c : K →+* (Sp K).residueField s :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).inv.hom.comp (algebraMap K s.asIdeal.ResidueField)
  have hc : spMap c = (Sp K).fromSpecResidueField s := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp]
    rfl
  have hcfin : c.Finite := by
    refine RingHom.Finite.of_surjective _ ?_
    refine (Scheme.Spec.residueFieldIso (CommRingCat.of K) s).commRingCatIsoToRingEquiv.symm.surjective.comp ?_
    have hq : Function.Surjective (Ideal.Quotient.mk s.asIdeal) := Ideal.Quotient.mk_surjective
    have hb := Ideal.bijective_algebraMap_quotient_residueField s.asIdeal
    have e : (algebraMap K s.asIdeal.ResidueField) = (algebraMap (K ⧸ s.asIdeal) s.asIdeal.ResidueField).comp (Ideal.Quotient.mk s.asIdeal) := by
      ext a; rfl
    rw [e]
    exact hb.2.comp hq
  let io : K →+* X.residueField w := (p.residueFieldMap w).hom.comp c
  have hio : io.Finite := (GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite p w).comp hcfin
  have hsio : spMap io = X.fromSpecResidueField w ≫ p := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← hc, ← Spec.map_comp]
    rfl

  have hu : X.fromSpecResidueField w ≫ p = spMap io := hsio.symm
  let u : Over.mk (spMap io) ⟶ torsion A.A 2 := Over.homMk (X.fromSpecResidueField w) hu
  let y : Over.mk (spMap io) ⟶ A.A := u ≫ torsion.ι A.A 2
  have hy : y * y = 1 := by
    have e1 : y * y = y ≫ mulN A.A 2 := by
      rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, sq]
    have e2 : torsion.ι A.A 2 ≫ mulN A.A 2 = pullback.snd (mulN A.A 2) η[A.A] ≫ η[A.A] :=
      pullback.condition
    rw [e1, Category.assoc, e2]
    show (u ≫ pullback.snd (mulN A.A 2) η[A.A]) ≫ η[A.A] = toUnit _ ≫ η[A.A]
    rw [toUnit_unique (u ≫ pullback.snd (mulN A.A 2) η[A.A]) (toUnit _)]
  have hlo : Spec.map φ ≫ X.fromSpecResidueField w ≫ p = spMap ga := by
    rw [← Category.assoc, htl]
    exact Over.w t
  refine ⟨X.residueField w, inferInstance, io, φ.hom, y, hio, ?_, hy, ?_⟩
  · have e : spMap (φ.hom.comp io) = spMap ga := by
      rw [← hlo, ← hsio]
      show _ = Spec.map φ ≫ Spec.map (CommRingCat.ofHom io)
      erw [← Spec.map_comp]
      rfl
    have e' := Spec.map_inj.mp e
    exact congrArg CommRingCat.Hom.hom e'
  · show Spec.map (CommRingCat.ofHom φ.hom) ≫ (X.fromSpecResidueField w ≫ (torsion.ι A.A 2).left) = x.left ≫ α
    rw [CommRingCat.ofHom_hom, ← Category.assoc, htl, ← hzl, ← ht]
    rfl

end GlobalTheory.TwoTorsionDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionPointAbelianVarietyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_ext_twoTorsion_point_abelianVariety : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (G : Over (Sp Ω)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A (spMap ga) α → ∀ x : 𝟙_ (Over (Sp Ω)) ⟶ G, x * x = 1 → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (l : K' →+* Ω) (y : Over.mk (spMap io) ⟶ A.A), io.Finite ∧ l.comp io = ga ∧ y * y = 1 ∧ spMap l ≫ y.left = x.left ≫ α := by
  first | exact @GlobalTheory.TwoTorsionDescent.exists_finite_ext_of_sq_eq_one | exact GlobalTheory.TwoTorsionDescent.exists_finite_ext_of_sq_eq_one | (intros; apply GlobalTheory.TwoTorsionDescent.exists_finite_ext_of_sq_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionRigidTranslateSameMumfordBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionRigidTranslateSameMumfordBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SymPrincipalTranslate
open GlobalTheory.CechPic

theorem pull_local_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X) (c : Pic X) :
    pull f c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hc : f.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  exact GlobalTheory.KTrivOfLam.pull_eq_zero_of_chart hL f i fun y =>
    ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open (L.U i).isOpen hi

theorem cls_lam_div {S : Scheme.{0}} {G : Over S} [GrpObj G] {L M : LB G.left} (hL : L.IsLB) (hM : M.IsLB)
    (h : (abelian₂ G (LB.div L M)).IsLB) (h₁ : (abelian₂ G L).IsLB) (h₂ : (abelian₂ G M).IsLB) :
    cls _ h = cls _ h₁ - cls _ h₂ := by
  rw [show cls (abelian₂ G (LB.div L M)) h = _ from cls_linComb (LB.isLB_div hL hM) _ _ h,
    show cls (abelian₂ G L) h₁ = _ from cls_linComb hL _ _ h₁, show cls (abelian₂ G M) h₂ = _ from cls_linComb hM _ _ h₂,
    cls_div hL hM, ← Finset.sum_sub_distrib]
  simp only [map_sub, smul_sub]

theorem exists_two_torsion_rigTransl : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (L' : LB P.A.left), L'.IsLB → Rigidified P.A L' → Sym P.A L' → LBIso (abelian₂ P.A L') (abelian₂ P.A P.L) → ∃ x : 𝟙_ (Over (Sp R)) ⟶ P.A, x * x = 1 ∧ LBIso L' (GlobalTheory.RigidTranslate.rigTransl P.L x) := by
  intro R _ _ _ P L' hL' _ hsym hlam
  have := P.isAb.comm
  have hO : (LB.div L' P.L).IsLB := LB.isLB_div hL' P.isLB
  have hΛ' : (abelian₂ P.A L').IsLB := LB.isLB_linComb hL' _ _
  have hΛ : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have hΛO : (abelian₂ P.A (LB.div L' P.L)).IsLB := LB.isLB_linComb hO _ _
  have hu : ∃ u : LB.Gen (abelian₂ P.A (LB.div L' P.L)), u.IsGen := by
    refine (cls_eq_zero_iff hΛO).1 ?_
    rw [cls_lam_div hL' P.isLB hΛO hΛ' hΛ, sub_eq_zero]
    exact (cls_eq_iff hΛ' hΛ).2 hlam
  obtain ⟨x, hx⟩ := GlobalTheory.LN.ega_holds.2.2.2 R P _ hO hu
  let τ : P.A ⟶ P.A := (toUnit P.A ≫ x) * 𝟙 P.A

  have hτ : cls L' hL' = pull τ.left (cls P.L P.isLB) := by
    have h1 := (cls_eq_iff hO (LB.isLB_linComb P.isLB _ _)).2 hx
    rw [cls_div hL' P.isLB hO, cls_linComb P.isLB] at h1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul, pull_id] at h1
    exact sub_left_injective (h1.trans (sub_eq_add_neg _ _).symm)

  have hR : (GlobalTheory.RigidTranslate.rigTransl P.L x).IsLB := LB.isLB_linComb P.isLB _ _
  have hcR : cls _ hR = pull τ.left (cls P.L P.isLB) := by
    have e : GlobalTheory.PolTranslate.transl x = τ := by rw [GlobalTheory.PolTranslate.transl, _root_.mul_comm]
    refine (cls_linComb P.isLB _ _ hR).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul]
    rw [Over.comp_left, pull_comp, pull_local_eq_zero (R := R) x.left, map_zero, neg_zero, add_zero, e]
  refine ⟨x, ?_, (cls_eq_iff hL' hR).1 (hτ.trans hcR.symm)⟩

  have hs : pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB :=
    GlobalTheory.RigSymSubring.cls_of_sym P.isLB P.sym
  have hs' : pull (GrpObj.inv : P.A ⟶ P.A).left (cls L' hL') = cls L' hL' :=
    GlobalTheory.RigSymSubring.cls_of_sym hL' hsym
  let τ' : P.A ⟶ P.A := (toUnit P.A ≫ x⁻¹) * 𝟙 P.A
  have e1 : (GrpObj.inv : P.A ⟶ P.A) ≫ τ = τ' ≫ GrpObj.inv := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv,
      ← GrpObj.comp_inv, inv_inv, Hom.inv_def, Category.id_comp]
  have e2 : τ ≫ τ' = 𝟙 P.A := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.one_mul]
  have e3 : τ ≫ τ = (toUnit P.A ≫ (x * x)) * 𝟙 P.A := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, ← _root_.mul_assoc,
      ← MonObj.comp_mul]
  have h2 : pull ((toUnit P.A ≫ (x * x)) * 𝟙 P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
    have k : pull τ'.left (cls P.L P.isLB) = pull τ.left (cls P.L P.isLB) := by
      have := hs'
      rw [hτ, ← pull_comp, ← Over.comp_left, e1, Over.comp_left, pull_comp, hs] at this
      exact this
    have k2 := congrArg (pull τ.left) k
    rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, e2, e3, Over.id_left, pull_id] at k2
    exact k2.symm

  refine (P.ktriv R (𝟙 (Sp R)) (x * x) fun p => ⟨⊤, trivial, ?_⟩).trans Hom.one_def.symm
  let T : Over (Sp R) := Over.mk (𝟙 (Sp R))
  have hTD : (translDiff P.A P.L (x * x)).IsLB := LB.isLB_linComb P.isLB _ _
  refine (cls_eq_zero_iff (pull_isLB hTD _)).1 ?_
  rw [cls_pull hTD]
  suffices h0 : cls _ hTD = 0 by rw [h0, map_zero]
  have e₁ : cls _ hTD = pull (lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A]).left (cls P.L P.isLB) -
      pull (snd T P.A).left (cls P.L P.isLB) := by
    refine (cls_linComb P.isLB _ _ hTD).trans ?_
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_smul,
      neg_smul]
    exact (sub_eq_add_neg _ _).symm
  have e₂ : lift (fst T P.A ≫ (x * x)) (snd T P.A) ≫ μ[P.A] = snd T P.A ≫ ((toUnit P.A ≫ (x * x)) * 𝟙 P.A) := by
    show (fst T P.A ≫ (x * x)) * snd T P.A = _
    rw [MonObj.comp_mul (snd T P.A), ← Category.assoc (snd T P.A), comp_toUnit, Category.comp_id]
    congr 1
  rw [e₁, e₂, Over.comp_left, pull_comp, h2, sub_self]
end GlobalTheory.SymPrincipalTranslate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionRigidTranslateSameMumfordBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twoTorsion_rigidTranslate_same_mumfordBundle : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (L' : LB P.A.left), L'.IsLB → Rigidified P.A L' → Sym P.A L' → LBIso (abelian₂ P.A L') (abelian₂ P.A P.L) → ∃ x : 𝟙_ (Over (Sp R)) ⟶ P.A, x * x = 1 ∧ LBIso L' (GlobalTheory.RigidTranslate.rigTransl P.L x) := by
  first | exact @GlobalTheory.SymPrincipalTranslate.exists_two_torsion_rigTransl | exact GlobalTheory.SymPrincipalTranslate.exists_two_torsion_rigTransl | (intros; apply GlobalTheory.SymPrincipalTranslate.exists_two_torsion_rigTransl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmetricBundleDescends
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem pull_pol : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (f : Sp R ⟶ Sp R₀) (A : PolAV (Sp R₀)) (G : Over (Sp R)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A f α → (A.L.pull α).IsLB ∧ Rigidified G (A.L.pull α) ∧ Sym G (A.L.pull α) ∧ RelAmple G (A.L.pull α) ∧ KTriv G (A.L.pull α) := by
  intro R R₀ _ _ f A G _ α hα
  have hw := (isGen_iff _).1 (GlobalTheory.UU.pullIso_isGen A.isLB α)
  exact ⟨pull_isLB A.isLB α, GlobalTheory.PolBaseChange.rigidified_pull hα A.rigid, GlobalTheory.PolBaseChange.sym_pull hα A.sym,
    relAmple_pull hα.1 A.isLB (pull_isLB A.isLB α) hw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample,
    kTriv_pull hα A.isLB (pull_isLB A.isLB α) hw A.ktriv⟩

theorem isSquare_unique : ∀ {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (φ : G'.left ⟶ G.left) (φ₂ φ₂' : (G' ⊗ G').left ⟶ (G ⊗ G).left), IsSquare φ φ₂ → IsSquare φ φ₂' → φ₂ = φ₂' := by
  intro S S' G' G φ φ₂ φ₂' h h'
  have e : φ₂ ≫ (G ⊗ G).hom = φ₂' ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← Category.assoc, h.1, h'.1]
  let u : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂ rfl
  let v : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂' e.symm
  have : u = v := CartesianMonoidalCategory.hom_ext _ _
    (Over.OverMorphism.ext (by simpa [u, v] using h.1.trans h'.1.symm))
    (Over.OverMorphism.ext (by simpa [u, v] using h.2.trans h'.2.symm))
  exact congrArg (fun z => z.left) this
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate GlobalTheory.GtCoordCompare

theorem lbIso_diff_pull_pull : ∀ (X Y₁ Y₂ Z : Scheme.{0}) (M : LB X) (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) (u₁ v₁ : Y₁ ⟶ Y₁) (u₂ v₂ : Y₂ ⟶ Y₂) (q₁ : Z ⟶ Y₁) (q₂ : Z ⟶ Y₂), M.IsLB → q₁ ≫ u₁ ≫ g₁ = q₂ ≫ u₂ ≫ g₂ → q₁ ≫ v₁ ≫ g₁ = q₂ ≫ v₂ ≫ g₂ → LBIso ((LB.LinComb (M.pull g₁) (K := Fin 2) ![u₁, v₁] ![1, -1]).pull q₁) ((LB.LinComb (M.pull g₂) (K := Fin 2) ![u₂, v₂] ![1, -1]).pull q₂) := by
  intro X Y₁ Y₂ Z M g₁ g₂ u₁ v₁ u₂ v₂ q₁ q₂ hM hu hv
  refine lbIso_of_refines hM
    ((((refines_self (L := M) (fun _ : PUnit => g₁) (fun _ => 1)).linComb _ _)).linComb _ _)
    ((((refines_self (L := M) (fun _ : PUnit => g₂) (fun _ => 1)).linComb _ _)).linComb _ _) _ isGen_one
    fun U _ f => ?_
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, hu, hv]
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem transl_comp_eq : ∀ {S S₁ S₀ : Scheme.{0}} (G : Over S) (G₁ : Over S₁) (A : Over S₀) [GrpObj G] [GrpObj G₁] [GrpObj A] (f : S ⟶ S₀) (f₁ : S₁ ⟶ S₀) (φ : G.left ⟶ A.left) (φ₁ : G₁.left ⟶ A.left), IsGrpPullback G A f φ → IsGrpPullback G₁ A f₁ φ₁ → ∀ (x : 𝟙_ (Over S) ⟶ G) (t : 𝟙_ (Over S₁) ⟶ G₁) (Z : Scheme.{0}) (q : Z ⟶ G.left) (q₁ : Z ⟶ G₁.left), q ≫ φ = q₁ ≫ φ₁ → q ≫ (toUnit G ≫ x).left ≫ φ = q₁ ≫ (toUnit G₁ ≫ t).left ≫ φ₁ → q ≫ (GlobalTheory.PolTranslate.transl x).left ≫ φ = q₁ ≫ (GlobalTheory.PolTranslate.transl t).left ≫ φ₁ := by
  intro S S₁ S₀ G G₁ A _ _ _ f f₁ φ φ₁ h h₁ x t Z q q₁ e ec
  let T : Over S := Over.mk (q ≫ G.hom)
  let T₁ : Over S₁ := Over.mk (q₁ ≫ G₁.hom)
  let a : T ⟶ G := Over.homMk q rfl
  let a₁ : T₁ ⟶ G₁ := Over.homMk q₁ rfl
  have k : q ≫ (GlobalTheory.PolTranslate.transl x).left = (a * (toUnit T ≫ x)).left := comp_transl_left a x
  have k₁ : q₁ ≫ (GlobalTheory.PolTranslate.transl t).left = (a₁ * (toUnit T₁ ≫ t)).left := comp_transl_left a₁ t
  have hw : (q ≫ G.hom) ≫ f = (q₁ ≫ G₁.hom) ≫ f₁ := by
    rw [Category.assoc, Category.assoc, ← h.1.w, ← h₁.1.w, ← Category.assoc, ← Category.assoc, e]
  let x₀ : Over.mk (T.hom ≫ f) ⟶ A := Over.homMk (a.left ≫ φ) (by
    show (q ≫ φ) ≫ A.hom = (q ≫ G.hom) ≫ f
    rw [Category.assoc, h.1.w, Category.assoc])
  let y₀ : Over.mk (T.hom ≫ f) ⟶ A := Over.homMk ((toUnit T ≫ x).left ≫ φ) (by
    show ((toUnit T ≫ x).left ≫ φ) ≫ A.hom = (q ≫ G.hom) ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w (toUnit T ≫ x)]
    rfl)
  let x₁ : Over.mk (T₁.hom ≫ f₁) ⟶ A := Over.homMk (a₁.left ≫ φ₁) (by
    show (q₁ ≫ φ₁) ≫ A.hom = (q₁ ≫ G₁.hom) ≫ f₁
    rw [Category.assoc, h₁.1.w, Category.assoc])
  let y₁ : Over.mk (T₁.hom ≫ f₁) ⟶ A := Over.homMk ((toUnit T₁ ≫ t).left ≫ φ₁) (by
    show ((toUnit T₁ ≫ t).left ≫ φ₁) ≫ A.hom = (q₁ ≫ G₁.hom) ≫ f₁
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w (toUnit T₁ ≫ t)]
    rfl)
  have E := h.2 T a (toUnit T ≫ x) x₀ y₀ rfl rfl
  have E₁ := h₁.2 T₁ a₁ (toUnit T₁ ≫ t) x₁ y₁ rfl rfl
  let j : Over.mk (T.hom ≫ f) ⟶ Over.mk (T₁.hom ≫ f₁) := Over.homMk (𝟙 Z) (by
    show 𝟙 Z ≫ (q₁ ≫ G₁.hom) ≫ f₁ = (q ≫ G.hom) ≫ f
    rw [Category.id_comp, hw])
  have hx : j ≫ x₁ = x₀ := Over.OverMorphism.ext (by
    show 𝟙 Z ≫ q₁ ≫ φ₁ = q ≫ φ
    rw [Category.id_comp, e])
  have hy : j ≫ y₁ = y₀ := Over.OverMorphism.ext (by
    show 𝟙 Z ≫ (toUnit T₁ ≫ t).left ≫ φ₁ = (toUnit T ≫ x).left ≫ φ
    have k2 : (toUnit T ≫ x).left = q ≫ (toUnit G ≫ x).left := by
      simp only [Over.comp_left]
      show (q ≫ G.hom) ≫ x.left = q ≫ (G.hom ≫ x.left)
      rw [Category.assoc]
    have k3 : (toUnit T₁ ≫ t).left = q₁ ≫ (toUnit G₁ ≫ t).left := by
      simp only [Over.comp_left]
      show (q₁ ≫ G₁.hom) ≫ t.left = q₁ ≫ (G₁.hom ≫ t.left)
      rw [Category.assoc]
    rw [Category.id_comp, k2, k3, Category.assoc, Category.assoc]
    exact ec.symm)
  have H := congrArg (fun z => z.left) (MonObj.comp_mul j x₁ y₁)
  rw [hx, hy] at H
  rw [← Category.assoc, ← Category.assoc, k, k₁, ← E, ← E₁, ← H]
  exact Category.id_comp _
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem lam_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  LBIso.chartPull (chartPullId L) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L (𝟙 X) (𝟙 X) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)

theorem exists_finite_ext : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (A' : PolAV (Sp Ω)) (α : A'.A.left ⟶ A.A.left) (α₂ : (G2 A'.A).left ⟶ (G2 A.A).left), IsGrpPullback A'.A A.A (spMap ga) α → Geo.Tor.IsSquare α α₂ → LBIso (abelian₂ A'.A A'.L) ((abelian₂ A.A A.L).pull α₂) → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (p : pullback A'.A.hom (spMap j) ⟶ A₁.A.left), io.Finite ∧ l.comp io = j.comp ga ∧ IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ Geo.Tor.IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ p ≫ α₁ = pullback.fst _ _ ≫ α ∧ p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l ∧ LBIso (A'.L.pull (pullback.fst A'.A.hom (spMap j))) (A₁.L.pull p) := by
  intro K Ω _ _ _ ga A A' α α₂ hα hsq hΛ
  have := A.isAb.comm
  have := A'.isAb.comm
  obtain ⟨hLB, hrig, hsym, hamp, hK⟩ := pull_pol Ω K (spMap ga) A A'.A α hα
  let P : PolAV (Sp Ω) := ⟨A'.A, A'.isAb, A'.g, A'.smoothDim, A.L.pull α, hLB, hrig, hsym, hamp, hK⟩
  have hΛA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  obtain ⟨β₂, hβ, hT⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (spMap ga) A.A A'.A α hα
  have e₁ := hT A.L (A.L.pull α) _ (abelian₂ A.A A.L) (𝟙 _) A.isLB hLB hΛA (GlobalTheory.PolBaseChange.lbIso_refl hLB)
    (lam_pull_id hΛA)
  rw [Category.comp_id, isSquare_unique α β₂ α₂ hβ hsq] at e₁
  have hΛ' : LBIso (abelian₂ P.A A'.L) (abelian₂ P.A P.L) :=
    LBIso.trans (DVR.linComb_isLB _ A'.isLB _ _) (pull_isLB hΛA _) (DVR.linComb_isLB _ hLB _ _) hΛ e₁.symm
  obtain ⟨x, hx2, hxL⟩ := GlobalTheory.T.exists_twoTorsion_rigidTranslate_same_mumfordBundle Ω P A'.L A'.isLB A'.rigid A'.sym hΛ'
  obtain ⟨K', _, io, l, y, hfin, hcomp, hy2, hy⟩ := GlobalTheory.T.exists_finite_ext_twoTorsion_point_abelianVariety K Ω ga A A'.A α hα x hx2
  obtain ⟨A₁, α₁, α₁₂, t, hα₁, hsq₁, hΛ₁, ht, hL₁⟩ := GlobalTheory.T.exists_baseChange_polarisation_translate_two_torsion K K' io A y hy2
  have hid : spMap (RingHom.id Ω) = 𝟙 _ := Spec.map_id _
  have w : (pullback.fst A'.A.hom (spMap (RingHom.id Ω)) ≫ α) ≫ A.A.hom =
      (pullback.snd A'.A.hom (spMap (RingHom.id Ω)) ≫ spMap l) ≫ spMap io := by
    rw [Category.assoc, hα.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc]
    congr 1
    rw [← hcomp, hid, Category.id_comp]
    show Spec.map (CommRingCat.ofHom (l.comp io)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  let p := hα₁.1.lift _ _ w
  have hp1 : p ≫ α₁ = pullback.fst _ _ ≫ α := hα₁.1.lift_fst _ _ _
  have hp2 : p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l := hα₁.1.lift_snd _ _ _
  refine ⟨K', inferInstance, io, Ω, inferInstance, RingHom.id Ω, l, A₁, α₁, α₁₂, p, hfin, by rw [hcomp]; rfl,
    hα₁, hsq₁, hΛ₁, hp1, hp2, ?_⟩
  have hc : pullback.fst A'.A.hom (spMap (RingHom.id Ω)) ≫ (toUnit A'.A ≫ x).left ≫ α =
      p ≫ (toUnit A₁.A ≫ t).left ≫ α₁ := by
    have hsnd : pullback.snd A'.A.hom (spMap (RingHom.id Ω)) ≫ spMap (RingHom.id Ω) = pullback.snd _ _ := by
      rw [hid, Category.comp_id]
    show pullback.fst _ _ ≫ (A'.A.hom ≫ x.left) ≫ α = p ≫ (A₁.A.hom ≫ t.left) ≫ α₁
    rw [Category.assoc, ← Category.assoc (pullback.fst _ _), pullback.condition, hsnd, Category.assoc,
      ← Category.assoc p, hp2, Category.assoc, ht, hy]
  have htr := transl_comp_eq A'.A A₁.A A.A (spMap ga) (spMap io) α α₁ hα hα₁ x t _ _ p hp1.symm hc
  have hE := lbIso_diff_pull_pull _ _ _ _ A.L α α₁ _ _ _ _ (pullback.fst A'.A.hom (spMap (RingHom.id Ω))) p A.isLB
    htr hc
  have hR₁ : (rigTransl (A.L.pull α₁) t).IsLB := DVR.linComb_isLB _ (pull_isLB A.isLB _) _ _
  have hR : (rigTransl (A.L.pull α) x).IsLB := DVR.linComb_isLB _ (pull_isLB A.isLB _) _ _
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB hR _) (pull_isLB A₁.isLB _) (GlobalTheory.RigidBundleGlue.LBIso.pull hxL _)
    (LBIso.trans (pull_isLB hR _) (pull_isLB hR₁ _) (pull_isLB A₁.isLB _) hE (GlobalTheory.RigidBundleGlue.LBIso.pull hL₁.symm _))

end GlobalTheory.SymFinExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmetricBundleDescendsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_symmetric_bundle_descends : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (A' : PolAV (Sp Ω)) (α : A'.A.left ⟶ A.A.left) (α₂ : (G2 A'.A).left ⟶ (G2 A.A).left), IsGrpPullback A'.A A.A (spMap ga) α → Geo.Tor.IsSquare α α₂ → LBIso (abelian₂ A'.A A'.L) ((abelian₂ A.A A.L).pull α₂) → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (p : pullback A'.A.hom (spMap j) ⟶ A₁.A.left), io.Finite ∧ l.comp io = j.comp ga ∧ IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ Geo.Tor.IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ p ≫ α₁ = pullback.fst _ _ ≫ α ∧ p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l ∧ LBIso (A'.L.pull (pullback.fst A'.A.hom (spMap j))) (A₁.L.pull p) := by
  first | exact @GlobalTheory.SymFinExt.exists_finite_ext | exact GlobalTheory.SymFinExt.exists_finite_ext | (intros; apply GlobalTheory.SymFinExt.exists_finite_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPolarisedVarietyFiniteExtensionFraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPolarisedVarietyFiniteExtensionFraction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem transport_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left), IsGrpPullback A₁.A A.A (spMap io) α₁ → Geo.Tor.IsSquare α₁ α₁₂ → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂), Function.Injective ρ → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q ∧ LBIso A₂.L (A₁.L.pull q) ∧ gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ G _ _ A gen hgen PP hExt K' _ io A₁ α₁ α₁₂ hα hsqα hΛ R₂ _ _ _ ρ i hρ hi G₂ _ _ β β₂ hβ hsqβ
  haveI := hgen
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R₂)).obj G₂) := Functor.isCommMonObj_obj
  obtain ⟨A₂, q, pq, -, mq, t, ht⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap i.toRingHom) A₁
  have hq : IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q := ⟨pq, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pq.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pq.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mq]; rfl⟩
  have hLq : LBIso A₂.L (A₁.L.pull q) := LBIso.symm ⟨t, ht⟩
  have hsq : jK R₂ ≫ spMap ρ = spMap i.toRingHom ≫ spMap io ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [hi]
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have hgi : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) gen.inv.left := isGrpPullback_of_iso gen.symm
  have gG : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hgi.comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have gA : IsGrpPullback A₂.A G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R)) := hq.comp (hα.comp gG)
  have g₂ : IsGrpPullback ((Over.pullback (jK R₂)).obj G₂) G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (pullback.fst G₂.hom (jK R₂) ≫ β) :=
    ((isGrpPullback_pullback G₂ (jK R₂)).comp hβ).congr hsq rfl
  obtain ⟨e, he, hee⟩ := grpPullback_iso g₂ gA
  haveI := he
  have hei : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hgh : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have h5 : e.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
    rw [← hee, ← Category.assoc, hei, Category.id_comp]
  refine ⟨A₂, e, q, he, ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩, hq, hLq, h5⟩

  obtain ⟨g₂m, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _
    (isGrpPullback_pullback G (jK R))
  obtain ⟨γ₁, hsqγ, Ha⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) A.A _ hgi
  obtain ⟨q₂, hsqq, Hc⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₁.A A₂.A _ hq
  obtain ⟨e₂, hsqe, Hd⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₂.A ((Over.pullback (jK R₂)).obj G₂) _
    (isGrpPullback_of_iso e)
  have hLK := pull_isLB A.isLB gen.hom.left
  have i₀ : LBIso A.L ((A.L.pull gen.hom.left).pull gen.inv.left) :=
    LBIso.chartPull (chartPullUnpull A.L (𝟙 _) rfl)
      (chartPullLinComb A.L gen.hom.left (fun _ => gen.inv.left) (fun _ => 𝟙 _) _ (𝟙 _)
        (fun _ => by rw [hgh, Category.id_comp]))
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A.isLB (𝟙 _)))
  have Ha' := Ha _ _ _ PP g₂m hLK A.isLB hExt.1 i₀ (hExt.2 g₂m hg₂)
  have Hb : LBIso (abelian₂ A₁.A A₁.L) (PP.pull (α₁₂ ≫ γ₁ ≫ g₂m)) :=
    LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB (DVR.linComb_isLB _ A.isLB _ _) _)
      (pull_isLB hExt.1 _) hΛ
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ α₁₂ α₁₂ rfl)
        (chartPullSame PP (fun _ => α₁₂ ≫ γ₁ ≫ g₂m) (fun _ => γ₁ ≫ g₂m) _ α₁₂ fun _ => rfl) Ha')
  have Hc' := Hc _ _ _ PP _ A₁.isLB A₂.isLB hExt.1 hLq Hb
  have Hd' := Hd _ _ _ PP _ A₂.isLB (pull_isLB A₂.isLB _) hExt.1
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A₂.isLB _)) Hc'
  have E : e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      simp only [Category.assoc, hg₂.1, reassoc_of% hsqγ.1, reassoc_of% hsqα.1, reassoc_of% hsqq.1,
        reassoc_of% hsqe.1, hsqβ.1, reassoc_of% hκ₂.1, hee]
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      simp only [Category.assoc, hg₂.2, reassoc_of% hsqγ.2, reassoc_of% hsqα.2, reassoc_of% hsqq.2,
        reassoc_of% hsqe.2, hsqβ.2, reassoc_of% hκ₂.2, hee]
  exact LBIso.trans (DVR.linComb_isLB _ (pull_isLB A₂.isLB _) _ _) (pull_isLB hExt.1 _)
    (pull_isLB (pull_isLB hExt.1 β₂) κ₂) Hd'
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => E) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPolarisedVarietyFiniteExtensionFractionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_polarisedVariety_finiteExtension_fraction : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left), IsGrpPullback A₁.A A.A (spMap io) α₁ → Geo.Tor.IsSquare α₁ α₁₂ → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂), Function.Injective ρ → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q ∧ LBIso A₂.L (A₁.L.pull q) ∧ gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  first | exact @GlobalTheory.Mum.transport_extLam | exact GlobalTheory.Mum.transport_extLam | (intros; apply GlobalTheory.Mum.transport_extLam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUniformisedPullbackMumfordBundleMatching
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUniformisedPullbackMumfordBundleMatching
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem genLam_pull_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → Geo.Tor.IsSquare βW βW₂ → LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) → ∃ (ga : FractionRing R →+* FractionRing W) (α : AW.A.left ⟶ A.A.left) (α₂ : (G2 AW.A).left ⟶ (G2 A.A).left), (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧ IsGrpPullback AW.A A.A (spMap ga) α ∧ Geo.Tor.IsSquare α α₂ ∧ LBIso (abelian₂ AW.A AW.L) ((abelian₂ A.A A.L).pull α₂) ∧ UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hExt W _ _ _ φ GW _ _ βW βW₂ DW AW UW hW hφ hφl hβ hsqW hPP
  let ga : FractionRing R →+* FractionRing W := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ
  have hga : ∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r) := fun r => by
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  let κW : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst _ _ ≫ βW) (pullback.snd _ _ ≫ spMap ga) (by
      rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κW ≫ pullback.fst G.hom (jK R) = pullback.fst GW.hom (jK W) ≫ βW := pullback.lift_fst _ _ _
  have w : κW ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GW).hom ≫ spMap ga :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GW) ((Over.pullback (jK R)).obj G) (spMap ga) κW :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GW (jK W)).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK W)).obj GW) := Functor.isCommMonObj_obj
  have : IsMonHom UW.gen.hom := UW.gen_hom
  have : IsMonHom gen.hom := hgen
  have : IsMonHom UW.gen.symm.hom := show IsMonHom UW.gen.inv by infer_instance
  have hu : IsGrpPullback AW.A ((Over.pullback (jK W)).obj GW) (𝟙 _) UW.gen.inv.left :=
    isGrpPullback_of_iso UW.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G) A.A (𝟙 _) gen.hom.left := isGrpPullback_of_iso gen
  have hα : IsGrpPullback AW.A A.A (spMap ga) (UW.gen.inv.left ≫ κW ≫ gen.hom.left) :=
    (hu.comp (hκ.comp hg)).congr (by simp) rfl
  obtain ⟨u₂, squ, Hu⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hu
  obtain ⟨κ₂, sqκ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hκ
  obtain ⟨g₂, sqg, Hg⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hg
  obtain ⟨fW₂, sqfW, HfW⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback GW (jK W))
  obtain ⟨fR₂, sqfR, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback G (jK R))
  have hLA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLG : (UW.LG.L.pull (pullback.fst GW.hom (jK W))).IsLB := pull_isLB UW.LG.isLB _
  have hAg : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _

  have Z : LBIso (abelian₂ ((Over.pullback (jK R)).obj G) (A.L.pull gen.hom.left)) ((abelian₂ A.A A.L).pull g₂) := by
    have h := Hg A.L (A.L.pull gen.hom.left) _ (abelian₂ A.A A.L) (𝟙 _) A.isLB hAg hLA
      (PolBaseChange.lbIso_refl hAg)
      (LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl hLA))
    rwa [Category.comp_id] at h
  have Y : LBIso (PP.pull fR₂) ((abelian₂ A.A A.L).pull g₂) :=
    LBIso.trans (pull_isLB hExt.1 _) (DVR.linComb_isLB _ hAg _ _) (pull_isLB hLA _) (hExt.2 fR₂ sqfR).symm Z
  have e : fW₂ ≫ βW₂ = κ₂ ≫ fR₂ := by
    apply pullback.hom_ext
    · show (fW₂ ≫ βW₂) ≫ (fst G G).left = (κ₂ ≫ fR₂) ≫ (fst G G).left
      simp only [Category.assoc, hsqW.1, sqfR.1]
      rw [← Category.assoc fW₂, sqfW.1, reassoc_of% sqκ.1, hκf, Category.assoc]
    · show (fW₂ ≫ βW₂) ≫ (snd G G).left = (κ₂ ≫ fR₂) ≫ (snd G G).left
      simp only [Category.assoc, hsqW.2, sqfR.2]
      rw [← Category.assoc fW₂, sqfW.2, reassoc_of% sqκ.2, hκf, Category.assoc]
  have B1 : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      (PP.pull (κ₂ ≫ fR₂)) := by
    have h := HfW UW.LG.L (UW.LG.L.pull (pullback.fst GW.hom (jK W))) _ PP βW₂ UW.LG.isLB hLG hExt.1
      (PolBaseChange.lbIso_refl hLG) hPP
    rwa [e] at h
  have B3 : LBIso (PP.pull (κ₂ ≫ fR₂)) ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.chartPull (chartPullSame PP _ (fun _ => fR₂) _ κ₂ fun _ => rfl)
      (chartPullSame (abelian₂ A.A A.L) _ (fun _ => g₂) _ κ₂ fun _ => rfl) Y
  have hLamW : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.trans (DVR.linComb_isLB _ hLG _ _) (pull_isLB hExt.1 _) (pull_isLB hLA _) B1 B3

  have hN : LBIso AW.L ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) := by
    have hext : LBIso (AW.L.pull UW.gen.hom.left) (UW.LG.L.pull (pullback.fst GW.hom (jK W))) := UW.ext
    have h1 : LBIso (AW.L.pull (𝟙 _)) ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) :=
      LBIso.chartPull (chartPullSame AW.L _ (fun _ => UW.gen.hom.left) _ UW.gen.inv.left fun _ => by
          rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left])
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) hext
    have h0 : LBIso AW.L (AW.L.pull (𝟙 _)) :=
      LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl AW.isLB)
    exact LBIso.trans AW.isLB (pull_isLB AW.isLB _) (pull_isLB hLG _) h0 h1
  refine ⟨ga, UW.gen.inv.left ≫ κW ≫ gen.hom.left, u₂ ≫ κ₂ ≫ g₂, hga, hα, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Category.assoc, sqg.1, reassoc_of% sqκ.1, reassoc_of% squ.1]
  · simp only [Category.assoc, sqg.2, reassoc_of% sqκ.2, reassoc_of% squ.2]
  · exact Hu _ AW.L _ (abelian₂ A.A A.L) (κ₂ ≫ g₂) hLG AW.isLB hLA hN hLamW
  · rw [Category.assoc, Category.assoc, ← Category.assoc gen.hom.left, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.id_comp, hκf]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUniformisedPullbackMumfordBundleMatchingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_uniformised_pullback_mumfordBundle_matching : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → Geo.Tor.IsSquare βW βW₂ → LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) → ∃ (ga : FractionRing R →+* FractionRing W) (α : AW.A.left ⟶ A.A.left) (α₂ : (G2 AW.A).left ⟶ (G2 A.A).left), (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧ IsGrpPullback AW.A A.A (spMap ga) α ∧ Geo.Tor.IsSquare α α₂ ∧ LBIso (abelian₂ AW.A AW.L) ((abelian₂ A.A A.L).pull α₂) ∧ UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  first | exact @GlobalTheory.Mum.genLam_pull_of_unif | exact GlobalTheory.Mum.genLam_pull_of_unif | (intros; apply GlobalTheory.Mum.genLam_pull_of_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCompleteTraitBaseChangeFiniteExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCompleteTraitBaseChangeFiniteExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unif_trait_baseChange : ∀ (R R₂ W W₂ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] (ρ : R →+* R₂) (φ : R →+* W) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂), Base R → GlobalTheory.LN.CDvr W → GlobalTheory.LN.CDvr W₂ → FinExt σ → IsLocalHom σ → φ₂.comp ρ = σ.comp φ → Function.Injective φ₂ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left), IsGrpPullback G₂ G (spMap ρ) β → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left), IsGrpPullback GW G (spMap φ) βW → ∀ (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), ∃ (GW' : Over (Sp W₂)) (_ : GrpObj GW') (_ : IsCommMonObj GW') (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' ∧ IsGrpPullback GW' GW (spMap σ) τ ∧ βW' ≫ β = τ ≫ βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' ∧ LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) := by
  intro R R₂ W W₂ _ _ _ _ _ _ _ _ _ _ _ _ ρ φ σ φ₂ _ hW hW₂ hσ hloc hc hφ₂ G _ _ hG G₂ _ _ β hβ GW _ _ βW hβW DW AW UW
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have := hW.1
  have hWa : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hGW : IsSemiAbelian GW := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hβW (isGrpPullback_pullback G (spMap φ))
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ G hG)
  obtain ⟨D₁, hX, A₁, U₁, hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hWa hσ.1 σ hσ.2.1 (map_maximalIdeal_le σ) hGW UW
  have hτ : IsGrpPullback ((Over.pullback (specOf σ)).obj GW) GW (spMap σ) (pullback.fst GW.hom (specOf σ)) :=
    isGrpPullback_pullback GW (specOf σ)
  have hb : spMap σ ≫ spMap φ = spMap φ₂ ≫ spMap ρ := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  have hn := (hτ.comp hβW).congr hb rfl
  have hw : (pullback.fst GW.hom (specOf σ) ≫ βW) ≫ G.hom =
      (((Over.pullback (specOf σ)).obj GW).hom ≫ spMap φ₂) ≫ spMap ρ := by
    rw [hn.1.w]; exact (Category.assoc _ _ _).symm
  have h₁ := hβ.1.lift_fst _ _ hw
  have h₂ := hβ.1.lift_snd _ _ hw
  have hβ' : IsGrpPullback ((Over.pullback (specOf σ)).obj GW) G₂ (spMap φ₂) (hβ.1.lift _ _ hw) :=
    hβ.cancel (hn.congr rfl h₁.symm) h₂
  have hsq : jK W₂ ≫ spMap φ₂ =
      spMap (IsFractionRing.map (K := FractionRing R₂) (L := FractionRing W₂) hφ₂) ≫ jK R₂ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [IsFractionRing.map, IsLocalization.map_eq]
  have cond : (pullback.fst ((Over.pullback (specOf σ)).obj GW).hom (jK W₂) ≫ hβ.1.lift _ _ hw) ≫ G₂.hom =
      (pullback.snd ((Over.pullback (specOf σ)).obj GW).hom (jK W₂) ≫
        spMap (IsFractionRing.map (K := FractionRing R₂) (L := FractionRing W₂) hφ₂)) ≫ jK R₂ := by
    rw [Category.assoc, h₂, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc]
  refine ⟨(Over.pullback (specOf σ)).obj GW, inferInstance, inferInstance, hβ.1.lift _ _ hw,
    pullback.fst GW.hom (specOf σ), D₁, A₁, U₁, pullback.lift _ _ cond, hβ', hτ, h₁, pullback.lift_fst _ _ _, ?_⟩
  obtain ⟨wL, hwL, -⟩ := hP.lg
  exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull U₁.LG.L _ _ rfl)
    (chartPullSame UW.LG.L _ (fun _ => (Iso.refl ((Over.pullback (specOf σ)).obj GW)).hom.left ≫
      pullback.fst GW.hom (specOf σ)) _ _ fun _ => by
        exact congrArg (_ ≫ ·) (Category.id_comp _).symm) ⟨wL, hwL⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCompleteTraitBaseChangeFiniteExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_completeTrait_baseChange_finite_ext : ∀ (R R₂ W W₂ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W₂] [IsDomain W₂] [IsLocalRing W₂] (ρ : R →+* R₂) (φ : R →+* W) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂), Base R → GlobalTheory.LN.CDvr W → GlobalTheory.LN.CDvr W₂ → FinExt σ → IsLocalHom σ → φ₂.comp ρ = σ.comp φ → Function.Injective φ₂ → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left), IsGrpPullback G₂ G (spMap ρ) β → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left), IsGrpPullback GW G (spMap φ) βW → ∀ (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), ∃ (GW' : Over (Sp W₂)) (_ : GrpObj GW') (_ : IsCommMonObj GW') (βW' : GW'.left ⟶ G₂.left) (τ : GW'.left ⟶ GW.left) (DW' : DegData W₂ (maximalIdeal W₂)) (AW' : PolAV (Sp (FractionRing W₂))) (UW' : Unif (maximalIdeal W₂) DW' AW' GW') (κ : pullback GW'.hom (jK W₂) ⟶ pullback G₂.hom (jK R₂)), IsGrpPullback GW' G₂ (spMap φ₂) βW' ∧ IsGrpPullback GW' GW (spMap σ) τ ∧ βW' ≫ β = τ ≫ βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW' ∧ LBIso (UW'.LG.L.pull (pullback.fst GW'.hom (jK W₂))) (UW.LG.L.pull (pullback.fst GW'.hom (jK W₂) ≫ τ)) := by
  first | exact @GlobalTheory.Mum.unif_trait_baseChange | exact GlobalTheory.Mum.unif_trait_baseChange | (intros; apply GlobalTheory.Mum.unif_trait_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionTraitUniformisingMumfordBun
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_finExt_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂), FinExt ρ ∧ ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  obtain ⟨W, _, _, _, φ, GW, _, _, βW, βW₂, DW, AW, UW, hW, hφi, hφl, hpbW, hsqW, hlamW⟩ :=
    GlobalTheory.T.exists_trait_uniformisation_mumfordBundle R hR G hG A gen hgen PP hPP
  obtain ⟨ga, α, α₂, hga, hpbα, hsqα, hlamα, hcompα⟩ :=
    GlobalTheory.T.generic_uniformised_pullback_mumfordBundle_matching R hR G hG A gen hgen PP hPP W φ GW βW βW₂ DW AW UW hW hφi hφl hpbW hsqW hlamW

  have : CharZero R := hR.2
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨K', _, io, Ω', _, j, l, A₁, α₁, α₁₂, p, hio, hlio, hpb₁, hsq₁, hlam₁, hp₁, hp₂, hpL⟩ :=
    GlobalTheory.T.exists_finite_extension_symmetric_bundle_descends (FractionRing R) (FractionRing W) ga A AW α α₂ hpbα hsqα hlamα
  have hcomp : ∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r)) := by
    intro r
    have h := DFunLike.congr_fun hlio (algebraMap R (FractionRing R) r)
    simp only [RingHom.comp_apply] at h
    rw [h, hga]
  obtain ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hρ, hW₂, hσ, hσl, hφ₂i, hφ₂l, hsq, hi, hj₂, hl₂⟩ :=
    GlobalTheory.T.exists_common_extension_dvr_fraction_fields R W hR hW φ hφi hφl K' Ω' io j l hio hcomp
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ, hρ, ?_⟩
  intro G₂ _ _ β β₂ hpb₂ hsq₂
  obtain ⟨A₂, gen₂, q, hgen₂, hext₂, hpbq, hlamq, hcompq⟩ :=
    GlobalTheory.T.transport_polarisedVariety_finiteExtension_fraction R G A gen hgen PP hPP K' io A₁ α₁ α₁₂ hpb₁ hsq₁ hlam₁ R₂ ρ i hρ.2.1 hi G₂ β β₂ hpb₂ hsq₂
  obtain ⟨GW', _, _, βW', τ, DW', AW', UW', κ, hpbW', hpbτ, hβτ, hκ, hLτ⟩ :=
    GlobalTheory.T.uniformisation_completeTrait_baseChange_finite_ext R R₂ W W₂ ρ φ σ φ₂ hR hW hW₂ hσ hσl hsq hφ₂i G hG G₂ β hpb₂ GW βW hpbW DW AW UW
  refine ⟨A₂, gen₂, W₂, inferInstance, inferInstance, inferInstance, φ₂, GW', inferInstance, inferInstance,
    βW', DW', AW', UW', κ, hgen₂, hext₂, hW₂, hφ₂i, hφ₂l, hpbW', hκ, ?_⟩
  exact GlobalTheory.T.uniformisation_bundle_genericFibre_descent R W R₂ W₂ K' Ω' φ ρ σ φ₂ io j l i j₂ hφi hρ.2.1 hσ.2.1 hφ₂i hsq hcomp hi hj₂ hl₂
    G A gen GW βW DW AW UW α hpbW hcompα A₁ α₁ p hpb₁ hp₁ hp₂ hpL G₂ β A₂ gen₂ q hpb₂ hpbq hlamq hcompq
    GW' βW' τ DW' AW' UW' κ hpbW' hpbτ hβτ hκ hLτ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionTraitUniformisingMumfordBunStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_trait_uniformisingMumfordBundle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂), FinExt ρ ∧ ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  first | exact @GlobalTheory.Mum.exists_finExt_trait_unif_lam | exact GlobalTheory.Mum.exists_finExt_trait_unif_lam | (intros; apply GlobalTheory.Mum.exists_finExt_trait_unif_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionIdempotentFactorTraitUnif
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FactorMove

theorem isLocalHom_of_finExt {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    {ρ : R →+* R'} (h : FinExt ρ) : IsLocalHom ρ := by
  letI := ρ.toAlgebra
  have hi : Algebra.IsIntegral R R' := ⟨fun x => h.2.2.to_isIntegral x⟩
  have hm : (maximalIdeal R').comap ρ = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (algebraMap _ _) h.2.2.to_isIntegral (maximalIdeal R'))
  exact ((IsLocalRing.local_hom_tfae ρ).out 1 5).2 hm

theorem exists_factor {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁] [GrpObj G₂]
    {f : S₁ ⟶ S} {g : S₂ ⟶ S₁} {β₁ : G₁.left ⟶ G.left} {β₂ : G₂.left ⟶ G.left}
    {β₁₂ : (G₁ ⊗ G₁).left ⟶ (G ⊗ G).left} {β₂₂ : (G₂ ⊗ G₂).left ⟶ (G ⊗ G).left}
    (h₁ : IsGrpPullback G₁ G f β₁) (h₂ : IsGrpPullback G₂ G (g ≫ f) β₂)
    (s₁ : Geo.Tor.IsSquare β₁ β₁₂) (s₂ : Geo.Tor.IsSquare β₂ β₂₂) :
    ∃ (β : G₂.left ⟶ G₁.left) (β' : (G₂ ⊗ G₂).left ⟶ (G₁ ⊗ G₁).left),
      IsGrpPullback G₂ G₁ g β ∧ Geo.Tor.IsSquare β β' ∧ β₂₂ = β' ≫ β₁₂ := by
  have w₀ : β₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f := by rw [h₂.1.w, Category.assoc]
  have e : h₁.1.lift β₂ (G₂.hom ≫ g) w₀ ≫ β₁ = β₂ := h₁.1.lift_fst _ _ _
  have w : h₁.1.lift β₂ (G₂.hom ≫ g) w₀ ≫ G₁.hom = G₂.hom ≫ g := h₁.1.lift_snd _ _ _
  generalize h₁.1.lift β₂ (G₂.hom ≫ g) w₀ = β at e w
  have s : Geo.Tor.IsSquare β (lift (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂))).left :=
    ⟨congrArg (fun q => q.left) (lift_fst (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂))),
      congrArg (fun q => q.left) (lift_snd (pushPt w (fst G₂ G₂)) (pushPt w (snd G₂ G₂)))⟩
  obtain ⟨β', s⟩ : ∃ β' : (G₂ ⊗ G₂).left ⟶ (G₁ ⊗ G₁).left, Geo.Tor.IsSquare β β' := ⟨_, s⟩
  refine ⟨β, β', IsGrpPullback.cancel h₁ (h₂.congr rfl e.symm) w, s, ?_⟩
  have a : β₂₂ ≫ (fst G G).left = (β' ≫ β₁₂) ≫ (fst G G).left := by
    rw [s₂.1, Category.assoc, s₁.1, ← Category.assoc, s.1, Category.assoc, e]
  have b : β₂₂ ≫ (snd G G).left = (β' ≫ β₁₂) ≫ (snd G G).left := by
    rw [s₂.2, Category.assoc, s₁.2, ← Category.assoc, s.2, Category.assoc, e]
  exact pullback.hom_ext a b

theorem extLam_congr {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {L : LB ((Over.pullback (jK R)).obj G).left} (hL : L.IsLB) {P Q : LB (G2 G).left} (h : ExtLam G L P) (hQ : Q.IsLB)
    (e : LBIso P Q) : ExtLam G L Q :=
  ⟨hQ, fun κ hκ => LBIso.trans (LB.isLB_linComb hL _ _) (LB.isLB_pull h.1 _) (LB.isLB_pull hQ _) (h.2 κ hκ)
    (GlobalTheory.GenSpread.lbIso_pullback e κ)⟩

theorem exists_finExt_factor_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ D₂' : DegData R₂ (maximalIdeal R₂)) (F₂ : Factor D₂.toPre D₂'.toPre) (A₂' : PolAV (Sp (FractionRing R₂))) (G₂' : Over (Sp R₂)) (_ : GrpObj G₂') (_ : IsCommMonObj G₂') (U₂' : Unif (maximalIdeal R₂) D₂' A₂' G₂') (oA₂ : A₂'.OAct F₂.O) (oG₂ : RingAct G₂' F₂.O) (G₂ : Over (Sp R₂)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (inc₂ : G₂ ⟶ G₂') (pr₂ : G₂' ⟶ G₂) (β₂ : G₂.left ⟶ G.left) (β₂₂ : (G2 G₂).left ⟶ (G2 G).left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), FinExt ρ₂ ∧ Base R₂ ∧ IsSemiAbelian G₂' ∧ U₂'.toUnifPre.OLinear F₂.O F₂.o oA₂ oG₂ ∧ IsSemiAbelian G₂ ∧ IsMonHom inc₂ ∧ IsMonHom pr₂ ∧ inc₂ ≫ pr₂ = 𝟙 G₂ ∧ pr₂ ≫ inc₂ = oG₂.act F₂.e ∧ IsGrpPullback G₂ G (spMap ρ₂) β₂ ∧ Geo.Tor.IsSquare β₂ β₂₂ ∧ IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) ∧ LBIso ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hO G _ _ hG inc pr hinc hpr hip hpi R₁ _ _ _ ρ₁ G₁ _ _ β₁ β₁₂ A₁ gen₁
    hρ₁ hβ₁ hsq₁ hgen₁ hext
  haveI := hR.2
  have hR₁ : Base R₁ := ⟨hρ₁.1, charZero_of_injective_ringHom hρ₁.2.1⟩
  have hG₁ : IsSemiAbelian G₁ := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hβ₁ (isGrpPullback_pullback G (spMap ρ₁))
    exact GlobalTheory.isSemiAbelian_of_grpIso e (Geo.Tor.IsSemiAbelian.pullback (f := spMap ρ₁) (G := G) hG)
  obtain ⟨R₂, _, _, _, ρ, hρ, H⟩ := GlobalTheory.T.exists_finiteExtension_trait_uniformisingMumfordBundle R₁ hR₁ G₁ hG₁ A₁ gen₁ hgen₁ _ hext
  have hρ₂ : FinExt (ρ.comp ρ₁) := ⟨hρ.1, hρ.2.1.comp hρ₁.2.1, hρ.2.2.comp hρ₁.2.2⟩
  have hR₂ : Base R₂ := ⟨hρ.1, charZero_of_injective_ringHom hρ₂.2.1⟩
  obtain ⟨D₂, D₂', F₂, A₂', G₂', _, _, U₂', oA₂, oG₂, G₂, _, _, β₂, β₂₂, inc₂, pr₂, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    GlobalTheory.FactorPull.factor_baseChange R hR.1 D D' F A' G' hG' U' oA oG hO G hG inc pr hinc hpr hip hpi R₂ (ρ.comp ρ₁) hρ.1
      hρ₂.2.1 (isLocalHom_of_finExt hρ₂)
  have es : spMap (ρ.comp ρ₁) = spMap ρ ≫ spMap ρ₁ := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨β, β', hβ, hsq, hc⟩ := exists_factor hβ₁ (h8.congr es rfl) hsq₁ h9
  obtain ⟨A₂, gen₂, W, _, _, _, φ, GW, _, _, βW, DW, AW, UW, κ, k1, k2, k3, k4, k5, k6, k7, k8⟩ := H G₂ β β' hβ hsq
  have hP := LB.isLB_pull (L := abelian₂ G' U'.LG.L) (LB.isLB_linComb U'.LG.isLB _ _)
    (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  have hP₂ := LB.isLB_pull (L := abelian₂ G₂' U₂'.LG.L) (LB.isLB_linComb U₂'.LG.isLB _ _)
    (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ.comp ρ₁, D₂, D₂', F₂, A₂', G₂', inferInstance, inferInstance,
    U₂', oA₂, oG₂, G₂, inferInstance, inferInstance, inc₂, pr₂, β₂, β₂₂, A₂, gen₂, W, inferInstance, inferInstance,
    inferInstance, φ, GW, inferInstance, inferInstance, βW, DW, AW, UW, κ, hρ₂, hR₂, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    k1, ?_, h10, k3, k4, k5, k6, k7, k8⟩
  exact extLam_congr (LB.isLB_pull A₂.isLB _) k2 hP₂
    (LBIso.trans hP₂ (LB.isLB_pull hP _) k2.1 h10 (GlobalTheory.GenSpread.lbIso_pull_pull hP β' hc)).symm

end GlobalTheory.Mum.FactorMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionIdempotentFactorTraitUnifStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExtension_idempotentFactor_trait_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ D₂' : DegData R₂ (maximalIdeal R₂)) (F₂ : Factor D₂.toPre D₂'.toPre) (A₂' : PolAV (Sp (FractionRing R₂))) (G₂' : Over (Sp R₂)) (_ : GrpObj G₂') (_ : IsCommMonObj G₂') (U₂' : Unif (maximalIdeal R₂) D₂' A₂' G₂') (oA₂ : A₂'.OAct F₂.O) (oG₂ : RingAct G₂' F₂.O) (G₂ : Over (Sp R₂)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (inc₂ : G₂ ⟶ G₂') (pr₂ : G₂' ⟶ G₂) (β₂ : G₂.left ⟶ G.left) (β₂₂ : (G2 G₂).left ⟶ (G2 G).left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), FinExt ρ₂ ∧ Base R₂ ∧ IsSemiAbelian G₂' ∧ U₂'.toUnifPre.OLinear F₂.O F₂.o oA₂ oG₂ ∧ IsSemiAbelian G₂ ∧ IsMonHom inc₂ ∧ IsMonHom pr₂ ∧ inc₂ ≫ pr₂ = 𝟙 G₂ ∧ pr₂ ≫ inc₂ = oG₂.act F₂.e ∧ IsGrpPullback G₂ G (spMap ρ₂) β₂ ∧ Geo.Tor.IsSquare β₂ β₂₂ ∧ IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) ∧ LBIso ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  first | exact @GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait | exact GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait | (intros; apply GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait <;> assumption)
end
