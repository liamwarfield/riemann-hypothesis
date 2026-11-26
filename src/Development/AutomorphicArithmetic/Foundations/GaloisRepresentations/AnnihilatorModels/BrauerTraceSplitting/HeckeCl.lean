module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.HeckeCl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.DescIsoOfPb
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

private lemma pb_comp (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ)
    (x : GlobalTheory.EtC.HQ l (GlobalTheory.EtC.sch.obj C) n 0) :
    GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map (f ≫ g)) n 0 x =
      GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map f) n 0 (GlobalTheory.EtC.pullHQ l (GlobalTheory.EtC.sch.map g) n 0 x) := by
  rw [Functor.map_comp, GlobalTheory.EtC.pullHQ, GlobalTheory.EtC.pullHl_comp, LinearMap.baseChange_comp]; rfl

private lemma pb_lift {A B S S' : Scheme.{0}} (a : A ⟶ S) (q : B ⟶ S) (u : A ⟶ B) (hu : u ≫ q = a)
    (c : S' ⟶ S) (h : (pullback.fst a c ≫ u) ≫ q = pullback.snd a c ≫ c) :
    IsPullback (pullback.fst a c) (pullback.lift (pullback.fst a c ≫ u) (pullback.snd a c) h) u
      (pullback.fst q c) := by
  subst hu
  refine IsPullback.of_bot (h₁₁ := pullback.fst (u ≫ q) c) (v₂₁ := pullback.snd q c) (v₂₂ := q) (h₃₁ := c)
    ?_ ?_ (IsPullback.of_hasPullback q c)
  · rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback _ _
  · rw [pullback.lift_fst]

private lemma desc_iso_of_pb {X Y Y' Z Z' : Scheme.{0}} {p : Z ⟶ Y} {p' : Z' ⟶ Y'} {a : Y' ⟶ Y} {b : Z' ⟶ Z}
    (P : IsPullback b p' p a) (x : X ⟶ Y') {m : ℕ} (z : Fin m → (X ⟶ Z')) (hz : ∀ i, z i ≫ p' = x)
    (H : SplitOn p (x ≫ a) fun i => z i ≫ b) :
    IsIso (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p' x) := by
  obtain ⟨h, hI⟩ := H
  have Q := (IsPullback.of_hasPullback p' x).paste_horiz P
  have claim : (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p' x) ≫ Q.isoPullback.hom =
      Sigma.desc (fun i => pullback.lift (z i ≫ b) (𝟙 X) (by rw [h i, Category.id_comp])) := by
    apply Sigma.hom_ext
    intro i
    rw [Sigma.ι_desc_assoc, Sigma.ι_desc]
    apply pullback.hom_ext
    · rw [Category.assoc, Q.isoPullback_hom_fst, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, Q.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]
  haveI : IsIso ((Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p' x) ≫ Q.isoPullback.hom) := by
    rw [claim]; exact hI
  exact IsIso.of_isIso_comp_right _ Q.isoPullback.hom

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private abbrev G {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) : E.gb M ⟶ E.gb N :=
  GlobalTheory.Et.geomMap (PadicAlgCl l) M.q (Model.genMap u hu) (Model.genMap_q u hu)

private abbrev gX (M : Model l K) : E.gb M ⟶ M.X := pullback.fst _ _ ≫ pullback.fst _ _

private lemma G_gX {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) : G u hu ≫ gX N = gX M ≫ u := by
  rw [G, gX, GlobalTheory.Et.geomMap, pullback.lift_fst_assoc, Category.assoc, Model.genMap, pullback.lift_fst,
    gX, Category.assoc]

private lemma G_comp {A B C : Model l K} (u : A.X ⟶ B.X) (hu : u ≫ B.p = A.p) (v : B.X ⟶ C.X)
    (hv : v ≫ C.p = B.p) (h : (u ≫ v) ≫ C.p = A.p) : G u hu ≫ G v hv = G (u ≫ v) h := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [G, GlobalTheory.Et.geomMap, Model.genMap]
    · simp [G, GlobalTheory.Et.geomMap, Model.genMap]
  · simp [G, GlobalTheory.Et.geomMap]

private lemma unit_gb (W : Model l K) : IsUnit (l : Γ(E.gb W, ⊤)) := by
  have hu : IsUnit ((l : ℕ) : PadicAlgCl l) :=
    (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero).isUnit
  let φ : CommRingCat.of (PadicAlgCl l) ⟶ Γ(E.gb W, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl l))).inv ≫ (pullback.snd W.q _).appTop
  have := hu.map φ.hom
  rwa [map_natCast] at this

private lemma corr_pb (M : Model l K) (T : Corr l M.X) : IsPullback (gX (corrM M T)) (corrP M T) T.p (gX M) := by
  have s1 := pb_lift (corrM M T).p M.p T.p rfl (Spec.map (CommRingCat.ofHom (OK l K).subtype))
    (by rw [Category.assoc]; exact pullback.condition)
  have s2 := pb_lift (corrM M T).q M.q (Model.genMap (M := corrM M T) (N := M) T.p rfl)
    (Model.genMap_q (M := corrM M T) (N := M) T.p rfl)
    (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
    (by rw [Category.assoc, Model.genMap_q]; exact pullback.condition)
  exact s2.paste_horiz s1

theorem hkOfPush : UpperTheory.Ru.crystallineComparison.HkOfPush := by
  intro l _ K M T hr j t hP W w hw z hz hsp v
  have hzp : ∀ i, z i ≫ (corrM M T).p = W.p := fun i => by
    show z i ≫ T.p ≫ M.p = W.p
    rw [← Category.assoc, hz, hw]
  have hs : ∀ i, G (M := W) (N := corrM M T) (z i) (hzp i) ≫ corrP M T = G (M := W) (N := M) w hw := fun i => by
    have e := G_comp (A := W) (B := corrM M T) (C := M) (z i) (hzp i) T.p rfl (by rw [hz, hw])
    have e' : G (M := W) (N := M) (z i ≫ T.p) (by rw [hz, hw] : (z i ≫ T.p) ≫ M.p = W.p) = G (M := W) (N := M) w hw := by
      have := hz i
      subst this
      rfl
    exact e.trans e'
  have hsplit : SplitOn T.p (G (M := W) (N := M) w hw ≫ gX M) fun i => G (M := W) (N := corrM M T) (z i) (hzp i) ≫ gX (corrM M T) := by
    have H := hsp (E.gb W) (gX W) (unit_gb W)
    have e1 : G (M := W) (N := M) w hw ≫ gX M = gX W ≫ w := G_gX (M := W) (N := M) w hw
    have e2 : (fun i => G (M := W) (N := corrM M T) (z i) (hzp i) ≫ gX (corrM M T)) = fun i => gX W ≫ z i :=
      funext fun i => G_gX (M := W) (N := corrM M T) (z i) (hzp i)
    rw [e1, e2]
    exact H
  have hI := desc_iso_of_pb (corr_pb M T) (G (M := W) (N := M) w hw) (fun i => G (M := W) (N := corrM M T) (z i) (hzp i)) hs hsplit
  have key := hP (E.gb W) (G (M := W) (N := M) w hw) T.d (fun i => G (M := W) (N := corrM M T) (z i) (hzp i)) hs hI (Model.pullV (M := corrM M T) (N := M) T.r hr j v)
  refine key.trans (Finset.sum_congr rfl fun i _ => ?_)
  have e := G_comp (A := W) (B := corrM M T) (C := M) (z i) (hzp i) T.r hr
    (by rw [Category.assoc, hr, ← Category.assoc, hz, hw])
  have := pb_comp l (G (M := W) (N := corrM M T) (z i) (hzp i)) (G (M := corrM M T) (N := M) T.r hr) j v
  rw [e] at this
  exact this.symm

end UpperTheory.Ru.crystallineComparison
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.TrPush
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3

namespace UpperTheory.Gal.crystallineComparison.Br

theorem trPush : TrPush := by
  intro l _ B Z Y p q s hs n tr htr W x m σ hσ hiso z
  exact htr W (x ≫ p) x rfl (Fin m) σ (fun j => by rw [← hs, ← Category.assoc, hσ j]) ⟨hσ, hiso⟩ z

end UpperTheory.Gal.crystallineComparison.Br
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.BcSplits
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3

private theorem bcSplits : BcSplits :=
  pBcSplits (pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits)

theorem UpperTheory.Gal.crystallineComparison.Br.trBc :
    UpperTheory.Gal.crystallineComparison.Br.TrBc := by
  intro B B' R _ T g Z Y p q s _ _ hs tr htr W r c hc J _ σ hσ hsp x
  exact htr _ (pullback.snd r g) (UpperTheory.Gal.G3.bcMap g c hc) (bcMap_snd g c hc) J
    (fun j ↦ UpperTheory.Gal.G3.bcMap g (σ j) ((hσ j).trans rfl)) (fun j ↦ bcMap_snd g (σ j) _)
    ((bcSplits g p q r s hs c hc J σ hσ).2.2 hsp) x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.TrTot
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3

namespace UpperTheory.Gal.crystallineComparison.Br

theorem trTot : TrTot := by
  intro l _ B Z Y p q s tr htr W r c hc J _ σ hσ hsp x
  change Htot l (sch.obj Y) at x
  change pullTot l (sch.map c) (DirectSum.lmap tr x) = ∑ j, pullTot l (sch.map (σ j)) x
  ext n
  rw [DirectSum.sum_apply]
  simp only [pullTot, DirectSum.lmap_apply]
  exact htr n W r c hc J σ hσ hsp (x n)

end UpperTheory.Gal.crystallineComparison.Br
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.BrauerTraceSplitting.GenFEt
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt gen)

namespace UpperTheory.Gal.crystallineComparison.Br

private theorem range_subset_basicOpen (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) {Y P : Scheme.{0}} (a : P ⟶ Y)
    (c : P ⟶ sp k) : Set.range a ⊆ (Y.basicOpen (l : Γ(Y, ⊤)) : Set Y) := by
  rintro _ ⟨x, rfl⟩
  have h1 : IsUnit ((l : Γ(sp k, ⊤))) := by
    have := (IsUnit.mk0 _ hl).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    simpa using this
  have h2 : IsUnit ((l : Γ(P, ⊤))) := by
    have := h1.map (c.app ⊤).hom
    rwa [map_natCast] at this
  have hu : IsUnit (a.app ⊤ (l : Γ(Y, ⊤))) := by
    rw [map_natCast]
    exact h2
  have hx : x ∈ a ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) := by
    rw [Scheme.preimage_basicOpen, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact hx

theorem genFEt : GenFEt := by
  intro l O k _ _ _ hl Y p T
  have sY := (IsPullback.of_hasPullback p (gen O k)).flip
  have sZ := (IsPullback.of_hasPullback (T.p ≫ p) (gen O k)).flip
  have hsq : IsPullback (pullback.fst (T.p ≫ p) (gen O k)) (bcMap (gen O k) (p := p) T.p rfl)
      T.p (pullback.fst p (gen O k)) := by
    have h := IsPullback.of_right (h₁₁ := bcMap (gen O k) (p := p) T.p rfl)
      (h₁₂ := pullback.snd p (gen O k)) (v₁₁ := pullback.fst (T.p ≫ p) (gen O k))
      (v₁₂ := pullback.fst p (gen O k)) (h₂₁ := T.p) (h₂₂ := p)
      (by rw [bcMap_snd]; exact sZ) (bcMap_fst _ _ _) sY
    exact h.flip
  show FEt (bcMap (gen O k) (p := p) T.p rfl) T.d
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsFinite) hsq T.fin
  · have hr : Set.range (pullback.fst p (gen O k)) ⊆ Set.range (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rw [Scheme.Opens.range_ι]
      exact range_subset_basicOpen l hl _ (pullback.snd p (gen O k))
    let φ := IsOpenImmersion.lift (Y.basicOpen (l : Γ(Y, ⊤))).ι (pullback.fst p (gen O k)) hr
    have hφ : φ ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι = pullback.fst p (gen O k) :=
      IsOpenImmersion.lift_fac _ _ _
    have t := (isPullback_morphismRestrict T.p (Y.basicOpen (l : Γ(Y, ⊤)))).flip
    have w : pullback.fst (T.p ≫ p) (gen O k) ≫ T.p =
        (bcMap (gen O k) (p := p) T.p rfl ≫ φ) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rw [Category.assoc, hφ]
      exact hsq.w
    have sq2 : IsPullback (t.lift _ _ w) (bcMap (gen O k) (p := p) T.p rfl)
        (T.p ∣_ Y.basicOpen (l : Γ(Y, ⊤))) φ := by
      refine IsPullback.of_right (h₁₂ := (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι)
        (h₂₂ := (Y.basicOpen (l : Γ(Y, ⊤))).ι) (v₁₃ := T.p) ?_ (t.lift_snd _ _ w) t
      rw [t.lift_fst, hφ]
      exact hsq
    exact MorphismProperty.of_isPullback (P := @Etale) sq2 T.et
  · intro K _ _ x
    have hlK : (l : K) ≠ 0 := by
      intro h
      apply hl
      apply (Spec.preimage (x ≫ pullback.snd p (gen O k))).hom.injective
      rw [map_natCast, map_zero]
      exact h
    rw [← T.deg K hlK (x ≫ pullback.fst p (gen O k))]
    exact Nat.card_congr
      { toFun := fun y => ⟨y.1 ≫ pullback.fst (T.p ≫ p) (gen O k), by
          rw [Category.assoc, hsq.w, ← Category.assoc, y.2]⟩
        invFun := fun z => ⟨hsq.lift z.1 x z.2, hsq.lift_snd _ _ _⟩
        left_inv := fun y => Subtype.ext (hsq.hom_ext (hsq.lift_fst _ _ _)
          (by rw [hsq.lift_snd]; exact y.2.symm))
        right_inv := fun z => Subtype.ext (hsq.lift_fst _ _ _) }

end UpperTheory.Gal.crystallineComparison.Br
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen)

namespace UpperTheory.Gal.crystallineComparison.Br

private theorem splitsBasic : SplitsBasic := pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits

private theorem bcSplits : BcSplits := pBcSplits splitsBasic

private theorem fEtBasic : FEtBasic := pFEtBasic pPtsOfSplits

private theorem etnGood : EtnGood := pEtnGood fEtBasic pEtTr

private theorem etGood : EtGood := pEtGood etnGood

private theorem bcGood : BcGood.{1} := pBcGood bcSplits (pBcGal bcSplits)

private theorem galClosD : GalClosD := pGalClosD (pSplitsPts pIsoPts) (pOrdEx pOrdStep)

private theorem hopSpec : HopSpec :=
  pHopSpec etGood bcGood (pGalClos galClosD) (pOpEx pOpTr) pOpTr pOpEt (pOpBc bcSplits (pBcGal bcSplits)) bcSplits

private theorem liesOp : LiesOp.{1} :=
  pLiesOp pLiesGen (pLiesAbs fEtBasic (pTrBase fEtBasic splitsBasic galClosD)
    (pTrPushM fEtBasic splitsBasic (pSplitsComp (pSplitsPts pIsoPts) pPtsOfSplits)
      (pMultiSplit fEtBasic splitsBasic galClosD) (pFEtInj galClosD)))

private theorem l_unit (l : ℕ) [Fact l.Prime] : IsUnit (l : Γ(G3.sp (PadicAlgCl l), ⊤)) := by
  have h : IsUnit (l : PadicAlgCl l) := (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero).isUnit
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl l))).inv.hom

private theorem l_ne (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : (l : K) ≠ 0 := by
  intro h
  have h2 := congrArg (algebraMap K (PadicAlgCl l)) h
  rw [map_natCast, map_zero] at h2
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2

private theorem lmap_pull {l : ℕ} [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E')
    (tr : ∀ n : ℤ, HQ l E n 0 →ₗ[ℚ_[l]] HQ l E'' n 0) (j : ℤ) (v : HQ l E' j 0) :
    DirectSum.lmap tr (pullTot l f (DirectSum.lof ℚ_[l] ℤ (fun n : ℤ => HQ l E' n 0) j v)) =
      DirectSum.lof ℚ_[l] ℤ (fun n : ℤ => HQ l E'' n 0) j (tr j (pullHQ l f j 0 v)) := by
  unfold pullTot
  rw [DirectSum.lmap_lof, DirectSum.lmap_lof]

theorem heckeCl : HeckeCl := by
  intro l _ K L _ H θ C T hr γ m d hfet hlies
  have hl := l_ne l K
  have hu := l_unit l
  have hgood : (etG l K (PadicAlgCl l)).Good := bcGood _ _ (etGood l _ hu)
  have hs := genFEt l (OK l K) K hl C.p T
  obtain ⟨hsF, hsE, -⟩ := id hs
  obtain ⟨hcF, hcE, -⟩ := bcSplits (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
    (pullback.snd C.p (gen (OK l K) K)) (pullback.snd (T.p ≫ C.p) (gen (OK l K) K))
    (pullback.snd C.p (gen (OK l K) K)) (G3.bcMap (gen (OK l K) K) T.p rfl)
    (bcMap_snd _ _ _) (𝟙 _) (Category.id_comp _) PEmpty (fun j ↦ j.elim) (fun j ↦ j.elim)
  have htrn : ∀ n : ℤ, ∃ tr, (etn l (G3.sp (PadicAlgCl l)) n 0).IsTr
      (pullback.snd (pullback.snd C.p (gen (OK l K) K))
        (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l)))))
      (pullback.snd (pullback.snd (T.p ≫ C.p) (gen (OK l K) K))
        (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l)))))
      (G3.bcMap (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
        (G3.bcMap (gen (OK l K) K) T.p rfl) (bcMap_snd _ _ _)) tr :=
    fun n ↦ (etnGood l _ hu n 0).tr _ _ _ (bcMap_snd _ _ _)
  choose trn htrn using htrn
  have htot := trTot l _ _ _ trn htrn
  have hbc := trBc (et l (G3.sp (PadicAlgCl l)))
    (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
    (pullback.snd C.p (gen (OK l K) K)) (pullback.snd (T.p ≫ C.p) (gen (OK l K) K))
    (G3.bcMap (gen (OK l K) K) T.p rfl) (bcMap_snd _ _ _) (DirectSum.lmap trn) htot
  have hF := hfet.1
  have hE := hfet.2.1
  obtain ⟨trg, htrg⟩ := hgood.tr H.q (H.s γ ≫ H.q) (H.s γ) rfl
  have hop_eq := (hopSpec l hl H (PadicAlgCl l) γ d hfet).2 trg htrg
  have hp : ∀ j : ℕ, LateralTheory.EtaleTrace.IsPush l
      (G3.bcMap (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
        (G3.bcMap (gen (OK l K) K) T.p rfl) (bcMap_snd _ _ _)) j (trn j) :=
    fun j ↦ trPush l _ _ _ (bcMap_snd _ _ _) j (trn j) (htrn j)
  have hc : corrP (mdl C) T = G3.bcMap (Spec.map (CommRingCat.ofHom (algebraMap K (PadicAlgCl l))))
      (G3.bcMap (gen (OK l K) K) T.p rfl) (bcMap_snd _ _ _) := by
    unfold corrP GlobalTheory.Et.geomMap Model.genMap
    rfl
  have hp2 : ∀ j : ℕ, LateralTheory.EtaleTrace.IsPush l (corrP (mdl C) T) j (trn j) := by
    intro j
    rw [hc]
    exact hp j
  have hk := fun j : ℕ ↦ hkOfPush l K (mdl C) T hr j _ (hp2 j)
  refine ⟨_, fun j ↦ ⟨hk j, fun v ↦ ?_⟩⟩
  have key := liesOp C γ T.p T.r hr m T.d hlies hs (etG l K (PadicAlgCl l)) hgood
    (DirectSum.lmap trn) trg hbc htrg
    (DirectSum.lof ℚ_[l] ℤ (fun n : ℤ ↦ HQ l (mdl C).spc n 0) j v)
  rw [hop_eq, LinearMap.comp_apply]
  refine key.trans ?_
  congr 2
  exact lmap_pull _ trn j v

end UpperTheory.Gal.crystallineComparison.Br
