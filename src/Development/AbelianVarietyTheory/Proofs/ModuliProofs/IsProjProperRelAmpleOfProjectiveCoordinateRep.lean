module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Amp
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjSpace TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

variable {Z : Scheme.{0}} {T : Type} [CommRing T]

def ev (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(Z, U) ⟶ CommRingCat.of T :=
  x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom

theorem inv_ev (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom ((ev x U h).hom a) = (x.appLE U ⊤ h).hom a := by
  have : ev x U h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).inv = x.appLE U ⊤ h := by
    rw [ev, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg (fun q => q.hom a) this

theorem comp_str {R : Type} [CommRing R] (s : Z ⟶ Sp R) (x : Sp T ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    x ≫ s = spMap (baseRingHom s U ≫ ev x U h).hom := by
  refine eq_of_baseRingHom_top ?_
  rw [← baseRingHom_appLE s x U ⊤ h, baseRingHom_top, spMap, CommRingCat.ofHom_hom,
    ← Scheme.ΓSpecIso_inv_naturality, ev]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem comp_toSpecΓ (U : Z.Opens) (y : Sp T ⟶ U.toScheme) (h : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U) :
    y ≫ U.toSpecΓ = Spec.map (ev (y ≫ U.ι) U h) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ev, Spec.map_comp,
    ← Spec.map_comp (U.topIso.inv)]
  congr 2
  rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl

theorem eq_zero_of_ev {U : Z.Opens} (a : Γ(Z, U))
    (H : ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z) (h : ⊤ ≤ x ⁻¹ᵁ U), (ev x U h).hom a = 0) : a = 0 := by
  refine ext_germ fun z hz => ?_
  have ht : ⊤ ≤ Z.fromSpecStalk z ⁻¹ᵁ U := fun p _ => by
    have : Z.fromSpecStalk z p ∈ Set.range (Z.fromSpecStalk z) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hz
  have e : ev (T := Z.presheaf.stalk z) (Z.fromSpecStalk z) U ht = Z.presheaf.germ U z hz := by
    change (Z.fromSpecStalk z).appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (Z.presheaf.stalk z)).hom = _
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hz]
    simp only [Category.assoc]
    have e : (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE (le_top : Z.fromSpecStalk z ⁻¹ᵁ U ≤ ⊤)).op ≫
        (Spec (Z.presheaf.stalk z)).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  rw [map_zero, ← e]
  exact H _ _ ht

variable {M : LB Z} {σ : Type} {th : σ → M.Sec}

theorem secCoord_ratio (x : Sp T ⟶ Z) (i : σ) (h : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (th i)) :
    SecCoord M th x fun j => (ev x _ h).hom (secRatio (th i) (th j)) := by
  have hu : ∀ k, IsUnit ((secPull (th i) x).f k) := fun k => by
    have := isUnit_resG_sec (secPull (th i) x) k
      (le_top.trans (h.trans (nonzeroLocus_secPull (th i) x).ge)) le_rfl
    rwa [resG_self] at this
  refine ⟨⟨fun k => (hu k).unit⟩, fun k l => Units.ext ((secPull (th i) x).compat k l), fun j k e => ?_⟩
  have e' : (M.pull x).U k ≤ x ⁻¹ᵁ (nonzeroLocus (th i) ⊓ M.U (k ⟨⟩)) := le_inf (le_top.trans h) e
  have := congrArg (x.appLE _ _ e').hom (secRatio_spec (th i) (th j) (k ⟨⟩))
  rw [map_mul, appLE_resG, appLE_resG, appLE_resG] at this
  rw [inv_ev, resG_appLE]
  exact this

theorem secCoord_chart (hM : M.IsLB) (x : Sp T ⟶ Z) (k : M.ι) (h : ⊤ ≤ x ⁻¹ᵁ M.U k) :
    SecCoord M th x fun j => (ev x _ h).hom ((th j).f k) := by
  have hle : ∀ l : PUnit → M.ι, (M.pull x).U l ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U k) := fun l =>
    le_inf (pull_U M x l).le (le_top.trans h)
  refine ⟨⟨fun l => Units.map (x.appLE _ _ (hle l)).hom.toMonoidHom (M.g (l ⟨⟩) k)⟩,
    (RepBC.isGen_val _).2 fun l l' => ?_, fun j l e => ?_⟩
  · have e' : (M.pull x).U l ⊓ (M.pull x).U l' ≤ x ⁻¹ᵁ (M.U (l ⟨⟩) ⊓ M.U (l' ⟨⟩) ⊓ M.U k) :=
      le_inf (RepBC.pull_inf_le M x l l') (le_top.trans h)
    have := congrArg (fun u => (x.appLE _ _ e').hom (Units.val u)) (hM.cocycle (l ⟨⟩) (l' ⟨⟩) k)
    simp only [Units.val_mul, val_res, map_mul] at this
    rw [appLE_resG, appLE_resG, appLE_resG] at this
    rw [RepBC.pull_g M x l l' (RepBC.pull_inf_le M x l l')]
    exact (resG_appLE x (hle l) _ _).trans (this.symm.trans (congrArg _ (resG_appLE x (hle l') _ _).symm))
  · have := congrArg (x.appLE _ _ (hle l)).hom ((th j).compat (l ⟨⟩) k)
    rw [map_mul] at this
    erw [appLE_resG, appLE_resG] at this
    rw [inv_ev, resG_appLE, mul_comm]
    exact this

theorem mem_locus (hM : M.IsLB) {x : Sp T ⟶ Z} {v : σ → T} (h : SecCoord M th x v) {i : σ} {p : Sp T}
    (hp : v i ∉ p.asIdeal) : x p ∈ nonzeroLocus (th i) := by
  obtain ⟨τ, -, h⟩ := h
  obtain ⟨k, hk⟩ := exists_chart hM (x p)
  have e := congrArg (Sp T).basicOpen (h i (fun _ => k) (pull_U M x _).le)
  rw [Scheme.basicOpen_appLE, Scheme.basicOpen_mul, Scheme.basicOpen_res,
    (Sp T).basicOpen_of_isUnit (Units.isUnit _)] at e
  have hp' : p ∈ (M.pull x).U fun _ => k := (pull_U M x fun _ => k).ge hk
  have h2 : p ∈ (Sp T).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i)) :=
    (basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).ge hp
  exact Opens.mem_iSup.2 ⟨k, (e.ge ⟨⟨hp', h2⟩, hp'⟩).2⟩

variable {R : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {s : Z ⟶ Sp R}

theorem iSup_locus (H : ProjRep I s M th) : ⨆ i, nonzeroLocus (th i) = ⊤ := by
  refine top_le_iff.1 fun z _ => ?_
  obtain ⟨k, hk⟩ := exists_chart H.1 z
  have ht : ⊤ ≤ Z.fromSpecResidueField z ⁻¹ᵁ M.U k := fun p _ => by
    change Z.fromSpecResidueField z p ∈ M.U k
    rwa [Scheme.fromSpecResidueField_apply]
  have hc := secCoord_chart (th := th) (T := Z.residueField z) H.1 (Z.fromSpecResidueField z) k ht
  have hs := (H.2.1 _ _ _ _ (comp_str s _ _ ht) hc).1
  let p : Sp (Z.residueField z) := IsLocalRing.closedPoint (Z.residueField z)
  by_contra hz
  refine p.isPrime.ne_top (top_le_iff.1 (hs.ge.trans (Ideal.span_le.2 ?_)))
  rintro _ ⟨i, rfl⟩
  by_contra hi
  have := mem_locus H.1 hc hi
  erw [Scheme.fromSpecResidueField_apply] at this
  exact hz (Opens.mem_iSup.2 ⟨i, this⟩)

theorem chart_affine (H : ProjRep I s M th) (i : σ) : IsAffineOpen (nonzeroLocus (th i)) ∧ Function.Surjective
    (MvPolynomial.eval₂Hom (baseRingHom s (nonzeroLocus (th i))).hom fun j => secRatio (th i) (th j)) := by
  set D := nonzeroLocus (th i) with hD
  let c : MvPolynomial σ R →+* Γ(Z, D) :=
    MvPolynomial.eval₂Hom (baseRingHom s D).hom fun j => secRatio (th i) (th j)
  let J : Ideal (MvPolynomial σ R) := I ⊔ Ideal.span {MvPolynomial.X i - 1}
  have hJ : ∀ F ∈ J, c F = 0 := by
    change J ≤ RingHom.ker c
    refine sup_le (fun F hF => eq_zero_of_ev _ fun T _ x h => ?_) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    · have := (H.2.1 _ _ _ _ (comp_str s x D h) (secCoord_ratio x i h)).2 F hF
      exact (MvPolynomial.eval₂_comp_left (ev x D h).hom _ _ F).trans this
    · simp [c, RingHom.mem_ker]
  let ρ : CommRingCat.of (MvPolynomial σ R ⧸ J) ⟶ Γ(Z, D) := CommRingCat.ofHom (Ideal.Quotient.lift J c hJ)
  have hXi : Ideal.Quotient.mk J (MvPolynomial.X i) = 1 :=
    Ideal.Quotient.eq.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨φ, ⟨hφ, hv⟩, -⟩ := H.2.2 _ ((Ideal.Quotient.mk J).comp MvPolynomial.C)
    (fun j => Ideal.Quotient.mk J (MvPolynomial.X j))
    ((Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨i, hXi⟩)) fun F hF => by
      have := MvPolynomial.eval₂_comp_left (Ideal.Quotient.mk J) MvPolynomial.C MvPolynomial.X F
      rw [MvPolynomial.eval₂_eta] at this
      exact this.symm.trans (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left hF))
  have hφD : ⊤ ≤ φ ⁻¹ᵁ D := fun p _ => mem_locus H.1 hv (by
    rw [hXi]; exact (Ideal.ne_top_iff_one _).1 p.isPrime.ne_top)
  let φ' : Sp (MvPolynomial σ R ⧸ J) ⟶ D.toScheme := IsOpenImmersion.lift D.ι φ (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hφD trivial)
  have hφ' : φ' ≫ D.ι = φ := IsOpenImmersion.lift_fac _ _ _
  have hin : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme), ⊤ ≤ (y ≫ D.ι) ⁻¹ᵁ D := fun T _ y p _ => (y p).2
  have e₁ : φ' ≫ D.toSpecΓ ≫ Spec.map ρ = 𝟙 _ := by
    rw [← Category.assoc, comp_toSpecΓ D φ' (hin _ φ'), ← Spec.map_comp, ← Spec.map_id]
    congr 1
    have hc := secCoord_ratio (φ' ≫ D.ι) i (hin _ φ')
    have hs := comp_str s (φ' ≫ D.ι) D (hin _ φ')
    generalize hin _ φ' = w at hc hs ⊢
    rw [hφ'] at w
    simp only [hφ'] at hc hs ⊢
    obtain ⟨u, hu⟩ := Coord.unique H.1 hv hc
    have hu1 : (u : MvPolynomial σ R ⧸ J) = 1 := by
      have := hu i
      rw [secRatio_self, map_one, hXi, _root_.mul_one] at this
      exact this.symm
    have hb := congrArg CommRingCat.Hom.hom (Spec.map_injective (hs.symm.trans hφ))
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun j => ?_))
    · exact (congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_C _ _ a)).trans (DFunLike.congr_fun hb a)
    · exact (congrArg (ev φ D _).hom (MvPolynomial.eval₂Hom_X' _ _ j)).trans
        ((hu j).trans (by rw [hu1, _root_.one_mul]; rfl))
  have e₂ : (D.toSpecΓ ≫ Spec.map ρ) ≫ φ' = 𝟙 _ := by
    rw [← cancel_mono D.ι, Category.assoc, hφ', Category.id_comp]
    refine D.toScheme.affineCover.hom_ext _ _ fun a => ?_
    have key : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ D.toScheme),
        y ≫ (D.toSpecΓ ≫ Spec.map ρ) ≫ φ = y ≫ D.ι := fun T _ y => by
      have hc := secCoord_ratio (y ≫ D.ι) i (hin _ y)
      have hs := comp_str s (y ≫ D.ι) D (hin _ y)
      obtain ⟨h₁, h₂⟩ := H.2.1 _ _ _ _ hs hc
      refine (H.2.2 _ _ _ h₁ h₂).unique ?_ ⟨hs, hc⟩
      rw [← Category.assoc, ← Category.assoc, comp_toSpecΓ D y (hin _ y), ← Spec.map_comp]
      constructor
      · rw [Category.assoc, hφ, ← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
        exact congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_C _ _ a)
      · have e : (fun j => (ev (y ≫ D.ι) D (hin _ y)).hom (secRatio (th i) (th j))) = fun j =>
            (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom (Ideal.Quotient.mk J (MvPolynomial.X j)) := funext fun j =>
          congrArg (ev (y ≫ D.ι) D (hin _ y)).hom (MvPolynomial.eval₂Hom_X' (baseRingHom s D).hom (fun j => secRatio (th i) (th j)) j).symm
        exact e ▸ Coord.baseChange hv (ρ ≫ ev (y ≫ D.ι) D (hin _ y)).hom
    exact key _ (D.toScheme.affineCover.f a)
  have hiso : IsIso (D.toSpecΓ ≫ Spec.map ρ) := ⟨φ', e₂, e₁⟩
  have ha : IsAffine D.toScheme := .of_isIso (D.toSpecΓ ≫ Spec.map ρ)
  have ha' : IsAffineOpen D := ha
  refine ⟨ha', ?_⟩
  have h1 : IsIso D.toSpecΓ := inferInstanceAs (IsIso ha'.isoSpec.hom)
  have h2 : IsIso (Spec.map ρ) := IsIso.of_isIso_comp_left D.toSpecΓ _
  exact (isIso_SpecMap_iff.1 h2).2.comp Ideal.Quotient.mk_surjective

end GlobalTheory.ZM.Amp

namespace GlobalTheory.ZM
open GlobalTheory.ProjSpace Amp
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem projRep_projective_ample : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → IsProjOver Z.hom ∧ IsProper Z.hom ∧ Out.RelAmple Z M := by
  intro R σ _ _ I Z M th H
  have hp : IsProjOver Z.hom := by
    cases isEmpty_or_nonempty σ with
    | inl h => exact isProjOver_of_disjoint_cover Z.hom _ (iSup_locus H) (fun i => isEmptyElim i) fun i => isEmptyElim i
    | inr h =>
      obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
      obtain _ | m := n
      · exact (h.elim fun i => (e i).elim0)
      have hs : ⨆ i, nonzeroLocus (th (e.symm i)) = ⊤ :=
        (e.symm.iSup_comp (g := fun i => nonzeroLocus (th i))).trans (iSup_locus H)
      refine ⟨m, toProj Z.hom (fun i => th (e.symm i)) hs, (isClosedImmersion_toProj_iff _ _ hs).2 fun i =>
        ⟨(chart_affine H _).1, fun a => by
          obtain ⟨F, hF⟩ := (chart_affine H (e.symm i)).2 a
          refine ⟨MvPolynomial.rename e F, ?_⟩
          simpa only [MvPolynomial.eval₂Hom_rename, Function.comp_def, Equiv.symm_apply_apply] using hF⟩, toProj_str _ _ _⟩
  have hpr : IsProper Z.hom := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  refine ⟨hp, hpr, (relAmple_iff_isAmpleLB_of_isAffine Z H.1).2 ?_⟩
  have e : ∀ i, nonzeroLocus (secToPow (th i) 1) = nonzeroLocus (th i) := fun i =>
    nonzeroLocus_secToPow (th i) le_rfl
  exact isAmpleLB_of_cover H.1 le_rfl (fun i => secToPow (th i) 1) ((iSup_congr e).trans (iSup_locus H))
    fun i => (e i).symm ▸ (chart_affine H i).1

end GlobalTheory.ZM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRepStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z : Over (Sp R)) (M : LB Z.left) (th : σ → M.Sec), ProjRep I Z.hom M th → IsProjOver Z.hom ∧ IsProper Z.hom ∧ Out.RelAmple Z M := by
  first | exact @GlobalTheory.ZM.projRep_projective_ample | exact GlobalTheory.ZM.projRep_projective_ample | (intros; apply GlobalTheory.ZM.projRep_projective_ample <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreOrbit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.levelMap_fibre_orbit : Out.Laws → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing
    B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s'
    : S' ⟶ Sp B') (f
    : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap
    o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l
    : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b'
    : Base l B') (b'' : Base l B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s''
    : S'' ⟶ Sp B'') (o : Obj D l b s) (o' : Obj D l b' s') (o''
    : Obj D l b'' s''), (∃ m : ObjMap o o (𝟙 S), m.toSABMap.φ = 𝟙 _) ∧ ∀ (f : S' ⟶ S) (f'
    : S'' ⟶ S') (m : ObjMap o' o f), (∀ m' : ObjMap o'' o' f', ∃ m'' : ObjMap o'' o (f' ≫
    f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ) ∧ (∀ m'' : ObjMap o'' o (f' ≫
    f), ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B
    : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p
    + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B
    : Type) [CommRing B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o₂
    : Obj D l₂ b₂ s), l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (o : Obj D l b s) (m
    : SABMap o₂.t o.t (𝟙 S)), (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = 𝟙 S ≫ (o.eta
    a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = 𝟙 S ≫ (o.etaA a).left)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B'
    : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s
    : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S'
    ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta
    a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (B
    : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o
    : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (k : Type) [Field
    k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e
    : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : TateIso D k Q act e, ∃ g : Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f
    n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n
    : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n
    : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f
    n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA
    a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo
    : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK
    : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l)
    : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M /
    l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A /
    l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc
    : c.F = c₂.F) (rF
    : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion
    hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y'
    : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ
    : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g
    : Sim D) (ρ
    : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂ :=
  GlobalTheory.LevelFibre.levelMap_fibre_simply_transitive_of_laws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsOfParts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem levelMaps_of_parts : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∃ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ g : Sim D, g.InGam l l₂ → ∃ ρ : Xo₂.X ≅ Xo₂.X, Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Xo₂.XF c₂), y ≫ rF = y' ≫ rF → (∃ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ ∧ Xo₂.LevAut g ρ ∧ ρ.hom ≫ r = r ∧ y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧ ∀ (g : Sim D) (ρ : Xo₂.X ≅ Xo₂.X), g.InGam l l₂ → Xo₂.LevAut g ρ → y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt l₂) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) := by
  intro h₁ h₂ h₃ h₄ E _ _ _ H D hpq l l₂ Xo Xo₂ hd
  obtain ⟨r, jK, m, hh⟩ := h₁ E H D l l₂ Xo Xo₂ hpq hd
  refine ⟨r, jK, m, hh.1, hh.2.1, hh.2.2.1, hh.2.2.2, h₂ E H D l l₂ Xo Xo₂ hpq hd r jK m hh, ?_⟩
  intro c c₂ hc
  have hring : (IntermediateField.inclusion c₂.le).toRingHom.comp jK =
      (IntermediateField.inclusion hc.le).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom := by
    ext x
    exact hh.1 x
  have w : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫
        spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hh.2.1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  have e₁ := pullback.lift_fst _ _ w
  have e₂ := pullback.lift_snd _ _ w
  have k₃ := h₃ E H D l l₂ Xo Xo₂ hpq hd r jK m hh c c₂ hc _ e₁ e₂
  exact ⟨pullback.lift _ _ w, e₁, e₂, k₃.1, k₃.2.1, k₃.2.2,
    h₄ E H D l l₂ Xo Xo₂ hpq hd r jK m hh c c₂ hc _ e₁ e₂⟩

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem levelMaps_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) := by
  intro hL

  have hsm := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
  have hid := ObjMaps.id_comp_cancel
  have hlow := obj_lower_level
  have hrep := moduli_rep_of_base hid
  have hsim := SimAlg.sim_group
  have hact := Moduli.LevelAction.similitude_acts hsm hid hlow hrep
    (exists_obj_twist_by_similitude hsim) hsim
  exact levelMaps_of_parts (exists_levelMap hsm hid hlow hrep) hact
    (LevCover.levelMap_finite_etale_surjective_of_laws hL)
    (levelMap_fibre_orbit hL obj_pull hid obj_isAbelianScheme_dim_rigidified_sym hlow
      (obj_rigid_closed hL) hrep tateIso_differ_by_similitude hsim hact)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.RelAmpleQProj

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out TopologicalSpace

variable {Y : Scheme.{0}} {L M G : LB Y}

def secPwOne (σ : G.Sec) : (pw G 1).Sec where
  f := σ.f
  compat i j := by
    have h := σ.compat i j
    rw [← zpow_one (G.g i j)] at h
    exact h

theorem exists_sec_tw_locus [CompactSpace Y] [QuasiSeparatedSpace Y] (hM : M.IsLB) (hG : G.IsLB) (σ : G.Sec)
    (V : Y.Opens) (hV : V = nonzeroLocus σ) (r : (M.pull V.ι).Sec) :
    ∃ (k : ℕ) (u : (tw M G (k : ℤ)).Sec), V.ι ⁻¹ᵁ nonzeroLocus u = nonzeroLocus r := by
  obtain ⟨s, ⟨hs, hr⟩, -⟩ := existsUnique_secOn_of_pull M V r
  obtain ⟨k, H⟩ := exists_tw_extend_pow_mul Y G M 1 (secPwOne σ) V 0 hG hM hV inferInstance inferInstance
    (SecOn.twZeroEquiv hM hG V (GlobalTheory.LB.mkSec s hs))
  rw [show (0 : ℤ) + k * 1 = k by ring] at H
  obtain ⟨a, ha⟩ := H
  let w : (tw M G (k : ℤ)).Sec := ⟨fun i => resG Y (le_inf le_top le_rfl) (GlobalTheory.LB.coord a i), fun i j => by
    change resG Y _ (resG Y _ _) = _ * resG Y _ (resG Y _ _)
    rw [resG_resG, resG_resG, GlobalTheory.LB.coord_rel a i j (le_inf le_top inf_le_left) (le_inf le_top inf_le_right) le_rfl, rs_self]⟩
  refine ⟨k, w, ?_⟩
  ext z
  obtain ⟨p, hp⟩ := exists_chart hM (V.ι z)
  obtain ⟨l, hl⟩ := exists_chart hG (V.ι z)
  have hzV : V.ι z ∈ V := z.2
  have hz : V.ι z ∈ V ⊓ (M.U p ⊓ G.U l) := ⟨hzV, hp, hl⟩
  have hz' : V.ι z ∈ M.U p ⊓ G.U l := ⟨hp, hl⟩
  have hzp : z ∈ (M.pull V.ι).U (fun _ => p) := mem_pull.2 hp
  have e := congrArg (gs V.ι z _) (ha p l)
  rw [SecOn.twCoord_twZeroEquiv, gs_res _ z _ hz, gs_mul _ z _ hz, gs_pow _ z _ hz, gs_res _ z _ hz] at e
  have e₁ : gs V.ι z _ ((w).f (p, l)) = gs V.ι z _ (SecOn.twCoord a p l) :=
    gs_res V.ι z _ hz' _
  have e₂ : gs (𝟙 _) z _ (r.f fun _ => p) = gs V.ι z _ (s p) := by
    rw [← hr, gs_appLE V.ι _ _ _ (𝟙 _) z hzp, Category.id_comp]
  have hσ : IsUnit (gs V.ι z (V ⊓ (M.U p ⊓ G.U l)) (rs Y (inf_le_right.trans inf_le_right) (σ.f l))) := by
    rw [gs_res _ z _ hz]
    exact (mem_nonzeroLocus_iff_pull σ V.ι z hl).1 (hV.le hzV)
  refine (mem_nonzeroLocus_iff_pull (w) V.ι z (k := (p, l)) hz').trans
    (Iff.trans ?_ (mem_nonzeroLocus_iff_isUnit r hzp).symm)
  rw [e₂]
  refine (iff_of_eq (congrArg IsUnit (e₁.trans e))).trans ?_
  rw [IsUnit.mul_iff]
  exact and_iff_right (hσ.pow k)

theorem exists_sec_pow_tw {m k c e : ℕ} (he : 1 ≤ e) (h : c * m = k + e) (u : (tw (lbPow L m) G (k : ℤ)).Sec)
    (σ : G.Sec) : ∃ w : (lbPow (tw L G (c : ℤ)) m).Sec, nonzeroLocus w = nonzeroLocus u ⊓ nonzeroLocus σ := by
  have le : ∀ J : PUnit → L.ι × G.ι, powChart (tw L G (c : ℤ)) J ≤
      powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2 := fun J y hy =>
    ⟨mem_powChart.2 (mem_powChart.1 hy).1, (mem_powChart.1 hy).2⟩
  let F : ∀ J : PUnit → L.ι × G.ι, Γ(Y, powChart (tw L G (c : ℤ)) J) := fun J =>
    resG Y (le J) (show Γ(Y, powChart L (fun _ => (J PUnit.unit).1) ⊓ G.U (J PUnit.unit).2) from
      u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
      resG Y ((le J).trans inf_le_right) (σ.f (J PUnit.unit).2) ^ e
  have hF : ∀ (y : Y) (J : PUnit → L.ι × G.ι), y ∈ powChart (tw L G (c : ℤ)) J → gs (𝟙 Y) y _ (F J) =
      gs (𝟙 Y) y _ (u.f (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)) *
        gs (𝟙 Y) y _ (σ.f (J PUnit.unit).2) ^ e := fun y J hy => by
    rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy]
    rfl
  refine ⟨powSecOfGerm (L := tw L G (c : ℤ)) m F fun y J J' hJ hJ' => ?_, ?_⟩
  · have e₁ := gs_compat u (𝟙 Y) y (j := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
      (j' := (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2)) (le J hJ) (le J' hJ')
    have e₂ := TwistGen.gm_tw_g (lbPow L m) G k y (fun _ => (J PUnit.unit).1, (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, (J' PUnit.unit).2) (le J hJ) (le J' hJ')
    have e₃ := gm_lbPow_g (L := L) m (𝟙 Y) y (fun _ => (J PUnit.unit).1) (fun _ => (J' PUnit.unit).1)
      (le J hJ).1 (le J' hJ').1
    have e₄ := TwistGen.gm_tw_g L G c y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.1 hJ) (mem_powChart.1 hJ')
    have e₅ := gs_compat σ (𝟙 Y) y (le J hJ).2 (le J' hJ').2
    dsimp only at e₂
    rw [e₃] at e₂
    refine (hF y J hJ).trans (Eq.trans ?_ (congrArg₂ (fun a b => a ^ m * b) e₄ (hF y J' hJ')).symm)
    rw [e₅]
    refine (congrArg (· * _) (e₁.trans (congrArg (· * _) e₂))).trans ?_
    simp only [Units.val_pow_eq_pow_val]
    rw [mul_pow, mul_pow, ← pow_mul, h]
    ring
  · refine nonzeroLocus_pow_eq_of _ _ (fun y hy => ?_) fun y J hJ => ?_
    · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy.1
      exact ⟨fun _ => (p.1 PUnit.unit, p.2), mem_powChart.2 ⟨mem_powChart.1 hp.1, hp.2⟩⟩
    · refine (iff_of_eq (congrArg IsUnit (hF y J hJ))).trans ?_
      rw [IsUnit.mul_iff, isUnit_pow_iff (by omega)]
      exact and_congr (mem_nonzeroLocus_iff_isUnit u (k := (fun _ => (J PUnit.unit).1, (J PUnit.unit).2))
        (le J hJ)).symm (mem_nonzeroLocus_iff_isUnit σ (le J hJ).2).symm

theorem exists_isAmpleLB_tw [CompactSpace Y] [QuasiSeparatedSpace Y] (hL : L.IsLB) (hG : G.IsLB)
    (h : ∀ y : Y, ∃ (σ : G.Sec) (V : Y.Opens), V = nonzeroLocus σ ∧ y ∈ V ∧ IsAmpleLB (L.pull V.ι)) :
    ∃ c : ℕ, IsAmpleLB (tw L G (c : ℤ)) := by
  have loc : ∀ y : Y, ∃ (m k : ℕ) (u : (tw (lbPow L m) G (k : ℤ)).Sec) (σ : G.Sec), 1 ≤ m ∧
      y ∈ nonzeroLocus u ⊓ nonzeroLocus σ ∧ IsAffineOpen (nonzeroLocus u ⊓ nonzeroLocus σ) := fun y => by
    obtain ⟨σ, V, hV, hy, hA⟩ := h y
    obtain ⟨m, hm, τ, hτ, ha⟩ := hA.exists_affine ⟨y, hy⟩
    obtain ⟨r, hr⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL m) V.ι)
      (isLB_lbPow hA.isLB m) (lbIso_lbPow_pull hL V.ι m).symm τ
    obtain ⟨k, u, hu⟩ := exists_sec_tw_locus (isLB_lbPow hL m) hG σ V hV r
    have e := hu.trans hr
    refine ⟨m, k, u, σ, hm, ⟨e.ge hτ, hV.le hy⟩, ?_⟩
    have h₁ := ha.image_of_isOpenImmersion V.ι
    rwa [← e, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm, hV] at h₁
  choose m k u σ hm hy ha using loc
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top (fun y => nonzeroLocus (u y) ⊓ nonzeroLocus (σ y)) hy
  refine ⟨T.sup k + 1, isLB_tw hL hG _, inferInstance, fun x => ?_⟩
  obtain ⟨y, hx⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ x))
  have h₁ : k y ≤ T.sup k := Finset.le_sup y.2
  have h₂ : T.sup k + 1 ≤ (T.sup k + 1) * m y := Nat.le_mul_of_pos_right _ (hm y)
  obtain ⟨w, hw⟩ := exists_sec_pow_tw (c := T.sup k + 1) (e := (T.sup k + 1) * m y - k y) (by omega) (by omega)
    (u y) (σ y)
  exact ⟨m y, hm y, w, hw.ge hx, hw ▸ ha y⟩

theorem isProper_morphismRestrict {S : Scheme.{0}} (A : Over S) {B : LB A.left} (h : RelAmple A B) {U : S.Opens}
    (hU : IsAffineOpen U) : IsProper (A.hom ∣_ U) := by
  obtain ⟨N, -, K, s, H⟩ := h U hU
  have h₁ := isProper_of_veryAmpleBy
    ((ProjSpace.veryAmpleBy_comp_iff (R := Γ(S, U)) (A.hom ∣_ U) hU.isoSpec.hom s).2 H)
  exact (MorphismProperty.cancel_right_of_respectsIso @IsProper _ _).1 h₁

theorem isProper_and_exists_isAmpleLB {S : Scheme.{0}} (A : Over S) {B : LB A.left} (hB : B.IsLB)
    (h : RelAmple A B) {H : LB S} (hH : IsAmpleLB H) : IsProper A.hom ∧ ∃ N : LB A.left, IsAmpleLB N := by
  obtain ⟨n, -, c, s, hs, ha⟩ := hH.exists_cover
  have hp : IsProper A.hom := IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) _ hs
    fun i => isProper_morphismRestrict A h (ha i)
  have := hH.compactSpace
  have := hH.quasiSeparatedSpace
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  obtain ⟨d, hd⟩ := exists_isAmpleLB_tw hB (LB.isLB_pull (isLB_lbPow hH.isLB n) A.hom) fun y => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ (A.hom y)))
    exact ⟨secPull (s i) A.hom, _, (nonzeroLocus_secPull _ _).symm, hi, isAmpleLB_of_relAmple A hB h _ (ha i)⟩
  exact ⟨hp, _, hd⟩

theorem isQProjOver_of_relAmple : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L → IsQProjOver (A.hom ≫ s) := by
  rintro K _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseTorsionAndEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.PrimePowerTorsion

theorem dense_torsion (hA : Out.AmpleSt) (hK : Out.KerPowSt) (hI : Out.IrredSt) (K : Type) [Field K] [IsAlgClosed K]
    (P : Out.PolAV (Sp K)) (l : ℕ) (hl : 2 ≤ l) (hlK : (l : K) ≠ 0) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) := by
  have := P.isAb.comm
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨a, -, s, hs, hle, -⟩ := (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).exists_affine_le
    (x := x) (U := ⟨U, hU⟩) hx
  have gen : ∀ N : ℕ, 4 ≤ N → ∀ y : P.A.left, ∃ t : (lbPow P.L N).Sec, y ∈ Out.nonzeroLocus t := fun N hN y => by
    obtain ⟨m, t, ht, -⟩ := veryAmple_lbPow hA K P N hN
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ y))
    exact ⟨t i, hi⟩
  obtain ⟨m, hm, ham⟩ : ∃ m : ℕ, 4 ≤ m ∧ a + m = l ^ (a + 4) := by
    have := Nat.lt_pow_self (n := a + 4) (show 1 < l by omega)
    exact ⟨l ^ (a + 4) - a, by omega, by omega⟩
  obtain ⟨t, ht⟩ := gen m hm x
  let p : (Out.baseOver (Sp K)).left := IsLocalRing.closedPoint K
  obtain ⟨t', ht'⟩ := gen (a + m) (by omega) ((1 : Out.baseOver (Sp K) ⟶ P.A).left p)
  have e := nonzeroLocus_secMul s t
  obtain ⟨b, hb, q, hq⟩ := TorsionDense.exists_mem_nonzeroLocus P hI hK (a + m) (by omega)
    (by rw [ham, Nat.cast_pow]; exact pow_ne_zero _ hlK)
    {x | ∃ j : ℕ, x ^ l ^ j = 1} (fun w hw b ⟨j, hb⟩ => ⟨a + 4 + j, by
      rw [mul_pow, pow_add, pow_mul w, ← ham, hw, one_pow, mul_comm _ (l ^ j), pow_mul, hb, one_pow,
        _root_.one_mul]⟩)
    (secMul s t) t' x (e.ge ⟨hs, ht⟩) 1 ⟨0, one_pow _⟩ p ht'
  exact ⟨b.left q, hle (e.le hq).1, Set.mem_iUnion₂.2 ⟨b, hb, q, rfl⟩⟩

theorem dense_torsion_and_eq_one :
    Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℕ), l.Prime → (l : K) ≠ 0 → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp K)) ⟶ P.A | ∃ j : ℕ, x ^ l ^ j = 1}, Set.range x.left) ∧ ∀ f : P.A ⟶ P.A, (∀ (j : ℕ) (x : 𝟙_ (Over (Sp K)) ⟶ P.A), x ^ l ^ j = 1 → x ≫ f = 1) → f = 1 := by
  intro h1 _ K _ _ P l hl hlK
  have hD := dense_torsion h1.ample h1.kerPow h1.irred K P l hl.two_le hlK
  refine ⟨hD, fun f hf => Over.OverMorphism.ext ?_⟩
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P.isAb.proper
  let g : P.A ⟶ P.A := 1
  suffices IsDominant (equalizer.ι f.left g.left) from
    ext_of_isDominant_of_isSeparated P.A.hom ((Over.w f).trans (Over.w g).symm) (equalizer.ι f.left g.left)
      (equalizer.condition _ _)
  refine ⟨Dense.mono (fun y hy => ?_) hD⟩
  obtain ⟨x, ⟨j, hx⟩, q, rfl⟩ := Set.mem_iUnion₂.1 hy
  have hxy : x.left ≫ f.left = x.left ≫ g.left :=
    congrArg CommaMorphism.left ((hf j x hx).trans (MonObj.comp_one x).symm)
  refine ⟨equalizer.lift x.left hxy q, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]

end GlobalTheory.PrimePowerTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevelMapField

private theorem KA_mono_of_A_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.A ∣ l.A) : KA l₀ ≤ KA l := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | rfl
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [GlobalTheory.LevelCover.zeta_dvd l.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _

private theorem M'_dvd_of_level_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.Dvd l) : l₀.M' ∣ l.M' := by
  unfold Level.Dvd at h
  unfold Level.M'
  exact Nat.lcm_dvd (h.1.trans (Nat.dvd_lcm_left _ _)) (h.2.2.trans (Nat.dvd_lcm_right _ _))

private theorem M'_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Level H) : 0 < l.M' := by
  unfold Level.M'
  have h3 := l.three_le
  exact Nat.lcm_pos (by omega) l.A_pos

theorem exists_levelMap : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (c : Coeff l) (o : Obj D l (baseKA l) (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)) (_ : ObjMap o (Xo l).univ (pullback.fst _ _)), l₀.Dvd l → ∃ (k : KA l₀ →+* c.F) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap o.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k), IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k ∧ LevComp o (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) := by
  intro _ _ _ E _ _ _ H D Xo hN l₀ l c o mo hd
  have hA : l₀.A ∣ l.A := by
    unfold Level.Dvd at hd
    exact hd.2.2
  have hle : KA l₀ ≤ c.F := (KA_mono_of_A_dvd hA).trans c.le
  have hz : zeta l₀.M' ∈ c.F := by
    rw [GlobalTheory.LevelCover.zeta_dvd (M'_pos' l) (M'_dvd_of_level_dvd hd)]
    exact pow_mem c.zeta_mem _
  obtain ⟨r₀, -, m, -, -, hm1, hm2, -, hF⟩ := hN l₀ l (Xo l₀) (Xo l) hd
  obtain ⟨rF, h1, h2, hfin, het, hsurj, -⟩ := hF ⟨c.F, c.fin, c.conj, hz, hle⟩ c rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c.F)).toRingHom = 𝟙 (Sp c.F) :=
    GlobalTheory.LevelCover.spMap_inclusion_self _
  have hr : (rF ≫ pullback.fst _ _) ≫ (Xo l₀).s =
      pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h2]
    erw [hid, Category.comp_id]
  have hlift : pullback.lift (rF ≫ pullback.fst _ _) (pullback.snd _ _) hr = rF := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd, h2]
      erw [hid, Category.comp_id]
  obtain ⟨ν, hν⟩ := GlobalTheory.LevelCover.sab_comp mo.toSABMap m (e := rF ≫ pullback.fst _ _) h1.symm
  refine ⟨(IntermediateField.inclusion hle).toRingHom, rF ≫ pullback.fst _ _, ν, hr,
    fun x => rfl, ?_, ?_, ?_, ?_⟩
  · unfold LevComp
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.eta a) ((Xo l).univ.eta a) (mo.eta a),
        Category.assoc, hm1 a, ← Category.assoc, ← h1]
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.etaA a) ((Xo l).univ.etaA a) (mo.etaA a),
        Category.assoc, hm2 a, ← Category.assoc, ← h1]
  · rw [hlift]; exact hfin
  · rw [hlift]; exact het
  · rw [hlift]; exact hsurj

end GlobalTheory.LevelMapField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelOfTheta

open GlobalTheory.CechPic

section Algebra

variable {G U : Type} [CommGroup G] [CommGroup U]

end Algebra

section Classes

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem pull_one (hL : L.IsLB) (hr : Out.Rigidified A L) (T : Over S) :
    pull (1 : T ⟶ A).left (cls L hL) = 0 := by
  have e : pull (eSec A) (cls L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 hr
  have e' : (1 : T ⟶ A).left = (toUnit T).left ≫ eSec A := rfl
  rw [e', pull_comp, e, map_zero]

omit [GrpObj A] in
theorem pull_pull {T T' : Over S} (f : T' ⟶ T) (a : T ⟶ A) (c : Pic A.left) :
    pull f.left (pull a.left c) = pull (f ≫ a).left c := (pull_comp _ _ _).symm

variable [IsCommMonObj A]

theorem isLB_lam (hL : L.IsLB) : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _

theorem cls_lam (hL : L.IsLB) :
    cls _ (isLB_lam hL) = pull (fst A A * snd A A).left (cls L hL) - pull (fst A A).left (cls L hL) -
      pull (snd A A).left (cls L hL) + pull (1 : A ⊗ A ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ (isLB_lam hL)).trans ?_
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum A (x2 A) I).left (cls L hL)) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have p₀ : psum A (x2 A) ∅ = 1 := rfl
  have p₁ : psum A (x2 A) {0} = fst A A := _root_.mul_one (fst A A)
  have p₂ : psum A (x2 A) {1} = snd A A := _root_.mul_one (snd A A)
  have p₃ : psum A (x2 A) {0, 1} = fst A A * snd A A := congrArg (fst A A * ·) (_root_.mul_one (snd A A))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem pull_lam (hL : L.IsLB) (hr : Out.Rigidified A L) {T : Over S} (a b : T ⟶ A) :
    pull (lift a b).left (cls _ (isLB_lam hL)) =
      pull (a * b).left (cls L hL) - pull a.left (cls L hL) - pull b.left (cls L hL) := by
  rw [cls_lam hL, pull_one hL hr, add_zero, map_sub, map_sub, pull_pull, pull_pull, pull_pull, MonObj.comp_mul,
    lift_fst, lift_snd]

end Classes

section Pairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L M : LB A.left}

theorem exists_theta_iff (hL : L.IsLB) (k : ℤ) {T : Over S} (x : T ⟶ A) :
    (∃ θ : Out.ThetaGrp A L k T, θ.pt = x) ↔
      k • pull (snd T A).left (cls L hL) - k • pull (Out.translPt A x).left (cls L hL) = 0 := by
  have e := cls_linComb hL (K := Fin 2) ![(snd T A).left, (Out.translPt A x).left] ![k, -k] (LB.isLB_linComb hL _ _)
  rw [Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, ← sub_eq_add_neg] at e
  rw [← e, cls_eq_zero_iff]
  exact ⟨fun ⟨θ, h⟩ => h ▸ ⟨θ.φ, θ.isGen⟩, fun ⟨t, ht⟩ => ⟨⟨x, t, ht⟩, rfl⟩⟩

theorem weilIs_of_pow (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (d : ℕ)
    (e : cls M hM = d • cls L hL) {k : ℤ} {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A L k x y c) : Out.WeilIs A M k x y (c ^ d) := by
  have up : ∀ (T' : Over S) (u : T' ⟶ A), (∃ θ : Out.ThetaGrp A L k T', θ.pt = u) →
      ∃ θ : Out.ThetaGrp A M k T', θ.pt = u := fun T' u H => by
    rw [exists_theta_iff hL] at H
    rw [exists_theta_iff hM, e, map_nsmul, map_nsmul, smul_comm k d, smul_comm k d, ← smul_sub, H, smul_zero]
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := k) (x := x) (y := y) hG hA hM
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, H, -⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨-, θ, -, H⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
  have iso : LBIso (lbPow L d) (M.pull (𝟙 A : A ⟶ A).left) :=
    (cls_eq_iff (isLB_lbPow hL d) (pull_isLB hM _)).1 (by
      rw [cls_lbPow hL, cls_pull hM, Over.id_left, pull_id, e])
  have := (weilIs_along_hom hG S A A (𝟙 A) L M d k T x y c c' hA hA hL hM inferInstance iso
    (by simpa using hc')).2 h
  exact this ▸ hc'

end Pairing

section Principal

variable {S : Scheme.{0}}

theorem cls_diag (hG : Out.GlobalFnsSt)
    (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    (P : Out.PolAV S) [IsCommMonObj P.A] :
    cls _ (pull_isLB (isLB_lam P.isLB) (lift (𝟙 P.A) (𝟙 P.A)).left) = 2 • cls P.L P.isLB := by
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2
    ((MulPull.mulPull_of_cube_of_symm hc (exists_gen_negLB hG)).1 S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id] at h
  have e : Out.mulA P.A 2 = 𝟙 P.A * 𝟙 P.A := pow_two _
  rw [e] at h
  rw [cls_pull (isLB_lam P.isLB), pull_lam P.isLB P.rigid, Over.id_left, pull_id]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  push_cast
  module

theorem relAmple_of_pow {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) (h : Out.RelAmple A L) : Out.RelAmple A M := by
  have := hA.proper
  rw [relAmple_iff_isAmpleLB A hL] at h
  refine relAmple_of_isAmpleLB A hM fun U hU => ?_
  refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _) ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).1
    ((isAmpleLB_pow_iff (pull_isLB hL _) hd).2 (h U hU))
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

end Principal

section Level

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

end Level

end GlobalTheory.SiegelOfTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

theorem isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (s : X ⟶ Sp R) :
    IsQProjOver s ↔ LocallyOfFiniteType s ∧ ∃ L : LB X, IsAmpleLB L := by
  constructor
  · rintro ⟨N, i, hi, hq, rfl⟩
    haveI := hi
    haveI := hq
    haveI : IsProper (PSpace.str R N) :=
      ((isProjOver_iff_isProper_and_exists_isAmpleLB (PSpace.str R N)).1
        ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩).1
    exact ⟨inferInstance, _, IsAmpleLB.pull_of_isImmersion (isAmpleLB_basic.2.2.2.2.2.2.1 R N) i⟩
  · rintro ⟨hs, L, hL⟩
    haveI := hs
    exact hL.isQProjOver s

theorem isQProjOver_comp_of_isAffineHom (f : Y ⟶ X) [IsAffineHom f] [LocallyOfFiniteType f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  haveI := hs
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (f ≫ s)).2 ⟨inferInstance, L.pull f, ?_⟩
  exact isAmpleLB_basic.2.2.1 f inferInstance hL

theorem isQProjOver_comp_of_isFinite (f : Y ⟶ X) [IsFinite f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := isQProjOver_comp_of_isAffineHom f h

theorem isQProjOver_of_isPullback {R' : Type} [CommRing R'] {b : R →+* R'} {s : X ⟶ Sp R} {π : Y ⟶ X}
    {s' : Y ⟶ Sp R'} (H : IsPullback π s' s (spMap b)) (h : IsQProjOver s) : IsQProjOver s' := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s').2 ⟨?_, L.pull π, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H hs
  · exact hL.pull_of_isPullback H

theorem isQProjOver_finite_and_baseChange :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      (∀ (Y : Scheme.{0}) (f : Y ⟶ X), IsFinite f → IsQProjOver (f ≫ s)) ∧
        ∀ (R' : Type) [CommRing R'] (b : R →+* R'), IsQProjOver (pullback.snd s (spMap b)) := by
  intro R _ _ X s h
  refine ⟨fun Y f hf => ?_, fun R' _ b => ?_⟩
  · haveI := hf
    exact isQProjOver_comp_of_isFinite f h
  · exact isQProjOver_of_isPullback (IsPullback.of_hasPullback s (spMap b)) h

end GlobalTheory
end
