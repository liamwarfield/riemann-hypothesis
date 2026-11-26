module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquiv
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem tateIsoAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (k : Type) [Field k] (x' : Sp k ⟶ X') (x : Sp k ⟶ X), x = x' ≫ f → (∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t' x', I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left) ∧ ∀ I' : TateIsoAt D t' x', ∃ I : TateIsoAt D t x, I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left := by
  intro E _ _ _ H D X X' t t' f m k _ x' x hx
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk x') (x' ≫ f) rfl
  have eact : ∀ c y, e (y ≫ t'.act.act c) = e y ≫ t.act.act c := fun c y => Over.OverMorphism.ext (by
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, m.act, Category.assoc])
  have eact' : ∀ c y, e.symm (y ≫ t.act.act c) = e.symm y ≫ t'.act.act c := fun c y =>
    e.injective (by rw [eact, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])
  have weil : ∀ (n : ℤ) (y y' : Over.mk x' ⟶ t'.G) (c : Γ(Sp k, ⊤)ˣ),
      Out.WeilIs t'.G t'.PP.L n y y' c ↔ Out.WeilIs t.G t.PP.L n (e y) (e y') c := fun n y y' c =>
    GlobalTheory.weilIs_grpPullback_of_comm' _ _ _ _ _ m.φ _ _ t.PP.isLB t'.PP.isLB m.cart hL (Over.mk x') n y y' (e y) (e y') c
      (he y) (he y')
  refine ⟨fun I => ⟨GlobalTheory.PELPeriod.tateIsoMap I e.symm eact' fun n y y' c h => (weil n _ _ _).2 ?_, rfl,
    fun n a => ?_⟩, fun I' => ⟨GlobalTheory.PELPeriod.tateIsoMap I' e eact fun n y y' c h => (weil n _ _ _).1 h, rfl,
    fun n a => (he _).symm⟩⟩
  · rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  · show (e.symm (I.ev n a)).left ≫ m.φ = _
    rw [← he, MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.XR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquivStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_iso_pullback_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (k : Type) [Field k] (x' : Sp k ⟶ X') (x : Sp k ⟶ X), x = x' ≫ f → (∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t' x', I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left) ∧ ∀ I' : TateIsoAt D t' x', ∃ I : TateIsoAt D t x, I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move | exact GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.tateIsoAt_move <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareGeneric
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

theorem exists_valPoint {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X)
    (W : ValuationSubring Ω') (i : Ω →+* Ω') (q : Cpt ξ) (hinj : Function.Injective (genMap ξ q))
    (h : DomBy W.toSubring i ξ q) :
    ∃ z : Sp W ⟶ X, spMap W.subtype ≫ z = spMap i ≫ ξ ∧ z (IsLocalRing.closedPoint W) = q.1 := by
  obtain ⟨h1, h2⟩ := h
  let φ : X.presheaf.stalk q.1 →+* W :=
    (i.comp (genMap ξ q)).codRestrict W.toSubring (fun a => h1 _ ⟨a, rfl⟩)
  have hφ : ∀ a, ((φ a : W) : Ω') = i (genMap ξ q a) := fun _ => rfl
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    have hne : genMap ξ q a ≠ 0 := by
      intro h0
      have : φ a = 0 := Subtype.ext (by rw [hφ, h0, map_zero]; rfl)
      rw [this] at ha
      exact not_isUnit_zero ha
    have hinv : (i (genMap ξ q a))⁻¹ ∈ W.toSubring := by
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hb' : i (genMap ξ q a) * (b : Ω') = 1 := by
        have := congrArg (fun x : W => (x : Ω')) hb
        simpa [hφ] using this
      rw [inv_eq_of_mul_eq_one_right hb']
      exact b.2
    obtain ⟨b, hb⟩ := h2 _ ⟨a, rfl⟩ hne hinv
    refine IsUnit.of_mul_eq_one b (hinj ?_)
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  let z : Sp W ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1
  refine ⟨z, ?_, ?_⟩
  · have e : CommRingCat.ofHom φ ≫ CommRingCat.ofHom W.subtype =
        X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
      ext a
      rfl
    have e2 : spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) =
        spMap i ≫ Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
      simp only [spMap, ← Spec.map_comp]
      rw [e]
      rfl
    show spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1 = _
    rw [← Category.assoc, e2]
    simp only [Category.assoc]
    have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
    have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have e5 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) ≫
        X.fromSpecStalk q.1 = ξ :=
      (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4
    exact congrArg (spMap i ≫ ·) e5
  · have : IsLocalHom (CommRingCat.ofHom φ).hom := hloc
    change X.fromSpecStalk q.1 (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint W)) = q.1
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem isSeparated_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str R N) := by
    unfold PSpace.str
    infer_instance
  infer_instance

theorem image_eq_of_domBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∀ (W : ValuationSubring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), DomBy W.toSubring (RingHom.id Ω) 𝔐.ξ q → DomBy W.toSubring i 𝔐₀.ξ q₀ → 𝔐.f q.1 = 𝔐₀.f q₀.1 := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i hξ W q q₀ hq hq₀
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W (RingHom.id Ω) q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐₀.ξ W i q₀ (𝔐₀.tie.gen.inj q₀) hq₀
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐₀.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    have : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [this, Category.id_comp, hξ]
    simp only [Category.assoc]
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐₀.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐₀.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐₀.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareGenericStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_compare_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∀ (W : ValuationSubring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), DomBy W.toSubring (RingHom.id Ω) 𝔐.ξ q → DomBy W.toSubring i 𝔐₀.ξ q₀ → 𝔐.f q.1 = 𝔐₀.f q₀.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.image_eq_of_domBy | exact GlobalTheory.CompanionTheory.Ar.OrVert.image_eq_of_domBy | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.image_eq_of_domBy <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareFlag
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTail
theorem UpperTheory.Reformulated.B.DYha5.main :
    ∀ {Ω Ω₀ F F₀ : Type} [inst : Field Ω] [inst_1 : Field Ω₀] [inst_2 : AddCommGroup F] [inst_3 : _root_.Module Ω F]
      [inst_4 : AddCommGroup F₀] [inst_5 : _root_.Module Ω₀ F₀] (i : Ω₀ →+* Ω) (ι : F₀ →+ F),
      (∀ (a : Ω₀) (e : F₀), (ι : F₀ → F) (a • e) = (i : Ω₀ → Ω) a • (ι : F₀ → F) e) →
        ∀ (W : Subring Ω) (A : Subring Ω₀),
          (∀ a ∈ A, (i : Ω₀ → Ω) a ∈ W) →
            ∀ (T : Set F₀),
              Submodule.span (↥W) ((⇑ι : F₀ → F) '' (↑(Submodule.span (↥A) T) : Set F₀)) =
                Submodule.span (↥W) ((⇑ι : F₀ → F) '' T) := by
  intro Ω Ω₀ F F₀ _ _ _ _ _ _ i ι hι W A hA T
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span (↥A) T := hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hy ‹_›) (hz ‹_›)
    | smul a y _ hy =>
      have h1 : ι (a • y) = (⟨i a, hA a a.2⟩ : ↥W) • ι y := hι (a : Ω₀) y
      rw [h1]
      exact Submodule.smul_mem _ _ (hy ‹_›)
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareFlag
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp

theorem exists_ext {S : Scheme.{0}} {G : Over S} [GrpObj G] (hs : Smooth G.hom) {R R' : Type} [Field R] [Field R']
    (i : R →+* R') (x : Sp R ⟶ S) (y : Sp R' ⟶ S) (hy : spMap i ≫ x = y) {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = spMap (dualMap i) ≫ (M.pt e).left) ∧ IsExtOver i j ∧
      Submodule.span R' (Set.range j) = ⊤ := by
  subst hy
  letI := i.toAlgebra
  obtain ⟨j, hj, hl, hsp⟩ := GlobalTheory.T.lie_model_base_change_map S G R R' x E E' M M'
  have hbc := hsp hs
  obtain ⟨m, ⟨b₁⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring S G hs R x E M
  refine ⟨j, hj, ⟨hl, fun n b hb => LiePull.indep_of_bases b₁ j (fun m B => (hbc m B).1) b hb⟩, ?_⟩
  refine top_le_iff.1 ((hbc m b₁).2.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

variable {Ω Ω₀ F F₀ : Type} [Field Ω] [Field Ω₀] [AddCommGroup F] [Module Ω F] [AddCommGroup F₀] [Module Ω₀ F₀]

theorem span_span (W A : Subring Ω) (h : ∀ a ∈ A, a ∈ W) (T : Set F) :
    Submodule.span W ((Submodule.span A T : Submodule A F) : Set F) = Submodule.span W T := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => ?_) (Submodule.span_mono Submodule.subset_span)
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ (⟨(a : Ω), h _ a.2⟩ : W) hx

theorem span_image_span (i : Ω₀ →+* Ω) (ι : F₀ →+ F) (hι : ∀ (a : Ω₀) (e : F₀), ι (a • e) = i a • ι e)
    (W : Subring Ω) (A : Subring Ω₀) (h : ∀ a ∈ A, i a ∈ W) (T : Set F₀) :
    Submodule.span W (ι '' ((Submodule.span A T : Submodule A F₀) : Set F₀)) = Submodule.span W (ι '' T) :=
  _root_.UpperTheory.Reformulated.B.DYha5.main i ι hι W A h T

theorem lie_cmp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (Fl₀ : 𝔐₀.Flag) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∃ ι : 𝔐₀.Li →+ 𝔐.Li, IsExtOver i ι ∧ Submodule.span Ω (Set.range ι) = ⊤ ∧ (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) ∧ ∀ (W : Subring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), (∀ a ∈ regAt 𝔐.ξ q, a ∈ W) → (∀ a ∈ regAt 𝔐₀.ξ q₀, i a ∈ W) → 𝔐.f q.1 = 𝔐₀.f q₀.1 → Submodule.span W ((𝔐.M.lat q : Set 𝔐.Li)) = Submodule.span W (ι '' (𝔐₀.M.lat q₀ : Set 𝔐₀.Li)) := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ Fl₀ i hh
  have hs : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨ι, hpt, hext, hspan⟩ := exists_ext hs i (𝔐₀.ξ ≫ 𝔐₀.f) (𝔐.ξ ≫ 𝔐.f) hh.symm
    (LieMove.pushModel 𝔐₀.m.cart 𝔐₀.M) (LieMove.pushModel 𝔐.m.cart 𝔐.M)
  have hpt' : ∀ e, (𝔐.M.pt (ι e)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ := hpt
  have hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ₀ 𝔐.f (i.comp 𝔐₀.fn) := by
    have h₀ : 𝔐₀.ξ ≫ 𝔐₀.f = Spec.map (CommRingCat.ofHom 𝔐₀.fn) ≫ 𝔐₀.ξ₀ := 𝔐₀.fn_over
    show 𝔐.ξ ≫ 𝔐.f = _
    rw [hh, h₀, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hj' : ∀ e, (𝔐.M.pt ((ι.comp Fl₀.j) e)).left ≫ 𝔐.m.φ =
      Spec.map (CommRingCat.ofHom (dualMap (i.comp 𝔐₀.fn))) ≫ (Fl₀.M₀.pt e).left := by
    intro e
    rw [AddMonoidHom.comp_apply, hpt', Fl₀.j_pt, ← LiePull.dualMap_comp, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc]
  have m₀ := (LiePull.main Y.X 𝔐₀.X 𝔐₀.Ω₀ Ω₀ 𝔐₀.ξ₀ 𝔐₀.ξ 𝔐₀.f 𝔐₀.fn Y.t.G 𝔐₀.t.G 𝔐₀.m.φ Fl₀.Li₀ 𝔐₀.Li Fl₀.M₀ 𝔐₀.M
    Fl₀.j 𝔐₀.gen₀ 𝔐₀.tie.gen 𝔐₀.fn_over 𝔐₀.m.cart hs Fl₀.j_pt).2.2
  have m₁ := (LiePull.main Y.X 𝔐.X 𝔐₀.Ω₀ Ω 𝔐₀.ξ₀ 𝔐.ξ 𝔐.f (i.comp 𝔐₀.fn) Y.t.G 𝔐.t.G 𝔐.m.φ Fl₀.Li₀ 𝔐.Li Fl₀.M₀ 𝔐.M
    (ι.comp Fl₀.j) 𝔐₀.gen₀ 𝔐.tie.gen hd 𝔐.m.cart hs hj').2.2
  refine ⟨ι, hext, hspan, fun e e' => ⟨fun h => ?_, ?_⟩, fun W q q₀ hq hq₀ hf => ?_⟩
  · exact (LieMove.pushModel 𝔐.m.cart 𝔐.M).inj (Over.OverMorphism.ext (h.trans (hpt' e).symm))
  · rintro rfl
    exact hpt' e
  · have a₁ := congrFun m₁ q
    rw [Lat.pull_apply _ hd] at a₁
    have a₀ := congrFun m₀ q₀
    rw [Lat.pull_apply _ 𝔐₀.fn_over] at a₀
    have es : (⟨𝔐.f q.1, hd.specializes q⟩ : Cpt 𝔐₀.ξ₀) = ⟨𝔐₀.f q₀.1, 𝔐₀.fn_over.specializes q₀⟩ := Subtype.ext hf
    rw [a₁, a₀, es, span_span W _ hq, span_image_span i ι hext.1 W _ hq₀, Set.image_image]
    rfl

end GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCompareFlagStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_compare_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (Fl₀ : 𝔐₀.Flag) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∃ ι : 𝔐₀.Li →+ 𝔐.Li, IsExtOver i ι ∧ Submodule.span Ω (Set.range ι) = ⊤ ∧ (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) ∧ ∀ (W : Subring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), (∀ a ∈ regAt 𝔐.ξ q, a ∈ W) → (∀ a ∈ regAt 𝔐₀.ξ q₀, i a ∈ W) → 𝔐.f q.1 = 𝔐₀.f q₀.1 → Submodule.span W ((𝔐.M.lat q : Set 𝔐.Li)) = Submodule.span W (ι '' (𝔐₀.M.lat q₀ : Set 𝔐₀.Li)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.lie_cmp | exact GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.lie_cmp | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.lie_cmp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesFlagDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesFlagDegree
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

theorem rootLine_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (r : CMType H × Fin (D.p + D.q)) (q : Cpt 𝔐.ξ) (cc : (k : K) → J k) (b : Fin (labelRk D (HodgeCpt.rootIdx D r).1) → 𝔐.Li) (t : Ω), Fl.RootLines xdeg e → InChart 𝔐.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc q → (∀ j, flagStep Ω b j = flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) j) → (𝔐.V (HodgeCpt.rootIdx D r).1).IsFrameAt b q → b (HodgeCpt.rootIdx D r).2 - t • Fl.b (HodgeCpt.rootIdx D r).1 (HodgeCpt.rootIdx D r).2 ∈ flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2 → unitAt 𝔐.ξ q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r / t ^ HodgeCpt.rootSgn D r) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 Fl xdeg e r q cc b t hd hq hF hL hc
  have ht := FlagModel.gr_isGenAt _ b (Fl.b (HodgeCpt.rootIdx D r).1) q hL hF _ t hc
  have hT : (Fl.rootLat r).IsGenAt q (t ^ HodgeCpt.rootSgn D r) := by
    simpa [HodgeCpt.Flag.rootLat] using FlagModel.tens_isGenAt
      (fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
      (fun _ => HodgeCpt.rootSgn D r) q (fun _ => t) fun _ => ht
  obtain ⟨he, h⟩ := hd r
  have h1 := h q (Set.mem_univ _) cc hq
  have hy : (∏ k, y ⟨k, cc k⟩ ^ xdeg r k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hq.1 k hk)
  have hW : (Fl.rootLat r).IsGenAt q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r) := ⟨mul_ne_zero hy he, h1⟩
  have hw0 := hW.1
  have ht0 := hT.1
  refine ⟨div_ne_zero hw0 ht0, ?_, ?_⟩
  · simpa using FlagModel.zpow_ratio _ q _ _ hT hW 1
  · simpa using FlagModel.zpow_ratio _ q _ _ hW hT 1

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesFlagDegreeStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_lines_flag_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (r : CMType H × Fin (D.p + D.q)) (q : Cpt 𝔐.ξ) (cc : (k : K) → J k) (b : Fin (labelRk D (HodgeCpt.rootIdx D r).1) → 𝔐.Li) (t : Ω), Fl.RootLines xdeg e → InChart 𝔐.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc q → (∀ j, flagStep Ω b j = flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) j) → (𝔐.V (HodgeCpt.rootIdx D r).1).IsFrameAt b q → b (HodgeCpt.rootIdx D r).2 - t • Fl.b (HodgeCpt.rootIdx D r).1 (HodgeCpt.rootIdx D r).2 ∈ flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2 → unitAt 𝔐.ξ q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r / t ^ HodgeCpt.rootSgn D r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.rootLine_unitAt | exact GlobalTheory.CompanionTheory.Ar.OrVert.rootLine_unitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.rootLine_unitAt <;> assumption)
end
end
