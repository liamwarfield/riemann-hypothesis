module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullback
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSecondPartialLawIffPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FrameTieHolds
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceInt.FrameTie

open GermD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cube_points {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (a : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (m : ℕ)
    (ha : x m ≫ t.act.act H.w0 =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (a p.2)) ≫ x m)
    (I : ULift.{0} (Finset (Fin 2))) :
    (x m).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (Formalism.L2.Pj.homAt x0 (sL m a)).left ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
  have hpt : (fun i => x m ≫ (![𝟙 t.G, t.act.act H.w0] : Fin 2 → (t.G ⟶ t.G)) i) =
      fun i => Formalism.L2.Pj.homAt x0 (sL m a) ≫
        (![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] : Fin 2 → (jOG x0 d m 2 ⟶ t.G)) i := by
    funext i
    fin_cases i
    · show x m ≫ 𝟙 t.G = Formalism.L2.Pj.homAt x0 (sL m a) ≫ Formalism.L2.Pj.homAt x0 (jetCopy d m (0 : Fin 2)) ≫ x m
      rw [Category.comp_id, ← Category.assoc, Formalism.L2.Pj.homAt_comp, sL_copy0, Formalism.L2.Pj.homAt_id, Category.id_comp]
    · show x m ≫ t.act.act H.w0 =
        Formalism.L2.Pj.homAt x0 (sL m a) ≫ Formalism.L2.Pj.homAt x0 (jetCopy d m (1 : Fin 2)) ≫ x m
      rw [← Category.assoc, Formalism.L2.Pj.homAt_comp, sL_copy1, ha]
  simp only [cφG, ← Over.comp_left]
  refine congrArg (fun f => Over.Hom.left f) ?_
  refine (psum_hom (Formalism.L2.Pj.preHom (x m)) _ I.down).trans
    (Eq.trans ?_ (psum_hom (Formalism.L2.Pj.preHom (Formalism.L2.Pj.homAt x0 (sL m a))) _ I.down).symm)
  exact congrArg (fun f => psum t.G f I.down) hpt

theorem prod_points {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (a : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (m : ℕ)
    (ha : x m ≫ t.act.act H.w0 =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (a p.2)) ≫ x m)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 1).left ⟶ t.G.left) → U) :
    (∏ k : Fin 1 ⊕ ULift.{0} (Finset (Fin 2)), h ((x m).left ≫ primφ t k) ^ primε k) *
      ∏ I : ULift.{0} (Finset (Fin 2)), h ((Formalism.L2.Pj.homAt x0 (sL m a)).left ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) ^ cε 2 I = h (x m).left := by
  simp only [Fintype.prod_sum_type, primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id,
    cube_points t x0 d x a m ha]
  rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
  simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one, zpow_one]

theorem val_eLG_tie {X0 X1 : Scheme.{0}} (t : SAB H X0) (t' : SAB H X1) {S S' : Type} [CommRing S] [CommRing S']
    (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X1) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t'.G)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (act' : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S')
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' x1 d x' m) (wP : PrimTyG t) (wP' : PrimTyG t')
    (φ : t'.G.left ⟶ t.G.left) (w : LB.Iso t'.PP.L (t.PP.L.pull φ)) (m : ℕ)
    (ha : x' m ≫ t'.act.act H.w0 =
      Formalism.L2.Pj.homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act' H.w0 p.2)) ≫ x' m)
    (c : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' x1 d x' m (0 : Fin 2),
      jptG t' x1 d x' m (1 : Fin 2)] J ≫ φ) (cε 2)))
    (hc : LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' x1 d x' m (0 : Fin 2),
      jptG t' x1 d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L φ _ _ c))
    (cP : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ φ) primε))
    (hP₁ : LB.Gen.Corr t.PP.L _ _ _ _ cP (LB.pullGen t.PP.L _ _ wP φ))
    (hP₂ : LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L φ _ _ cP))
    {Z : Scheme.{0}} (r : Z ⟶ (jOG x1 d m 1).left) (s : Z ⟶ (jOG x0 d m 1).left) (z : Z)
    {J : (Z ⟶ t.G.left) → t.PP.L.ι} {J' : (Z ⟶ t'.G.left) → t'.PP.L.ι} (hJ : Good t.PP.L z J)
    (hJ' : Good t'.PP.L z J') (hx : s ≫ (x m).left = (r ≫ (x' m).left) ≫ φ)
    (he : val (φ := cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (ε := cε 2) (e m)
        (s ≫ (Formalism.L2.Pj.homAt x0 (sL m (act H.w0))).left) z J =
      val c (r ≫ (Formalism.L2.Pj.homAt x1 (sL m (act' H.w0))).left) z J) :
    val (eLG t x0 d x act e wP m) s z J =
      Geo.Tor.gw w (r ≫ (x' m).left) z (J ((r ≫ (x' m).left) ≫ φ)) (J' (r ≫ (x' m).left)) *
        val (eLG t' x1 d x' act' e' wP' m) r z J' := by
  have p₁ := (congrArg (fun q => val wP q z J) hx).trans ((val_pull hJ wP φ _).symm.trans
    ((val_corr hJ hP₁ _).symm.trans (GlobalTheory.RigOriginPull.val_tie w _ _ wP' cP hP₂ _ z hJ hJ')))
  have p₂ := he.trans (GlobalTheory.RigOriginPull.val_tie w _ _ (e' m) c hc _ z hJ hJ')
  have q := prod_points t' x1 d x' (act' H.w0) m ha
    (fun f => Geo.Tor.gw w (r ≫ f) z (J ((r ≫ f) ≫ φ)) (J' (r ≫ f)))
  refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) ((val_pull hJ _ _ _).trans p₁)
    ((val_pull hJ _ _ _).trans p₂)).trans ((_root_.mul_mul_mul_comm _ _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · refine Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)) q
    · exact congrArg (fun f => Geo.Tor.gw w f z (J (f ≫ φ)) (J' f) ^ primε k) (Category.assoc _ _ _)
    · exact congrArg (fun f => Geo.Tor.gw w f z (J (f ≫ φ)) (J' f) ^ cε 2 k) (Category.assoc _ _ _)
  · exact ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ' _ _ _) (val_pull hJ' _ _ _))).symm

theorem exists_frame {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t) (m : ℕ) (he : (e m).IsGen) (hP : wP.IsGen)
    (ha : x m ≫ t.act.act H.w0 =
      Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act H.w0 p.2)) ≫ x m) :
    ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left) fun _ => (1 : ℤ)),
      τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι),
        Good t.PP.L z J → val τ r z J = val (eLG t x0 d x act e wP m) r z J := by
  refine exists_gen t.PP.isLB ?_ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen t.PP.L _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ hP _) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen t.PP.L _ _ _ he _))
  intro U _ hU
  rw [Fintype.prod_sum_type, Fin.prod_univ_one, zpow_one]
  exact prod_points t x0 d x (act H.w0) m ha hU

theorem act_of_map {X0 : Scheme.{0}} (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S))
    (mp : SABMap t' t x0) {A : Type} [CommRing A] [Algebra S A] (x : overAt x0 A ⟶ t.G)
    (x' : overAt (𝟙 (Sp S)) A ⟶ t'.G) (hx : x'.left ≫ mp.φ = x.left) (a : 𝓞 E) (σ : A →ₐ[S] A)
    (h : x ≫ t.act.act a = Formalism.L2.Pj.homAt x0 σ ≫ x) :
    x' ≫ t'.act.act a = Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ ≫ x' := by
  apply Over.OverMorphism.ext
  refine mp.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)
  have h' : x.left ≫ (t.act.act a).left = (Formalism.L2.Pj.homAt x0 σ).left ≫ x.left := congrArg (fun q => q.left) h
  have hx' : x'.left ≫ mp.cm.F = x.left := hx
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, mp.act a, ← Category.assoc, hx']
  exact h'

end GlobalTheory.PlaceInt.FrameTie


open GlobalTheory.PlaceInt.FrameTie GermD in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PlaceInt.frameTie_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ReciprocityTheory.ChartRestriction.G.PullbackSections.FrameTieSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ _ Tc io yI C
  letI := io.toAlgebra
  obtain ⟨⟨-, hact, -⟩, x', hx2, hx1, ⟨e', he'⟩, wP', hPg, ⟨cP₂, hP₂, hP₂'⟩, cP₁, hP₁, hP₁'⟩ := C.gen
  have ha : ∀ m, x' m ≫ C.I.t'.act.act H.w0 = Formalism.L2.Pj.homAt (𝟙 (Sp Tc.Fr))
      (jetSubstP m fun p : Fin 1 × Fin C.ch.d => psTrunc m (C.ch.B.A.act H.w0 p.2)) ≫ x' m := fun m =>
    act_of_map Xo.univ.t yI.1.x C.I.t' C.I.m1 (C.ch.x m) (x' m) (hx1 m) H.w0 _ (C.ch.chart.act m H.w0)
  choose τ _ hτ using fun m => exists_frame C.I.t' (𝟙 (Sp Tc.Fr)) C.ch.d x' C.ch.B.A.act e' wP' m (he' m).1 hPg (ha m)
  refine ⟨x', hx1, hx2, τ, fun m Z r z J J' J'' hJ hJ' hJ'' => ?_⟩
  obtain ⟨-, ⟨c₂, hc₂, hc₂'⟩, c₁, hc₁, hc₁'⟩ := he' m
  rw [Category.comp_id, hτ m Z r z J' hJ']
  constructor
  · refine val_eLG_tie Xo.univ.t C.I.t' yI.1.x (𝟙 (Sp Tc.Fr)) C.ch.d C.ch.x x' C.ch.B.A.act C.ch.B.A.act C.ch.e e'
      C.ch.wP wP' C.I.m1.φ C.I.w1 m (ha m) c₁ hc₁' cP₁ hP₁ hP₁' r r z hJ hJ' ?_ (val_corr hJ hc₁ _).symm
    exact (congrArg (r ≫ ·) (hx1 m).symm).trans (Category.assoc _ _ _).symm
  · refine val_eLG_tie C.I.G C.I.t' (𝟙 (Sp Tc.V)) (𝟙 (Sp Tc.Fr)) C.ch.d C.xT x' C.actT C.ch.B.A.act C.eT e'
      C.wPT wP' C.I.m2.φ C.I.w2 m (ha m) c₂ hc₂' cP₂ hP₂ hP₂' r _ z hJ'' hJ' ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (hx2 m).symm).trans (Category.assoc _ _ _).symm)
    · refine Eq.symm ((val_corr hJ'' hc₂ _).trans ((val_pull hJ'' _ _ _).trans ?_))
      refine congrArg (fun q => val (C.eT m) q z J'') ?_
      refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      refine congrArg (r ≫ ·) (GlobalTheory.ChartRigBC.subst_jetCoef (algebraMap Tc.V Tc.Fr) (𝟙 _)
        (spMap (algebraMap Tc.V Tc.Fr)) C.ch.d m 2 1 _ _ ?_)
      rintro ⟨i, j⟩
      fin_cases i
      · exact (MvPolynomial.map_X _ _).symm
      · exact (congrArg (psIn C.ch.d m ![0]) (hact H.w0 j)).trans (GlobalTheory.RawChartGermBC.map_psIn _ C.ch.d m _ _).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScale
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.RegularGerm

theorem psJet_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (g : MvPowerSeries κ R) : psJet m (MvPowerSeries.map f g) = jetCoef f κ m (psJet m g) := by
  unfold psJet jetCoef
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]
  congr 1
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem psJet_smul {F κ : Type} [CommRing F] [Fintype κ] [DecidableEq κ] (m : ℕ) (c : F) (f : MvPowerSeries κ F) :
    psJet m (c • f) = algebraMap F (Jet F κ m) c * psJet m f := by
  have h : psTrunc m (c • f) = MvPolynomial.C c * psTrunc m f := by
    simp only [psTrunc, Finset.mul_sum, MvPolynomial.C_mul_monomial, map_smul, smul_eq_mul]
  rw [psJet, h]
  rfl

theorem gs_spMap_toΓ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {Z : Scheme.{0}} (r : Z ⟶ Sp B) (z : Z)
    (a : A) : gs (r ≫ spMap f) z ⊤ (toΓ A a) = gs r z ⊤ (toΓ B (f a)) := by
  refine (gs_pull r (spMap f) z ⊤ trivial (toΓ A a)).symm.trans ?_
  exact congrArg (gs r z ⊤)
    (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem tie_alg {R : Type} [CommRing R] {a b s v : R} {u₁ u₂ e e₁ e₂ : Rˣ} {k : ℕ} (ha : a = u₁.val ^ k * s)
    (hb : b = u₂.val ^ k * s) (hv : b = v * (e₂ ^ k).val) (h₁ : e₁ = u₁ * e) (h₂ : e₂ = u₂ * e) :
    a = v * (e₁ ^ k).val := by
  subst h₁ h₂
  have hs : s = v * e.val ^ k := by
    refine (Units.mul_right_inj (u₂ ^ k)).1 ?_
    rw [Units.val_pow_eq_pow_val, ← hb, hv, Units.val_pow_eq_pow_val, Units.val_mul]
    ring
  rw [ha, hs, Units.val_pow_eq_pow_val, Units.val_mul]
  ring

section Values
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}

abbrev sv (t : SAB H X) {k : ℤ} {T : Over X} (s : LB.Sec (LPow t.G t.PP.L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ t.G).left)
    (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) : Z.presheaf.stalk z :=
  sval (L := t.PP.L) (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => k) s r z J

theorem ptSecT_snd {T : Over X} (a : T ⟶ t.G) : (ptSecT t.G a).left ≫ (snd T t.G).left = a.left := by
  rw [← Over.comp_left, ptSecT, lift_snd]

theorem sv_of_isValueAt {n : ℤ} {T : Over X} {s : LB.Sec (LPow t.G t.PP.L n T)} {a : T ⟶ t.G}
    {τ : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => a.left) (fun _ => n))} {c : Γ(T.left, ⊤)}
    (h : IsValueAt t.G t.PP.L n s a τ c) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J}
    (hJ : Good t.PP.L z J) : sv t s (r ≫ (ptSecT t.G a).left) z J = gs r z ⊤ c * (val τ r z J).val := by
  have hz := hJ.mem (fun _ : Fin 1 => a.left) r
  refine (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s _ z J (fun _ => J (r ≫ a.left))
    (fun _ => by rw [Category.assoc, ptSecT_snd])).trans ?_
  exact ((gs_res r z _ hz _).trans (gs_pull r (ptSecT t.G a).left z _ (val_le t.G t.PP.L a _ hz) _)).symm.trans
    ((congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_res r z le_top hz c) (gs_unit r z _ hz _))))

theorem isValueAt_of_sv {n : ℤ} {T : Over X} {s : LB.Sec (LPow t.G t.PP.L n T)} {a : T ⟶ t.G}
    {τ : LB.Gen (LB.LinComb t.PP.L (Y := T.left) (K := Fin 1) (fun _ => a.left) (fun _ => n))} {c : Γ(T.left, ⊤)}
    (h : ∀ (z : T.left) J, Good t.PP.L z J →
      sv t s (𝟙 _ ≫ (ptSecT t.G a).left) z J = gs (𝟙 _) z ⊤ c * (val τ (𝟙 _) z J).val) :
    IsValueAt t.G t.PP.L n s a τ c := fun j => fn_ext fun y hy => by
  obtain ⟨J, hJ, e⟩ := exists_good t.PP.L t.PP.isLB y (fun _ : Fin 1 => a.left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k)
  have q := h y J hJ
  rw [val_of τ _ y J j (fun k => by rw [Category.id_comp]; exact e k)] at q
  have q' := (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s (𝟙 _ ≫ (ptSecT t.G a).left) y J j
    (fun k => by rw [Category.id_comp, ptSecT_snd]; exact e k)).symm.trans q
  exact ((gs_res _ y _ hy _).trans (gs_pull _ (ptSecT t.G a).left y _ (val_le t.G t.PP.L a _ hy) _)).trans
    (q'.trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy c) (gs_unit _ y _ hy _))).symm)

theorem sv_pullSec {n : ℤ} {T T' : Over X} {h : T' ⊗ t.G ⟶ T ⊗ t.G} {hh : h ≫ snd T t.G = snd T' t.G}
    {s : LB.Sec (LPow t.G t.PP.L n T)} {s' : LB.Sec (LPow t.G t.PP.L n T')} (hs : IsPullSec t.G t.PP.L n h hh s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ t.G).left) (z : Z) {J} (hJ : Good t.PP.L z J) :
    sv t s' r z J = sv t s (r ≫ h.left) z J :=
  (GermD.pullSec_stalk t.G t.PP.L n hs r z _ (hJ.mem (fun _ : Fin 1 => (snd T' t.G).left) r)).trans
    (sval_of (φ := fun _ : Fin 1 => (snd T t.G).left) (ε := fun _ => n) s _ z J _
      (fun _ => by rw [Category.assoc, ← Over.comp_left, hh])).symm

theorem sv_scale {n : ℤ} {T : Over X} {s s' : LB.Sec (LPow t.G t.PP.L n T)} {c : Γ(T.left, ⊤)}
    (h : ∀ j, s'.f j = liftFun t.G _ c * s.f j) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ t.G).left) (z : Z) {J}
    (hJ : Good t.PP.L z J) : sv t s' r z J = gs (r ≫ (fst T t.G).left) z ⊤ c * sv t s r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd T t.G).left) r
  exact (congrArg (gs r z _) (h _)).trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z le_top hm _).trans (gs_pull r (fst T t.G).left z ⊤ trivial c)) rfl))

variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X} {d : ℕ}

def jetPt {m : ℕ} (a : jOG x0 d m 1 ⟶ t.G) : (jOG x0 d m 1).left ⟶ (Over.mk x0 ⊗ t.G).left :=
  (ptSecT t.G a).left ≫ (jBaseG x0 d m 1 ▷ t.G).left

theorem jetPt_snd {m : ℕ} (a : jOG x0 d m 1 ⟶ t.G) : jetPt a ≫ (snd (Over.mk x0) t.G).left = a.left := by
  rw [jetPt, ← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_snd]

theorem jetPt_fst {m : ℕ} (a : jOG x0 d m 1 ⟶ t.G) :
    jetPt a ≫ (fst (Over.mk x0) t.G).left = spMap (algebraMap S (Jet S (Fin 1 × Fin d) m)) := by
  rw [jetPt, ← Over.comp_left, ← Over.comp_left, ptSecT, lift_whiskerRight, lift_fst, Category.id_comp]; rfl

variable {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {e : ∀ m, FrTyG t x0 d x m} {wP : PrimTyG t} {k : ℕ} {s : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))}
  {f : MvPowerSeries (Fin 1 × Fin d) S}

theorem sv_of_isGerm (h : IsGermG t x0 d x act e wP k s f) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jOG x0 d m 1).left) (z : Z)
    {J} (hJ : Good t.PP.L z J) :
    sv t s (r ≫ jetPt (x m)) z J =
      gs r z ⊤ (toΓ _ (psJet m f)) * (val (eLG t x0 d x act e wP m) r z J ^ k).val := by
  obtain ⟨s₁, τ, hp, hτ, hv⟩ := h m
  have q₁ := sv_of_isValueAt hv r z hJ
  have q₂ := (val_corr hJ hτ r).trans (GermD.val_genPowG t _ _ _ k r z J)
  have q₃ := sv_pullSec hp (r ≫ (ptSecT t.G (x m)).left) z hJ
  rw [Category.assoc] at q₃
  rw [← q₂]
  exact q₃.symm.trans q₁

theorem isGerm_of_sv {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S} (hc : IsChartG t x0 d F act tg uvec x)
    (hP : wP.IsGen) (hg : ∀ m, (e m).IsGen)
    (h : ∀ (m : ℕ) (z : (jOG x0 d m 1).left) J, Good t.PP.L z J → sv t s (𝟙 _ ≫ jetPt (x m)) z J =
      gs (𝟙 _) z ⊤ (toΓ _ (psJet m f)) * (val (eLG t x0 d x act e wP m) (𝟙 _) z J ^ k).val) :
    IsGermG t x0 d x act e wP k s f := by
  intro m
  have heL : (eLG t x0 d x act e wP m).IsGen :=
    DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (DVR.pullGen_isGen t.PP.L _ _ _ hP _) (DVR.pullGen_isGen t.PP.L _ _ _ (hg m) _)
  obtain ⟨τ, -, hτ⟩ : ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (k : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (genPowG t _ _ (eLG t x0 d x act e wP m) k) r z J := by
    refine exists_gen t.PP.isLB ?_ _ (GermD.genPowG_isGen t _ _ _ heL k)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, _root_.mul_one,
      GermD.formEq_eL hc m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, _root_.mul_neg, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  obtain ⟨s₁, hp⟩ := GermD.exists_pullSec t.G t.PP.L (k : ℤ) (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) s
  refine ⟨s₁, τ, hp, corr_of_val t.PP.isLB fun y J hJ => hτ _ _ y J hJ, isValueAt_of_sv fun z J hJ => ?_⟩
  have q₃ := (hτ _ (𝟙 _) z J hJ).trans (GermD.val_genPowG t _ _ _ k (𝟙 _) z J)
  refine (sv_pullSec hp _ z hJ).trans ?_
  rw [Category.assoc, q₃]
  exact h m z J hJ

theorem isGerm_smul {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S} (hc : IsChartG t x0 d F act tg uvec x)
    (hP : wP.IsGen) (hg : ∀ m, (e m).IsGen) {s' : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))} {a : S}
    (hs : ∀ j, s'.f j = liftFun t.G _ (T := Over.mk x0) (toΓ S a) * s.f j) (h : IsGermG t x0 d x act e wP k s f) :
    IsGermG t x0 d x act e wP k s' (a • f) := by
  refine isGerm_of_sv hc hP hg fun m z J hJ => ?_
  refine (sv_scale hs _ z hJ).trans ?_
  rw [sv_of_isGerm h m (𝟙 _) z hJ, Category.assoc, jetPt_fst, psJet_smul, map_mul, ← _root_.mul_assoc]
  refine congrArg₂ (· * ·) ?_ rfl
  exact (congrArg₂ (· * ·) (gs_spMap_toΓ _ _ z a) rfl).trans (gs_mul _ z ⊤ trivial _ _).symm

end Values

theorem exists_sec_id {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (n : ℤ)
    (σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => n))) (T : Over X) :
    ∃ σ' : LB.Sec (LPow t.G t.PP.L n T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ t.G).left) (z : Z) (J),
      Good t.PP.L z J → sv t σ' r z J = sval σ (r ≫ (snd T t.G).left) z J := by
  obtain ⟨σ', hσ'⟩ := exists_sec t.PP.isLB
    (φ := fun _ : Fin 1 => (snd T t.G).left ≫ 𝟙 t.G.left)
    (ε := fun _ => n) (φ' := fun _ : Fin 1 => (snd T t.G).left)
    (ε' := fun _ => n) (fun U _ f => by simp)
    (ReciprocityTheory.ChartRestriction.G.DVR.pullSec t.PP.L (fun _ => 𝟙 t.G.left) (fun _ => n) σ (snd T t.G).left)
  exact ⟨σ', fun Z r z J hJ => (hσ' Z r z J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ σ _ r z hJ)⟩

section Chart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem map_injective {κ : Type} :
    Function.Injective (MvPowerSeries.map (σ := κ) (algebraMap T.V T.Fr)) := fun f g h => by
  ext n
  refine IsFractionRing.injective T.V T.Fr ?_
  rw [← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, h]

theorem germIs_unique (C : IntegralChartA3 Xo c T io y) (k : ℕ) (F : SecN Xo (xOf y) k) (f f' : PS T.V 1 (chD C.ch))
    (h : GermIs C k F f) (h' : GermIs C k F f') : f = f' := by
  letI := io.toAlgebra
  exact map_injective (isGermFun_holds E H Dw l Xo c T.Fr y.1 _ _ _ _ _ k F _ _ h h')

theorem germIs_smul (C : IntegralChartA3 Xo c T io y) (k : ℕ) (F F' : SecN Xo (xOf y) k) (r : T.V) (f : PS T.V 1 (chD C.ch))
    (hs : ∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo (xOf y)) (toΓ T.Fr (algebraMap T.V T.Fr r)) * F.f j)
    (h : GermIs C k F f) : GermIs C k F' (r • f) := by
  letI := io.toAlgebra
  have e : MvPowerSeries.map (algebraMap T.V T.Fr) (r • f) =
      algebraMap T.V T.Fr r • MvPowerSeries.map (algebraMap T.V T.Fr) f := by
    ext n
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, map_mul]
  have q := isGerm_smul ((isChart_iff y.1 _ _ _ _ _).1 C.ch.chart) C.ch.prim.1 C.ch.frame.gen hs
    ((isGerm_iff y.1 _ _ _ _ _ _ _ _).1 h)
  rw [← e] at q
  exact (isGerm_iff y.1 _ _ _ _ _ _ _ _).2 q


set_option maxHeartbeats 1600000 in
theorem exists_germIs (hFT : ReciprocityTheory.ChartRestriction.G.PullbackSections.FrameTieSt Xo c) (C : IntegralChartA3 Xo c T io y)
    (hC : FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT) (k : ℕ) (F : SecN Xo (xOf y) k) (hF : Regular C k F) :
    ∃ f, GermIs C k F f := by
  letI := io.toAlgebra
  obtain ⟨σ, σt, hT1, hT2⟩ := hF
  obtain ⟨x', hx1, hx2, eL', heL'⟩ := hFT T io y C
  obtain ⟨σ', hσ'⟩ := exists_sec_id C.I.G (k : ℤ) σ (Over.mk (𝟙 (Sp T.V)))
  obtain ⟨fV, hfV⟩ := germSt_holds E H (Sp T.V) C.I.G T.V (𝟙 _) (chD C.ch) C.FT C.actT
    (Fin (chD C.ch)) C.tgT (fun j => Pi.single j (1 : T.V)) C.xT C.ph1T C.ph2T C.syT C.adT C.eT C.wPT
    C.chartT C.frameT C.primT hC k σ'
  refine ⟨fV, (isGerm_iff y.1 _ _ _ _ _ _ _ _).2
    (isGerm_of_sv ((isChart_iff y.1 _ _ _ _ _).1 C.ch.chart) C.ch.prim.1 C.ch.frame.gen fun m z J hJ => ?_)⟩
  obtain ⟨J', hJ', -⟩ := exists_good C.I.t'.PP.L C.I.t'.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  obtain ⟨J'', hJ'', -⟩ := exists_good C.I.G.PP.L C.I.G.PP.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  let ρ : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.V (Fin 1 × Fin (chD C.ch)) m) :=
    spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin (chD C.ch)) m)
  let i : Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) ⟶ Sp (Jet T.Fr (Fin 1 × Fin (chD C.ch)) m) := 𝟙 _
  obtain ⟨f₁, f₂⟩ := heL' m _ i z J J' J'' hJ hJ' hJ''
  have a₁ := hT1 _ (i ≫ (x' m).left) (i ≫ jetPt (C.ch.x m))
    ((Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((jetPt_snd (C.ch.x m)).trans (hx1 m).symm)).trans
      (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((jetPt_fst (C.ch.x m)).trans
      ((Over.w (x' m)).trans (Category.comp_id _)).symm)).trans (Category.assoc _ _ _).symm)) z J J' hJ hJ'
  have a₂ := hT2 _ (i ≫ (x' m).left) z J'' J' hJ'' hJ'
  have a₃ := sv_of_isGerm hfV m (i ≫ ρ) z hJ''
  have a₄ := hσ' _ ((i ≫ ρ) ≫ jetPt (C.xT m)) z J'' hJ''
  have b : ((i ≫ ρ) ≫ jetPt (C.xT m)) ≫ (snd (Over.mk (𝟙 (Sp T.V))) C.I.G.G).left =
      (i ≫ (x' m).left) ≫ C.I.m2.φ :=
    (Category.assoc _ _ _).trans ((congrArg ((i ≫ ρ) ≫ ·) (jetPt_snd (C.xT m))).trans ((Category.assoc _ _ _).trans
      ((congrArg (i ≫ ·) (hx2 m).symm).trans (Category.assoc _ _ _).symm)))
  have a₅ := (congrArg (fun q => sval σ q z J'') b).symm.trans (a₄.symm.trans a₃)
  refine (tie_alg a₁ a₂ a₅ f₁ f₂).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [psJet_map]
  exact gs_spMap_toΓ _ i z _

end Chart

theorem regular_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ) (F : SecN Xo (xOf y) k), (Regular C k F → ∃ f, GermIs C k F f) ∧ (∀ f f', GermIs C k F f → GermIs C k F f' → f = f') ∧ ∀ (F' : SecN Xo (xOf y) k) (r : T.V) (f : PS T.V 1 (chD C.ch)), (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo (xOf y)) (toΓ T.Fr (algebraMap T.V T.Fr r)) * F.f j) → GermIs C k F f → GermIs C k F' (r • f) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hC k F
  exact ⟨exists_germIs (GlobalTheory.PlaceInt.frameTie_holds E H Dw l Xo c hstar) C hC k F, germIs_unique C k F, germIs_smul C k F⟩

end GlobalTheory.RegularGerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScaleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_section_integral_germ_unique_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (k : ℕ) (F : SecN Xo (xOf y) k), (Regular C k F → ∃ f, GermIs C k F f) ∧ (∀ f f', GermIs C k F f → GermIs C k F f' → f = f') ∧ ∀ (F' : SecN Xo (xOf y) k) (r : T.V) (f : PS T.V 1 (chD C.ch)), (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo (xOf y)) (toΓ T.Fr (algebraMap T.V T.Fr r)) * F.f j) → GermIs C k F f → GermIs C k F' (r • f) := by
  first | exact @GlobalTheory.RegularGerm.regular_germ | exact GlobalTheory.RegularGerm.regular_germ | (intros; apply GlobalTheory.RegularGerm.regular_germ <;> assumption)
end
