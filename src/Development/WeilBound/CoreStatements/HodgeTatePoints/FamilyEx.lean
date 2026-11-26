module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.MapFirstPower
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CocpMain
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CdFrame

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CdAffine
noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem germ_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ z : X0, ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧ Nonempty (GermAt t j d) := by
  intro E _ _ _ H _ hs X0 t hp z
  obtain ⟨S, _, x0, d, G, A, tg, x, c, hj, hz, hc, ht, hb, hU⟩ := chart_affine E H X0 t z
  obtain ⟨e, ph1, ph2, sy, ad, hfr, htr, hfa, had⟩ := frame_affine E H X0 t S x0 d G A tg _ x c hc hU
  obtain ⟨hax, hr⟩ := FBIdAd.fbId E H X0 t hp hs S x0 _ G A _ tg _ x e ph1 ph2 sy ad hc hfr hfa had
  exact ⟨S, _, x0, d, hj, hz, ⟨⟨mkFB G A ph1 ph2 sy ad hax hr, x, e, tg, hc, ht, hb, hfr, htr, hfa⟩⟩⟩

end PositivityTheory.HtPt.Cd
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.ActGeneratorZero
noncomputable section
namespace PositivityTheory.HtPt.Cd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Gen
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw comp1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {X0 : Scheme.{0}}
  {t : SAB H X0} {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d n : ℕ}

theorem aug_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S) :
    (jetAug : Jet S κ m →ₐ[S] S) (psJet m f) = MvPowerSeries.constantCoeff f := by
  show MvPolynomial.aeval (fun _ => (0 : S)) (psTrunc m f) = _
  rw [MvPolynomial.aeval_zero', ← FBIdPh.cc_psTrunc m f]; rfl

theorem aug_jQ {k : ℕ} (m : ℕ) (b : Fin k → Q S d n) :
    (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S).comp (jQ m b) = jetAug :=
  jet_hom_ext fun s => by
    rw [AlgHom.comp_apply, jQ_X, aug_psJet, GermB.jetAug_X]; exact (b s.1).2 s.2

theorem trunc_jQ {k : ℕ} (m : ℕ) (b : Fin k → Q S d n) :
    (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] _).comp (jQ (m + 1) b) = (jQ m b).comp jetTrunc :=
  jet_hom_ext fun s => by
    rw [AlgHom.comp_apply, jQ_X, FrRatio.psJet_trunc, AlgHom.comp_apply, jetTrunc_mk, jQ_X]

theorem act_generator_zero (A : Q S d 1) : ac A (gen 0) = A :=
  Subtype.ext (funext fun i => (congrArg (sb · (A.1 i)) (funext fun j => by fin_cases j; rfl)).trans (sb_gen _))

theorem ac_zero (A : Q S d 1) : ac A (0 : Q S d n) = 0 := Subtype.ext (funext fun i => by
  have e := TB.LogPf.ev_zeroFam (n := n) (A.1 i)
  rw [A.2 i, map_zero] at e
  exact ((sb_apply _ _).trans (congrArg (ev · (A.1 i)) (funext fun j => by fin_cases j; rfl))).trans e)

variable (g g₂ : GermAt t x d)

theorem PP_inj {u v : Q S d n} (h : ∀ m, PP m g.x u = PP m g.x v) : u = v := by
  refine Subtype.ext (funext fun i => ps_ext fun m => ?_)
  have := (coord_aug g (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S) (ker_aug_pow _ m) (PP m g.x u) (by
    rw [PP, ← Category.assoc, Formalism.L2.Pj.homAt_comp, aug_jQ, g.chart.zero])).unique ⟨aug_jQ m ![u], rfl⟩ ⟨aug_jQ m ![v], h m⟩
  have e := AlgHom.congr_fun this (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
  rwa [jQ_X, jQ_X] at e

theorem exists_coord : ∃ φ : Q S d 1, ∀ m, g₂.x m = PP m g.x φ := by
  choose χ hχ using fun m => (coord_aug g (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) (ker_aug_pow _ m) (g₂.x m)
    (g₂.chart.zero m)).exists
  have tr : ∀ m, (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp jetTrunc = jetAug := fun m =>
    jet_hom_ext fun s => by rw [AlgHom.comp_apply, jetTrunc_mk, GermB.jetAug_X, GermB.jetAug_X]
  have hc : ∀ m, (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (χ (m + 1)) = (χ m).comp jetTrunc := fun m => by
    refine (coord_aug g (m := m + 1) (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S)
      (le_bot_iff.1 ((Ideal.pow_le_pow_right (Nat.le_succ _)).trans (ker_aug_pow _ m).le)) (g₂.x m) (g₂.chart.zero m)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [← AlgHom.comp_assoc, tr, (hχ (m + 1)).1]
    · rw [← Formalism.L2.Pj.homAt_comp, Category.assoc, ← (hχ (m + 1)).2, g₂.chart.trunc]
    · rw [← AlgHom.comp_assoc, (hχ m).1, tr]
    · rw [← Formalism.L2.Pj.homAt_comp, Category.assoc, g.chart.trunc, ← (hχ m).2]
  choose φ hφ using fun i : Fin d => exists_ps_of_jets
    (fun m => χ m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))) (fun m => AlgHom.congr_fun (hc m) _)
  have h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := fun i => by
    rw [← aug_psJet 0, hφ, ← AlgHom.comp_apply, (hχ 0).1, GermB.jetAug_X]
  refine ⟨⟨φ, h0⟩, fun m => (hχ m).2.trans ?_⟩
  rw [PP]
  congr 2
  refine jet_hom_ext fun s => ?_
  obtain ⟨j, s⟩ := s
  obtain rfl := Subsingleton.elim j 0
  rw [jQ_X]
  exact (hφ s m).symm

variable {g g₂} {φ : Q S d 1} (hφ : ∀ m, g₂.x m = PP m g.x φ)
include hφ

theorem PP_coord (m : ℕ) (u : Q S d n) : PP m g₂.x u = PP m g.x (ac φ u) := by
  rw [PP, hφ, PP_sq]; rfl

theorem coord_op (u v : Q S d n) : ac φ (op (FQ g₂.B.G) u v) = op (FQ g.B.G) (ac φ u) (ac φ v) :=
  PP_inj g fun m => by rw [← PP_coord hφ, PP_op g₂.chart, PP_op g.chart, PP_coord hφ, PP_coord hφ]

theorem coord_ac (a : 𝓞 E) (u : Q S d n) : ac φ (ac (AQ g₂.B.A a) u) = ac (AQ g.B.A a) (ac φ u) :=
  PP_inj g fun m => by rw [← PP_coord hφ, PP_ac g₂.chart, PP_ac g.chart, PP_coord hφ]

theorem coord_inv {ψ : Q S d 1} (hψ : ∀ m, g.x m = PP m g₂.x ψ) : comp1 φ.1 ψ.1 = pt S (n := 1) d 0 := by
  have : ac φ (ac ψ (gen 0)) = (gen 0 : Q S d 1) := PP_inj g fun m => by rw [← PP_coord hφ, ← PP_coord hψ]
  rw [act_generator_zero] at this
  exact (ac_val φ ψ).symm.trans (congrArg Subtype.val this)

theorem coord_tan (l : Fin d) : IsCombAtG t x g.tg (fun j => lin φ.1 1 j l) (g₂.tg l) := by
  have e : jetSubstP 1 (fun p : Fin 1 × Fin d => psTrunc 1 (φ.1 p.2)) = jQ 1 ![φ] :=
    subst_eq 1 _ ![φ] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl)
      (fun s => (FBIdPh.cc_psTrunc 1 _).trans (φ.2 _))
  have e₂ : (fun j => lin φ.1 1 j l) = (lin φ.1 1).mulVec (Pi.single l 1) := by
    funext j; simp
  rw [comb_iff, tg_eq, tv_gd, tv_gd, hφ, PP, ← e, GlobalTheory.ChartCompare.hcomp, vec_subst, e₂]

theorem exists_lam : ∃ lam : PS S 2 d, ∀ {n m} {y : (jOG x d m n).left} {J}, Good t.PP.L y J → ∀ u v : Q S d n,
    VV m y (E2 lam u v) = (ee g₂.x g₂.e y J u v * (ee g.x g.e y J (ac φ u) (ac φ v))⁻¹).val := by
  let b : Fin 2 → Q S d 2 := ![ac φ (gen 0), ac φ (gen 1)]
  have hb : ∀ m (i : Fin 2), homAt x (jQ m b) ≫ jptG t x d g.x m i = jptG t x d g₂.x m i := fun m i => by
    rw [PP_gen, PP_gen, PP_sq, sq_gen, PP_coord hφ]
    fin_cases i <;> rfl
  obtain ⟨lam, hlam⟩ := GermB.exists_series t x d (n := 2)
    (fun m => cφG t ![jptG t x d g₂.x m (0 : Fin 2), jptG t x d g₂.x m (1 : Fin 2)]) (cε 2) _ (cε 2)
    (fun m => g₂.e m) g₂.frame.gen
    (fun m => LB.pullGen t.PP.L (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cε 2) (g.e m)
      (homAt x (jQ m b)).left)
    (fun m => pullGen_isGen _ _ _ _ (g.frame.gen m) _)
    (fun m U _ h => Finset.prod_congr rfl fun I _ => by rw [GermB.pe_pt, hb, hb]; rfl)
    (fun m y J hJ => (congrArg (fun r => val (g₂.e (m + 1)) r y J) (Category.id_comp _).symm).trans
      ((val_pull hJ _ _ _).symm.trans (val_corr hJ (g₂.trunc m) _)))
    (fun m y J hJ => by
      have hs : (GermB.ρn x d 2 m).left ≫ (homAt x (jQ (m + 1) b)).left =
          (𝟙 _ ≫ (homAt x (jQ m b)).left) ≫ (GermB.ρn x d 2 m).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, Formalism.L2.Pj.homAt_comp, Formalism.L2.Pj.homAt_comp, trunc_jQ]
      exact (val_pull hJ (g.e (m + 1)) _ _).trans ((congrArg (fun r => val (g.e (m + 1)) r y J) hs).trans
        ((val_pull hJ (g.e (m + 1)) _ _).symm.trans ((val_corr hJ (g.trunc m) _).trans (val_pull hJ (g.e m) _ _).symm))))
  refine ⟨lam, fun {n m y J} hJ u v => ?_⟩
  obtain ⟨U, hU, h⟩ := hlam m
  have hc := gm_unit (y := y) U ![u, v] _ hU
  have e₀ : val (LB.pullGen t.PP.L (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cε 2) (g.e m)
      (homAt x (jQ m b)).left) (homAt x (jQ m ![u, v])).left y J = ee g.x g.e y J (ac φ u) (ac φ v) := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [← Over.comp_left, Formalism.L2.Pj.homAt_comp, jQ_comp]
    exact congrArg (fun a => val (L := t.PP.L)
      (φ := cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)])
      (ε := cε 2) (g.e m) (homAt x (jQ m a)).left y J) (funext fun j => by
        fin_cases j
        · exact (sq_ac _ _ _).trans (congrArg (ac φ) (sq_gen _ _))
        · exact (sq_ac _ _ _).trans (congrArg (ac φ) (sq_gen _ _)))
  have k : ee g₂.x g₂.e y J u v = _ * ee g.x g.e y J (ac φ u) (ac φ v) :=
    (val_corr hJ h _).trans ((FBIdAd.val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl e₀))
  exact hc.symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

omit hφ in
theorem exists_dA (hs : ∀ a : 𝓞 E, star a = H.bar a) (g : GermAt t x d) (a : 𝓞 E) :
    ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
      (∀ {n m} {y : (jOG x d m n).left} {J}, Good t.PP.L y J → ∀ u v : Q S d n, VV m y (E2 (g.B.ad a) u v) =
        (val₂ wL y J (PP m g.x u) (PP m g.x v) * ee g.x g.e y J (ac (AQ g.B.A a) u) v *
          (ee g.x g.e y J u (ac (AQ g.B.A (star a)) v))⁻¹).val) ∧
      ∀ {n m} {y : (jOG x d m n).left} {J}, Good t.PP.L y J → val₂ wL y J (1 : jOG x d m n ⟶ t.G) 1 = 1 := by
  obtain ⟨wL, hw, hU⟩ := g.frame.ad a
  have dA : ∀ {n m} {y : (jOG x d m n).left} {J}, Good t.PP.L y J → ∀ u v : Q S d n, VV m y (E2 (g.B.ad a) u v) =
        (val₂ wL y J (PP m g.x u) (PP m g.x v) * ee g.x g.e y J (ac (AQ g.B.A a) u) v *
          (ee g.x g.e y J u (ac (AQ g.B.A (star a)) v))⁻¹).val := fun {n m y J} hJ u v => by
    obtain ⟨U, h₁, h₂⟩ := hU m
    rw [hs]; exact dict_ad hJ a wL U h₁ h₂ u v
  refine ⟨wL, hw, dA, fun {n m y J} hJ => ?_⟩
  have k := dA hJ 0 0
  have z : E2 (g.B.ad a) (0 : Q S d n) 0 = 1 := by
    have e : E2 (g.B.ad a) (0 : Q S d 1) (gen 0) = 1 := (formalSeriesValueAtTwoPoints_eq_ev _ _ _).trans (g.B.adjoint_zero_fst a)
    have := congrArg (sb ![(0 : Q S d n)]) e
    rwa [formalPointSubstitutionSeries_valueAtTwoPoints, map_one, map_zero, sq_gen] at this
  rw [z, VV_one, ac0, ac0, mul_inv_cancel_right, PP_zero g.chart] at k
  exact Units.ext k.symm

omit hφ in
theorem val₂_eq (hp : PowFns t) {K : Type} [Fintype K] {ξ : K → ((t.G ⊗ t.G).left ⟶ t.G.left)} {ε : K → ℤ}
    {w w' : LB.Gen (LB.LinComb t.PP.L ξ ε)} (hw : w.IsGen) (hw' : w'.IsGen) {T : Over X0} {z : T.left} {J}
    (hJ : Good t.PP.L z J) (h : val₂ w z J (1 : T ⟶ t.G) 1 = 1) (h' : val₂ w' z J (1 : T ⟶ t.G) 1 = 1)
    (p q : T ⟶ t.G) : val₂ w z J p q = val₂ w' z J p q := by
  have key := ratio_pow (hp 3).2 t.PP.isLB (fun U _ h => rfl)
    (pullGen_isGen _ _ _ _ hw (lift (powPr t.G (0 : Fin 3)) (powPr t.G (2 : Fin 3))).left)
    (pullGen_isGen _ _ _ _ hw' (lift (powPr t.G (0 : Fin 3)) (powPr t.G (2 : Fin 3))).left) p p q hJ
  simpa only [val_ros _ _ hJ, tup_0, tup_2, h, h', _root_.mul_one] using key

set_option maxHeartbeats 2000000 in
theorem iso_of_coord (hs : ∀ a : 𝓞 E, star a = H.bar a) (hp : PowFns t) {ψ : Q S d 1}
    (hψ : ∀ m, g.x m = PP m g₂.x ψ) : ∃ lam, GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B g₂.B φ.1 ψ.1 lam := by
  have hL := t.PP.isLB
  obtain ⟨lam, dL⟩ := exists_lam hφ
  have g2 : ∀ f : PS S 2 d, ev (n := 2) ![pt S d 0, pt S d 1] f = f := fun f =>
    (formalSeriesValueAtTwoPoints_eq_ev f (gen 0) (gen 1)).symm.trans (formalSeriesValueAtTwoPoints_genericPoints f)
  have g3 : ∀ f : PS S 3 d, ev (n := 3) ![pt S d 0, pt S d 1, pt S d 2] f = f := fun f =>
    (formalSeriesValueAtThreePoints_eq_ev f (gen 0) (gen 1) (gen 2)).symm.trans (formalSeriesValueAtThreePoints_genericPoints f)
  refine ⟨lam, φ.2, ψ.2, coord_inv hφ hψ, coord_inv hψ hφ, ⟨?_, ?_⟩, ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have : E2 lam (0 : Q S d 1) (gen 0) = 1 := VV_ext (x0 := x) hL fun m y J hJ => by
      rw [dL hJ, VV_one, ac_zero, (dict_ax hJ g.axes _).1, (dict_ax hJ g₂.axes _).1]; simp
    exact (formalSeriesValueAtTwoPoints_eq_ev lam (0 : Q S d 1) (gen 0)).symm.trans this
  · have : E2 lam (gen 0 : Q S d 1) 0 = 1 := VV_ext (x0 := x) hL fun m y J hJ => by
      rw [dL hJ, VV_one, ac_zero, (dict_ax hJ g.axes _).2, (dict_ax hJ g₂.axes _).2]; simp
    exact (formalSeriesValueAtTwoPoints_eq_ev lam (gen 0 : Q S d 1) 0).symm.trans this
  · have := congrArg Subtype.val (coord_op hφ (gen 0 : Q S d 2) (gen 1))
    simpa only [op_val, ac_val, gen_val] using this
  · have := coord_ac hφ a (gen 0 : Q S d 1)
    rw [act_generator_zero, act_generator_zero] at this
    simpa only [ac_val] using congrArg Subtype.val this
  · have : E3 g₂.B.ph1 (gen 0 : Q S d 3) (gen 1) (gen 2) * E2 lam (op (FQ g₂.B.G) (gen 0) (gen 1)) (gen 2) =
        E2 lam (gen 0) (gen 2) * E2 lam (gen 1) (gen 2) *
          E3 g.B.ph1 (ac φ (gen 0)) (ac φ (gen 1)) (ac φ (gen 2)) := VV_ext (x0 := x) hL fun m y J hJ => by
      simp only [VV_mul, frame_biext_dictionary_first_partial_law hJ g.frame, frame_biext_dictionary_first_partial_law hJ g₂.frame, dL hJ, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [PP_coord hφ, coord_op hφ, ofMul_mul, ofMul_inv]
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, g3] using this
  · have : E3 g₂.B.ph2 (gen 0 : Q S d 3) (gen 1) (gen 2) * E2 lam (gen 0) (op (FQ g₂.B.G) (gen 1) (gen 2)) =
        E2 lam (gen 0) (gen 1) * E2 lam (gen 0) (gen 2) *
          E3 g.B.ph2 (ac φ (gen 0)) (ac φ (gen 1)) (ac φ (gen 2)) := VV_ext (x0 := x) hL fun m y J hJ => by
      simp only [VV_mul, frame_biext_dictionary_second_partial_law hJ g.frame, frame_biext_dictionary_second_partial_law hJ g₂.frame, dL hJ, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [PP_coord hφ, coord_op hφ, ofMul_mul, ofMul_inv]
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, g3] using this
  · have : E2 g₂.B.sy (gen 0 : Q S d 2) (gen 1) * E2 lam (gen 0) (gen 1) =
        E2 g.B.sy (ac φ (gen 0)) (ac φ (gen 1)) * E2 lam (gen 1) (gen 0) := VV_ext (x0 := x) hL fun m y J hJ => by
      simp only [VV_mul, dict_sy hJ g.frame, dict_sy hJ g₂.frame, dL hJ, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, g2] using this
  · obtain ⟨w, hw, dA, h1⟩ := exists_dA hs g a
    obtain ⟨w₂, hw₂, dA₂, h1₂⟩ := exists_dA hs g₂ a
    have : E2 (g₂.B.ad a) (gen 0 : Q S d 2) (gen 1) * E2 lam (gen 0) (ac (AQ g₂.B.A (star a)) (gen 1)) =
        E2 lam (ac (AQ g₂.B.A a) (gen 0)) (gen 1) * E2 (g.B.ad a) (ac φ (gen 0)) (ac φ (gen 1)) :=
      VV_ext (x0 := x) hL fun m y J hJ => by
        simp only [VV_mul, dA hJ, dA₂ hJ, dL hJ, ← Units.val_mul]
        refine congrArg Units.val (Additive.ofMul.injective ?_)
        simp only [PP_coord hφ, coord_ac hφ, ofMul_mul, ofMul_inv]
        rw [val₂_eq hp hw₂ hw hJ (h1₂ hJ) (h1 hJ)]
        abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, g2] using this

end Gen

theorem germ_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g g₂ : GermAt t x d), ∃ (φ ψ : Germ.Pt S 1 d) (lam : Germ.PS S 2 d), IsIso g.B g₂.B φ ψ lam ∧ ∀ l, IsCombAtG t x g.tg (fun j => lin φ 1 j l) (g₂.tg l) := by
  intro E _ _ _ H _ hs X0 t hp S _ _ x d g g₂
  obtain ⟨φ, hφ⟩ := exists_coord g g₂
  obtain ⟨ψ, hψ⟩ := exists_coord g₂ g
  obtain ⟨lam, h⟩ := iso_of_coord hφ hs hp hψ
  exact ⟨φ.1, ψ.1, lam, h, coord_tan hφ⟩

end PositivityTheory.HtPt.Cd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentPowerFreeConjInjective
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentPowerFreeConjInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.tangent_power_free_conj_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), TanPF t x p → ConjInj g.B p := by
  first | exact @PositivityTheory.HtPt.Cocp.tanpf_inj | exact PositivityTheory.HtPt.Cocp.tanpf_inj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentPowerFreeConjInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_power_free_conj_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), TanPF t x p → ConjInj g.B p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tangent_power_free_conj_injective | exact GlobalTheory.CompanionTheory.Relay.tangent_power_free_conj_injective | (intros; apply GlobalTheory.CompanionTheory.Relay.tangent_power_free_conj_injective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricToTangentPowerFree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricToTangentPowerFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.geometric_to_tangent_power_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0), GeomPF t x → TanPF t x p := by
  first | exact @PositivityTheory.HtPt.Ce.geompf_tan | exact PositivityTheory.HtPt.Ce.geompf_tan
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricToTangentPowerFreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_to_tangent_power_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0), GeomPF t x → TanPF t x p := by
  first | exact @GlobalTheory.CompanionTheory.Relay.geometric_to_tangent_power_free | exact GlobalTheory.CompanionTheory.Relay.geometric_to_tangent_power_free | (intros; apply GlobalTheory.CompanionTheory.Relay.geometric_to_tangent_power_free <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormalGermOpenAffine
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormalGermOpenAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_formal_germ_open_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ z : X0, ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧ Nonempty (GermAt t j d) := by
  first | exact @PositivityTheory.HtPt.Cd.germ_affine | exact PositivityTheory.HtPt.Cd.germ_affine
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormalGermOpenAffineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formal_germ_open_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ z : X0, ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧ Nonempty (GermAt t j d) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_formal_germ_open_affine | exact GlobalTheory.CompanionTheory.Relay.exists_formal_germ_open_affine | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_formal_germ_open_affine <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermsIsomorphic
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermsIsomorphic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem germ_iso_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g g₂ : GermAt t x d), ∃ (φ ψ : Germ.Pt S 1 d) (lam : Germ.PS S 2 d), IsIso g.B g₂.B φ ψ lam ∧ ∀ l, IsCombAtG t x g.tg (fun j => lin φ 1 j l) (g₂.tg l) :=
  @PositivityTheory.HtPt.Cd.germ_iso

end GlobalTheory.CompanionTheory.Ar.Conj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermsIsomorphicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_germs_isomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g g₂ : GermAt t x d), ∃ (φ ψ : Germ.Pt S 1 d) (lam : Germ.PS S 2 d), IsIso g.B g₂.B φ ψ lam ∧ ∀ l, IsCombAtG t x g.tg (fun j => lin φ 1 j l) (g₂.tg l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main | exact GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.IsMapOfCancel
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CcInjAlg
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

theorem mulVec_injective_map_iff {k k₂ m n : Type} [Field k] [Field k₂] [Fintype m] [Fintype n] (f : k →+* k₂)
    (M : Matrix m n k) : Function.Injective (M.map f).mulVec ↔ Function.Injective M.mulVec := by
  letI := f.toAlgebra
  rw [Matrix.mulVec_injective_iff, Matrix.mulVec_injective_iff]
  exact linearIndependent_algebraMap_comp_iff (R := k) (S := k₂) (v := M.col)

theorem conjInj_iff_fromRows {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
    (p : ℕ) : ConjInj B p ↔ Function.Injective (Matrix.fromRows (hw B p) (am B p).transpose).mulVec := by
  have e : (Matrix.fromRows (hw B p) (am B p).transpose).mulVec =
      (Equiv.sumArrowEquivProdArrow (Fin d) (Fin d) R).symm ∘ alpha B p := by
    funext u
    rw [Matrix.fromRows_mulVec, Function.comp_apply, alpha_apply]
    rfl
  rw [e, Equiv.comp_injective, ConjInj]

theorem conjInj_map {k k₂ : Type} [Field k] [Field k₂] {f : k →+* k₂} {d : ℕ} {O : Type} [CommRing O] [StarRing O]
    {B : FB k d O} {B₂ : FB k₂ d O} (h : IsMapOf f B B₂) (p : ℕ) : ConjInj B₂ p ↔ ConjInj B p := by
  obtain ⟨h1, h2⟩ := (map_mats k k₂ f d O B B₂ h).2.2 p
  rw [conjInj_iff_fromRows, conjInj_iff_fromRows, ← mulVec_injective_map_iff f, h1, h2, Matrix.fromRows_map,
    Matrix.transpose_map]

end PositivityTheory.HtPt.Cc
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cf

theorem fib_inj_of (htan : type_of% @GlobalTheory.T.geometric_to_tangent_power_free) (hbc : type_of% @GlobalTheory.T.formal_germ_base_change)
    (hinj : type_of% @GlobalTheory.T.tangent_power_free_conj_injective) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p := by
  intro E _ _ _ H _ hs X0 t hP k _ p _ _ x d g ⟨k', _, _, x', hx, h⟩
  obtain ⟨Ω, _, _, y, a, -, e⟩ := exists_common x (IsLocalRing.closedPoint k) x' hx
  obtain ⟨b, rfl⟩ : ∃ b : k →+* Ω, y = spMap b := ⟨(Spec.preimage y).hom, (Spec.map_preimage y).symm⟩
  have : CharP Ω p := charP_of_injective_ringHom b.injective p
  have h' : GeomPF t (spMap b ≫ x) := e ▸ (geompf_bc E H X0 t).1 k' Ω a x' h
  obtain ⟨g₂, hg, -⟩ := hbc E H hs X0 t k Ω b x d g
  exact (PositivityTheory.HtPt.Cc.conjInj_map hg p).1 (hinj E H hs X0 t Ω p _ d g₂ (htan E H hs X0 t hP Ω p _ h'))

theorem isMapOf_cancel {R R₂ R₃ O : Type} [CommRing R] [CommRing R₂] [CommRing R₃] [CommRing O] [StarRing O] {d : ℕ}
    {f : R →+* R₂} {g : R₂ →+* R₃} {B : Germ.FB R d O} {B₂ : Germ.FB R₂ d O} {B₃ : Germ.FB R₃ d O}
    (h : IsMapOf f B B₂) (h' : IsMapOf (g.comp f) B B₃) : IsMapOf g B₂ B₃ := by
  exact
    { F := fun i => by simp only [h'.F i, h.F i, MvPowerSeries.map_comp, RingHom.comp_apply]
      act := fun a i => by simp only [h'.act a i, h.act a i, MvPowerSeries.map_comp, RingHom.comp_apply]
      ph1 := by simp only [h'.ph1, h.ph1, MvPowerSeries.map_comp, RingHom.comp_apply]
      ph2 := by simp only [h'.ph2, h.ph2, MvPowerSeries.map_comp, RingHom.comp_apply]
      sy := by simp only [h'.sy, h.sy, MvPowerSeries.map_comp, RingHom.comp_apply]
      ad := fun a => by simp only [h'.ad a, h.ad a, MvPowerSeries.map_comp, RingHom.comp_apply] }

theorem spMap_comp' {R R₂ R₃ : Type} [CommRing R] [CommRing R₂] [CommRing R₃] (f : R →+* R₂) (g : R₂ →+* R₃) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem dualMap_comp' {R R₂ R₃ : Type} [CommRing R] [CommRing R₂] [CommRing R₃] (f : R →+* R₂) (g : R₂ →+* R₃) :
    (GlobalTheory.CompanionTheory.Ar.dualMap g).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) = GlobalTheory.CompanionTheory.Ar.dualMap (g.comp f) := by
  ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem exists_factor {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] {X : Scheme.{0}} (x : Sp R ⟶ X)
    (j : Sp A ⟶ X) [IsOpenImmersion j] (h : GlobalTheory.CompanionTheory.Ar.centre x ∈ Set.range j) : ∃ a : A →+* R, x = spMap a ≫ j := by
  have hr : Set.range x ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint q).map x.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j x hr)).hom, ?_⟩
  show x = Spec.map (Spec.preimage (IsOpenImmersion.lift j x hr)) ≫ j
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem finite_nonint {K : Type} [Field K] (C : ACurve K) (x : K) : {i | ¬ C.v i x ≤ 1}.Finite := by
  by_cases h : x = 0
  · simp [h]
  · exact (C.fin x h).subset fun i hi e => hi e.le

theorem family_ex_of' (hfib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p)
    (hbc : type_of% @GlobalTheory.T.formal_germ_base_change) (huniv : type_of% @GlobalTheory.T.formal_germ_dimension_unique) (hiso : type_of% @GlobalTheory.T.formal_germs_isomorphic)
    (haff : type_of% @GlobalTheory.T.exists_formal_germ_open_affine) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
  intro E _ _ _ H _ hs X0 t hP K _ p _ _ C z Y hY
  have bc : ∀ {S S₂ : Type} [CommRing S] [CommRing S₂] (f : S →+* S₂) {x : Sp S ⟶ X0} {x₂ : Sp S₂ ⟶ X0}
      (_ : x₂ = spMap f ≫ x) {d : ℕ} (g : GermAt t x d), ∃ g₂ : GermAt t x₂ d, IsMapOf f g.B g₂.B ∧
        ∀ l, g₂.tg l = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
    intro S S₂ _ _ f x x₂ e d g
    subst e
    exact hbc E H hs X0 t S S₂ f x d g
  obtain ⟨A, _, j, d, _, hj, ⟨gA⟩⟩ := haff E H hs X0 t hP (GlobalTheory.CompanionTheory.Ar.centre z)
  obtain ⟨a, ha⟩ := exists_factor z j hj
  obtain ⟨g, hg, hgt⟩ := bc a ha gA
  obtain ⟨φ₀, ψ₀, lam₀, h₀, h₀t⟩ := hiso E H hs X0 t hP K z d g g
  have loc : ∀ i : C.I, ∃ (gi : GermAt t (Y.x i) d) (BK : Germ.FB K d (𝓞 E)) (φ ψ : Germ.Pt K 1 d)
      (lam : Germ.PS K 2 d), IsMapOf (C.v i).valuationSubring.subtype gi.B BK ∧ GlobalTheory.CompanionTheory.Ar.Conj.IsIso g.B BK φ ψ lam ∧
      (GlobalTheory.CompanionTheory.Ar.centre (Y.x i) ∈ Set.range j → φ = φ₀ ∧ ψ = ψ₀ ∧ lam = lam₀) ∧
      ∀ l, IsCombAtG t z g.tg (fun j => lin φ 1 j l)
        (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
    intro i
    by_cases hi : GlobalTheory.CompanionTheory.Ar.centre (Y.x i) ∈ Set.range j
    · obtain ⟨b, hb⟩ := exists_factor (Y.x i) j hi
      obtain ⟨gi, hgi, hgit⟩ := bc b hb gA
      have e : spMap ((C.v i).valuationSubring.subtype.comp b) = spMap a := by
        rw [← cancel_mono j, ← ha, ← spMap_comp', Category.assoc, ← hb]
        exact Y.gen i
      obtain rfl : (C.v i).valuationSubring.subtype.comp b = a :=
        congrArg CommRingCat.Hom.hom (Spec.map_injective e)
      refine ⟨gi, g.B, φ₀, ψ₀, lam₀, isMapOf_cancel hgi hg, h₀, fun _ => ⟨rfl, rfl, rfl⟩, fun l => ?_⟩
      rw [hgit, ← Category.assoc, spMap_comp', dualMap_comp', ← hgt]
      exact h₀t l
    · obtain ⟨d', ⟨gi⟩⟩ := PositivityTheory.HtPt.Cd.germ_local E H hs X0 t hP _ (Y.x i)
      obtain ⟨g₂, hg₂, hg₂t⟩ := bc (C.v i).valuationSubring.subtype (Y.gen i).symm gi
      obtain rfl := (huniv E H hs X0 t K z d g).1 d' g₂
      obtain ⟨φ, ψ, lam, h, ht⟩ := hiso E H hs X0 t hP K z d g g₂
      exact ⟨gi, g₂.B, φ, ψ, lam, hg₂, h, fun h' => absurd h' hi, fun l => hg₂t l ▸ ht l⟩
  choose gi BK φ ψ lam hK hI hgood ht using loc
  have red : ∀ i : C.I, ∃ Bk : Germ.FB (IsLocalRing.ResidueField (C.v i).valuationSubring) d (𝓞 E),
      IsMapOf (IsLocalRing.residue _) (gi i).B Bk ∧ ConjInj Bk p := by
    intro i
    obtain ⟨gk, hk, -⟩ := bc (IsLocalRing.residue _) rfl (gi i)
    have h0 : (p : (C.v i).valuationSubring) = 0 := Subtype.ext (by simp)
    have : CharP (IsLocalRing.ResidueField (C.v i).valuationSubring) p :=
      (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
        rw [← map_natCast (IsLocalRing.residue (C.v i).valuationSubring), h0, map_zero])
    refine ⟨gk.B, hk, hfib E H hs X0 t hP _ p _ d gk ?_⟩
    have e : (spMap (IsLocalRing.residue (C.v i).valuationSubring) ≫ Y.x i) (IsLocalRing.closedPoint _) =
        GlobalTheory.CompanionTheory.Ar.centre (Y.x i) :=
      (Scheme.Hom.comp_apply _ _ _).trans (congrArg (Y.x i) (IsLocalRing.comap_closedPoint (IsLocalRing.residue _)))
    exact e ▸ hY i
  choose Bk hk hinj using red
  refine ⟨d, ⟨g.B, fun i => (gi i).B, BK, Bk, hK, hk, hinj, φ, ψ, lam, hI, ?_⟩, g, rfl, fun i => ⟨gi i, ht i⟩⟩
  refine ((Y.ae j.opensRange hj).union (Set.finite_iUnion fun a : Fin d => Set.finite_iUnion fun b : Fin d =>
    (finite_nonint C (lin φ₀ 1 a b)).union ((finite_nonint C (lin ψ₀ 1 a b)).union
      (finite_nonint C (bil lam₀ 1 1 a b))))).subset fun i hi => ?_
  by_cases hc : GlobalTheory.CompanionTheory.Ar.centre (Y.x i) ∈ Set.range j
  · obtain ⟨e₁, e₂, e₃⟩ := hgood i hc
    rw [Set.mem_ofPred_eq, e₁, e₂, e₃] at hi
    simp only [not_forall, not_and_or] at hi
    obtain ⟨a, b, h⟩ := hi
    exact Or.inr (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨b, h⟩⟩)
  · exact Or.inl hc

theorem family_ex_of (htan : type_of% @GlobalTheory.T.geometric_to_tangent_power_free)
    (hbc : type_of% @GlobalTheory.T.formal_germ_base_change) (hinj : type_of% @GlobalTheory.T.tangent_power_free_conj_injective)
    (haff : type_of% @GlobalTheory.T.exists_formal_germ_open_affine) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) :=
  family_ex_of' (fib_inj_of htan hbc hinj) hbc PositivityTheory.HtPt.Cd.germ_univ PositivityTheory.HtPt.Cd.germ_iso haff

end PositivityTheory.HtPt.Cf
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cf

theorem fib_inj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d), FibPF t (x (IsLocalRing.closedPoint k)) → ConjInj g.B p :=
  fib_inj_of PositivityTheory.HtPt.Ce.geompf_tan PositivityTheory.HtPt.Ce.germ_bc PositivityTheory.HtPt.Cocp.tanpf_inj

theorem family_ex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) :=
  family_ex_of PositivityTheory.HtPt.Ce.geompf_tan PositivityTheory.HtPt.Ce.germ_bc PositivityTheory.HtPt.Cocp.tanpf_inj PositivityTheory.HtPt.Cd.germ_affine

end PositivityTheory.HtPt.Cf
