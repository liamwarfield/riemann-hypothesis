module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FFVMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.BiextensionDepthLeOfRelated
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioFirstPartialLaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SvalValueAt
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh GlobalTheory.FrameBiextId

namespace GlobalTheory.ChartField

section Sections
variable {X Z : Scheme.{0}} {A : Over X} [GrpObj A] {L : LB A.left} {T T' : Over X}

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ (ptSecT A x).left) z J =
      gs r z ⊤ v * (val τ r z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) r
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ (ptSecT A x).left) z J
    (fun _ => J (r ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs r z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull r (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ x.left))) (val_le A L x _ hy) _)).symm

theorem sval_pull {a : ℤ} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A} {s : LB.Sec (LPow A L a T)}
    {s' : LB.Sec (LPow A L a T')} (H : IsPullSec A L a h hh s s') (r : Z ⟶ (T' ⊗ A).left) {z : Z} {J}
    (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T' A).left) (ε := fun _ => a) s' r z J =
      sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ h.left) z J := by
  have hy := hJ.mem (fun _ : Fin 1 => (snd T' A).left) r
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ h.left) z J
    (fun _ => J (r ≫ (snd T' A).left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, hh])]
  refine (congrArg (gs r z _) (H _)).trans ((gs_res _ z _ hy _).trans ?_)
  exact gs_pull r h.left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (r ≫ (snd T' A).left)))
    (chart_le_res A L h hh a _ hy) _

end Sections

variable {S : Type} [CommRing S] {d : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
  {x0 : Sp S ⟶ X0} {x x' : ∀ m, jOG x0 d m 1 ⟶ t.G}

theorem germ_val {G : FGLaw S d} (A : Germ.OAct (𝓞 E) G) {e : ∀ m, FrTyG t x0 d x m} {wP : PrimTyG t} {k : ℕ}
    {F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))} {f : PS S 1 d} (h : IsGermG t x0 d x A.act e wP k F f)
    {m n : ℕ} {y : (jOG x0 d m n).left} {J} (hJ : Good t.PP.L y J) (u : Q S d n) :
    sval (φ := fun _ : Fin 1 => (snd (Over.mk x0) t.G).left) (ε := fun _ => (k : ℤ)) F
        (lift (jBaseG x0 d m n) (PP m x u)).left y J =
      VV m y (sb ![u] f) * ((val wP (PP m x u).left y J * ee x e y J u (ac (AQ A H.w0) u)) ^ k).val := by
  obtain ⟨F', τ, h1, h2, h3⟩ := h m
  have v := sval_valueAt h3 (Formalism.L2.Pj.homAt x0 (jQ m ![u])).left hJ
  rw [sval_pull h1 _ hJ] at v
  have e1 : ((Formalism.L2.Pj.homAt x0 (jQ m ![u])).left ≫ (ptSecT t.G (x m)).left) ≫ (jBaseG x0 d m 1 ▷ t.G).left =
      (lift (jBaseG x0 d m n) (PP m x u)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, whiskerRight_fst, ptSecT, lift_fst_assoc, Category.id_comp, lift_fst]
      exact Over.OverMorphism.ext (spMap_comp_alg _)
    · simp only [Category.assoc, whiskerRight_snd, ptSecT, lift_snd, PP]
  rw [e1] at v
  have e₀ := val_peG x hJ e ![u] ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn d m ![0] (A.act H.w0 j)]
    (gen 0) (ac (AQ A H.w0) (gen 0)) (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, hA _ 0 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, (cc_psIn d m _ _).trans (A.const _ j)])
  rw [sq_ac, sq_gen] at e₀
  refine v.trans (congrArg₂ (· * ·) ?_ (congrArg Units.val ((val_corr hJ h2 _).trans ((map_pow _ _ _).trans
    (congrArg (· ^ k) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) e₀)))))))
  rw [VV, ← jQ_psJet]
  refine Eq.trans ?_ (cst_comp (𝟙 _) (jQ m ![u] : Jet S (Fin 1 × Fin d) m →+* Jet S (Fin n × Fin d) m) y _)
  rw [Category.id_comp]; rfl

theorem exists_ratio (Φ : Q S d 1) (hco : ∀ m n (u : Q S d n), PP m x' u = PP m x (ac Φ u))
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x0 d x' m) (he : ∀ m, (e m).IsGen) (he' : ∀ m, (e' m).IsGen)
    (m : ℕ) : ∃ ε : PS S 2 d, IsUnit (MvPowerSeries.constantCoeff ε) ∧
      ∀ n (y : (jOG x0 d m n).left) J, Good t.PP.L y J → ∀ u v : Q S d n,
        VV m y (E2 ε u v) = (ee x' e' y J u v * (ee x e y J (ac Φ u) (ac Φ v))⁻¹).val := by
  let b : Fin 2 → Q S d 2 := ![ac Φ (gen 0), ac Φ (gen 1)]
  have hfam : cφG t ![jptG t x0 d x' m (0 : Fin 2), jptG t x0 d x' m (1 : Fin 2)] =
      fun I => (Formalism.L2.Pj.homAt x0 (jQ m b)).left ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
    funext I
    rw [cφG, cφG, ← Over.comp_left, FrameRatio.comp_psum']
    congr 2
    funext k
    fin_cases k
    · show jptG t x0 d x' m 0 = _ ≫ jptG t x0 d x m 0
      rw [PP_gen, PP_gen, PP_sq, sq_gen, hco]; rfl
    · show jptG t x0 d x' m 1 = _ ≫ jptG t x0 d x m 1
      rw [PP_gen, PP_gen, PP_sq, sq_gen, hco]; rfl
  obtain ⟨U, hU⟩ := FrameRatio.exists_corr_scaled t.PP.L t.PP.isLB _ _ hfam (cε 2) (e' m)
    (LB.pullGen t.PP.L _ _ (e m) (Formalism.L2.Pj.homAt x0 (jQ m b)).left) (he' m) (DVR.pullGen_isGen _ _ _ _ (he m) _)
  obtain ⟨u, rfl⟩ := FrameRatio.unitΓ_surj U
  obtain ⟨ε, hε⟩ := FrameRatio.psJet_surj m (u : Jet S (Fin 2 × Fin d) m)
  refine ⟨ε, ?_, fun n y J hJ p q => ?_⟩
  · rw [← GaugeR.jetAug_psJet m ε, hε]
    exact u.isUnit.map _
  · have e₀ : val (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m)
        (Formalism.L2.Pj.homAt x0 (jQ m b)).left) (Formalism.L2.Pj.homAt x0 (jQ m ![p, q])).left y J =
        ee x e y J (ac Φ p) (ac Φ q) := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [← Over.comp_left, GermD.homAt_comp, jQ_comp]
      refine congrArg (fun a => val (L := t.PP.L)
        (φ := cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (ε := cε 2) (e m)
        (Formalism.L2.Pj.homAt x0 (jQ m a)).left y J) (funext fun j => ?_)
      fin_cases j
      · exact (sq_ac _ _ _).trans (congrArg (ac Φ) (sq_gen _ _))
      · exact (sq_ac _ _ _).trans (congrArg (ac Φ) (sq_gen _ _))
    have k : ee x' e' y J p q = _ := (val_corr hJ hU (Formalism.L2.Pj.homAt x0 (jQ m ![p, q])).left).trans
      ((val_scale hJ (unitΓ u) _ _).trans (congrArg₂ (· * ·) rfl e₀))
    exact (gm_unit (y := y) u ![p, q] _ hε.symm).symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

theorem jeq_of_VV (t : SAB H X0) (x0 : Sp S ⟶ X0) {m n : ℕ} {f g : PS S n d}
    (h : ∀ (y : (jOG x0 d m n).left) J, Good t.PP.L y J → VV m y f = VV m y g) : JEq m f g :=
  RatioPh1.jeq_of_psJet (cst_ext fun y => by
    choose J hJ using fun ψ : (jOG x0 d m n).left ⟶ t.G.left => exists_chart t.PP.isLB (ψ y)
    exact h y J hJ)

theorem exists_jRel [StarRing (𝓞 E)] (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    (hs : Function.Surjective (t.G ⊗ t.G).hom.appTop.hom) (B B' : FB S d (𝓞 E)) {κ : Type} [Fintype κ]
    {tg tg' : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uv uv' : κ → Fin d → S}
    (hc : IsChartG t x0 d B.G.F B.A.act tg uv x) (hc' : IsChartG t x0 d B'.G.F B'.A.act tg' uv' x')
    {e : ∀ m, FrTyG t x0 d x m} {e' : ∀ m, FrTyG t x0 d x' m}
    (hf : IsFrameG t x0 d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e)
    (hf' : IsFrameG t x0 d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e')
    (Φ Ψ : Q S d 1) (hinv : IsInvPair Φ.1 Ψ.1) (hco : ∀ m n (u : Q S d n), PP m x' u = PP m x (ac Φ u))
    (hl : ∀ i, B'.G.F i = transF B.G.F Φ.1 Ψ.1 i) (hact : ∀ a, B'.A.act a = comp1 Ψ.1 (comp1 (B.A.act a) Φ.1))
    (wP : PrimTyG t) (m : ℕ) :
    ∃ ε : PS S 2 d, JRel m B B' Φ.1 Ψ.1 ε ∧
      ∀ (k : ℕ) (F : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))) (f f' : PS S 1 d),
        IsGermG t x0 d x B.A.act e wP k F f → IsGermG t x0 d x' B'.A.act e' wP k F f' →
        JEq m (ev ![Φ.1] f) (f' * ev (n := 1) ![pt S d 0, comp1 (B'.A.act H.w0) (pt S d 0)] ε ^ k) := by
  obtain ⟨ε, hε, hE⟩ := exists_ratio Φ hco e e' hf.gen hf'.gen m
  have hΦΨ : ac Φ Ψ = gen 0 := Subtype.ext ((ac_val Φ Ψ).trans hinv.2.2.1)
  have hA : ∀ (b : 𝓞 E) {n} (u : Q S d n), ac Φ (ac (AQ B'.A b) u) = ac (AQ B.A b) (ac Φ u) := fun b n u => by
    have : AQ B'.A b = ac Ψ (ac (AQ B.A b) Φ) := Subtype.ext (by rw [ac_val, ac_val]; exact hact b)
    rw [this, FrameRatioAdj.ac_ac, FrameRatioAdj.ac_ac, ← FrameRatioAdj.ac_ac Φ Ψ, hΦΨ]
    exact sq_gen _ _
  have g2 : ∀ f : PS S 2 d, ev (n := 2) ![pt S d 0, pt S d 1] f = f := fun f =>
    (formalSeriesValueAtTwoPoints_eq_ev f (gen 0) (gen 1)).symm.trans (formalSeriesValueAtTwoPoints_genericPoints f)
  refine ⟨ε, ⟨hinv, hε, hl, hact, ?_, ?_, ?_, fun a => ?_⟩, fun k F f f' hg hg' => ?_⟩
  · have := jeq_of_VV t x0 (m := m)
      (f := E3 B'.ph1 (gen 0 : Q S d 3) (gen 1) (gen 2) * E2 ε (op (FQ B'.G) (gen 0) (gen 1)) (gen 2))
      (g := E3 B.ph1 (ac Φ (gen 0 : Q S d 3)) (ac Φ (gen 1)) (ac Φ (gen 2)) *
        (E2 ε (gen 0) (gen 2) * E2 ε (gen 1) (gen 2))) fun y J hJ => by
      simp only [VV_mul, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_first_partial_law hJ hf', hE _ y J hJ, ← Units.val_mul, hco,
        RatioPh1.ac_op_trans Φ Ψ hinv.2.2.1 hl]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [formalSeriesValueAtThreePoints_genericPoints] at this
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val] using this
  · have := jeq_of_VV t x0 (m := m)
      (f := E3 B'.ph2 (gen 0 : Q S d 3) (gen 1) (gen 2) * E2 ε (gen 0) (op (FQ B'.G) (gen 1) (gen 2)))
      (g := E3 B.ph2 (ac Φ (gen 0 : Q S d 3)) (ac Φ (gen 1)) (ac Φ (gen 2)) *
        (E2 ε (gen 0) (gen 1) * E2 ε (gen 0) (gen 2))) fun y J hJ => by
      simp only [VV_mul, frame_biext_dictionary_second_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf', hE _ y J hJ, ← Units.val_mul, hco,
        RatioPh1.ac_op_trans Φ Ψ hinv.2.2.1 hl]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [formalSeriesValueAtThreePoints_genericPoints] at this
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val] using this
  · have := jeq_of_VV t x0 (m := m) (f := E2 B'.sy (gen 0 : Q S d 2) (gen 1) * E2 ε (gen 0) (gen 1))
      (g := E2 B.sy (ac Φ (gen 0 : Q S d 2)) (ac Φ (gen 1)) * E2 ε (gen 1) (gen 0)) fun y J hJ => by
      simp only [VV_mul, dict_sy hJ hf, dict_sy hJ hf', hE _ y J hJ, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, ac_val, ac_val] at this
    exact this
  · obtain ⟨w, hw, hU⟩ := hf.ad a
    obtain ⟨w', hw', hU'⟩ := hf'.ad a
    obtain ⟨U, h₁, h₂⟩ := hU m
    obtain ⟨U', h₁', h₂'⟩ := hU' m
    obtain ⟨c₀, hc₀⟩ := exists_const t.PP.L t.PP.isLB (t.G ⊗ t.G).hom hs
      (LB.mulGen t.PP.L _ _ _ _ w' (LB.invGen t.PP.L _ _ w))
      (mulGen_isGen _ _ _ _ _ _ _ hw' (invGen_isGen _ _ _ _ hw)) (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
    have := jeq_of_VV t x0 (m := m)
      (f := E2 (B'.ad a) (gen 0 : Q S d 2) (gen 1) * E2 ε (gen 0) (ac (AQ B'.A (H.bar a)) (gen 1)))
      (g := E2 (B.ad a) (ac Φ (gen 0)) (ac Φ (gen 1)) * E2 ε (ac (AQ B'.A a) (gen 0)) (gen 1)) fun y J hJ => by
      have dA := dict_ad (A := B.A) (ad := B.ad) hJ a w U h₁ h₂
      have dB := dict_ad (A := B'.A) (ad := B'.ad) hJ a w' U' h₁' h₂'
      have k : ∀ p q : jOG x0 d m 2 ⟶ t.G, (val₂ w' y J p q * (val₂ w y J p q)⁻¹).val =
          gs (jOG x0 d m 2).hom y ⊤ c₀ := fun p q => by
        have := hc₀ _ (lift p q).left y J hJ
        rw [val_mul hJ, val_inv, Over.w] at this
        exact this
      have a₀ := dA 0 0
      have b₀ := dB 0 0
      rw [FrameRatioAdj.formalSeriesValueAtTwoPoints_zero_zero _ (B.adjoint_zero_fst a), VV_one, ac0, ac0, mul_inv_cancel_right, PP_zero hc] at a₀
      rw [FrameRatioAdj.formalSeriesValueAtTwoPoints_zero_zero _ (B'.adjoint_zero_fst a), VV_one, ac0, ac0, mul_inv_cancel_right, PP_zero hc'] at b₀
      have k₁ := Units.ext ((k (PP m x (ac Φ (gen 0))) (PP m x (ac Φ (gen 1)))).trans (k 1 1).symm)
      rw [Units.ext a₀.symm (v := 1), Units.ext b₀.symm (v := 1), mul_inv_cancel, mul_inv_eq_one] at k₁
      simp only [VV_mul, dA, dB, hE _ y J hJ, hA, hco, k₁, ← Units.val_mul]
      refine congrArg Units.val (Additive.ofMul.injective ?_)
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [hstar a]
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, ac_val, gen_val, g2] using this
  · have := jeq_of_VV t x0 (m := m) (f := sb ![ac Φ (gen 0 : Q S d 1)] f)
      (g := sb ![(gen 0 : Q S d 1)] f' * E2 ε (gen 0) (ac (AQ B'.A H.w0) (gen 0)) ^ k) fun y J hJ => by
      have v := germ_val B.A hg hJ (ac Φ (gen 0))
      have v' := germ_val B'.A hg' hJ (gen 0)
      rw [hco, v] at v'
      have hp : ∀ (g : PS S 1 d) (k : ℕ), VV m y (g ^ k) = VV m y g ^ k := fun g k => by
        induction k with
        | zero => rw [pow_zero, pow_zero, VV_one]
        | succ k ih => rw [pow_succ, pow_succ, VV_mul, ih]
      rw [VV_mul, hp, hE _ y J hJ, hA, ← Units.val_pow_eq_pow_val, (Units.eq_mul_inv_iff_mul_eq _).2 v', _root_.mul_assoc,
        ← Units.val_mul]
      congr 2
      rw [← inv_pow, ← mul_pow]
      congr 1
      refine Additive.ofMul.injective ?_
      simp only [ofMul_mul, ofMul_inv]
      abel
    have e1 : ac Φ (gen 0 : Q S d 1) = Φ := Subtype.ext (funext fun i =>
      (congrArg (sb · (Φ.1 i)) (funext fun j => by fin_cases j; rfl)).trans (sb_gen _))
    have e2 : sb ![(gen 0 : Q S d 1)] f' = f' := (congrArg (sb · f') (funext fun j => by fin_cases j; rfl)).trans (sb_gen _)
    have e3 : sb ![Φ] f = ev ![Φ.1] f := (sb_apply _ _).trans (congrArg (ev · f) (funext fun j => by fin_cases j; rfl))
    rw [e1, e2, e3, formalSeriesValueAtTwoPoints_eq_ev, ac_val, gen_val] at this
    exact this

end GlobalTheory.ChartField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NabValNTransport
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
open GlobalTheory.ChartCmp GlobalTheory.ChartVal GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartField


open GlobalTheory.FBMap in
theorem nabValN_transport (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O]
    [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B B' : FB R d O)
    (φ φi : Pt R 1 d) (h h' : PS k 2 d) (hh : B.IsCanonGauge k h) (hh' : B'.IsCanonGauge k h')
    (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k) (h1 : ∀ τ, cc (cc τ) = τ)
    (h2 : ∀ τ, isX τ ∨ isX (cc τ)) (h3 : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (h4 : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) (u u' : (Σ τ : T, Fin (r τ)) → Fin d → k)
    (hu' : ∀ l a, (dAct k B' a).mulVec (u' l) = σ l.1 a • u' l)
    (hu : ∀ l, u l = ((dLin φ).map (algebraMap R k)).mulVec (u' l)) (n : ℕ) (P : MvPolynomial (Letter T r n) k)
    (hP : P ∈ harmK r n k cc isX (fun _ => 1)) (w0 : O) (q : ℕ) (f' : PS R n d) (m : ℕ) (hm : m = P.totalDegree + 2)
    (ε : PS R 2 d) (hε : JRel m B B' φ φi ε) :
    nabValN B k h w0 q (MvPowerSeries.map (algebraMap R k) (ev (n := n) (fun b => comp1 φi (pt R (n := n) d b))
        (f' * ∏ b : Fin n, (ev ![pt R (n := n) d b, comp1 (B'.A.act w0) (pt R (n := n) d b)] ε) ^ q)))
      (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P =
    nabValN B' k h' w0 q (MvPowerSeries.map (algebraMap R k) f') (fun ℓ : Letter T r n => ℓ.2.2)
      (fun ℓ : Letter T r n => u' ⟨ℓ.1, ℓ.2.1⟩) P := by
  have hε1 := (GlobalTheory.T.formalChartJetRel_unit_one_on_axes R d O m B B' φ φi ε hε).1
  obtain ⟨lam, hl0, hle⟩ := (GlobalTheory.T.jetEq_formalExp_iff_and_exists_log k 2 d m).2 (FB.toK k ε) (by simp [FB.toK, hε1])
  have hbi := GlobalTheory.T.canonicalGauge_difference_biadditive_jet R d O m B B' φ φi ε hε k h h' lam hh hh' hl0 hle
  obtain ⟨g', hg', hgg⟩ := GlobalTheory.T.exists_biadditive_series_jetEq_of_biadditiveJet R d O B' k m (by omega) _ hbi
  have hcan := GlobalTheory.T.isCanonicalGauge_sub_biadditive R d O B' k h' g' hh' hg'
  have c0 : ∀ {C : FB R d O} {g : PS k 2 d}, C.IsCanonGauge k g → MvPowerSeries.constantCoeff g = 0 := by
    intro C g hg
    have := congrArg MvPowerSeries.constantCoeff hg.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have hφ : NoConst φ := hε.inv.1
  have hφi : NoConst φi := hε.inv.2.1
  have hinv : IsInvPair (mapPt (algebraMap R k) φ) (mapPt (algebraMap R k) φi) := by
    refine ⟨fun i => by simp [mapPt, hφ i], fun i => by simp [mapPt, hφi i], ?_, ?_⟩
    · rw [← mapPt_comp1 _ _ hφi, hε.inv.2.2.1, mapPt_pt]
    · rw [← mapPt_comp1 _ _ hφ, hε.inv.2.2.2, mapPt_pt]
  have hact : B'.actK k w0 = comp1 (mapPt (algebraMap R k) φi) (comp1 (B.actK k w0) (mapPt (algebraMap R k) φ)) := by
    change mapPt (algebraMap R k) (B'.A.act w0) = comp1 _ (comp1 (mapPt (algebraMap R k) (B.A.act w0)) _)
    rw [hε.act w0, mapPt_comp1 _ _ (nc_comp1 (nc_act _ _) hφ), mapPt_comp1 _ _ hφ]
  have hF : B'.FK k = transF (mapLaw (algebraMap R k) B.G).F (mapPt (algebraMap R k) φ) (mapPt (algebraMap R k) φi) := by
    funext i
    change MvPowerSeries.map (algebraMap R k) (B'.G.F i) = _
    rw [hε.law i]
    unfold transF
    rw [map_ev1 _ (nc_addOf (nc_law _) (nc_comp1 hφ (nc_pt _)) (nc_comp1 hφ (nc_pt _))),
      mapPt_addOf _ _ (nc_comp1 hφ (nc_pt _)) (nc_comp1 hφ (nc_pt _)), mapPt_comp1 _ _ (nc_pt _),
      mapPt_comp1 _ _ (nc_pt _), mapPt_pt, mapPt_pt]
    rfl
  have hd : dLin (mapPt (algebraMap R k) φ) = (dLin φ).map (algebraMap R k) := by
    ext i j
    simp [dLin, mapPt]
  have hj : JEq m (h' - g') (ev ![comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 0),
      comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 1)] h + lam) := by
    intro e he
    have := hgg e he
    rw [map_sub, map_sub] at this
    rw [map_sub, map_add (f := _), ← this]
    change _ - (_ - MvPowerSeries.coeff e (ev ![comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 0),
      comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 1)] h) - _) = _
    ring
  have haK : GP (B.actK k w0) := fun i => by simp [FB.actK, B.A.const w0 i]
  have key := jeq_main (n := n) m q _ _ (B.actK k w0) hinv haK h (h' - g') lam (c0 hh) (c0 hcan) hl0 hj
    (MvPowerSeries.map (algebraMap R k) f')
  rw [GlobalTheory.T.harmonicValueCopies_gauge_independent R d O k B' h' (h' - g') hh' hcan T r cc isX σ h1 h2 h3 h4 u' hu' n P hP w0 q]
  have hmap : MvPowerSeries.map (algebraMap R k) (ev (n := n) (fun b => comp1 φi (pt R (n := n) d b))
      (f' * ∏ b : Fin n, (ev ![pt R (n := n) d b, comp1 (B'.A.act w0) (pt R (n := n) d b)] ε) ^ q)) =
      ev (n := n) (fun b => comp1 (mapPt (algebraMap R k) φi) (pt k (n := n) d b))
        (MvPowerSeries.map (algebraMap R k) f' * ∏ b : Fin n, (ev ![pt k (n := n) d b,
          comp1 (B'.actK k w0) (pt k (n := n) d b)] (FB.expS k lam)) ^ q) := by
    rw [map_ev _ (fun b => nc_comp1 hφi (nc_pt b)), map_mul, map_prod]
    congr 1
    · funext b
      rw [mapPt_comp1 _ _ (nc_pt _), mapPt_pt]
    · congr 1
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [map_pow, map_ev2 _ (nc_pt _) (nc_comp1 (nc_act _ _) (nc_pt _)), mapPt_comp1 _ _ (nc_pt _), mapPt_pt, hle]
      rfl
  unfold nabValN FB.hL
  rw [hmap, hF, hact, GlobalTheory.T.constantCoeff_invariantPolyOperator_jetEq k d n _ _ _ _ P m _ _ (by omega) key,
    GlobalTheory.T.invariantPolyOperatorCopies_transportedLaw k d n (mapLaw (algebraMap R k) B.G) _ _ hinv,
    gt_const_ev_eq _ (fun b => gp_comp1 _ _ hinv.1 (gp_pt b)), hd]
  simp only [hu]
  rfl

section Box
variable {k : Type} [CommRing k] {d n : ℕ}

theorem boxSer_eq (f : Fin n → PS k 1 d) : GlobalTheory.PowGerm.boxSer f = ∏ b, sb ![(gen b : Q k d n)] (f b) := by
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [MvPowerSeries.rename_eq_subst, sb_apply, ev]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem jeq_prod {σ J : Type} {m : ℕ} (s : Finset J) {f g : J → MvPowerSeries σ k} (h : ∀ i, JEq m (f i) (g i)) :
    JEq m (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using JEq.refl m _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ((GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).1 _ _ _ _ _ (h a) ih).2.2

theorem sb_one (u : Q k d n) (f : PS k 1 d) : sb ![u] f = ev ![u.1] f :=
  (sb_apply _ _).trans (congrArg (ev · f) (funext fun j => by fin_cases j; rfl))

theorem sb_sb_one {l : ℕ} (b : Fin n → Q k d l) (u : Q k d n) (f : PS k 1 d) : sb b (sb ![u] f) = sb ![sq b u] f :=
  (sb_sb _ _ _).trans (congrArg (sb · f) (funext fun j => by fin_cases j; rfl))

theorem jeq_box {m q : ℕ} (Φ Ψ A : Q k d 1) (hΦΨ : ac Φ Ψ = gen 0) (ε : PS k 2 d) (f f' : Fin n → PS k 1 d)
    (h : ∀ b, JEq m (ev ![Φ.1] (f b)) (f' b * ev (n := 1) ![pt k d 0, comp1 A.1 (pt k d 0)] ε ^ q)) :
    JEq m (GlobalTheory.PowGerm.boxSer f) (ev (n := n) (fun b => comp1 Ψ.1 (pt k (n := n) d b))
      (GlobalTheory.PowGerm.boxSer f' * ∏ b : Fin n, (ev ![pt k (n := n) d b, comp1 A.1 (pt k (n := n) d b)] ε) ^ q)) := by
  have e1 : ∀ g : PS k n d, ev (n := n) (fun b => comp1 Ψ.1 (pt k (n := n) d b)) g =
      sb (fun b => ac Ψ (gen b : Q k d n)) g := fun g => by
    rw [sb_apply]; simp only [ac_val, gen_val]
  have e2 : ∀ b : Fin n, ev ![pt k (n := n) d b, comp1 A.1 (pt k (n := n) d b)] ε =
      sb ![(gen b : Q k d n)] (ev (n := 1) ![pt k d 0, comp1 A.1 (pt k d 0)] ε) := fun b => by
    rw [← gen_val, ← gen_val, ← ac_val, ← ac_val, ← formalSeriesValueAtTwoPoints_eq_ev, ← formalSeriesValueAtTwoPoints_eq_ev, formalPointSubstitutionSeries_valueAtTwoPoints, sq_ac, sq_gen]
    rfl
  rw [e1, boxSer_eq, boxSer_eq, ← Finset.prod_mul_distrib, map_prod]
  refine jeq_prod _ fun b => ?_
  rw [e2, ← map_pow, ← map_mul, sb_sb_one, sq_gen]
  have e3 : sb ![(gen b : Q k d n)] (f b) = sb ![ac Ψ (gen b : Q k d n)] (ev ![Φ.1] (f b)) := by
    rw [← sb_one, sb_sb_one]
    change _ = sb ![ac Φ (ac Ψ (gen b))] (f b)
    rw [← FrameRatioAdj.ac_ac, hΦΨ]
    exact congrArg (fun u => sb ![u] (f b)) (sq_gen ![gen b] 0).symm
  rw [e3, sb_apply, sb_apply]
  exact (GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).2.2.2.1 d 1 n _ _ _ _ (fun i j => (_ : Q k d n).2 j) (fun i j => (_ : Q k d n).2 j)
    (fun _ _ => JEq.refl _ _) (h b)

theorem ac_gen (Φ : Q k d 1) : ac Φ (gen 0 : Q k d 1) = Φ := Subtype.ext ((ac_val _ _).trans (gt_comp1_pt_right _))

theorem gen_ac (u : Q k d n) : ac (gen 0) u = u := sq_gen _ _

theorem coord_of_exp (α β α' β' : Q k d 1) (h : IsInvPair α.1 β.1) (h' : IsInvPair α'.1 β'.1) :
    IsInvPair (ac α β').1 (ac α' β).1 ∧ ac (ac α β') α' = α ∧
    (∀ F F' L : Q k d 2, op F (ac α (gen 0 : Q k d 2)) (ac α (gen 1)) = ac α L →
      op F' (ac α' (gen 0 : Q k d 2)) (ac α' (gen 1)) = ac α' L → ∀ i, F'.1 i = transF F.1 (ac α β').1 (ac α' β).1 i) ∧
    ∀ A A' D : Q k d 1, ac A α = ac α D → ac A' α' = ac α' D →
      A'.1 = comp1 (ac α' β).1 (comp1 A.1 (ac α β').1) := by
  have i1 : ∀ {l} (u : Q k d l), ac α (ac β u) = u := fun u => Subtype.ext (by
    rw [ac_val, ac_val]; exact gt_comp_inv h _ u.2)
  have i2 : ∀ {l} (u : Q k d l), ac β (ac α u) = u := fun u => Subtype.ext (by
    rw [ac_val, ac_val]; exact gt_comp_inv' h _ u.2)
  have i1' : ∀ {l} (u : Q k d l), ac α' (ac β' u) = u := fun u => Subtype.ext (by
    rw [ac_val, ac_val]; exact gt_comp_inv h' _ u.2)
  have i2' : ∀ {l} (u : Q k d l), ac β' (ac α' u) = u := fun u => Subtype.ext (by
    rw [ac_val, ac_val]; exact gt_comp_inv' h' _ u.2)
  have j : ∀ {a b : Q k d 1}, (∀ u : Q k d 1, ac a (ac b u) = u) → ac a b = gen 0 := fun {a b} e => by
    rw [← e (gen 0), ac_gen]
  refine ⟨⟨(ac α β').2, (ac α' β).2, ?_, ?_⟩, ?_, fun F F' L e e' => ?_, fun A A' D e e' => ?_⟩
  · rw [← ac_val, FrameRatioAdj.ac_ac, ← FrameRatioAdj.ac_ac β', j i2', gen_ac, j i1, gen_val]
  · rw [← ac_val, FrameRatioAdj.ac_ac, ← FrameRatioAdj.ac_ac β, j i2, gen_ac, j i1', gen_val]
  · rw [FrameRatioAdj.ac_ac, j i2', ac_gen]
  · have c := congrArg (sq ![ac β' (gen 0 : Q k d 2), ac β' (gen 1)]) e
    have c' := congrArg (sq ![ac β' (gen 0 : Q k d 2), ac β' (gen 1)]) e'
    simp only [sq_op, sq_ac, sq_gen, Matrix.cons_val, i1'] at c c'
    have : F' = ac (ac α' β) (op F (ac (ac α β') (gen 0 : Q k d 2)) (ac (ac α β') (gen 1))) := by
      simp only [FrameRatioAdj.ac_ac, c, i2, ← c']
      exact Subtype.ext (funext fun i => (formalSeriesValueAtTwoPoints_genericPoints _).symm)
    intro i
    rw [this]
    simp only [ac_val (ac α' β), op_val, ac_val (ac α β'), gen_val]
    rfl
  · rw [← ac_val, ← ac_val, ← FrameRatioAdj.ac_ac A, e, FrameRatioAdj.ac_ac, FrameRatioAdj.ac_ac, i2,
      ← FrameRatioAdj.ac_ac, ← e', FrameRatioAdj.ac_ac, j i1', ac_gen]

end Box

theorem nabValN_box_eq (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O]
    [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] (B B' : FB k d O)
    (Φ Ψ : Q k d 1) (h h' : PS k 2 d) (hh : B.IsCanonGauge k h) (hh' : B'.IsCanonGauge k h')
    (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k) (h1 : ∀ τ, cc (cc τ) = τ)
    (h2 : ∀ τ, isX τ ∨ isX (cc τ)) (h3 : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (h4 : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) (u u' : (Σ τ : T, Fin (r τ)) → Fin d → k)
    (hu' : ∀ l a, (dAct k B' a).mulVec (u' l) = σ l.1 a • u' l)
    (hu : ∀ l, u l = (dLin Φ.1).mulVec (u' l)) (n : ℕ) (P : MvPolynomial (Letter T r n) k)
    (hP : P ∈ harmK r n k cc isX (fun _ => 1)) (w0 : O) (q : ℕ) (f f' : Fin n → PS k 1 d)
    (ε : PS k 2 d) (hε : JRel (P.totalDegree + 2) B B' Φ.1 Ψ.1 ε)
    (hf : ∀ b, JEq (P.totalDegree + 2) (ev ![Φ.1] (f b))
      (f' b * ev (n := 1) ![pt k d 0, comp1 (B'.A.act w0) (pt k d 0)] ε ^ q)) :
    nabValN B k h w0 q (GlobalTheory.PowGerm.boxSer f) (fun ℓ : Letter T r n => ℓ.2.2)
      (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P =
    nabValN B' k h' w0 q (GlobalTheory.PowGerm.boxSer f') (fun ℓ : Letter T r n => ℓ.2.2)
      (fun ℓ : Letter T r n => u' ⟨ℓ.1, ℓ.2.1⟩) P := by
  have key := nabValN_transport k d O k B B' Φ.1 Ψ.1 h h' hh hh' T r cc isX σ h1 h2 h3 h4 u u' hu'
    (fun l => by rw [hu l]; rfl) n P hP w0 q (GlobalTheory.PowGerm.boxSer f') _ rfl ε hε
  rw [gt_map_id, gt_map_id] at key
  rw [← key]
  have hb := jeq_box Φ Ψ (⟨B'.A.act w0, B'.A.const w0⟩ : Q k d 1) (Subtype.ext ((ac_val Φ Ψ).trans hε.inv.2.2.1)) ε f f' hf
  exact (GlobalTheory.PowGerm.nabJet k d O B k h w0 q n _ _ _).1 P _ _ fun e he => hb e (by omega)

end GlobalTheory.ChartField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueGermsIndependentOfChart
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

namespace GlobalTheory.ChartField

section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FrameBiextId GlobalTheory.ChartCmp ReciprocityTheory.ChartRestriction.G.TB.WickVanishing Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {S : Type} [Field S] [Algebra c.F S] [Algebra ℚ S]

theorem chartVal_eq {y : FrPt Xo c S} (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (f : Fin n → PS S 1 C.d)
    (P : MvPolynomial (LtN Dw n) c.F) :
    chartVal C k f P = nabValN C.B S C.h H.w0 k (GlobalTheory.PowGerm.boxSer f) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ : LtN Dw n => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (P.map (algebraMap c.F S)) := by
  classical
  have h0 : MvPowerSeries.constantCoeff C.h = 0 := by
    have := congrArg MvPowerSeries.constantCoeff C.gauge.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have key := GlobalTheory.nabValN_boxSer S C.d (𝓞 E) C.B S C.h H.w0 h0 k n f (Lt1 Dw) (LtN Dw n) (ltEquiv Dw n).symm
    (fun ℓ : LtN Dw n => ℓ.2.2) C.uvec (fun ℓ : LtN Dw n => C.uvec ⟨ℓ.1, ℓ.2.1⟩) (fun _ => rfl) (fun _ => rfl)
    (MvPolynomial.rename (ltEquiv Dw n) (P.map (algebraMap c.F S)))
  rw [MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id_apply,
    MvPolynomial.support_rename_of_injective (ltEquiv Dw n).injective,
    Finset.sum_image (fun _ _ _ _ h => Finsupp.mapDomain_injective (ltEquiv Dw n).injective h),
    MvPolynomial.support_map_of_injective _ (algebraMap c.F S).injective] at key
  rw [key, chartVal]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ (ltEquiv Dw n).injective, MvPolynomial.coeff_map]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  refine congrArg (fun z => C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial z 1)) (Finsupp.ext fun ℓ => ?_)
  exact (Finsupp.mapDomain_apply_of_injective (ltEquiv Dw n).injective m ⟨ℓ.1, ℓ.2, b⟩).symm


omit [StarRing (𝓞 E)] [Algebra ℚ S] in
theorem exp_facts (G : FGLaw S (dL Dw)) (uvec : Lt1 Dw → Fin (dL Dw) → S)
    (hb : ∀ v : Fin (dL Dw) → S, ∃! a : Lt1 Dw → S, ∀ j, ∑ ℓ, a ℓ * uvec ℓ j = v j) (φ : Pt S 1 (dL Dw))
    (h : IsExpOf G.F uvec φ) :
    (∃ β : Q S (dL Dw) 1, IsInvPair φ β.1) ∧
    op (FQ G) (ac (⟨φ, h.const⟩ : Q S (dL Dw) 1) (gen 0 : Q S (dL Dw) 2)) (ac ⟨φ, h.const⟩ (gen 1)) =
      ac ⟨φ, h.const⟩ (gen 0 + gen 1) := by
  classical
  constructor
  · have hs : Function.Surjective (dLin φ).mulVec := fun v => by
      obtain ⟨a, ha, -⟩ := hb v
      refine ⟨fun i => a ((ltIdx Dw).symm i), funext fun j => ?_⟩
      rw [← ha j, Matrix.mulVec, dotProduct, ← (ltIdx Dw).sum_comp]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [Equiv.symm_apply_apply, mul_comm, ← h.lin ℓ j]
      rfl
    obtain ⟨φi, hi⟩ := GlobalTheory.ChartInv.exists_isInvPair S _ φ h.const
      ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_surjective_iff_isUnit.1 hs))
    exact ⟨⟨φi, hi.2.1⟩, hi⟩
  · refine Subtype.ext (funext fun j => ?_)
    rw [op_val, ac_val, ac_val, ac_val]
    refine Eq.trans ?_ ((h.hom j).trans ?_)
    · simp only [addOf, ev]
      congr 1
      funext p
      obtain ⟨i, s⟩ := p
      fin_cases i <;> exact CoordLaw.ev_one_eq _ _
    · rw [comp1, CoordLaw.ev_one_eq]
      congr 1

end


open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FrameBiextId GlobalTheory.ChartCmp ReciprocityTheory.ChartRestriction.G.TB.WickVanishing Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh in
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct) in
theorem chartVal_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → chartVal C k f P = chartVal C' k f' P := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C C' k n F f f' hf hf' a P hP
  have hAct := expActOf_of GlobalTheory.EigDir.linEig_holds
  obtain ⟨φ, hφ, hx⟩ := expChartOf_of hAct E H Dw l Xo c S y C
  obtain ⟨φ', hφ', hx'⟩ := expChartOf_of hAct E H Dw l Xo c S y C'
  have hxx := ExpUniqChart.expUniqTan E H Dw l Xo c S y _ _ hx' hx
  have ha := hAct E H Dw l Xo c S y C φ hφ
  have ha' := hAct E H Dw l Xo c S y C' φ' hφ'
  have heig := GlobalTheory.EigDir.linEig_holds E H Dw l Xo c S y C'
  have hw := primUniq_of_global GlobalTheory.SemiRigid.globalFns E H Dw l Xo _ _ C.prim C'.prim
  have hd := CIndRelPf.dim_eq_card C.uvec C.chart.basis
  have hd' := CIndRelPf.dim_eq_card C'.uvec C'.chart.basis
  rw [chartVal_eq, chartVal_eq]
  obtain ⟨d, B, u, x, e, wP, h, hc, hfr, hp, hg, hr⟩ := C
  obtain ⟨d', B', u', x', e', wP', h', hc', hfr', hp', hg', hr'⟩ := C'
  dsimp only at hd hd' hw hφ hφ' ha ha' heig f f' hf hf' φ φ' ⊢
  subst hd hd' hw
  obtain ⟨⟨β, hβ⟩, hl⟩ := exp_facts B.G u hc.basis φ hφ
  obtain ⟨⟨β', hβ'⟩, hl'⟩ := exp_facts B'.G u' hc'.basis φ' hφ'
  let α : Q S (dL Dw) 1 := ⟨φ, hφ.const⟩
  let α' : Q S (dL Dw) 1 := ⟨φ', hφ'.const⟩
  obtain ⟨hinv, hαα, hlaw, hact⟩ := coord_of_exp α β α' β' hβ hβ'
  let D : 𝓞 E → Q S (dL Dw) 1 := fun b => ⟨fun j => algebraMap c.F S (embK c ((ltIdx Dw).symm j).1 b) •
    MvPowerSeries.X ((0 : Fin 1), j), fun j => by simp⟩
  have hD : ∀ (A ψ : Q S (dL Dw) 1) (b : 𝓞 E), (∀ j, MvPowerSeries.subst (fun p : Fin 1 × Fin (dL Dw) => ψ.1 p.2) (A.1 j) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 b) •
        (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin (dL Dw)) S)) (ψ.1 j)) → ac A ψ = ac ψ (D b) := by
    intro A ψ b hb
    refine Subtype.ext (funext fun j => ?_)
    rw [ac_val, ac_val, comp1, comp1, CoordLaw.ev_one_eq, CoordLaw.ev_one_eq, hb j]
    congr 1
    funext q
    obtain ⟨i, s⟩ := q
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  have hj : ∀ (ψ : Q S (dL Dw) 1) (m : ℕ), jφ ψ.1 m = jQ m ![ψ] := fun ψ m =>
    subst_eq m _ ![ψ] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl) (fun s => (cc_psTrunc m _).trans (ψ.2 _))
  have hco : ∀ m n (v : Q S (dL Dw) n), PP (t := Xo.univ.t) (x0 := y.x) m x' v =
      PP (t := Xo.univ.t) (x0 := y.x) m x (ac (ac α β') v) := fun m n v => by
    have e0 : homAt y.x (jφ α'.1 m) ≫ x' m = homAt y.x (jφ α.1 m) ≫ x m := congrFun hxx m
    rw [hj, hj] at e0
    have e1 : PP (t := Xo.univ.t) (x0 := y.x) m x' α' = PP (t := Xo.univ.t) (x0 := y.x) m x α := e0
    have e2 := congrArg (homAt y.x (jQ m ![ac β' v]) ≫ ·) e1
    simp only [PP_sq] at e2
    have e3 : sq ![ac β' v] α' = v := Subtype.ext (by
      rw [show sq ![ac β' v] α' = ac α' (ac β' v) from rfl, ac_val, ac_val]; exact gt_comp_inv hβ' _ v.2)
    rw [e3] at e2
    rw [FrameRatioAdj.ac_ac]
    exact e2
  have hsurj := (GlobalTheory.SemiRigid.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ (isAbelianScheme_univ Xo)
    (isAbelianScheme_univ Xo))).2
  obtain ⟨ε, hε, hge⟩ := exists_jRel hs hsurj B B' ((isChart_iff y _ _ _ _ _).1 hc) ((isChart_iff y _ _ _ _ _).1 hc')
    ((isFrame_iff y _ _ _ _ _ _ _ _ _).1 hfr) ((isFrame_iff y _ _ _ _ _ _ _ _ _).1 hfr') (ac α β') (ac α' β) hinv hco
    (hlaw (FQ B.G) (FQ B'.G) _ hl hl')
    (fun b => hact (AQ B.A b) (AQ B'.A b) (D b) (hD _ α b (ha b)) (hD _ α' b (ha' b))) wP
    ((P.map (algebraMap c.F S)).totalDegree + 2)
  refine nabValN_box_eq _ (𝓞 E) S B B' (ac α β') (ac α' β) h h' hg hg' (E →+* ℂ) Dw.mult
    ComplexEmbedding.conjugate (InPsi H) (fun τ => (algebraMap c.F S).comp (embK c τ)) (fun τ => by ext x; simp)
    (inPsi_or_conjugate H)
    (fun τ a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hs]
      congr 1
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])
    (fun σ τ hne => by
      have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))
      obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_⟩
      have h0 : embK c σ a - embK c τ a ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        apply ha
        rw [← embK_coe c, ← embK_coe c, h1]
      rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub]
      exact (Ne.isUnit h0).map _)
    u u' (fun ℓ b => funext fun i => ?_) (fun ℓ => funext fun i => ?_) n _
    (PullbackSections.harmK_map (algebraMap c.F S) hP.1.1) H.w0 k f f' ε hε
    (fun b => hge k (F b) (f b) (f' b) ((isGerm_iff y _ _ _ _ _ _ _ _).1 (hf b))
      ((isGerm_iff y _ _ _ _ _ _ _ _).1 (hf' b)))
  · refine Eq.trans ?_ (heig b ℓ i)
    simp only [Matrix.mulVec, dotProduct, dAct, FB.actK, gt_map_id, dLin]
  · have e0 : comp1 (ac α β').1 φ' = φ := (ac_val _ α').symm.trans (congrArg Subtype.val hαα)
    have e1 := congrFun (congrFun (dLin_comp1 (ac α β').1 φ' hφ'.const) i) (ltIdx Dw ℓ)
    rw [e0, Matrix.mul_apply] at e1
    rw [← hφ.lin ℓ i]
    refine e1.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [← hφ'.lin ℓ j]
    rfl

end GlobalTheory.ChartField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueGermsIndependentOfChartStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_germs_independent_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → chartVal C k f P = chartVal C' k f' P := by
  first | exact @GlobalTheory.ChartField.chartVal_indep | exact GlobalTheory.ChartField.chartVal_indep | (intros; apply GlobalTheory.ChartField.chartVal_indep <;> assumption)
end
