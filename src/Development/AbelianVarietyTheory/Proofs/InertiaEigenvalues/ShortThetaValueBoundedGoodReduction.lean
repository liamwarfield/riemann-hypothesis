module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.BilLActRight
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsExtAllModelsUniformised
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ReachedSectionRegularOnIntegralModel
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinPartCanonGaugeCongr
set_option autoImplicit false

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem bilinPart_canonGauge_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → (∀ i j, ((bilinPart k h)ᵀ - bilinPart k h) i j ∈ (algebraMap R k).range) ∧ (∀ a : O, (∀ i j, ((dAct k B a)ᵀ * bilinPart k h - bilinPart k h * dAct k B (star a)) i j ∈ (algebraMap R k).range)) ∧ (∀ a : O, (∀ i j, (dAct k B a) i j ∈ (algebraMap R k).range)) ∧ dAct k B 1 = 1 ∧ (∀ a b : O, dAct k B (a + b) = dAct k B a + dAct k B b) ∧ ∀ a b : O, dAct k B (a * b) = dAct k B a * dAct k B b := by
  intro R _ d O _ _ k _ _ _ B h hc
  refine ⟨fun i j => ?_, fun a i j => ?_, fun a i j => ?_, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_one k B,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add k B, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_mul k B⟩
  · have e := congrArg (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)) hc.sy
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_expS_two _ (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_swap_sub_low h hc.ax0 hc.ax1) _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.degree_xz i j), map_sub, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_swap', coeff_map,
      Finsupp.embDomain_add, Finsupp.embDomain_single, Finsupp.embDomain_single, add_comm (Finsupp.single (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.swE d _) 1)] at e
    exact ⟨_, e⟩
  · obtain ⟨r, hr⟩ := ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.M_int B h hc a j i
    refine ⟨-r, ?_⟩
    rw [map_neg, hr]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, bilinPart,
      neg_mul, Finset.sum_neg_distrib, mul_comm (dAct k B _ _ _)]
    ring
  · exact ⟨coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i), by
      unfold dAct FB.actK; rw [coeff_map]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSymmBalancedCongrOfSeparability
open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart)

namespace GlobalTheory

theorem exists_addHom_tensor_int_of_biadditive {M N P : Type} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] (f : M → N → P) (h1 : ∀ m m' n, f (m + m') n = f m n + f m' n)
    (h2 : ∀ m n n', f m (n + n') = f m n + f m n') :
    ∃ g : M ⊗[ℤ] N →+ P, ∀ m n, g (m ⊗ₜ[ℤ] n) = f m n := by
  let F : M →+ N →+ P := AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (f m) (h2 m))
    (fun m m' => by ext n; exact h1 m m' n)
  refine ⟨TensorProduct.liftAddHom F (fun r m n => ?_), fun m n => ?_⟩
  · rw [map_zsmul, map_zsmul]; rfl
  · rw [TensorProduct.liftAddHom_tmul]; rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinearLogFormEvalZeroRightEqZero
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.TB (dAct bilinPart dLin)

namespace GlobalTheory.GaugeShift

open ReciprocityTheory.ChartRestriction.G.TB.LogPf (CZ ev_sub ev_zeroFam logOf)
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix (bilL lg)
open GlobalTheory.TwistCheck (ev_bilL cc_log bilL_mixed balanced_iff)

variable {S : Type} [CommRing S] {d : ℕ}

theorem cz2 {n : ℕ} {a b : Pt S n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    CZ (![a, b] : Fin 2 → Pt S n d) := by
  intro j i
  fin_cases j
  · exact ha i
  · exact hb i

theorem coeff_mixed (g : PS S 2 d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1) g =
      constantCoeff (pderiv (R := S) ((0 : Fin 2), i) (pderiv (R := S) ((1 : Fin 2), l) g)) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, coeff_pderiv, zero_add]
  simp

variable [Algebra ℚ S]

theorem ev_zero_log {n : ℕ} (G : FGLaw S d) (i : Fin d) : ev (n := n) ![0] (logOf G i) = 0 := by
  have e : (![0] : Fin 1 → Pt S n d) = fun _ _ => 0 := by
    funext j c; fin_cases j; rfl
  rw [e, ev_zeroFam, cc_log, map_zero]

theorem cz0 {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt S n d) i) = 0 := by simp

theorem bilinearLogForm_eval_zero_left_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![0, pt S d 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 cz0 (FBMap.cz_pt _))]
  simp [ev_zero_log]

theorem bilinearLogForm_eval_zero_right_eq_zero (G : FGLaw S d) (c : Fin d → Fin d → S) : ev (n := 1) ![pt S d 0, 0] (bilL G c) = 0 := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) cz0)]
  simp [ev_zero_log]

theorem bilL_add_left (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![G.add (pt S d 0) (pt S d 1), pt S d 2] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) + ev (n := 3) ![pt S d 1, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (FBMap.cz_pt _)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2c.formal_log_add_first_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_add_right (G : FGLaw S d) (c : Fin d → Fin d → S) :
    ev (n := 3) ![pt S d 0, G.add (pt S d 1) (pt S d 2)] (bilL G c) =
      ev (n := 3) ![pt S d 0, pt S d 1] (bilL G c) + ev (n := 3) ![pt S d 0, pt S d 2] (bilL G c) := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (CIndFrFix2b.constantCoeff_add_second_third G)), ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _)),
    ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CIndFrFix2b.formal_log_add_last_two, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem bilL_swap (G : FGLaw S d) (c : Fin d → Fin d → S) (hs : ∀ i l, c i l = c l i) :
    ev (n := 2) ![pt S d 1, pt S d 0] (bilL G c) = bilL G c := by
  rw [ev_bilL G c (cz2 (FBMap.cz_pt _) (FBMap.cz_pt _))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, bilL, lg, smul_eq_C_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hs l i, mul_comm (ev _ _)]

theorem canon_sub_bilin : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ β : Matrix (Fin d) (Fin d) k, βᵀ = β → (∀ a : O, (dAct k B a)ᵀ * β = β * dAct k B (star a)) → ∃ h' : PS k 2 d, B.IsCanonGauge k h' ∧ bilinPart k h' = bilinPart k h - β := by
  intro R _ d O _ _ k _ _ _ B h hc β hs hb
  let G : FGLaw k d := FBMap.mapG (algebraMap R k) B.G
  let A : OAct O G := FBMap.mapA (algebraMap R k) B.A
  have hF : B.FK k = G.F := rfl
  have hA : ∀ a, B.actK k a = A.act a := fun _ => rfl
  have p {n : ℕ} (j : Fin n) := FBMap.cz_pt (R := k) (d := d) j
  have q (a : O) (j : Fin 2) := FBMap.cz_comp1 (A.act a) (A.const a) (pt k d j) (p j)
  refine ⟨h - bilL G β, ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩, ?_⟩
  · rw [ev_sub (cz2 cz0 (p _)), hc.ax0, bilinearLogForm_eval_zero_left_eq_zero G β, sub_zero]
  · rw [ev_sub (cz2 (p _) cz0), hc.ax1, bilinearLogForm_eval_zero_right_eq_zero G β, sub_zero]
  · rw [hc.ph1, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (CIndFrFix2c.constantCoeff_add_first_second G) (p _)), bilL_add_left G β]
    congr 1; ring
  · rw [hc.ph2, hF, ev_sub (cz2 (p _) (p _)), ev_sub (cz2 (p _) (p _)),
      ev_sub (cz2 (p _) (CIndFrFix2b.constantCoeff_add_second_third G)), bilL_add_right G β]
    congr 1; ring
  · rw [hc.sy, ev_sub (cz2 (p _) (p _)), bilL_swap G β (fun i l => congrFun (congrFun hs l) i)]
    congr 1; ring
  · have hbal := (balanced_iff G A a (star a) β).1 (hb a)
    rw [hc.ad a, hA, hA, ev_sub (cz2 (q _ _) (p _)), ev_sub (cz2 (p _) (q _ _)), hbal]
    congr 1; ring
  · funext i l
    have := coeff_mixed (bilL G β) i l
    rw [bilL_mixed G β] at this
    simp only [bilinPart, map_sub, this, Matrix.sub_apply]

end GlobalTheory.GaugeShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChartValIndepOfHarmonic
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HarmonicAny


open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FrameBiextId GlobalTheory.ChartCmp ReciprocityTheory.ChartRestriction.G.TB.WickVanishing Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh GlobalTheory.ChartField in
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct) in
theorem chartVal_indep_of_harmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C C' : ChartAt Xo c y) (k n : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S) (f' : Fin n → MvPowerSeries (Fin 1 × Fin C'.d) S), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → (∀ b, IsGerm y C'.d C'.x C'.B.A.act C'.e C'.wP k (F b) (f' b)) → ∀ (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) → chartVal C k f P = chartVal C' k f' P := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C C' k n F f f' hf hf' P hP
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
    (PullbackSections.harmK_map (algebraMap c.F S) hP) H.w0 k f f' ε hε
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


set_option maxHeartbeats 1000000 in
theorem sum_map_of_harmonic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) {S S' : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    [Field S'] [Algebra c.F S'] [Algebra ℚ S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S')
    (hm : FrMap ψ y y') (h : ptO Xo y'.x ⟶ ptO Xo y.x) (hh : h.left = spMap ψ.toRingHom)
    (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1)) (K : ℤ) (k : ℕ)
    (hK : K = k) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y'.x)))
    (hF' : ∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L K (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) :
    ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (F b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' K (F' b) (colOf m b) := by
  subst hK
  obtain ⟨hx, hu, -⟩ := hm
  obtain ⟨x', xo', u', tan', eig', basis', s', gen'⟩ := y'
  dsimp only at hx hu h hh F' hF'
  have hu' : u' = fun τ i => spMap (dualMap (ψ : S →+* S')) ≫ y.u τ i := funext fun τ => funext fun i => hu τ i
  have hx' : x' = spMap (ψ : S →+* S') ≫ y.x := hx
  subst hx'
  subst hu'
  have hh' : h = ptBC (ψ : S →+* S') y.x := Over.OverMorphism.ext hh
  subst hh'
  obtain ⟨C, hex, hpin⟩ := hnab.2 S y
  choose f hf using fun b => hex k (F b)
  obtain ⟨B', x2, e2, -, hF, hA, -, -, -, -, hch, hfr, hga, hrig, hgerm⟩ :=
    GlobalTheory.rawChart_baseChange E H Dw l Xo c S S' ψ y.x y.u (ChartAt.toRaw C)
  let z : FrPt Xo c S' := ⟨_, xo', _, tan', eig', basis', s', gen'⟩
  set_option backward.isDefEq.respectTransparency false in
  let C2 : ChartAt Xo c z :=
    ⟨C.d, B', fun ℓ j => ψ (C.uvec ℓ j), x2, e2, C.wP, MvPowerSeries.map (ψ : S →+* S') C.h,
      ⟨hch.zero, hch.trunc, hch.law, hch.act, hch.tan, hch.basis⟩,
      ⟨hfr.gen, hfr.ph1, hfr.ph2, hfr.sy, hfr.ad⟩, C.prim, hga, hrig⟩
  have hg2 : ∀ b, IsGerm z C2.d C2.x C2.B.A.act C2.e C2.wP k (F' b)
      (MvPowerSeries.map (ψ : S →+* S') (f b)) := fun b => hgerm k (F b) (F' b) (f b) (hF' b) (hf b)
  obtain ⟨C3, hex3, hpin3⟩ := hnab.2 S' z
  choose f3 hf3 using fun b => hex3 k (F' b)
  have hI := chartVal_indep_of_harmonic E H Dw l Xo c hnab.1 S' z C2 C3 k n F' _ f3 hg2 hf3 P hP
  have e3 : (∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab z k (F' b) (colOf m b)) =
      chartVal C3 k f3 P := by
    unfold chartVal
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun b _ => hpin3 k (F' b) (f3 b) (hf3 b) (colOf m b)
  refine Eq.trans ?_ (hI.trans e3.symm)
  unfold chartVal
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, AlgHom.commutes, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hN := nabMap_holds S S' (ψ : S →+* S') C.d (𝓞 E) C.B B' hF hA C.h C.gauge H.w0 k (f b) (Lt1 Dw) C.uvec
    (MvPolynomial.monomial (colOf m b) 1)
  rw [MvPolynomial.map_monomial, map_one] at hN
  exact (congrArg ψ (hpin k (F b) (f b) (hf b) (colOf m b))).trans hN.symm

theorem exists_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1))
    {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (w : FrPt Xo c T) (hm : FrMap ψ y w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo y.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) :
    ∃ (z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
        LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo w.x))),
      (∀ i, InZh Xo Λ N (z' i)) ∧ GeoInj Xo w.x z' ∧
      (∀ q b, tp' q b ^ N = levPt Xo w.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp' q b)) ∧
      (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N w.s (z' i b) (tp' q b) (F' q i b)) ∧
      ∀ q, ψ (∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)) =
        ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
          ∏ b, nab w ((N : ℤ) ^ 2) (F' q i b) (colOf m b) := by
  let h : ptO Xo w.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  choose F' hF' using fun q i b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2)
    (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F q i b)
  obtain ⟨p1, -, p3, -⟩ := GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N
  refine ⟨fun i b => h ≫ z i b, fun q b => h ≫ tp q b, F', fun i => p1 _ _ h _ (hz i),
    p3 S T y.x w.x ψ.toRingHom h rfl _ z hg, fun q b => ⟨?_, ?_⟩, fun q i b => ?_, fun q => ?_⟩
  · have e : h ≫ levPt Xo y.x (levRep (q b)) = levPt Xo w.x (levRep (q b)) := by
      unfold levPt
      rw [← Category.assoc, comp_toUnit]
    rw [← e, ← (ht q b).1, MonObj.comp_pow]
  · obtain ⟨j, hj⟩ := (ht q b).2
    exact ⟨j, fun u hu => by rw [Category.assoc, hj u hu, MonObj.comp_one]⟩
  · exact (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo N ⊤ _ _ h y.s w.s
      (GlobalTheory.FramedBaseChange.isPullSec ψ hm h rfl) (F q i b) (F' q i b) (hF' q i b)).2 _ _ (hF q i b)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
      letI : Algebra ℚ T := ((algebraMap c.F T).comp (algebraMap ℚ c.F)).toAlgebra
      exact Finset.sum_congr rfl fun i _ =>
        sum_map_of_harmonic nab hnab ψ y w hm h rfl n P hP _ (N ^ 2) (by push_cast; rfl) (F q i) (F' q i) (hF' q i)

theorem map_shortValAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hN : Λ.LevOK N l.M)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1))
    (cf : (Fin n → LevQ Dw l) → c.F) (β : c.F)
    {K k : Type} [Field K] [Algebra c.F K] [Field k] [Algebra c.F k] (ψ : K →ₐ[c.F] k)
    (y : FrPt Xo c K) (yk : FrPt Xo c k) (hψ : FrMap ψ y yk)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo yk.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo yk.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo yk.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo yk.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo yk.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N yk.s (z i b) (tp q b) (F q i b))
    (v : K) (hv : ShortValAt Xo c nab cf Λ β N P y v) :
    ψ v = algebraMap c.F k (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F k (cf q) *
        ∑ i, ∑ m ∈ P.support, algebraMap c.F k (P.coeff m) * ∏ b, nab yk ((N : ℤ) ^ 2) (F q i b) (colOf m b) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  haveI := GlobalTheory.ShortAtField.finite_levQ Dw l
  obtain ⟨S1, _, _, φ1, y1, z1, tp1, F1, hf1, hm1, hz1, hg1, ht1, hu1, e1⟩ := hv
  obtain ⟨U, _, _, ψ2, ψ1, hc, -, hinj⟩ := GlobalTheory.exists_faithfullyFlat_pushout c.F K k S1 ψ φ1 hf1
  haveI : Nontrivial U := hinj.nontrivial
  obtain ⟨Ω, _, _, ⟨κ⟩⟩ := GlobalTheory.ShortAtField.exists_algHom_field c.F U
  obtain ⟨u, hu⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S1 Ω (κ.comp ψ1) y1
  obtain ⟨u', hu'⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c k Ω (κ.comp ψ2) yk
  have e : (κ.comp ψ2).comp ψ = (κ.comp ψ1).comp φ1 := by
    rw [AlgHom.comp_assoc, hc, AlgHom.comp_assoc]
  have h1 := GlobalTheory.FramedBaseChange.trans φ1 _ hm1 hu
  have h2 := GlobalTheory.FramedBaseChange.trans ψ _ hψ hu'
  rw [e] at h2
  obtain rfl : u = u' := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c K Ω _ y).1 u u' h1 h2
  obtain ⟨z1', tp1', G1, a1', b1', c1', d1', f1⟩ :=
    exists_pull nab hnab Λ N P hP (κ.comp ψ1) y1 u hu z1 tp1 F1 hz1 hg1 ht1 hu1
  obtain ⟨z2', tp2', G2, a2', b2', c2', d2', f2⟩ :=
    exists_pull nab hnab Λ N P hP (κ.comp ψ2) yk u hu' z tp F hz hg ht hF
  apply (κ.comp ψ2).toRingHom.injective
  change (κ.comp ψ2) (ψ v) = (κ.comp ψ2) _
  rw [show (κ.comp ψ2) (ψ v) = (κ.comp ψ1) (φ1 v) from AlgHom.congr_fun e v, e1]
  refine GlobalTheory.ShortAtField.map_weighted (κ.comp ψ1) (κ.comp ψ2) _ cf _ _ fun q => ?_
  exact (f1 q).trans ((GlobalTheory.shortSum_indep_local hL E H Dw l Xo c nab hnab n Λ N hU hT hN P Ω u z1' tp1' G1 z2' tp2' G2
    a1' b1' c1' d1' a2' b2' c2' d2' q).trans (f2 q).symm)

end GlobalTheory.HarmonicAny
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonGaugeNabValBoundedDenom
set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt

namespace GlobalTheory.GaugeBoundedDenom

theorem exists_symm_balanced {k : Type} [CommRing k] [Algebra ℚ k] (S : Subring k) (E : Type) [Field E]
    [NumberField E] [StarRing (𝓞 E)] {d : ℕ} (A : 𝓞 E →+* Matrix (Fin d) (Fin d) k)
    (hA : ∀ a i j, A a i j ∈ S) (β : Matrix (Fin d) (Fin d) k) (hsym : ∀ i j, (βᵀ - β) i j ∈ S)
    (hbal : ∀ a i j, ((A a)ᵀ * β - β * A (star a)) i j ∈ S) :
    ∃ β' : Matrix (Fin d) (Fin d) k, β'ᵀ = β' ∧ (∀ a, (A a)ᵀ * β' = β' * A (star a)) ∧
      ∀ i j, ((2 * discr E : ℤ) : k) * (β - β') i j ∈ S := by
  obtain ⟨x, y, h1, hc⟩ := GlobalTheory.IntSepElement.exists_sep_discr E
  obtain ⟨u, hu⟩ : ∃ u : k, ((2 * discr E : ℤ) : k) * u = 1 := by
    refine ⟨algebraMap ℚ k (((2 * discr E : ℤ) : ℚ)⁻¹), ?_⟩
    rw [← map_intCast (algebraMap ℚ k), ← map_mul, mul_inv_cancel₀, map_one]
    exact_mod_cast mul_ne_zero two_ne_zero (discr_ne_zero E)
  obtain ⟨g, hg⟩ := GlobalTheory.exists_addHom_tensor_int_of_biadditive
    (fun a b : 𝓞 E => (A a)ᵀ * β * A (star b))
    (fun m m' n => by simp only [map_add (f := _), transpose_add, Matrix.add_mul])
    (fun m n n' => by simp only [star_add, map_add (f := _), Matrix.mul_add])
  have hT : ∀ a b : 𝓞 E, (A (a * b))ᵀ = (A a)ᵀ * (A b)ᵀ := fun a b => by
    rw [mul_comm a b, map_mul, transpose_mul]
  set γ : Matrix (Fin d) (Fin d) k := ∑ i, (A (x i))ᵀ * β * A (star (y i)) with hγ
  have hγbal : ∀ a, (A a)ᵀ * γ = γ * A (star a) := fun a => by
    have := congrArg g (hc a)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hg] at this
    rw [hγ, Finset.mul_sum, Finset.sum_mul]
    convert this using 2 with i _ i _
    · rw [hT]; simp only [Matrix.mul_assoc]
    · rw [star_mul, map_mul]; simp only [Matrix.mul_assoc]
  have hβ : ((discr E : ℤ) : k) • β = ∑ i, (A (x i))ᵀ * ((A (y i))ᵀ * β) := by
    have := congrArg (fun a => (A a)ᵀ * β) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, transpose_sum, Finset.sum_mul, hT, Matrix.mul_assoc, map_intCast,
      transpose_intCast] at this
    rw [this, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  have hdiff : ∀ i j, (((discr E : ℤ) : k) • β - γ) i j ∈ S := fun i j => by
    have e : ((discr E : ℤ) : k) • β - γ =
        ∑ l, (A (x l))ᵀ * ((A (y l))ᵀ * β - β * A (star (y l))) := by
      rw [hβ, hγ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.mul_sub, Matrix.mul_assoc]
    rw [e, Matrix.sum_apply]
    refine Subring.sum_mem _ fun l _ => ?_
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hA _ _ _) (hbal _ _ _)
  refine ⟨u • (γ + γᵀ), ?_, fun a => ?_, fun i j => ?_⟩
  · rw [transpose_smul, transpose_add, transpose_transpose, add_comm]
  · have h := congrArg transpose (hγbal (star a))
    rw [transpose_mul, transpose_mul, transpose_transpose, star_star] at h
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hγbal, h]
  · have h := sub_mem (add_mem (hdiff i j) (hdiff j i)) (mul_mem (intCast_mem S (discr E)) (hsym i j))
    convert h using 1
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul]
    rw [mul_sub, ← mul_assoc, hu]
    push_cast
    ring

section Ring

variable {R k : Type} [CommRing R] [CommRing k] [Algebra ℚ k] {φ : R →+* k} {d : ℕ}

theorem pow_mul_const_dmonOf_mem {F : Pt k 2 d} (iF : IP φ F) {ι : Type} [Fintype ι] (U : ι → Fin d → k)
    (hu : ∀ l i, U l i ∈ φ.range) (δ : k) (hδ : δ ∈ φ.range) (q : PS k 1 d) (q0 : constantCoeff q = 0)
    (q1 : ∀ l, constantCoeff (Dof F (U l) q) = 0)
    (q2 : ∀ l l', C δ * Dof F (U l) (Dof F (U l') q) ∈ IntS φ 1 d) (m : ℕ) (f : PS k 1 d)
    (hf : f ∈ IntS φ 1 d) (α : ι →₀ ℕ) :
    δ ^ α.degree * constantCoeff (DmonOf F U α (f * FB.expS k ((m : k) • q))) ∈ φ.range := by
  let M : Subring (PS k 1 d) :=
    Subring.closure ((IntS φ 1 d : Set (PS k 1 d)) ∪ Set.range fun l => C δ * Dof F (U l) q)
  have hI : ∀ g ∈ IntS φ 1 d, g ∈ M := fun g hg => Subring.subset_closure (Or.inl hg)
  have hp : ∀ l, C δ * Dof F (U l) q ∈ M := fun l => Subring.subset_closure (Or.inr ⟨l, rfl⟩)
  have hc : ∀ g ∈ M, constantCoeff g ∈ φ.range := by
    intro g hg
    have : M ≤ φ.range.comap (constantCoeff (σ := Fin 1 × Fin d) (R := k)) := by
      refine Subring.closure_le.2 ?_
      rintro x (hx | ⟨l, rfl⟩)
      · exact int_const hx
      · show constantCoeff (C δ * Dof F (U l) q) ∈ φ.range
        rw [map_mul, q1, mul_zero]
        exact zero_mem _
    exact this hg
  have hD : ∀ l, ∀ g ∈ M, C δ * Dof F (U l) g ∈ M := by
    intro l g hg
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with hx | ⟨l', rfl⟩
      · exact hI _ (mul_mem (int_C hδ) (dof_int iF (hu l) hx))
      · rw [GE.dof_C_mul]
        exact hI _ (mul_mem (int_C hδ) (q2 l l'))
    | zero => simp [Dof]
    | one => simp [Dof]
    | add x y _ _ hx hy => rw [GE.dof_add, mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [← GE.dofD_apply, map_neg, GE.dofD_apply, mul_neg]; exact neg_mem hx
    | mul x y h1 h2 hx hy =>
      have := add_mem (mul_mem hx h2) (mul_mem h1 hy)
      convert this using 1
      rw [GE.dof_mul]
      ring
  have hmq : constantCoeff ((m : k) • q) = 0 := by rw [smul_eq_C_mul, map_mul, q0, mul_zero]
  let P : ℕ → PS k 1 d → Prop := fun n x => ∃ g ∈ M, C δ ^ n * x = g * FB.expS k ((m : k) • q)
  have step : ∀ l n x, P n x → P (n + 1) (Dof F (U l) x) := by
    rintro l n x ⟨g, hg, e⟩
    refine ⟨C δ * Dof F (U l) g + g * (m : PS k 1 d) * (C δ * Dof F (U l) q),
      add_mem (hD l g hg) (mul_mem (mul_mem hg (natCast_mem M m)) (hp l)), ?_⟩
    have e' := congrArg (Dof F (U l)) e
    rw [← map_pow, GE.dof_C_mul, GE.dof_mul, Nab.dof_expS F _ hmq] at e'
    have e2 : Dof F (U l) ((m : k) • q) = (m : PS k 1 d) * Dof F (U l) q := by
      rw [smul_eq_C_mul, GE.dof_C_mul, map_natCast]
    rw [e2, map_pow] at e'
    rw [pow_succ', mul_assoc, e']
    ring
  have iter : ∀ l (j : ℕ) n x, P n x → P (j + n) ((Dof F (U l))^[j] x) := by
    intro l j n x hx
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      rw [Function.iterate_succ_apply', add_right_comm]
      exact step l _ _ ih
  have fold : ∀ L : List ι, P (L.map α).sum
      (L.foldr (fun l g => (Dof F (U l))^[α l] g) (f * FB.expS k ((m : k) • q))) := by
    intro L
    induction L with
    | nil => exact ⟨f, hI f hf, by simp⟩
    | cons a L ih => exact iter a _ _ _ ih
  obtain ⟨g, hg, e⟩ := fold (Finset.univ : Finset ι).toList
  have e' := congrArg constantCoeff e
  have hE : constantCoeff (FB.expS k ((m : k) • q)) = 1 := by
    unfold FB.expS
    rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hmq),
      finsum_eq_single _ 0]
    · simp
    · intro j hj
      rw [map_pow, hmq, zero_pow hj, smul_zero]
  rw [map_mul, map_mul, map_pow, constantCoeff_C, Finset.sum_map_toList, hE, mul_one] at e'
  rw [Finsupp.degree_eq_sum, DmonOf, e']
  exact hc g hg

end Ring

theorem dpolyOf_monomial_one {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (mo : ι →₀ ℕ) (g : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g = DmonOf F u mo g := by
  classical
  have e : DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g =
      ∑ m ∈ ({mo} : Finset (ι →₀ ℕ)), C ((MvPolynomial.monomial mo (1 : k)).coeff m) * DmonOf F u m g := by
    unfold DpolyOf
    refine Finset.sum_subset MvPolynomial.support_monomial_subset fun x _ hx => ?_
    rw [MvPolynomial.notMem_support_iff.1 hx, map_zero, zero_mul]
  rw [e, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, map_one, one_mul]

theorem pow_mul_nabVal_mem {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (k : Type)
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (g : PS k 2 d) (hg : B.IsCanonGauge k g) (δ : k)
    (hδ : δ ∈ (algebraMap R k).range) (hβ : ∀ i j, δ * bilinPart k g i j ∈ (algebraMap R k).range)
    (w0 : O) (m : ℕ) (f : PS R 1 d) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι →₀ ℕ) :
    δ ^ α.degree * B.nabVal k g w0 m (FB.toK k f) (fun l i => algebraMap R k (u l i))
      (MvPolynomial.monomial α 1) ∈ (algebraMap R k).range := by
  have iF : IP (algebraMap R k) (B.FK k) := ⟨B.G.F, B.G.const, rfl⟩
  have iw : IP (algebraMap R k) (B.actK k w0) := ⟨B.A.act w0, B.A.const w0, rfl⟩
  have hF := iF.gp
  have hw := iw.gp
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k w0) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k w0) (pt k (n := 2) d 0))
      (comp1 (B.actK k w0) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom w0)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const w0) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const w0) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have c0 : constantCoeff g = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 0 (by simp)
  have c1 : ∀ s, constantCoeff (pderiv (R := k) s g) = 0 := fun s => by
    rw [const_pderiv]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 _ (by simp)
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  have hl : DI (algebraMap R k) (defL (B.FK k) g) := by
    refine di_of_exp B.ph1 ?_ _ ?_ hg.ph1
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleLeft_zero_fst, map_one]
    · rw [defL, map_sub, map_add (f := _), gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (gp_addOf _ hF _ _ (hp _) (hp _)) (hp _)) _ c0]
      simp
  have hr : DI (algebraMap R k) (defR (B.FK k) g) := by
    refine di_of_exp B.ph2 ?_ _ ?_ hg.ph2
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleRight_zero_fst, map_one]
    · rw [defR, map_sub, map_add (f := _), gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (gp_addOf _ hF _ _ (hp _) (hp _))) _ c0]
      simp
  have hu : ∀ l i, algebraMap R k (u l i) ∈ (algebraMap R k).range := fun l i => ⟨u l i, rfl⟩
  have hq : B.hL k g w0 = ev (n := 1) ![pt k d 0, B.actK k w0] g := by
    rw [FB.hL, gt_comp1_pt_right]
  have hW : ∀ l j, coeff (Finsupp.single ((0 : Fin 1), l) 1) (B.actK k w0 j) ∈ (algebraMap R k).range :=
    fun l j => ⟨coeff (Finsupp.single ((0 : Fin 1), l) 1) (B.A.act w0 j), by simp only [FB.actK, coeff_map]⟩
  rw [FB.nabVal, dpolyOf_monomial_one, hq]
  refine pow_mul_const_dmonOf_mem iF _ hu δ hδ _ (gt_const_ev _ (pair_points_zero_constant (gp_pt 0) hw) _ c0)
    (fun l => ?_) (fun l l' => ?_) m _ ⟨f, rfl⟩ α
  · rw [Dof]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, constantCoeff_pderiv_formalSubst_two _ _ (gp_pt 0) hw, c1, zero_mul,
      Finset.sum_const_zero, add_zero, mul_zero]
  · have h := mul_mem (int_C (n := 1) (d := d) hδ) (quad_int iF hU iw hom g c1 hl hr (hu l) (hu l'))
    rw [mul_sub, ← map_mul] at h
    have h' := add_mem h (int_C (n := 1) (d := d) (add_mem
      (sum_mem (t := Finset.univ) fun j _ => mul_mem
        (sum_mem (t := Finset.univ) fun a _ => mul_mem (hu l' a) (hW a j))
        (sum_mem (t := Finset.univ) fun i _ => mul_mem (hu l i) (hβ i j)))
      (sum_mem (t := Finset.univ) fun i _ => mul_mem (hu l' i)
        (sum_mem (t := Finset.univ) fun a _ => mul_mem (hu l a)
          (sum_mem (t := Finset.univ) fun j _ => mul_mem (hβ i j) (hW a j))))))
    convert h' using 1
    rw [sub_add_eq_add_sub, eq_sub_iff_add_eq]
    congr 2
    simp only [bilinPart, mul_add, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => by ring
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => by ring

theorem exists_canonGauge_nabVal_bounded_denom :
    ∀ (V k : Type) [CommRing V] [CommRing k] [Algebra ℚ k] [Algebra V k] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (d : ℕ) (B : FB V d (𝓞 E)) (h : PS k 2 d), B.IsCanonGauge k h → ∃ h' : PS k 2 d, B.IsCanonGauge k h' ∧ ∀ (w0 : 𝓞 E) (m : ℕ) (f : PS V 1 d) (ι : Type) [Fintype ι] (u : ι → Fin d → V) (α : ι →₀ ℕ), ((2 * NumberField.discr E : ℤ) : k) ^ α.degree * B.nabVal k h' w0 m (FB.toK k f) (fun l i => algebraMap V k (u l i)) (MvPolynomial.monomial α 1) ∈ (algebraMap V k).range := by
  intro V k _ _ _ _ E _ _ _ d B h hc
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := GlobalTheory.bilinPart_canonGauge_congr V d (𝓞 E) k B h hc
  let A : 𝓞 E →+* Matrix (Fin d) (Fin d) k :=
    { toFun := dAct k B
      map_one' := c4
      map_mul' := c6
      map_add' := c5
      map_zero' := by
        have e := c5 0 0
        rw [add_zero] at e
        exact left_eq_add.1 e }
  obtain ⟨β, b1, b2, b3⟩ := exists_symm_balanced (algebraMap V k).range E A c3 (bilinPart k h) c1 c2
  obtain ⟨h', hc', e⟩ := GlobalTheory.GaugeShift.canon_sub_bilin V d (𝓞 E) k B h hc β b1 b2
  exact ⟨h', hc', fun w0 m f ι _ u α =>
    pow_mul_nabVal_mem k B h' hc' _ (intCast_mem _ _) (e ▸ b3) w0 m f ι u α⟩

end GlobalTheory.GaugeBoundedDenom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShortThetaValueBoundedGoodReduction
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodThetaBound

section Parts

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PlaceInt GlobalTheory.GoodPts
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem unif_of_splitModel {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (I : IntData Xo c T io y.1)
    (hS : PullbackSections.SplitModel I) : ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, P.TorsionIso := by
  have hprop : IsProper I.t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) I.m1.cart.1 Xo.univ.proper
  obtain ⟨j, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance I.G I.G I.t' hprop I.m2 I.m2
  have hp := GlobalTheory.UnifAfterExt.polAt_of_sabMap j I.m2 I.m1 Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (jK T.V) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨-, P, -, hP⟩ := GlobalTheory.UnifAfterExt.isOpen_and_uniformised T.V inferInstance I.G hp hS
  exact ⟨P, hP⟩

theorem root_pow_sq {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) {N : ℕ} (hN : l.M ∣ N) (a : Dw.La)
    {t : ptO Xo x ⟶ Xo.univ.t.G} (ht : t ^ N = levPt Xo x a) : t ^ (N ^ 2) = 1 := by
  obtain ⟨k, hk⟩ := hN
  have h : levPt Xo x a ^ l.M = 1 := by
    rw [levPt, ← MonObj.comp_pow, (GlobalTheory.moduli_univ_eta_killed GlobalTheory.firstFiveLaws.1 E H Dw l Xo a).2.2, MonObj.comp_one]
  rw [pow_two, pow_mul, ht, hk, pow_mul, h, one_pow]

theorem reach_of_isUUOver {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {N : ℕ} (hN : Odd N) (s : SecN Xo x 1)
    {x₁ x₂ : ptO Xo x ⟶ Xo.univ.t.G} (h₁ : x₁ ^ (N ^ 2) = 1) (h₂ : x₂ ^ (N ^ 2) = 1)
    {F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo x))}
    (hF : IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F) : Reach Xo s (N ^ 2) (sqN Xo N F) := by
  obtain ⟨F₀, F₁, p, m₁, m₂⟩ := ((uu_through_moves E H Dw l Xo S x N hN s).1 x₁ x₂ F h₁ h₂).1 hF
  refine .move _ x₂ F₁ _ (.move _ x₁ F₀ F₁ (.pull 1 (N ^ 2) (N ^ 2) (N : 𝓞 E) s F₀ .base (.inl rfl) hN.pow ?_
    (Nat.one_mul _).symm p) m₁) m₂
  rw [map_natCast, Nat.cast_pow, pow_two]

theorem splitModel_of_good {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (hy : GoodPts.Good y)
    (I : IntData Xo c T io y.1) : PullbackSections.SplitModel I := by
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, hG⟩ := hy
  obtain ⟨-, n, -⟩ := GlobalTheory.ThetaBound.Prep.sab_extensions_iso E H Dw l Xo T.V T.Fr y.1.x I.G G I.t' t' I.m1 I.m2 m1 m2
  have hp : IsProper I.G.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n.cart.1 hG
  exact ⟨_, GlobalTheory.ZJ.isGt_splitExtOfAbelian _ (GlobalTheory.isAbelianScheme_pullback_obj _ _
    (isAbelianScheme_of_proper _ I.G.semi hp))⟩

theorem exists_ext [StarRing (𝓞 E)] (hstar : ∀ a : 𝓞 E, star a = H.bar a) {T : CDVR} {io : c.F →+* T.Fr}
    (y : IntFr Xo c T io) (hy : GoodPts.Good y) (M : ℕ) (hM : 0 < M) :
    ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io))
      (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ Good3 C' ∧ AllRat Xo (xOf y') M := by
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists E H Dw l Xo c hstar T io y
  have hgood₁ : Good3 C₁ := ⟨hC₁, unif_of_splitModel C₁.I (splitModel_of_good y hy C₁.I)⟩
  obtain ⟨L, _, _, hL, hrat⟩ := (GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo T.Fr (xOf y) M hM).1
  obtain ⟨T₂, i₂, e₂, ψ, φ, he₂, hv₂, hψ, -, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
  obtain ⟨⟨y₂, hext₂⟩, hy⟩ := GlobalTheory.ThetaBound.exists_isExt_and_trans E H Dw l Xo c T T₂ io y i₂ e₂ he₂ hv₂
  have hx₂ := (hy y₂ hext₂).1
  obtain ⟨C₂, hgood₂⟩ :=
    GlobalTheory.ThetaBound.Prep.exists_good_chart_ext E H Dw l Xo c hstar T io y C₁ hgood₁ T₂ i₂ e₂ y₂ hext₂
  have hrat₂ := ((GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo L _ M hM).2 hrat).1 T₂.Fr ψ.toRingHom
  have hi : i₂ = ψ.toRingHom.comp (algebraMap T.Fr L) := RingHom.ext fun a => (hψ a).symm
  have hsp : spMap ψ.toRingHom ≫ spMap (algebraMap T.Fr L) ≫ xOf y = xOf y₂ := by
    rw [hx₂, hi, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  rw [hsp] at hrat₂
  exact ⟨T₂, i₂, e₂, y₂, C₂, hext₂, hgood₂, hrat₂⟩

theorem sum_degree_colOf {n : ℕ} (m : LtN Dw n →₀ ℕ) : ∑ b, (colOf m b).degree = m.degree := by
  simp only [Finsupp.degree_eq_sum, colOf, Finsupp.equivFunOnFinite_symm_apply_apply]
  rw [Finset.sum_comm, Fintype.sum_sigma, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun τ _ => (Fintype.sum_prod_type (fun p : Fin (Dw.mult τ) × Fin n => m ⟨τ, p⟩)).symm

theorem hv_bound [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab) {T : CDVR} {io : c.F →+* T.Fr}
    (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (k n d : ℕ) (F : Fin n → SecN Xo (xOf y) k)
    (f : Fin n → PS T.V 1 (chD C.ch)) (hf : ∀ b, GermIs C k (F b) (f b)) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1)) (hd : P.IsHomogeneous d)
    (hc : ∀ m, InV T (io (P.coeff m))) :
    letI := io.toAlgebra
    InV T (((2 * NumberField.discr E : ℤ) : T.Fr) ^ d * hv Xo c nab y.1 k F P) := by
  letI := io.toAlgebra
  obtain ⟨B, hB, hB2⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hnab.1 T io y C
  obtain ⟨h', hg', hbd⟩ := GlobalTheory.GaugeBoundedDenom.exists_canonGauge_nabVal_bounded_denom T.V T.Fr E _ B _ (hB2 B hB).1
  have tk : ∀ {r : ℕ} (g : PS T.Fr r (chD C.ch)), FB.toK T.Fr g = g := fun g => by
    ext m
    simp
  have h1 : C.ch.B.FK T.Fr = B.FK T.Fr := by
    funext j
    simp only [FB.FK, FGLaw.mapF, hB.1, ← C.gen.1.1 j]
    simp
  have h2 : ∀ a, C.ch.B.actK T.Fr a = B.actK T.Fr a := by
    intro a
    funext j
    simp only [FB.actK, hB.2.1, ← C.gen.1.2.1 a j]
    simp
  have hg : C.ch.B.IsCanonGauge T.Fr h' := by
    refine ⟨hg'.ax0, hg'.ax1, ?_, ?_, ?_, fun a => ?_⟩
    · rw [h1, tk, ← hg'.ph1, hB.2.2.1]
      exact C.gen.1.2.2.1
    · rw [h1, tk, ← hg'.ph2, hB.2.2.2.1]
      exact C.gen.1.2.2.2.1
    · rw [tk, ← hg'.sy, hB.2.2.2.2.1]
      exact C.gen.1.2.2.2.2.1
    · rw [h2, h2, tk, ← hg'.ad, hB.2.2.2.2.2]
      exact C.gen.1.2.2.2.2.2.1 a
  let C' : ChartAt Xo c y.1 := { C.ch with h := h', gauge := hg }
  obtain ⟨C₀, hex, hpin⟩ := hnab.2 T.Fr y.1
  choose f₀ hf₀ using fun b => hex k (F b)
  have e₀ : ∀ m, ∏ b, nab y.1 k (F b) (colOf m b) =
      ∏ b, C₀.B.nabVal T.Fr C₀.h H.w0 k (f₀ b) C₀.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin k (F b) (f₀ b) (hf₀ b) (colOf m b)
  have h := GlobalTheory.HarmonicAny.chartVal_indep_of_harmonic E H Dw l Xo c hnab.1 T.Fr y.1 C₀ C' k n F f₀
    (fun b => MvPowerSeries.map (algebraMap T.V T.Fr) (f b)) hf₀ hf P hP
  have e₁ : hv Xo c nab y.1 k F P = chartVal C₀ k f₀ P := by
    simp only [hv, chartVal, e₀]
  rw [e₁, h, chartVal, Finset.mul_sum]
  refine Subring.sum_mem _ fun m hm => ?_
  have hm' : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hd (MvPolynomial.mem_support_iff.1 hm)
  rw [_root_.mul_left_comm, ← hm', ← sum_degree_colOf, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Subring.mul_mem _ (hc m) (Subring.prod_mem _ fun b _ => ?_)
  have hu : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i) :=
    funext fun ℓ => funext fun i => C.gen.1.2.2.2.2.2.2 ℓ i
  have key := hbd H.w0 k (f b) (Lt1 Dw) C.uvecT (colOf m b)
  rw [← hu] at key
  have e : C'.B.nabVal T.Fr C'.h H.w0 k (MvPowerSeries.map (algebraMap T.V T.Fr) (f b)) C'.uvec
      (MvPolynomial.monomial (colOf m b) 1) =
      B.nabVal T.Fr h' H.w0 k (FB.toK T.Fr (f b)) C.ch.uvec (MvPolynomial.monomial (colOf m b) 1) := by
    change C.ch.B.nabVal T.Fr h' H.w0 k (FB.toK T.Fr (f b)) C.ch.uvec _ = _
    simp only [FB.nabVal, FB.hL, h1, h2]
  rw [e]
  exact key

theorem inV_of_ext {T T' : CDVR} (iT : T.Fr →+* T'.Fr) {e : ℕ} (he : 0 < e)
    (hv : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) {x : T.Fr} : InV T' (iT x) ↔ InV T x := by
  constructor
  · rintro ⟨a, ha⟩
    have h := GlobalTheory.ThetaBound.Prep.vV_nonneg T' a
    rw [ha, hv] at h
    exact Formalism.L2.PjFree.mem_range_of_vV_nonneg
      (le_of_mul_le_mul_left (by simpa using h) (by exact_mod_cast he : (0 : ℤ) < e))
  · rintro ⟨a, rfl⟩
    exact Formalism.L2.PjFree.mem_range_of_vV_nonneg (by
      rw [hv]; exact mul_nonneg (by exact_mod_cast he.le) (GlobalTheory.ThetaBound.Prep.vV_nonneg T a))

theorem scalar_cases {K : Type} [Field K] [CharZero K] (m r N d d' : ℕ) (D : ℤ) (s : K) (h : d' = d ∨ s = 0) :
    ∃ ε : ℕ, ((m * r : ℕ) : K) * ((2 * D * N : ℤ) : K) ^ d *
      ((1 : K)⁻¹ * (m : K)⁻¹ * (r : K)⁻¹ * ((N : K) ^ d')⁻¹ * s) = ε * (((2 * D : ℤ) : K) ^ d * s) := by
  rcases h with rfl | rfl
  · by_cases h0 : (m : K) = 0 ∨ (r : K) = 0 ∨ (N : K) ^ d' = 0
    · refine ⟨0, ?_⟩
      rcases h0 with h | h | h <;> simp [h]
    · push Not at h0
      obtain ⟨a, b, c⟩ := h0
      refine ⟨1, ?_⟩
      push_cast
      rw [mul_pow]
      field_simp
  · exact ⟨0, by simp⟩

end Parts

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts

theorem theta_value_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (n d N : ℕ) (La : GenLat E n) (w : (Fin n → LevQ Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F) (v : T.Fr), Good y → La.Unimod → La.TrivAt l.M → La.LevOK N l.M → (∀ q, InV T (io (w q))) → P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) → P.IsHomogeneous d → (∀ m, InV T (io (P.coeff m))) → (letI := io.toAlgebra; thLaValAt Xo c nab w La N P y.1 v) → InV T (((La.mIdx N (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw l) : ℕ) : T.Fr) * ((2 * NumberField.discr E * N : ℤ) : T.Fr) ^ d * v) := by
  intro E _ _ _ H Dw l Xo c _ nab hnab T io y n d N La w P v hy hU hT hL hw hP hd hc hv
  obtain ⟨T', iT, e, y', C, ⟨he, hval, φ, hφ, hmap⟩, hC, hrat⟩ :=
    exists_ext hnab.1 y hy (N ^ 2) (pow_pos hL.1.pos 2)
  letI := io.toAlgebra
  letI := (iT.comp io).toAlgebra
  obtain ⟨z, tp, F, hz, hg, ht, hF⟩ :=
    (GlobalTheory.RatData.exists_thetaVal_data E H Dw l Xo c T'.Fr y'.1).2 n La N hU hL hrat
  have key := GlobalTheory.HarmonicAny.map_shortValAt nab hnab La N hU hT hL P hP w 1 φ y.1 y'.1 hmap z tp F hz hg ht hF v hv
  have hφv : φ v = iT v := congrArg (fun g : T.Fr →+* T'.Fr => g v) hφ
  choose f hf using fun q i b => (GlobalTheory.RegularGerm.regular_germ E H Dw l Xo c hnab.1 T' _ y' C hC.1 (N ^ 2) _).1
    (GlobalTheory.ReachRegular.regular_of_reach E H Dw l Xo c hnab.1 T' _ y' C hC (N ^ 2) _
      (reach_of_isUUOver hL.1 (GlobalTheory.PlaceInt.sOf1 y') ((hz i).1 b)
        (root_pow_sq _ hL.2.1 _ (ht q b).1) (hF q i b)))
  have hb := fun q i => hv_bound nab hnab y' C (N ^ 2) n d _ (f q i) (hf q i) P hP hd
    (fun m => (inV_of_ext iT he hval).2 (hc m))
  have hcast := (GlobalTheory.PlaceInt.hv_linear E H Dw l Xo c hnab.1 nab hnab T'.Fr y'.1 n P).2.2 N
  haveI := GlobalTheory.ShortAtField.finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  haveI : CharZero T'.Fr := algebraRat.charZero _
  rw [← inV_of_ext iT he hval, map_mul, map_mul, map_pow, map_natCast, map_intCast, ← hφv, key]
  simp only [map_mul, map_inv₀, map_one, map_natCast, map_pow]
  have hcases : P.totalDegree = d ∨ (∑ᶠ q : Fin n → LevQ Dw l, algebraMap c.F T'.Fr (w q) *
      ∑ i, ∑ m ∈ P.support, algebraMap c.F T'.Fr (P.coeff m) *
        ∏ b, nab y'.1 ((N : ℤ) ^ 2) (F q i b) (colOf m b)) = 0 := by
    by_cases h0 : P = 0
    · right
      subst h0
      simp
    · exact Or.inl (hd.totalDegree h0)
  obtain ⟨ε, hε⟩ := scalar_cases (La.mIdx N (Dw.p + Dw.q)) (Nat.card (Fin n → LevQ Dw l)) N d P.totalDegree
    (NumberField.discr E) _ hcases
  rw [hε]
  refine Subring.mul_mem _ (natCast_mem _ ε) ?_
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Subring.sum_mem _ fun q _ => ?_
  rw [mul_left_comm, Finset.mul_sum]
  refine Subring.mul_mem _ ((inV_of_ext iT he hval).2 (hw q)) (Subring.sum_mem _ fun i _ => ?_)
  rw [hcast (F q i)]
  exact hb q i

end GlobalTheory.GoodThetaBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShortThetaValueBoundedGoodReductionStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortThetaValue_bounded_goodReduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (n d N : ℕ) (La : GenLat E n) (w : (Fin n → LevQ Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F) (v : T.Fr), Good y → La.Unimod → La.TrivAt l.M → La.LevOK N l.M → (∀ q, InV T (io (w q))) → P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) → P.IsHomogeneous d → (∀ m, InV T (io (P.coeff m))) → (letI := io.toAlgebra; thLaValAt Xo c nab w La N P y.1 v) → InV T (((La.mIdx N (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw l) : ℕ) : T.Fr) * ((2 * NumberField.discr E * N : ℤ) : T.Fr) ^ d * v) := by
  first | exact @GlobalTheory.GoodThetaBound.theta_value_bounded | exact GlobalTheory.GoodThetaBound.theta_value_bounded | (intros; apply GlobalTheory.GoodThetaBound.theta_value_bounded <;> assumption)
end
