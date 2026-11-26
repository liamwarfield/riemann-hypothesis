module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqLoc
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependent
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioFirstPartialLaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSecondPartialLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSecondPartialLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartCmp.RatioSecondLaw
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh GlobalTheory.FrameBiextId

section Dict
variable {S : Type} [CommRing S] {d n k m : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0} {x0 : Sp S ⟶ X0}
  {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {y : (jOG x0 d m n).left} {J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι}

theorem frame_value_second_partial_law (hJ : Good t.PP.L y J) (G : FGLaw S d) {e : ∀ m, FrTyG t x0 d x m} {ph2 : PS S 3 d}
    (hf : FamPh2 t x0 d x G.F ph2 e) (u v w : Q S d n) :
    VV m y (E3 ph2 u v w) = (cubV t.cub y J (PP m x v) (PP m x w) (PP m x u) *
    (ee x e y J u (op (FQ G) v w))⁻¹ * ee x e y J u v * ee x e y J u w).val := by
  obtain ⟨U, hU, h⟩ := hf m
  have hc := gm_unit (y := y) U ![u, v, w]
  have e₀ := val_peG x hJ e ![u, v, w] ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (G.F j)] (gen 0) (op (FQ G) (gen 1) (gen 2))
    (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, hF 1 2 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, (cc_psIn d m _ _).trans (G.const j)])
  rw [sq_op, sq_gen, sq_gen, sq_gen] at e₀
  have k := (val_th hJ ![u, v, w] 1 2 0).symm.trans ((val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 0 1))) ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 0 2))))))))))
  refine (hc _ hU).symm.trans (congrArg Units.val (Additive.ofMul.injective ?_))
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul, ofMul_inv, Matrix.cons_val] at k' ⊢
  linear_combination (norm := abel) -k'

theorem mk_psIn_one (Φ : Q S d 1) (i : Fin k) (j : Fin d) :
    (Ideal.Quotient.mk _ (psIn d m ![i] (Φ.1 j)) : Jet S (Fin k × Fin d) m) = psJet m ((ac Φ (gen i) : Q S d k).1 j) :=
  (mk_psIn m _ _).trans (congrArg (fun b => psJet m (sb b (Φ.1 j))) (funext fun l => by fin_cases l; rfl))

end Dict

section Rel
variable {V : Type} [CommRing V] {d n m : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
  {x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {y : (jOG (𝟙 (Sp V)) d m n).left}
  {J : ((jOG (𝟙 (Sp V)) d m n).left ⟶ t.G.left) → t.PP.L.ι}

theorem PP_rel (Φ : Q V d 1) (h : CoordRel x x' Φ.1) (u : Q V d n) : PP m x' u = PP m x (ac Φ u) := by
  have e := h m
  rw [subst_eq m _ ![Φ] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl)
    (fun s => (cc_psTrunc m _).trans (Φ.2 _))] at e
  exact (congrArg (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jQ m ![u]) ≫ ·) e).trans (PP_sq m x _ _)

theorem val_eps (hJ : Good t.PP.L y J) (Φ : Q V d 1) {e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m}
    {e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m} {ε : PS V 2 d} (h : FrRel t x x' e e' Φ.1 m ε) (u v : Q V d n) :
    VV m y (E2 ε u v) = (ee x' e' y J u v * (ee x e y J (ac Φ u) (ac Φ v))⁻¹).val := by
  obtain ⟨U, hU, h⟩ := h
  have hc := gm_unit (y := y) U ![u, v]
  have e₀ := val_peG x hJ e ![u, v] ![fun j => psIn d m ![0] (Φ.1 j), fun j => psIn d m ![1] (Φ.1 j)]
    (ac Φ (gen 0)) (ac Φ (gen 1))
    (by rintro ⟨l, j⟩; fin_cases l; exacts [mk_psIn_one Φ 0 j, mk_psIn_one Φ 1 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [(cc_psIn d m _ _).trans (Φ.2 j), (cc_psIn d m _ _).trans (Φ.2 j)])
  rw [sq_ac, sq_ac, sq_gen, sq_gen] at e₀
  have k : ee x' e' y J u v = _ := (val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl e₀))
  exact (hc _ hU).symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

theorem ac_op_trans (G G' : FGLaw V d) (Φ Ψ : Q V d 1) (hi : comp1 Φ.1 Ψ.1 = pt V (n := 1) d 0)
    (h : ∀ i, G'.F i = transF G.F Φ.1 Ψ.1 i) (u v : Q V d n) :
    ac Φ (op (FQ G') u v) = op (FQ G) (ac Φ u) (ac Φ v) := by
  have h1 : (FQ G' : Q V d 2) = ac Ψ (op (FQ G) (ac Φ (gen 0)) (ac Φ (gen 1))) := by
    apply Subtype.ext
    simp only [ac_val, op_val]
    exact funext h
  have h2 : ac Φ Ψ = gen 0 := Subtype.ext ((ac_val _ _).trans hi)
  have h3 : ∀ w : Q V d n, ac Φ (ac Ψ w) = w := fun w => by
    have := congrArg (sq ![w]) h2
    rw [sq_ac, sq_gen] at this
    exact this
  rw [op, h1, sq_ac, h3, sq_op, sq_ac, sq_ac, sq_gen, sq_gen]
  rfl

end Rel

theorem ratio_second_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamPh2 t (𝟙 (Sp V)) d x B.G.F B.ph2 e → FamPh2 t (𝟙 (Sp V)) d x' B'.G.F B'.ph2 e' → JEq m (B'.ph2 * ev (n := 3) ![pt V (n := 3) d 0, addOf B'.G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)] ε) (ev (n := 3) ![comp1 φ (pt V (n := 3) d 0), comp1 φ (pt V (n := 3) d 1), comp1 φ (pt V (n := 3) d 2)] B.ph2 * (ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 1] ε * ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 2] ε)) := by
  intro E _ _ _ H _ V _ _ t d B B' κ κ' _ _ tg tg' uv uv' x x' e e' φ φi m ε _ _ hi hco hl _ _ _ hr hf hf'
  let Φ : Q V d 1 := ⟨φ, hi.1⟩
  let Ψ : Q V d 1 := ⟨φi, hi.2.1⟩
  have key : psJet m (E3 B'.ph2 (gen 0 : Q V d 3) (gen 1) (gen 2) * E2 ε (gen 0) (op (FQ B'.G) (gen 1) (gen 2))) =
      psJet m (E3 B.ph2 (ac Φ (gen 0)) (ac Φ (gen 1)) (ac Φ (gen 2)) * (E2 ε (gen 0) (gen 1) * E2 ε (gen 0) (gen 2))) := by
    refine cst_ext fun y => ?_
    choose J hJ using fun ψ : (jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left => exists_chart t.PP.isLB (ψ y)
    have hJ : Good t.PP.L (Z := (jOG (𝟙 (Sp V)) d m 3).left) y J := hJ
    show VV (x0 := 𝟙 (Sp V)) m y _ = VV (x0 := 𝟙 (Sp V)) m y _
    simp only [VV_mul, frame_value_second_partial_law hJ _ hf, frame_value_second_partial_law hJ _ hf', val_eps hJ Φ hr, PP_rel Φ hco,
      ac_op_trans B.G B'.G Φ Ψ hi.2.2.1 hl, ← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [formalSeriesValueAtThreePoints_genericPoints, formalSeriesValueAtThreePoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, op_val, ac_val, ac_val, ac_val] at key
  exact ((JCalc.jeq_calculus V m).2.2.2.2.1 _ _ _).2 key

end GlobalTheory.ChartCmp.RatioSecondLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSecondPartialLawStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_ratio_second_partial_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamPh2 t (𝟙 (Sp V)) d x B.G.F B.ph2 e → FamPh2 t (𝟙 (Sp V)) d x' B'.G.F B'.ph2 e' → JEq m (B'.ph2 * ev (n := 3) ![pt V (n := 3) d 0, addOf B'.G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)] ε) (ev (n := 3) ![comp1 φ (pt V (n := 3) d 0), comp1 φ (pt V (n := 3) d 1), comp1 φ (pt V (n := 3) d 2)] B.ph2 * (ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 1] ε * ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 2] ε)) := by
  first | exact @GlobalTheory.ChartCmp.RatioSecondLaw.ratio_second_law | exact GlobalTheory.ChartCmp.RatioSecondLaw.ratio_second_law | (intros; apply GlobalTheory.ChartCmp.RatioSecondLaw.ratio_second_law <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSymmetrySeries
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSymmetrySeries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh GlobalTheory.FrameBiextId

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameRatioSym

theorem jEq_of_psJet {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] {m : ℕ} {f g : MvPowerSeries σ R}
    (h : psJet m f = psJet m g) : JEq m f g := by
  intro e he
  rw [psJet, psJet, FBIdJet.psTrunc_eq, FBIdJet.psTrunc_eq] at h
  have h' : Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ (m + 1)) (MvPowerSeries.truncTotal (m + 1) f) =
      Ideal.Quotient.mk _ (MvPowerSeries.truncTotal (m + 1) g) := h
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at h'
  have := h' e (Nat.lt_succ_of_le he)
  rwa [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_of_le he),
    MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_of_le he), sub_eq_zero] at this

variable {V : Type} [CommRing V] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
  {d n m : ℕ} {x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}
  {e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m} {e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m}
  {y : (jOG (𝟙 (Sp V)) d m n).left} {J : ((jOG (𝟙 (Sp V)) d m n).left ⟶ t.G.left) → t.PP.L.ι}

theorem val_sy (hJ : Good t.PP.L y J) {sy : PS V 2 d} (hf : FamSy t (𝟙 (Sp V)) d x sy e) (u v : Q V d n) :
    VV m y (E2 sy u v) = (ee x e y J v u * (ee x e y J u v)⁻¹).val := by
  obtain ⟨U, hU, h⟩ := hf m
  have hc := gm_unit (y := y) U ![u, v]
  generalize hq : gm (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jQ m ![u, v])).left y ⊤ (unitΓ U) = c at hc
  have k : ee x e y J u v = c⁻¹ * ee x e y J v u := (val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·)
    (((congrArg _ (map_inv (Units.map (toΓ _).toMonoidHom) U)).trans (map_inv _ _)).trans (congrArg (·⁻¹) hq))
    (peXX hJ _ 1 0)))
  refine (hc _ hU).symm.trans (congrArg Units.val ?_)
  rw [k, mul_inv, inv_inv, mul_comm c, mul_inv_cancel_left]

theorem val_ratio (hJ : Good t.PP.L y J) (φ : Q V d 1) {ε : PS V 2 d} (hr : FrRel t x x' e e' φ.1 m ε) (u v : Q V d n) :
    VV m y (E2 ε u v) = (ee x' e' y J u v * (ee x e y J (ac φ u) (ac φ v))⁻¹).val := by
  obtain ⟨U, hU, h⟩ := hr
  have hc := gm_unit (y := y) U ![u, v]
  have hφ : ∀ (i : Fin 2) (j : Fin d), (Ideal.Quotient.mk _ (psIn d m ![i] (φ.1 j)) : Jet V (Fin 2 × Fin d) m) =
      psJet m ((ac φ (gen i) : Q V d 2).1 j) := fun i j =>
    (mk_psIn m _ _).trans (congrArg (fun b => psJet m (sb b (φ.1 j))) (funext fun l => by fin_cases l; rfl))
  have e₀ := val_peG x hJ e ![u, v] ![fun j => psIn d m ![0] (φ.1 j), fun j => psIn d m ![1] (φ.1 j)]
    (ac φ (gen 0)) (ac φ (gen 1)) (by rintro ⟨l, j⟩; fin_cases l; exacts [hφ 0 j, hφ 1 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [(cc_psIn d m _ _).trans (φ.2 j), (cc_psIn d m _ _).trans (φ.2 j)])
  rw [sq_ac, sq_ac, sq_gen, sq_gen] at e₀
  have k : ee x' e' y J u v = _ * ee x e y J (ac φ u) (ac φ v) :=
    (val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl e₀))
  exact (hc _ hU).symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

theorem frameRatio_sy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamSy t (𝟙 (Sp V)) d x B.sy e → FamSy t (𝟙 (Sp V)) d x' B'.sy e' → JEq m (B'.sy * ε) (ev (n := 2) ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)] B.sy * ev (n := 2) ![pt V (n := 2) d 1, pt V (n := 2) d 0] ε) := by
  intro E _ _ _ H _ V _ _ t d B B' κ κ' _ _ tg tg' uv uv' x x' e e' φ φi m ε _ _ hi _ _ _ _ _ hr hs hs'
  let p : Q V d 1 := ⟨φ, hi.1⟩
  have key : psJet m (E2 B'.sy (gen 0 : Q V d 2) (gen 1) * E2 ε (gen 0) (gen 1)) =
      psJet m (E2 B.sy (ac p (gen 0 : Q V d 2)) (ac p (gen 1)) * E2 ε (gen 1) (gen 0)) := cst_ext fun y => by
    choose J hJ using fun ψ : (jOG (𝟙 (Sp V)) d m 2).left ⟶ t.G.left => exists_chart t.PP.isLB (ψ y)
    have hJ' : Good t.PP.L (Z := (jOG (𝟙 (Sp V)) d m 2).left) y J := hJ
    show VV (x0 := 𝟙 (Sp V)) m y _ = VV (x0 := 𝟙 (Sp V)) m y _
    rw [VV_mul, VV_mul, val_sy hJ' hs, val_sy hJ' hs', val_ratio hJ' p hr, val_ratio hJ' p hr, ← Units.val_mul,
      ← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_genericPoints, formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, ac_val, ac_val] at key
  exact jEq_of_psJet key

end GlobalTheory.FrameRatioSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioSymmetrySeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_ratio_symmetry_series : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamSy t (𝟙 (Sp V)) d x B.sy e → FamSy t (𝟙 (Sp V)) d x' B'.sy e' → JEq m (B'.sy * ε) (ev (n := 2) ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)] B.sy * ev (n := 2) ![pt V (n := 2) d 1, pt V (n := 2) d 0] ε) := by
  first | exact @GlobalTheory.FrameRatioSym.frameRatio_sy | exact GlobalTheory.FrameRatioSym.frameRatio_sy | (intros; apply GlobalTheory.FrameRatioSym.frameRatio_sy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCoordinateRelationUniversalJets
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCoordinateRelationUniversalJets
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.Coord
open Formalism.MainNotions.ModuliIntegralCharts.H1

variable {V : Type} [CommRing V]

theorem uniq {G : Over (Sp V)} [GrpObj G] {κ : Type} {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x)
    {A : Type} [CommRing A] [Algebra V A] (aug : A →ₐ[V] V) (m : ℕ) (hk : RingHom.ker aug ^ (m + 1) = ⊥)
    {ψ₁ ψ₂ : Jet V κ m →ₐ[V] A} (h1 : aug.comp ψ₁ = jetAug) (h2 : aug.comp ψ₂ = jetAug)
    (e : Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₁ ≫ x m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₂ ≫ x m) : ψ₁ = ψ₂ := by
  have hy : Formalism.L2.Pj.homAt (𝟙 (Sp V)) aug ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ₁ ≫ x m) = 1 := by
    rw [← Category.assoc, GermD.homAt_comp, h1, hx.2.1]
  exact (hx.2.2 A aug m hk _ hy).unique ⟨h1, rfl⟩ ⟨h2, e⟩

theorem jetSubstP_trunc {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (φ : κ → MvPowerSeries κ' V) :
    jetSubstP m (fun p => psTrunc m (φ p)) = jetSubstPS (m := m) φ := rfl

theorem aug_X {κ : Type} (m : ℕ) (j : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = 0 := ExpUniqJet.augmentation_jet_variable m j

theorem aug_comp_subst {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (m : ℕ)
    (φ : κ → MvPowerSeries κ' V) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    (jetAug : Jet V κ' m →ₐ[V] V).comp (jetSubstPS (m := m) φ) = jetAug := by
  apply GermD.jet_hom_ext
  intro i
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m φ hφ, GaugeR.jetAug_psJet, hφ, aug_X]

theorem exists_coord {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) {x' : GlobalTheory.PowGerm.JetPts G κ'}
    (hx' : GlobalTheory.PowGerm.IsUnivJ G κ' x') :
    ∃ φ : κ → MvPowerSeries κ' V, (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) ∧
      ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φ) ≫ x m := by
  have h := fun m => (hx.2.2 (Jet V κ' m) jetAug m (ExpUniqLoc.ker_aug_pow le_rfl) (x' m) (hx'.2.1 m)).exists
  choose ψ hψa hψ using h
  have hc : ∀ m, (jetTrunc : Jet V κ' (m + 1) →ₐ[V] Jet V κ' m).comp (ψ (m + 1)) =
      (ψ m).comp (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) := by
    intro m
    refine uniq hx (jetAug : Jet V κ' m →ₐ[V] V) (m + 1) (ExpUniqLoc.ker_aug_pow (by omega)) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, ExpUniqLoc.aug_comp_trunc, hψa]
    · rw [← AlgHom.comp_assoc, hψa, ExpUniqLoc.aug_comp_trunc]
    · rw [← GermD.homAt_comp, ← GermD.homAt_comp, Category.assoc, Category.assoc, hx.1, ← hψ, ← hψ, hx'.1]
  have hs := fun i : κ => GaugeR.exists_ps_of_compat
    (fun m => ψ m (Ideal.Quotient.mk _ (MvPolynomial.X i))) (fun m => DFunLike.congr_fun (hc m) _)
  choose φ hφ using hs
  have h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := by
    intro i
    rw [← GaugeR.jetAug_psJet 0, hφ, ← AlgHom.comp_apply, hψa, aug_X]
  refine ⟨φ, h0, fun m => ?_⟩
  have : jetSubstPS (m := m) φ = ψ m := by
    apply GermD.jet_hom_ext
    intro i
    rw [ExpChartJet.jetSubstPS_mk m φ h0, hφ]
  rw [this]
  exact hψ m

theorem subst_eq_X {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) {x' : GlobalTheory.PowGerm.JetPts G κ'}
    {φ : κ → MvPowerSeries κ' V} (h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φ) ≫ x m)
    {φi : κ' → MvPowerSeries κ V} (h0i : ∀ i, MvPowerSeries.constantCoeff (φi i) = 0)
    (hφi : ∀ m, x m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φi) ≫ x' m) (i : κ) :
    MvPowerSeries.subst φi (φ i) = MvPowerSeries.X i := by
  apply GermFun.psJet_inj
  intro m
  have e : (jetSubstPS (m := m) φi).comp (jetSubstPS (m := m) φ) = AlgHom.id V _ := by
    refine uniq hx (jetAug : Jet V κ m →ₐ[V] V) m (ExpUniqLoc.ker_aug_pow le_rfl) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, aug_comp_subst m φi h0i, aug_comp_subst m φ h0]
    · rfl
    · rw [← GermD.homAt_comp, Category.assoc, ← hφ, ← hφi, GermD.homAt_id, Category.id_comp]
  have e' := DFunLike.congr_fun e (Ideal.Quotient.mk _ (MvPolynomial.X i))
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m φ h0, ExpChartJet.jetSubstPS_psJet m φi h0i] at e'
  rw [e', ← MvPolynomial.coe_X]
  exact (GaugeR.psJet_eq_mk m _ _ fun e _ => (MvPolynomial.coeff_coe _ _).symm).symm

end GlobalTheory.ChartCmp.Coord

namespace GlobalTheory.ChartCmp

theorem exists_coordRel_of_isUnivJ : ∀ (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x' → ∃ φ φi : Pt V 1 d, IsInvPair φ φi ∧ CoordRel x x' φ ∧ CoordRel x' x φi := by
  intro V _ G _ d x x' hx hx'
  obtain ⟨φ, h0, hφ⟩ := Coord.exists_coord hx hx'
  obtain ⟨φi, h0i, hφi⟩ := Coord.exists_coord hx' hx
  have key : ∀ f : Fin 1 × Fin d → MvPowerSeries (Fin 1 × Fin d) V, (fun p : Fin 1 × Fin d => f (0, p.2)) = f := by
    intro f
    funext p
    rw [show ((0 : Fin 1), p.2) = p from Prod.ext (Subsingleton.elim _ _) rfl]
  have key2 : ∀ f : Fin 1 × Fin d → MvPowerSeries (Fin 1 × Fin d) V,
      (fun p : Fin 1 × Fin d => (![fun j => f (0, j)] : Fin 1 → Pt V 1 d) p.1 p.2) = f := by
    intro f
    funext p
    obtain ⟨a, b⟩ := p
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rfl
  refine ⟨fun j => φ (0, j), fun j => φi (0, j), ⟨fun i => h0 _, fun i => h0i _, ?_, ?_⟩, fun m => ?_, fun m => ?_⟩
  · funext i
    simp only [comp1, ev, pt]
    rw [key2]
    exact Coord.subst_eq_X hx h0 hφ h0i hφi _
  · funext i
    simp only [comp1, ev, pt]
    rw [key2]
    exact Coord.subst_eq_X hx' h0i hφi h0 hφ _
  · rw [Coord.jetSubstP_trunc m (fun p : Fin 1 × Fin d => φ (0, p.2)), key]
    exact hφ m
  · rw [Coord.jetSubstP_trunc m (fun p : Fin 1 × Fin d => φi (0, p.2)), key]
    exact hφi m

end GlobalTheory.ChartCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsCoordinateRelationUniversalJetsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinateRelation_universalJets : ∀ (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] (d : ℕ) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x' → ∃ φ φi : Pt V 1 d, IsInvPair φ φi ∧ CoordRel x x' φ ∧ CoordRel x' x φi := by
  first | exact @GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ | exact GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ | (intros; apply GlobalTheory.ChartCmp.exists_coordRel_of_isUnivJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TangentDirectionTwoChartsLinearPart
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TangentDirectionTwoChartsLinearPart
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet

namespace GlobalTheory.ChartCmp.CoordDir

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
  {t : SAB H (Sp V)} {d : ℕ}

def tanPt (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (g : Fin 1 × Fin d → V) :
    overAt (𝟙 (Sp V)) (DualNumber V) ⟶ t.G :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (tp g) ≫ x 1

theorem tp_zero : (tp (0 : Fin 1 × Fin d → V)) =
      (Algebra.ofId V (DualNumber V)).comp (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) := by
  apply jet_hom_ext
  intro q
  rw [tp_mk, AlgHom.comp_apply]
  show TrivSqZeroExt.inr (0 : V) =
    algebraMap V (DualNumber V) (MvPolynomial.aeval (fun _ => (0 : V)) (MvPolynomial.X q))
  rw [MvPolynomial.aeval_X, map_zero, TrivSqZeroExt.inr_zero]

theorem fst_tp (g : Fin 1 × Fin d → V) : (TrivSqZeroExt.fstHom V V V).comp (tp g) =
      (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) := by
  apply jet_hom_ext
  intro q
  rw [AlgHom.comp_apply, tp_mk]
  show (0 : V) = MvPolynomial.aeval (fun _ => (0 : V)) (MvPolynomial.X q)
  rw [MvPolynomial.aeval_X]

variable {κ : Type} [Fintype κ] {G : FGLaw V d} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V}
  {tg : κ → (Sp (DualNumber V) ⟶ t.G.left)} {uv : κ → Fin d → V} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}

theorem tanPt_zero (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) : tanPt x 0 = 1 := by
  have hz : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) ≫ x 1 = 1 := hx.zero 1
  rw [tanPt, tp_zero, ← GermD.homAt_comp, Category.assoc, hz, MonObj.comp_one]

theorem tanPt_add (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) (g g' : Fin 1 × Fin d → V) :
    tanPt x (g + g') = tanPt x g * tanPt x g' := by
  let T : Jet V (Fin 2 × Fin d) (0 + 1) →ₐ[V] DualNumber V :=
    tp (fun p : Fin 2 × Fin d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) p.1 p.2)
  have hT : T = tp (fun p : Fin 2 × Fin d =>
    (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) p.1 p.2) := rfl
  have hc : ∀ i : Fin 2, T.comp (jetCopy d (0 + 1) i) =
      tp (fun q : Fin 1 × Fin d => (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) i q.2) := by
    intro i
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetCopy, jetMap_mk, MvPolynomial.aeval_X, hT, tp_mk, tp_mk]
  have h0 : tp (fun q : Fin 1 × Fin d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) 0 q.2) = tp g := by
    congr 1
    funext ⟨i, j⟩
    have : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h1 : tp (fun q : Fin 1 × Fin d =>
      (![fun j => g (0, j), fun j => g' (0, j)] : Fin 2 → Fin d → V) 1 q.2) = tp g' := by
    congr 1
    funext ⟨i, j⟩
    have : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hF : T.comp (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => G.F p.2)) = tp (g + g') := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin d => G.F p.2) (fun p => G.const p.2),
      hT, tp_psJet, tp_mk, G.const, TrivSqZeroExt.inl_zero, zero_add, lin_F]
    simp only [Pi.add_apply, fin_one_pair_eq]
  have hl : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => G.F p.2)) ≫ x 1 =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d (0 + 1) (0 : Fin 2)) ≫ x 1) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d (0 + 1) (1 : Fin 2)) ≫ x 1) :=
    hx.law 1
  have e := congrArg (fun f => Formalism.L2.Pj.homAt (𝟙 (Sp V)) T ≫ f) hl
  simp only [MonObj.comp_mul, ← Category.assoc, GermD.homAt_comp, hc, hF, h0, h1] at e
  exact e

theorem tanPt_sum (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) : ∀ (n : ℕ) (f : Fin n → Fin 1 × Fin d → V),
    tanPt x (∑ i, f i) = (List.ofFn fun i => tanPt x (f i)).prod
  | 0, f => by rw [Fin.sum_univ_zero, List.ofFn_zero, List.prod_nil, tanPt_zero hx]
  | n + 1, f => by rw [Fin.sum_univ_succ, tanPt_add hx, tanPt_sum hx n, List.ofFn_succ, List.prod_cons]

theorem eps_tanPt (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (a : V) (g : Fin 1 × Fin d → V) :
    spMap (epsMul a) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (tp g) ≫ x 1).left = (tanPt x (a • g)).left := by
  have h : (TrivSqZeroExt.map (a • LinearMap.id : V →ₗ[V] V)).comp (tp g) = tp (a • g) := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, tp_mk, tp_mk, TrivSqZeroExt.map_inr]
    rfl
  rw [tanPt, ← h]
  simp only [Over.comp_left, Formalism.L2.Pj.homAt, Over.homMk_left, ← Category.assoc, spMap, epsMul, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

theorem comb_eq (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) {u : Fin d → V} {v : Sp (DualNumber V) ⟶ t.G.left}
    (h : IsCombAtG t (𝟙 (Sp V)) (dirs x) u v) : (tanPt x fun q => u q.2).left = v := by
  obtain ⟨w, hw, hprod⟩ := h
  have hw' : w = fun i => tanPt x (u i • fun q : Fin 1 × Fin d => if q = ((0 : Fin 1), i) then (1 : V) else 0) := by
    funext i
    apply Over.OverMorphism.ext
    rw [hw i, dirs, jetTan_eq_tp, eps_tanPt]
  have hq : ∀ (q : Fin 1 × Fin d) (i : Fin d), (q = ((0 : Fin 1), i)) = (i = q.2) := fun q i =>
    propext ⟨fun h => by rw [h], fun h => by rw [h, fin_one_pair_eq]⟩
  have hs : (∑ i, u i • fun q : Fin 1 × Fin d => if q = ((0 : Fin 1), i) then (1 : V) else 0) =
      fun q => u q.2 := by
    funext q
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hq, mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  rw [← hs, tanPt_sum hx, ← hprod, hw']

theorem tanPt_rel {x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {φ : Pt V 1 d}
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (h : CoordRel x x' φ) (u : Fin d → V) :
    tanPt x' (fun q => u q.2) = tanPt x (fun q => (dLin φ).mulVec u q.2) := by
  have hF : (tp (fun q : Fin 1 × Fin d => u q.2)).comp (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => φ p.2)) =
      tp (fun q : Fin 1 × Fin d => (dLin φ).mulVec u q.2) := by
    apply jet_hom_ext
    intro q
    rw [AlgHom.comp_apply, jetSubstPS_mk (0 + 1) (fun p : Fin 1 × Fin d => φ p.2) (fun p => hφ p.2),
      tp_psJet, tp_mk, hφ, TrivSqZeroExt.inl_zero, zero_add]
    congr 1
    simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mulVec, dotProduct, dLin]
    exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
  have h1 : x' 1 = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := 0 + 1) (fun p : Fin 1 × Fin d => φ p.2)) ≫ x 1 := h 1
  rw [tanPt, tanPt, h1, ← Category.assoc, GermD.homAt_comp, hF]

theorem tanPt_inj {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} (hx : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x)
    {g g' : Fin 1 × Fin d → V} (h : tanPt x g = tanPt x g') : g = g' := by
  have hz : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) ≫ x 1 = 1 := hx.2.1 1
  have h0 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (TrivSqZeroExt.fstHom V V V) ≫ tanPt x g = 1 := by
    rw [tanPt, ← Category.assoc, GermD.homAt_comp, fst_tp, hz]
  have e : tp g = tp g' :=
    (hx.2.2 (DualNumber V) (TrivSqZeroExt.fstHom V V V) (0 + 1) ker_fst_sq (tanPt x g) h0).unique
      ⟨fst_tp g, rfl⟩ ⟨fst_tp g', h⟩
  funext q
  have := congrArg (fun ψ : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V =>
    ψ (Ideal.Quotient.mk _ (MvPolynomial.X q))) e
  simp only [tp_mk] at this
  exact TrivSqZeroExt.inr_injective this

end

theorem coord_dir : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ V _ t d B B' κ κ' _ _ tg tg' uv uv' x x' φ hx hx' hU hφ hrel u u' v hu hu'
  have e : tanPt x (fun q => u q.2) = tanPt x (fun q => (dLin φ).mulVec u' q.2) := by
    rw [← tanPt_rel hφ hrel]
    apply Over.OverMorphism.ext
    rw [comb_eq hx hu, comb_eq hx' hu']
  funext j
  exact congrFun (tanPt_inj hU e) (0, j)

end GlobalTheory.ChartCmp.CoordDir
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TangentDirectionTwoChartsLinearPartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentDirection_two_charts_linearPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (φ : Pt V 1 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → CoordRel x x' φ → ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  first | exact @GlobalTheory.ChartCmp.CoordDir.coord_dir | exact GlobalTheory.ChartCmp.CoordDir.coord_dir | (intros; apply GlobalTheory.ChartCmp.CoordDir.coord_dir <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartsWithFramesRelatedAllOrders
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jRel_of_charts_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ hstar V _ _ t hsurj d B B' κ κ' _ _ tg tg' uv uv' x x' e e' hc hc' hu hu' hf hf'
  obtain ⟨φ, φi, hinv, hx, -⟩ := GlobalTheory.T.exists_coordinateRelation_universalJets V t.G d x x' hu hu'
  obtain ⟨hlaw, hact⟩ := GlobalTheory.T.chart_law_action_eq_transported_of_coordRel E H V t d B B' κ κ' tg tg' uv uv' x x' φ φi hc hc' hu hinv hx
  obtain ⟨hg, h1, h2, hs, ha⟩ := (isFrameG_iff t _ d x _ _ _ _ _ _ e).1 hf
  obtain ⟨hg', h1', h2', hs', ha'⟩ := (isFrameG_iff t _ d x' _ _ _ _ _ _ e').1 hf'
  have h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := hinv.1
  refine ⟨φ, φi, fun m => ?_,
    GlobalTheory.T.tangentDirection_two_charts_linearPart E H V t d B B' κ κ' tg tg' uv uv' x x' φ hc hc' hu h0 hx⟩
  obtain ⟨ε, hε, hr⟩ := GlobalTheory.T.jetFrames_differ_by_unit_each_order E H V t d x x' e e' φ h0 hx hg hg' m
  exact ⟨ε, hinv, hε, hlaw, hact,
    GlobalTheory.T.frame_ratio_first_partial_law E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr h1 h1',
    GlobalTheory.T.frame_ratio_second_partial_law E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr h2 h2',
    GlobalTheory.T.frame_ratio_symmetry_series E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr hs hs',
    GlobalTheory.T.frame_ratio_adjointness_series E H V t d B B' κ κ' tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx hlaw hact hg hg' hr hstar hsurj ha ha'⟩

end GlobalTheory.ChartCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartsWithFramesRelatedAllOrdersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartsWithFrames_related_allOrders : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t (𝟙 (Sp V)) (dirs x') u' v → u = (dLin φ).mulVec u' := by
  first | exact @GlobalTheory.ChartCmp.jRel_of_charts_frames | exact GlobalTheory.ChartCmp.jRel_of_charts_frames | (intros; apply GlobalTheory.ChartCmp.jRel_of_charts_frames <;> assumption)
end
