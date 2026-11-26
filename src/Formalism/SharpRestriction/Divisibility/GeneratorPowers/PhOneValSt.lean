module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GmHomAt
section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartActionPoint
section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.HasSubstActPS
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG

open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]

theorem const_actPS (a : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) : constantCoeff (actPS (Dw := Dw) (S := S) c a q) = 0 := by
  simp [actPS]

theorem hasSubst_actPS (a : 𝓞 E) : HasSubst (actPS (Dw := Dw) (S := S) c a) :=
  hasSubst_of_constantCoeff_zero (fun q => const_actPS c a q)

theorem actPS_comp (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    subst (actPS (Dw := Dw) (S := S) c v) (actPS (Dw := Dw) (S := S) c u q) = actPS (Dw := Dw) (S := S) c (u * v) q := by
  have hv := hasSubst_actPS (Dw := Dw) (S := S) c v
  have e : actPS (Dw := Dw) (S := S) c u q =
      algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 u) • MvPowerSeries.X q := rfl
  rw [e, subst_smul hv, subst_X hv]
  simp only [actPS, smul_smul, map_mul]

theorem φa_mul {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (u v : 𝓞 E) (j : Fin d) :
    subst (actPS (Dw := Dw) c v) (φa c φ u j) = φa c φ (u * v) j := by
  simp only [φa]
  rw [subst_comp_subst_apply (hasSubst_actPS c u) (hasSubst_actPS c v)]
  congr 1
  funext q
  exact actPS_comp c u v q

theorem φa_one {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : φa c φ 1 = φ := by
  have e : actPS (Dw := Dw) (S := S) c 1 = MvPowerSeries.X := by
    funext q
    simp [actPS]
  funext j
  simp only [φa, e, subst_self, id]

theorem actPS_add (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    actPS (Dw := Dw) (S := S) c u q + actPS (Dw := Dw) (S := S) c v q = actPS (Dw := Dw) (S := S) c (u + v) q := by
  simp only [actPS, map_add (f := _), add_smul]

theorem const_φa {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : ∀ j, constantCoeff (φ j) = 0)
    (u : 𝓞 E) (j : Fin d) : constantCoeff (φa c φ u j) = 0 :=
  ExpGF.const_substPS _ (fun q => const_actPS c u q) _ (hφ j)

theorem law_φa {d : ℕ} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {uvec : Lt1 Dw → Fin d → S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : IsExpOf F uvec φ) (u v : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 2 × Fin d => φa c φ (![u, v] p.1) p.2) (F j) = φa c φ (u + v) j := by
  let b : Fin 2 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun p => actPS (Dw := Dw) (S := S) c (![u, v] p.1) ((0 : Fin 1), p.2)
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero (fun p => const_actPS c _ _)
  have hX : ∀ i : Fin 2, HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X (i, q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    fun i => hasSubst_of_constantCoeff_zero (fun q => by simp)
  have hA : HasSubst (fun p : Fin 2 × Fin d => atPt p.1 (φ p.2)) :=
    hasSubst_of_constantCoeff_zero (fun p => ExpGF.const_substPS _ (fun q => by simp) _ (hφ.const p.2))
  have hS : HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    hasSubst_of_constantCoeff_zero (fun q => by simp)
  have key := congrArg (MvPowerSeries.subst b) (hφ.hom j)
  rw [subst_comp_subst_apply hA hb, subst_comp_subst_apply hS hb] at key
  have e1 : (fun p : Fin 2 × Fin d => MvPowerSeries.subst b (atPt p.1 (φ p.2))) =
      fun p => φa c φ (![u, v] p.1) p.2 := by
    funext ⟨i, k⟩
    simp only [atPt, φa]
    rw [subst_comp_subst_apply (hX i) hb]
    congr 1
    funext ⟨q1, q2⟩
    rw [subst_X hb]
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rfl
  have e2 : (fun q : Fin 1 × Fin (dL Dw) => MvPowerSeries.subst b
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) = actPS (Dw := Dw) (S := S) c (u + v) := by
    funext ⟨q1, q2⟩
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rw [subst_add hb, subst_X hb, subst_X hb]
    exact actPS_add c u v _
  rw [e1, e2] at key
  exact key

theorem act_φa {d : ℕ} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : ∀ j, constantCoeff (φ j) = 0)
    (hact : ∀ a j, subst (fun p : Fin 1 × Fin d => φ p.2) (act a j) = subst (actPS (Dw := Dw) c a) (φ j))
    (a u : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 1 × Fin d => φa c φ u p.2) (act a j) = φa c φ (a * u) j := by
  have hP : HasSubst (fun p : Fin 1 × Fin d => φ p.2) :=
    hasSubst_of_constantCoeff_zero (fun p => hφ p.2)
  have h := subst_comp_subst_apply hP (hasSubst_actPS (Dw := Dw) (S := S) c u) (act a j)
  rw [hact a j] at h
  exact h.symm.trans (φa_mul c φ a u j)

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

def ptm (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    jO y (dL Dw) m 1 ⟶ jO y C.d m n :=
  homAt y.x (jetSubstPS (m := m) (fun p : Fin n × Fin C.d => P p.1 p.2))

theorem ptm_congr (C : ChartAt Xo c y) {n : ℕ} {P P' : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S}
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (hP' : ∀ i j, MvPowerSeries.constantCoeff (P' i j) = 0)
    (m : ℕ) (h : ∀ i j, psJet m (P i j) = psJet m (P' i j)) : ptm C P m = ptm C P' m := by
  unfold ptm
  refine congrArg (homAt y.x) (GermD.jet_hom_ext fun q => ?_)
  exact (ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => hP p.1 p.2) q).trans
    ((h q.1 q.2).trans (ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P' p.1 p.2) (fun p => hP' p.1 p.2) q).symm)

theorem coe_actP (u : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    ((actP (Dw := Dw) (S := S) c u q : MvPolynomial _ S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) =
      actPS (Dw := Dw) (S := S) c u q := by
  simp only [actP, actPS, MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X]
  rw [← MvPowerSeries.smul_eq_C_mul, algebraMap_smul]

theorem cc_actP (u : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    MvPolynomial.constantCoeff (actP (Dw := Dw) (S := S) c u q) = 0 := by
  simp [actP]

theorem jetSubstP_actP (m : ℕ) (u : 𝓞 E) :
    jetSubstP m (actP (Dw := Dw) (S := S) c u) = jetSubstPS (m := m) (actPS (Dw := Dw) (S := S) c u) := by
  rw [ExpGF.jetSubstP_eq_jetSubstPS m _ (fun q => cc_actP u q)]
  congr 1
  funext q
  exact coe_actP u q

theorem sA_ptm (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (u : 𝓞 E) :
    homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c u)) ≫ ptm C P m =
      ptm C (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) (P i j)) m := by
  unfold ptm
  rw [GermD.homAt_comp, jetSubstP_actP,
    ExpGF.jetSubstPS_comp m (fun p : Fin n × Fin C.d => P p.1 p.2) (actPS (Dw := Dw) (S := S) c u)
      (fun p => hP p.1 p.2) (const_actPS c u)]

theorem ptm_copy (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (i : Fin n) :
    ptm C P m ≫ homAt y.x (jetCopy C.d m i) = ptm C ![P i] m := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin n × Fin C.d => P p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [(fun p => hP p.1 p.2) q]; exact IsNilpotent.zero)
  unfold ptm
  rw [GermD.homAt_comp, ExpGF.jetCopy_eq_PS,
    ExpGF.jetSubstPS_comp m (fun p : Fin 1 × Fin C.d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin C.d) S))
      (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => MvPowerSeries.constantCoeff_X _) (fun p => hP p.1 p.2)]
  refine congrArg (homAt y.x) (congrArg (jetSubstPS (m := m)) ?_)
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  simp [MvPowerSeries.subst_X hs]

theorem ptm_subst (C : ChartAt Xo c y) {n n' : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ)
    (σ : Fin n' × Fin C.d → MvPolynomial (Fin n × Fin C.d) S) (hσ : ∀ k, MvPolynomial.constantCoeff (σ k) = 0) :
    ptm C P m ≫ homAt y.x (jetSubstP m σ) =
      ptm C (fun i j => MvPowerSeries.subst (fun p : Fin n × Fin C.d => P p.1 p.2)
        ((σ (i, j) : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S)) m := by
  unfold ptm
  rw [GermD.homAt_comp, ExpGF.jetSubstP_eq_jetSubstPS m σ hσ,
    ExpGF.jetSubstPS_comp m (fun k => ((σ k : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S))
      (fun p : Fin n × Fin C.d => P p.1 p.2) (fun k => by
        have h0 : AddMonoidAlgebra.coeff (σ k) 0 = 0 := hσ k
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe, h0]) (fun p => hP p.1 p.2)]

theorem jφ_eq (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    homAt y.x (jφ φ m) = ptm C ![φ] m := by
  have e : (fun p : Fin 1 × Fin C.d => φ p.2) = (fun p : Fin 1 × Fin C.d => (![φ] : Fin 1 → _) p.1 p.2) := by
    funext p
    obtain ⟨a, j⟩ := p
    fin_cases a
    rfl
  unfold ptm jφ
  rw [e]

theorem exp_chart_action_point (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (hx : IsExpChart y (xExp y C φ)) (m : ℕ) (u : 𝓞 E) :
    xExp y C φ m ≫ Xo.univ.t.act.act u = ptm C ![φa c φ u] m ≫ C.x m := by
  have hP : ∀ i j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j
    fin_cases i
    exact hφ j
  have e : (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) ((![φ] : Fin 1 → _) i j)) =
      ![φa c φ u] := by
    funext i j
    fin_cases i
    rfl
  rw [hx.act m u, xExp, ← Category.assoc, jφ_eq, sA_ptm C _ hP m u, e]

theorem ptm_jpt (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (hx : IsExpChart y (xExp y C φ)) (m : ℕ) {n : ℕ}
    (us : Fin n → 𝓞 E) (i : Fin n) :
    ptm C (fun k => φa c φ (us k)) m ≫ jpt y C.d C.x m i = xExp y C φ m ≫ Xo.univ.t.act.act (us i) := by
  have hP : ∀ k j, MvPowerSeries.constantCoeff (φa c φ (us k) j) = 0 := fun k j => const_φa c φ hφ (us k) j
  rw [jpt, ← Category.assoc, ptm_copy C _ hP m i, exp_chart_action_point C φ hφ hx m (us i)]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

abbrev σL (C : ChartAt Xo c y) (m : ℕ) : Fin 2 × Fin C.d → MvPolynomial (Fin 1 × Fin C.d) S :=
  fun p => (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn C.d m ![0] (C.B.A.act H.w0 j)] :
    Fin 2 → Fin C.d → MvPolynomial (Fin 1 × Fin C.d) S) p.1 p.2

theorem cc_σL (C : ChartAt Xo c y) (m : ℕ) (p : Fin 2 × Fin C.d) : MvPolynomial.constantCoeff (σL C m p) = 0 := by
  rcases p with ⟨i, j⟩
  fin_cases i <;> simp [σL, psIn, MvPolynomial.constantCoeff_rename, Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.cc_psTrunc', C.B.A.const]

theorem ptm_one_φa (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (m : ℕ) (k : 𝓞 E) :
    homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c k)) ≫ homAt y.x (jφ φ m) = ptm C ![φa c φ k] m := by
  rw [jφ_eq, sA_ptm C ![φ] (fun i j => by rw [Fin.fin_one_eq_zero i]; exact hφ j) m k]
  refine congrArg (fun P => ptm C P m) (funext fun i => funext fun j => ?_)
  rw [Fin.fin_one_eq_zero i]
  rfl

theorem ptm_σL (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) (m : ℕ) (k : 𝓞 E) :
    ptm C ![φa c φ k] m ≫ homAt y.x (jetSubstP m (σL C m)) = ptm C ![φa c φ k, φa c φ (H.w0 * k)] m := by
  have hP0 : ∀ j, MvPowerSeries.constantCoeff (φa c φ k j) = 0 := const_φa c φ hφ k
  have hP : ∀ i j, MvPowerSeries.constantCoeff ((![φa c φ k] : Fin 1 → _) i j) = 0 := by
    intro i j
    rw [Fin.fin_one_eq_zero i]
    exact hP0 j
  rw [ptm_subst C _ hP m _ (cc_σL C m)]
  set Q : Fin 1 × Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun p => (![φa c φ k] : Fin 1 → _) p.1 p.2 with hQdef
  have hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0 := fun p => hP p.1 p.2
  have hQe : Q = fun p => φa c φ k p.2 := by
    funext p
    obtain ⟨p1, p2⟩ := p
    rw [hQdef, Fin.fin_one_eq_zero p1]
    rfl
  refine ptm_congr C (fun i j => const_substPS Q hQ _ ?_) ?_ m ?_
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    exact cc_σL C m (i, j)
  · rw [Fin.forall_fin_two]
    exact ⟨fun j => hP0 j, fun j => const_φa c φ hφ _ j⟩
  · rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · simp only [σL, Matrix.cons_val_zero]
      rw [MvPolynomial.coe_X, MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ), hQe]
    · simp only [σL, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [power_series_in_fin_one, psJet_subst_trunc m Q hQ, hQe, act_φa c hφ hact]

theorem gm_top {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (v : Γ(Y, ⊤)ˣ) :
    gm r z ⊤ v = gm (𝟙 Z) z ⊤ (Units.map r.appTop.hom.toMonoidHom v) := by
  first
  | rfl
  | (simp only [gm, pullU]; rfl)
  | (ext; simp [gm, pullU]; rfl)

theorem gm_homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (z : (overAt y.x B).left) (w : Aˣ) :
    gm (homAt y.x f).left z ⊤ (unitΓ w) = gm (𝟙 _) z ⊤ (unitΓ (Units.map f.toMonoidHom w)) := by
  rw [gm_top, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB.unitΓ_homAt]

theorem val_eG (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jO y (dL Dw) m 1).left) (z : Z)
    (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (ExpGA.eG C φ τ u m) r z J = gm r z ⊤ (unitΓ (u m)) * val (τ m) (r ≫ (homAt y.x (jφ φ m)).left) z J := by
  show val (scaleGen (fun _ : Fin 1 => (homAt y.x (jφ φ m)).left ≫ (C.x m).left) (fun _ => (1 : ℤ)) (unitΓ (u m))
    (LB.pullGen Xo.univ.t.PP.L _ _ (τ m) (homAt y.x (jφ φ m)).left)) r z J = _
  rw [ExpGD.val_scale' _ _ _ _ _ z J hJ, val_pull hJ]

theorem val_eAt (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j))
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (m : ℕ) (k : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
    (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (eAt y (xExp y C φ) (ExpGA.eG C φ τ u) m k) (𝟙 _) z J =
      gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstP m (actP (Dw := Dw) (S := S) c k)).toMonoidHom (u m))) *
        (val C.wP ((ptm C ![φa c φ k] m).left ≫ (C.x m).left) z J *
          val (C.e m) (ptm C ![φa c φ k, φa c φ (H.w0 * k)] m).left z J) := by
  have hm1 : (𝟙 _ ≫ (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c k))).left) ≫ (homAt y.x (jφ φ m)).left =
      (ptm C ![φa c φ k] m).left := by
    rw [Category.id_comp, ← Over.comp_left, ptm_one_φa C φ hφ m k]
  have hm2 : (ptm C ![φa c φ k] m).left ≫ (homAt y.x (jetSubstP m (σL C m))).left =
      (ptm C ![φa c φ k, φa c φ (H.w0 * k)] m).left := by
    rw [← Over.comp_left, ptm_σL C φ hφ hact m k]
  unfold eAt
  rw [val_pull hJ, val_eG C φ τ u m _ z J hJ, val_corr hJ (hτc m), hm1, Category.id_comp, gm_homAt]
  unfold eL
  rw [val_mul hJ, val_pull hJ,
    show val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn C.d m ![0] (C.B.A.act H.w0 j)])
        (ptm C ![φa c φ k] m).left z J =
      val (C.e m) ((ptm C ![φa c φ k] m).left ≫ (homAt y.x (jetSubstP m (σL C m))).left) z J from val_pull hJ _ _ _,
    hm2]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

attribute [local instance] Over.cartesianMonoidalCategory

def PhOneValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
    ∀ (m : ℕ) (u0 u1 u2 : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
      (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J →
      ∃ w : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
        (w : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (atP ![φa c φ u0, φa c φ u1, φa c φ u2] C.B.ph1) ∧
        val (ExpGC.cubAt (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2)) (xExp y C φ m).left z J =
          gm (𝟙 _) z ⊤ (unitΓ w) * (val (C.e m) (ptm C ![φa c φ (u0 + u1), φa c φ u2] m).left z J *
            (val (C.e m) (ptm C ![φa c φ u0, φa c φ u2] m).left z J)⁻¹ *
            (val (C.e m) (ptm C ![φa c φ u1, φa c φ u2] m).left z J)⁻¹)

def PhTwoValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
    ∀ (m : ℕ) (u0 u1 u2 : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
      (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J →
      ∃ w : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
        (w : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (atP ![φa c φ u0, φa c φ u1, φa c φ u2] C.B.ph2) ∧
        val (ExpGC.cubAt (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2) (Xo.univ.t.act.act u0)) (xExp y C φ m).left z J =
          gm (𝟙 _) z ⊤ (unitΓ w) * (val (C.e m) (ptm C ![φa c φ u0, φa c φ (u1 + u2)] m).left z J *
            (val (C.e m) (ptm C ![φa c φ u0, φa c φ u1] m).left z J)⁻¹ *
            (val (C.e m) (ptm C ![φa c φ u0, φa c φ u2] m).left z J)⁻¹)

def AdValSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
    (∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) →
    ∀ (a' : 𝓞 E) (wL : ExpGC.AdTy Xo a'), ExpGD.AdRel C a' wL →
    ∀ (m : ℕ) (u0 u1 : 𝓞 E) (z : (jO y (dL Dw) m 1).left)
      (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J →
      ∃ w : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
        (w : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (atP ![φa c φ u0, φa c φ u1] (C.B.ad a')) ∧
        val (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1)).left)
            (xExp y C φ m).left z J =
          gm (𝟙 _) z ⊤ (unitΓ w) * (val (C.e m) (ptm C ![φa c φ u0, φa c φ (H.bar a' * u1)] m).left z J *
            (val (C.e m) (ptm C ![φa c φ (a' * u0), φa c φ u1] m).left z J)⁻¹)

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
