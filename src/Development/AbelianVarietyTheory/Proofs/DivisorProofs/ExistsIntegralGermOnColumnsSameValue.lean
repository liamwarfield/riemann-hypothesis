module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstTwoPointsPowerSeriesZeroOfVanishFirstAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffDpolyNEqDerivAt0
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpCoord

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj GlobalTheory.LawLog
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (pderiv_subst)

section Deriv

variable {C : Type} [Field C] {σ : Type}

theorem mfact_eq_prod [Fintype σ] (α : σ →₀ ℕ) : (mfact α : C) = ∏ s, ((α s).factorial : C) := by
  first
  | exact Finsupp.prod_fintype α _ (fun _ => by simp)
  | (unfold mfact; rw [Finsupp.prod_fintype]; intro; simp)

theorem mfact_add_single [Fintype σ] (α : σ →₀ ℕ) (l : σ) :
    (mfact (α + Finsupp.single l 1) : C) = mfact α * ((α l : C) + 1) := by
  classical
  first
  | (have h : ∀ s, (((α + Finsupp.single l 1 : σ →₀ ℕ) s).factorial : C) =
        ((α s).factorial : C) * (if s = l then ((α l : C) + 1) else 1) := by
      intro s
      by_cases hs : s = l
      · rw [if_pos hs]
        subst hs
        rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
        push_cast
        ring
      · rw [if_neg hs, mul_one]
        simp [Finsupp.single_apply, Ne.symm hs]
     rw [mfact_eq_prod, mfact_eq_prod, Finset.prod_congr rfl (fun s _ => h s), Finset.prod_mul_distrib]
     simp
     done)

theorem derivAt0_monomial (α : σ →₀ ℕ) (a : C) (S : MvPowerSeries σ C) :
    derivAt0 (MvPolynomial.monomial α a) S = a * mfact α * coeff α S := by
  classical
  first
  | (rw [derivAt0_eq_sum_of_subset _ _ MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]; done)
  | (by_cases ha : a = 0 <;> simp [derivAt0, ha, MvPolynomial.support_monomial]; done)

private lemma hasSubst_lemma {ι τ : Type} [Finite ι] {a : ι → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha]; exact IsNilpotent.zero)

private lemma cc_subst_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    constantCoeff (subst a f) = 0 := by
  first
  | exact constantCoeff_subst_eq_zero (hasSubst_lemma ha) ha hf
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_lemma ha) ha hf
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_lemma ha) hf

private lemma subst_zero_lemma_3 {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ C) = 0 := by
  first
  | (rw [← MvPowerSeries.coe_substAlgHom ha]; exact map_zero _)
  | simp

private lemma subst_C_eq_C' {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (r : C) :
    subst a (MvPowerSeries.C r : MvPowerSeries σ C) = MvPowerSeries.C r := by
  first
  | (rw [← MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes,
      MvPowerSeries.c_eq_algebraMap])
  | (rw [← MvPowerSeries.coe_substAlgHom ha]; exact AlgHom.commutes _ r)
  | simp [ha]

private lemma subst_subst_eq_subst_comp {σ τ ρ : Type} {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries ρ C}
    (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ C) :
    subst b (subst a f) = subst (fun s => subst b (a s)) f := by
  first
  | exact MvPowerSeries.subst_comp_subst_apply ha hb f
  | exact (MvPowerSeries.subst_comp_subst_apply ha hb f).symm
  | exact congrFun (MvPowerSeries.subst_comp_subst ha hb) f

private lemma pderiv_inr_subst_twoVars {d : ℕ} (f : MvPowerSeries (Fin 2 × Fin d) C) (k : Fin d) :
    pderiv (Sum.inr k) (subst (GlobalTheory.LawLog.twoVars C d) f) =
      subst (GlobalTheory.LawLog.twoVars C d) (pderiv ((1 : Fin 2), k) f) := by
  classical
  rw [pderiv_subst GlobalTheory.LawLog.cc_twoVars, Finset.sum_eq_single ((1 : Fin 2), k)]
  · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.pderiv_X, Pi.single_apply]
  · rintro ⟨a, i⟩ _ hs
    fin_cases a
    · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.pderiv_X, Pi.single_apply]
    · have hik : i ≠ k := fun h => hs (by subst h; rfl)
      simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.pderiv_X, Pi.single_apply, hik]
  · simp

variable [CharZero C] (v : AddValuation C (WithTop ℝ))
include v

theorem derivAt0_pderiv [Fintype σ] (Q : MvPolynomial σ C) (l : σ) (S : MvPowerSeries σ C) :
    derivAt0 Q (pderiv l S) = derivAt0 (Q * MvPolynomial.X l) S := by
  classical
  first
  | (unfold derivAt0
     rw [MvPolynomial.support_mul_X, Finset.sum_map]
     refine Finset.sum_congr rfl fun α _ => ?_
     simp only [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, mfact_add_single]
     first
     | (rw [MvPowerSeries.coeff_pderiv]; ring)
     | (simp [MvPowerSeries.coeff_pderiv]; ring)
     | (simp [MvPowerSeries.coeff_pderiv])
     done)

end Deriv

section Chain

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem subst_jacEntry (G : FGLaw C d) (L : LogFGL v d)
    (hL : ∀ a, L.F a = subst (twoVars C d) (G.F a)) {n : ℕ} {Λ : Type} [Finite Λ]
    (ψ : Fin n × Fin d → MvPowerSeries Λ C) (hψ : ∀ q, constantCoeff (ψ q) = 0) (j : Fin n) (k e : Fin d) :
    subst (fun i => ψ (j, i)) (GlobalTheory.LogJacobian.jacEntry L k e) =
      subst ψ (ev (n := n) ![pt C d j, 0] (pderiv ((1 : Fin 2), k) (G.F e))) := by
  classical
  have hA : HasSubst (GlobalTheory.LogJacobian.substSecondBlockZero (C := C) d) := hasSubst_lemma (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d)
  have hT : HasSubst (GlobalTheory.LawLog.twoVars C d) := hasSubst_lemma GlobalTheory.LawLog.cc_twoVars
  have hB : HasSubst (fun i => ψ (j, i)) := hasSubst_lemma (fun i => hψ (j, i))
  have hΨ : HasSubst ψ := hasSubst_lemma hψ
  have hAT : HasSubst (fun s => subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := C) d) (GlobalTheory.LawLog.twoVars C d s)) :=
    hasSubst_lemma (fun s => cc_subst_lemma_2 (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d) (GlobalTheory.LawLog.cc_twoVars s))
  have hP : HasSubst (fun p : Fin 2 × Fin d => (![fun i => X (j, i), 0] : Fin 2 → Fin d → MvPowerSeries (Fin n × Fin d) C) p.1 p.2) := by
    refine hasSubst_lemma (fun p => ?_)
    rcases p with ⟨a, i⟩
    fin_cases a <;> simp
  unfold GlobalTheory.LogJacobian.jacEntry ev pt
  rw [hL e, pderiv_inr_subst_twoVars, subst_subst_eq_subst_comp hT hA, subst_subst_eq_subst_comp hAT hB, subst_subst_eq_subst_comp hP hΨ]
  congr 1
  funext p
  rcases p with ⟨a, i⟩
  fin_cases a
  · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.subst_X hA, MvPowerSeries.subst_X hΨ]
    all_goals simp [GlobalTheory.LogJacobian.substSecondBlockZero, MvPowerSeries.subst_X hB]
  · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.subst_X hA, MvPowerSeries.subst_X hΨ, subst_zero_lemma_3 hΨ]
    all_goals simp [GlobalTheory.LogJacobian.substSecondBlockZero, subst_zero_lemma_3 hB]

variable (L : LogFGL v d) {n : ℕ} {Λ : Type} [Fintype Λ] (β : Λ → Fin n → C) (w : Λ → Fin d → C)

def lin (j : Fin n) : Fin d → MvPowerSeries Λ C :=
  fun e => ∑ l, (β l j * w l e) • (X l : MvPowerSeries Λ C)

def psi : Fin n × Fin d → MvPowerSeries Λ C :=
  fun q => subst (lin β w q.1) (expOf L q.2)

theorem cc_lin (j : Fin n) (e : Fin d) : constantCoeff (lin β w j e) = 0 := by
  first
  | (simp [lin, MvPowerSeries.smul_eq_C_mul]; done)
  | (unfold lin
     set_option synthInstance.maxHeartbeats 100000 in
       rw [map_sum]
     refine Finset.sum_eq_zero fun l _ => ?_
     rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero])

theorem cc_psi (q : Fin n × Fin d) : constantCoeff (psi L β w q) = 0 := by
  have hs : MvPowerSeries.HasSubst (lin β w q.1) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (cc_lin β w q.1)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_lin β w q.1)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [cc_lin]; exact IsNilpotent.zero)
  first
  | exact constantCoeff_subst_eq_zero hs (cc_lin β w q.1) ((isExp_expOf L).1 q.2)
  | exact MvPowerSeries.constantCoeff_subst_eq_zero hs (cc_lin β w q.1) ((isExp_expOf L).1 q.2)
  | exact MvPowerSeries.constantCoeff_subst_eq_zero hs ((isExp_expOf L).1 q.2)

theorem pderiv_lin (l : Λ) (j : Fin n) (e : Fin d) :
    pderiv l (lin β w j e) = MvPowerSeries.C (β l j * w l e) := by
  classical
  first
  | (simp only [lin, map_sum, Derivation.map_smul, MvPowerSeries.pderiv_X]
     simp [Pi.single_apply, MvPowerSeries.smul_eq_C_mul]
     done)
  | (simp [lin, MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]; done)

theorem pderiv_subst_psi (G : FGLaw C d) (hL : ∀ a, L.F a = subst (twoVars C d) (G.F a)) (l : Λ) (g : PS C n d) :
    pderiv l (subst (psi L β w) g) =
      subst (psi L β w) (∑ j, MvPowerSeries.C (β l j) * DofN G.F j (w l) g) := by
  classical
  have hΨ : HasSubst (psi L β w) := hasSubst_lemma (cc_psi L β w)
  have hcol : ∀ (j : Fin n) (c : Fin d), pderiv l (psi L β w (j, c)) =
      ∑ e, subst (psi L β w) (ev ![pt C d j, 0] (pderiv ((1 : Fin 2), e) (G.F c))) *
        MvPowerSeries.C (β l j * w l e) := by
    intro j c
    have hlin : HasSubst (lin β w j) := hasSubst_lemma (cc_lin β w j)
    have hE : HasSubst (expOf L) := hasSubst_lemma (isExp_expOf L).1
    show pderiv l (subst (lin β w j) (expOf L c)) = _
    rw [pderiv_subst (cc_lin β w j)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [pderiv_lin, GlobalTheory.LogJacobian.pderiv_expOf, subst_subst_eq_subst_comp hE hlin]
    congr 1
    exact subst_jacEntry G L hL (psi L β w) (cc_psi L β w) j e c
  rw [pderiv_subst (cc_psi L β w), Fintype.sum_prod_type]
  simp only [hcol]
  simp only [DofN]
  rw [← MvPowerSeries.coe_substAlgHom hΨ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, MvPowerSeries.coe_substAlgHom, subst_C_eq_C' hΨ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

end Chain


open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies GlobalTheory.MatChain in
theorem constantCoeff_dpolyN_eq_derivAt0 : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : FGLaw C d) (L : LogFGL v d), (∀ a, L.F a = MvPowerSeries.subst (twoVars C d) (G.F a)) → ∀ (n : ℕ) (ι Λ : Type) [Fintype ι] [Fintype Λ] (cp : ι → Fin n) (u : ι → Fin d → C) (β : Λ → Fin n → C) (t : Λ → Fin n → ι) (w : Λ → Fin d → C), (∀ l j, cp (t l j) = j) → (∀ l j, u (t l j) = w l) → ∀ (P : MvPolynomial Λ C) (g : PS C n d), MvPowerSeries.constantCoeff (DpolyN G.F cp u (MvPolynomial.aeval (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C)) P) g) = derivAt0 P (MvPowerSeries.subst (fun q : Fin n × Fin d => (MvPowerSeries.subst (fun e : Fin d => ∑ l, (β l q.1 * w l e) • (MvPowerSeries.X l : MvPowerSeries Λ C)) (expOf L q.2) : MvPowerSeries Λ C)) g) := by
  intro C _ _ v d G L hL n ι Λ _ _ cp u β t w hcp hu P g
  classical
  show constantCoeff (DpolyN G.F cp u (MvPolynomial.aeval
      (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C)) P) g) =
    derivAt0 P (subst (psi L β w) g)
  have hΨ : HasSubst (psi L β w) := hasSubst_lemma (cc_psi L β w)
  have hmon0 : ∀ f : PS C n d, DmonN G.F cp u 0 f = f := by
    intro f
    simp [DmonN]
  have hsub : ∀ (Q : MvPolynomial ι C) (s : Finset (ι →₀ ℕ)) (f : PS C n d), Q.support ⊆ s →
      DpolyN G.F cp u Q f = ∑ m ∈ s, MvPowerSeries.C (AddMonoidAlgebra.coeff Q m) * DmonN G.F cp u m f := by
    intro Q s f hs
    unfold DpolyN
    refine Finset.sum_subset hs fun m _ hm => ?_
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]
  have hadd : ∀ (Q1 Q2 : MvPolynomial ι C) (f : PS C n d),
      DpolyN G.F cp u (Q1 + Q2) f = DpolyN G.F cp u Q1 f + DpolyN G.F cp u Q2 f := by
    intro Q1 Q2 f
    rw [hsub (Q1 + Q2) (Q1.support ∪ Q2.support) f MvPolynomial.support_add,
      hsub Q1 (Q1.support ∪ Q2.support) f Finset.subset_union_left,
      hsub Q2 (Q1.support ∪ Q2.support) f Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]
  have hC : ∀ (a : C) (f : PS C n d), DpolyN G.F cp u (MvPolynomial.C a) f = MvPowerSeries.C a * f := by
    intro a f
    rw [hsub (MvPolynomial.C a) {0} f (by rw [MvPolynomial.C_apply]; exact MvPolynomial.support_monomial_subset),
      Finset.sum_singleton, MvPolynomial.coeff_C, if_pos rfl, hmon0]
  have hfin : ∀ (Q : Fin n → MvPolynomial ι C) (f : PS C n d),
      DpolyN G.F cp u (∑ j, Q j) f = ∑ j, DpolyN G.F cp u (Q j) f := fun Q f =>
    map_sum (AddMonoidHom.mk' (fun Q => DpolyN G.F cp u Q f) (fun Q1 Q2 => hadd Q1 Q2 f)) Q Finset.univ
  have hcomm1 : ∀ (j : Fin n) (x : Fin d → C) (Q : MvPolynomial ι C) (f : PS C n d),
      DofN G.F j x (DpolyN G.F cp u Q f) = DpolyN G.F cp u Q (DofN G.F j x f) := by
    intro j x Q
    induction Q using MvPolynomial.induction_on
    next a =>
      intro f
      rw [hC, hC, GlobalTheory.MatChain.dofN_C_mul]
    next Q1 Q2 h1 h2 =>
      intro f
      rw [hadd, hadd, GlobalTheory.MatChain.dofN_add, h1, h2]
    next Q m h =>
      intro f
      rw [GlobalTheory.MatChain.dpoly_mul_X, GlobalTheory.MatChain.dpoly_mul_X, Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.dofN_comm, h]
  have hccs : ∀ f : PS C n d, constantCoeff (subst (psi L β w) f) = constantCoeff f := by
    intro f
    have h0 : constantCoeff (f - MvPowerSeries.C (constantCoeff f)) = 0 := by simp
    have h1 := cc_subst_lemma_2 (cc_psi L β w) h0
    rw [← MvPowerSeries.coe_substAlgHom hΨ, map_sub, MvPowerSeries.coe_substAlgHom, subst_C_eq_C' hΨ,
      map_sub] at h1
    simpa [sub_eq_zero] using h1
  have hlinD : ∀ (Q : MvPolynomial Λ C) (b : Fin n → C) (s : Fin n → MvPowerSeries Λ C),
      derivAt0 Q (∑ j, MvPowerSeries.C (b j) * s j) = ∑ j, b j * derivAt0 Q (s j) := by
    intro Q b s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [derivAt0, map_sum, MvPowerSeries.coeff_C_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => by ring
  revert g
  induction P using MvPolynomial.induction_on
  next a =>
    intro g
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, hC, MvPolynomial.C_apply, derivAt0_monomial]
    simp [mfact, hccs, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  next P1 P2 h1 h2 =>
    intro g
    rw [map_add (f := _), hadd, map_add (f := _), h1, h2,
      (derivAt0_linear C v Λ P1 P2 (subst (psi L β w) g) (subst (psi L β w) g) 0).2.2.1]
  next Q l h =>
    intro g
    have hφ : MvPolynomial.aeval (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C))
          (Q * MvPolynomial.X l) =
        ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.aeval
          (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C)) Q *
            MvPolynomial.X (t l j)) := by
      rw [map_mul, MvPolynomial.aeval_X, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hφ, hfin]
    simp only [GlobalTheory.MatChain.dpoly_C_mul, GlobalTheory.MatChain.dpoly_mul_X, hcp, hu, hcomm1]
    rw [← derivAt0_pderiv v Q l, pderiv_subst_psi L β w G hL l g, ← MvPowerSeries.coe_substAlgHom hΨ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPowerSeries.coe_substAlgHom, subst_C_eq_C' hΨ, MvPowerSeries.constantCoeff_C, h]
    rw [hlinD]

end GlobalTheory.ExpCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitMatrixGauge
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv

namespace GlobalTheory.MatrixGauge

section Small

variable (R : Type) [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {m : ℕ}

def Small (f : PS k m d) : Prop :=
  constantCoeff f = 0 ∧ ∃ w : PS R m d, constantCoeff w = 1 ∧ FB.toK k w = FB.expS k f

def IsBase (P : Pt k m d) : Prop := ∃ Q : Pt R m d, GP Q ∧ P = mapP (algebraMap R k) Q

variable {R}

theorem small_zero : Small R (0 : PS k m d) :=
  ⟨map_zero _, 1, map_one _, by
    rw [FB.toK, map_one, FB.expS, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]⟩

theorem Small.congr {f g : PS k m d} (hf : Small R f) (e : f = g) : Small R g := e ▸ hf

theorem Small.add {f g : PS k m d} (hf : Small R f) (hg : Small R g) : Small R (f + g) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  obtain ⟨g0, w, w1, hw⟩ := hg
  refine ⟨by simp [f0, g0], v * w, by simp [v1, w1], ?_⟩
  rw [FB.toK, map_mul, gt_expS_add _ _ f0 g0]
  exact congrArg₂ (· * ·) hv hw

theorem Small.neg {f : PS k m d} (hf : Small R f) : Small R (-f) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  have n0 : constantCoeff (-f) = 0 := by simp [f0]
  refine ⟨n0, invOfUnit v 1, by simp, ?_⟩
  have h1 : FB.toK k v * FB.toK k (invOfUnit v 1) = 1 := by
    rw [FB.toK, FB.toK, ← map_mul, mul_invOfUnit v 1 (by simpa using v1), map_one]
  have h2 : FB.expS k (-f) * FB.expS k f = 1 := by
    rw [← gt_expS_add _ _ n0 f0, neg_add_cancel, FB.expS, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  rw [hv] at h1
  calc FB.toK k (invOfUnit v 1) = (FB.expS k (-f) * FB.expS k f) * FB.toK k (invOfUnit v 1) := by
        rw [h2, _root_.one_mul]
    _ = FB.expS k (-f) := by rw [_root_.mul_assoc, h1, _root_.mul_one]

theorem Small.sum {ι : Type} (s : Finset ι) {f : ι → PS k m d} (hf : ∀ i, Small R (f i)) :
    Small R (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Small R) (fun _ _ => Small.add) small_zero fun i _ => hf i

theorem Small.sum_sub {ι : Type} (s : Finset ι) {f g : ι → PS k m d} (hf : ∀ i, Small R (f i - g i)) :
    Small R (∑ i ∈ s, f i - ∑ i ∈ s, g i) :=
  (Small.sum s hf).congr (Finset.sum_sub_distrib _ _)

theorem Small.trans {f g e : PS k m d} (h1 : Small R (f - g)) (h2 : Small R (g - e)) : Small R (f - e) :=
  (h1.add h2).congr (by ring)

omit [Algebra ℚ k] in
theorem IsBase.gp {P : Pt k m d} (hP : IsBase R P) : GP P := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact constantCoeff_mapP_eq_zero _ _ hQ

omit [Algebra ℚ k] in
theorem isBase_pt (j : Fin m) : IsBase R (pt k d j) := ⟨pt R d j, gp_pt j, (baseChange_pt _ j).symm⟩

omit [Algebra ℚ k] in
theorem isBase_zero : IsBase R (0 : Pt k m d) := ⟨0, gp_zero₂, funext fun _ => (map_zero _).symm⟩

theorem Small.subst {l : ℕ} {V : Fin l → Pt k m d} (hV : ∀ j, IsBase R (V j)) {f : PS k l d}
    (hf : Small R f) : Small R (ev V f) := by
  obtain ⟨f0, w, w1, hw⟩ := hf
  have hV' : ∀ j, GP (V j) := fun j => (hV j).gp
  choose a ha e using hV
  refine ⟨gt_const_ev V hV' f f0, ev a w, by rw [gt_const_ev_eq a ha, w1], ?_⟩
  rw [← gt_ev_expS V hV' f f0, ← hw, FB.toK, QuadDeriv.map_ev _ _ ha]
  congr 1
  funext j
  exact (e j).symm

omit [Algebra ℚ k] in
theorem isBase2 {P Q : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q) : ∀ j, IsBase R (![P, Q] j) := by
  intro j; fin_cases j
  · exact hP
  · exact hQ

omit [Algebra ℚ k] in
theorem isBase3 {P Q T : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q) (hT : IsBase R T) :
    ∀ j, IsBase R (![P, Q, T] j) := by
  intro j; fin_cases j
  · exact hP
  · exact hQ
  · exact hT

end Small

section Points

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra R k] (B : FB R d O) {m : ℕ}

theorem gp_act (a : O) : GP (B.actK k a) := constantCoeff_mapP_eq_zero _ _ (B.A.const a)

theorem gp_law : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const

theorem IsBase.act (a : O) {P : Pt k m d} (hP : IsBase R P) : IsBase R (comp1 (B.actK k a) P) := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact ⟨comp1 (B.A.act a) Q, gp_comp1 _ _ (B.A.const a) hQ, (baseChange_comp1 _ _ _ hQ).symm⟩

theorem IsBase.add {P P' : Pt k m d} (hP : IsBase R P) (hP' : IsBase R P') :
    IsBase R (addOf (B.FK k) P P') := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  obtain ⟨Q', hQ', rfl⟩ := hP'
  exact ⟨addOf B.G.F Q Q', gp_addOf _ B.G.const _ _ hQ hQ', (baseChange_addOf _ _ _ _ hQ hQ').symm⟩

theorem isBase_foldr {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b)) (L : List ι) :
    IsBase R (L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0) := by
  induction L with
  | nil => exact isBase_zero
  | cons b L ih => exact (hg b).add B ih

theorem act_act (a c : O) {P : Pt k m d} (hP : GP P) :
    comp1 (B.actK k a) (comp1 (B.actK k c) P) = comp1 (B.actK k (a * c)) P := by
  rw [FramePull.actK_mul, gt_comp1_comp1 _ _ (gp_act B c) _ hP]

theorem add_act (a c : O) {P : Pt k m d} (hP : GP P) :
    comp1 (B.actK k (a + c)) P = addOf (B.FK k) (comp1 (B.actK k a) P) (comp1 (B.actK k c) P) := by
  rw [FramePull.actK_add]
  exact evP_addOf ![P] (single_point_zero_constant hP) _ _ _ (gp_act B a) (gp_act B c)

theorem act_add (a : O) {P Q : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q) :
    comp1 (B.actK k a) (addOf (B.FK k) P Q) =
      addOf (B.FK k) (comp1 (B.actK k a) P) (comp1 (B.actK k a) Q) := by
  obtain ⟨P, hP, rfl⟩ := hP
  obtain ⟨Q, hQ, rfl⟩ := hQ
  have hV := pair_points_zero_constant hP hQ
  have p0 : GP (pt R (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt R (n := 2) d 1) := gp_pt 1
  have hc : ∀ {n : ℕ} {X : Pt R n d}, GP X → GP (comp1 (B.A.act a) X) :=
    fun hX => gp_comp1 _ _ (B.A.const a) hX
  have h1 := congrArg (evP ![P, Q]) (B.A.hom a)
  rw [evP_comp1 _ hV _ _ (gp_addOf _ B.G.const _ _ p0 p1), evP_addOf _ hV _ _ _ p0 p1,
    evP_addOf _ hV _ _ _ (hc p0) (hc p1), evP_comp1 _ hV _ _ p0, evP_comp1 _ hV _ _ p1,
    evP_pt _ hV, evP_pt _ hV] at h1
  have h2 : comp1 (B.A.act a) (addOf B.G.F P Q) =
      addOf B.G.F (comp1 (B.A.act a) P) (comp1 (B.A.act a) Q) := h1
  have h3 := congrArg (mapP (algebraMap R k)) h2
  rw [baseChange_comp1 _ _ _ (gp_addOf _ B.G.const _ _ hP hQ), baseChange_addOf _ _ _ _ hP hQ,
    baseChange_addOf _ _ _ _ (hc hP) (hc hQ), baseChange_comp1 _ _ _ hP, baseChange_comp1 _ _ _ hQ] at h3
  exact h3

theorem act_foldr (a : O) {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b)) (L : List ι) :
    comp1 (B.actK k a) (L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0) =
      L.foldr (fun b acc => addOf (B.FK k) (comp1 (B.actK k a) (g b)) acc) 0 := by
  induction L with
  | nil => exact gt_comp1_zero _ (gp_act B a)
  | cons b L ih => rw [List.foldr_cons, List.foldr_cons, act_add B a (hg b) (isBase_foldr B hg L), ih]

end Points

section Gauge

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d} {m : ℕ}

theorem const_gauge (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have := congrArg constantCoeff hh.ax0
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this

theorem gauge_zero_left (hh : B.IsCanonGauge k h) {Q : Pt k m d} (hQ : GP Q) : ev ![0, Q] h = 0 := by
  have := congrArg (ev ![Q]) hh.ax0
  rwa [formalSubst_single_of_formalSubst_two _ hQ _ _ gp_zero₂ (gp_pt 0), formalComp_zero_left_point _ hQ, gt_comp1_pt _ hQ,
    gt_ev_zero _ (single_point_zero_constant hQ)] at this

theorem gauge_zero_right (hh : B.IsCanonGauge k h) {Q : Pt k m d} (hQ : GP Q) : ev ![Q, 0] h = 0 := by
  have := congrArg (ev ![Q]) hh.ax1
  rwa [formalSubst_single_of_formalSubst_two _ hQ _ _ (gp_pt 0) gp_zero₂, formalComp_zero_left_point _ hQ, gt_comp1_pt _ hQ,
    gt_ev_zero _ (single_point_zero_constant hQ)] at this

theorem small_balanced (hh : B.IsCanonGauge k h) (a : O) {P Q : Pt k m d} (hP : IsBase R P)
    (hQ : IsBase R Q) :
    Small R (ev ![comp1 (B.actK k a) P, Q] h - ev ![P, comp1 (B.actK k (star a)) Q] h) := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have c0 := pair_points_zero_constant (gp_comp1 _ _ (gp_act B a) p0) p1
  have c1 := pair_points_zero_constant p0 (gp_comp1 _ _ (gp_act B (star a)) p1)
  have w1 : constantCoeff (B.ad a) = 1 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant (gp_zero₂ (n := 1)) (gp_pt 0)), B.adjoint_zero_fst, map_one]
  have key := Small.subst (isBase2 hP hQ) ⟨by
    rw [map_sub, gt_const_ev_eq _ c0, gt_const_ev_eq _ c1, sub_self], _, w1, hh.ad a⟩
  have hV := pair_points_zero_constant hP.gp hQ.gp
  rw [gt_ev_sub _ hV, gt_ev_ev' _ _ hV c0, gt_ev_ev' _ _ hV c1, eval_pair_points, eval_pair_points,
    evP_comp1 _ hV _ _ p0, evP_comp1 _ hV _ _ p1, evP_pt _ hV, evP_pt _ hV] at key
  exact key

theorem small_add_left (hh : B.IsCanonGauge k h) {P P' Q : Pt k m d} (hP : IsBase R P) (hP' : IsBase R P')
    (hQ : IsBase R Q) :
    Small R (ev ![P, Q] h + ev ![P', Q] h - ev ![addOf (B.FK k) P P', Q] h) := by
  have p0 : GP (pt k (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt k (n := 3) d 2) := gp_pt 2
  have c0 := pair_points_zero_constant p0 p2
  have c1 := pair_points_zero_constant p1 p2
  have c2 := pair_points_zero_constant (gp_addOf _ (gp_law B) _ _ p0 p1) p2
  have w1 : constantCoeff B.ph1 = 1 := by
    rw [← gt_const_ev_eq _ (triple_points_zero_constant (gp_zero₂ (n := 2)) (gp_pt 0) (gp_pt 1)), B.cocycleLeft_zero_fst, map_one]
  have key := Small.subst (isBase3 hP hP' hQ) ⟨by
    rw [map_sub, map_add (f := _), gt_const_ev_eq _ c0, gt_const_ev_eq _ c1, gt_const_ev_eq _ c2, const_gauge hh,
      add_zero, sub_self], _, w1, hh.ph1⟩
  have hV := triple_points_zero_constant hP.gp hP'.gp hQ.gp
  rw [gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV c0, gt_ev_ev' _ _ hV c1, gt_ev_ev' _ _ hV c2,
    eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ p0 p1, evP_pt _ hV, evP_pt _ hV,
    evP_pt _ hV] at key
  exact key

theorem small_add_right (hh : B.IsCanonGauge k h) {P Q Q' : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q)
    (hQ' : IsBase R Q') :
    Small R (ev ![P, Q] h + ev ![P, Q'] h - ev ![P, addOf (B.FK k) Q Q'] h) := by
  have p0 : GP (pt k (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt k (n := 3) d 2) := gp_pt 2
  have c0 := pair_points_zero_constant p0 p1
  have c1 := pair_points_zero_constant p0 p2
  have c2 := pair_points_zero_constant p0 (gp_addOf _ (gp_law B) _ _ p1 p2)
  have w1 : constantCoeff B.ph2 = 1 := by
    rw [← gt_const_ev_eq _ (triple_points_zero_constant (gp_zero₂ (n := 2)) (gp_pt 0) (gp_pt 1)), B.cocycleRight_zero_fst, map_one]
  have key := Small.subst (isBase3 hP hQ hQ') ⟨by
    rw [map_sub, map_add (f := _), gt_const_ev_eq _ c0, gt_const_ev_eq _ c1, gt_const_ev_eq _ c2, const_gauge hh,
      add_zero, sub_self], _, w1, hh.ph2⟩
  have hV := triple_points_zero_constant hP.gp hQ.gp hQ'.gp
  rw [gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV c0, gt_ev_ev' _ _ hV c1, gt_ev_ev' _ _ hV c2,
    eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ p1 p2, evP_pt _ hV, evP_pt _ hV,
    evP_pt _ hV] at key
  exact key

theorem small_foldr_left (hh : B.IsCanonGauge k h) {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b))
    {Q : Pt k m d} (hQ : IsBase R Q) (L : List ι) :
    Small R (ev ![L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0, Q] h -
      (L.map fun b => ev ![g b, Q] h).sum) := by
  induction L with
  | nil => exact small_zero.congr (by rw [List.foldr_nil, gauge_zero_left hh hQ.gp]; simp)
  | cons b L ih =>
    refine (ih.add (small_add_left hh (hg b) (isBase_foldr B hg L) hQ).neg).congr ?_
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    ring

theorem small_foldr_right (hh : B.IsCanonGauge k h) {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b))
    {P : Pt k m d} (hP : IsBase R P) (L : List ι) :
    Small R (ev ![P, L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0] h -
      (L.map fun b => ev ![P, g b] h).sum) := by
  induction L with
  | nil => exact small_zero.congr (by rw [List.foldr_nil, gauge_zero_right hh hP.gp]; simp)
  | cons b L ih =>
    refine (ih.add (small_add_right hh hP (hg b) (isBase_foldr B hg L)).neg).congr ?_
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    ring

theorem small_sum_scalar (hh : B.IsCanonGauge k h) {ι : Type} (s : Finset ι) (c : ι → O) {P Q : Pt k m d}
    (hP : IsBase R P) (hQ : IsBase R Q) :
    Small R (∑ i ∈ s, ev ![P, comp1 (B.actK k (c i)) Q] h - ev ![P, comp1 (B.actK k (∑ i ∈ s, c i)) Q] h) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := small_add_right hh hP (hQ.act B 0) (hQ.act B 0)
    rw [← add_act B 0 0 hQ.gp, add_zero] at this
    refine this.neg.congr ?_
    rw [Finset.sum_empty, Finset.sum_empty]
    ring
  | insert i s hi ih =>
    have := small_add_right hh hP (hQ.act B (c i)) (hQ.act B (∑ i ∈ s, c i))
    rw [← add_act B _ _ hQ.gp] at this
    refine (ih.add this).congr ?_
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    ring

theorem small_column (hh : B.IsCanonGauge k h) (w0 : O) (y : Fin m → O) :
    Small R (ev (n := m) ![(List.finRange m).foldr
        (fun b acc => addOf (B.FK k) (comp1 (B.actK k (y b)) (pt k d b)) acc) 0] (B.hL k h w0) -
      ∑ b : Fin m, ∑ b' : Fin m,
        ev (n := m) ![pt k d b, comp1 (B.actK k (w0 * (star (y b) * y b'))) (pt k d b')] h) := by
  have hg : ∀ b, IsBase R (comp1 (B.actK k (y b)) (pt k (n := m) d b)) := fun b => (isBase_pt b).act B _
  have hS := isBase_foldr B hg (List.finRange m)
  rw [FB.hL, gt_comp1_pt_right, formalSubst_single_of_formalSubst_two _ hS.gp _ _ (gp_pt 0) (gp_act B w0), gt_comp1_pt _ hS.gp]
  have h1 := small_foldr_left hh hg (hS.act B w0) (List.finRange m)
  rw [← Fin.sum_univ_def] at h1
  refine h1.trans (Small.sum_sub _ fun b => ?_)
  refine (small_balanced hh (y b) (isBase_pt b) (hS.act B w0)).trans ?_
  rw [act_act B _ _ hS.gp, act_foldr B _ hg]
  have h2 := small_foldr_right hh (fun b' => (hg b').act B (star (y b) * w0)) (isBase_pt b) (List.finRange m)
  rw [← Fin.sum_univ_def] at h2
  refine h2.congr ?_
  congr 1
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [act_act B _ _ (gp_pt b'), show star (y b) * w0 * y b' = w0 * (star (y b) * y b') by ring]

end Gauge

end GlobalTheory.MatrixGauge

namespace GlobalTheory

open MatrixGauge

theorem exists_integral_unit_matrix_gauge :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 : O) (m n : ℕ) (x : Fin m → Fin n → O), ∃ U : PS R m d, constantCoeff U = 1 ∧ FB.toK k U = FB.expS k ((∑ j : Fin n, ev (n := m) ![(List.finRange m).foldr (fun b acc => addOf (B.FK k) (comp1 (B.actK k (x b j)) (pt k d b)) acc) 0] (B.hL k h w0)) - ∑ b : Fin m, ∑ b' : Fin m, ev (n := m) ![pt k d b, comp1 (B.actK k (w0 * ∑ j : Fin n, star (x b j) * x b' j)) (pt k d b')] h) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 m n x
  have h1 := Small.sum_sub (Finset.univ : Finset (Fin n)) fun j => small_column hh w0 fun b => x b j
  refine (h1.trans ?_).2
  rw [Finset.sum_comm]
  refine Small.sum_sub _ fun b => ?_
  rw [Finset.sum_comm]
  refine Small.sum_sub _ fun b' => ?_
  rw [Finset.mul_sum]
  exact small_sum_scalar hh _ _ (isBase_pt b) (isBase_pt b')

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnColumnsSameValue
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns GlobalTheory.LawLog ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ColApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem map_polyT {T : CDVR} {C : Type} [Field C] (φ : T.Fr →+* C) (cx : Lt1 Dw → ℕ) {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) :
    MvPolynomial.map φ (polyT B cx) = MvPolynomial.aeval (fun ℓ : Let cx => ∑ j,
      MvPolynomial.C (φ (algebraMap T.V T.Fr (B ℓ.1.1.1 ℓ.1.2 j))) *
        (MvPolynomial.X ⟨ℓ.1.1.1.1, Fin.castLE (rk_le _) ℓ.2, j⟩ : MvPolynomial (LtN Dw n) C)) (polyH C cx) := by
  classical
  unfold polyT polyP polyH
  rw [map_prod, map_prod, ← Finset.prod_filter_of_ne (p := fun f => cx f ≠ 0)
    (fun f _ hf h0 => hf (by rw [h0, pow_zero, map_one])),
    Finset.prod_subtype (p := fun f => cx f ≠ 0) _ (fun f => by simp)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_rename, GlobalTheory.FGDepth.detPow, map_pow, map_pow, RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext a b : 2
  simp [GlobalTheory.CombMinor.cMat]

theorem exists_cols {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ} {cx : Lt1 Dw → ℕ} {n : ℕ}
    {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V} (hB : IsCols c T io p cx B) (N : ℕ) :
    ∃ x : Col cx → Fin n → 𝓞 E,
      (∀ b j, ∃ z : T.V, io (embK c b.1.1.1 (x b j)) = algebraMap T.V T.Fr (B b.1.1 b.2 j + (p : T.V) ^ N * z)) ∧
      ∀ b b', ∑ j, H.bar (x b j) * x b' j ∈ Ideal.span {(p : 𝓞 E) ^ N} := by
  obtain ⟨blk, hb⟩ := hB
  choose x h0 h1 h2 using fun f => (hb f).2.2 N
  refine ⟨fun b => x b.1 b.2, fun b j => h1 b.1 b.2 j, ?_⟩
  rintro ⟨f, b⟩ ⟨f', b'⟩
  by_cases hf : f = f'
  · subst hf
    simpa only [mul_comm] using h2 f b' b
  · rw [Finset.sum_eq_zero]
    · exact Ideal.zero_mem _
    intro j _
    dsimp only
    by_cases hj : j ∈ Set.range fun j => blk ⟨f, j⟩
    · rw [h0 f' b' j, mul_zero]
      rintro ⟨j2, e2⟩
      obtain ⟨j1, e1⟩ := hj
      exact hf (congrArg Sigma.fst (blk.injective (e1.trans e2.symm)))
    · rw [h0 f b j hj, map_zero, zero_mul]

theorem isIntV_ringHom {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (φ : 𝓞 E →+* X.C) (a : 𝓞 E) :
    IsIntV (vX_vp X) (φ a) := by
  rw [isIntV_iff, ← X.ints.isIntegral_iff_v_le_one]
  exact (map_isIntegral_int φ (Algebra.IsIntegral.isIntegral a)).tower_top

theorem le_v_pow_mul {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (N : ℕ) {z : X.C}
    (hz : IsIntV (vX_vp X) z) : (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X ((p : X.C) ^ N * z) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, vX_vp_p]
  refine le_add_of_le_of_nonneg (le_of_eq ?_) hz
  simp

theorem lin_col {C : Type} [Field C] {d m : ℕ} {κ : Type} [Fintype κ] {ι : κ → Type} [∀ b, Fintype (ι b)]
    (e : κ ≃ Fin m) (u : ∀ b, ι b → Fin d → C) (q : Fin m) :
    lin (fun ℓ : Σ b, ι b => u ℓ.1 ℓ.2) (fun ℓ => if e ℓ.1 = q then 1 else 0) =
      fun i => ∑ a, u (e.symm q) a i • (MvPowerSeries.X ⟨e.symm q, a⟩ : MvPowerSeries (Σ b, ι b) C) := by
  funext i
  unfold lin
  rw [Fintype.sum_sigma, Finset.sum_eq_single (e.symm q)]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    have hq : e b ≠ q := fun h => hb (by rw [← h]; simp)
    simp [hq]
  · simp

theorem exists_germ_cols : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (g : PS X.C n (chD Ch.ch)), MvIsInt (vX_vp X) g → ∃ f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) f ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e _ y Ch X cx n B hB N k g hg
  classical
  letI := io.toAlgebra
  obtain ⟨BT, -, -, -, -, -, -, e7⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y Ch
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra T.V X.C := (X.ιF.comp (algebraMap T.V T.Fr)).toAlgebra
  haveI : IsScalarTower T.V T.Fr X.C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := e7 X.C
  have hc := (h3 _).2 h4
  let eC := Fintype.equivFin (Col cx)
  let σ : Col cx → 𝓞 E →+* X.C := fun b => X.ιF.comp (io.comp (embK c b.1.1.1))
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct X.C BT a).mulVec (lieVec Ch X ℓ) =
      X.ιF (io (embK c ℓ.1 a)) • lieVec Ch X ℓ := by
    intro a ℓ
    funext i
    have h := congrArg X.ιF (congrFun (GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y Ch a ℓ) i)
    have hu : ∀ i, lieVec Ch X ℓ i = X.ιF (Ch.ch.uvec ℓ i) := fun i =>
      congrArg X.ιF (Ch.gen.1.2.2.2.2.2.2 ℓ i).symm
    simp only [Matrix.mulVec, dotProduct, dAct, h2, hu, Pi.smul_apply, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, dAct, FB.actK, MvPowerSeries.coeff_map, map_sum, map_mul, Pi.smul_apply,
      smul_eq_mul] at h ⊢
    exact h
  obtain ⟨K, hK⟩ := exists_germ_close (v := vX_vp X) BT (G := lawX Ch X) h1.symm (fgl Ch X).F_int
    (fun ℓ : Let cx => eC ℓ.1) (fun ℓ => frame Ch X ℓ.1.1.1 ℓ.2) (fun b a => σ (eC.symm b) a)
    (fun a ℓ => by rw [eC.symm_apply_apply]; exact heig a _) (isIntV_jX X) hc H.w0
    (fun ℓ i => isIntV_jX X _) (fun b a => isIntV_ringHom X _ a)
    (fun x => (GlobalTheory.exists_integral_unit_matrix_gauge _ _ _ _ BT _ hc H.w0 _ n x).imp fun _ h => h.2)
    (polyH X.C cx) k g hg
  obtain ⟨N', hN'⟩ := exists_nat_ge ((N : ℝ) + K)
  obtain ⟨x, hx1, hx2⟩ := exists_cols hB N'
  let β : Col cx → Fin n → X.C := fun b j => jX X (B b.1.1 b.2 j)
  obtain ⟨f, hf, hv⟩ := hK N' (fun b => x (eC.symm b)) (fun b => β (eC.symm b)) (fun b j => isIntV_jX X _)
    (fun b j => by
      obtain ⟨z, hz⟩ := hx1 (eC.symm b) j
      have : β (eC.symm b) j - σ (eC.symm b) (x (eC.symm b) j) = (p : X.C) ^ N' * jX X (-z) := by
        show _ - X.ιF (io (embK c _ _)) = _
        rw [hz]
        show jX X _ - jX X _ = _
        simp
      rw [this]
      exact le_v_pow_mul X N' (isIntV_jX X _))
    (fun b b' => by
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (hx2 (eC.symm b) (eC.symm b'))
      have : σ (eC.symm b') (H.w0 * ∑ j, star (x (eC.symm b) j) * x (eC.symm b') j) =
          (p : X.C) ^ N' * σ (eC.symm b') (H.w0 * r) := by
        rw [show ∑ j, star (x (eC.symm b) j) * x (eC.symm b') j = _ from hr, mul_left_comm, map_mul, map_pow,
          map_natCast]
      rw [this]
      exact le_v_pow_mul X N' (isIntV_ringHom X _ _))
  have cX : ∀ q : Fin (Fintype.card (Col cx)) × Fin (chD Ch.ch), MvPowerSeries.constantCoeff
      (MvPowerSeries.X ⟨eC.symm q.1, q.2⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) = 0 := fun q => by simp
  have hE : MvPowerSeries.HasSubst (expH Ch X cx) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun q =>
    nc_exPt (fgl Ch X) (fun i => by simp) q.2
  refine ⟨MvPowerSeries.subst (fun q : Fin (Fintype.card (Col cx)) × Fin (chD Ch.ch) =>
    (MvPowerSeries.X ⟨eC.symm q.1, q.2⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C)) f,
    ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst _ hf
      (fun q α => by rw [MvPowerSeries.coeff_X]; split_ifs <;> simp [IsIntV]) cX, ?_⟩
  refine le_trans (WithTop.coe_le_coe.2 (by linarith)) (hv.trans (le_of_eq ?_))
  congr 2
  · have hA := GlobalTheory.ExpCoord.constantCoeff_dpolyN_eq_derivAt0 X.C (vX_vp X) _ (lawX Ch X) (fgl Ch X) (fun _ => rfl) n (LtN Dw n) (Let cx)
      (fun ℓ => ℓ.2.2) (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (fun ℓ => β ℓ.1)
      (fun ℓ j => ⟨ℓ.1.1.1.1, Fin.castLE (rk_le _) ℓ.2, j⟩) (fun ℓ => frame Ch X ℓ.1.1.1 ℓ.2) (fun _ _ => rfl)
      (fun _ _ => rfl) (polyH X.C cx)
    unfold nabX nabValN
    rw [map_polyT]
    simp only [eC.symm_apply_apply, FB.hL, h2]
    exact (hA _).symm
  · rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero cX) hE]
    congr 2
    funext q
    rw [MvPowerSeries.subst_X hE]
    unfold colExp
    rw [lin_col eC (fun b : Col cx => frame Ch X b.1.1)]
    rfl

end GlobalTheory.ColApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGermOnColumnsSameValueStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_germ_on_columns_same_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (g : PS X.C n (chD Ch.ch)), MvIsInt (vX_vp X) g → ∃ f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) f ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  first | exact @GlobalTheory.ColApprox.exists_germ_cols | exact GlobalTheory.ColApprox.exists_germ_cols | (intros; apply GlobalTheory.ColApprox.exists_germ_cols <;> assumption)
end
