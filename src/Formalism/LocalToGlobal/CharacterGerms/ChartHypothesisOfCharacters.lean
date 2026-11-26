module

public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
public import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfUnitGerm
public import Formalism.IncomingBounds.FlowDegreeBounds.Cayley
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffPderivUncurry
section -- merged from Formalism.LocalToGlobal.CharacterGerms.MfactMulCoeffMvExpLinF
noncomputable section

open scoped BigOperators
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

section ExpLin

variable {K : Type} [Field K] {τ : Type} [Fintype τ]

def linF (lam : τ → K) : MvPowerSeries τ K := ∑ w, lam w • (X w : MvPowerSeries τ K)

theorem constantCoeff_linF (lam : τ → K) : constantCoeff (linF lam) = 0 := by
  simp [linF, MvPowerSeries.smul_eq_C_mul]

theorem pderiv_linF (lam : τ → K) (w : τ) : pderiv (R := K) w (linF lam) = C (lam w) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [linF, map_sum]
  simp only [Derivation.map_smul, pderiv_X]
  rw [Finset.sum_eq_single w]
  · simp [MvPowerSeries.smul_eq_C_mul]
  · intro b _ hb
    simp [hb]
  · simp

theorem coeff_linF_pow_step (lam : τ → K) (w : τ) (m : τ →₀ ℕ) (k : ℕ) :
    coeff (m + Finsupp.single w 1) (linF lam ^ (k + 1)) * ((m w : K) + 1)
      = ((k : K) + 1) * lam w * coeff m (linF lam ^ k) := by
  have h := congrArg (coeff m) (Derivation.leibniz_pow (pderiv (R := K) w) (linF lam) (k + 1))
  rw [coeff_pderiv, pderiv_linF] at h
  rw [h]
  rw [Nat.add_sub_cancel, smul_eq_mul, map_nsmul, MvPowerSeries.coeff_mul_C, nsmul_eq_mul]
  push_cast
  ring

variable [CharZero K]

private theorem coeff_mvExp_eq_sum_range_degree {K : Type} [Field K] {ρ : Type} (h : MvPowerSeries ρ K) (m : ρ →₀ ℕ) :
    coeff m (Formalism.IncomingBounds.mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : K) := rfl

private theorem add_single_one_ne_zero {ρ : Type} (m : ρ →₀ ℕ) (w : ρ) : m + Finsupp.single w 1 ≠ 0 := by
  intro h
  have := congrArg (fun f : ρ →₀ ℕ => f w) h
  simp at this

theorem coeff_mvExp_linF_step (lam : τ → K) (w : τ) (m : τ →₀ ℕ) :
    coeff (m + Finsupp.single w 1) (mvExp (linF lam)) * ((m w : K) + 1)
      = lam w * coeff m (mvExp (linF lam)) := by
  rw [coeff_mvExp_eq_sum_range_degree, coeff_mvExp_eq_sum_range_degree, map_add Finsupp.degree, Finsupp.degree_single,
    Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
  have h0 : coeff (m + Finsupp.single w 1) (linF lam ^ 0) = 0 := by
    classical
    rw [pow_zero, MvPowerSeries.coeff_one, if_neg (add_single_one_ne_zero m w)]
  rw [h0, zero_div, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h3 := coeff_linF_pow_step lam w m j
  have hf : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj : ((j : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [div_mul_eq_mul_div, h3, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp

theorem coeff_zero_mvExp (h : MvPowerSeries τ K) : coeff 0 (mvExp h) = 1 := by
  rw [coeff_mvExp_eq_sum_range_degree]
  simp

end ExpLin

section Rename

variable {K : Type} [Field K] {σ τ : Type}

end Rename

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

section Uniq

variable {K : Type} [Field K] [CharZero K] {τ : Type} [Fintype τ]

theorem exp_unique (y : τ → K) (Ψ : MvPowerSeries τ K) (h0 : MvPowerSeries.constantCoeff Ψ = 1)
    (hd : ∀ w, MvPowerSeries.pderiv (R := K) w Ψ = Ψ * MvPowerSeries.C (y w)) : Ψ = mvExp (linF y) := by
  have step : ∀ (w : τ) (m : τ →₀ ℕ), MvPowerSeries.coeff (m + Finsupp.single w 1) Ψ * ((m w : K) + 1) =
      y w * MvPowerSeries.coeff m Ψ := by
    intro w m
    have h := congrArg (MvPowerSeries.coeff m) (hd w)
    rw [MvPowerSeries.coeff_pderiv, mul_comm Ψ, MvPowerSeries.coeff_C_mul] at h
    exact h
  have key : ∀ (n : ℕ) (m : τ →₀ ℕ), m.degree = n →
      MvPowerSeries.coeff m Ψ = MvPowerSeries.coeff m (mvExp (linF y)) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
      subst hm0
      rw [coeff_zero_mvExp, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    | succ n ih =>
      intro m hm
      obtain ⟨w, hw⟩ : ∃ w, m w ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        have : m = 0 := Finsupp.ext hcon
        rw [this] at hm
        simp at hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        ext x
        by_cases hx : x = w
        · subst hx
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
          omega
        · simp [Ne.symm hx]
      have hdeg : m'.degree = n := by
        rw [map_add (f := _), Finsupp.degree_single] at hm
        omega
      have hne : ((m' w : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' w)
      have e1 := step w m'
      have e2 := coeff_mvExp_linF_step y w m'
      rw [ih m' hdeg, ← e2] at e1
      exact mul_right_cancel₀ hne e1
  ext m
  exact key _ m rfl

end Uniq

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

open VP

theorem chi_mul {χ : PS C 1 dd} (hχ : Y.IsChar χ) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (un1 χ) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ) *
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (un1 χ) := by
  have h := hχ.2.2
  rw [eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst] at h
  rw [subst_singlePointUncurry (cc_F Y), subst_singlePointUncurry (fun _ => cc_X _), subst_singlePointUncurry (fun _ => cc_X _)]
  have h2 : (fun p : Fin 1 × Fin dd => addOf Y.B.G.F (pt C dd 0) (pt C dd 1) p.2) =
      fun p : Fin 1 × Fin dd => Y.B.G.F p.2 := by
    funext p
    exact ev_id _
  rw [h2] at h
  exact h

theorem constantCoeff_pderiv_uncurry (χ : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := C) i (un1 χ)) = dlogC χ i := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  have h1 : MvPowerSeries.coeff (Finsupp.single i 1) (un1 χ) = dlogC χ i := by
    show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) χ = _
    rw [Finsupp.mapDomain_single]
    rfl
  simp [h1]

def Psi (χ : PS C 1 dd) : MvPowerSeries (Fin dd) C := MvPowerSeries.subst (e Y) (un1 χ)

theorem chi_ode {χ : PS C 1 dd} (hχ : Y.IsChar χ) (i : Fin dd) :
    MvPowerSeries.pderiv (R := C) i (Psi Y χ) = Psi Y χ * MvPowerSeries.C (dlogC χ i) := by
  have hFK : ∀ k, Y.B.FK C k = Y.B.G.F k := by
    intro k
    show MvPowerSeries.map (algebraMap C C) (Y.B.G.F k) = _
    rw [Algebra.algebraMap_self, MvPowerSeries.map_id]
    rfl

  have hL : MvPowerSeries.pderiv (R := C) i (Psi Y χ) =
      ∑ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv (R := C) k (un1 χ)) := by
    unfold Psi
    rw [pderiv_subst (og (cc_e Y))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := expODE Y i k
    rw [hFK] at this
    show MvPowerSeries.pderiv (R := C) i (un1 (Y.ex k)) * _ = _
    rw [this]

  have h := congrArg (fun G => MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) G)) (chi_mul Y hχ)
  beta_reduce at h
  rw [Derivation.leibniz, pderiv_subst (og (cc_F Y)), pderiv_subst (og fun _ => cc_X _), pderiv_subst (og fun _ => cc_X _),
    MvPowerSeries.subst_add (hs (cc_exZero Y)), subst_sum (cc_exZero Y), smul_eq_mul, smul_eq_mul,
    subst_mul (cc_exZero Y), subst_mul (cc_exZero Y), subst_sum (cc_exZero Y), subst_sum (cc_exZero Y)] at h
  have h1 : ∀ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k) *
      MvPowerSeries.subst (fun k => Y.B.G.F k) (MvPowerSeries.pderiv (R := C) k (un1 χ))) =
      MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv (R := C) k (un1 χ)) := by
    intro k
    rw [subst_mul (cc_exZero Y), subst_subst (cc_F Y) (cc_exZero Y)]
    congr 2
    funext k'
    exact F_exZero Y k'
  have h2 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) k (un1 χ))) = 0 := by
    intro k
    rw [MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_mul,
      subst_zero' (cc_exZero Y)]
  have h3 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) k (un1 χ))) = if k = i then MvPowerSeries.C (dlogC χ i) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [MvPowerSeries.pderiv_X_self, one_mul, subst_subst (fun _ => cc_X _) (cc_exZero Y), if_pos rfl]
      have : (fun s : Fin dd => MvPowerSeries.subst (exZero Y) (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) =
          fun _ => 0 := by
        funext s
        rw [subst_X (cc_exZero Y)]
        rfl
      rw [this, subst_zeroPt, constantCoeff_pderiv_uncurry]
    · rw [MvPowerSeries.pderiv_X_of_ne (fun hh => hk (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' (cc_exZero Y),
        if_neg hk]
  have h4 : MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ)) = Psi Y χ := by
    rw [subst_subst (fun _ => cc_X _) (cc_exZero Y)]
    unfold Psi
    congr 1
    funext s
    rw [subst_X (cc_exZero Y)]
    rfl
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl fun k _ => h2 k,
    Finset.sum_congr rfl fun k _ => h3 k, Finset.sum_const_zero, mul_zero, add_zero, Finset.sum_ite_eq', h4] at h
  rw [hL, h]
  simp

theorem cc_Psi {χ : PS C 1 dd} (hχ : Y.IsChar χ) : MvPowerSeries.constantCoeff (Psi Y χ) = 1 := by
  obtain ⟨-, hχ1, -⟩ := hχ
  have hu : ∀ f : PS C 1 dd, MvPowerSeries.constantCoeff (un1 f) = MvPowerSeries.constantCoeff f := by
    intro f
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _
    rw [Finsupp.mapDomain_zero]
  have he0 : ∀ k, MvPowerSeries.constantCoeff (e Y k) = 0 := fun k => (hu _).trans (Y.ex_const k)
  have hA : MvPowerSeries.HasSubst (e Y) := MvPowerSeries.hasSubst_of_constantCoeff_zero he0
  unfold Psi
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hA, finsum_eq_single _ 0]
  · simp [hu, hχ1]
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs), smul_zero]
    rw [map_pow, he0, zero_pow hs]

theorem chi_exp {χ : PS C 1 dd} (hχ : Y.IsChar χ) : Psi Y χ = mvExp (linF (dlogC χ)) := exp_unique (dlogC χ) (Psi Y χ) (cc_Psi Y hχ) (chi_ode Y hχ)

end ChG

end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

open VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem integralSeries_uncurry_one {χ : PS C 1 dd} (h : IntS V χ) : IntS V (un1 χ) := by
  intro μ
  exact h _

end ChG


section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
