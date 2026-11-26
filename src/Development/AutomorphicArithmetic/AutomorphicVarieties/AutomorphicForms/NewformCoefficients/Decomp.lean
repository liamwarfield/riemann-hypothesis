module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolCap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd Matrix in
theorem UpperTheory.V.Af.Nf.decomp :
    UpperTheory.V.Af.Nf.Decomp := by
  intro M hM g
  obtain ⟨hK, hA⟩ := UpperTheory.V.Af.Nf.kOpen M hM
  obtain ⟨γ, h, y, u, hu, -, e⟩ := UpperTheory.V.Sd.strongApp ℚ _ hK g
  obtain ⟨r, u', -, hu', rfl⟩ := UpperTheory.V.Af.Nf.ratAd.1 y
  have h1 : aff (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u') 0 = toF (aff r 0) * aff u' 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [aff, toF, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨γ * aff r 0, (toR (aff r 0))⁻¹ * GeneralLinearGroup.map ev h, aff u' 0 * u,
    mul_mem (hA u' hu' 0 (zero_mem _)) hu, ?_⟩
  rw [e, h1, ← upR_ev, map_mul (ratGL ℚ 2), ratGL_eq (aff r 0), upR_comm (toR _), map_mul upR, map_inv upR, mul_assoc (toF _), map_mul (finGL ℚ 2) (toF _),
    ← mul_assoc (upR _), upR_comm _ (toF _)]
  simp only [mul_assoc, mul_inv_cancel_left]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftExp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CoefAt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

private theorem ord_diff (w : HeightOneSpectrum (𝓞 ℚ)) : ordI w (differentIdeal ℤ (𝓞 ℚ)) = 0 := by
  have h : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, absNorm_differentIdeal ℚ (𝓞 ℚ), discr_rat]; rfl
  rw [h, ordI, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one, Associates.count_zero w.associates_irreducible]

private theorem eq_of_ord {I J : Ideal (𝓞 ℚ)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ w, ordI w I = ordI w J) : I = J := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI, ← Ideal.finprod_heightOneSpectrum_factorization hJ]
  refine finprod_congr fun w => ?_
  exact congrArg (fun n => w.asIdeal ^ n) (h w)

private theorem val_unit {u : (Af ℚ)ˣ} (hu : IsZU u) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (pLoc ℚ w (u : Af ℚ)) = 1 := by
  have h1 : Valued.v (pLoc ℚ w (u : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.1 w
  have h2 : Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.2 w
  have h3 : Valued.v (pLoc ℚ w (u : Af ℚ)) * Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm h1 ?_
  calc 1 = _ := h3.symm
    _ ≤ Valued.v (pLoc ℚ w (u : Af ℚ)) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

private theorem genD_iff (q : ℚ) {u : (Af ℚ)ˣ} (hu : IsZU u) (𝔪 : Ideal (𝓞 ℚ)) :
    GenD (algebraMap ℚ (Af ℚ) q * (u : Af ℚ)) 𝔪 ↔
      𝔪 ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), w.valuation ℚ q = WithZero.exp (-(ordI w 𝔪 : ℤ)) := by
  refine and_congr_right fun _ => forall_congr' fun w => ?_
  have h : Valued.v (pLoc ℚ w (algebraMap ℚ (Af ℚ) q)) = w.valuation ℚ q :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q
  rw [map_mul, map_mul, val_unit hu, mul_one, h, ord_diff, Nat.cast_zero, zero_sub]

private theorem val_nat {n : ℕ} (hn : n ≠ 0) (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ (n : ℚ) = WithZero.exp (-(ordI w (Ideal.span {(n : 𝓞 ℚ)}) : ℤ)) := by
  rw [← map_natCast (algebraMap (𝓞 ℚ) ℚ) n, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg w (Nat.cast_ne_zero.2 hn)]
  rfl

theorem UpperTheory.V.Af.Nf.coefAt :
    UpperTheory.V.Af.Nf.CoefAt := by
  intro a q hq u hu
  by_cases hd : q.den = 1
  · rw [if_pos hd]
    have hnum : 0 < q.num := Rat.num_pos.2 hq
    have hn : q.num.toNat ≠ 0 := by omega
    have hqn : q = (q.num.toNat : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnum.le]
      exact ((Rat.den_eq_one_iff q).1 hd).symm
    have hb : Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact Nat.cast_ne_zero.2 hn
    have hv : ∀ w : HeightOneSpectrum (𝓞 ℚ),
        w.valuation ℚ q = WithZero.exp (-(ordI w (Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)}) : ℤ)) := fun w => by
      rw [← val_nat hn w, ← hqn]
    have hex : ∃ 𝔪, GenD (algebraMap ℚ (Af ℚ) q * (u : Af ℚ)) 𝔪 := ⟨_, (genD_iff q hu _).2 ⟨hb, hv⟩⟩
    obtain ⟨h1, h2⟩ := (genD_iff q hu _).1 hex.choose_spec
    have he : hex.choose = Ideal.span {((q.num.toNat : ℕ) : 𝓞 ℚ)} := eq_of_ord h1 hb fun w => by
      have := WithZero.exp_injective ((h2 w).symm.trans (hv w))
      omega
    rw [UpperTheory.V.Sd.coefAt, dite_eq_left hex, he, Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]
  · rw [if_neg hd, UpperTheory.V.Sd.coefAt, dite_eq_right]
    rintro ⟨𝔪, h⟩
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ q fun w => by
      rw [((genD_iff q hu _).1 h).2 w, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    obtain ⟨m, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective r
    apply hd
    rw [← hr, eq_intCast Rat.ringOfIntegersEquiv.symm m, map_intCast]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsF
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

private theorem val_one (u : (Af ℚ)ˣ) (hu : IsZU u) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (pLoc ℚ w (u : Af ℚ)) = 1 := by
  have a1 : Valued.v (pLoc ℚ w (u : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.1 w
  have a2 : Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) ≤ 1 := Subring.mem_iInf.1 hu.2 w
  have a3 : Valued.v (pLoc ℚ w (u : Af ℚ)) * Valued.v (pLoc ℚ w ((u⁻¹ : (Af ℚ)ˣ) : Af ℚ)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc ℚ w (u : Af ℚ)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

theorem UpperTheory.V.Af.Nf.absF :
    UpperTheory.V.Af.Nf.AbsF := by
  intro r hr u hu
  obtain ⟨-, h2, h3, h4⟩ := UpperTheory.V.Sd.Hm.absf ℚ
  rw [h2, h3 u (val_one u hu), mul_one]
  have h := h4 r
  have hr' : (0 : ℝ) < ((r : ℚ) : ℝ) := by exact_mod_cast hr
  have e : (∏ v, |reAt v (r : ℚ)|) = ((r : ℚ) : ℝ) := by
    rw [Fintype.prod_subsingleton _ Rat.infinitePlace, reAt, eq_ratCast]
    simp [abs_of_pos hr']
  rw [e] at h
  exact eq_inv_of_mul_eq_one_right h
end

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

private theorem reAt_rat (v : InfinitePlace ℚ) (q : ℚ) : reAt v q = (q : ℝ) := by
  simp [reAt]

private theorem sum_f {k M : ℕ} (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ => coef f (n + 1) * Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) * (τ : ℂ)))) (f τ) := by
  haveI : NeZero M := ⟨by omega⟩
  have hp : (1 : ℝ) ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hp)
    f.holo' (ModularFormClass.bdd_at_infty f) τ
  have h0 : (qExpansion 1 f).coeff 0 = 0 := CuspFormClass.qExpansion_coeff_zero f one_pos hp
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, h0, zero_smul, sub_zero] at h
  refine cast (congrArg (HasSum · (f τ)) (funext fun n => ?_)) h
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul, coef]
  congr 2
  push_cast
  ring

private theorem nsl_aff (k : ℕ) (f : ℍ → ℂ) (y : ℝˣ) (hy : 0 < (y : ℝ)) (x : ℝ) :
    nsl k f (aff y x : GL (Fin 2) ℝ) UpperHalfPlane.I =
      (((y : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f (ofComplex ((x : ℂ) + Complex.I * (y : ℝ))) := by
  have hd : (aff y x : GL (Fin 2) ℝ).val.det = y := by simp [aff, Matrix.det_fin_two]
  rw [nsl, hd, abs_of_pos hy, sign_pos hy]
  simp [aff, add_comm, mul_comm]

private theorem pt_eq (x : TR.Rinf ℚ) (y : (TR.Rinf ℚ)ˣ) (r : ℚˣ) (u : (Af ℚ)ˣ) :
    TR.infGL ℚ 2 (aff y x) * finGL ℚ 2 (aff (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u) 0) =
      ratGL ℚ 2 (aff r 0) * (upR (aff (Units.map ev.toMonoidHom y * (Units.map (Rat.castHom ℝ).toMonoidHom r)⁻¹)
        (ev x / (r : ℚ))) * finGL ℚ 2 (aff u 0)) := by
  have hr : ((r : ℚ) : ℝ) ≠ 0 := by exact_mod_cast r.ne_zero
  rw [ratGL_eq, mul_assoc, ← mul_assoc (finGL ℚ 2 _), ← upR_comm, mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, ← upR_ev]
  congr 2
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [aff, toR, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp
  · ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [aff, toF, Matrix.mul_apply, Fin.sum_univ_succ]

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.liftExp :
    UpperTheory.V.Af.Nf.LiftExp := by
  intro k M hM f φ hφ x y hy yf
  obtain ⟨r, u, hr, hu, rfl⟩ := ratAd.1 yf
  have hr' : (0 : ℝ) < ((r : ℚ) : ℝ) := by exact_mod_cast hr
  have hrc : (((r : ℚ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hy0 : 0 < ev y.val := hy _
  have hyv : ((Units.map ev.toMonoidHom y * (Units.map (Rat.castHom ℝ).toMonoidHom r)⁻¹ : ℝˣ) : ℝ) = ev y.val * ((r : ℚ) : ℝ)⁻¹ := by
    simp
  have hpos : 0 < ev y.val * ((r : ℚ) : ℝ)⁻¹ := by positivity
  have hprod : ∏ v, y.val v = ev y.val := Fintype.prod_subsingleton _ _
  rw [pt_eq, hφ _ _ _ ((kOpen M hM).2 u hu 0 (zero_mem _)), nsl_aff _ _ _ (hyv ▸ hpos), UpperTheory.V.Af.Nf.absF r hr u hu, hyv, hprod,
    mul_div_cancel_left₀ _ (by exact_mod_cast (Real.rpow_pos_of_pos hpos _).ne'), Pi.zero_apply, sub_zero]
  have him : 0 < (((ev x / (r : ℚ) : ℝ) : ℂ) + Complex.I * ((ev y.val * ((r : ℚ) : ℝ)⁻¹ : ℝ) : ℂ)).im := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re, zero_add] using hpos
  have hc : ∀ q : ℚ, 0 < q → UpperTheory.V.Sd.coefAt (icoef f) (algebraMap ℚ (Af ℚ) q *
      ((Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u : (Af ℚ)ˣ) : Af ℚ)) =
      if (q * r).den = 1 then coef f (q * r).num.toNat else 0 := fun q hq => by
    rw [← UpperTheory.V.Af.Nf.coefAt (coef f) (q * r) (mul_pos hq hr) u hu, map_mul, mul_assoc]
    rfl
  let j : ℕ → {ξ : ℚ // ∀ v, 0 < reAt v ξ} := fun n => ⟨((n + 1 : ℕ) : ℚ) / r, fun v => by
    rw [reAt_rat]; exact_mod_cast div_pos (by positivity) hr⟩
  have hj : Function.Injective j := fun a b h => by
    have := congrArg Subtype.val h
    simpa [j, hr.ne'] using this
  have hq : ∀ ξ : {ξ : ℚ // ∀ v, 0 < reAt v ξ}, 0 < ξ.1 := fun ξ => by
    have := ξ.2 Rat.infinitePlace
    rw [reAt_rat] at this
    exact_mod_cast this
  rw [← hj.hasSum_iff fun ξ hξ => ?_]
  · convert sum_f hM f (ofComplex _) using 2 with n
    rw [ofComplex_apply_of_im_pos him]
    have e : (j n).1 * r = ((n + 1 : ℕ) : ℚ) := div_mul_cancel₀ _ hr.ne'
    simp only [Function.comp]
    rw [hc _ (hq _), e, Fintype.sum_subsingleton _ Rat.infinitePlace, reAt_rat]
    simp only [Rat.den_natCast, Rat.num_natCast, Int.toNat_natCast, if_true]
    congr 3
    change ((((((n + 1 : ℕ) : ℚ) / r : ℚ) : ℝ)) : ℂ) * ((ev x : ℂ) + Complex.I * (ev y.val : ℂ)) = _
    push_cast
    ring
  · rw [hc _ (hq ξ), if_neg, zero_mul]
    intro hd
    have h1 : 0 < (ξ.1 * r).num := Rat.num_pos.2 (mul_pos (hq ξ) hr)
    refine hξ ⟨(ξ.1 * r).num.toNat - 1, Subtype.ext ?_⟩
    have h2 : (((ξ.1 * r).num.toNat - 1 + 1 : ℕ) : ℤ) = (ξ.1 * r).num := by omega
    change ((_ : ℕ) : ℚ) / r = _
    rw [← Int.cast_natCast, h2, Rat.coe_int_num_of_den_eq_one hd, mul_div_cancel_right₀ _ hr.ne']
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCrit
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AutPer
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd Filter Topology
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem map_aff {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map p (aff 1 x) = aff 1 (p x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.GeneralLinearGroup.map]

private theorem aff_comm {R : Type} [CommRing R] (x y : R) : aff 1 x * aff 1 y = aff 1 y * aff (1 : Rˣ) x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem aff_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem continuous_aff {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun x : R => aff (1 : Rˣ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · change Continuous fun x : R => (!![(((1 : Rˣ)⁻¹ : Rˣ) : R), -((((1 : Rˣ)⁻¹ : Rˣ) : R) * x); 0, 1] : Matrix (Fin 2) (Fin 2) R)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem unip_eq {R : Type} [CommRing R] (x : BlockIx 2 1 → R) : unip x = aff 1 (x ⟨(0, 1), by decide⟩) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (1 + nilM x : Matrix (Fin 2) (Fin 2) R) i j = _
  fin_cases i <;> fin_cases j <;> simp [aff, nilM]

end UpperTheory.V.Af.Nf

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.autPer :
    UpperTheory.V.Af.Nf.AutPer := by
  intro φ hl ho g
  set t : GL (Fin 2) (Af ℚ) := Matrix.GeneralLinearGroup.map (pFin ℚ) g with ht
  have hc : Continuous fun x : Af ℚ => t⁻¹ * aff 1 x * t := (continuous_const.mul continuous_aff).mul continuous_const
  have h0 : t⁻¹ * aff 1 (0 : Af ℚ) * t ∈ {u | TR.finRep ℚ 2 u φ = φ} := by
    simp [aff_zero]
  obtain ⟨n, hn⟩ := (((hc.tendsto 0).comp (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ)).eventually
    (ho.mem_nhds h0)).exists
  refine ⟨n.factorial, n.factorial_pos, fun x => ?_⟩
  set N : ℕ := n.factorial with hN
  have hn' : ∀ g, φ.1 (g * finGL ℚ 2 (t⁻¹ * aff 1 (N : Af ℚ) * t)) = φ.1 g := fun g => congrFun (congrArg Subtype.val hn) g
  have e1 : g * finGL ℚ 2 (t⁻¹ * aff 1 (N : Af ℚ) * t) = finGL ℚ 2 (aff 1 (N : Af ℚ)) * g :=
    TR.ga_ext (by simp) (by simp [← ht, mul_assoc])
  have e2 : unip x * finGL ℚ 2 (aff 1 (N : Af ℚ)) = finGL ℚ 2 (aff 1 (N : Af ℚ)) * unip x :=
    TR.ga_ext (by simp) (by simp [unip_eq, map_aff, aff_comm])
  have e3 : ratGL ℚ 2 (aff 1 (N : ℚ)) = upR (aff 1 (N : ℝ)) * finGL ℚ 2 (aff 1 (N : Af ℚ)) := by
    rw [ratGL_eq, toR, toF, map_aff, map_aff, map_natCast, map_natCast]
  rw [← hn', ← hl (aff 1 (N : ℚ)) (unip x * g), e3, mul_assoc, mul_assoc, e1, mul_assoc, ← mul_assoc (unip x), e2, mul_assoc]
end

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af.Nf
open scoped Matrix MatrixGroups

private theorem two_periods {f : ℝ → ℂ} (hc : Continuous f) {N N' : ℕ} (hN' : 0 < N') (h : Function.Periodic f N)
    (h' : Function.Periodic f N') (h0 : ∫ t in (0 : ℝ)..N', f t = 0) : ∫ t in (0 : ℝ)..N, f t = 0 := by
  have e1 := h.intervalIntegral_add_zsmul_eq (N' : ℤ) 0 fun a b => hc.intervalIntegrable a b
  have e2 := h'.intervalIntegral_add_zsmul_eq (N : ℤ) 0 fun a b => hc.intervalIntegrable a b
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast] at e1 e2
  rw [h0, mul_zero, mul_comm, e1] at e2
  exact (mul_eq_zero.1 e2).resolve_left (Nat.cast_ne_zero.2 hN'.ne')

private theorem aff_add {R : Type} [CommRing R] (x y : R) : aff 1 (x + y) = aff 1 x * aff 1 y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem upR_aff (t : ℝ) : upR (aff 1 t) = aff 1 (TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) t)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (1 : Matrix (Fin 2) (Fin 2) (Ad ℚ)) i j - TR.sInf ℚ ((1 : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) i j) +
    TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) ((aff 1 t).val i j)) = (aff 1 _).val i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem ratGL_aff (q : ℚ) : ratGL ℚ 2 (aff 1 q) = aff 1 (algebraMap ℚ (Ad ℚ) q) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap ℚ (Ad ℚ) ((aff 1 q).val i j) = (aff 1 _).val i j
  fin_cases i <;> fin_cases j <;> simp [aff]

theorem UpperTheory.V.Af.Nf.cuspCrit :
    UpperTheory.V.Af.Nf.CuspCrit := by
  intro φ hl ho hct r h0 h1 _ _ μ D hμ hD g
  obtain rfl : r = 1 := by omega
  obtain ⟨i1, i2, -, i3, -, hu, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock ℚ
  have hφ := smCont ℚ 2 φ ho
  obtain ⟨N, hN, hper⟩ := autPer φ hl ho g
  let e : ℝ → BlockIx 2 1 → Ad ℚ := fun t _ => TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) t)
  have he : Continuous e := continuous_pi fun _ =>
    (((TR.continuous_infEq ℚ).comp (continuous_algebraMap ℝ (TR.Rinf ℚ))).prodMk continuous_const :
      Continuous fun t : ℝ => ((TR.infEq ℚ (algebraMap ℝ (TR.Rinf ℚ) t), 0) :
        InfiniteAdeleRing ℚ × Af ℚ))
  have hadd : ∀ t x, unip (e t + x) = upR (aff 1 t) * unip x := fun t x => by
    rw [hx, hx, upR_aff, ← aff_add]; rfl
  have hψ : Continuous fun x : BlockIx 2 1 → Ad ℚ => φ.1 (unip x * g) := hφ.comp (hu.mul continuous_const)
  refine avgZero _ (ratN ℚ 2 1) μ D hμ hD _ hψ ?_ e he N (Nat.cast_pos.2 hN) fun x => ?_
  · rintro _ ⟨q, rfl⟩ x
    have : ∀ y : BlockIx 2 1 → Ad ℚ, y ⟨(0, 1), by decide⟩ = algebraMap ℚ (Ad ℚ) (q ⟨(0, 1), by decide⟩) →
        unip (y + x) = ratGL ℚ 2 (aff 1 (q ⟨(0, 1), by decide⟩)) * unip x := fun y hy => by
      rw [hx, hx, ratGL_aff, ← aff_add, ← hy]; rfl
    rw [this _ rfl, mul_assoc, hl]
  · obtain ⟨N', hN', hp', hz⟩ := hct (unip x * g)
    have ef : (fun t : ℝ => φ.1 (upR (aff 1 t) * (unip x * g))) = fun t => φ.1 (unip (e t + x) * g) :=
      funext fun t => by rw [hadd, mul_assoc]
    have hp : Function.Periodic (fun t : ℝ => φ.1 (upR (aff 1 t) * (unip x * g))) N := fun t => by
      have := hper (e t + x)
      rw [hadd, mul_assoc] at this
      beta_reduce
      rw [add_comm t, aff_add, map_mul, mul_assoc, this]
    rw [ef] at hp hp' hz
    exact two_periods (hψ.comp (he.add continuous_const)) hN' hp hp' hz
end
