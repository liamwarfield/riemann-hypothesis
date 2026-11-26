module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Af.Nf

private theorem cv_mem {x : Af ℚ} : x ∈ Ohat ℚ ↔ ∀ w : Pl ℚ, Valued.v (pLoc ℚ w x) ≤ 1 := by
  simp [Ohat, Subring.mem_iInf, HeightOneSpectrum.mem_adicCompletionIntegers]

private theorem cv_val (w : Pl ℚ) (x : ℚ) : Valued.v (pLoc ℚ w (algebraMap ℚ (Af ℚ) x)) = w.valuation ℚ x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

private theorem cv_nat (w : Pl ℚ) (n : ℕ) : w.valuation ℚ (n : ℚ) = w.intValuation (n : 𝓞 ℚ) := by
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ)]
  exact congrArg _ (map_natCast (algebraMap (𝓞 ℚ) ℚ) n).symm

private theorem cv_one (w : Pl ℚ) (n : ℕ) (h : ¬ normV w ∣ n) : w.valuation ℚ (n : ℚ) = 1 := by
  obtain ⟨hp, hI, -⟩ := places w
  rw [cv_nat]
  refine le_antisymm (w.intValuation_le_one _) (not_lt.1 fun hlt => ?_)
  have hn : (n : 𝓞 ℚ) ∈ w.asIdeal := (w.intValuation_lt_one_iff_mem _).1 hlt
  have hq : ((normV w : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := by rw [hI]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a, b, e⟩ : IsCoprime ((normV w : ℕ) : 𝓞 ℚ) (n : 𝓞 ℚ) := ((Nat.Prime.coprime_iff_not_dvd hp).2 h).cast
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ add_mem (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hn)))

private theorem cv_unif (w : Pl ℚ) : w.valuation ℚ ((normV w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨hp, hI, -⟩ := places w
  rw [cv_nat]
  exact w.intValuation_singleton (by exact_mod_cast hp.ne_zero) hI

private theorem cv_ne {v w : Pl ℚ} (h : v ≠ w) : v.valuation ℚ ((normV w : ℕ) : ℚ) = 1 := by
  refine cv_one v _ fun hd => h (HeightOneSpectrum.ext ?_)
  rw [(places v).2.1, (places w).2.1, (Nat.prime_dvd_prime_iff_eq (places v).1 (places w).1).1 hd]

private theorem cv_div {M : ℕ} (hM : 1 ≤ M) {w : Pl ℚ} (hw : ¬ normV w ∣ M) {x : Af ℚ}
    (h0 : ∀ v, v ≠ w → pLoc ℚ v x = 0) (h1 : Valued.v (pLoc ℚ w x) ≤ 1) : ∃ y ∈ Ohat ℚ, x = M * y := by
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  refine ⟨algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * x, cv_mem.2 fun v => ?_, ?_⟩
  · by_cases h : v = w
    · subst h
      rw [map_mul, map_mul, cv_val, map_inv₀, cv_one v M hw, inv_one, one_mul]; exact h1
    · rw [map_mul, h0 v h, mul_zero, map_zero]; exact zero_le_one
  · rw [← mul_assoc, ← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]

private theorem cv_zu {u : (Af ℚ)ˣ} (h : ∀ v : Pl ℚ, Valued.v (pLoc ℚ v u) = 1) : IsZU u := by
  refine ⟨cv_mem.2 fun v => (h v).le, cv_mem.2 fun v => ?_⟩
  rw [map_units_inv, map_inv₀, h v, inv_one]

private theorem cv_same (w : Pl ℚ) (x : w.adicCompletion ℚ) : pLoc ℚ w (finiteSingle ℚ w x) = x := by
  classical
  exact Pi.mulSingle_eq_same (M := fun v : Pl ℚ => v.adicCompletion ℚ) w x

private theorem cv_other {v w : Pl ℚ} (h : v ≠ w) (x : w.adicCompletion ℚ) : pLoc ℚ v (finiteSingle ℚ w x) = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne (M := fun v : Pl ℚ => v.adicCompletion ℚ) h x

private theorem cv_loc (w : Pl ℚ) (x : (w.adicCompletion ℚ)ˣ) :
    finId ℚ (Units.map (finiteSingle ℚ w) x) = localIdele ℚ w x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing ℚ) - 0 + 0 = 1
    simp
  · change (1 : Af ℚ) - 1 + finiteSingle ℚ w x = finiteSingle ℚ w x
    simp

private theorem cv_split (x : Ideles ℚ) :
    TR.infId ℚ (Units.map (TR.pInf ℚ).toMonoidHom x) * finId ℚ (Units.map (pFin ℚ).toMonoidHom x) = x := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  have h2 : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  have h3 : ∀ x, pFin ℚ (TR.sInf ℚ x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin ℚ (sFin ℚ x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h, h2]
  · change pFin ℚ ((1 - TR.sInf ℚ 1 + TR.sInf ℚ (TR.pInf ℚ x.val)) * (1 - sFin ℚ 1 + sFin ℚ (pFin ℚ x.val))) = _
    simp [h3, h4]

private theorem cv_rat {M : ℕ} {χ : DirichletCharacter ℂ M} {ω : HChar ℚ} (h : IsDirOf χ ω) (r : ℚˣ) (hr : 0 < (r : ℚ)) :
    ω.1 (finId ℚ (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r)) = 1 := by
  have h1 := ω.2.2 r
  rw [← cv_split (diagUnits ℚ r), map_mul, h.pos _ fun v => ?_, one_mul] at h1
  · exact h1
  · have e := eq_ratCast ((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).comp
      ((TR.pInf ℚ).comp (algebraMap ℚ (Ad ℚ)))) (r : ℚ)
    exact lt_of_lt_of_eq (Rat.cast_pos.2 hr) e.symm

theorem UpperTheory.V.Af.Nf.charVal :
    UpperTheory.V.Af.Nf.CharVal := by
  intro M hM χ ω h
  haveI : NeZero M := ⟨by omega⟩
  refine ⟨isOfFinOrder_iff_pow_eq_one.2 ⟨2 * Fintype.card (ZMod M)ˣ, by positivity, Subtype.ext (MonoidHom.ext fun z => ?_)⟩,
    fun w hw => ?_⟩
  · change ω.1 z ^ (2 * Fintype.card (ZMod M)ˣ) = 1
    obtain ⟨r, u, hr, hu, e⟩ := ratAd.1 (Units.map (pFin ℚ).toMonoidHom z)
    obtain ⟨d, hd⟩ := ratAd.2.1 M hM _ hu.1
    have h1 := h.unit u hu d hd
    have h2 : IsUnit (d : ZMod M) := by
      by_contra hn
      rw [χ.map_nonunit hn, mul_zero] at h1
      exact zero_ne_one h1
    obtain ⟨c, hc⟩ := h2
    have h3 : ω.1 (finId ℚ u) ^ Fintype.card (ZMod M)ˣ = 1 := by
      have := congrArg (· ^ Fintype.card (ZMod M)ˣ) h1
      simp only [mul_pow, one_pow] at this
      rw [← hc, ← map_pow, ← Units.val_pow_eq_pow_val c, pow_card_eq_one, Units.val_one, map_one, mul_one] at this
      exact Units.ext this
    have h4 : ∀ t, ω.1 (TR.infId ℚ t) ^ 2 = 1 := fun t => by
      rw [← map_pow, ← map_pow]
      exact h.pos _ fun v => by
        rw [Units.val_pow_eq_pow_val, Pi.pow_apply]
        exact sq_pos_of_ne_zero (by simpa using (Units.map (Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) v).toMonoidHom t).ne_zero)
    rw [← cv_split z, e, map_mul, map_mul, map_mul, cv_rat h r hr, one_mul, mul_pow, pow_mul, h4, one_pow, one_mul,
      mul_comm 2, pow_mul, h3, one_pow]
  · have hun : ω.UnrAt w := fun x hx => by
      have h1 := h.unit (Units.map (finiteSingle ℚ w) x) (cv_zu fun v => ?_) 1 (cv_div hM hw (fun v hv => ?_) ?_)
      · rw [cv_loc, Int.cast_one, map_one, mul_one] at h1
        exact Units.ext h1
      · by_cases hv : v = w
        · subst hv; exact (congrArg _ (cv_same v x)).trans hx
        · exact (congrArg _ (cv_other hv x)).trans (map_one _)
      · rw [map_sub, Units.coe_map, cv_other hv, Int.cast_one, map_one, sub_self]
      · rw [map_sub, Units.coe_map, cv_same, Int.cast_one, map_one]
        exact (Valuation.map_sub _ _ _).trans (max_le (le_of_eq hx) (map_one _).le)
    let p : ℚˣ := Units.mk0 ((normV w : ℕ) : ℚ) (by exact_mod_cast (places w).1.ne_zero)
    have hp : 0 < (p : ℚ) := by
      change 0 < ((normV w : ℕ) : ℚ)
      exact_mod_cast (places w).1.pos
    have hU : IsUnifAt w (atFin w p) := (cv_val w p).trans (cv_unif w)
    let u : (Af ℚ)ˣ := Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom p * Units.map (finiteSingle ℚ w) (atFin w p)⁻¹
    have u1 : pLoc ℚ w u = 1 := by
      rw [Units.val_mul, map_mul, Units.coe_map (finiteSingle ℚ w), cv_same]
      exact (atFin w p).mul_inv
    have u2 : ∀ v, v ≠ w → pLoc ℚ v u = pLoc ℚ v (algebraMap ℚ (Af ℚ) p) := fun v hv => by
      rw [Units.val_mul, map_mul, Units.coe_map (finiteSingle ℚ w), cv_other hv, mul_one]
      rfl
    have e : (((normV w : ℕ) : ℤ) : Af ℚ) = algebraMap ℚ (Af ℚ) p := by
      rw [Int.cast_natCast]; exact (map_natCast _ _).symm
    have h1 := h.unit u (cv_zu fun v => ?_) (normV w : ℕ) (cv_div hM hw (fun v hv => ?_) ?_)
    · rw [map_mul, map_mul, cv_rat h p hp, one_mul, cv_loc, map_inv, map_inv, Int.cast_natCast, Units.val_inv_eq_inv_val,
        inv_mul_eq_one₀ (Units.ne_zero _)] at h1
      rw [← ω.val_eq hun _ hU]
      exact h1
    · by_cases hv : v = w
      · subst hv; rw [u1, map_one]
      · rw [u2 v hv, cv_val]; exact cv_ne hv
    · rw [map_sub, u2 v hv, e, sub_self]
    · rw [map_sub, u1, e]
      refine (Valuation.map_sub _ _ _).trans (max_le (map_one _).le ?_)
      rw [cv_val]
      exact (cv_nat w _).trans_le (w.intValuation_le_one _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep

namespace UpperTheory.V.Af.Nf

private theorem dc_inv {M : ℕ} (hM : 1 ≤ M) : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1 := by
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]

private theorem dc_uniq {M : ℕ} (hM : 1 ≤ M) {x : Af ℚ} {d e : ℤ} (hd : ∃ y ∈ Ohat ℚ, x - d = M * y)
    (he : ∃ y ∈ Ohat ℚ, x - e = M * y) : (d : ZMod M) = e := by
  obtain ⟨y, hy, hd⟩ := hd
  obtain ⟨z, hz, he⟩ := he
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z := by
    rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * dc_inv hM
  obtain ⟨n, hn⟩ := ratAd.2.2 _ (h1 ▸ sub_mem hy hz)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨n, ?_⟩
  rw [inv_mul_eq_iff_eq_mul₀ hM'] at hn
  exact_mod_cast hn

private theorem dc_red {M : ℕ} (hM : 1 ≤ M) : ∃ ρ : ↥(Ohat ℚ) →* ZMod M,
    ∀ (x : ↥(Ohat ℚ)) (d : ℤ), (∃ y ∈ Ohat ℚ, (x : Af ℚ) - d = M * y) → ρ x = d := by
  choose f hf using fun x : ↥(Ohat ℚ) => ratAd.2.1 M hM x x.2
  refine ⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d h => dc_uniq hM (hf x) h⟩
  · have := dc_uniq hM (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩
    simpa using this
  · obtain ⟨y, hy, h1⟩ := hf a
    obtain ⟨z, hz, h2⟩ := hf b
    have := dc_uniq hM (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y,
      add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by
        rw [Subring.coe_mul, Int.cast_mul]
        linear_combination (a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩
    simpa using this

private noncomputable abbrev pF : Ideles ℚ →* (Af ℚ)ˣ := Units.map (pFin ℚ).toMonoidHom

private noncomputable abbrev pR : Ideles ℚ →* ℝˣ := Units.map (ev.comp (TR.pInf ℚ)).toMonoidHom

private noncomputable abbrev dg : ℚˣ →* Ideles ℚ := Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom

private theorem pR_dg (r : ℚˣ) : (pR (dg r) : ℝ) = ((r : ℚ) : ℝ) :=
  eq_ratCast ((ev.comp (TR.pInf ℚ)).comp (algebraMap ℚ (Ad ℚ))) (r : ℚ)

private theorem pF_dg (r : ℚˣ) : pF (dg r) = Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r := Units.ext rfl

private theorem pF_inf (t : (TR.Rinf ℚ)ˣ) : pF (TR.infId ℚ t) = 1 := by
  refine Units.ext ?_
  change (1 : Af ℚ) - 0 + 0 = 1
  simp

private theorem pR_inf (t : (TR.Rinf ℚ)ˣ) : (pR (TR.infId ℚ t) : ℝ) = t.val Rat.infinitePlace := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  change ev (TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ t.val)) = ev t.val
  simp [h]

private theorem pF_fin (u : (Af ℚ)ˣ) : pF (finId ℚ u) = u := by
  refine Units.ext ?_
  change (1 : Af ℚ) - 1 + u = u
  simp

private theorem pR_fin (u : (Af ℚ)ˣ) : (pR (finId ℚ u) : ℝ) = 1 := by
  have h : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  change ev (TR.pInf ℚ (1 - sFin ℚ 1 + sFin ℚ u.val)) = 1
  simp [h]

private theorem zu_mul {u v : (Af ℚ)ˣ} (hu : IsZU u) (hv : IsZU v) : IsZU (u * v) :=
  ⟨mul_mem hu.1 hv.1, by rw [mul_inv]; exact mul_mem hu.2 hv.2⟩

private theorem zu_one : IsZU 1 := ⟨one_mem _, one_mem _⟩

private noncomputable def PU : Subgroup (Ideles ℚ) where
  carrier := {a | 0 < (pR a : ℝ) ∧ IsZU (pF a)}
  one_mem' := ⟨by rw [map_one]; exact one_pos, by rw [map_one]; exact zu_one⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul]; exact mul_pos ha.1 hb.1, by rw [map_mul]; exact zu_mul ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨by rw [map_inv, Units.val_inv_eq_inv_val]; exact inv_pos.2 ha.1,
    by rw [map_inv]; exact ⟨ha.2.2, ha.2.1⟩⟩

private theorem dc_ker (r : ℚˣ) (h : dg r ∈ PU) : r = 1 := by
  obtain ⟨h0, h1, h2⟩ := h
  rw [pR_dg, Rat.cast_pos] at h0
  obtain ⟨n, hn⟩ := ratAd.2.2 r h1
  obtain ⟨m, hm⟩ := ratAd.2.2 (r⁻¹ : ℚˣ) h2
  have e : n * m = 1 := by
    have := r.mul_inv
    rw [hn, hm] at this
    exact_mod_cast this
  rw [hn] at h0
  have := Int.eq_one_of_mul_eq_one_right (by exact_mod_cast h0.le) e
  exact Units.ext (by rw [hn, this]; rfl)

private theorem dc_surj : Function.Surjective (PU.subtype.coprod dg) := by
  intro a
  obtain ⟨r, u, hr, hu, e⟩ := ratAd.1 (pF a)
  have key : ∀ s : ℚˣ, s * s = 1 → IsZU (pF (dg s)) → 0 < ((s : ℚ) : ℝ) * pR a →
      ∃ p, PU.subtype.coprod dg p = a := fun s hs hz hp => by
    refine ⟨(⟨a * dg (s * r⁻¹), ?_, ?_⟩, s * r), ?_⟩
    · rw [map_mul, Units.val_mul, pR_dg, Units.val_mul, Rat.cast_mul, ← mul_assoc, mul_comm _ (((s : ℚ) : ℝ))]
      refine mul_pos hp ?_
      rw [Units.val_inv_eq_inv_val, Rat.cast_pos]
      exact inv_pos.2 hr
    · have : pF (a * dg (s * r⁻¹)) = u * pF (dg s) := by
        rw [map_mul, e, ← pF_dg, map_mul, map_mul, map_inv, map_inv, mul_comm _ u, mul_comm (pF (dg s)),
          mul_assoc, mul_inv_cancel_left]
      rw [this]
      exact zu_mul hu hz
    · change a * dg (s * r⁻¹) * dg (s * r) = a
      rw [mul_assoc, ← map_mul, mul_mul_mul_comm, hs, inv_mul_cancel, mul_one, map_one, mul_one]
  rcases lt_or_gt_of_ne (pR a).ne_zero with h | h
  · refine key (-1) (by simp) ?_ (by simpa using h)
    have : algebraMap ℚ (Af ℚ) (-1) ∈ Ohat ℚ := by rw [map_neg, map_one]; exact neg_mem (one_mem _)
    exact ⟨this, this⟩
  · exact key 1 (by simp) (by rw [map_one, map_one]; exact zu_one) (by simpa using h)

private theorem dc_nhds {M : ℕ} : ∀ᶠ a : Ideles ℚ in 𝓝 1, a ∈ PU ∧
    algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * ((pF a : Af ℚ) - (1 : ℤ)) ∈ Ohat ℚ := by
  have c1 : Continuous pF := Continuous.units_map _ continuous_snd
  have c2 : Continuous fun a => (pR a : ℝ) :=
    ((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).continuous.comp
      ((continuous_apply Rat.infinitePlace).comp continuous_fst)).comp Units.continuous_val
  have c3 : Continuous fun a => (pF a : Af ℚ) := Units.continuous_val.comp c1
  have c4 : Continuous fun a => (((pF a)⁻¹ : (Af ℚ)ˣ) : Af ℚ) := Units.continuous_coe_inv.comp c1
  have c5 : Continuous fun a => algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * ((pF a : Af ℚ) - (1 : ℤ)) :=
    continuous_const.mul (c3.sub continuous_const)
  have h2 : ∀ᶠ a : Ideles ℚ in 𝓝 1, 0 < (pR a : ℝ) := (isOpen_lt continuous_const c2).mem_nhds PU.one_mem.1
  have h3 := (isOpen_Ohat.preimage c3).mem_nhds (x := 1) PU.one_mem.2.1
  have h4 := (isOpen_Ohat.preimage c4).mem_nhds (x := 1) PU.one_mem.2.2
  have h5 := (isOpen_Ohat.preimage c5).mem_nhds (x := 1) (by
    rw [Set.mem_preimage, map_one, Units.val_one, Int.cast_one, sub_self, mul_zero]; exact zero_mem (Ohat ℚ))
  filter_upwards [h2, h3, h4, h5] with a a2 a3 a4 a5
  exact ⟨⟨a2, a3, a4⟩, a5⟩

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.dirChar :
    UpperTheory.V.Af.Nf.DirChar := by
  intro M hM χ
  obtain ⟨ρ, hρ⟩ := dc_red hM
  let j : ↥PU →* ↥(Ohat ℚ) :=
    { toFun := fun p => ⟨pF p, p.2.2.1⟩
      map_one' := Subtype.ext (congrArg Units.val (map_one pF))
      map_mul' := fun a b => Subtype.ext (congrArg Units.val (map_mul pF a.1 b.1)) }
  let ψ : ↥PU →* ℂˣ := (χ.toMonoidHom.comp (ρ.comp j)).toHomUnits
  let φ : ↥PU × ℚˣ →* ℂˣ := ψ⁻¹.comp (MonoidHom.fst _ _)
  have hker : (PU.subtype.coprod dg).ker ≤ φ.ker := fun p hp => by
    have h1 : (p.1 : Ideles ℚ) * dg p.2 = 1 := hp
    have h2 := dc_ker p.2 (by rw [eq_inv_of_mul_eq_one_right h1]; exact PU.inv_mem p.1.2)
    rw [h2, map_one, mul_one] at h1
    change ψ⁻¹ p.1 = 1
    rw [show p.1 = 1 from Subtype.ext h1, map_one]
  let ω : Ideles ℚ →* ℂˣ := MonoidHom.liftOfSurjective _ dc_surj ⟨φ, hker⟩
  have hω : ∀ p, ω (PU.subtype.coprod dg p) = φ p := fun p => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ p
  have hv : ∀ a (ha : a ∈ PU) (d : ℤ), (∃ y ∈ Ohat ℚ, (pF a : Af ℚ) - d = M * y) → (ω a : ℂ) * χ (d : ZMod M) = 1 := by
    intro a ha d hd
    have h1 : ω (a * dg 1) = (ψ ⟨a, ha⟩)⁻¹ := hω (⟨a, ha⟩, 1)
    rw [map_one, mul_one] at h1
    rw [h1, ← hρ (j ⟨a, ha⟩) d hd]
    exact (ψ ⟨a, ha⟩).inv_mul
  have hone : ∀ a (ha : a ∈ PU), (∃ y ∈ Ohat ℚ, (pF a : Af ℚ) - (1 : ℤ) = M * y) → ω a = 1 := fun a ha h => by
    have := hv a ha 1 h
    rw [Int.cast_one, map_one, mul_one] at this
    exact Units.ext this
  refine ⟨⟨ω, continuous_of_continuousAt_one ω ?_, fun k => ?_⟩, fun t ht => ?_, fun u hu d hd => ?_⟩
  · refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [dc_nhds (M := M)] with a ha
    exact (hone a ha.1 ⟨_, ha.2, by rw [← mul_assoc, mul_comm (M : Af ℚ), dc_inv hM, one_mul]⟩).symm
  · have h1 : ω (1 * dg k) = ψ⁻¹ 1 := hω (1, k)
    rw [map_one, one_mul] at h1
    exact h1
  · exact hone _ ⟨by rw [pR_inf]; exact ht _, by rw [pF_inf]; exact zu_one⟩
      ⟨0, zero_mem _, by rw [pF_inf]; simp⟩
  · exact hv _ ⟨by rw [pR_fin]; exact one_pos, by rw [pF_fin]; exact hu⟩ d (by rw [pF_fin]; exact hd)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KOpen
open NumberField GlobalTheory.CuspRep UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.kOpen :
    UpperTheory.V.Af.Nf.KOpen := by
  intro M hM
  refine ⟨Subgroup.isOpen_mono (H₁ := KLev ℚ 2 M) (fun g hg => ?_) (isOpen_KLev hM), fun u hu x hx => ?_⟩
  · obtain ⟨ha, hb, hc⟩ := mem_KLev.1 hg
    refine (memK M g).2 ⟨ha, hb, ?_, ?_⟩
    · simpa using hc 1 0
    · simpa using hc 1 1
  · refine (memK M _).2 ⟨?_, ?_, ⟨0, zero_mem _, ?_⟩, ⟨0, zero_mem _, ?_⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.1, hx⟩, Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨hu.2, neg_mem (mul_mem hu.2 hx)⟩,
        Fin.forall_fin_two.2 ⟨zero_mem _, one_mem _⟩⟩
    · exact (mul_zero _).symm
    · exact (sub_self (1 : Af ℚ)).trans (mul_zero _).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.HkCoef
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Sd

private theorem le_asIdeal_of_normV_dvd_absNorm (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h𝔪 : 𝔪 ≠ ⊥)
    (hd : normV w ∣ Ideal.absNorm 𝔪) : 𝔪 ≤ w.asIdeal := by
  obtain ⟨hp, hspan, -, -⟩ := UpperTheory.V.Af.Nf.places w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  by_contra h
  have htop : w.asIdeal ⊔ 𝔪 = ⊤ := by
    by_contra hne
    exact h (le_sup_right.trans ((w.isMaximal.eq_of_le hne le_sup_left).symm.le))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : 𝓞 ℚ) ∈ w.asIdeal ⊔ 𝔪)
  have hne : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd hne
  haveI : Finite (𝓞 ℚ ⧸ 𝔪) := Nat.finite_of_card_ne_zero hne
  obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 ℚ ⧸ 𝔪) (normV w) hd
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hpx : ((normV w : ℕ) : 𝓞 ℚ) * x ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast, ← nsmul_eq_mul, ← hy]
    exact addOrderOf_nsmul_eq_zero _
  have hx : x ∈ 𝔪 := by
    rw [hspan, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have : x = c * (((normV w : ℕ) : 𝓞 ℚ) * x) + b * x := by
      rw [← mul_assoc, mul_comm c, ← add_mul, hab, one_mul]
    rw [this]
    exact 𝔪.add_mem (𝔪.mul_mem_left _ hpx) (𝔪.mul_mem_right _ hb)
  have h0 : (Ideal.Quotient.mk 𝔪 x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [h0, addOrderOf_zero] at hy
  exact hp.one_lt.ne hy

private theorem coefDiv_icoef_eq_ite_dvd (g : UpperHalfPlane → ℂ) (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h𝔪 : 𝔪 ≠ ⊥) :
    coefDiv (UpperTheory.V.Af.Nf.icoef g) w.asIdeal 𝔪 =
      if normV w ∣ Ideal.absNorm 𝔪 then UpperTheory.V.Af.coef g (Ideal.absNorm 𝔪 / normV w) else 0 := by
  obtain ⟨hp, -, hnorm, -⟩ := UpperTheory.V.Af.Nf.places w
  unfold coefDiv
  split_ifs with h1 h2 h2
  · have hc := h1.choose_spec
    have habs : Ideal.absNorm 𝔪 = normV w * Ideal.absNorm h1.choose := by
      conv_lhs => rw [hc]
      rw [map_mul, hnorm]
    simp only [UpperTheory.V.Af.Nf.icoef]
    rw [habs, Nat.mul_div_cancel_left _ hp.pos]
  · exfalso
    apply h2
    obtain ⟨n, hn⟩ := h1
    rw [hn, map_mul, hnorm]
    exact dvd_mul_right _ _
  · exfalso
    exact h1 (Ideal.dvd_iff_le.mpr (le_asIdeal_of_normV_dvd_absNorm w 𝔪 h𝔪 h2))
  · rfl

private theorem chiI_eq_of_conductor_eq_zero (ω : Formalism.L2.Host.HChar ℚ) (c : Pl ℚ → ℕ) (w : Pl ℚ) (hc : c w = 0) :
    chiI ω c w.asIdeal = ↑(ω.val w) := by
  classical
  have hirr : ∀ v : Pl ℚ, Irreducible (Associates.mk v.asIdeal) :=
    fun v => Associates.irreducible_mk.mpr v.irreducible
  unfold chiI
  rw [finprod_eq_single _ w]
  · simp only [hc, if_true]
    unfold ordI
    rw [Associates.count_self (hirr w), pow_one]
  · intro v hv
    unfold ordI
    rw [Associates.count_eq_zero_of_ne (hirr v) (hirr w), pow_zero]
    intro he
    apply hv
    rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at he
    exact HeightOneSpectrum.ext he

theorem UpperTheory.V.Af.Nf.hkCoef :
    UpperTheory.V.Af.Nf.HkCoef := by
  intro k f ω w hw hω 𝔪 h𝔪
  obtain ⟨hp, -, hnorm, hlev⟩ := UpperTheory.V.Af.Nf.places w
  have hl : UpperTheory.V.Af.Nf.lev f.M w = 0 := hlev f.M f.pos hw
  have hn : 1 ≤ Ideal.absNorm 𝔪 := Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have heig := f.eig (normV w) hp hw (Ideal.absNorm 𝔪) hn
  unfold UpperTheory.V.Sd.hkCoef
  rw [chiI_eq_of_conductor_eq_zero ω _ w hl, coefDiv_icoef_eq_ite_dvd _ w 𝔪 h𝔪, hω]
  simp only [UpperTheory.V.Af.Nf.icoef, map_mul, hnorm, UpperTheory.V.Af.Newform.a]
  exact heig
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SmCont
theorem UpperTheory.V.Af.Nf.smCont :
    UpperTheory.V.Af.Nf.SmCont :=
  UpperTheory.eisenstein_smooth_continuous
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslInv
open CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

private def cj (δ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![δ 0 0, -δ 0 1; -δ 1 0, δ 1 1], by
    have h := δ.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

private theorem eps_mul_cj (δ : SL(2, ℤ)) :
    eps * δ.1.map (Int.cast : ℤ → ℝ) = (cj δ).1.map (Int.cast : ℤ → ℝ) * eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, cj, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_map (δ : SL(2, ℤ)) : (δ.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  have h := (Int.castRingHom ℝ).map_det δ.1
  rw [δ.det_coe, map_one] at h
  have h' : (δ.1.map (Int.cast : ℤ → ℝ)).det = 1 := h.symm
  rw [h']
  exact one_ne_zero

private theorem pos_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < x.det) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) : nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rw [← (nslMul k f).1 _ x (det_map δ) hx, (nslSl k f).1 δ, h, (nslMul k f).2.2.2]

private theorem gen_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) (h' : f ∣[(k : ℤ)] (cj δ) = c • f) :
    nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hd : 0 < (eps * x).det := by
      rw [Matrix.det_mul]
      have : eps.det = -1 := by simp [eps]
      rw [this]
      linarith
    rw [← (nslMul k f).2.1, ← Matrix.mul_assoc, eps_mul_cj, Matrix.mul_assoc, pos_case k f _ hd _ c h',
      (nslMul k f).2.1]
  · exact pos_case k f x hpos δ c h

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.nslInv :
    UpperTheory.V.Af.Nf.NslInv := by
  intro k M f x hx
  refine ⟨fun hf δ hδ => ?_, fun χ hχ δ hδ => ?_⟩
  · have hδ' : cj δ ∈ Gamma1 M := by
      rw [Gamma1_mem] at hδ ⊢
      obtain ⟨h1, h2, h3⟩ := hδ
      refine ⟨?_, ?_, ?_⟩
      · exact h1
      · exact h2
      · show (((-δ 1 0 : ℤ)) : ZMod M) = 0
        rw [Int.cast_neg, h3, neg_zero]
    have := gen_case k f x hx δ 1 (by rw [one_smul]; exact hf δ hδ) (by rw [one_smul]; exact hf _ hδ')
    rwa [one_smul] at this
  · have hδ' : cj δ ∈ Gamma0 M := by
      rw [Gamma0_mem] at hδ ⊢
      show (((-δ 1 0 : ℤ)) : ZMod M) = 0
      rw [Int.cast_neg, hδ, neg_zero]
    exact gen_case k f x hx δ _ (hχ δ hδ) (hχ _ hδ')
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DvdOfOhat
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open scoped Matrix MatrixGroups

namespace UpperTheory.V.Af.Nf

private theorem dvd_of_ohat {M : ℕ} (hM : 1 ≤ M) (n : ℤ) {y : Af ℚ} (hy : y ∈ Ohat ℚ)
    (h : (n : Af ℚ) = M * y) : (M : ℤ) ∣ n := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have e : algebraMap ℚ (Af ℚ) ((n : ℚ) / M) = y := by
    have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹) * (M : Af ℚ) = 1 := by
      rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]
    rw [div_eq_inv_mul, map_mul, map_intCast, h, ← mul_assoc, h1, one_mul]
  obtain ⟨m, hm⟩ := ratAd.2.2 _ (e ▸ hy)
  refine ⟨m, ?_⟩
  have : (n : ℚ) = M * m := by rw [← hm]; field_simp
  exact_mod_cast this

private theorem part1 {M : ℕ} (hM : 1 ≤ M) (γ : GL (Fin 2) ℚ) (hγ : toF γ ∈ K1G M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      ((toR γ).val = δ.1.map (Int.cast : ℤ → ℝ) ∨ (toR γ).val = eps * δ.1.map (Int.cast : ℤ → ℝ)) := by
  obtain ⟨h1, h2, ⟨y, hy, h3⟩, z, hz, h4⟩ := (memK M _).1 hγ
  rw [← map_inv] at h2
  choose A hA using fun a b => ratAd.2.2 (γ a b) (h1 a b)
  choose B hB using fun a b => ratAd.2.2 ((γ⁻¹ : GL (Fin 2) ℚ) a b) (h2 a b)
  have hA' : γ.val = (Matrix.of A).map (Int.castRingHom ℚ) := Matrix.ext hA
  have hB' : (γ⁻¹).val = (Matrix.of B).map (Int.castRingHom ℚ) := Matrix.ext hB
  have hdet : (Matrix.of A).det * (Matrix.of B).det = 1 := by
    have : γ.val.det * (γ⁻¹).val.det = 1 := by rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rw [hA', hB', ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det] at this
    simp only [eq_intCast] at this
    exact_mod_cast this
  have hc : (M : ℤ) ∣ A 1 0 := by
    refine dvd_of_ohat hM _ hy ?_
    rw [← h3, ← map_intCast (algebraMap ℚ (Af ℚ)), ← hA]; rfl
  have hd : (M : ℤ) ∣ A 1 1 - 1 := by
    refine dvd_of_ohat hM _ hz ?_
    rw [← h4, Int.cast_sub, Int.cast_one, ← map_intCast (algebraMap ℚ (Af ℚ)), ← hA]; rfl
  have hc' : ((A 1 0 : ℤ) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hc
  have hd' : ((A 1 1 : ℤ) : ZMod M) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    push_cast at this
    exact sub_eq_zero.1 this
  have hR : ∀ a b, (toR γ).val a b = (A a b : ℝ) := fun a b => by
    show Rat.castHom ℝ (γ a b) = _
    rw [hA]; simp
  have key : ∀ δ : SL(2, ℤ), δ 1 0 = A 1 0 → δ 1 1 = A 1 1 → δ ∈ Gamma1 M := by
    intro δ e1 e2
    rw [Gamma1_mem, e1, e2]
    refine ⟨?_, hd', hc'⟩
    have := congrArg (Int.cast : ℤ → ZMod M) δ.det_coe
    rw [Matrix.det_fin_two] at this
    push_cast at this
    change ((δ 0 0 : ℤ) : ZMod M) * (δ 1 1 : ℤ) - (δ 0 1 : ℤ) * (δ 1 0 : ℤ) = 1 at this
    rw [e1, e2, hc', hd'] at this
    simpa using this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
  · refine ⟨⟨Matrix.of A, h⟩, key _ rfl rfl, Or.inl (Matrix.ext hR)⟩
  · refine ⟨⟨!![-A 0 0, -A 0 1; A 1 0, A 1 1], ?_⟩, key _ rfl rfl, Or.inr ?_⟩
    · rw [Matrix.det_fin_two] at h
      simp only [Matrix.of_apply] at h
      rw [Matrix.det_fin_two_of]; linear_combination -h
    · ext a b
      rw [hR]
      fin_cases a <;> fin_cases b <;> simp [eps, Matrix.mul_apply, Fin.sum_univ_two]

private theorem part2 {M : ℕ} (hM : 1 ≤ M) (u : (Af ℚ)ˣ) (hu : IsZU u) :
    ∃ (δ : SL(2, ℤ)) (γ : GL (Fin 2) ℚ), δ ∈ Gamma0 M ∧ γ.val = δ.1.map (Int.cast : ℤ → ℚ) ∧
      (toF γ)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ K1G M ∧
      ∃ y ∈ Ohat ℚ, (u : Af ℚ) - (δ 1 1 : ℤ) = M * y := by
  obtain ⟨d, y, hy, hd⟩ := ratAd.2.1 M hM _ hu.1
  obtain ⟨e, z, hz, he⟩ := ratAd.2.1 M hM _ hu.2
  have hI : ∀ n : ℤ, (n : Af ℚ) ∈ Ohat ℚ := fun n => intCast_mem _ n
  have huu : (u : Af ℚ) * (u⁻¹ : (Af ℚ)ˣ) = 1 := u.mul_inv
  obtain ⟨t, ht⟩ : (M : ℤ) ∣ e * d - 1 := by
    refine dvd_of_ohat hM _ (y := -(z * u + e * y)) (neg_mem (add_mem (mul_mem hz hu.1) (mul_mem (hI e) hy))) ?_
    push_cast
    linear_combination (-(u : Af ℚ)) * he - (e : Af ℚ) * hd + huu
  let δ : SL(2, ℤ) := ⟨!![e, t; M, d], by rw [Matrix.det_fin_two_of]; linear_combination ht⟩
  have hδ : ∀ (δ : SL(2, ℤ)) a b, (toF (Matrix.SpecialLinearGroup.mapGL ℚ δ)).val a b = ((δ a b : ℤ) : Af ℚ) := by
    intro δ a b
    show algebraMap ℚ (Af ℚ) (algebraMap ℤ ℚ (δ a b)) = _
    simp
  have e1 : ∀ a b, ((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u).val a b
      = (((δ⁻¹ : SL(2, ℤ)) a b : ℤ) : Af ℚ) * u := by
    intro a b
    rw [← map_inv, ← map_inv, Units.val_mul, ← hδ]
    simp
  have e2 : ∀ a b, (((toF (Matrix.SpecialLinearGroup.mapGL ℚ δ))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹).val a b
      = (u⁻¹ : (Af ℚ)ˣ) * ((δ a b : ℤ) : Af ℚ) := by
    intro a b
    rw [mul_inv_rev, inv_inv, ← map_inv, Units.val_mul, ← hδ]
    generalize u⁻¹ = v
    simp
  have i10 : (δ⁻¹ : SL(2, ℤ)) 1 0 = -M := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  have i11 : (δ⁻¹ : SL(2, ℤ)) 1 1 = e := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
  refine ⟨δ, Matrix.SpecialLinearGroup.mapGL ℚ δ, ?_, rfl, (memK M _).2 ⟨fun a b => ?_, fun a b => ?_, ⟨-u, neg_mem hu.1, ?_⟩,
    -(z * u), neg_mem (mul_mem hz hu.1), ?_⟩, y, hy, hd⟩
  · rw [Gamma0_mem]; simp [δ]
  · rw [e1]; exact mul_mem (hI _) hu.1
  · rw [e2]; exact mul_mem hu.2 (hI _)
  · rw [e1, i10]; push_cast; ring
  · rw [e1, i11]; linear_combination (-(u : Af ℚ)) * he + huu

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.ratK :
    UpperTheory.V.Af.Nf.RatK := fun _ hM =>
  ⟨fun γ hγ => UpperTheory.V.Af.Nf.part1 hM γ hγ, fun u hu => UpperTheory.V.Af.Nf.part2 hM u hu⟩
end
