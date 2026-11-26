module

public import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
public import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzNormV
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Filter Topology

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [hg : Fact g.Prime]

theorem val_lt_one_of_norm_lt_one (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (u : ℚ_[g])
    (hu : ‖u‖ < 1) : Valued.v (i u) < 1 := by
  have := DiscreteGroups.sglob.DzIso.norm_lt_of_lt i hi hu
  rwa [Valued.toNormedField.norm_lt_one_iff] at this

theorem mem_of_val_lt_one (y : 𝓞 E) (h : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) < 1) :
    y ∈ w.asIdeal := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rwa [e] at h

theorem val_le_one_int (y : 𝓞 E) : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≤ 1 := by
  have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
  rw [e]
  exact w.valuation_le_one y

theorem alg_sub_natCast (y : 𝓞 E) (a : ℕ) : algebraMap E (w.adicCompletion E) (((y - (a : 𝓞 E) : 𝓞 E)) : E) =
    algebraMap E (w.adicCompletion E) (y : E) - (a : w.adicCompletion E) := by
  simp

theorem alg_natCast (a : ℕ) : algebraMap E (w.adicCompletion E) (((a : 𝓞 E)) : E) = (a : w.adicCompletion E) := by
  simp

theorem normV_eq_of_padic (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : normV w = g := by
  classical
  have hres : ∀ y : 𝓞 E, ∃ a : ℕ, y - (a : 𝓞 E) ∈ w.asIdeal := by
    intro y
    set x := i.symm (algebraMap E (w.adicCompletion E) (y : E)) with hx
    have hxy : i x = algebraMap E (w.adicCompletion E) (y : E) := by rw [hx, RingEquiv.apply_symm_apply]
    have hxn : ‖x‖ ≤ 1 := by
      by_contra hc
      push Not at hc
      have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact absurd hc (by norm_num)
      have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
      have h2 := val_lt_one_of_norm_lt_one w g i hi _ h1
      rw [map_inv₀, hxy, map_inv₀] at h2
      have h3 := val_le_one_int w y
      have hy0 : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) ≠ 0 := by
        intro h0
        rw [h0, inv_zero] at h2
        have : i x ≠ 0 := (map_ne_zero i).mpr hx0
        rw [hxy] at this
        exact this ((Valuation.zero_iff _).mp h0)
      have h4 : 1 ≤ (Valued.v (algebraMap E (w.adicCompletion E) (y : E)))⁻¹ := one_le_inv₀ (zero_lt_iff.mpr hy0) |>.mpr h3
      exact absurd h2 (not_lt.mpr h4)
    let xz : ℤ_[g] := ⟨x, hxn⟩
    obtain ⟨a, -, ha⟩ := PadicInt.exists_mem_range xz
    refine ⟨a, mem_of_val_lt_one w _ ?_⟩
    have h5 : ‖x - a‖ < 1 := by
      have h := (PadicInt.mem_nonunits).mp ha
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h
      exact h
    have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
    rw [map_sub, hxy, map_natCast] at h6
    rw [alg_sub_natCast]
    exact h6
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    apply mem_of_val_lt_one w
    have := val_lt_one_of_norm_lt_one w g i hi (g : ℚ_[g]) Padic.norm_p_lt_one
    rw [map_natCast] at this
    rw [alg_natCast]
    exact this
  haveI : w.asIdeal.IsPrime := w.isPrime
  have hgQ : ((g : ℕ) : 𝓞 E ⧸ w.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hgw
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := (CharP.charP_iff_prime_eq_zero hg.out).mpr hgQ
  let f : ZMod g →+* 𝓞 E ⧸ w.asIdeal := ZMod.castHom (dvd_refl g) _
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := hres y
    refine ⟨(a : ZMod g), ?_⟩
    rw [ZMod.castHom_apply, ZMod.cast_natCast (dvd_refl g), ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact ha
  unfold normV
  rw [← Nat.card_congr (RingEquiv.ofBijective f ⟨hinj, hsurj⟩).toEquiv, Nat.card_zmod]

end DiscreteGroups.sglob.DzType

end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.StepData

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

theorem exists_int_lift {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ_[g]) (h : ∀ a b, ‖M a b‖ ≤ 1) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ_[g], (algebraMap ℤ_[g] ℚ_[g]).mapMatrix A = M :=
  ⟨fun a b => ⟨M a b, h a b⟩, by ext a b; rfl⟩

theorem mapMatrix_int_injective {n : ℕ} :
    Function.Injective ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix : Matrix (Fin n) (Fin n) ℤ_[g] → _) :=
  fun _ _ h => Matrix.ext fun a b => PadicInt.ext (congrFun (congrFun h a) b)

include hi

theorem mem_integer_iff (x : ℚ_[g]) : i x ∈ 𝒪[w.adicCompletion E] ↔ ‖x‖ ≤ 1 :=
  (Valuation.mem_integer_iff _ _).trans (valuation_le_iff i hi x)

theorem map_inc_mem_KO {n : ℕ} (k : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) ∈ KO (w.adicCompletion E) (Fin n) := by
  rw [mem_KO]
  refine ⟨fun a b => (mem_integer_iff i hi _).2 (k.val a b).2, fun a b => ?_⟩
  rw [← map_inv, ← map_inv]
  exact (mem_integer_iff i hi _).2 ((k⁻¹).val a b).2

theorem exists_of_mem_KO {n : ℕ} {m : GL (Fin n) (w.adicCompletion E)} (hm : m ∈ KO (w.adicCompletion E) (Fin n)) :
    ∃ k : GL (Fin n) ℤ_[g], Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) = m := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hm
  have hint : ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E), IntM M →
      ∀ a b, ‖i.symm.toRingHom.mapMatrix M a b‖ ≤ 1 := by
    intro M hM a b
    rw [← norm_le_iff i hi]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    exact (val_le_iff _).1 ((Valuation.mem_integer_iff _ _).1 (hM a b))
  obtain ⟨A, hA⟩ := exists_int_lift _ (hint _ h1)
  obtain ⟨B, hB⟩ := exists_int_lift _ (hint _ h2)
  have hAB : A * B = 1 := mapMatrix_int_injective (by rw [map_mul, hA, hB, ← map_mul, Units.mul_inv, map_one, map_one])
  have hBA : B * A = 1 := mapMatrix_int_injective (by rw [map_mul, hA, hB, ← map_mul, Units.inv_mul, map_one, map_one])
  refine ⟨⟨A, B, hAB, hBA⟩, Units.ext (Matrix.ext fun a b => ?_)⟩
  change i ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix A a b) = m.val a b
  rw [hA]
  simp

def toKO (n : ℕ) : GL (Fin n) ℤ_[g] →* KO (w.adicCompletion E) (Fin n) :=
  ((Matrix.GeneralLinearGroup.map i.toRingHom).comp (inc g n)).codRestrict _ fun k => map_inc_mem_KO i hi k

theorem coe_toKO (n : ℕ) (k : GL (Fin n) ℤ_[g]) :
    ((toKO i hi n k : KO (w.adicCompletion E) (Fin n)) : GL (Fin n) (w.adicCompletion E)) =
      Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) := rfl

theorem toKO_injective (n : ℕ) : Function.Injective (toKO i hi n) := by
  intro k k' h
  have h' := congrArg (fun x : KO (w.adicCompletion E) (Fin n) =>
    ((x : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) h
  refine Units.ext (Matrix.ext fun a b => PadicInt.ext (i.injective ?_))
  exact congrFun (congrFun h' a) b

theorem toKO_surjective (n : ℕ) : Function.Surjective (toKO i hi n) := by
  intro m
  obtain ⟨k, hk⟩ := exists_of_mem_KO i hi m.2
  exact ⟨k, Subtype.ext hk⟩

def equivKO (n : ℕ) : GL (Fin n) ℤ_[g] ≃* KO (w.adicCompletion E) (Fin n) :=
  MulEquiv.ofBijective (toKO i hi n) ⟨toKO_injective i hi n, toKO_surjective i hi n⟩

def redKO (n : ℕ) : KO (w.adicCompletion E) (Fin n) →* Gn g n :=
  (red g n).comp (equivKO i hi n).symm.toMonoidHom

theorem redKO_toKO (n : ℕ) (k : GL (Fin n) ℤ_[g]) : redKO i hi n (toKO i hi n k) = red g n k := by
  show red g n ((equivKO i hi n).symm (equivKO i hi n k)) = red g n k
  rw [MulEquiv.symm_apply_apply]

theorem redKO_surjective (n : ℕ) : Function.Surjective (redKO i hi n) :=
  (GlobalTheory.GLp.Model.red_surjective n).comp (equivKO i hi n).symm.surjective

theorem ker_redKO (n : ℕ) :
    (redKO i hi n).ker = (KOne (w.adicCompletion E) (Fin n)).subgroupOf (KO (w.adicCompletion E) (Fin n)) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨k, rfl⟩ := toKO_surjective i hi n m
  rw [redKO_toKO, coe_toKO]
  constructor
  · intro hk
    exact map_mem_KOne i hi k hk
  · intro hm
    obtain ⟨k', hk', he⟩ := exists_of_mem_KOne i hi hm
    have : k' = k := toKO_injective i hi n (Subtype.ext he)
    rw [← this]
    exact hk'

end DiscreteGroups.sglob.DzIso
end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzApprox
open IsDedekindDomain NumberField

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem exists_int_approx (e : E) (he : w.valuation E e ≤ 1) :
    ∃ x : 𝓞 E, w.valuation E (e - algebraMap (𝓞 E) E x) < 1 := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) e
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbE : algebraMap (𝓞 E) E b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hν0 : w.intValuation b ≠ 0 := w.intValuation_ne_zero b hb0
  set m : ℕ := (-(w.intValuation b).log).toNat with hm
  have hνm : w.intValuation b = WithZero.exp (-(m : ℤ)) := by
    have hlog : (w.intValuation b).log ≤ 0 := by
      have h1 : WithZero.exp (w.intValuation b).log ≤ WithZero.exp 0 := by
        rw [WithZero.exp_log hν0, WithZero.exp_zero]; exact w.intValuation_le_one b
      exact WithZero.exp_le_exp.mp h1
    rw [hm, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hν0]
  have hbm : b ∈ w.asIdeal ^ m := (w.intValuation_le_pow_iff_mem b m).mp hνm.le
  have hbm1 : b ∉ w.asIdeal ^ (m + 1) := by
    intro h
    have h2 := (w.intValuation_le_pow_iff_mem b (m + 1)).mpr h
    rw [hνm, WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  have hva : w.intValuation a ≤ w.intValuation b := by
    have h1 : w.valuation E (algebraMap (𝓞 E) E a) =
        w.valuation E (algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b) * w.valuation E (algebraMap (𝓞 E) E b) := by
      rw [← map_mul, div_mul_cancel₀ _ hbE]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap] at h1
    rw [h1]
    exact mul_le_of_le_one_left' he
  have ham : a ∈ w.asIdeal ^ m := (w.intValuation_le_pow_iff_mem a m).mp (hva.trans hνm.le)
  obtain ⟨B, hB⟩ : w.asIdeal ^ m ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hbm)
  have hBw : ¬ B ≤ w.asIdeal := by
    intro hle
    apply hbm1
    have : Ideal.span {b} ≤ w.asIdeal ^ (m + 1) := by
      rw [hB, pow_succ]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).mp this
  obtain ⟨s, hsB, hsw⟩ := SetLike.not_le_iff_exists.mp hBw
  have hsa : s * a ∈ Ideal.span {b} := by
    rw [hB, mul_comm s a]; exact Ideal.mul_mem_mul ham hsB
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hsa
  haveI := w.isMaximal
  have hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨s'', hs''⟩ := Ideal.Quotient.exists_inv hs0
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s''
  have hss : s * s' - 1 ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hs'', map_one, sub_self]
  have hsne : s ≠ 0 := fun h => hsw (h ▸ w.asIdeal.zero_mem)
  have hsE : algebraMap (𝓞 E) E s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]; exact hsne
  refine ⟨c * s', ?_⟩
  have hcE : algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E a := by
    rw [← map_mul, ← map_mul, hc]
  have hab : algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E c / algebraMap (𝓞 E) E s := by
    rw [div_eq_div_iff hbE hsE]; linear_combination (-1 : E) * hcE
  have e1 : algebraMap (𝓞 E) E a / algebraMap (𝓞 E) E b - algebraMap (𝓞 E) E (c * s') =
      algebraMap (𝓞 E) E c * (-algebraMap (𝓞 E) E (s * s' - 1)) / algebraMap (𝓞 E) E s := by
    rw [hab]
    simp only [map_mul, map_sub, map_one]
    field_simp
    ring
  have hs1 : w.intValuation s = 1 :=
    le_antisymm (w.intValuation_le_one s) (not_lt.mp fun h => hsw ((w.intValuation_lt_one_iff_mem s).mp h))
  have hss1 : w.intValuation (s * s' - 1) < 1 := (w.intValuation_lt_one_iff_mem _).mpr hss
  rw [e1, map_div₀, map_mul, Valuation.map_neg, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hs1, div_one]
  calc w.intValuation c * w.intValuation (s * s' - 1) ≤ 1 * w.intValuation (s * s' - 1) :=
        mul_le_mul_left (w.intValuation_le_one c) _
    _ = w.intValuation (s * s' - 1) := one_mul _
    _ < 1 := hss1

theorem exists_int_approx_compl (u : w.adicCompletion E) (hu : Valued.v u ≤ 1) :
    ∃ x : 𝓞 E, Valued.v (u - algebraMap E (w.adicCompletion E) (x : E)) < 1 := by
  have hvF : ∀ e : E, Valued.v (algebraMap E (w.adicCompletion E) e) = w.valuation E e :=
    fun e => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w e
  obtain ⟨e, he⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_dist_lt u one_pos
  rw [dist_eq_norm, Valued.toNormedField.norm_lt_one_iff] at he
  have hve : w.valuation E e ≤ 1 := by
    rw [← hvF]
    have e2 : algebraMap E (w.adicCompletion E) e = u - (u - algebraMap E (w.adicCompletion E) e) := by ring
    rw [e2]
    exact (Valuation.map_sub _ _ _).trans (max_le hu he.le)
  obtain ⟨x, hx⟩ := exists_int_approx w e hve
  refine ⟨x, ?_⟩
  have e3 : u - algebraMap E (w.adicCompletion E) (x : E) =
      (u - algebraMap E (w.adicCompletion E) e) + algebraMap E (w.adicCompletion E) (e - algebraMap (𝓞 E) E x) := by
    rw [map_sub]; ring
  rw [e3]
  exact Valuation.map_add_lt _ he (by rw [hvF]; exact hx)

end DiscreteGroups.sglob.DzType

end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Art

variable {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A w'}

theorem val_eq_one_iff (y : w'.adicCompletion E') :
    valuation (w'.adicCompletion E') y = 1 ↔ Valued.v y = 1 := by
  have e1 := DiscreteGroups.sglob.DzIso.val_lt_iff y
  have e2 := DiscreteGroups.sglob.DzIso.val_le_iff y
  rw [Valued.toNormedField.norm_lt_one_iff] at e1
  rw [Valued.toNormedField.norm_le_one_iff] at e2
  constructor
  · intro h
    exact le_antisymm (e2.1 h.le) (not_lt.1 fun hl => (e1.2 hl).ne h)
  · intro h
    exact le_antisymm (e2.2 h.le) (not_lt.1 fun hl => (e1.1 hl).ne h)

theorem exists_ine_of_v_eq_one {a' : Weil h' →* (w'.adicCompletion E')ˣ} (ha' : IsLocalArtin h' a')
    (u : (w'.adicCompletion E')ˣ) (hu : Valued.v (u : w'.adicCompletion E') = 1) :
    ∃ t : Ine (F := E') A, a' (ineIncl h' t) = u := by
  obtain ⟨σ, hσ⟩ := ha'.surj u
  have h1 := ha'.ord_eq σ
  rw [hσ, GlobalTheory.SmGL.SphCompletion.ord_completion, hu] at h1
  have h2 : deg σ = 0 := by simpa using h1
  exact ⟨⟨σ, deg_eq_zero_iff.1 h2⟩, by rw [← hσ]; rfl⟩

end Art

set_option linter.unusedVariables false in
theorem exists_ine_of_res {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ)
    (hn : 0 < n) (hN : normV w' = g ^ n) (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red) (hk : RingHom.ker red = w'.asIdeal) :
    ∀ z : Kˣ, ∃ (t : Ine (F := E') A) (x : 𝓞 E'), red x = z ∧
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  intro z
  obtain ⟨x, hx⟩ := hr z
  have hnm : x ∉ w'.asIdeal := fun hm => z.ne_zero (by rw [← hx, ← RingHom.mem_ker, hk]; exact hm)
  have hv : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = 1 := by
    have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
    rw [e]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w') (K := E')).2 hnm
  have h0 : algebraMap E' (w'.adicCompletion E') (x : E') ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv; exact zero_ne_one hv
  obtain ⟨t, ht⟩ := exists_ine_of_v_eq_one ha' (Units.mk0 _ h0) (by simpa using hv)
  refine ⟨t, x, hx, ?_⟩
  rw [ht, Units.val_mk0, sub_self, map_zero]
  exact zero_lt_one

theorem exists_resChar {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w') (n : ℕ)
    (hn : 0 < n) (hN : normV w' = g ^ n) (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red) (hk : RingHom.ker red = w'.asIdeal)
    (η : Weil h' →* ℂˣ) (hη : IsSmooth η) (hηN : ∀ t : Ine (F := E') A, η (ineIncl h' t) ^ (g ^ n - 1) = 1) :
    ∃ ξ : Kˣ →* ℂˣ, ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        ξ z = η (ineIncl h' t) := by
  obtain ⟨χ, -, hχ⟩ := ha'.factor η hη
  have hgp : g.Prime := Fact.out
  have hvF : ∀ e : E', Valued.v (algebraMap E' (w'.adicCompletion E') e) = w'.valuation E' e :=
    fun e => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' e

  have hpow : ∀ u : (w'.adicCompletion E')ˣ, Valued.v (u : w'.adicCompletion E') = 1 → χ u ^ (g ^ n - 1) = 1 := by
    intro u hu
    obtain ⟨t, ht⟩ := exists_ine_of_v_eq_one ha' u hu
    rw [← ht, ← MonoidHom.comp_apply, ← hχ]
    exact hηN t

  have hgw : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal := by
    have : Finite (𝓞 E' ⧸ w'.asIdeal) := w'.asIdeal.finiteQuotientOfFreeOfNeBot w'.ne_bot
    let := Fintype.ofFinite (𝓞 E' ⧸ w'.asIdeal)
    have hc : ((Fintype.card (𝓞 E' ⧸ w'.asIdeal) : ℕ) : 𝓞 E' ⧸ w'.asIdeal) = 0 := Nat.cast_card_eq_zero _
    rw [← Nat.card_eq_fintype_card, show Nat.card (𝓞 E' ⧸ w'.asIdeal) = g ^ n from hN, Nat.cast_pow] at hc
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact (pow_eq_zero_iff hn.ne').1 hc
  have hgv : Valued.v ((g : ℕ) : w'.adicCompletion E') < 1 := by
    have h1 := (w'.valuation_lt_one_iff_mem (K := E') ((g : ℕ) : 𝓞 E')).2 hgw
    have h2 := hvF ((g : ℕ) : E')
    rw [map_natCast] at h2
    rw [h2]
    simpa using h1
  have : CharP 𝓀[w'.adicCompletion E'] g := by
    rw [CharP.charP_iff_prime_eq_zero hgp, ← map_natCast (IsLocalRing.residue 𝒪[w'.adicCompletion E']) g,
      GlobalTheory.StepData.residue_eq_zero_iff_lt]
    have e : (((g : ℕ) : 𝒪[w'.adicCompletion E']) : w'.adicCompletion E') = ((g : ℕ) : w'.adicCompletion E') := by
      simp
    rw [e]
    exact (DiscreteGroups.sglob.DzIso.val_lt_iff _).2 (Valued.toNormedField.norm_lt_one_iff.2 hgv)

  have hmU : IsUnit (((g ^ n - 1 : ℕ) : ℤ_[g])) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast]
    have : Fact (1 < g) := ⟨hgp.one_lt⟩
    have h1 : 1 ≤ g ^ n := Nat.one_le_pow _ _ hgp.pos
    rw [Nat.cast_sub h1, Nat.cast_pow, ZMod.natCast_self, zero_pow hn.ne', Nat.cast_one, zero_sub, neg_eq_zero]
    exact one_ne_zero
  have hU1 : ∀ u : (w'.adicCompletion E')ˣ,
      valuation (w'.adicCompletion E') ((u : w'.adicCompletion E') - 1) < 1 → χ u = 1 := by
    intro u hu
    have hmem : u ∈ GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1 :=
      (GroundTheory.LocalField.mem_unitFiltrationUnits_iff_valBall le_rfl).2 (GroundTheory.LocalField.mem_valBall_one_iff.2 hu)
    let U : Additive (GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) := Additive.ofMul ⟨u, hmem⟩
    let y := ((hmU.unit⁻¹ : ℤ_[g]ˣ) : ℤ_[g]) • U
    have hy : (((g ^ n - 1 : ℕ) : ℤ_[g])) • y = U := by
      rw [smul_smul, IsUnit.mul_val_inv, one_smul]
    rw [GroundTheory.LocalField.natCast_smul g (g ^ n - 1) y] at hy
    have hy' : ((Additive.toMul y : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) :
        (w'.adicCompletion E')ˣ) ^ (g ^ n - 1) = u := by
      have := congrArg (fun z : Additive (GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) =>
        ((Additive.toMul z : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) :
          (w'.adicCompletion E')ˣ)) hy
      simpa [U] using this
    have hy0 : ((Additive.toMul y : GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 1) :
        (w'.adicCompletion E')ˣ) ∈ GroundTheory.LocalField.unitFiltrationUnits (w'.adicCompletion E') 0 :=
      GroundTheory.LocalField.unitFiltrationUnits_antitone (Nat.zero_le 1) (Additive.toMul y).2
    have hyv := (val_eq_one_iff _).1 (GroundTheory.LocalField.mem_unitFiltrationUnits_zero_iff.1 hy0)
    rw [← hy', map_pow]
    exact hpow _ hyv

  have hcong : ∀ u1 u2 : (w'.adicCompletion E')ˣ, Valued.v (u1 : w'.adicCompletion E') = 1 →
      Valued.v ((u1 : w'.adicCompletion E') - u2) < 1 → χ u1 = χ u2 := by
    intro u1 u2 h1 h2
    have hinv : Valued.v (((u1⁻¹ : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
    have : χ (u1⁻¹ * u2) = 1 := hU1 _ (by
      rw [DiscreteGroups.sglob.DzIso.val_lt_iff, Valued.toNormedField.norm_lt_one_iff]
      have e : (((u1⁻¹ * u2 : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') - 1 =
          ((u1⁻¹ : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') * ((u2 : w'.adicCompletion E') - u1) := by
        rw [Units.val_mul, mul_sub, Units.inv_mul]
      rw [e, map_mul, hinv, one_mul, Valuation.map_sub_swap]
      exact h2)
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  have hv1 : ∀ x : 𝓞 E', red x ≠ 0 → Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = 1 := by
    intro x hx
    have hnm : x ∉ w'.asIdeal := fun hm => hx (by rw [← RingHom.mem_ker, hk]; exact hm)
    rw [hvF]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w') (K := E')).2 hnm
  choose xz hxz using hr
  have hne : ∀ z : Kˣ, algebraMap E' (w'.adicCompletion E') (xz z : E') ≠ 0 := fun z h0 => by
    have := hv1 (xz z) (by rw [hxz]; exact z.ne_zero)
    rw [h0, map_zero] at this
    exact zero_ne_one this
  let Uz : Kˣ → (w'.adicCompletion E')ˣ := fun z => Units.mk0 _ (hne z)
  have hUv : ∀ z : Kˣ, Valued.v ((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1 :=
    fun z => hv1 (xz z) (by rw [hxz]; exact z.ne_zero)
  have hUc : ∀ (z : Kˣ) (x : 𝓞 E'), red x = z →
      Valued.v (((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') -
        algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
    intro z x hx
    have hm : xz z - x ∈ w'.asIdeal := by rw [← hk, RingHom.mem_ker, map_sub, hxz, hx, sub_self]
    have := (w'.valuation_lt_one_iff_mem (K := E') (xz z - x)).2 hm
    show Valued.v (algebraMap E' (w'.adicCompletion E') (xz z : E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1
    rw [← map_sub, hvF]
    exact this
  let ξ : Kˣ →* ℂˣ :=
    { toFun := fun z => χ (Uz z)
      map_one' := by
        have h := hUc 1 1 (by rw [map_one, Units.val_one])
        rw [show algebraMap E' (w'.adicCompletion E') ((1 : 𝓞 E') : E') = (((1 : (w'.adicCompletion E')ˣ)) :
          w'.adicCompletion E') by simp] at h
        show χ (Uz 1) = 1
        rw [hcong _ 1 (hUv 1) h, map_one]
      map_mul' := fun z1 z2 => by
        show χ (Uz (z1 * z2)) = χ (Uz z1) * χ (Uz z2)
        rw [← map_mul]
        refine hcong _ _ (hUv _) ?_
        have h := hUc (z1 * z2) (xz z1 * xz z2) (by rw [map_mul, hxz, hxz, Units.val_mul])
        have e : (((Uz z1 * Uz z2 : (w'.adicCompletion E')ˣ)) : w'.adicCompletion E') =
            algebraMap E' (w'.adicCompletion E') ((xz z1 * xz z2 : 𝓞 E') : E') := by
          simp [Uz]
        rw [e]
        exact h }
  refine ⟨ξ, fun t x z hxz' hv => ?_⟩
  show χ (Uz z) = η (ineIncl h' t)
  rw [hχ, MonoidHom.comp_apply]
  refine hcong _ _ (hUv z) ?_
  have h1 := hUc z x hxz'
  have e : ((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - (a' (ineIncl h' t) : w'.adicCompletion E') =
      (((Uz z : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) -
        ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) := by
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 hv)

end DiscreteGroups.sglob.DzType
end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzIsoRes
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

theorem norm_symm_le (y : 𝒪[w.adicCompletion E]) : ‖i.symm (y : w.adicCompletion E)‖ ≤ 1 := by
  rw [← norm_le_iff i hi, RingEquiv.apply_symm_apply]
  exact (val_le_iff _).1 ((Valuation.mem_integer_iff _ _).1 y.2)

def toIntFun (y : 𝒪[w.adicCompletion E]) : ℤ_[g] := ⟨i.symm y, norm_symm_le i hi y⟩

theorem coe_toIntFun (y : 𝒪[w.adicCompletion E]) : ((toIntFun i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def toInt : 𝒪[w.adicCompletion E] →+* ℤ_[g] where
  toFun := toIntFun i hi
  map_one' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_one]; simp)
  map_mul' a b := PadicInt.ext (by rw [PadicInt.coe_mul, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)
  map_zero' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_zero]; simp)
  map_add' a b := PadicInt.ext (by rw [PadicInt.coe_add, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)

theorem coe_toInt (y : 𝒪[w.adicCompletion E]) : ((toInt i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def redO : 𝒪[w.adicCompletion E] →+* ZMod g := (PadicInt.toZMod (p := g)).comp (toInt i hi)

theorem redO_surjective : Function.Surjective (redO i hi) := by
  intro a
  refine ⟨(a.val : 𝒪[w.adicCompletion E]), ?_⟩
  show PadicInt.toZMod (toInt i hi (a.val : 𝒪[w.adicCompletion E])) = a
  rw [map_natCast, map_natCast, ZMod.natCast_zmod_val]

theorem ker_redO : RingHom.ker (redO i hi) = IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E] := by
  ext y
  rw [← IsLocalRing.residue_eq_zero_iff, residue_eq_zero_iff_lt, RingHom.mem_ker]
  show PadicInt.toZMod (toInt i hi y) = 0 ↔ _
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def,
    coe_toInt, ← valuation_lt_iff i hi, RingEquiv.apply_symm_apply]

end DiscreteGroups.sglob.DzIso
end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzLDepth
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem lDepth : LDepth := by
  intro E _ _ w g _ i hi n τ σ hs
  obtain ⟨φ, hφ, hφe⟩ := hs
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    exact hφ (LinearMap.ext fun u => not_not.1 fun hne => h ⟨u, hne⟩)
  let e := equivRep σ
  have hfix : ∀ m ∈ KOne (w.adicCompletion E) (Fin n), σ.ρ m (φ u) = φ u := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KOne i hi hm
    have := hφe k u
    rw [hk, map_one, Module.End.one_apply] at this
    exact this.symm
  intro hbot
  have hv : e.toIntertwiningMap (φ u) ∈ fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) := by
    intro m
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [← e.toIntertwiningMap.isIntertwining, hfix m m.2]
  rw [hbot, Submodule.mem_bot] at hv
  have h2 : e.toLinearEquiv (φ u) = 0 := hv
  exact hu (e.toLinearEquiv.injective (h2.trans (map_zero _).symm))

end DiscreteGroups.sglob.DzType
end
end
