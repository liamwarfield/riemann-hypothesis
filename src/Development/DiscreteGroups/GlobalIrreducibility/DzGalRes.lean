module

public import Development.DiscreteGroups.GlobalIrreducibility.DzNormV
public import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
public import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A w'}

theorem val_artin_ine {a' : Weil h' →* (w'.adicCompletion E')ˣ} (ha' : IsLocalArtin h' a') (t : Ine (F := E') A) :
    Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1 := by
  have h1 := ha'.ord_eq (ineIncl h' t)
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, deg_ineIncl] at h1
  have hv0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact Units.ne_zero _
  have hl : WithZero.log (Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E')) = 0 := by
    simpa using h1
  rw [← WithZero.exp_log hv0, hl, WithZero.exp_zero]

theorem val_alg_lt_one_of_mem (x : 𝓞 E') (hx : x ∈ w'.asIdeal) :
    Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
  rw [e]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E') w' x).mpr hx

theorem val_alg_le_one (x : 𝓞 E') : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) ≤ 1 := by
  have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
  rw [e]
  exact w'.valuation_le_one x

variable {a' : Weil h' →* (w'.adicCompletion E')ˣ} (ha' : IsLocalArtin h' a') {K : Type} [Field K]
  {red : 𝓞 E' →+* K} (hk : RingHom.ker red = w'.asIdeal)
include ha' hk

theorem red_ne_zero_of_approx {t : Ine (F := E') A} {x : 𝓞 E'}
    (hx : Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1) :
    red x ≠ 0 := by
  intro h0
  have hxm : x ∈ w'.asIdeal := by rw [← hk, RingHom.mem_ker]; exact h0
  have hlt : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') < 1 := by
    have e : ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') =
        (((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') -
          algebraMap E' (w'.adicCompletion E') (x : E')) + algebraMap E' (w'.adicCompletion E') (x : E') := by ring
    rw [e]
    exact Valuation.map_add_lt _ hx (val_alg_lt_one_of_mem x hxm)
  rw [val_artin_ine ha' t] at hlt
  exact lt_irrefl _ hlt

theorem red_eq_of_approx {t : Ine (F := E') A} {x x' : 𝓞 E'}
    (hx : Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1)
    (hx' : Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) < 1) :
    red x = red x' := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hk]
  apply mem_of_val_lt_one w'
  have e : algebraMap E' (w'.adicCompletion E') (((x - x' : 𝓞 E')) : E') =
      ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x' : E')) -
        ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) := by
    rw [show (((x - x' : 𝓞 E')) : E') = (x : E') - (x' : E') by push_cast; ring, map_sub]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx' hx)

theorem exists_resHom : ∃ R : Ine (F := E') A →* Kˣ, ∀ (t : Ine (F := E') A) (x : 𝓞 E'),
    Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
      ((R t : Kˣ) : K) = red x := by
  have hex : ∀ t : Ine (F := E') A, ∃ x : 𝓞 E',
      Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 :=
    fun t => exists_int_approx_compl w' _ (val_artin_ine ha' t).le
  choose x hx using hex
  refine ⟨MonoidHom.mk' (fun t => Units.mk0 (red (x t)) (red_ne_zero_of_approx ha' hk (hx t))) ?_,
    fun t y hy => red_eq_of_approx ha' hk (hx t) hy⟩
  intro s t
  ext
  simp only [Units.val_mk0, Units.val_mul]
  rw [← map_mul]
  apply red_eq_of_approx ha' hk (hx (s * t))
  rw [map_mul, map_mul, Units.val_mul]
  have e : ((a' (ineIncl h' s) : w'.adicCompletion E') * (a' (ineIncl h' t) : w'.adicCompletion E')) -
      algebraMap E' (w'.adicCompletion E') (((x s * x t : 𝓞 E')) : E') =
      (a' (ineIncl h' s) : w'.adicCompletion E') *
        ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x t : E')) +
      ((a' (ineIncl h' s) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x s : E')) *
        algebraMap E' (w'.adicCompletion E') (x t : E') := by
    rw [show (((x s * x t : 𝓞 E')) : E') = (x s : E') * (x t : E') by push_cast; ring, map_mul]; ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul, val_artin_ine ha' s, one_mul]; exact hx t
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_alg_le_one (x t))) (hx s)

end DiscreteGroups.sglob.DzType

end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzTwChar
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzTw

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

def resMap : IsLocalRing.ResidueField 𝒪[w.adicCompletion E] →+* ZMod g :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E]) (DzIso.redO i hi) fun a ha => by
    rw [← RingHom.mem_ker, DzIso.ker_redO i hi]
    exact ha

end DiscreteGroups.sglob.DzTw
end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzGalW
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [hg : Fact g.Prime]

theorem g_not_mem_sq (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) :
    ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro hg2
  have hvF : ∀ y : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.intValuation y := fun y => by
    have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
    rw [e]; exact HeightOneSpectrum.valuation_of_algebraMap w y
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hg2' : w.intValuation ((g : ℕ) : 𝓞 E) ≤ WithZero.exp (-(2 : ℕ) : ℤ) :=
    (w.intValuation_le_pow_iff_mem _ 2).mpr hg2
  set x := i.symm (algebraMap E (w.adicCompletion E) (π : E)) with hx
  have hxπ : i x = algebraMap E (w.adicCompletion E) (π : E) := by rw [hx, RingEquiv.apply_symm_apply]
  have hπ1 : Valued.v (algebraMap E (w.adicCompletion E) (π : E)) < 1 := by
    rw [hvF, hπ]
    have h0 : WithZero.exp (-1 : ℤ) < WithZero.exp 0 := WithZero.exp_lt_exp.mpr (by norm_num)
    simpa using h0
  have hxn : ‖x‖ < 1 := by
    rw [← DiscreteGroups.sglob.DzIso.norm_lt_iff i hi, hxπ, Valued.toNormedField.norm_lt_one_iff]
    exact hπ1
  have hxg : ‖x / (g : ℚ_[g])‖ ≤ 1 := by
    have h1 : ‖x‖ ≤ (g : ℝ) ^ (-1 : ℤ) := by
      rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]; simpa using hxn
    rw [norm_div, Padic.norm_p, div_le_one (inv_pos.mpr (by exact_mod_cast hg.out.pos))]
    simpa [zpow_neg, zpow_one] using h1
  have h2 := DiscreteGroups.sglob.DzIso.norm_le_of_le i hi hxg
  rw [Valued.toNormedField.norm_le_one_iff] at h2
  have e : algebraMap E (w.adicCompletion E) (π : E) = ((g : ℕ) : w.adicCompletion E) * i (x / (g : ℚ_[g])) := by
    rw [← hxπ, ← map_natCast i g, ← map_mul, mul_div_cancel₀]
    exact_mod_cast hg.out.ne_zero
  have h3 : Valued.v (algebraMap E (w.adicCompletion E) (π : E)) ≤ WithZero.exp (-(2 : ℕ) : ℤ) := by
    rw [e, map_mul]
    have hgv : Valued.v ((g : ℕ) : w.adicCompletion E) = w.intValuation ((g : ℕ) : 𝓞 E) := by
      rw [← hvF]; simp
    rw [hgv]
    calc w.intValuation ((g : ℕ) : 𝓞 E) * Valued.v (i (x / (g : ℚ_[g])))
        ≤ w.intValuation ((g : ℕ) : 𝓞 E) * 1 := mul_le_mul_right h2 _
      _ ≤ _ := by rw [mul_one]; exact hg2'
  rw [hvF, hπ, WithZero.exp_le_exp] at h3
  norm_num at h3

end DiscreteGroups.sglob.DzType

end
end

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzGalKappa
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal ValuativeRel GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


section Ring

variable {Ω : Type} [Field Ω]

def kappaToA {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) : 𝓞 F →+* A :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A fun x =>
    mem_of_isIntegral_int A (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap

def kappaQ {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp (kappaToA A)

theorem kappa_ker_A {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (hv : IsPlaceOver A v) :
    RingHom.ker (kappaQ A : 𝓞 F →+* IsLocalRing.ResidueField A) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaQ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff, ← hv y]
  rfl

end Ring

section Compl

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem kappa_val_le_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y ≤ 1 ↔ Valued.v y ≤ 1 :=
  (DiscreteGroups.sglob.DzIso.val_le_iff y).trans Valued.toNormedField.norm_le_one_iff

theorem kappa_val_lt_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y < 1 ↔ Valued.v y < 1 :=
  (DiscreteGroups.sglob.DzIso.val_lt_iff y).trans Valued.toNormedField.norm_lt_one_iff

theorem kappa_v_int (y : 𝓞 L) :
    Valued.v (algebraMap L (v.adicCompletion L) (y : L)) = v.valuation L (y : L) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) v (y : L)

def kappaToO : 𝓞 L →+* 𝒪[v.adicCompletion L] :=
  ((algebraMap L (v.adicCompletion L)).comp (algebraMap (𝓞 L) L)).codRestrict 𝒪[v.adicCompletion L] fun y =>
    (Valuation.mem_integer_iff _ _).2 ((kappa_val_le_iff v _).2
      ((kappa_v_int v y).trans_le (v.valuation_le_one y)))

def kappaP : 𝓞 L →+* 𝓀[v.adicCompletion L] := (IsLocalRing.residue 𝒪[v.adicCompletion L]).comp (kappaToO v)

theorem kappa_ker_O : RingHom.ker (kappaP v) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaP, RingHom.comp_apply, ← map_zero (IsLocalRing.residue 𝒪[v.adicCompletion L]),
    residue_eq_iff_valuation_lt]
  have e1 : ((kappaToO v y : 𝒪[v.adicCompletion L]) : v.adicCompletion L) -
      ((0 : 𝒪[v.adicCompletion L]) : v.adicCompletion L) = algebraMap L (v.adicCompletion L) (y : L) := by
    rw [ZeroMemClass.coe_zero, sub_zero]
    rfl
  rw [e1, kappa_val_lt_iff v, kappa_v_int v y]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v y

theorem kappa_surj_O : Function.Surjective (kappaP v) := by
  intro z
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective z
  have hu : Valued.v (u : v.adicCompletion L) ≤ 1 :=
    (kappa_val_le_iff v _).1 ((Valuation.mem_integer_iff _ _).1 u.2)
  obtain ⟨x, hx⟩ := exists_int_approx_compl v (u : v.adicCompletion L) hu
  refine ⟨x, ?_⟩
  rw [kappaP, RingHom.comp_apply, residue_eq_iff_valuation_lt, Valuation.map_sub_swap]
  exact (kappa_val_lt_iff v _).2 hx

end Compl

end DiscreteGroups.sglob.DzType
end
end
