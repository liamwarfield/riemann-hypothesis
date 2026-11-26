module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemLoc
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem af_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y := by
  first
    | exact RestrictedProduct.ext h
    | exact Subtype.ext (funext h)
    | (ext w
       exact h w)


open Classical in
def sglV (a : v.adicCompletion F) : Af F :=
  ⟨Pi.single v a, by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton v).subset ?_)
    intro w hw
    by_contra hne
    apply hw
    have : w ≠ v := hne
    rw [Pi.single_eq_of_ne this]
    exact zero_mem _⟩

theorem sglV_same (a : v.adicCompletion F) : evalV F v (sglV v a) = a := by
  classical
  first
    | exact Pi.single_eq_same (i := v) (x := a)
    | exact Pi.single_eq_same v a
    | simp [sglV, evalV]

theorem sglV_ne (a : v.adicCompletion F) {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (sglV v a) = 0 := by
  classical
  first
    | exact Pi.single_eq_of_ne h a
    | exact Pi.single_eq_of_ne (i := v) h a
    | simp [sglV, evalV, h]

theorem sglV_add (a b : v.adicCompletion F) : sglV v (a + b) = sglV v a + sglV v b := by
  refine af_ext fun w => ?_
  rw [map_add (f := _)]
  by_cases h : w = v
  · subst h
    rw [sglV_same, sglV_same, sglV_same]
  · rw [sglV_ne _ _ h, sglV_ne _ _ h, sglV_ne _ _ h, add_zero]

theorem sglV_mul (a b : v.adicCompletion F) : sglV v (a * b) = sglV v a * sglV v b := by
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases h : w = v
  · subst h
    rw [sglV_same, sglV_same, sglV_same]
  · rw [sglV_ne _ _ h, sglV_ne _ _ h, sglV_ne _ _ h, mul_zero]

theorem sglV_zero : sglV v (0 : v.adicCompletion F) = 0 := by
  refine af_ext fun w => ?_
  rw [map_zero]
  by_cases h : w = v
  · subst h
    rw [sglV_same]
  · rw [sglV_ne _ _ h]

theorem sglV_smul (f : F) (a : v.adicCompletion F) :
    algebraMap F (Af F) f * sglV v a = sglV v (algebraMap F (v.adicCompletion F) f * a) := by
  refine af_ext fun w => ?_
  rw [map_mul, AlgHom.commutes]
  by_cases h : w = v
  · subst h
    rw [sglV_same, sglV_same] <;> rfl
  · rw [sglV_ne _ _ h, sglV_ne _ _ h, mul_zero]

theorem sglV_int {a : v.adicCompletion F} (ha : a ∈ v.adicCompletionIntegers F) : sglV v a ∈ intAf F := by
  first
    | (intro w
       by_cases h : w = v
       · subst h
         rw [sglV_same]
         exact ha
       · rw [sglV_ne _ _ h]
         exact zero_mem _)
    | (intro w
       by_cases h : w = v
       · subst h
         show evalV F w (sglV w a) ∈ _
         rw [sglV_same]
         exact ha
       · show evalV F w (sglV v a) ∈ _
         rw [sglV_ne _ _ h]
         exact zero_mem _)

def sA : v.adicCompletion F →ₙ+* AF F where
  toFun a := pairA F 0 (sglV v a)
  map_mul' a b := Prod.ext (by show (0 : Ainf F) = 0 * 0; rw [mul_zero]) (sglV_mul v a b)
  map_zero' := Prod.ext rfl (sglV_zero v)
  map_add' a b := Prod.ext (by show (0 : Ainf F) = 0 + 0; rw [add_zero]) (sglV_add v a b)

theorem sA_smul (f : F) (a : v.adicCompletion F) :
    algebraMap F (AF F) f * sA v a = sA v (algebraMap F (v.adicCompletion F) f * a) := by
  first
    | exact Prod.ext (mul_zero _) (sglV_smul v f a)
    | (refine Prod.ext ?_ ?_
       · show _ * (0 : Ainf F) = 0
         exact mul_zero _
       · exact sglV_smul v f a)

theorem sA_one_mul (a : AF F) : sA v 1 * a = sA v (evalV F v (sndA F a)) := by
  refine Prod.ext ?_ ?_
  · show (0 : Ainf F) * _ = 0
    exact zero_mul _
  · show sglV v 1 * _ = sglV v _
    refine af_ext fun w => ?_
    rw [map_mul]
    by_cases h : w = v
    · subst h
      rw [sglV_same, sglV_same, one_mul] <;> rfl
    · rw [sglV_ne _ _ h, sglV_ne _ _ h, zero_mul]

theorem mem_O_of_integral {y : v.adicCompletion F} (hy : IsIntegral ℤ y) : Valued.v y ≤ 1 := by
  first
    | (have hm := (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).mem_of_integral
         (IsIntegral.tower_top hy)
       first
         | exact hm
         | (obtain ⟨o, rfl⟩ := hm
            exact o.2)
         | (rcases hm with ⟨o, ho⟩
            rw [← ho]
            exact o.2))
    | (have hm := Valuation.Integers.mem_of_integral (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _))
         (IsIntegral.tower_top (A := (Valued.v : Valuation (v.adicCompletion F) _).integer) hy)
       first
         | exact hm
         | (obtain ⟨o, rfl⟩ := hm
            exact o.2))

theorem val_coe_lt_one_iff (f : 𝓞 F) :
    Valued.v (((f : F) : v.adicCompletion F)) < 1 ↔ f ∈ v.asIdeal := by
  have e : Valued.v (((f : F) : v.adicCompletion F)) = v.intValuation f := by
    first
      | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
         exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (r := f))
      | simp [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [e]
  first
    | exact IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v f
    | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd v f).trans Ideal.dvd_span_singleton
    | (rw [IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd, Ideal.dvd_span_singleton])

theorem val_coe_le_one (f : 𝓞 F) : Valued.v (((f : F) : v.adicCompletion F)) ≤ 1 := by
  first
    | exact mem_O_of_integral v ((NumberField.RingOfIntegers.isIntegral_coe f).map (algebraMap F (v.adicCompletion F)).toIntAlgHom)
    | (rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
         ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (r := f) ▸ rfl]
       exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v f)
    | (have e : Valued.v (((f : F) : v.adicCompletion F)) = v.intValuation f := by
         rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
         exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (v := v) (r := f)
       rw [e]
       exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v f)


set_option maxHeartbeats 800000 in
theorem roots_exist (t N : 𝓞 F) (hN : N ∈ v.asIdeal) (ht : t ∉ v.asIdeal) :
    ∃ r₁ r₂ : v.adicCompletion F, r₁ + r₂ = ((t : F) : v.adicCompletion F) ∧ r₁ * r₂ = ((N : F) : v.adicCompletion F) ∧
      Valued.v r₁ < 1 ∧ Valued.v r₂ = 1 := by
  open IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero Filter Topology Formalism.BasicNotions.Examples₂ in
    have adicInt_dvd_iff (x y : (v.adicCompletionIntegers F)) :
        x ∣ y ↔ Valued.v (y : (v.adicCompletion F)) ≤ Valued.v (x : (v.adicCompletion F)) := by
      first
      | exact (adicInt_integers (K := F) v).dvd_iff_le
      | exact Valuation.Integers.dvd_iff_le (adicInt_integers (K := F) v)

    have adicInt_max_eq_span (π : (v.adicCompletionIntegers F)) (hπ : Valued.v (π : (v.adicCompletion F)) = exp (-1 : ℤ)) :
        maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {π} := by
      ext x
      rw [adicInt_mem_max_iff v x, Ideal.mem_span_singleton, adicInt_dvd_iff π x, hπ, wz_lt_one_iff]

    have adicInt_mem_pow_iff (n : ℕ) (x : (v.adicCompletionIntegers F)) :
        x ∈ (maximalIdeal (v.adicCompletionIntegers F)) ^ n ↔ Valued.v (x : (v.adicCompletion F)) ≤ exp (-(n : ℤ)) := by
      obtain ⟨π, hπ⟩ := adicInt_exists_unif (K := F) v
      have h1 : ((π ^ n : (v.adicCompletionIntegers F)) : (v.adicCompletion F)) = (π : (v.adicCompletion F)) ^ n := by
        first
        | rfl
        | push_cast; rfl
        | simp
      have hpow : Valued.v ((π ^ n : (v.adicCompletionIntegers F)) : (v.adicCompletion F)) = exp (-(n : ℤ)) := by
        rw [h1, map_pow, hπ]
        first
        | (rw [← WithZero.exp_nsmul]; congr 1; simp)
        | (rw [← WithZero.exp_nsmul]; simp)
        | simp [WithZero.exp, ← ofAdd_nsmul]
      rw [adicInt_max_eq_span π hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
        adicInt_dvd_iff, hpow]

    have wz_exists_nat_lt (γ : ℤᵐ⁰) (h : γ ≠ 0) : ∃ N : ℕ, exp (-(N : ℤ)) < γ := by
      obtain ⟨m, rfl⟩ : ∃ m : ℤ, exp m = γ := ⟨_, WithZero.exp_log h⟩
      exact ⟨m.natAbs + 1, by rw [WithZero.exp_lt_exp]; omega⟩

    have adicInt_eq_zero_of_forall (x : (v.adicCompletion F)) (h : ∀ n : ℕ, Valued.v x ≤ exp (-(n : ℤ))) : x = 0 := by
      by_contra hx
      have h0 : Valued.v x ≠ 0 := by
        first
        | exact (Valuation.ne_zero_iff _).mpr hx
        | exact (map_ne_zero _).mpr hx
        | simpa using hx
      obtain ⟨N, hN⟩ := wz_exists_nat_lt (Valued.v x) h0
      exact absurd (h N) (not_le.mpr hN)

    have adicCompl_isClosed_le (r : ℤᵐ⁰) : IsClosed {x : (v.adicCompletion F) | Valued.v x ≤ r} := by
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro x hx
      have hx' : r < Valued.v x := not_le.mp hx
      have hx0 : Valued.v x ≠ 0 := (lt_of_le_of_lt zero_le' hx').ne'
      have hmem : {y : (v.adicCompletion F) | Valued.v y = Valued.v x} ∈ 𝓝 x := by
        first
        | exact Valuation.loc_const hx0
        | exact Valued.locally_const hx0
        | exact (Valued.isOpen_sphere (v.adicCompletion F) hx0).mem_nhds rfl
        | exact (Valued.isClopen_sphere (v.adicCompletion F) hx0).isOpen.mem_nhds rfl
        | exact (Valued.isOpen_sphere (R := (v.adicCompletion F)) hx0).mem_nhds rfl
      filter_upwards [hmem] with y hy
      show ¬ Valued.v y ≤ r
      rw [show Valued.v y = Valued.v x from hy]
      exact not_le.mpr hx'

    have adicInt_isAdicComplete : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := by
      have key : ∀ (n : ℕ) (x y : (v.adicCompletionIntegers F)), x ≡ y [SMOD (maximalIdeal (v.adicCompletionIntegers F) ^ n • ⊤ : Submodule (v.adicCompletionIntegers F) (v.adicCompletionIntegers F))] ↔
          Valued.v ((x : (v.adicCompletion F)) - y) ≤ exp (-(n : ℤ)) := by
        intro n x y
        rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, adicInt_mem_pow_iff]
        rfl
      have h1 : IsHausdorff (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := by
        refine ⟨fun x hx => ?_⟩
        have h0 : (x : (v.adicCompletion F)) = 0 := adicInt_eq_zero_of_forall _ (fun n => by
          simpa using (key n x 0).1 (hx n))
        exact Subtype.ext h0
      have h2 : IsPrecomplete (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := by
        refine ⟨fun f hf => ?_⟩
        set g : ℕ → (v.adicCompletion F) := fun n => (f n : (v.adicCompletion F))
        have hg : ∀ m n, m ≤ n → Valued.v (g n - g m) ≤ exp (-(m : ℤ)) := by
          intro m n hmn
          have := (key m (f m) (f n)).1 (hf hmn)
          rwa [← Valuation.map_neg, neg_sub] at this
        have hc : CauchySeq g := by
          rw [(Valued.hasBasis_uniformity (v.adicCompletion F) ℤᵐ⁰).cauchySeq_iff]
          intro γ _
          have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := fun h =>
            γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_injective (h.trans (map_zero _).symm))
          obtain ⟨N, hN⟩ := wz_exists_nat_lt _ hne
          refine ⟨N, fun m hm n hn => ?_⟩
          simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
          have hle : ∀ a b, N ≤ a → a ≤ b →
              Valued.v (g b - g a) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := fun a b ha hab =>
            lt_of_le_of_lt ((hg a b hab).trans (exp_le_exp.2 (by omega))) hN
          rcases le_total m n with h | h
          · exact hle m n hm h
          · rw [← Valuation.map_neg, neg_sub]; exact hle n m hn h
        obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
        have hLmem : L ∈ (v.adicCompletionIntegers F) := by
          refine (Valued.isClosed_valuationSubring (v.adicCompletion F)).mem_of_tendsto hL (Eventually.of_forall ?_)
          intro n; exact (f n).2
        refine ⟨⟨L, hLmem⟩, fun n => ?_⟩
        rw [key]
        have hcl : IsClosed {y : (v.adicCompletion F) | Valued.v (g n - y) ≤ exp (-(n : ℤ))} :=
          (adicCompl_isClosed_le _).preimage (continuous_const.sub continuous_id)
        refine hcl.mem_of_tendsto hL ?_
        filter_upwards [eventually_ge_atTop n] with k hk
        show Valued.v (g n - g k) ≤ _
        rw [← Valuation.map_neg, neg_sub]; exact hg n k hk
      exact { toIsHausdorff := h1, toIsPrecomplete := h2 }
    haveI : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := adicInt_isAdicComplete
    haveI : HenselianRing (v.adicCompletionIntegers F) (maximalIdeal (v.adicCompletionIntegers F)) := inferInstance
    haveI : HenselianLocalRing (v.adicCompletionIntegers F) := by
      refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
      exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)
    have hI : (Valued.v : Valuation (v.adicCompletion F) _).Integers (v.adicCompletionIntegers F) :=
      ⟨Subtype.val_injective, fun x => x.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
    have ea : ∀ x : v.adicCompletionIntegers F, algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) x = (x : v.adicCompletion F) := fun x => rfl
    have hnu : ∀ x : v.adicCompletionIntegers F, ¬ IsUnit x ↔ Valued.v (x : v.adicCompletion F) < 1 := by
      intro x
      have hle := hI.map_le_one x
      rw [ea] at hle
      rw [hI.isUnit_iff_valuation_eq_one, ea]
      exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
    have ht1 : Valued.v (((t : F) : v.adicCompletion F)) = 1 :=
      le_antisymm (val_coe_le_one v t) (not_lt.1 fun h => ht ((val_coe_lt_one_iff v t).1 h))
    have hN1 : Valued.v (((N : F) : v.adicCompletion F)) < 1 := (val_coe_lt_one_iff v N).2 hN
    obtain ⟨t', ht'⟩ : ∃ t' : v.adicCompletionIntegers F, (t' : v.adicCompletion F) = ((t : F) : v.adicCompletion F) := ⟨⟨_, val_coe_le_one v t⟩, rfl⟩
    obtain ⟨N', hN'⟩ : ∃ N' : v.adicCompletionIntegers F, (N' : v.adicCompletion F) = ((N : F) : v.adicCompletion F) := ⟨⟨_, val_coe_le_one v N⟩, rfl⟩
    have hmon : (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N').Monic := by
      first
        | monicity!
        | exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one 2 (by compute_degree!) (by simp)
    have he0 : Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N') = N' := by simp
    have h0 : Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N') ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
      rw [he0, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hnu, hN']
      exact hN1
    have hd0 : Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N')) = -t' := by simp
    have hu : IsUnit (Polynomial.eval (0 : v.adicCompletionIntegers F) (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N'))) := by
      rw [hd0]
      refine IsUnit.neg ?_
      rw [hI.isUnit_iff_valuation_eq_one, ea, ht']
      exact ht1
    obtain ⟨a, ha, ha0⟩ := HenselianLocalRing.is_henselian _ hmon 0 h0 hu
    have ha1 : Valued.v (a : v.adicCompletion F) < 1 := by
      have h4 := ha0
      rw [sub_zero, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hnu] at h4
      exact h4
    have h2 : (a : v.adicCompletion F) ^ 2 - ((t : F) : v.adicCompletion F) * a + ((N : F) : v.adicCompletion F) = 0 := by
      have ha' : Polynomial.eval a (Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C N') = 0 := ha
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C] at ha'
      have h3 := congrArg (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) ha'
      push_cast at h3
      rw [ht', hN'] at h3
      exact h3
    refine ⟨(a : v.adicCompletion F), ((t : F) : v.adicCompletion F) - a, by ring, by linear_combination -h2, ha1, ?_⟩
    first
      | rw [Valuation.map_sub_eq_of_lt_left _ (by rw [ht1]; exact ha1), ht1]
      | rw [Valuation.map_sub_eq_of_lt_right _ (by rw [ht1]; exact ha1), ht1]

end Loc

end Formalism.IndefR.Fin

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable {D : D7}

theorem algebraMap_adic_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (f : D.host.F) :
    algebraMap D.host.F (v.adicCompletion D.host.F) f = (f : v.adicCompletion D.host.F) := rfl

theorem isIntegral_star (x : 𝓞 D.host.E) : IsIntegral ℤ (star (x : D.host.E)) := (NumberField.RingOfIntegers.isIntegral_coe x).map (starRingEnd D.host.E).toIntAlgHom

def starO (x : 𝓞 D.host.E) : 𝓞 D.host.E := ⟨star (x : D.host.E), isIntegral_star x⟩

theorem coe_starO (x : 𝓞 D.host.E) : ((starO x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := rfl

theorem fixed_int (y : 𝓞 D.host.E) (hy : star (y : D.host.E) = y) :
    ∃ f : 𝓞 D.host.F, algebraMap D.host.F D.host.E (f : D.host.F) = (y : D.host.E) := by
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hmem : (y : D.host.E) ∈ NumberField.maximalRealSubfield D.host.E := by
    rw [NumberField.mem_maximalRealSubfield_iff]
    intro φ
    have h := NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ (y : D.host.E)
    have hs : (NumberField.IsCMField.complexConj D.host.E) (y : D.host.E) = y := hy
    rw [hs] at h
    exact h.symm
  have hint : IsIntegral ℤ (⟨(y : D.host.E), hmem⟩ : D.host.F) := by
    have h := NumberField.RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
      (IsScalarTower.toAlgHom ℤ D.host.F D.host.E : D.host.F →+* D.host.E).injective).mp h
  exact ⟨⟨⟨(y : D.host.E), hmem⟩, hint⟩, rfl⟩

theorem algebraMap_O (f : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) f : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (f : D.host.F) := rfl

theorem split_datum (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ¬ Lev.IsConjPl (D := D) P P)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) :
    ∃ (b : 𝓞 D.host.E) (t N : 𝓞 D.host.F), b ∈ P.asIdeal ∧ starO b ∉ P.asIdeal ∧
      algebraMap D.host.F D.host.E (t : D.host.F) = (b : D.host.E) + star (b : D.host.E) ∧
      algebraMap D.host.F D.host.E (N : D.host.F) = (b : D.host.E) * star (b : D.host.E) ∧
      t ∉ v.asIdeal ∧ N ∈ v.asIdeal := by
  have hnc : ∃ c ∈ P.asIdeal, starO c ∉ P.asIdeal := by
    by_contra hcon
    push_neg at hcon
    exact hP (fun c hc => ⟨starO c, hcon c hc, rfl⟩)
  obtain ⟨b, hbP, hbs⟩ := hnc
  obtain ⟨t, ht⟩ := fixed_int (b + starO b) (by simp [coe_starO, add_comm])
  obtain ⟨N, hN⟩ := fixed_int (b * starO b) (by simp [coe_starO, mul_comm])
  have htO : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = b + starO b :=
    NumberField.RingOfIntegers.ext (by rw [algebraMap_O, ht])
  have hNO : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) N = b * starO b :=
    NumberField.RingOfIntegers.ext (by rw [algebraMap_O, hN])
  refine ⟨b, t, N, hbP, hbs, ?_, ?_, ?_, ?_⟩
  · rw [ht]; simp [coe_starO]
  · rw [hN]; simp [coe_starO]
  · rw [← hv, Ideal.mem_comap, htO]
    intro hmem
    apply hbs
    have h2 := P.asIdeal.sub_mem hmem hbP
    simpa using h2
  · rw [← hv, Ideal.mem_comap, hNO]
    exact P.asIdeal.mul_mem_right _ hbP

instance finiteFE : Module.Finite D.host.F D.host.E :=
  Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)


set_option synthInstance.maxHeartbeats 200000 in
theorem emb_exists (v : HeightOneSpectrum (𝓞 D.host.F)) (b : D.host.E) (t N : D.host.F)
    (ht : algebraMap D.host.F D.host.E t = b + star b) (hN : algebraMap D.host.F D.host.E N = b * star b)
    (hb : star b ≠ b) (r₁ : v.adicCompletion D.host.F)
    (hr : r₁ ^ 2 - (t : v.adicCompletion D.host.F) * r₁ + (N : v.adicCompletion D.host.F) = 0) :
    ∃ ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F, ι b = r₁ ∧ Algebra.adjoin D.host.F {b} = ⊤ := by
  classical
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hfix : ∀ x : D.host.E, star x = x → ∃ f : D.host.F, algebraMap D.host.F D.host.E f = x := by
    intro x hx
    have hmem : x ∈ NumberField.maximalRealSubfield D.host.E := by
      rw [NumberField.mem_maximalRealSubfield_iff]
      intro φ
      have h := NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x
      have hs : (NumberField.IsCMField.complexConj D.host.E) x = x := hx
      rw [hs] at h
      exact h.symm
    exact ⟨⟨x, hmem⟩, rfl⟩
  have hbb : b - star b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  let P : Polynomial D.host.F := X ^ 2 - C t * X + C N
  have hPm : P.Monic := by simp only [P]; monicity!
  have hPd : P.natDegree = 2 := by simp only [P]; compute_degree!
  have hPb : Polynomial.aeval b P = 0 := by
    simp only [P, map_add (f := _), map_sub, map_mul, Polynomial.aeval_X_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, ht, hN]
    ring
  have hint : IsIntegral D.host.F b := ⟨P, hPm, hPb⟩
  have hsb : star b = algebraMap D.host.F D.host.E t - b := by rw [ht]; ring
  have htop : IntermediateField.adjoin D.host.F {b} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨f1, hf1⟩ := hfix (x + star x) (by rw [star_add, star_star, add_comm])
    obtain ⟨f2, hf2⟩ := hfix ((x - star x) / (b - star b)) (by
      rw [star_div₀, star_sub, star_sub, star_star, star_star, ← neg_sub x, ← neg_sub b, neg_div_neg_eq])
    have hxe : x = (algebraMap D.host.F D.host.E f1 + algebraMap D.host.F D.host.E f2 * (b - star b)) / 2 := by
      rw [hf1, hf2]
      field_simp
      ring
    have hbm : b ∈ IntermediateField.adjoin D.host.F {b} := IntermediateField.mem_adjoin_simple_self _ b
    have hsbm : star b ∈ IntermediateField.adjoin D.host.F {b} := by
      rw [hsb]
      exact sub_mem (IntermediateField.algebraMap_mem _ t) hbm
    have h2 : (2 : D.host.E) ∈ IntermediateField.adjoin D.host.F {b} := by
      rw [show (2 : D.host.E) = 1 + 1 by norm_num]
      exact add_mem (one_mem _) (one_mem _)
    rw [hxe]
    exact div_mem (add_mem (IntermediateField.algebraMap_mem _ f1)
      (mul_mem (IntermediateField.algebraMap_mem _ f2) (sub_mem hbm hsbm))) h2
  have hnotF : b ∉ (algebraMap D.host.F D.host.E).range := by
    rintro ⟨f, hf⟩
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    apply hb
    apply φ.injective
    have h := NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ b
    have h2 := (NumberField.mem_maximalRealSubfield_iff _).mp f.2 φ
    have hs : star b = (NumberField.IsCMField.complexConj D.host.E) b := rfl
    rw [hs, h, ← hf]
    exact h2
  have hmin : minpoly D.host.F b = P := by
    have hdvd : minpoly D.host.F b ∣ P := minpoly.dvd D.host.F b hPb
    have hdeg : 2 ≤ (minpoly D.host.F b).natDegree := by
      have h0 := minpoly.natDegree_pos hint
      have h1 : (minpoly D.host.F b).natDegree ≠ 1 := fun h => hnotF (minpoly.natDegree_eq_one_iff.mp h)
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPm hdvd (by omega)).symm
  let pb := IntermediateField.adjoin.powerBasis hint
  have hr' : Polynomial.aeval r₁ (minpoly D.host.F pb.gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin]
    simp only [P, map_add (f := _), map_sub, map_mul, Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hr
  let ι0 := pb.lift r₁ hr'
  refine ⟨ι0.comp ((IntermediateField.equivOfEq htop).symm.toAlgHom.comp
    (IntermediateField.topEquiv (F := D.host.F) (E := D.host.E)).symm.toAlgHom), ?_, ?_⟩
  · have hg : ((IntermediateField.equivOfEq htop).symm
        ((IntermediateField.topEquiv (F := D.host.F) (E := D.host.E)).symm b)) = pb.gen := by
      rw [IntermediateField.adjoin.powerBasis_gen]
      rfl
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    erw [hg]
    exact pb.lift_gen r₁ hr'
  · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop, IntermediateField.top_toSubalgebra]

end Glob

section Elt

variable {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F))

def phiE (a : v.adicCompletion D.host.F) : AE D := algebraMap (AF D.host.F) (AE D) (sA v a)

theorem phiE_mul (a b : v.adicCompletion D.host.F) : phiE v (a * b) = phiE v a * phiE v b := by
  simp only [phiE, map_mul]

theorem phiE_add (a b : v.adicCompletion D.host.F) : phiE v (a + b) = phiE v a + phiE v b := by
  simp only [phiE, map_add (f := _)]

theorem phiE_sub (a b : v.adicCompletion D.host.F) : phiE v (a - b) = phiE v a - phiE v b := by
  simp only [phiE, map_sub]

theorem phiE_zero : phiE v (0 : v.adicCompletion D.host.F) = 0 := by
  simp only [phiE, map_zero]

theorem phiE_smul (f : D.host.F) (a : v.adicCompletion D.host.F) :
    algebraMap D.host.F (AE D) f * phiE v a = phiE v (algebraMap D.host.F (v.adicCompletion D.host.F) f * a) := by
  unfold phiE
  rw [← sA_smul, map_mul, ← IsScalarTower.algebraMap_apply]

theorem cA_phiE (a : v.adicCompletion D.host.F) : cA D (phiE v a) = phiE v a := by
  unfold phiE cA
  first
    | exact AlgHom.commutes _ _
    | exact AlgEquiv.commutes _ _
    | simp [sigR]

theorem cA_incA (w : D.host.E) : cA D (incA D w) = incA D (star w) := by
  unfold cA incA
  simp [sigR, inclR]
  rfl

theorem incA_alg (f : D.host.F) : incA D (algebraMap D.host.F D.host.E f) = algebraMap D.host.F (AE D) f := by
  unfold incA
  first
    | exact AlgHom.commutes _ _
    | simp [inclR]

def compV (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) :
    Af D.host.F ⊗[D.host.F] D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F :=
  Algebra.TensorProduct.lift (evalV D.host.F v) ι (fun _ _ => Commute.all _ _)

theorem compV_phiE (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) (a : v.adicCompletion D.host.F) :
    compV v ι (finPart D (phiE v a)) = a := by
  have h1 : algebraMap (AF D.host.F) (AE D) (sA v a) = sA v a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  simp only [compV, phiE, finPart, h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  exact sglV_same v a

theorem compV_incA (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) (w : D.host.E) :
    compV v ι (finPart D (incA D w)) = ι w := by
  unfold compV incA
  simp [inclR, finPart]

theorem val_emb_le (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) (x : 𝓞 D.host.E) :
    Valued.v (ι (x : D.host.E)) ≤ 1 := by
  have hx : IsIntegral ℤ (ι (x : D.host.E)) :=
    IsIntegral.map_of_comp_eq (RingHom.id ℤ) (ι : D.host.E →+* v.adicCompletion D.host.F)
      (RingHom.ext_int _ _) (NumberField.RingOfIntegers.isIntegral_coe x)
  have h2 : IsIntegral (v.adicCompletionIntegers D.host.F) (ι (x : D.host.E)) := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2

theorem compV_int (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F) {z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ intAE D) : Valued.v (compV v ι z) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    simp only [compV, Algebra.TensorProduct.lift_tmul]
    rw [Valuation.map_mul]
    exact mul_le_one' (ha v) (val_emb_le v ι x)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _)]
    exact (Valuation.map_add _ _ _).trans (max_le hy hz)
  | neg y _ hy => rwa [map_neg, Valuation.map_neg]

end Elt

end Formalism.IndefR.Fin

end
