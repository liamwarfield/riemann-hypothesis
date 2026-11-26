module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCyclotomicGeneratesUnitsMod
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCyclotomicGeneratesUnitsMod
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing
namespace GlobalTheory.CycGen

open Pointwise

theorem fix_of_unram {E Ω : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field Ω] [Algebra E Ω]
    [Algebra ℚ Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hw : IsPlaceOver A w)
    (he : w.asIdeal.ramificationIdx ℤ = 1) (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A) (x : E) :
    σ (algebraMap E Ω x) = algebraMap E Ω x := by
  have : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  set τ : E ≃ₐ[ℚ] E := AlgEquiv.restrictNormalHom E σ with hτdef
  have hcomm : ∀ y : E, algebraMap E Ω (τ y) = σ (algebraMap E Ω y) := fun y =>
    AlgEquiv.restrictNormal_commutes σ E y
  have hin : τ ∈ Ideal.inertia (E ≃ₐ[ℚ] E) w.asIdeal := by
    intro y
    show τ • y - y ∈ w.asIdeal
    rw [← hw]
    have hy : algebraMap E Ω (y : E) ∈ A :=
      ReciprocityTheory.Gal.mem_of_isIntegral_int A ((y.2).map (IsScalarTower.toAlgHom ℤ E Ω))
    have h := hσ.2 (algebraMap E Ω (y : E)) ((A.valuation_le_one_iff _).mpr hy)
    have e : ((τ • y - y : 𝓞 E) : E) = τ y - y := rfl
    rw [e, map_sub, hcomm]
    exact h
  have hcard : Nat.card (Ideal.inertia (E ≃ₐ[ℚ] E) w.asIdeal) = 1 := by
    have := w.isPrime
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (w.asIdeal.under ℤ) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal (E ≃ₐ[ℚ] E), he]
  have h1 : τ = 1 := by
    have := (Subgroup.card_eq_one.mp hcard)
    have h2 : τ ∈ (⊥ : Subgroup (E ≃ₐ[ℚ] E)) := this ▸ hin
    exact Subgroup.mem_bot.mp h2
  rw [← hcomm, h1]
  rfl

end GlobalTheory.CycGen

namespace GlobalTheory.CycGen

theorem exists_unit_gen (l : ℕ) [Fact l.Prime] :
    ∃ v : ℤ_[l]ˣ, orderOf (PadicInt.toZMod (v : ℤ_[l])) = l - 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  set b : ℤ_[l] := ((a : ZMod l).val : ℤ_[l])
  have hb : PadicInt.toZMod b = (a : ZMod l) := by
    simp only [b, map_natCast, ZMod.natCast_zmod_val]
  have hu : IsUnit b := by
    by_contra hn
    have hm : b ∈ IsLocalRing.maximalIdeal ℤ_[l] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hb] at hm
    exact a.ne_zero hm
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hb, orderOf_units, orderOf_eq_card_of_forall_mem_zpowers ha,
    Nat.card_eq_fintype_card, ZMod.card_units]

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc), (∀ v ∈ placesOver H.E (N.l i), v.asIdeal.ramificationIdx ℤ = 1) → ∃ w ∈ placesOver H.E (N.l i), ∃ g0 ∈ Ine (F := H.E) (N.plOm.1 w), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 := by
  intro R H what₂ N i hram
  obtain ⟨w, hw⟩ := GlobalTheory.TameFixedLift.exists_place H.E (N.l i)
  refine ⟨w, hw, ?_⟩
  have : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap H.E N.Om).injective
  have : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed H.E
  have : IsScalarTower ℚ H.E N.Om := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : IsAlgClosure ℚ N.Om := IsAlgClosure.ofAlgebraic ℚ H.E N.Om
  have hA : (N.plOm.1 w).valuation (N.l i : N.Om) < 1 := by
    have := (N.plOm.2 w (N.l i : 𝓞 H.E)).2 hw
    simpa using this
  have := H.hostE_isGalois
  obtain ⟨v, hv⟩ := exists_unit_gen (N.l i)
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective N.Om (N.l i) (N.plOm.1 w) hA v
  obtain ⟨g, hg, hc⟩ := GlobalTheory.TameFixedLift.transfer (E := H.E) (N.plOm.1 w) (N.l i) σ hσ
    (fix_of_unram (N.plOm.1 w) w (N.plOm.2 w) (hram w hw) σ hσ)
  exact ⟨g, hg, by rw [hc, hσv, hv]⟩

end GlobalTheory.CycGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaCyclotomicGeneratesUnitsModStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertia_cyclotomic_generates_units_mod : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc), (∀ v ∈ placesOver H.E (N.l i), v.asIdeal.ramificationIdx ℤ = 1) → ∃ w ∈ placesOver H.E (N.l i), ∃ g0 ∈ Ine (F := H.E) (N.plOm.1 w), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 := by
  first | exact @GlobalTheory.CycGen.main | exact GlobalTheory.CycGen.main | (intros; apply GlobalTheory.CycGen.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HenselRootsOfLocalFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HenselRootsOfLocalFamily
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

namespace GlobalTheory

theorem localSubalgebra_eval_sub_mem_maximalIdeal {X O : Type} [CommRing O] [IsLocalRing O]
    (T : Subalgebra O (X → O)) [IsLocalRing T] {f : X → O} (hf : f ∈ T) (x y : X) :
    f x - f y ∈ IsLocalRing.maximalIdeal O := by
  classical
  haveI : (IsLocalRing.maximalIdeal O).IsMaximal := IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  let ψ : X → (T →+* O ⧸ IsLocalRing.maximalIdeal O) := fun z =>
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp
      ((Pi.evalRingHom (fun _ : X => O) z).comp (T.val : T →+* (X → O)))
  have hψ : ∀ z (g : T), ψ z g = Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) ((g : X → O) z) :=
    fun _ _ => rfl
  have hsurj : ∀ z, Function.Surjective (ψ z) := by
    intro z q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨algebraMap O T a, by rw [hψ]; rfl⟩
  have hker : ∀ z, RingHom.ker (ψ z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hg : (⟨f, hf⟩ - algebraMap O T (f y) : T) ∈ RingHom.ker (ψ y) := by
    rw [RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem]
    simp
  rw [hker y, ← hker x, RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem] at hg
  simpa using hg

theorem hensel_roots_of_local_family : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [HenselianRing O (IsLocalRing.maximalIdeal O)] {t : ℕ} (T : Subalgebra O (X → O)), IsLocalRing T → ∀ (P : X → Polynomial O), (∀ j, (fun x => (P x).coeff j) ∈ T) → (∀ x, (P x).Monic ∧ (P x).natDegree = t) → ∀ (π : X) (d : Fin t → O), (∀ a b, a ≠ b → IsUnit (d a - d b)) → P π = ∏ c, (Polynomial.X - Polynomial.C (d c)) → ∀ x, ∃ β : Fin t → O, Function.Injective β ∧ P x = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  intro X O _ _ _ _ t T hT P hcoeff hdeg π d hd hπ x
  have hmap : (P x).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) =
      (P π).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) := by
    ext j
    simp only [Polynomial.coeff_map]
    rw [Ideal.Quotient.eq]
    exact localSubalgebra_eval_sub_mem_maximalIdeal T (hcoeff j) x π
  have hroot : ∀ c, ∃ b, (P x).IsRoot b ∧ b - d c ∈ IsLocalRing.maximalIdeal O := by
    intro c
    apply HenselianRing.is_henselian (P x) (hdeg x).1 (d c)
    · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
        hmap, hπ, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_prod,
        Finset.prod_eq_zero (Finset.mem_univ c) (by simp), map_zero]
    · rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← Polynomial.derivative_map, hmap,
        Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      apply IsUnit.map
      rw [hπ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero,
        Polynomial.eval_prod]
      have : ∀ a ∈ Finset.univ.erase c, IsUnit (d c - d a) := fun a ha =>
        hd c a (Finset.ne_of_mem_erase ha).symm
      exact IsUnit.prod_iff.2 this
  choose β hβ hβm using hroot
  have hinj : Function.Injective β := by
    intro a b hab
    by_contra hne
    have hmem : d b - d a ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ (hβm a) (hβm b)
      rw [hab] at this
      convert this using 1; ring
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (hd b a (Ne.symm hne))
  refine ⟨β, hinj, ?_⟩
  have hx0 : P x ≠ 0 := (hdeg x).1.ne_zero
  have hle : (Finset.univ.val.map β) ≤ (P x).roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hinj Finset.univ.nodup)]
    intro r hr
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp hr
    exact (Polynomial.mem_roots hx0).mpr (hβ c)
  have hcard : (P x).roots.card ≤ (Finset.univ.val.map β).card := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, ← (hdeg x).2]
    exact Polynomial.card_roots' _
  have heq : Finset.univ.val.map β = (P x).roots := Multiset.eq_of_le_of_card_le hle hcard
  have hrc : (P x).roots.card = (P x).natDegree := by
    rw [← heq, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, (hdeg x).2]
  rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hdeg x).1 hrc, ← heq,
    Multiset.map_map]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HenselRootsOfLocalFamilyStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_roots_of_distinct_units_roots : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [HenselianRing O (IsLocalRing.maximalIdeal O)] {t : ℕ} (T : Subalgebra O (X → O)), IsLocalRing T → ∀ (P : X → Polynomial O), (∀ j, (fun x => (P x).coeff j) ∈ T) → (∀ x, (P x).Monic ∧ (P x).natDegree = t) → ∀ (π : X) (d : Fin t → O), (∀ a b, a ≠ b → IsUnit (d a - d b)) → P π = ∏ c, (Polynomial.X - Polynomial.C (d c)) → ∀ x, ∃ β : Fin t → O, Function.Injective β ∧ P x = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  first | exact @GlobalTheory.hensel_roots_of_local_family | exact GlobalTheory.hensel_roots_of_local_family | (intros; apply GlobalTheory.hensel_roots_of_local_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSubCharValuesOfCyclotomicGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSubCharValuesOfCyclotomicGenerator
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

namespace GlobalTheory.CharacterUnits

theorem unit_pow_sub_isUnit {l : ℕ} [Fact l.Prime] (u : ℤ_[l]ˣ)
    (hu : orderOf (PadicInt.toZMod (u : ℤ_[l])) = l - 1)
    (a b : ℕ) (ha : a < l - 1) (hb : b < l - 1) (hab : a ≠ b) :
    IsUnit ((u : ℤ_[l]) ^ a - (u : ℤ_[l]) ^ b) := by
  by_contra h
  have h1 : (u : ℤ_[l]) ^ a - (u : ℤ_[l]) ^ b ∈ IsLocalRing.maximalIdeal ℤ_[l] := h
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow, map_pow, sub_eq_zero] at h1
  exact hab (pow_injOn_Iio_orderOf (by rw [hu]; exact ha) (by rw [hu]; exact hb) h1)

theorem chi_sub_isUnit : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (g0 : G H.E N.Om), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 → R.t + 1 < N.l i → ∀ a ∈ Finset.Icc 1 R.t, ∀ b ∈ Finset.Icc 1 R.t, a ≠ b → IsUnit (((N.chi i a g0 : (N.O i)ˣ) : N.O i) - ((N.chi i b g0 : (N.O i)ˣ) : N.O i)) := by
  intro R H what₂ N i g0 hε hl a ha b hb hab
  rw [Finset.mem_Icc] at ha hb
  set e : (N.O i)ˣ := Units.map (algebraMap ℤ_[N.l i] (N.O i)).toMonoidHom
    (cycZ (F := H.E) (Ω := N.Om) (N.l i) g0) with he_def
  have h3 : ∀ c, 1 ≤ c → c ≤ R.t → N.chi i c g0 = N.chi i 1 g0 * (e⁻¹ ^ (c - 1)) := by
    intro c h1 h2
    rw [N.chi_def i c h1 h2, MonoidHom.mul_apply]
    congr 1
    have h4 : (-(((c : ℕ) : ℤ) - 1)) = -(((c - 1 : ℕ) : ℤ)) := by omega
    rw [h4, _root_.zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply, inv_pow]
    rfl
  have hu := (unit_pow_sub_isUnit _ hε (b - 1) (a - 1) (by omega) (by omega)
    (by omega)).map (algebraMap ℤ_[N.l i] (N.O i))
  rw [map_sub, map_pow, map_pow] at hu
  have he : algebraMap ℤ_[N.l i] (N.O i) ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      ((e : (N.O i)ˣ) : N.O i) := rfl
  rw [he] at hu
  rw [h3 a ha.1 ha.2, h3 b hb.1 hb.2]
  set x := N.chi i 1 g0
  have a1 : ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (a - 1) * (e : N.O i) ^ (a - 1) = 1 := by rw [← mul_pow]; simp
  have a2 : ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (b - 1) * (e : N.O i) ^ (b - 1) = 1 := by rw [← mul_pow]; simp
  have key : ((x * e⁻¹ ^ (a - 1) : (N.O i)ˣ) : N.O i) - ((x * e⁻¹ ^ (b - 1) : (N.O i)ˣ) : N.O i) =
      ((x * e⁻¹ ^ (a - 1) * e⁻¹ ^ (b - 1) : (N.O i)ˣ) : N.O i) *
        ((e : N.O i) ^ (b - 1) - (e : N.O i) ^ (a - 1)) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (-((x : N.O i) * ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (a - 1))) * a2 +
      ((x : N.O i) * ((e⁻¹ : (N.O i)ˣ) : N.O i) ^ (b - 1)) * a1
  rw [key]
  exact (Units.isUnit _).mul hu

end GlobalTheory.CharacterUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitSubCharValuesOfCyclotomicGeneratorStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_sub_charValues_of_cyclotomic_generator : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (g0 : G H.E N.Om), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 → R.t + 1 < N.l i → ∀ a ∈ Finset.Icc 1 R.t, ∀ b ∈ Finset.Icc 1 R.t, a ≠ b → IsUnit (((N.chi i a g0 : (N.O i)ˣ) : N.O i) - ((N.chi i b g0 : (N.O i)ˣ) : N.O i)) := by
  first | exact @GlobalTheory.CharacterUnits.chi_sub_isUnit | exact GlobalTheory.CharacterUnits.chi_sub_isUnit | (intros; apply GlobalTheory.CharacterUnits.chi_sub_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorIner
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.UseFive

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

theorem exists_good_gen (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (g0 : GE N)
    (hw : ∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w))
    (hord : orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) =
      N.l i - 1)
    (hu : ∀ a ∈ Finset.Icc 1 R.t, ∀ b ∈ Finset.Icc 1 R.t, a ≠ b →
      IsUnit (((N.chi i a g0 : (N.O i)ˣ) : N.O i) - ((N.chi i b g0 : (N.O i)ˣ) : N.O i)))
    (eB e1 X0 : N.X i → MatN N i) (hT : CharPolyIn (N.T i) rep)
    (hspan : Submodule.span (N.O i) (Set.range (mat (ρ π))) = ⊤)
    (hid : InRing (N.T i) rep eB ∧ InRing (N.T i) rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧
      e1 * eB = 0 ∧ (∀ x, ((eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((e1 x).map (toK N i)).rank = 1))
    (e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)))
    (hd : IsDecomp (t := R.t) (rep π) (ρ π) (N.chi i) e)
    (heB : ∀ u, e (((eB π).map (toK N i)).mulVec u) = (0, (e u).2))
    (hX : InRing (N.T i) rep X0) (hX1 : eB * X0 = X0) (hX2 : X0 * eB = X0)
    (hXπ : ∀ u, e (((X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i) * (e u).2 c))
    (hβ : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c))) :
    ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧ IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition N rep ρ π S := by
  classical
  have hinjχ : Set.InjOn (fun c => ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) (Finset.Icc 1 R.t : Set ℕ) := by
    intro a ha b hb hab
    by_contra hne
    have := hu a ha b hb hne
    simp only at hab
    rw [hab, sub_self] at this
    exact not_isUnit_zero this
  have hβ' : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c)) ∧
      (x = π → ∀ c, β c = ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i)) := by
    intro x
    by_cases hx : x = π
    · subst hx
      refine ⟨fun c => ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i), fun a b hab => ?_, ?_,
        fun _ _ => rfl⟩
      · have := hinjχ (x₁ := (a : ℕ) + 1) (by simp) (x₂ := (b : ℕ) + 1) (by simp) hab
        exact Fin.ext (by omega)
      · apply Polynomial.map_injective (toK N i) (IsFractionRing.injective _ _)
        rw [blockPol_map, (GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hXπ).2, Polynomial.map_prod]
        simp
    · obtain ⟨β, h1, h2⟩ := hβ x
      exact ⟨β, h1, h2, fun h => absurd h hx⟩
  choose β hβi hβp hβπ using hβ'
  have hrπ : ∀ c ∈ Finset.Icc 1 R.t, root β c (π, 1) = ((N.chi i c g0 : (N.O i)ˣ) : N.O i) := by
    intro c hc
    obtain ⟨a, rfl⟩ := exists_succ hc
    rw [root_succ]
    exact hβπ π rfl a
  have hset : (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ) =
      Set.range fun c : Fin R.t => fun x' : N.X i × Equiv.Perm (Fin R.t) => β x'.1 (x'.2 c) := by
    ext f
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨a, rfl⟩ := exists_succ hc
      exact ⟨a, funext fun x' => (root_succ β a x').symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : ℕ) + 1, by simp, funext fun x' => root_succ β a x'⟩
  let T' : Subalgebra (N.O i) (N.X i × Equiv.Perm (Fin R.t) → N.O i) :=
    Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f x'.1) '' (N.T i : Set _) ∪
      (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ))
  have hTT : ∀ f ∈ N.T i, (fun x' : N.X i × Equiv.Perm (Fin R.t) => f x'.1) ∈ T' :=
    fun f hf => Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)
  have hT' : CharPolyIn T' (fun x' => rep x'.1) := fun h d => hTT _ (hT h d)
  obtain ⟨ψρ, ψχ, hψ, hψs⟩ := GlobalTheory.T.exists_block_action_of_decomposition T' (fun x' => rep x'.1) (ρ π) (N.chi i) (π, 1) e hspan hd
  have hpol : ∀ x' : N.X i × Equiv.Perm (Fin R.t),
      ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (root β c x')) =
        blockPol (eB x'.1) (X0 x'.1) := by
    intro x'
    rw [prod_Icc_eq, hβp, ← Equiv.prod_comp x'.2 (fun c => Polynomial.X - Polynomial.C (β x'.1 c))]
    simp only [root_succ]
  have hE := fun x' : N.X i × Equiv.Perm (Fin R.t) =>
    GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain R.nV R.t (eB x'.1) (X0 x'.1) (fun c => root β c x') (two_le_ranks_t R)
      (congrFun hid.2.2.1 _) (congrFun hX1 _) (congrFun hX2 _) (by
        intro c hc c' hc' h
        obtain ⟨a, rfl⟩ := exists_succ hc
        obtain ⟨a', rfl⟩ := exists_succ hc'
        simp only [root_succ] at h
        rw [x'.2.injective (hβi _ h)]) (hpol x')
  refine ⟨{ eB := eB, e1 := e1, g0 := g0, X0 := X0, X' := N.X i × Equiv.Perm (Fin R.t), p := Prod.fst,
            T' := T', rr := root β, π' := (π, 1), e := e, ψρ := ψρ, ψχ := ψχ }, rfl,
    hid, hd, hψ, hψs, hw, hord, ⟨hX, hX1, hX2, hXπ⟩, ⟨hTT, ?_, rfl, ?_, ?_⟩, hpol, ⟨rfl, hrπ⟩,
    ⟨fun x' => (hE x').1, fun x' => (hE x').2, ?_, ?_⟩, GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T' _ hT', GlobalTheory.T.blockDet_mem_heckeAlgebra_of_heckeSpan T' _ hT'⟩
  · exact fun c hc => Algebra.subset_adjoin (Or.inr ⟨c, hc, rfl⟩)
  · have := GlobalTheory.SplittingAlgebra.main (N.T i) R.t β hβi (N.T_sep i) (fun j => by
      simpa only [hβp] using blockPol_coeff_mem hT hid.1 hX j)
    simp only [← hset] at this
    exact this
  · intro x
    have : {x' : N.X i × Equiv.Perm (Fin R.t) // x'.1 = x} ≃ Equiv.Perm (Fin R.t) :=
      { toFun := fun a => a.1.2
        invFun := fun σ => ⟨(x, σ), rfl⟩
        left_inv := by rintro ⟨⟨y, σ⟩, rfl⟩; rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr this).trans (by simp [Fintype.card_perm])
  · refine GlobalTheory.T.prod_other_root_factors_action_first_coordinate e (eB π) (X0 π) (fun c => root β c (π, 1)) (two_le_ranks_t R) heB (fun u => ?_)
    rw [hXπ]
    congr 1
    funext c
    rw [hrπ _ (by simp)]
  · have h2 := two_le_ranks_t R
    have : del51 N (⟨eB, e1, g0, X0, N.X i × Equiv.Perm (Fin R.t), Prod.fst, T', root β, (π, 1), e, ψρ, ψχ⟩ :
        IdempotentChoiceData N i) (π, 1) = ∏ c ∈ Finset.Ioc 1 R.t,
        (((N.chi i 1 g0 : (N.O i)ˣ) : N.O i) - ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) := by
      refine Finset.prod_congr rfl fun c hc => ?_
      show root β 1 (π, 1) - root β c (π, 1) = _
      rw [hrπ 1 (by simp; omega), hrπ c (Finset.Ioc_subset_Icc_self hc)]
    rw [this]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun c hc => ?_)
    have hc' := Finset.mem_Ioc.1 hc
    exact hu 1 (by simp; omega) c (Finset.Ioc_subset_Icc_self hc) (by omega)

end Record

theorem objects_globalStep_gen : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.admSS i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → ResSpan i ρ π → π ∈ D.nd.Z i → (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) → D.R.t + 1 < D.nd.l i → ∃ S : IdempotentChoiceData D.nd i, IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S := by
  intro D i r ρ π _ hG1 _ _ _ hdec _ hres _ hun ht
  classical
  obtain ⟨e, hd⟩ := hdec
  obtain ⟨w, hw, g0, hg0, hord⟩ := GlobalTheory.T.exists_inertia_cyclotomic_generates_units_mod D.nd i hun
  have hu := GlobalTheory.T.isUnit_sub_charValues_of_cyclotomic_generator D.nd i g0 hord ht
  have hT : CharPolyIn (D.nd.T i) r := hG1
  have hspan : Submodule.span (D.nd.O i) (Set.range (mat (ρ π))) = ⊤ := GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top (ρ π) hres
  obtain ⟨eB, e1, ⟨hB, h1, hBB, h11, hB1, h1B⟩, heB, ε, hε, he1⟩ :=
    GlobalTheory.T.exists_orthogonal_idempotents_heckeSpan_rep (D.nd.l i) (D.nd.T i) r (ρ π) (D.nd.chi i) π e (two_le_r _) hspan hd
  have hl := D.nd.T_local i
  have hXπ : ∀ u, e (((eB π * mat (r π) g0 * eB π).map (toK D.nd i)).mulVec u) =
      (0, fun c : Fin D.R.t => toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g0 : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c) := by
    intro u
    rw [Matrix.map_mul, Matrix.map_mul]
    exact corner_act e heB (hd g0) u
  have hat := GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hXπ
  have hrB : ∀ x, ((eB x).map (toK D.nd i)).rank = D.R.t := fun x => by
    rw [rank_const hl hT hB hBB x π]; exact hat.1
  have hr1 : ∀ x, ((e1 x).map (toK D.nd i)).rank = 1 := fun x => by
    rw [rank_const hl hT h1 h11 x π, GlobalTheory.T.rank_eq_of_mulVec_through_first_block e _ ε he1, hε]
  have hX : InRing (D.nd.T i) r (fun x => eB x * mat (r x) g0 * eB x) :=
    inRing_mul (inRing_mul hB (inRing_mat g0)) hB
  have hBx : ∀ x, eB x * eB x = eB x := congrFun hBB
  have hX1 : eB * (fun x => eB x * mat (r x) g0 * eB x) = fun x => eB x * mat (r x) g0 * eB x := by
    funext x; simp only [Pi.mul_apply, ← mul_assoc, hBx]
  have hX2 : (fun x => eB x * mat (r x) g0 * eB x) * eB = fun x => eB x * mat (r x) g0 * eB x := by
    funext x; simp only [Pi.mul_apply, mul_assoc, hBx]
  haveI := D.nd.O_complete i
  have hβ := GlobalTheory.T.exists_injective_roots_of_distinct_units_roots (t := D.R.t) (D.nd.T i) hl (fun x => blockPol (eB x) (eB x * mat (r x) g0 * eB x))
    (blockPol_coeff_mem hT hB hX)
    (fun x => by
      have hm := blockPol_monic (congrFun hBB x) (hrB x) (congrFun hX1 x) (congrFun hX2 x)
      exact ⟨Polynomial.monic_of_injective (IsFractionRing.injective _ _) hm.1,
        (Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _).symm.trans hm.2⟩)
    π (fun c => ((D.nd.chi i ((c : ℕ) + 1) g0 : (D.nd.O i)ˣ) : D.nd.O i))
    (fun a b hab => hu _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩) _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (fun h => hab (Fin.ext (by omega))))
    (by
      apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective _ _)
      rw [blockPol_map, hat.2, Polynomial.map_prod]
      simp)
  obtain ⟨S, -, hS⟩ := exists_good_gen D.nd i r ρ π g0 ⟨w, hw, hg0⟩ hord hu eB e1 _ hT hspan
    ⟨hB, h1, hBB, h11, hB1, h1B, hrB, hr1⟩ e hd heB hX hX1 hX2 hXπ hβ
  exact ⟨S, hS⟩

end GlobalTheory.UseFive

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorInerStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.admSS i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → ResSpan i ρ π → π ∈ D.nd.Z i → (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) → D.R.t + 1 < D.nd.l i → ∃ S : IdempotentChoiceData D.nd i, IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S := by
  first | exact @GlobalTheory.UseFive.objects_globalStep_gen | exact GlobalTheory.UseFive.objects_globalStep_gen | (intros; apply GlobalTheory.UseFive.objects_globalStep_gen <;> assumption)
end
