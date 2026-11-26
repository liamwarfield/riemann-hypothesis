module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactLocalConditionDataAtPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKato

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFinitePartOfLift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionLocalIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionLocalIntegers
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem exists_linRetraction_of_isTorsionFree {R S : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] (hinj : Function.Injective (algebraMap R S))
    [Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S))] :
    ∃ r : S →ₗ[R] R, r 1 = 1 := by
  set N := LinearMap.range (Algebra.linearMap R S) with hN
  haveI : Module.Free R (S ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let φ : S →ₗ[R] S := LinearMap.id - s ∘ₗ N.mkQ
  have hφ : ∀ x, φ x ∈ N := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hs (N.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    have this' : (Submodule.Quotient.mk (s (Submodule.Quotient.mk x)) : S ⧸ N) = Submodule.Quotient.mk x := this
    simp [φ, Submodule.Quotient.mk_sub, this']
  have hinj' : Function.Injective (Algebra.linearMap R S) := hinj
  let e := LinearEquiv.ofInjective (Algebra.linearMap R S) hinj'
  refine ⟨e.symm.toLinearMap ∘ₗ φ.codRestrict N hφ, ?_⟩
  have h1 : (1 : S) ∈ N := ⟨1, map_one (algebraMap R S)⟩
  have hφ1 : φ 1 = 1 := by
    have : N.mkQ 1 = 0 := (Submodule.Quotient.mk_eq_zero N).2 h1
    simp [φ, this]
  apply hinj'
  have := congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict N hφ 1))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofInjective_apply] at this
  rw [this, LinearMap.codRestrict_apply, hφ1, Algebra.linearMap_apply, map_one]

theorem isTorsionFree_quot_range {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    (H : ∀ a : R, a ≠ 0 → ∀ (b : R) (z : S), algebraMap R S b = algebraMap R S a * z → ∃ c, algebraMap R S c = z) :
    Module.IsTorsionFree R (S ⧸ LinearMap.range (Algebra.linearMap R S)) := by
  refine ⟨fun a ha => ?_⟩
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with | _ x => ?_
  induction y using Submodule.Quotient.induction_on with | _ y => ?_
  have hxy' : (Submodule.Quotient.mk (a • x) : S ⧸ LinearMap.range (Algebra.linearMap R S)) =
      Submodule.Quotient.mk (a • y) := hxy
  rw [Submodule.Quotient.eq] at hxy' ⊢
  obtain ⟨b, hb⟩ := hxy'
  rw [← smul_sub, Algebra.smul_def] at hb
  obtain ⟨c, hc⟩ := H a ha.ne_zero b (x - y) hb
  exact ⟨c, hc⟩

end GlobalTheory.UseLoc

namespace GlobalTheory.UseLoc

theorem incO_injective {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    Function.Injective (incO h) := by
  intro a b hab
  have := congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hab
  exact Subtype.ext (Subtype.ext this)

theorem incO_div {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {a b : ↥(OL LL)} (ha0 : a ≠ 0)
    {z : ↥(OL LL')} (hb : incO h b = incO h a * z) : ∃ c, incO h c = z := by
  have haL : ((a : ↥LL.1) : Om l) ≠ 0 := fun e => ha0 (Subtype.ext (Subtype.ext e))
  have hb' : ((b : ↥LL.1) : Om l) = ((a : ↥LL.1) : Om l) * ((z : ↥LL'.1) : Om l) :=
    congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) hb
  have hz : ((z : ↥LL'.1) : Om l) = ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) := by
    rw [eq_div_iff haL, mul_comm]
    exact hb'.symm
  have hc : (b : ↥LL.1) / (a : ↥LL.1) ∈ OL LL := by
    rw [Formalism.BasicNotions.Examples₂.LB.mem_OL]
    have hz1 := (Formalism.BasicNotions.Examples₂.LB.mem_OL LL' (z : ↥LL'.1)).1 z.2
    rw [hz] at hz1
    simpa using hz1
  refine ⟨⟨_, hc⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change ((b : ↥LL.1) : Om l) / ((a : ↥LL.1) : Om l) = ((z : ↥LL'.1) : Om l)
  rw [hz]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_intRetraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1),
    ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  intro l _ LL LL' h
  letI A : Algebra ↥(OL LL) ↥(OL LL') := (incO h).toAlgebra
  haveI : IsDiscreteValuationRing ↥(OL LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr LL
  haveI T : IsScalarTower ℤ_[l] ↥(OL LL) ↥(OL LL') := IsScalarTower.of_algebraMap_eq (fun x => by
    apply Subtype.ext; apply Subtype.ext; rfl)
  haveI : Module.Finite ℤ_[l] ↥(OL LL') := Formalism.BasicNotions.Examples₂.LB.OL_finite LL'
  haveI : Module.Finite ↥(OL LL) ↥(OL LL') := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI := isTorsionFree_quot_range (R := ↥(OL LL)) (S := ↥(OL LL')) (fun a ha b z hb => incO_div h ha hb)
  obtain ⟨r, hr⟩ := exists_linRetraction_of_isTorsionFree (R := ↥(OL LL)) (S := ↥(OL LL')) (incO_injective h)
  refine ⟨r.toAddMonoidHom, fun a x => ?_, hr⟩
  show r (incO h a * x) = a * r x
  have e1 : incO h a * x = a • x := (Algebra.smul_def a x).symm
  rw [e1, map_smul, smul_eq_mul]

end GlobalTheory.UseLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralRetractionLocalIntegersStatement
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_retraction_localIntegers : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1), ∃ r : ↥(OL LL') →+ ↥(OL LL), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) ∧ r 1 = 1 := by
  first | exact @GlobalTheory.UseLoc.exists_intRetraction | exact GlobalTheory.UseLoc.exists_intRetraction | (intros; apply GlobalTheory.UseLoc.exists_intRetraction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetraction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetraction
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc

noncomputable section

namespace GlobalTheory.UseLoc.ExtRet

variable {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l}

theorem algebraMap_ne_zero (LL : FinExt l) {d : ℤ_[l]} (hd : d ≠ 0) : algebraMap ℤ_[l] LL.1 d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] LL.1]
  intro h0
  apply hd
  have h1 : algebraMap ℤ_[l] ℚ_[l] d = 0 := (map_eq_zero_iff _ (algebraMap ℚ_[l] LL.1).injective).1 h0
  exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h1

theorem exists_mul (LL : FinExt l) (x : LL.1) : ∃ d : ℤ_[l], d ≠ 0 ∧ IsIntegral ℤ_[l] (d • x) := by
  haveI := LL.2
  haveI : Algebra.IsAlgebraic ℤ_[l] LL.1 :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l]) (C := LL.1)).2 inferInstance
  exact (Algebra.IsAlgebraic.isAlgebraic x).exists_integral_multiple

theorem r_smul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (c : ℤ_[l]) (z : ↥(OL LL')) :
    ((r (c • z) : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 c * ((r z : ↥(OL LL)) : LL.1) := by
  have e : c • z = incO h (algebraMap ℤ_[l] (OL LL) c) * z := by
    apply Subtype.ext
    simp [incO, Algebra.smul_def]
  rw [e, hr]
  simp

def ext (r : ↥(OL LL') →+ ↥(OL LL)) (x : LL'.1) : LL.1 :=
  ((r ⟨(exists_mul LL' x).choose • x, (exists_mul LL' x).choose_spec.2⟩ : ↥(OL LL)) : LL.1) /
    algebraMap ℤ_[l] LL.1 (exists_mul LL' x).choose

theorem ext_eq (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x)
    (x : LL'.1) (d : ℤ_[l]) (hd : d ≠ 0) (y : ↥(OL LL')) (hy : (y : LL'.1) = d • x) :
    ext r x = ((r y : ↥(OL LL)) : LL.1) / algebraMap ℤ_[l] LL.1 d := by
  unfold ext
  set d0 := (exists_mul LL' x).choose with hd0def
  have hd0 : d0 ≠ 0 := (exists_mul LL' x).choose_spec.1
  set y0 : ↥(OL LL') := ⟨d0 • x, (exists_mul LL' x).choose_spec.2⟩ with hy0
  have key : d • y0 = d0 • y := by
    apply Subtype.ext
    simp only [SetLike.val_smul, hy0, hy, smul_smul, mul_comm]
  have k2 := congrArg (fun z => ((r z : ↥(OL LL)) : LL.1)) key
  simp only [r_smul h r hr] at k2
  rw [div_eq_div_iff (algebraMap_ne_zero LL hd0) (algebraMap_ne_zero LL hd)]
  linear_combination k2

theorem ext_add (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x₁ x₂ : LL'.1) :
    ext r (x₁ + x₂) = ext r x₁ + ext r x₂ := by
  obtain ⟨d₁, hd₁, hi₁⟩ := exists_mul LL' x₁
  obtain ⟨d₂, hd₂, hi₂⟩ := exists_mul LL' x₂
  let y₁ : ↥(OL LL') := ⟨d₁ • x₁, hi₁⟩
  let y₂ : ↥(OL LL') := ⟨d₂ • x₂, hi₂⟩
  have hy : ((d₂ • y₁ + d₁ • y₂ : ↥(OL LL')) : LL'.1) = (d₁ * d₂) • (x₁ + x₂) := by
    simp only [y₁, y₂, Subalgebra.coe_add, SetLike.val_smul, smul_smul, smul_add]
    rw [mul_comm d₂ d₁]
  rw [ext_eq h r hr _ (d₁ * d₂) (mul_ne_zero hd₁ hd₂) _ hy, ext_eq h r hr x₁ d₁ hd₁ y₁ rfl,
    ext_eq h r hr x₂ d₂ hd₂ y₂ rfl, map_add, Subalgebra.coe_add, r_smul h r hr, r_smul h r hr, map_mul]
  have n₁ := algebraMap_ne_zero LL hd₁
  have n₂ := algebraMap_ne_zero LL hd₂
  field_simp

theorem ext_mul (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (a : LL.1) (x : LL'.1) :
    ext r (IntermediateField.inclusion h a * x) = a * ext r x := by
  obtain ⟨d, hd, hi⟩ := exists_mul LL' x
  obtain ⟨e, he, hie⟩ := exists_mul LL a
  let y : ↥(OL LL') := ⟨d • x, hi⟩
  let a'' : ↥(OL LL) := ⟨e • a, hie⟩
  have hy : ((incO h a'' * y : ↥(OL LL')) : LL'.1) = (e * d) • (IntermediateField.inclusion h a * x) := by
    simp only [incO, y, a'', RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subalgebra.coe_mul,
      SetLike.val_smul, map_smul]
    simp only [Algebra.smul_def, map_mul]
    have hc : IntermediateField.inclusion h (algebraMap ℤ_[l] LL.1 e) = algebraMap ℤ_[l] LL'.1 e := by simp
    rw [hc]
    ring
  rw [ext_eq h r hr _ (e * d) (mul_ne_zero he hd) _ hy, ext_eq h r hr x d hd y rfl, hr,
    Subalgebra.coe_mul, map_mul]
  have n₁ := algebraMap_ne_zero LL hd
  have n₂ := algebraMap_ne_zero LL he
  have ha : ((a'' : ↥(OL LL)) : LL.1) = algebraMap ℤ_[l] LL.1 e * a := by
    simp [a'', Algebra.smul_def]
  rw [ha]
  field_simp

theorem ext_int (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL))
    (hr : ∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) (x : ↥(OL LL')) :
    ext r (x : LL'.1) = ((r x : ↥(OL LL)) : LL.1) := by
  rw [ext_eq h r hr _ 1 one_ne_zero x (by simp)]
  simp

end GlobalTheory.UseLoc.ExtRet

namespace GlobalTheory.UseLoc

theorem extRet_exists : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  intro l _ LL LL' h r hr _
  refine ⟨{ toFun := ExtRet.ext r
            map_add' := ExtRet.ext_add h r hr
            map_smul' := fun q x => ?_ }, ExtRet.ext_mul h r hr, ExtRet.ext_int h r hr⟩
  have e : q • x = IntermediateField.inclusion h (algebraMap ℚ_[l] LL.1 q) * x := by
    rw [Algebra.smul_def]
    rfl
  simp only [RingHom.id_apply]
  rw [e, ExtRet.ext_mul h r hr, Algebra.smul_def]

end GlobalTheory.UseLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldExtensionOfIntegralRetractionStatement
open Formalism.MainNotions.N Formalism.BasicNotions.Loc GlobalTheory.UseLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fieldExtension_of_integral_retraction : ∀ {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (r : ↥(OL LL') →+ ↥(OL LL)), (∀ (a : ↥(OL LL)) (x : ↥(OL LL')), r (incO h a * x) = a * r x) → r 1 = 1 → ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧ ∀ x : ↥(OL LL'), p (x : ↥LL'.1) = ((r x : ↥(OL LL)) : ↥LL.1) := by
  first | exact @GlobalTheory.UseLoc.extRet_exists | exact GlobalTheory.UseLoc.extRet_exists | (intros; apply GlobalTheory.UseLoc.extRet_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFinitePartOfLift
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescHf

theorem exists_retraction {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧
      (∀ a : ↥LL.1, p (IntermediateField.inclusion h a) = a) ∧ (∀ x : ↥LL'.1, x ∈ OL LL' → p x ∈ OL LL) := by
  obtain ⟨r, hr, hr1⟩ := GlobalTheory.T.exists_integral_retraction_localIntegers h
  obtain ⟨p, hp, hpr⟩ := GlobalTheory.T.exists_fieldExtension_of_integral_retraction h r hr hr1
  have h1 : p 1 = 1 := by
    have := hpr 1
    rw [hr1] at this
    exact this
  refine ⟨p, hp, fun a => ?_, fun x hx => ?_⟩
  · have := hp a 1
    rw [mul_one, h1, mul_one] at this
    exact this
  · have := hpr ⟨x, hx⟩
    rw [show p x = _ from this]
    exact (r ⟨x, hx⟩).2


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem descHf : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  intro D i w hw C k M z hz
  obtain ⟨p, hpm, hp1, hpO⟩ := exists_retraction C.le
  obtain ⟨c, hc, m, hcm⟩ := (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).1 hz
  have hent : ∀ g a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g) a b =
      IntermediateField.inclusion C.le (Br.loc D.nbr i w hw M g a b) := fun g a b => rfl
  have hp : ∀ g (v : Fin k → ↥C.LL.1),
      (fun j => p ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v j)) =
        (Br.loc D.nbr i w hw M g).mulVec fun j => p (v j) := by
    intro g v
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, hent, hpm]
  have hc' := GlobalTheory.TwistedSelmerCompare.crystallineCocycle_transport_conjugation (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).Kw C.LL
    (D.nbr i w hw).LL (MonoidHom.id _) continuous_id 1 (fun g => by simp) _ (Br.loc D.nbr i w hw M) p hp c hc
  refine (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).2 ⟨_, hc', fun j => p (m j), fun g => ?_⟩
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (z g)
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (c g + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m - m)) := by
    refine (liftQ_mk C.le k u).symm.trans ?_
    refine Eq.trans ?_ (hcm g)
    exact congrArg (liftQ C.le k) hu
  obtain ⟨n, hn⟩ := (Submodule.Quotient.eq (stdG ↥(OL C.LL) ↥C.LL.1 k)).1 h1
  refine hu.symm.trans ((Submodule.Quotient.eq (stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k)).2 ?_)
  refine ⟨fun j => ⟨p (n j), hpO _ (n j).2⟩, ?_⟩
  funext j
  have h2 := congrArg p (congrFun hn j)
  have h3 := congrFun (hp g m) j
  change p ((n j : ↥C.LL.1)) = p (IntermediateField.inclusion C.le (u j) - (c g j + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m j - m j))) at h2
  change (p (n j) : Br.LL D.nbr i w hw) = u j - (p (c g j) + ((Br.loc D.nbr i w hw M g).mulVec (fun j => p (m j)) j - p (m j)))
  rw [h2, map_sub, map_add (f := _), map_sub, hp1, ← h3]

end GlobalTheory.UseLoc.DescHf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFinitePartOfLiftStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_finite_part_of_lift : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.UseLoc.DescHf.descHf | exact GlobalTheory.UseLoc.DescHf.descHf | (intros; apply GlobalTheory.UseLoc.DescHf.descHf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCocycleDescentEnlargement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCocycleDescentEnlargement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc

theorem descUr_entry (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) :
    (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M)) g a b =
      IntermediateField.inclusion C.le ((Br.loc D.nbr i w hw M) g a b) := by
  simp only [mapM, locOC, Br.loc, Br.locM, MonoidHom.coe_comp, Function.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl


set_option maxHeartbeats 2000000 in
theorem descUr_mem : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (I : Subgroup (Br.G D.nbr i w hw))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ Z1urD (latC C (locOC C M)) I → z ∈ Z1urD (Br.locLat D.nbr i w hw M) I := by
  intro D i w hw C k M I z hz
  obtain ⟨r, hrl, hr1, hrO⟩ :=
    GlobalTheory.CoefRetraction.exists_integral_retraction (D.nd.l i) (D.nbr i w hw).LL C.LL C.le
  have hri : ∀ a, r (IntermediateField.inclusion C.le a) = a := fun a => by
    have := hrl a 1
    simpa [hr1] using this
  obtain ⟨x', hx'⟩ := hz
  obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  refine ⟨Submodule.Quotient.mk (fun j => r (v' j)), fun g hg => ?_⟩
  have h : liftQ C.le k (z g) = actD (latC C (locOC C M)) g (Submodule.Quotient.mk v') - Submodule.Quotient.mk v' := hx' g hg
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective (Br.locLat D.nbr i w hw M).T (z g)
  rw [← hu] at h ⊢
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) ((repV C (locOC C M)) g v') -
        Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) v' := h
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq] at h1
  show (Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) u) =
      Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) ((matRep (Br.loc D.nbr i w hw M)) g (fun j => r (v' j))) -
        Submodule.Quotient.mk (p := stdG ↥(OL (D.nbr i w hw).LL) ↥(D.nbr i w hw).LL.1 k) (fun j => r (v' j))
  rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]
  obtain ⟨t, ht⟩ := h1
  refine ⟨fun j => ⟨r (t j), hrO _ (t j).2⟩, ?_⟩
  funext j
  have hj := congrFun ht j
  have hrl' : ∀ a x, r (IntermediateField.inclusion C.le a * x) = a * r x := hrl
  have hj' : ((t j : ↥(OL C.LL)) : ↥C.LL.1) = IntermediateField.inclusion C.le (u j) -
      ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v' j - v' j) := hj
  change r ((t j : ↥(OL C.LL)) : ↥C.LL.1) =
    u j - ((Br.loc D.nbr i w hw M g).mulVec (fun j => r (v' j)) j - r (v' j))
  rw [hj', map_sub, map_sub, hri]
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, descUr_entry, hrl']

end GlobalTheory.UseLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCocycleDescentEnlargementStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedCocycle_descent_enlargement : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (I : Subgroup (Br.G D.nbr i w hw))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ Z1urD (latC C (locOC C M)) I → z ∈ Z1urD (Br.locLat D.nbr i w hw M) I := by
  first | exact @GlobalTheory.UseLoc.descUr_mem | exact GlobalTheory.UseLoc.descUr_mem | (intros; apply GlobalTheory.UseLoc.descUr_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDescentEnlargementCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDescentEnlargementCoefficients
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescBD

section Abstract

theorem exists_retr_abs {Z O O' K K' : Type} [CommRing Z] [CommRing O] [CommRing O'] [IsDedekindDomain O]
    [Field K] [Field K'] [Algebra O K] [IsFractionRing O K] [Algebra Z O] [Algebra Z O'] [Module.Finite Z O']
    (f : O →+* O') (hf : ∀ c, algebraMap Z O' c = f (algebraMap Z O c)) (j : O' →+* K') (φ : K →+* K')
    (hc : ∀ a, φ (algebraMap O K a) = j (f a)) (hs : ∀ x : K', ∃ a : K, a ≠ 0 ∧ ∃ y, j y = φ a * x) :
    ∃ R : K' →+ K, (∀ a x, R (φ a * x) = a * R x) ∧ (∀ a, R (φ a) = a) ∧ ∀ x, ∃ y, j y = φ (R (j x)) := by
  letI : Algebra K K' := φ.toAlgebra
  letI : Algebra O K' := (φ.comp (algebraMap O K)).toAlgebra
  letI : Algebra O O' := f.toAlgebra
  letI : Algebra O' K' := j.toAlgebra
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower O O' K' := IsScalarTower.of_algebraMap_eq hc
  haveI : IsScalarTower Z O O' := IsScalarTower.of_algebraMap_eq hf
  haveI : Module.Finite O O' := Module.Finite.of_restrictScalars_finite Z _ _
  let L : Submodule O K' := LinearMap.range (IsScalarTower.toAlgHom O O' K').toLinearMap
  haveI : Module.Finite O L := inferInstance
  have hsp : Submodule.span K (L : Set K') = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, y, hy⟩ := hs x
    have e : x = a⁻¹ • j y := by
      rw [hy]
      change x = φ a⁻¹ * (φ a * x)
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.St.G.Inter.exists_retraction (O := O) (K := K)
    (Algebra.linearMap K K') φ.injective L hsp
  exact ⟨T.toAddMonoidHom, fun a x => T.map_smul a x, hT, fun x => hT' (j x) ⟨x, rfl⟩⟩

theorem mem_BD_iff {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) O) (z : Γ → (Fin k → K) ⧸ stdG O K k) :
    z ∈ BD (stdLatG hinj N) ↔ ∃ m : Fin k → K, ∀ g v, Submodule.Quotient.mk v = z g →
      ∃ u : Fin k → O, ∀ j, algebraMap O K (u j) = ∑ t, algebraMap O K (N g j t) * m t - m j - v j := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨m, fun g v hv => ?_⟩
    have hg := (congrFun hm g).trans hv.symm
    have hg' : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := (Submodule.Quotient.eq _).1 hg
    obtain ⟨u, hu⟩ := hg'
    exact ⟨u, fun j => congrFun hu j⟩
  · rintro ⟨m, hm⟩
    refine ⟨Submodule.Quotient.mk m, funext fun g => ?_⟩
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (z g)
    obtain ⟨u, hu⟩ := hm g v hv
    have key : matRep (mapM (algebraMap O K) N) g m - m - v ∈ stdG O K k := ⟨u, funext hu⟩
    exact ((Submodule.Quotient.eq _).2 key).trans hv

theorem desc_abs {O K O' K' : Type} [CommRing O] [Field K] [Algebra O K] [CommRing O'] [Field K'] [Algebra O' K']
    (hinj : Function.Injective (algebraMap O K)) (hinj' : Function.Injective (algebraMap O' K'))
    (f : O →+* O') (φ : K →+* K') (hc : ∀ a, algebraMap O' K' (f a) = φ (algebraMap O K a))
    (R : K' →+ K) (hR : ∀ a x, R (φ a * x) = a * R x) (hR1 : ∀ a, R (φ a) = a)
    (hRO : ∀ x, ∃ y, algebraMap O K y = R (algebraMap O' K' x))
    {Γ : Type} [Group Γ] {k : ℕ} (N : Γ →* Matrix (Fin k) (Fin k) O)
    (q : (Fin k → K) ⧸ stdG O K k → (Fin k → K') ⧸ stdG O' K' k)
    (hq : ∀ v, q (Submodule.Quotient.mk v) = Submodule.Quotient.mk (fun j => φ (v j)))
    (z : Γ → (Fin k → K) ⧸ stdG O K k) (hz : (fun g => q (z g)) ∈ BD (stdLatG hinj' (mapM f N))) :
    z ∈ BD (stdLatG hinj N) := by
  obtain ⟨m, hm⟩ := (mem_BD_iff hinj' (mapM f N) (fun g => q (z g))).1 hz
  refine (mem_BD_iff hinj N z).2 ⟨fun j => R (m j), fun g v hv => ?_⟩
  obtain ⟨u, hu⟩ := hm g (fun j => φ (v j)) (by rw [← hv, hq])
  choose r hr using hRO
  refine ⟨fun j => r (u j), fun j => ?_⟩
  have hj : algebraMap O' K' (u j) = ∑ t, algebraMap O' K' (f (N g j t)) * m t - m j - φ (v j) := hu j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hr, hj, map_sub, map_sub, map_sum, hR1]
  simp only [hc, hR]

end Abstract

section Gen
variable {l : ℕ} [Fact l.Prime]

theorem exists_retr {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ R : ↥LL'.1 →+ ↥LL.1, (∀ a x, R (IntermediateField.inclusion h a * x) = a * R x) ∧
      (∀ a, R (IntermediateField.inclusion h a) = a) ∧ ∀ x ∈ OL LL', R x ∈ OL LL := by
  haveI := LL.2
  haveI := LL'.2
  haveI : IsDedekindDomain ↥(OL LL) := integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL') :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL'.1 (integralClosure ℤ_[l] ↥LL'.1)
  obtain ⟨R, h1, h2, h3⟩ := exists_retr_abs (Z := ℤ_[l]) (O := ↥(OL LL)) (O' := ↥(OL LL')) (K := ↥LL.1)
    (K' := ↥LL'.1) (incO h) (fun _ => rfl) (OL LL').val.toRingHom (IntermediateField.inclusion h).toRingHom
    (fun _ => rfl) (fun x => by
      have hx : IsAlgebraic ℤ_[l] x :=
        (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL'.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
      obtain ⟨y, hy, hi⟩ := hx.exists_integral_multiple
      refine ⟨algebraMap ℤ_[l] ↥LL.1 y, ?_, ⟨y • x, hi⟩, Algebra.smul_def y x⟩
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
      simpa using hy)
  refine ⟨R, h1, h2, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h3 ⟨x, hx⟩
  have hy' : (y : ↥LL'.1) = ((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x) := hy
  have : IsIntegral ℤ_[l] (((IntermediateField.inclusion h).restrictScalars ℤ_[l]) (R x)) := hy' ▸ y.2
  exact (isIntegral_algHom_iff ((IntermediateField.inclusion h).restrictScalars ℤ_[l])
    (IntermediateField.inclusion h).injective).1 this

theorem desc {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {Γ : Type} [Group Γ] {k : ℕ}
    (N : Γ →* Matrix (Fin k) (Fin k) ↥(OL LL))
    (z : Γ → (Fin k → ↥LL.1) ⧸ stdG ↥(OL LL) ↥LL.1 k)
    (hz : (fun g => liftQ h k (z g)) ∈
      BD (stdLatG (O := ↥(OL LL')) (LL := ↥LL'.1) Subtype.val_injective (mapM (incO h) N))) :
    z ∈ BD (stdLatG (O := ↥(OL LL)) (LL := ↥LL.1) Subtype.val_injective N) := by
  obtain ⟨R, hR, hR1, hRO⟩ := exists_retr h
  exact desc_abs (O := ↥(OL LL)) (K := ↥LL.1) (O' := ↥(OL LL')) (K' := ↥LL'.1) Subtype.val_injective
    Subtype.val_injective (incO h) (IntermediateField.inclusion h).toRingHom (fun _ => rfl) R hR hR1
    (fun x => ⟨⟨R x, hRO _ x.2⟩, rfl⟩) N (liftQ h k) (liftQ_mk h k) z hz

end Gen

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ BD (latC C (locOC C M)) → z ∈ BD (Br.locLat D.nbr i w hw M) :=
  fun D i w hw C _ M z hz => desc C.le (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w))) z hz

end GlobalTheory.UseLoc.DescBD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryDescentEnlargementCoefficientsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_descent_enlargement_coefficients : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ BD (latC C (locOC C M)) → z ∈ BD (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.UseLoc.DescBD.main | exact GlobalTheory.UseLoc.DescBD.main | (intros; apply GlobalTheory.UseLoc.DescBD.main <;> assumption)
end
end

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UseLoc
open Module

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), tableLineDegreeTwo.aux₃ D HW F → tableLineDegreeTwo.adm20 D HW F → AdmissibleParameterJ.ConclusionJa D → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → 5 ≤ D.nd.l i → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ (n : ℕ) [NeZero n] (up : ZMod n → Bool) (τ : ZMod n → D.what₂.Tau), ∃ (h w η : ZMod n → ℕ) (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), tableLineDegreeTwo.PositionHyps (D.nd.l i) n D.R.t h w η typ U ∧ ∀ (a : ZMod n) (b : ℤ), ((U a).count (b + w a) = 1 ↔ (b : ℚ) ∈ AdmissibleParameterJ.JW D (up a) (D.nd.j i) (τ a)) ∧ (U a).count (b + w a) ≤ 1) → ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)) := by
  intro D HW F i r ρ π hconds hadm20 hJa hGood hπ hG2 hG3 hCont hDec hEps h5 hsm hq hd hposition w hw
  obtain ⟨C, hA, lam, hlam, θ, h, w', η, typ, U, hS⟩ :=
    GlobalTheory.T.exists_exactLocalConditionData_at_place D HW F i r ρ π hadm20 hJa hGood hπ hG2 hG3 hCont hDec hEps h5 hsm hq hd hposition w hw
  have hTop : tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) :=
    hconds (D.nd.l i) (D.nbr i w hw).Kw C.LL hA lam hlam
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.unramifiedEnlargement_cut_cocycles_blochKato D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hS hGood hπ hDec hCont
  refine ⟨?_, ?_, ?_⟩
  · have hsub : ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
        z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (WpO D.nd i ρ π)) :=
      fun z hz => GlobalTheory.T.mem_finite_part_of_lift D i w hw C D.R.r _ z (h1 z hz)
    have hle := Submodule.span_le.2 hsub
    unfold LocBound lenModN
    have h0 : Module.length (Br.OLL D.nbr i w hw)
        (↥(Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Set.univ (WpO D.nd i ρ π))) ⧸
          (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw (WpO D.nd i ρ π))).comap
            (Submodule.span (Br.OLL D.nbr i w hw) (cutCoc i w hw r Set.univ (WpO D.nd i ρ π))).subtype) = 0 := by
      rw [Module.length_eq_zero_iff, Submodule.comap_subtype_eq_top.2 hle]
      refine ⟨fun a b => ?_⟩
      induction a using Submodule.Quotient.induction_on
      induction b using Submodule.Quotient.induction_on
      exact (Submodule.Quotient.eq _).2 Submodule.mem_top
    rw [h0]
    exact zero_le
  · intro c hc z hz
    exact GlobalTheory.T.coboundary_descent_enlargement_coefficients D i w hw C 1 _ z (h2 c hc z hz)
  · intro z hz
    have := GlobalTheory.T.unramifiedCocycle_descent_enlargement D i w hw C 1 _ _ z (h3 z hz)
    rwa [← GlobalTheory.BridgeInertia.inertEq D i w hw] at this

end GlobalTheory.UseLoc
