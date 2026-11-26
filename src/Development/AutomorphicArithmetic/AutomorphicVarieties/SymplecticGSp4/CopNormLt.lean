module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoproductGeometry
theorem UpperTheory.Reformulated.B.CoproductGeometry.cop_geom :
    ∀ {R κ : Type} [inst : CommRing R] [IsNoetherianRing R]
    [inst_2 : NormedField κ] [IsUltrametricDist κ] (m : Ideal R) (y : R →+* κ),
    (∀ (x : R), ‖(y : R → κ) x‖ ≤ (1 : ℝ)) →
      (∀ x ∈ m, ‖(y : R → κ) x‖ < (1 : ℝ)) →
        ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ (n : ℕ), ∀ x ∈ m ^ n, ‖(y : R → κ) x‖ ≤ a ^ n := by
  intro R κ _ _ _ _ m y h1 hm
  classical
  have key : ∀ T : Finset R, (∀ s ∈ T, ‖y s‖ < 1) →
      ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ s ∈ T, ‖y s‖ ≤ a := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨0, by norm_num, le_rfl, by simp⟩
    | insert b T hb ih =>
      intro h
      obtain ⟨a, ha1, ha0, ha⟩ := ih (fun s hs => h s (Finset.mem_insert_of_mem hs))
      refine ⟨max a ‖y b‖, max_lt ha1 (h b (Finset.mem_insert_self _ _)),
        le_max_of_le_left ha0, ?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact le_max_right _ _
      · exact (ha s hs).trans (le_max_left _ _)
  obtain ⟨S, hS⟩ : m.FG := IsNoetherian.noetherian m
  obtain ⟨a, ha1, ha0, ha⟩ := key S (fun s hs => hm s (hS ▸ Ideal.subset_span hs))
  have hgen : ∀ z ∈ m, ‖y z‖ ≤ a := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact ha x hx
    | zero => simpa using ha0
    | add u v _ _ hu hv =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
    | smul r u _ hu =>
      rw [smul_eq_mul, map_mul, norm_mul]
      calc ‖y r‖ * ‖y u‖ ≤ 1 * a := mul_le_mul (h1 r) hu (norm_nonneg _) zero_le_one
        _ = a := one_mul a
  refine ⟨a, ha1, ha0, ?_⟩
  intro n
  induction n with
  | zero => intro x _; simpa using h1 x
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem u hu v hv =>
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih u hu) (hgen v hv) (norm_nonneg _) (pow_nonneg ha0 n)
    | add u _ v _ hu hv =>
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

open Polynomial

private theorem cop_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem cop_norm_lt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    (y : R →ₐ[ℤ_[l]] PadicAlgCl l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt y a ha

private theorem cop_coef {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h => ?_⟩
  exact ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 ((cop_intIff _).2 h), rfl⟩

private theorem cop_geom {R κ : Type} [CommRing R] [IsNoetherianRing R] [NormedField κ] [IsUltrametricDist κ]
    (m : Ideal R) (y : R →+* κ) (h1 : ∀ x, ‖y x‖ ≤ 1) (hm : ∀ x ∈ m, ‖y x‖ < 1) :
    ∃ a : ℝ, a < 1 ∧ 0 ≤ a ∧ ∀ n, ∀ x ∈ m ^ n, ‖y x‖ ≤ a ^ n :=
  _root_.UpperTheory.Reformulated.B.CoproductGeometry.cop_geom m y h1 hm

private theorem cop_bdd {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra ℤ_[l] R]
    (F : R →ₐ[ℤ_[l]] DualNumber (PadicAlgCl l)) (c : Coef l) (h1 : ∀ x, ‖(F x).fst‖ ≤ 1)
    (hc : ∀ x, (F x).fst ∈ c.O) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(F x).snd‖ ≤ C := by
  classical
  let f : R →ₐ[ℤ_[l]] c.O := ((TrivSqZeroExt.fstHom ℤ_[l] _ _).comp F).codRestrict c.O hc
  haveI : Module.Finite ℤ_[l] f.range := Module.Finite.of_injective f.range.val.toLinearMap Subtype.val_injective
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := f.range)
  choose b hb using fun i => f.rangeRestrict_surjective (s i)
  obtain ⟨P, hP⟩ : (RingHom.ker f).FG := IsNoetherian.noetherian _
  let C : NNReal := P.sup fun x => ‖(F x).snd‖₊
  have h2 : ∀ a ∈ Ideal.span (P : Set R), ‖(F a).snd‖ ≤ C := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem z hz => exact Finset.le_sup (f := fun x => ‖(F x).snd‖₊) hz
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), TrivSqZeroExt.snd_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul c x hx0 hx =>
      have h0 : (F x).fst = 0 := by
        have : x ∈ RingHom.ker f := hP ▸ hx0
        exact congrArg Subtype.val this
      rw [smul_eq_mul, map_mul, DualNumber.snd_mul, h0, mul_zero, add_zero, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (h1 c)).trans hx
  refine ⟨C + ∑ i, ‖(F (b i)).snd‖, by positivity, fun a => ?_⟩
  have hc : f.rangeRestrict a ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
  have h3 : f.rangeRestrict (a - ∑ i, u i • b i) = 0 := by simp [hb, hu]
  have h4 : a - ∑ i, u i • b i ∈ RingHom.ker f := congrArg Subtype.val h3
  have h5 := h2 _ (hP ▸ h4)
  have h6 : ‖(F (∑ i, u i • b i)).snd‖ ≤ ∑ i, ‖(F (b i)).snd‖ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, TrivSqZeroExt.snd_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul, TrivSqZeroExt.snd_smul, Algebra.smul_def, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) ((cop_intIff _).1 isIntegral_algebraMap)
  have h7 : (F a).snd = (F (a - ∑ i, u i • b i)).snd + (F (∑ i, u i • b i)).snd := by
    rw [← TrivSqZeroExt.snd_add, ← map_add (f := _), sub_add_cancel]
  rw [h7]
  exact (norm_add_le _ _).trans (add_le_add h5 h6)

private theorem cop_snd {R κ : Type} [CommRing R] [NormedField κ] [IsUltrametricDist κ]
    (m : Ideal R) (F : R →+* DualNumber κ) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (h1 : ∀ n, ∀ x ∈ m ^ n, ‖(F x).fst‖ ≤ a ^ n) (h2 : ∀ x, ‖(F x).snd‖ ≤ C) (n : ℕ) :
    ∀ x ∈ m ^ (n + 1), ‖(F x).snd‖ ≤ a ^ n * C := by
  induction n with
  | zero => intro x _; simpa using h2 x
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun u hu v hv => ?_) fun u v hu hv => ?_
    · rw [map_mul, DualNumber.snd_mul]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        exact mul_le_mul (h1 _ u hu) (h2 v) (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        have h3 := h1 1 v (by rwa [pow_one])
        calc _ ≤ (a ^ n * C) * a ^ 1 := mul_le_mul (ih u hu) h3 (norm_nonneg _) (by positivity)
          _ = _ := by ring
    · rw [map_add (f := _), TrivSqZeroExt.snd_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)

private theorem cop_main {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R]
    (F : R →ₐ[O] DualNumber (PadicAlgCl l)) :
    (∃ c' : Coef l, ∀ x, (F x).fst ∈ c'.O) ∧
    (∃ a : ℝ, a < 1 ∧ 0 ≤ a ∧ ∀ n, ∀ x ∈ maximalIdeal R ^ n, ‖(F x).fst‖ ≤ a ^ n) ∧
    (∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x, (F x).fst ∈ K ∧ (F x).snd ∈ K) ∧
    ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ maximalIdeal R ^ n, ‖(F x).snd‖ ≤ ε := by
  letI : Algebra ℤ_[l] R := ((algebraMap O R).comp (algebraMap ℤ_[l] O)).toAlgebra
  haveI : IsScalarTower ℤ_[l] O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : R →ₐ[O] PadicAlgCl l := UpperTheory.V.U3.dualFst F
  have hm : ∀ x ∈ maximalIdeal R, ‖(F x).fst‖ < 1 := cop_norm_lt (f.restrictScalars ℤ_[l])
  have h1 : ∀ x, ‖(F x).fst‖ ≤ 1 := by
    intro x
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) x
    have h2 : f x = f (x - algebraMap O R c) + algebraMap O _ c := by simp
    have h3 : IsIntegral ℤ_[l] (algebraMap O (PadicAlgCl l) c) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) c).map (IsScalarTower.toAlgHom ℤ_[l] O (PadicAlgCl l))
    show ‖f x‖ ≤ 1
    rw [h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hm _ hc).le ((cop_intIff _).1 h3))
  obtain ⟨E, hE⟩ := UpperTheory.V.Loc.ptFin (l := l) R F hm
  haveI : FiniteDimensional ℚ_[l] E.1 := E.2
  obtain ⟨c', hc'⟩ := cop_coef E.1
  have hc : ∀ x, (F x).fst ∈ c'.O := fun x => hc' _ (hE x).1 (h1 x)
  obtain ⟨a, ha1, ha0, ha⟩ := cop_geom (maximalIdeal R) (f : R →+* PadicAlgCl l) h1 hm
  refine ⟨⟨c', hc⟩, ⟨a, ha1, ha0, ha⟩, ⟨E.1, E.2, hE⟩, fun ε hε => ?_⟩
  obtain ⟨C, hC0, hC⟩ := cop_bdd (F.restrictScalars ℤ_[l]) c' h1 hc
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const C
  rw [zero_mul] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨k + 1, fun x hx =>
    (cop_snd (maximalIdeal R) (F : R →+* DualNumber (PadicAlgCl l)) ha0 hC0 ha hC k x hx).trans hk.le⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.GradeZeroInterpolatingElement.coPt :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R], (∀ y : R →ₐ[c.O] PadicAlgCl l, (∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ x, y x ∈ c'.O) ∧ ∃ a : ℝ, a < 1 ∧ 0 ≤ a ∧ ∀ n, ∀ x ∈ maximalIdeal R ^ n, ‖y x‖ ≤ a ^ n) ∧ ∀ y : R →ₐ[c.O] DualNumber (PadicAlgCl l), (∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x, (y x).fst ∈ K ∧ (y x).snd ∈ K) ∧ ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ maximalIdeal R ^ n, ‖(y x).snd‖ ≤ ε := by
  intro l _ c R _ _ _
  refine ⟨fun y => ?_, fun y => (cop_main R y).2.2⟩
  obtain ⟨⟨c', hc'⟩, h2, -⟩ := cop_main R ((TrivSqZeroExt.inlAlgHom c.O (PadicAlgCl l) (PadicAlgCl l)).comp y)
  refine ⟨⟨c', fun x hx => ?_, hc'⟩, h2⟩
  have h : y (algebraMap c.O R ⟨x, hx⟩) ∈ c'.O := hc' _
  rwa [AlgHom.commutes] at h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.GradeZeroInterpolatingElement

instance dualCO (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] :
    IsCO O (DualNumber O) := co_sqz O O O fun _ => rfl

abbrev QDer {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O) (a : O) :
    Submodule O (A →ₗ[O] O ⧸ Ideal.span {a}) := PtDer x (O ⧸ Ideal.span {a})

def Sp1 (O : Type) [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (h : M4 R) : Prop :=
  IsGSp 1 h ∧ h.map (res O R) = 1

namespace Ex

section

variable {R R' : Type} [CommRing R] [CommRing R']

theorem adj_map' (f : R →+* R') (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp [adj_apply]

theorem smul_map' (f : R →+* R') (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

theorem isGSp_map (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) : IsGSp (f ν) (f.mapMatrix g) := by
  unfold IsGSp at *
  rw [adj_map', ← map_mul, h, smul_map', map_one]

theorem aeval_map' (f : R →+* R') (X : M4 R) (p : Polynomial R) :
    Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  refine RingHom.ext fun r => ?_
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.algebraMap_eq_diagonal]
  · simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, h]

theorem prj_map (f : R →+* R') (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  simp only [prj]
  rw [← aeval_map']
  congr 1
  simp [Polynomial.map_prod]

theorem ord_map {H : Type} [Group H] (f : R →+* R') {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H}
    {r : H →* M4 R} {r' : H →* M4 R'} (hr : ∀ g, r' g = f.mapMatrix (r g)) {ps' : Fin 4 → H → R'}
    (hps : ∀ i g, ps' i g = f (ps i g)) (h : Ord I ps s₀ r) : Ord I ps' s₀ r' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hr, hps, RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  · intro g i j hij
    simp only [hr, hps]
    rw [prj_map, prj_map, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · intro s hs i
    simp only [hr, hps]
    have e : f.mapMatrix (r s) - f (ps i s) • (1 : M4 R') = f.mapMatrix (r s - ps i s • 1) := by
      rw [map_sub, smul_map', map_one]
    rw [e, prj_map, ← map_mul, ← map_mul, h.inert s hs i, map_zero]

end

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] {R' : Type} [CommRing R'] [Algebra c.O R'] [IsCO c.O R']

theorem condL_map (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt l) R) (h : D.condL R ρ) :
    D.condL R' (ρ.map f) := by
  have hm : ∀ g, (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := fun g => by
    ext a b
    exact Lift.map_hom f ρ g a b
  refine ⟨fun g => ?_, ord_map (f : R →+* R') hm (fun i g => (f.commutes _).symm) h.2⟩
  rw [hm, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h.1 g)

theorem condP_map (p : ℕ) (f : R →ₐ[c.O] R') (ρ : Lift c.O (D.rbarAt p) R) (h : D.condP p R ρ) :
    D.condP p R' (ρ.map f) := by
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · have := isGSp_map (f : R →+* R') (h.1 g)
    rw [RingHom.coe_coe, f.commutes] at this
    exact this
  · show (f : R →+* R').mapMatrix (ρ.hom g) = 1
    rw [h.2 g hg, map_one]

theorem mult_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.Mult ρ.hom) : D.Mult (ρ.map f).hom := by
  intro g
  have hm : (ρ.map f).hom g = (f : R →+* R').mapMatrix (ρ.hom g) := by
    ext a b
    exact Lift.map_hom f ρ g a b
  rw [hm, ← f.commutes]
  exact isGSp_map (f : R →+* R') (h g)

theorem unr_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (h : D.UnrT ρ.hom 1) :
    D.UnrT (ρ.map f).hom 1 := by
  intro A hA g hg h1
  show (f : R →+* R').mapMatrix (ρ.hom g) = 1
  rw [h A hA g hg h1, map_one]

theorem hEl_map (f : R →ₐ[c.O] R') (ρ : Lift c.O D.rbar R) (i j : Fin 4) :
    D.hEl (ρ.map f).hom i j = f (D.hEl ρ.hom i j) := by
  simp only [Raw.hEl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Lift.map_hom, map_add (f := _), map_mul, AlgHom.commutes]

end

end Ex

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

theorem Raw.LocEqs.map {D : Raw Ω c} {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] {R' : Type} [CommRing R']
    [Algebra c.O R'] [IsCO c.O R'] {ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) R} (h : D.LocEqs ρ) (f : R →ₐ[c.O] R') :
    D.LocEqs fun v => (ρ v).map f :=
  ⟨Ex.condL_map D f _ h.1, fun p hp => Ex.condP_map D p f _ (h.2 p hp)⟩

structure IsFr {D : Raw Ω c} (L : LocBase D) {R : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] (i : L.B →ₐ[c.O] R)
    (r : Lift c.O D.rbar R) (α : D.T → M4 R) : Prop where
  mult : D.Mult r.hom
  unr : D.UnrT r.hom 1
  sp : ∀ v, Sp1 c.O (α v)
  atL : α ⟨l, D.residueChar_mem_levelPrimes⟩ = 1
  loc : ∀ (v : D.T) (g : D.Gp v), r.hom g * α v = α v * ((L.ρ v).hom g).map i

structure Fr (D : Raw Ω c) (L : LocBase D) where
  U : Type
  [cU : CommRing U]
  [aU : Algebra c.O U]
  [coU : IsCO c.O U]
  i : L.B →ₐ[c.O] U
  r : Lift c.O D.rbar U
  α : D.T → M4 U
  fr : IsFr L i r α
  univ : ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (i' : L.B →ₐ[c.O] R) (r' : Lift c.O D.rbar R)
    (α' : D.T → M4 R), IsFr L i' r' α' → ∃! y : U →ₐ[c.O] R, y.comp i = i' ∧ r.map y = r' ∧ ∀ v, (α v).map y = α' v
  W : WPres c.O (ℤ × ℤ) U
  τ : Type
  κ : Type
  [fτ : Fintype τ]
  [fκ : Fintype κ]
  e : L.W.σ ⊕ τ ≃ W.σ
  f : κ → MvPowerSeries W.σ c.O
  wf : κ → ℤ × ℤ
  rel : IsRelPres L.W i W e f wf
  homr : ∀ g a b, r.hom g a b ∈ W.part (wt a b)
  homα : ∀ v a b, α v a b ∈ W.part (wt a b)
  vars : ∀ t, ∃ a b, W.wt (e (.inr t)) = wt a b ∧
    ((∃ g, W.z (e (.inr t)) = r.hom g a b - algebraMap c.O U (D.r0 g a b)) ∨ ∃ v, W.z (e (.inr t)) = (α v - 1) a b)
  org : W.HasOrigin
  at0r : ∀ g a b, W.origin org (r.hom g a b) = D.r0 g a b
  at0α : ∀ v, (α v).map (W.origin org) = 1
  at0i : (W.origin org).comp i = L.W.origin L.org
  numf : ∀ j, Nat.card {u // wf u = j} =
    Nat.card {t // W.wt (e (.inr t)) = j} + (if j = 0 then 2 else if j = wPs ∨ j = -wPs then 1 else 0)
  numz : ∀ j, j ≠ 0 → j ≠ wPs → j ≠ -wPs → Nat.card {t // W.wt (e (.inr t)) = j} = 0

attribute [instance] Fr.cU Fr.aU Fr.coU Fr.fτ Fr.fκ

structure Cover {O X B U : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [AddCommGroup X] [CommRing B] [Algebra O B]
    [CommRing U] [Algebra O U] (WB : WPres O X B) (hB : WB.HasOrigin) (i : B →ₐ[O] U) (W : WPres O X U) (h : W.HasOrigin)
    {τ κ : Type} (e : WB.σ ⊕ τ ≃ W.σ) (wf : κ → X) (n : X → ℕ) where
  P : Type
  [cP : CommRing P]
  [aP : Algebra O P]
  [coP : IsCO O P]
  WP : WPres O X P
  org : WP.HasOrigin
  p : P →ₐ[O] U
  iP : B →ₐ[O] P
  g : κ → P
  wts : ∀ s, ∃ s', WP.wt s = W.wt s'
  surj : Function.Surjective p
  part : ∀ j, W.part j = (WP.part j).map p.toLinearMap
  comp : p.comp iP = i
  org_p : (W.origin h).comp p = WP.origin org
  hg : ∀ u, g u ∈ WP.part (wf u)
  ker : RingHom.ker p = Ideal.span (Set.range g)
  smooth : SmoothPt WP.part (WP.origin org) fun j => n j + Nat.card {t // W.wt (e (.inr t)) = j}
  der : ∀ (a : O) (j : X), ∀ Db ∈ QDer (W.origin h) a, ∀ DB ∈ PtDer (WB.origin hB) O,
    HasWt WB.part j DB → (∀ x, Db (i x) = Ideal.Quotient.mk _ (DB x)) →
    (∀ t, W.wt (e (.inr t)) ≠ j → Db (W.z (e (.inr t))) = 0) →
    ∃ δ ∈ PtDer (WP.origin org) O, HasWt WP.part j δ ∧ ∀ y, Ideal.Quotient.mk _ (δ y) = Db (p y)

attribute [instance] Cover.cP Cover.aP Cover.coP

end UpperTheory.V.GradeZeroInterpolatingElement

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PhiGam
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  simpa [mul_assoc] using QuotientGroup.eq.1 h

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  letI : TopologicalSpace (ZMod n) := ⊥
  haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩
  have hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x := fun x => continuous_inv.smul continuous_const
  have hc : ContAction (permR (ZMod n) H) := by
    refine continuous_pi fun x => ?_
    have h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2 := continuous_of_discreteTopology
    exact h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))
  haveI h1 := h _ _ hc
  haveI : Finite (Z1 (permR (ZMod n) H)) := by
    have hB : Finite (B1 (permR (ZMod n) H)) := (Set.finite_range _).to_subtype
    have hB' : Finite ((B1 (permR (ZMod n) H)).comap (Z1 (permR (ZMod n) H)).subtype).toAddSubgroup :=
      Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : B1 (permR (ZMod n) H)))
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    exact @Finite.of_addSubgroup_quotient _ _ _ hB' h1
  have hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ := fun φ hφ =>
    continuous_of_continuousAt_one φ (by
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]
      exact hφ.mem_nhds φ.ker.one_mem)
  let c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → Z1 (permR (ZMod n) H) := fun φ =>
    ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, sec_mem H g x⟩), by
      refine ⟨continuous_pi fun x => continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩
      · exact (continuous_const.mul continuous_id).mul
          ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))
      · funext x
        rw [Pi.add_apply, permR_apply, ← toAdd_mul, ← map_mul]
        refine congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)
        simp [mul_smul, mul_assoc]⟩
  refine Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)
  let x : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hx : x.out ∈ H := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm
    simpa using this
  have hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x := by
    change (((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)
  have hu : (⟨_, sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u := by
    apply Subtype.ext
    simp only [hfix]
    group
  have := congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x
  simp only [c, hu] at this
  exact Multiplicative.toAdd.injective this

private theorem fin_above {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((n : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_span_singleton]; exact hv

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.phiGam :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → CohomologyHyp → PhiCond D.Gam l := by
  intro Ω _ _ _ l hl c D hD hP
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfin : D.SP.Finite := by
    refine (D.S.finite_toSet.biUnion fun p hp => fin_above (hD.S_prime p hp).ne_zero).subset ?_
    rintro v ⟨p, hp, hv⟩
    exact Set.mem_biUnion hp hv
  have hS : ContainsAbove hfin.toFinset l := fun v hv => hfin.mem_toFinset.2 ⟨l, hD.l_mem, hv⟩
  haveI hK : CompactSpace (GS Ω (hfin.toFinset : Set (HeightOneSpectrum (𝓞 ℚ)))) := inferInstance
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (GS Ω (hfin.toFinset : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1) :=
    phi_condition_of_finite_cohomology (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
      obtain ⟨-, f1, -⟩ := hP.gf ℚ Ω l 1 M hfin.toFinset ρ one_pos hS hρ
      exact f1
  rw [pow_one, hfin.coe_toFinset] at key
  exact key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtActInternal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ptAct_internal {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    [DecidableEq X] (𝒜 : X → Submodule O R) [SetLike.GradedMonoid 𝒜] (h : iSupIndep 𝒜) :
    DirectSum.IsInternal fun j => (𝒜 j).comap (gradedSub 𝒜).val.toLinearMap := by
  set f := (gradedSub 𝒜).val.toLinearMap with hf
  have hinj : Function.Injective f := fun a b hab => Subtype.ext hab
  have hind : iSupIndep fun j => (𝒜 j).comap f := by
    intro i
    rw [disjoint_iff_inf_le]
    have h1 : (⨆ (j) (_ : j ≠ i), (𝒜 j).comap f) ≤ (⨆ (j) (_ : j ≠ i), 𝒜 j).comap f :=
      iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => 𝒜 j) j hj)
    calc (𝒜 i).comap f ⊓ ⨆ (j) (_ : j ≠ i), (𝒜 j).comap f
        ≤ (𝒜 i).comap f ⊓ (⨆ (j) (_ : j ≠ i), 𝒜 j).comap f := inf_le_inf_left _ h1
      _ = (𝒜 i ⊓ ⨆ (j) (_ : j ≠ i), 𝒜 j).comap f := (Submodule.comap_inf _ _ _).symm
      _ = ⊥ := by rw [(h i).eq_bot, Submodule.comap_bot, LinearMap.ker_eq_bot.2 hinj]
      _ ≤ ⊥ := le_rfl
  have hr : LinearMap.range f = ⨆ j, 𝒜 j := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have htop : ⨆ j, (𝒜 j).comap f = ⊤ := by
    apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_iSup, Submodule.map_top]
    simp_rw [Submodule.map_comap_eq, hr]
    exact le_antisymm (iSup_le fun j => inf_le_left)
      (iSup_le fun j => le_trans (le_inf (le_iSup 𝒜 j) le_rfl) (le_iSup (fun k => (⨆ j, 𝒜 j) ⊓ 𝒜 k) j))
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨hind, htop⟩

private def UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr {K : Type} [CommRing K] (t : Kˣ × Kˣ) : Multiplicative (ℤ × ℤ) →* Kˣ where
  toFun w := wv t w.toAdd
  map_one' := by simp [wv]
  map_mul' a b := by
    simp only [wv, toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptAct :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ (K : Type) [CommRing K] [Algebra c.O K] (ξ : M.SS →ₐ[c.O] K) (t : Kˣ × Kˣ), ∃ ξ' : M.SS →ₐ[c.O] K, (∀ g, M.rep ξ' g = tconj t (M.rep ξ g)) ∧ ∀ w (f : M.SS), f.1 ∈ M.sPart w → ξ' f = (wv t w : K) * ξ f := by
  intro Ω _ _ _ l _ c D hD M K _ _ ξ t
  let 𝒜' : ℤ × ℤ → Submodule c.O M.SS := fun j => (M.sPart j).comap M.SS.val.toLinearMap
  have hint : DirectSum.IsInternal 𝒜' := UpperTheory.V.GradeZeroInterpolatingElement.ptAct_internal M.sPart (sInternal D hD M).1
  letI hgm : SetLike.GradedMonoid 𝒜' :=
    { one_mem := by
        show ((1 : M.SS) : M.S) ∈ M.sPart 0
        exact SetLike.GradedOne.one_mem
      mul_mem := fun i j a b ha hb => by
        show ((a * b : M.SS) : M.S) ∈ M.sPart (i + j)
        exact SetLike.GradedMul.mul_mem ha hb }
  letI : DirectSum.Decomposition 𝒜' := hint.chooseDecomposition
  letI : GradedAlgebra 𝒜' := { hgm, (inferInstance : DirectSum.Decomposition 𝒜') with }
  have key : ∀ w (f : M.SS), f.1 ∈ M.sPart w →
      act 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ f = (wv t w : K) * ξ f :=
    fun w f hf => act_of_mem 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ (j := w) hf
  refine ⟨act 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ, fun g => ?_, key⟩
  ext i j
  show act 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ (M.ent g i j) = (wv t (wt i j) : K) * ξ (M.ent g i j)
  exact key _ _ (M.entry_mem g i j)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtLift
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem pt_of_ft {K C : Type} [Field K] [IsAlgClosed K] [CommRing C] [Algebra K C] [Nontrivial C]
    [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (C ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)
  haveI : Algebra.IsIntegral K (C ⧸ m) := Algebra.IsIntegral.of_finite K _
  have hb : Function.Bijective (algebraMap K (C ⧸ m)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨((AlgEquiv.ofBijective (Algebra.ofId K (C ⧸ m)) hb).symm : (C ⧸ m) →ₐ[K] K).comp
    (Ideal.Quotient.mkₐ K m)⟩

private theorem pt_of_lin {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K] [Algebra A B]
    [Algebra A K] [Algebra.FiniteType A B] (ρ : B →ₗ[A] K) (h : ρ 1 = 1) : Nonempty (B →ₐ[A] K) := by
  classical
  let f : TensorProduct A K B →ₗ[A] K := TensorProduct.lift ((LinearMap.mul A K).compl₂ ρ)
  have hf : f 1 = 1 := by
    rw [Algebra.TensorProduct.one_def]
    simp [f, h]
  haveI : Nontrivial (TensorProduct A K B) := by
    refine ⟨⟨1, 0, fun h0 => ?_⟩⟩
    have h1 := congrArg f h0
    rw [hf, map_zero] at h1
    exact one_ne_zero h1
  haveI : Algebra.FiniteType K (TensorProduct A K B) := Algebra.FiniteType.baseChange K
  obtain ⟨φ⟩ := pt_of_ft (K := K) (C := TensorProduct A K B)
  exact ⟨(φ.restrictScalars A).comp Algebra.TensorProduct.includeRight⟩

private theorem ext_of_proj {O A B K : Type} [CommRing O] [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
    [Algebra O A] [Algebra O B] [Algebra O K] (φ : A →ₐ[O] B) (x : A →ₐ[O] K) (hk : ∀ f, φ f = 0 → x f = 0)
    (P : B →+ B) (hP : ∀ f s, P (φ f * s) = φ f * P s) (hr : ∀ s, ∃ f, φ f = P s) (h1 : P 1 = 1)
    (s : Set B) (hs : s.Finite) (hg : Algebra.adjoin O (Set.range φ ∪ s) = ⊤) :
    ∃ ξ : B →ₐ[O] K, ξ.comp φ = x := by
  classical
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra A K := x.toRingHom.toAlgebra
  have hwd : ∀ f g, φ f = φ g → x f = x g := fun f g hfg => by
    have h0 := hk (f - g) (by rw [map_sub, hfg, sub_self])
    rwa [map_sub, sub_eq_zero] at h0
  choose pre hpre using hr
  have hO : ∀ r : O, algebraMap O B r = algebraMap A B (algebraMap O A r) := fun r => by
    show algebraMap O B r = φ (algebraMap O A r)
    rw [AlgHom.commutes]
  let ρ : B →ₗ[A] K :=
    { toFun := fun t => x (pre t)
      map_add' := fun t u => by
        rw [← map_add (f := _)]
        apply hwd
        rw [map_add (f := _), hpre, hpre, hpre, map_add (f := _)]
      map_smul' := fun a t => by
        show x (pre (a • t)) = x a * x (pre t)
        rw [← map_mul]
        apply hwd
        rw [hpre, map_mul, hpre, Algebra.smul_def]
        exact hP a t }
  have h1' : ρ 1 = 1 := by
    show x (pre 1) = 1
    rw [← map_one x]
    apply hwd
    rw [hpre, h1, map_one]
  haveI : Algebra.FiniteType A B := by
    refine ⟨⟨hs.toFinset, ?_⟩⟩
    rw [eq_top_iff]
    rintro b -
    have hb : b ∈ Algebra.adjoin O (Set.range φ ∪ s) := by
      rw [hg]
      trivial
    rw [Set.Finite.coe_toFinset]
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨f, rfl⟩ | hy
      · exact Subalgebra.algebraMap_mem _ f
      · exact Algebra.subset_adjoin hy
    | algebraMap r =>
      rw [hO]
      exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  obtain ⟨ψ⟩ := pt_of_lin ρ h1'
  refine ⟨{ toRingHom := ψ.toRingHom, commutes' := fun r => ?_ }, ?_⟩
  · show ψ (algebraMap O B r) = algebraMap O K r
    rw [hO, ψ.commutes]
    exact x.commutes r
  · ext f
    exact ψ.commutes f

private theorem exists_proj {O S X : Type} [CommRing O] [AddCommGroup S] [Module O S] (𝒜 : X → Submodule O S)
    (h : iSupIndep 𝒜) (p : X → Prop) [DecidablePred p] :
    ∃ P : S → S, P 0 = 0 ∧ (∀ a ∈ ⨆ j, 𝒜 j, ∀ b ∈ ⨆ j, 𝒜 j, P (a + b) = P a + P b) ∧
      ∀ j, ∀ a ∈ 𝒜 j, P a = if p j then a else 0 := by
  classical
  let L := DFinsupp.lsum ℕ (fun i => (𝒜 i).subtype)
  let Q := DFinsupp.lsum ℕ (fun i => if p i then (𝒜 i).subtype else (0 : 𝒜 i →ₗ[O] S))
  have hL : Function.Injective L := h.dfinsupp_lsum_injective
  let P : S → S := fun t => if ht : ∃ y, L y = t then Q ht.choose else 0
  have hP : ∀ y, P (L y) = Q y := fun y => by
    have ht : ∃ y', L y' = L y := ⟨y, rfl⟩
    show (if ht : ∃ y', L y' = L y then Q ht.choose else 0) = Q y
    rw [dite_eq_left ht, hL ht.choose_spec]
  have hmem : ∀ a ∈ ⨆ j, 𝒜 j, ∃ y, L y = a := fun a ha => by
    rw [Submodule.iSup_eq_range_dfinsupp_lsum] at ha
    exact LinearMap.mem_range.1 ha
  refine ⟨P, ?_, ?_, ?_⟩
  · have h0 := hP 0
    rwa [map_zero, map_zero] at h0
  · intro a ha b hb
    obtain ⟨ya, rfl⟩ := hmem a ha
    obtain ⟨yb, rfl⟩ := hmem b hb
    rw [← map_add (f := _), hP, hP, hP, map_add (f := _)]
  · intro j a ha
    have e : L (DFinsupp.single j ⟨a, ha⟩) = a := by
      simp [L]
    conv_lhs => rw [← e]
    rw [hP]
    simp only [Q, DFinsupp.lsum_single]
    split_ifs <;> simp

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptLift :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ x : M.A →ₐ[c.O] PadicAlgCl l, OnS M.eqns.ideal x → ∃ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ.comp M.toSS = x := by
  intro Ω _ _ _ l _ c D hD M x hx
  obtain ⟨hind, ⟨s, hs1, hs2⟩, -⟩ := sInternal D hD M
  obtain ⟨hk1, hk2, -⟩ := kerA D hD M
  obtain ⟨P, hP0, hPadd, hPj⟩ := exists_proj M.sPart hind (fun j : ℤ × ℤ => j.1 = 0)
  have hz0 : ((M.toSS 0 : M.SS) : M.S) = 0 := by
    have e0 : M.toSS 0 = 0 := M.toSS.map_zero
    rw [e0]
    rfl
  have hPS : ∀ y ∈ ⨆ j, M.sPart j, P y ∈ ⨆ j, M.sPart j ∧ ∃ f : M.A, (M.toSS f : M.S) = P y := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem j y hy =>
      rw [hPj j y hy]
      split_ifs with hj
      · refine ⟨Submodule.mem_iSup_of_mem j hy, ?_⟩
        obtain ⟨j1, j2⟩ := j
        simp only at hj
        subst hj
        obtain ⟨f, -, hf⟩ := hk2 j2 ⟨y, M.sPart_le hy⟩ hy
        exact ⟨f, congrArg Subtype.val hf⟩
      · exact ⟨zero_mem _, 0, hz0⟩
    | zero =>
      rw [hP0]
      exact ⟨zero_mem _, 0, hz0⟩
    | add a b ha hb iha ihb =>
      rw [hPadd a ha b hb]
      obtain ⟨h1, f1, hf1⟩ := iha
      obtain ⟨h2, f2, hf2⟩ := ihb
      refine ⟨add_mem h1 h2, f1 + f2, ?_⟩
      have e : M.toSS (f1 + f2) = M.toSS f1 + M.toSS f2 := M.toSS.map_add f1 f2
      rw [← hf1, ← hf2, e]
      rfl
  have hπm : ∀ g ∈ ⨆ n, M.aPart n, ∀ y ∈ ⨆ j, M.sPart j, M.π g * y ∈ ⨆ j, M.sPart j :=
    fun g hg y hy => M.SS.mul_mem (M.π_mem ⟨g, hg⟩) hy
  have hPmul : ∀ g ∈ ⨆ n, M.aPart n, ∀ y ∈ ⨆ j, M.sPart j, P (M.π g * y) = M.π g * P y := by
    intro g hg
    induction hg using Submodule.iSup_induction' with
    | mem n g hg =>
      intro y hy
      have hg' : g ∈ ⨆ n, M.aPart n := Submodule.mem_iSup_of_mem n hg
      induction hy using Submodule.iSup_induction' with
      | mem j y hy =>
        have hπ : M.π g ∈ M.sPart (0, n) := Submodule.mem_map_of_mem (f := M.π.toLinearMap) hg
        have hgy : M.π g * y ∈ M.sPart ((0, n) + j) := SetLike.GradedMul.mul_mem hπ hy
        rw [hPj _ _ hgy, hPj _ _ hy]
        simp only [Prod.fst_add, zero_add]
        split_ifs <;> simp
      | zero => rw [mul_zero, hP0, mul_zero]
      | add a b ha hb iha ihb =>
        rw [mul_add, hPadd _ (hπm g hg' a ha) _ (hπm g hg' b hb), iha, ihb, hPadd a ha b hb, mul_add]
    | zero =>
      intro y hy
      have e0 : M.π 0 = 0 := M.π.map_zero
      rw [e0, zero_mul, hP0, zero_mul]
    | add g h hg hh ihg ihh =>
      intro y hy
      have e : M.π (g + h) = M.π g + M.π h := M.π.map_add g h
      rw [e, add_mul, hPadd _ (hπm g hg y hy) _ (hπm h hh y hy), ihg y hy, ihh y hy, add_mul]
  let P' : M.SS →+ M.SS :=
    { toFun := fun y => ⟨P y.1, (hPS y.1 y.2).1⟩
      map_zero' := Subtype.ext hP0
      map_add' := fun a b => Subtype.ext (hPadd _ a.2 _ b.2) }
  have h1P : P 1 = 1 := by
    have h1 := hPj 0 1 SetLike.GradedOne.one_mem
    simpa using h1
  let s' : Set M.SS := Subtype.val ⁻¹' (s : Set M.S)
  have hs' : s'.Finite := s.finite_toSet.preimage Subtype.val_injective.injOn
  set_option synthInstance.maxHeartbeats 200000 in
  have hgen : Algebra.adjoin c.O (Set.range M.toSS ∪ s') = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have key : Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ (s : Set M.S)) ≤
        (Algebra.adjoin c.O (Set.range M.toSS ∪ s')).map M.SS.val := by
      apply Algebra.adjoin_le
      rintro z (hz | hz)
      · obtain ⟨f, -, hf⟩ := hk2 0 ⟨z, M.sPart_le hz⟩ hz
        exact Subalgebra.mem_map.2 ⟨⟨z, M.sPart_le hz⟩, Algebra.subset_adjoin (Or.inl ⟨f, hf⟩), rfl⟩
      · obtain ⟨w, hw⟩ := hs1 z hz
        exact Subalgebra.mem_map.2 ⟨⟨z, M.sPart_le hw⟩, Algebra.subset_adjoin (Or.inr hz), rfl⟩
    have hy : (y : M.S) ∈ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ (s : Set M.S)) := by
      rw [hs2]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := Subalgebra.mem_map.1 (key hy)
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hz
  exact ext_of_proj M.toSS x (fun f hf => hx f ((hk1 f).1 hf)) P'
    (fun f y => Subtype.ext (hPmul f.1 f.2 y.1 y.2))
    (fun y => ⟨(hPS y.1 y.2).2.choose, Subtype.ext (hPS y.1 y.2).2.choose_spec⟩)
    (Subtype.ext h1P) s' hs' hgen
end
