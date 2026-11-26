module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftVal
open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
private theorem pow_finrank_aut {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    (s : K ≃ₐ[k] K) : s ^ Module.finrank k K = 1 := by
  classical
  have h1 : Nat.card (⊤ : Subgroup (K ≃ₐ[k] K)) ∣ Module.finrank k K := by
    rw [← IntermediateField.finrank_fixedField_eq_card,
      ← (letI : Module.Free (IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K))) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank k (IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K))) K)]
    exact dvd_mul_left _ _
  rw [Subgroup.card_top] at h1
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard s).trans h1)

private theorem partial_twConj {k K : Type} [Field k] [Field K] [Algebra k K] (s : K ≃ₐ[k] K) (n : ℕ)
    (δ g : GL (Fin n) K) (m : ℕ) :
    (List.ofFn fun j : Fin m => GlobalTheory.LBC.galAct (s ^ (j : ℕ)) n (g⁻¹ * δ * GlobalTheory.LBC.galAct s n g)).prod =
      g⁻¹ * (List.ofFn fun j : Fin m => GlobalTheory.LBC.galAct (s ^ (j : ℕ)) n δ).prod * GlobalTheory.LBC.galAct (s ^ m) n g := by
  induction m with
  | zero => simp [GlobalTheory.LBC.galAct_one]
  | succ m ih =>
    rw [List.ofFn_succ', List.ofFn_succ', List.prod_concat, List.prod_concat]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    have e : GlobalTheory.LBC.galAct (s ^ m) n (GlobalTheory.LBC.galAct s n g) = GlobalTheory.LBC.galAct (s ^ (m + 1)) n g := by
      rw [pow_succ, GlobalTheory.LBC.galAct_mul, MonoidHom.comp_apply]
    rw [map_mul, map_mul, map_inv, e]
    group

private theorem norm_tw {k K : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] (s : K ≃ₐ[k] K)
    (n : ℕ) (δ g : GL (Fin n) K) :
    GlobalTheory.LBC.norm k s (g⁻¹ * δ * GlobalTheory.LBC.galAct s n g) = g⁻¹ * GlobalTheory.LBC.norm k s δ * g := by
  unfold GlobalTheory.LBC.norm
  rw [partial_twConj, pow_finrank_aut, GlobalTheory.LBC.galAct_one, MonoidHom.id_apply]

private theorem fb_eq_of_isFinNorm {F₀ F₁ : Type} [Field F₀] [Field F₁] [Algebra F₀ F₁] [Finite F₁]
    (sb : F₁ ≃ₐ[F₀] F₁) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (hfb : ∀ a b, fb (b⁻¹ * a * b) = fb a)
    {δ : GL (Fin n) F₁} {γ γ' : GL (Fin n) F₀} (h : IsFinNorm sb δ γ) (h' : IsFinNorm sb δ γ') :
    fb γ' = fb γ := by
  have hc : IsConj γ' γ := GlobalTheory.Shin.isConj_of_isConj_incl F₀ F₁ n γ' γ (h'.trans h.symm)
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have := hfb γ' c⁻¹
  rw [inv_inv] at this
  rw [← this, hc]

end UpperTheory.Gal.InertialTypesAlt.L

theorem UpperTheory.Gal.InertialTypesAlt.L.liftVal :
    UpperTheory.Gal.InertialTypesAlt.L.LiftVal := by
  intro F₀ F₁ _ _ _ _ _ sb _ n fb hfb
  haveI : FiniteDimensional F₀ F₁ := Module.Finite.of_finite
  refine ⟨fun δ γ h => ?_, fun δ x => ?_⟩
  · have hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ := ⟨γ, h⟩
    rw [GlobalTheory.DZA.normLift, dite_eq_left hex]
    exact UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb h hex.choose_spec
  · have hiff : ∀ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ ↔ GlobalTheory.DZA.IsFinNorm sb δ γ := by
      intro γ
      have hc : IsConj (GlobalTheory.LBC.norm F₀ sb δ) (GlobalTheory.LBC.norm F₀ sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x)) := by
        rw [UpperTheory.Gal.InertialTypesAlt.L.norm_tw]
        refine isConj_iff.mpr ⟨x⁻¹, ?_⟩
        simp
      exact ⟨fun h => IsConj.trans h hc.symm, fun h => IsConj.trans h hc⟩
    have hfun : (fun γ => GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ) =
        fun γ => GlobalTheory.DZA.IsFinNorm sb δ γ := funext fun γ => propext (hiff γ)
    by_cases hex : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ
    · obtain ⟨γ, hγ⟩ := hex
      have h1 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb δ γ := ⟨γ, hγ⟩
      have h2 : ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ := ⟨γ, (hiff γ).2 hγ⟩
      rw [GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dite_eq_left h1, dite_eq_left h2]
      exact (UpperTheory.Gal.InertialTypesAlt.L.fb_eq_of_isFinNorm sb fb hfb ((hiff _).1 h2.choose_spec) h1.choose_spec).symm
    · have h2 : ¬ ∃ γ, GlobalTheory.DZA.IsFinNorm sb (x⁻¹ * δ * GlobalTheory.LBC.galAct sb n x) γ :=
        fun ⟨γ, hγ⟩ => hex ⟨γ, (hiff γ).1 hγ⟩
      rw [GlobalTheory.DZA.normLift, GlobalTheory.DZA.normLift, dite_eq_right hex, dite_eq_right h2]
end

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Val

variable {k K : Type} [Field k] [ValuativeRel k] [Field K] [ValuativeRel K] [Algebra k K]
  [ValuativeExtension k K]

private theorem val_le_one_iff (x : k) :
    valuation K (algebraMap k K x) ≤ 1 ↔ valuation k x ≤ 1 := by
  rw [← ValuativeExtension.mapValueGroupWithZero_valuation,
    ← (ValuativeExtension.mapValueGroupWithZero k K).map_one]
  exact ValuativeExtension.mapValueGroupWithZero_strictMono.le_iff_le

private theorem val_eq_one_of_alg {x : k} (hx : valuation K (algebraMap k K x) = 1) :
    valuation k x = 1 := by
  rw [← ValuativeExtension.mapValueGroupWithZero_valuation,
    ← (ValuativeExtension.mapValueGroupWithZero k K).map_one] at hx
  exact ValuativeExtension.mapValueGroupWithZero_strictMono.injective hx

end Val

section Int

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra k K]
  [ValuativeExtension k K]

private theorem incl_mem_iff (n : ℕ) (g : GL (Fin n) k) : incl K n g ∈ KO K n ↔ g ∈ KO k n := by
  have hmem : ∀ x : k, algebraMap k K x ∈ 𝒪[K] ↔ x ∈ 𝒪[k] := fun x => by
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
    exact val_le_one_iff x
  change incl K n g ∈ GroundTheory.Automorphic.GLnLocal.integralGL K n ↔
    g ∈ GroundTheory.Automorphic.GLnLocal.integralGL k n
  rw [GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff, GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff,
    ← map_inv]
  simp only [GlobalTheory.LBC.incl_apply, hmem]

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
private theorem intEl_of_conj (n : ℕ) (γ : GL (Fin n) k) (g : GL (Fin n) K)
    (hg : g⁻¹ * incl K n γ * g ∈ KO K n) : IntEl γ := by
  obtain ⟨y, hy⟩ := hg
  have hM : ((g⁻¹ * incl K n γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (y : Matrix (Fin n) (Fin n) 𝒪[K]).map (algebraMap 𝒪[K] K) := by
    rw [← hy]
    rfl
  have hγ : ((incl K n γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k K) := by
    ext i j
    simp [GlobalTheory.LBC.incl_apply]
  have hinv : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    simp
  have hchar : ((γ : Matrix (Fin n) (Fin n) k).charpoly).map (algebraMap k K) =
      ((y : Matrix (Fin n) (Fin n) 𝒪[K]).charpoly).map (algebraMap 𝒪[K] K) := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, ← hM, Units.val_mul, Units.val_mul,
      Matrix.charpoly_mul_comm, ← mul_assoc, hinv, one_mul, hγ]
  have hdet : algebraMap k K (γ : Matrix (Fin n) (Fin n) k).det =
      algebraMap 𝒪[K] K (y : Matrix (Fin n) (Fin n) 𝒪[K]).det := by
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← hM,
      ← hγ, Units.val_mul, Units.val_mul, Matrix.det_units_conj']
  constructor
  · intro i
    rw [← val_le_one_iff (K := K)]
    have h := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hchar
    simp only [Polynomial.coeff_map] at h
    rw [h]
    exact (Valuation.mem_integer_iff _ _).1 ((y : Matrix (Fin n) (Fin n) 𝒪[K]).charpoly.coeff i).2
  · apply val_eq_one_of_alg (K := K)
    rw [hdet]
    exact (Valuation.integer.integers _).one_of_isUnit (y.isUnit.map Matrix.detMonoidHom)

end Int

section Norm

variable {k K : Type} [Field k] [Field K] [Algebra k K]

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
private theorem aut_pow_finrank [FiniteDimensional k K] (s : K ≃ₐ[k] K) :
    s ^ Module.finrank k K = 1 := by
  have h1 := IntermediateField.finrank_fixedField_eq_card (F := k) (E := K) (Subgroup.zpowers s)
  rw [Nat.card_zpowers] at h1
  rw [← (letI : Module.Free (IntermediateField.fixedField (Subgroup.zpowers s)) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank k (IntermediateField.fixedField (Subgroup.zpowers s)) K), h1,
    pow_mul', pow_orderOf_eq_one, one_pow]

private theorem ofFn_twConj (s : K ≃ₐ[k] K) (n : ℕ) (δ g : GL (Fin n) K) (m : ℕ) :
    (List.ofFn fun j : Fin m => galAct (s ^ (j : ℕ)) n (g⁻¹ * δ * galAct s n g)).prod =
      g⁻¹ * (List.ofFn fun j : Fin m => galAct (s ^ (j : ℕ)) n δ).prod * galAct (s ^ m) n g := by
  induction m with
  | zero => simp [galAct_one]
  | succ m ih =>
    simp only [List.ofFn_succ', List.prod_concat, Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    simp only [map_mul, map_inv]
    rw [pow_succ, galAct_mul, MonoidHom.comp_apply]
    group

private theorem norm_twConj [FiniteDimensional k K] (s : K ≃ₐ[k] K) (n : ℕ) (δ g : GL (Fin n) K) :
    GlobalTheory.LBC.norm k s (g⁻¹ * δ * galAct s n g) = g⁻¹ * GlobalTheory.LBC.norm k s δ * g := by
  unfold GlobalTheory.LBC.norm
  rw [ofFn_twConj, aut_pow_finrank, galAct_one, MonoidHom.id_apply]

end Norm

section Lift

variable {K : Type} [Field K] [ValuativeRel K] {k F₀ F₁ : Type} [Field k] [Algebra k K] [Field F₀]
  [Field F₁] [Algebra F₀ F₁] {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁} {n : ℕ}

private theorem lift_pow
    (hf : ∀ y : GL (Fin n) 𝒪[K], ∃ y' : GL (Fin n) 𝒪[K],
      GeneralLinearGroup.map (algebraMap 𝒪[K] K) y' = galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) ∧
      GeneralLinearGroup.map rK y' = galAct sb n (GeneralLinearGroup.map rK y))
    (j : ℕ) (y : GL (Fin n) 𝒪[K]) : ∃ y' : GL (Fin n) 𝒪[K],
      GeneralLinearGroup.map (algebraMap 𝒪[K] K) y' =
        galAct (s ^ j) n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) ∧
      GeneralLinearGroup.map rK y' = galAct (sb ^ j) n (GeneralLinearGroup.map rK y) := by
  induction j generalizing y with
  | zero => exact ⟨y, by simp [galAct_one], by simp [galAct_one]⟩
  | succ j ih =>
    obtain ⟨y1, h1, h2⟩ := hf y
    obtain ⟨y2, h3, h4⟩ := ih y1
    refine ⟨y2, ?_, ?_⟩
    · rw [h3, h1, pow_succ, galAct_mul, MonoidHom.comp_apply]
    · rw [h4, h2, pow_succ, galAct_mul, MonoidHom.comp_apply]

private theorem lift_prod
    (hf : ∀ y : GL (Fin n) 𝒪[K], ∃ y' : GL (Fin n) 𝒪[K],
      GeneralLinearGroup.map (algebraMap 𝒪[K] K) y' = galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) ∧
      GeneralLinearGroup.map rK y' = galAct sb n (GeneralLinearGroup.map rK y))
    (y : GL (Fin n) 𝒪[K]) (m : ℕ) : ∃ z : GL (Fin n) 𝒪[K],
      GeneralLinearGroup.map (algebraMap 𝒪[K] K) z =
        (List.ofFn fun j : Fin m =>
          galAct (s ^ (j : ℕ)) n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y)).prod ∧
      GeneralLinearGroup.map rK z =
        (List.ofFn fun j : Fin m => galAct (sb ^ (j : ℕ)) n (GeneralLinearGroup.map rK y)).prod := by
  induction m with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨z, h1, h2⟩ := ih
    obtain ⟨y', h3, h4⟩ := lift_pow hf m y
    refine ⟨z * y', ?_, ?_⟩
    · simp only [List.ofFn_succ', List.prod_concat, Fin.coe_castSucc, Fin.val_last, map_mul, h1, h3]
    · simp only [List.ofFn_succ', List.prod_concat, Fin.coe_castSucc, Fin.val_last, map_mul, h2, h4]

end Lift

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.redNorm :
    UpperTheory.Gal.InertialTypesAlt.L.RedNorm := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb hres n
  obtain ⟨-, hfr⟩ := frobFacts k K F₀ F₁ rk rK s sb hres
  obtain ⟨-, -, hlift⟩ := hfr n
  obtain ⟨-, -, -, -, hformK, hsuppK⟩ := inflFacts K F₁ rK hres.onto₁ n
  obtain ⟨-, -, -, -, hformk, -⟩ := inflFacts k F₀ rk hres.onto₀ n
  have hnormKO : ∀ β ∈ KO K n, GlobalTheory.LBC.norm k s β ∈ KO K n := by
    rintro β ⟨y, rfl⟩
    obtain ⟨z, hz, -⟩ := lift_prod hlift y (Module.finrank k K)
    exact ⟨z, hz⟩
  refine ⟨fun h => incl_mem_iff n h, hnormKO, fun β g => norm_twConj s n β g,
    fun γ g hg => intEl_of_conj n γ g hg, ?_⟩
  intro fb hfb
  obtain ⟨hlv1, hlv2⟩ := liftVal F₀ F₁ sb hres.frob n fb hfb
  refine ⟨?_, ?_⟩
  · intro β hβ γ hγ
    have hγmem : γ ∈ KO k n := (incl_mem_iff n γ).1 (hγ ▸ hnormKO β hβ)
    obtain ⟨y, rfl⟩ := hβ
    obtain ⟨x, rfl⟩ := hγmem
    rw [hformK, hformk]
    apply hlv1
    obtain ⟨z, hz1, hz2⟩ := lift_prod hlift y (Module.finrank F₀ F₁)
    have hz1' : GeneralLinearGroup.map (algebraMap 𝒪[K] K) z =
        incl K n (GeneralLinearGroup.map (algebraMap 𝒪[k] k) x) := by
      rw [hz1, ← hγ, hres.deg]
      rfl
    have hzx : GeneralLinearGroup.map rK z = incl F₁ n (GeneralLinearGroup.map rk x) := by
      ext i j
      have h := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K) i j) hz1'
      simp only [incl_apply] at h ⊢
      exact hres.inc _ _ h
    show IsConj _ _
    rw [show GlobalTheory.LBC.norm F₀ sb (GeneralLinearGroup.map rK y) = GeneralLinearGroup.map rK z from hz2.symm,
      hzx]
  · intro κ hκ y
    have hsκ : galAct s n κ ∈ KO K n := by
      obtain ⟨u, rfl⟩ := hκ
      obtain ⟨u', hu1, -⟩ := hlift u
      exact ⟨u', hu1⟩
    by_cases hy : y ∈ KO K n
    · obtain ⟨w, rfl⟩ := hy
      obtain ⟨u, rfl⟩ := hκ
      obtain ⟨u', hu1, hu2⟩ := hlift u
      rw [← hu1, ← map_inv, ← map_mul, ← map_mul, hformK, hformK, map_mul, map_mul, map_inv, hu2]
      exact hlv2 _ _
    · have hy' : κ⁻¹ * y * galAct s n κ ∉ KO K n := by
        intro h
        apply hy
        have hy2 : y = κ * (κ⁻¹ * y * galAct s n κ) * (galAct s n κ)⁻¹ := by group
        rw [hy2]
        exact mul_mem (mul_mem hκ h) (inv_mem hsκ)
      have h0 : ∀ x, x ∉ KO K n → infl rK (normLift sb fb) x = 0 := fun x hx =>
        by_contra fun h => hx ((hsuppK (normLift sb fb)).2.2 x h)
      rw [h0 _ hy, h0 _ hy']
