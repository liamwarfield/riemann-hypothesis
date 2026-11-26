module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecValEqIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.FiniteCover

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']

abbrev toField {U : X.Opens} (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U (genericPoint X) h).hom

theorem generic_mem {U : X.Opens} {x : X} (h : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, h⟩

theorem generic_inf {U V : X.Opens} (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V) :
    genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩

theorem generic_top : genericPoint X ∈ (⊤ : X.Opens) := trivial

theorem toField_rs {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (a : Γ(X, U)) :
    toField hV (rs X h a) = toField (h hV) a :=
  X.presheaf.germ_res_apply (homOfLE h) _ hV a

theorem toField_injective {U : X.Opens} (h : genericPoint X ∈ U) :
    Function.Injective (toField h) := germ_injective_of_isIntegral X _ h

theorem exists_toField_eq {D : X.Opens} (hD : genericPoint X ∈ D) {I : Type} (O : I → X.Opens)
    (hO : ∀ a, O a ≤ D) (hc : D ≤ ⨆ a, O a) (hη : ∀ a, genericPoint X ∈ O a) (x : X.functionField)
    (hx : ∀ a, ∃ y, toField (hη a) y = x) : ∃ y, toField hD y = x := by
  choose y hy using hx
  obtain ⟨z, hz, -⟩ := X.sheaf.existsUnique_gluing' O D (fun a => homOfLE (hO a)) hc y
    fun a b => toField_injective (U := O a ⊓ O b) (generic_inf (hη a) (hη b))
      (((toField_rs inf_le_left _ _).trans (hy a)).trans ((toField_rs inf_le_right _ _).trans (hy b)).symm)
  obtain ⟨a, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hD)
  exact ⟨z, (toField_rs (hO a) (hη a) z).symm.trans ((congrArg _ (hz a)).trans (hy a))⟩

theorem toField_appLE (φ : X' ⟶ X) [IsDominant φ] {U : X.Opens} {V : X'.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (hU : genericPoint X ∈ U) (hV : genericPoint X' ∈ V) (a : Γ(X, U)) :
    toField hV ((φ.appLE U V e).hom a) = functionFieldMap φ (toField hU a) := by
  have h₁ : toField hV ((φ.appLE U V e).hom a) = toField (e hV) ((φ.app U).hom a) :=
    toField_rs e hV _
  rw [h₁, functionFieldMap, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (Scheme.Hom.germ_stalkMap_apply φ U (genericPoint X') (e hV) a).symm

variable {M : LB X} {k₀ : M.ι} (h₀ : genericPoint X ∈ M.U k₀)

def secVal {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) : X.functionField :=
  toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀)) (GlobalTheory.LB.coord σ k₀)

theorem toField_coord {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) {k : M.ι}
    (hk : genericPoint X ∈ M.U k) :
    toField (U := V ⊓ M.U k) (generic_inf (hV) (hk)) (GlobalTheory.LB.coord σ k) =
      toField (U := M.U k ⊓ M.U k₀) (generic_inf (hk) (h₀)) (M.g k k₀).val * secVal h₀ hV σ := by
  have e := congrArg (toField (U := V ⊓ M.U k ⊓ M.U k₀) (generic_inf (generic_inf hV hk) h₀))
    (SecOn.compat σ k k₀ (O := V ⊓ M.U k ⊓ M.U k₀) inf_le_left (inf_le_inf_right _ inf_le_left)
      (inf_le_inf_right _ inf_le_right))
  rw [map_mul, toField_rs, toField_rs, toField_rs] at e
  exact e

theorem secVal_injective {V : X.Opens} (hV : genericPoint X ∈ V) :
    Function.Injective (secVal h₀ hV) := fun σ τ h => GlobalTheory.LB.sec_ext fun k => by
  by_cases hk : genericPoint X ∈ M.U k
  · refine toField_injective (U := V ⊓ M.U k) (generic_inf (hV) (hk)) ?_
    rw [toField_coord h₀ hV σ hk, toField_coord h₀ hV τ hk, h]
  · have : V ⊓ M.U k = ⊥ := eq_bot_iff.2 fun x hx => (hk (generic_mem hx.2)).elim
    have : Subsingleton Γ(X, V ⊓ M.U k) := this ▸ inferInstance
    exact Subsingleton.elim _ _

theorem secVal_restrict {V W : X.Opens} (h : W ≤ V) (hW : genericPoint X ∈ W) (σ : SecOn M V) :
    secVal h₀ hW (SecOn.restrict M h σ) = secVal h₀ (h hW) σ :=
  toField_rs (inf_le_inf_right _ h) _ _

theorem secVal_smul {V : X.Opens} (hV : genericPoint X ∈ V) (a : Γ(X, V)) (σ : SecOn M V) :
    secVal h₀ hV (a • σ) = toField hV a * secVal h₀ hV σ :=
  (map_mul (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) (rs X inf_le_left a) _).trans
    (congrArg (· * secVal h₀ hV σ) (toField_rs _ _ _))

theorem secVal_add {V : X.Opens} (hV : genericPoint X ∈ V) (σ τ : SecOn M V) :
    secVal h₀ hV (σ + τ) = secVal h₀ hV σ + secVal h₀ hV τ :=
  map_add (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) _ _

theorem exists_secVal_eq_iff (hM : M.IsLB) {I : Type} (D : I → X.Opens) (hc : ⊤ ≤ ⨆ i, D i)
    (hη : ∀ i, genericPoint X ∈ D i) (τ : ∀ i, SecOn M (D i))
    (hτ : ∀ i k, IsUnit (GlobalTheory.LB.coord (τ i) k)) (x : X.functionField) :
    (∃ σ : SecOn M ⊤, secVal h₀ generic_top σ = x) ↔
      ∀ i, ∃ a ∈ (toField (hη i)).range, x = a * secVal h₀ (hη i) (τ i) := by
  constructor
  · rintro ⟨σ, rfl⟩ i
    have hne : secVal h₀ (hη i) (τ i) ≠ 0 := ((hτ i k₀).map _).ne_zero
    refine ⟨secVal h₀ generic_top σ / secVal h₀ (hη i) (τ i), ?_, (div_mul_cancel₀ _ hne).symm⟩
    refine exists_toField_eq (hη i) (fun k : {k // genericPoint X ∈ M.U k} => D i ⊓ M.U k.1)
      (fun _ => inf_le_left) (fun y hy => ?_) (fun k => (generic_inf (hη i) (k.2))) _ fun k => ?_
    · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (trivial : y ∈ ⊤))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨k, generic_mem hk⟩, hy, hk⟩
    · obtain ⟨u, hu⟩ := hτ i k.1
      refine ⟨GlobalTheory.LB.coord (SecOn.restrict M le_top σ) k.1 * u⁻¹.val, ?_⟩
      have e₁ := toField_coord h₀ (hη i) (τ i) k.2
      have e₂ := toField_coord h₀ (hη i) (SecOn.restrict M le_top σ) k.2
      have hg : toField (U := M.U k.1 ⊓ M.U k₀) (generic_inf (k.2) (h₀)) (M.g k.1 k₀).val ≠ 0 :=
        ((M.g k.1 k₀).isUnit.map _).ne_zero
      rw [map_mul, map_units_inv, hu, e₁, e₂, secVal_restrict]
      field_simp
  · intro h
    choose a ha hx using h
    choose b hb using ha
    have hv : ∀ i, secVal h₀ (hη i) (b i • τ i) = x := fun i => by
      rw [secVal_smul, hb, hx i]
    obtain ⟨σ, hσ, -⟩ := SecOn.existsUnique_glue D (fun _ => le_top) hc (fun i => b i • τ i)
      fun i j => secVal_injective h₀ (V := D i ⊓ D j) (generic_inf (hη i) (hη j)) (by
        rw [secVal_restrict, secVal_restrict, hv, hv])
    obtain ⟨i, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
    exact ⟨σ, by rw [← hv i, ← hσ i, secVal_restrict]⟩

def secValLin {K : Type} [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [Algebra K X.functionField]
    (hK : ∀ r, algebraMap K X.functionField r = toField generic_top (cst f ⊤ r)) :
    SecOnR f M ⊤ →ₗ[K] X.functionField where
  toFun σ := secVal h₀ generic_top σ
  map_add' σ τ := secVal_add h₀ generic_top σ τ
  map_smul' r σ := (secVal_smul h₀ generic_top (cst f ⊤ r) σ).trans (by
    rw [RingHom.id_apply, Algebra.smul_def, hK])

theorem secVal_pull (φ : X' ⟶ X) [IsDominant φ] {V : X.Opens} (hV : genericPoint X ∈ V)
    (h₀' : genericPoint X' ∈ (M.pull φ).U fun _ => k₀) (hV' : genericPoint X' ∈ φ ⁻¹ᵁ V)
    (σ : SecOn M V) :
    secVal h₀' hV' (SecOn.pull M φ V σ) = functionFieldMap φ (secVal h₀ hV σ) :=
  toField_appLE φ _ _ _ _

end GlobalTheory.FiniteCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCommonMultiple
open Module

namespace GlobalTheory.FiniteCover

theorem finrank_le_of_range_le {K P Q E : Type*} [Field K] [AddCommGroup P] [Module K P]
    [AddCommGroup Q] [Module K Q] [AddCommGroup E] [Module K E] [Module.Finite K Q]
    (L : P →ₗ[K] E) (hL : Function.Injective L) (B : Q →ₗ[K] E) (h : ∀ p, ∃ q, B q = L p) :
    finrank K P ≤ finrank K Q := by
  rw [← LinearMap.finrank_range_of_inj hL]
  refine (Submodule.finrank_mono (t := LinearMap.range B) ?_).trans B.finrank_range_le
  rintro _ ⟨p, rfl⟩
  exact h p

theorem exists_denominator {A C F F' ι : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Field F] [Field F'] [Algebra A C] [Module.Finite A C] [Algebra A F] [IsFractionRing A F]
    [Algebra C F'] [IsFractionRing C F'] [Algebra F F'] [Algebra A F'] [IsScalarTower A F F']
    [IsScalarTower A C F'] [Fintype ι] (e : Basis ι F F') :
    ∃ c : A, c ≠ 0 ∧
      (∀ j (y : C), ∃ a : A, algebraMap A F a = algebraMap A F c * e.repr (algebraMap C F' y) j) ∧
      ∀ j, ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := C)
  obtain ⟨c₁, hc₁⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun p : ι × Fin n => e.repr (algebraMap C F' (g p.2)) p.1)
  have h2 : ∀ j, ∃ c : A, c ≠ 0 ∧ ∃ y : C, algebraMap C F' y = algebraMap A F c • e j := by
    intro j
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := C) (e j)
    have hinj : Function.Injective (algebraMap A C) := by
      have : Function.Injective (algebraMap A F') := by
        rw [IsScalarTower.algebraMap_eq A F F']
        exact (algebraMap F F').injective.comp (IsFractionRing.injective A F)
      rw [IsScalarTower.algebraMap_eq A C F'] at this
      exact Function.Injective.of_comp this
    have hal : IsAlgebraic A q := (Algebra.IsIntegral.isIntegral (R := A) q).isAlgebraic
    obtain ⟨c, hc, z, hz⟩ := hal.exists_nonzero_dvd hq
    refine ⟨c, hc, z * p, ?_⟩
    have hq' : algebraMap C F' q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    rw [← hpq, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A C F', hz, map_mul, map_mul]
    field_simp
  choose c₂ hc₂ y₂ hy₂ using h2
  refine ⟨c₁ * ∏ j, c₂ j, mul_ne_zero (nonZeroDivisors.coe_ne_zero c₁)
    (Finset.prod_ne_zero_iff.2 fun j _ => hc₂ j), fun j y => ?_, fun j => ?_⟩
  · have hy : y ∈ Submodule.span A (Set.range g) := hg ▸ Submodule.mem_top
    suffices h : ∃ a : A, algebraMap A F a = algebraMap A F c₁ * e.repr (algebraMap C F' y) j by
      obtain ⟨a, ha⟩ := h
      exact ⟨a * ∏ j, c₂ j, by rw [map_mul, map_mul, ha]; ring⟩
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨a, ha⟩ := hc₁ (j, k)
      exact ⟨a, by rw [ha, Algebra.smul_def]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), map_add (f := _), Finsupp.add_apply, ha, hb, mul_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨r * a, ?_⟩
      have : algebraMap C F' (r • x) = algebraMap A F r • algebraMap C F' x := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ha]
      ring
  · refine ⟨(c₁ * ∏ k ∈ Finset.univ.erase j, c₂ k : A) • y₂ j, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), ← mul_assoc, map_mul (algebraMap A F) _ (c₂ j),
      mul_smul (algebraMap A F _), ← hy₂, Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_common_multiple {F I : Type*} [Field F] [Fintype I] (A : I → Subring F) (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k) :
    ∃ (a : ℕ) (u : F), u ≠ 0 ∧ ∀ i, ∃ b ∈ A i, u = ρ i ^ a * c i * b := by
  classical
  choose m hm using hext
  let M : I → ℕ := fun i => ∑ k, m i k
  have hM : ∀ i k, c i * (ρ i / ρ k) ^ M i ∈ A k := fun i k => by
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (f := m i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    change c i * (ρ i / ρ k) ^ (∑ k, m i k) ∈ A k
    rw [hl, pow_add, ← mul_assoc]
    exact mul_mem (hm i k) (pow_mem (hr i k) _)
  refine ⟨∑ i, M i, ∏ i, c i * ρ i ^ M i,
    Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (hc i) (pow_ne_zero _ (hρ i)), fun k => ?_⟩
  refine ⟨∏ i ∈ Finset.univ.erase k, c i * (ρ i / ρ k) ^ M i, prod_mem fun i _ => hM i k, ?_⟩
  have e : ∀ i, c i * ρ i ^ M i = ρ k ^ M i * (c i * (ρ i / ρ k) ^ M i) := fun i => by
    have := hρ k
    rw [div_pow]
    field_simp
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k), div_self (hρ k), one_pow, mul_one, mul_assoc]

theorem finrank_sandwich {K F F' I : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Fintype I] {d : ℕ} (e : Basis (Fin d) F F')
    (A : I → Subring F) (C : I → Subring F') (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k)
    (hAC : ∀ i, ∀ a ∈ A i, algebraMap F F' a ∈ C i)
    (hc₁ : ∀ i j, ∀ y ∈ C i, c i * e.repr y j ∈ A i) (hc₂ : ∀ i j, c i • e j ∈ C i)
    (V W : ℕ → Type*) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)]
    [∀ t, Module K (W t)] (hV : ∀ t, Module.Finite K (V t)) (hW : ∀ t, Module.Finite K (W t))
    (α : ∀ t, V t →ₗ[K] F) (β : ∀ t, W t →ₗ[K] F') (hα : ∀ t, Function.Injective (α t))
    (hβ : ∀ t, Function.Injective (β t))
    (rα : ∀ t x, (∃ v, α t v = x) ↔ ∀ i, ∃ a ∈ A i, x = a * ρ i ^ t)
    (rβ : ∀ t y, (∃ w, β t w = y) ↔ ∀ i, ∃ a ∈ C i, y = a * algebraMap F F' (ρ i ^ t)) :
    ∃ a : ℕ, ∀ t : ℕ, d * finrank K (V t) ≤ finrank K (W (t + a)) ∧
      finrank K (W t) ≤ d * finrank K (V (t + a)) := by
  obtain ⟨a, u, hu, hub⟩ := exists_common_multiple A ρ c hρ hc hr hext
  have hpi : ∀ t, finrank K (Fin d → V t) = d * finrank K (V t) := fun t => by
    rw [Module.finrank_pi_fintype]
    simp
  refine ⟨a, fun t => ⟨?_, ?_⟩⟩
  · rw [← hpi]
    let L : (Fin d → V t) →ₗ[K] F' :=
      ((e.equivFun.symm.toLinearMap.restrictScalars K).comp
        (((LinearMap.mulLeft K u).comp (α t)).compLeft (Fin d)))
    have hL : ∀ v, L v = ∑ j, (u * α t (v j)) • e j := fun v => e.equivFun_symm_apply _
    refine finrank_le_of_range_le L ?_ (β (t + a)) fun v => (rβ _ _).2 fun i => ?_
    · intro v w h
      have h' := e.equivFun.symm.injective h
      funext j
      exact hα t (mul_left_cancel₀ hu (congrFun h' j))
    · obtain ⟨b, hb, rfl⟩ := hub i
      choose x hx hx' using fun j => (rα t _).1 ⟨v j, rfl⟩ i
      refine ⟨∑ j, algebraMap F F' (b * x j) * (c i • e j),
        sum_mem fun j _ => mul_mem (hAC i _ (mul_mem hb (hx j))) (hc₂ i j), ?_⟩
      rw [hL, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx' j]
      simp only [Algebra.smul_def, map_mul, map_pow, pow_add]
      ring
  · rw [← hpi]
    let L : W t →ₗ[K] (Fin d → F) := ((LinearMap.mulLeft K u).compLeft (Fin d)).comp
      ((e.equivFun.toLinearMap.restrictScalars K).comp (β t))
    have hL : ∀ w j, L w j = u * e.repr (β t w) j := fun w j => rfl
    refine finrank_le_of_range_le L ?_ ((α (t + a)).compLeft (Fin d)) fun w => ?_
    · intro v w h
      refine hβ t (e.equivFun.injective (funext fun j => ?_))
      exact mul_left_cancel₀ hu (congrFun h j)
    · have key : ∀ j, ∃ v, α (t + a) v = L w j := fun j => (rα _ _).2 fun i => by
        obtain ⟨b, hb, hub⟩ := hub i
        obtain ⟨y, hy, hy'⟩ := (rβ t _).1 ⟨w, rfl⟩ i
        refine ⟨b * (c i * e.repr y j), mul_mem hb (hc₁ i j y hy), ?_⟩
        rw [hL, hy', mul_comm y, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hub,
          pow_add]
        ring
      choose v hv using key
      exact ⟨v, funext hv⟩

end GlobalTheory.FiniteCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FiniteCover

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']

theorem rankAtStalk_bot {A C : Type} [CommRing A] [IsDomain A] [AddCommGroup C] [Module A C] :
    Module.rankAtStalk (R := A) C ⊥ = Module.finrank A C := by
  have h : (⊥ : PrimeSpectrum A).asIdeal.primeCompl ≤ nonZeroDivisors A := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hx (h0 ▸ Ideal.zero_mem _)
  rw [Module.rankAtStalk, IsLocalization.finrank_eq _ _ h]
  exact IsLocalizedModule.finrank_eq _ (LocalizedModule.mkLinearMap _ C) h

theorem generic_mem_preimage (φ : X' ⟶ X) [Surjective φ] {U : X.Opens} (h : genericPoint X ∈ U) :
    genericPoint X' ∈ φ ⁻¹ᵁ U := by
  obtain ⟨y, hy⟩ := φ.surjective (genericPoint X)
  exact generic_mem (x := y) (show φ y ∈ U from hy ▸ h)

theorem chart_data (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ]
    [Algebra X.functionField X'.functionField]
    (hF : ∀ x, algebraMap X.functionField X'.functionField x = functionFieldMap φ x)
    {D : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D) :
    (∃ x, Module.finrank X.functionField X'.functionField = φ.finrank x) ∧
    ∀ {d : ℕ} (e : Module.Basis (Fin d) X.functionField X'.functionField),
      ∃ c ∈ (toField h).range, c ≠ 0 ∧
        (∀ j, ∀ y ∈ (toField (generic_mem_preimage φ h)).range, c * e.repr y j ∈ (toField h).range) ∧
        ∀ j, c • e j ∈ (toField (generic_mem_preimage φ h)).range := by
  have h' := generic_mem_preimage φ h
  haveI : Nonempty D := ⟨⟨_, h⟩⟩
  haveI : Nonempty (φ ⁻¹ᵁ D) := ⟨⟨_, h'⟩⟩
  letI := (φ.app D).hom.toAlgebra
  haveI : Module.Finite Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := φ.finite_app D hD
  haveI : Module.Flat Γ(X, D) Γ(X', φ ⁻¹ᵁ D) := by
    have := φ.flat_appLE hD (hD.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  haveI := functionField_isFractionRing_of_isAffineOpen X D hD
  haveI := functionField_isFractionRing_of_isAffineOpen X' _ (hD.preimage φ)
  letI : Algebra Γ(X, D) X'.functionField :=
    ((algebraMap X.functionField X'.functionField).comp (algebraMap Γ(X, D) X.functionField)).toAlgebra
  haveI : IsScalarTower Γ(X, D) X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower Γ(X, D) Γ(X', φ ⁻¹ᵁ D) X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      have e := toField_appLE φ le_rfl h h' a
      rw [Scheme.Hom.appLE_eq_app] at e
      exact (hF _).trans e.symm
  refine ⟨⟨hD.fromSpec (⊥ : PrimeSpectrum Γ(X, D)), ?_⟩, fun e => ?_⟩
  · have hp : IsPullback (hD.preimage φ).fromSpec (Spec.map (φ.app D)) φ hD.fromSpec :=
      (IsOpenImmersion.isPullback _ _ _ _ (by
        rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hD (hD.preimage φ)])
        (by simp)).flip
    rw [IsFractionRing.finrank_eq Γ(X, D) X.functionField Γ(X', φ ⁻¹ᵁ D) X'.functionField,
      ← rankAtStalk_bot]
    refine Eq.trans ?_ (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp _)
    exact (Scheme.Hom.finrank_SpecMap_algebraMap Γ(X, D) Γ(X', φ ⁻¹ᵁ D) _).symm
  · obtain ⟨c, hc, h₁, h₂⟩ := exists_denominator (A := Γ(X, D)) (C := Γ(X', φ ⁻¹ᵁ D)) e
    refine ⟨toField h c, ⟨c, rfl⟩, fun h0 => hc (toField_injective h (h0.trans (map_zero _).symm)),
      ?_, h₂⟩
    rintro j _ ⟨y, rfl⟩
    exact h₁ j y

theorem exists_mul_pow_mem {D D' : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D)
    (h' : genericPoint X ∈ D') (r : Γ(X, D)) (hr : toField h r ≠ 0) (hle : X.basicOpen r ≤ D')
    (c : Γ(X, D')) : ∃ m : ℕ, toField h' c * toField h r ^ m ∈ (toField h).range := by
  have hb : genericPoint X ∈ X.basicOpen r :=
    (Scheme.mem_basicOpen X r _ h).2 (isUnit_iff_ne_zero.2 hr)
  have := hD.isLocalization_basicOpen r
  obtain ⟨m, b, e⟩ := IsLocalization.Away.surj r (rs X hle c)
  have e' : toField hb (rs X hle c * rs X (X.basicOpen_le r) r ^ m) =
      toField hb (rs X (X.basicOpen_le r) b) := congrArg (toField hb) e
  rw [map_mul, map_pow, toField_rs, toField_rs, toField_rs] at e'
  exact ⟨m, b, e'.symm⟩


omit [IsIntegral X] in
theorem basicOpen_le_nonzeroLocus {H : LB X} (s s' : LB.Sec H) (r : Γ(X, nonzeroLocus s))
    (h : ∀ k, rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s'.f k) =
      rs X (inf_le_left : nonzeroLocus s ⊓ H.U k ≤ nonzeroLocus s) r *
        rs X (inf_le_right : nonzeroLocus s ⊓ H.U k ≤ H.U k) (s.f k)) :
    X.basicOpen r ≤ nonzeroLocus s' := by
  intro x hx
  have hs : x ∈ nonzeroLocus s := X.basicOpen_le r hx
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  have e := congrArg X.basicOpen (h l)
  rw [Scheme.basicOpen_mul] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ nonzeroLocus s ⊓ H.U l := ⟨hs, X.basicOpen_le _ hl⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, (e.ge ⟨⟨hx', hx⟩, hx', hl⟩).2⟩

def powSec {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (t : ℕ) : LB.Sec (pw H t) where
  f k := (s.f k : Γ(X, H.U k)) ^ t
  compat i j := by
    have e := congrArg (· ^ t) (s.compat i j)
    simp only [mul_pow, ← map_pow] at e
    refine e.trans ?_
    congr 1

end GlobalTheory.FiniteCover

namespace GlobalTheory

open FiniteCover

theorem finrank_sec_pull_sandwich : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Etale φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  haveI : Surjective φ := φ.one_le_finrank_iff_surjective.1 fun x => (hd x).symm ▸ hd1
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwichStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shift_finrank_sec_pull_bounds : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Etale φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  first | exact @GlobalTheory.finrank_sec_pull_sandwich | exact GlobalTheory.finrank_sec_pull_sandwich | (intros; apply GlobalTheory.finrank_sec_pull_sandwich <;> assumption)
end
