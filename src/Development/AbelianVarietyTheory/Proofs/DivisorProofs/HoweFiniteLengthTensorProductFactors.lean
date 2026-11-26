module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodGlRepPiTensorActionAtFactorAndCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodGlRepPiTensorActionAtFactorAndCommute
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.FactorAct

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

omit [Fintype T] in
theorem atPl_tprod' (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

omit [Fintype T] in
theorem atPl_mul' (w : T) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun f => ?_)
  simp [atPl_tprod']

omit [Fintype T] in
theorem atPl_comm' {w w' : T} (h : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) (x : ⨂[ℂ] i, V i) :
    atPl w L (atPl w' L' x) = atPl w' L' (atPl w L x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, atPl_tprod', Function.update_of_ne h, Function.update_of_ne h.symm]
    rw [Function.update_comm h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def intersection_update_fsHerm_neg_one (f : ∀ i, V i) (w : T) : V w →ₗ[ℂ] ⨂[ℂ] i, V i := (PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w

omit [Fintype T] in
theorem position_apply (f : ∀ i, V i) (w : T) (v : V w) : intersection_update_fsHerm_neg_one f w v = PiTensorProduct.tprod ℂ (Function.update f w v) := rfl

omit [Fintype T] in
theorem position_self (f : ∀ i, V i) (w : T) : intersection_update_fsHerm_neg_one f w (f w) = PiTensorProduct.tprod ℂ f := by
  rw [position_apply, Function.update_eq_self]

omit [Fintype T] in
theorem atPl_tprod_update (f : ∀ i, V i) (w : T) (L : Module.End ℂ (V w)) (v : V w) :
    atPl w L (intersection_update_fsHerm_neg_one f w v) = intersection_update_fsHerm_neg_one f w (L v) := by
  simp [position_apply, atPl_tprod']

variable {p q : ℕ}

omit [Fintype T] in
theorem atPl_sub' (w : T) (A B : Module.End ℂ (V w)) : atPl w (A - B) = atPl w A - atPl w B :=
  map_sub ((PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w) A B

theorem actAt_lie (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : IsLieAct a) : IsLieAct (actAt w a) := by
  intro X Y
  rw [actAt_apply, actAt_apply, actAt_apply, h X Y, atPl_sub', atPl_mul', atPl_mul']

theorem actAt_wts (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ)
    (x : ⨂[ℂ] i, V i) : x ∈ ⨆ μ : Ix p q → ℚ, wtSub (actAt w a) μ := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine Submodule.smul_mem _ _ ?_
    rw [← position_self f w]
    refine Submodule.iSup_induction _ (motive := fun v => intersection_update_fsHerm_neg_one f w v ∈ ⨆ μ : Ix p q → ℚ, wtSub (actAt w a) μ) (h (f w))
      ?_ (by simp) ?_
    · intro μ y hy
      refine Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply] at hy ⊢
      intro c
      rw [actAt_apply, atPl_tprod_update, ← map_smul, ← map_sub, hy c, map_zero]
    · intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem actAt_locU (w : T) {a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)} (h : LocU (fun c : Ix p q => c.isLeft) (units a)) :
    LocU (fun c : Ix p q => c.isLeft) (units (actAt w a)) := by
  refine GlobalTheory.T.isLocallyBlockUnitary_of_iSup_intertwiner_range (Ix p q) (V w) (fun c : Ix p q => c.isLeft) (units a) (⨂[ℂ] i, V i) (units (actAt w a))
    {g | ∃ f : ∀ i, V i, g = intersection_update_fsHerm_neg_one f w} ?_ ?_ h
  · rintro g ⟨f, rfl⟩ c d _ x
    simp only [units, actAt_apply, atPl_tprod_update]
  · refine eq_top_iff.2 ?_
    rw [← PiTensorProduct.span_tprod_eq_top]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, rfl⟩
    refine (le_iSup₂ (f := fun (g : V w →ₗ[ℂ] ⨂[ℂ] i, V i) (_ : g ∈ {g | ∃ f : ∀ i, V i, g = intersection_update_fsHerm_neg_one f w}) =>
      LinearMap.range g) (intersection_update_fsHerm_neg_one f w) ⟨f, rfl⟩ : _) ⟨f w, position_self f w⟩

end GlobalTheory.HoweR.FactorAct

namespace GlobalTheory.HoweR

theorem actAt_good_comm : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)), (∀ w, Good (a w)) →
    (∀ w, Good (actAt w (a w))) ∧ ∀ w w', w ≠ w' → ∀ Z Z' v,
      actAt w (a w) Z (actAt w' (a w') Z' v) = actAt w' (a w') Z' (actAt w (a w) Z v) := by
  intro T _ _ V _ _ R S a ha
  refine ⟨fun w => ⟨FactorAct.actAt_lie w (ha w).1, FactorAct.actAt_wts w (ha w).2.1, FactorAct.actAt_locU w (ha w).2.2⟩,
    fun w w' hw Z Z' v => ?_⟩
  exact FactorAct.atPl_comm' hw _ _ v

end GlobalTheory.HoweR

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodGlRepPiTensorActionAtFactorAndCommuteStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodGlRep_piTensorActionAtFactor_and_commute : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)), (∀ w, Good (a w)) → (∀ w, Good (actAt w (a w))) ∧ ∀ w w', w ≠ w' → ∀ Z Z' v, actAt w (a w) Z (actAt w' (a w') Z' v) = actAt w' (a w') Z' (actAt w (a w) Z v) := by
  first | exact @GlobalTheory.HoweR.actAt_good_comm | exact GlobalTheory.HoweR.actAt_good_comm | (intros; apply GlobalTheory.HoweR.actAt_good_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSpanAllFactorsSupFiniteSingleton
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSpanAllFactorsSupFiniteSingleton
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensSup

theorem tensAll_sup_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U C : ∀ w, Submodule ℂ (V w)) :
    tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose u hu c hc huc using fun w => Submodule.mem_sup.1 (hf w)
  have hfe : f = u + c := funext fun w => (huc w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_add_univ]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : s = Finset.univ
  · subst hs
    refine Submodule.mem_sup_left (Submodule.subset_span ⟨u, hu, ?_⟩)
    congr 1
    simp
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ s := by
      by_contra h
      push_neg at h
      exact hs (Finset.eq_univ_of_forall h)
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨s.piecewise u c, ⟨w, ?_⟩, rfl⟩)
    rw [Finset.piecewise_eq_of_notMem _ _ _ hw]
    exact hc w

theorem tensAll_fin {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (U : ∀ w, Submodule ℂ (V w)) (hU : ∀ w, FiniteDimensional ℂ (U w)) :
    FiniteDimensional ℂ (tensAll U) := by
  have : tensAll U ≤ LinearMap.range (PiTensorProduct.map fun w => (U w).subtype) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun w => (⟨f w, hf w⟩ : U w), by rw [PiTensorProduct.map_tprod]; rfl⟩
  exact Submodule.finiteDimensional_of_le this

theorem tensAll_span_le {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)] (v : ∀ w, V w) :
    tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  choose a ha using fun w => Submodule.mem_span_singleton.1 (hf w)
  have hfe : f = fun w => a w • v w := funext fun w => (ha w).symm
  rw [SetLike.mem_coe, hfe, MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem main : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)],
    ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧
      ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧
      ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  intro T _ _ V _ _ U C
  exact ⟨tensAll_sup_le U C, tensAll_fin U, tensAll_span_le⟩

end GlobalTheory.HoweR.TensSup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorSpanAllFactorsSupFiniteSingletonStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧ ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧ ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  first | exact @GlobalTheory.HoweR.TensSup.main | exact GlobalTheory.HoweR.TensSup.main | (intros; apply GlobalTheory.HoweR.TensSup.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodCyclicModuloSpanSomeFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodCyclicModuloSpanSomeFactor
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR

theorem tprod_cyclic_top : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)) (v : ∀ w, V w), (∀ w, genSub (a w) {v w} ⊔ C w = ⊤) → ∀ N : Submodule ℂ (PiTensorProduct ℂ V), (∀ w, Stab (actAt w (a w)) N) → tensAny C ≤ N → PiTensorProduct.tprod ℂ v ∈ N → N = ⊤ := by
  intro T _ _ V _ _ R S a C v hgen N hN hC hv
  have key : ∀ s : Finset T, ∀ f : ∀ w, V w, (∀ w, w ∉ s → f w = v w) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = v := funext fun w => hf w (Finset.notMem_empty w)
      rw [this]; exact hv
    | insert w s hws ih =>
      intro f hf
      let K : Submodule ℂ (V w) :=
        Submodule.comap ((PiTensorProduct.tprod ℂ (s := V)).toLinearMap f w) N
      have hmem : ∀ x, x ∈ K ↔ PiTensorProduct.tprod ℂ (Function.update f w x) ∈ N := by
        intro x; simp [K, MultilinearMap.toLinearMap_apply]
      have hstab : ∀ Z, ∀ y ∈ K, a w Z y ∈ K := by
        intro Z y hy
        rw [hmem] at hy ⊢
        have h1 := hN w Z _ hy
        rw [actAt_apply, atPl, PiTensorProduct.map_tprod] at h1
        convert h1 using 2
        funext i
        by_cases h : i = w
        · subst h; simp
        · simp [Function.update_of_ne h]
      have hvK : v w ∈ K := by
        rw [hmem]
        apply ih
        intro u hu
        by_cases h : u = w
        · subst h; simp
        · rw [Function.update_of_ne h]
          exact hf u (by simp [h, hu])
      have hCK : C w ≤ K := by
        intro c hc
        rw [hmem]
        apply hC
        apply Submodule.subset_span
        exact ⟨Function.update f w c, ⟨w, by simpa using hc⟩, rfl⟩
      have hgK : genSub (a w) {v w} ≤ K := by
        apply sInf_le
        refine ⟨?_, hstab⟩
        simpa using hvK
      have htop : K = ⊤ := by
        rw [eq_top_iff, ← hgen w]
        exact sup_le hgK hCK
      have : f w ∈ K := by rw [htop]; trivial
      rw [hmem, Function.update_eq_self] at this
      exact this
  have hall : ∀ f : ∀ w, V w, PiTensorProduct.tprod ℂ f ∈ N :=
    fun f => key Finset.univ f (fun w hw => absurd (Finset.mem_univ w) hw)
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact hall f

end GlobalTheory.HoweR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodCyclicModuloSpanSomeFactorStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tprod_cyclic_modulo_spanSomeFactor : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)) (v : ∀ w, V w), (∀ w, genSub (a w) {v w} ⊔ C w = ⊤) → ∀ N : Submodule ℂ (PiTensorProduct ℂ V), (∀ w, Stab (actAt w (a w)) N) → tensAny C ≤ N → PiTensorProduct.tprod ℂ v ∈ N → N = ⊤ := by
  first | exact @GlobalTheory.HoweR.tprod_cyclic_top | exact GlobalTheory.HoweR.tprod_cyclic_top | (intros; apply GlobalTheory.HoweR.tprod_cyclic_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPiTensorSpanAllFactorsOfJointKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPiTensorSpanAllFactorsOfJointKernel
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.JointKer

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem dual_contr (f : ∀ i, Module.Dual ℂ (V i)) (w : T) (ν : Module.Dual ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    ν (GlobalTheory.TensorFactorUnique.contr f w y) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update f w ν)) y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, GlobalTheory.TensorFactorUnique.contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem contr_atPl (f : ∀ i, Module.Dual ℂ (V i)) (w : T) (L : Module.End ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    GlobalTheory.TensorFactorUnique.contr f w (atPl w L y) = L (GlobalTheory.TensorFactorUnique.contr f w y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, atPl_tprod, GlobalTheory.TensorFactorUnique.contr_tprod, GlobalTheory.TensorFactorUnique.contr_tprod,
      map_smul, Function.update_self, LinearMap.map_smul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem atPl_eq_zero_of_common (w : T) (F : Set (Module.End ℂ (V w))) (g : Module.End ℂ (V w))
    (hg : ∀ v, (∀ L ∈ F, L v = 0) → g v = 0) (y : ⨂[ℂ] i, V i) (hy : ∀ L ∈ F, atPl w L y = 0) :
    atPl w g y = 0 := by
  apply GlobalTheory.PiTensorCommute.eq_zero_of_forall_dualDistrib
  intro f
  have hv : g (GlobalTheory.TensorFactorUnique.contr f w y) = 0 := hg _ fun L hL => by rw [← contr_atPl, hy L hL, map_zero]
  have h := dual_contr f w (f w) (atPl w g y)
  rw [contr_atPl, hv, map_zero, Function.update_eq_self] at h
  exact h.symm

theorem atPl_sub_one (w : T) (p : Module.End ℂ (V w)) (y : ⨂[ℂ] i, V i) :
    atPl w (p - 1) y = atPl w p y - y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, atPl_tprod, atPl_tprod, LinearMap.sub_apply, Module.End.one_apply,
      MultilinearMap.map_update_sub, Function.update_eq_self, smul_sub]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]; abel

theorem exists_proj {M : Type} [AddCommGroup M] [Module ℂ M] (A : Submodule ℂ M) :
    ∃ π : Module.End ℂ M, (∀ v, π v ∈ A) ∧ ∀ v ∈ A, π v = v := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.subtype (Submodule.ker_subtype _)
  refine ⟨A.subtype ∘ₗ g, fun v => (g v).2, fun v hv => ?_⟩
  have := congrArg (fun h => ((h ⟨v, hv⟩ : A) : M)) hg
  simpa using this

end GlobalTheory.HoweR.JointKer

namespace GlobalTheory.HoweR

open JointKer

theorem mem_tensAll_of_killed : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (L : ∀ w, Set (Module.End ℂ (V w))) (H : ∀ w, Submodule ℂ (V w)),
    (∀ w v, (∀ l ∈ L w, l v = 0) → v ∈ H w) → ∀ y : PiTensorProduct ℂ V, (∀ w, ∀ l ∈ L w, atPl w l y = 0) →
    y ∈ tensAll H := by
  intro T _ _ V _ _ L H hH y hy
  choose p hpK hpid using fun w => exists_proj (H w)
  have hfix : ∀ w, atPl w (p w) y = y := by
    intro w
    have h0 := atPl_eq_zero_of_common w (L w) (p w - 1) (fun v hv => by
        rw [LinearMap.sub_apply, Module.End.one_apply, hpid w v (hH w v hv), sub_self]) y (hy w)
    rw [atPl_sub_one] at h0
    exact sub_eq_zero.1 h0
  have hmap : ∀ s : Finset T,
      PiTensorProduct.map (fun w => if w ∈ s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [PiTensorProduct.map_id]
    | insert a s ha ih =>
      have e : (fun w => if w ∈ insert a s then p w else (LinearMap.id : V w →ₗ[ℂ] V w)) =
          fun w => (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) a (p a) w) ∘ₗ
            (if w ∈ s then p w else LinearMap.id) := by
        funext w
        by_cases hw : w = a
        · subst hw
          simp [ha]
        · simp [hw, Function.update_of_ne hw]
      rw [e, PiTensorProduct.map_comp, LinearMap.comp_apply, ih]
      exact hfix a
  have hy' : PiTensorProduct.map p y = y := by
    have := hmap Finset.univ
    simpa using this
  rw [← hy']
  clear hy' hmap hfix hy
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun w => p w (f w), fun w => hpK w _, rfl⟩)
  | add x z hx hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hz

end GlobalTheory.HoweR

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPiTensorSpanAllFactorsOfJointKernelStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_piTensorSpanAllFactors_of_jointKernel : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (L : ∀ w, Set (Module.End ℂ (V w))) (H : ∀ w, Submodule ℂ (V w)), (∀ w v, (∀ l ∈ L w, l v = 0) → v ∈ H w) → ∀ y : PiTensorProduct ℂ V, (∀ w, ∀ l ∈ L w, atPl w l y = 0) → y ∈ tensAll H := by
  first | exact @GlobalTheory.HoweR.mem_tensAll_of_killed | exact GlobalTheory.HoweR.mem_tensAll_of_killed | (intros; apply GlobalTheory.HoweR.mem_tensAll_of_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactor
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensQuad

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  rcases eq_or_ne i w with rfl | h
  · simp
  · simp [Function.update_of_ne h]

noncomputable def atPlLin (w : T) : Module.End ℂ (V w) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w

theorem atPlLin_apply (w : T) (L : Module.End ℂ (V w)) : atPlLin w L = atPl w L := rfl

theorem atPl_mul (w : T) (L₁ L₂ : Module.End ℂ (V w)) : atPl w (L₁ * L₂) = atPl w L₁ * atPl w L₂ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod, Module.End.mul_apply]

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [atPl_tprod]

theorem qop_atPl {ι : Type} [Fintype ι] [DecidableEq ι] (w : T) (F : ι → ι → Module.End ℂ (V w)) (α β : ℂ) (i j : ι) :
    qop (fun a b => atPl w (F a b)) α β i j = atPl w (qop F α β i j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qop, ← atPlLin_apply, map_sub, map_sum, map_smul, apply_ite (atPlLin w), map_zero]
  simp only [atPlLin_apply, atPl_mul, atPl_one]

theorem mem_of_atPl (C : ∀ w, Submodule ℂ (V w)) (w : T) (L : Module.End ℂ (V w)) (hL : ∀ x, L x ∈ C w)
    (v : ⨂[ℂ] i, V i) : atPl w L v ∈ tensAny C := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, atPl_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨w, by simpa using hL (f w)⟩, rfl⟩)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact add_mem hx hy

end GlobalTheory.HoweR.TensQuad

open GlobalTheory.HoweR.TensQuad in
theorem GlobalTheory.HoweR.quadMod_actAt : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  intro T _ _ V _ _ C w p q a α β α' β' h i j v _
  have hu : units (actAt w a) = fun i j => atPl w (units a i j) := rfl
  have hn : negT (units (actAt w a)) = fun i j => atPl w (negT (units a) i j) := by
    funext i j
    simp only [negT, units, actAt_apply, ← atPlLin_apply, map_neg]
  refine ⟨?_, ?_⟩
  · rw [hu, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).1) v
  · rw [hn, qop_atPl]
    exact mem_of_atPl C w _ (fun x => (h i j x Submodule.mem_top).2) v
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlActionQuadraticRelationModuloPiTensorAtFactorStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  first | exact @GlobalTheory.HoweR.quadMod_actAt | exact GlobalTheory.HoweR.quadMod_actAt | (intros; apply GlobalTheory.HoweR.quadMod_actAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthTensorProductFactors
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.TensAlg

variable {T : Type} [Fintype T] [DecidableEq T] {V : T → Type} [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)]

theorem atPl_eq_toLinearMap (w : T) (L : Module.End ℂ (V w)) :
    atPl w L = (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L := rfl

theorem atPl_one (w : T) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  unfold atPl
  have h : Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id := by
    funext i
    by_cases hi : i = w
    · subst hi; simp; rfl
    · simp [hi]
  rw [h]; exact PiTensorProduct.map_id

theorem atPl_sub_smul (w : T) (L : Module.End ℂ (V w)) (c : ℂ) (y : ⨂[ℂ] i, V i) :
    atPl w (L - c • 1) y = atPl w L y - c • y := by
  rw [atPl_eq_toLinearMap, map_sub, map_smul, ← atPl_eq_toLinearMap, ← atPl_eq_toLinearMap, atPl_one]
  simp

theorem atPl_tprod (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v w (L (v w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp
  · simp [hi]

theorem atPl_tprod_eq_zero (w : T) (L : Module.End ℂ (V w)) (v : ∀ i, V i) (h : L (v w) = 0) :
    atPl w L (PiTensorProduct.tprod ℂ v) = 0 := by
  rw [atPl_tprod, h]
  exact MultilinearMap.map_update_zero _ _ _

theorem tensAll_mono {H H' : ∀ w, Submodule ℂ (V w)} (h : ∀ w, H w ≤ H' w) : tensAll H ≤ tensAll H' := by
  apply Submodule.span_mono
  rintro y ⟨f, hf, rfl⟩
  exact ⟨f, fun w => h w (hf w), rfl⟩

theorem iInf_hwSub_le {R S : T → ℕ} (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (μ : ∀ w, Ix (R w) (S w) → ℚ) :
    (⨅ w, hwSub (actAt w (a w)) (μ w)) ≤ tensAll (fun w => hwSub (a w) (μ w)) := by
  intro y hy
  rw [Submodule.mem_iInf] at hy
  refine GlobalTheory.T.mem_piTensorSpanAllFactors_of_jointKernel T V
    (fun w => {l | (∃ c, l = a w (Eab c c) - ((μ w c : ℚ) : ℂ) • 1) ∨ ∃ c d, posC c d ∧ l = a w (Eab c d)})
    (fun w => hwSub (a w) (μ w)) ?_ y ?_
  · intro w x hx
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    refine ⟨fun c => ?_, fun c d hcd => ?_⟩
    · exact hx _ (Or.inl ⟨c, rfl⟩)
    · exact hx _ (Or.inr ⟨c, d, hcd, rfl⟩)
  · intro w l hl
    have hyw := hy w
    simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyw
    rcases hl with ⟨c, rfl⟩ | ⟨c, d, hcd, rfl⟩
    · rw [atPl_sub_smul]
      have h1 := hyw.1 c
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply] at h1
      exact h1
    · have h2 := hyw.2 c d hcd
      rw [actAt_apply] at h2
      exact h2

end GlobalTheory.HoweR.TensAlg

namespace GlobalTheory.HoweR


open GlobalTheory.HoweR.TensAlg in
theorem howeAlg_tensAny : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)]
    [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w))
    (C : ∀ w, Submodule ℂ (V w)), (∀ w, Pack (a w) (C w)) → HoweAlg (fun w => actAt w (a w)) (tensAny C) := by
  intro T _ _ V _ _ R S a C hP
  have hG := GlobalTheory.T.isGoodGlRep_piTensorActionAtFactor_and_commute T V R S a (fun w => (hP w).1)
  choose α β α' β' hQ using fun w => (hP w).2.2.1
  choose μ v hv hgen hmul using fun w => (hP w).2.2.2.2
  refine GlobalTheory.T.howeAlg_of_cyclic_highest_weight T R S (⨂[ℂ] i, V i) (fun w => actAt w (a w)) hG.1 hG.2 (tensAny C) α β α' β'
    (fun w => GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor T V C w (R w) (S w) (a w) _ _ _ _ (hQ w)) ?_ ?_
  · intro B
    choose U hUfd hU using fun w => (hP w).2.2.2.1 B
    refine ⟨tensAll U, (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).2.1 hUfd, fun ν hν => ?_⟩
    exact (iInf_hwSub_le a ν).trans
      ((tensAll_mono (fun w => hU w (ν w) (fun c => hν w c))).trans (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V U C).1)
  · refine ⟨μ, PiTensorProduct.tprod ℂ v, fun w => ?_,
      fun N hN hC hvN => GlobalTheory.T.tprod_cyclic_modulo_spanSomeFactor T V R S a C v hgen N hN hC hvN, ?_⟩
    · have h := hv w
      simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h ⊢
      refine ⟨fun c => ?_, fun c d hcd => ?_⟩
      · rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, actAt_apply, ← atPl_sub_smul]
        exact atPl_tprod_eq_zero w _ v (h.1 c)
      · rw [actAt_apply]
        exact atPl_tprod_eq_zero w _ v (h.2 c d hcd)
    · refine (iInf_hwSub_le a μ).trans ((tensAll_mono (fun w => hmul w)).trans ?_)
      refine (GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).1.trans ?_
      exact sup_le_sup_right ((GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton T V (fun w => Submodule.span ℂ {v w}) C).2.2 v) _

end GlobalTheory.HoweR

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthTensorProductFactorsStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howe_finite_length_tensor_product_factors : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)), (∀ w, Pack (a w) (C w)) → HoweAlg (fun w => actAt w (a w)) (tensAny C) := by
  first | exact @GlobalTheory.HoweR.howeAlg_tensAny | exact GlobalTheory.HoweR.howeAlg_tensAny | (intros; apply GlobalTheory.HoweR.howeAlg_tensAny <;> assumption)
end
