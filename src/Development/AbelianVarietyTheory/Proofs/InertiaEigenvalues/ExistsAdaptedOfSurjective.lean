module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComponentEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfLinearIndependentDdRE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankMulLeFinrankDdROfSpans
noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

theorem finrank_le_of_span_subspace {K F M : Type} [Field K] [CommRing F] [Nontrivial F] [Algebra K F]
    [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M] (D : Submodule K M)
    [FiniteDimensional K D] (h : Submodule.span F (D : Set M) = ⊤) :
    finrank F M ≤ finrank K D := by
  classical
  let bD := Module.finBasis K D
  let s : Finset M := Finset.univ.image fun i => ((bD i : D) : M)
  have hs : Submodule.span F (s : Set M) = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    intro x hx
    have hx' := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hx'
    rw [← hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul F]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [s]))
  calc finrank F M = finrank F (⊤ : Submodule F M) := (finrank_top F M).symm
    _ = finrank F (Submodule.span F (s : Set M)) := by rw [hs]
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ (Finset.univ : Finset (Fin (finrank K D))).card := Finset.card_image_le
    _ = finrank K D := by simp

theorem finrank_mul_le_finrank_DdR_of_spans {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F]
    [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (hs : Spans PD ρ) :
    Module.finrank Qp K * Module.finrank LL V ≤ Module.finrank LL ↥(DdR PD ρ) := by
  classical
  haveI : Nontrivial F := by
    refine nontrivial_of_ne (PD.ι PD.t) 0 fun h0 => PD.not_mem_filtration_two ?_
    rw [h0]
    exact (PD.Fil 2).zero_mem
  unfold Spans mulR at hs
  set W := DdR PD ρ with hW
  let e : V ⊗[Qp] F ≃ₗ[Qp] F ⊗[Qp] V := TensorProduct.comm Qp V F

  have he : ∀ (b : F) (x : V ⊗[Qp] F),
      e (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b) x) = b • e x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

  have hK : ∀ (c : K) (x : V ⊗[Qp] F), x ∈ W →
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) x ∈ W := by
    intro c x hx
    simp only [hW, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    have hcomm : ∀ y : V ⊗[Qp] F, actVdR PD ρ g
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) y) =
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c))
          (actVdR PD ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v z => simp [actVdR]
      | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
    rw [hcomm, hx g]

  let D' : Submodule K (F ⊗[Qp] V) :=
    { carrier := e '' (W : Set (V ⊗[Qp] F))
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, W.add_mem hx hy, map_add e x y⟩
      zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        refine ⟨_, hK c x hx, ?_⟩
        rw [he, algebraMap_smul] }
  have hspan : Submodule.span F (D' : Set (F ⊗[Qp] V)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨m, b, d, hd, hy⟩ := hs (e.symm y)
    have hy' : y = ∑ i, b i • e (d i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← e.apply_symm_apply y, hy, map_sum]
      simp only [he]
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (show e (d i) ∈ (D' : Set (F ⊗[Qp] V)) from ⟨d i, hd i, rfl⟩))
  haveI : FiniteDimensional LL W := hfin
  haveI : FiniteDimensional Qp W := Module.Finite.trans LL W
  let φ : W ≃ₗ[Qp] D' :=
    LinearEquiv.ofBijective
      ({ toFun := fun w => ⟨e (w : V ⊗[Qp] F), (w : V ⊗[Qp] F), w.2, rfl⟩
         map_add' := fun x y => Subtype.ext (map_add e (x : V ⊗[Qp] F) y)
         map_smul' := fun a x => Subtype.ext (map_smul e a (x : V ⊗[Qp] F)) } : W →ₗ[Qp] D')
      ⟨fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy)),
        by rintro ⟨_, w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩⟩
  haveI : FiniteDimensional Qp D' := Module.Finite.equiv φ
  haveI : FiniteDimensional K D' := Module.Finite.of_restrictScalars_finite Qp K D'
  have h1 := finrank_le_of_span_subspace D' hspan
  rw [Module.finrank_baseChange] at h1
  have h2 : finrank Qp K * finrank K D' = finrank Qp LL * finrank LL W := by
    rw [Module.finrank_mul_finrank, ← φ.finrank_eq, Module.finrank_mul_finrank]
  have h3 : finrank Qp LL * finrank LL V = finrank Qp V := Module.finrank_mul_finrank _ _ _
  have hpos : 0 < finrank Qp LL := Module.finrank_pos
  have key : finrank Qp LL * (finrank Qp K * finrank LL V) ≤ finrank Qp LL * finrank LL W :=
    calc finrank Qp LL * (finrank Qp K * finrank LL V)
        = finrank Qp K * finrank Qp V := by rw [← h3]; ring
      _ ≤ finrank Qp K * finrank K D' := Nat.mul_le_mul_left _ h1
      _ = finrank Qp LL * finrank LL W := h2
  exact Nat.le_of_mul_le_mul_left key hpos

end GlobalTheory.DRFil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinBasisSubsetOfIsField
noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

theorem exists_fin_basis_subset_of_isField {F M : Type} [CommRing F] (hF : IsField F) [AddCommGroup M]
    [Module F M] [Module.Finite F M] (S : Set M) (h : Submodule.span F S = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n) F M), ∀ i, b i ∈ S := by
  let := hF.toField
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent F S
  have hsp : ⊤ ≤ Submodule.span F (Set.range ((↑) : t → M)) := by
    rw [Subtype.range_coe, hspan, h]
  let bt : Basis t F M := Basis.mk hli hsp
  have : Finite t := Module.Finite.finite_basis bt
  refine ⟨Nat.card t, bt.reindex (Finite.equivFin t), fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact htS (Subtype.prop _)

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)

def mulRHom (Qp : Type) [Field Qp] (F : Type) [CommRing F] [Algebra Qp F] (V : Type) [AddCommGroup V]
    [Module Qp V] : F →+* Module.End Qp (V ⊗[Qp] F) where
  toFun b := mulR Qp F Qp V b
  map_one' := LinearMap.ext fun x => by
    rw [← sm_one_tmul, ← Algebra.TensorProduct.one_def, sm_one]; rfl
  map_mul' a b := LinearMap.ext fun x => by
    rw [Module.End.mul_apply, ← sm_one_tmul, ← sm_one_tmul, ← sm_one_tmul, ← sm_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_zero' := LinearMap.ext fun x => by
    rw [← sm_one_tmul, TensorProduct.tmul_zero, map_zero]
  map_add' a b := LinearMap.ext fun x => by
    rw [LinearMap.add_apply, ← sm_one_tmul, ← sm_one_tmul, ← sm_one_tmul, TensorProduct.tmul_add,
      map_add, LinearMap.add_apply]

theorem spans_dual_base {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V]
    (ρ : Representation Qp G V) {V' : Type} [AddCommGroup V'] [Module Qp V']
    (ρ' : Representation Qp G V') (β : V →ₗ[Qp] V' →ₗ[Qp] Qp) (hF : IsField F)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hb : Function.Bijective β.flip)
    (h : Spans PD ρ) : Spans PD ρ' := by
  classical
  let _ : Module F (V ⊗[Qp] F) := Module.compHom (V ⊗[Qp] F) (mulRHom Qp F V)
  have hsm : ∀ (c : F) (y : V ⊗[Qp] F), c • y = mulR Qp F Qp V c y := fun _ _ => rfl
  let bV := Module.finBasis Qp V
  let κ : Fin (Module.finrank Qp V) → (V ⊗[Qp] F) →ₗ[Qp] F := fun k =>
    (TensorProduct.lid Qp F).toLinearMap ∘ₗ TensorProduct.map (bV.coord k) LinearMap.id
  have hκ : ∀ k (v : V) (c : F), κ k (v ⊗ₜ c) = bV.coord k v • c := fun k v c => by simp [κ]
  have hκmul : ∀ k (c : F) (y : V ⊗[Qp] F), κ k (c • y) = c * κ k y := by
    intro k c y
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero, mul_zero]
    | tmul v a => simp only [hsm, mulR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, hκ, mul_smul_comm]
    | add y₁ y₂ h₁ h₂ => simp only [smul_add, map_add (f := _), h₁, h₂, mul_add]
  have hdec : ∀ y : V ⊗[Qp] F, y = ∑ k, κ k y • (bV k ⊗ₜ[Qp] (1 : F)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      simp only [hκ, hsm, mulR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, mul_one]
      conv_lhs => rw [← bV.sum_repr v]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [TensorProduct.smul_tmul, Basis.coord_apply]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) h₁ h₂
  have hspanD : Submodule.span F (DdR PD ρ : Set (V ⊗[Qp] F)) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨m, b, d, hd, rfl⟩ := h y
    exact Submodule.sum_mem _ fun i _ => by
      rw [← hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hd i))
  have hfin : Module.Finite F (V ⊗[Qp] F) := by
    refine ⟨⟨Finset.univ.image fun k => bV k ⊗ₜ[Qp] (1 : F), eq_top_iff.2 fun y _ => ?_⟩⟩
    rw [hdec y]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨m, E, hE⟩ := exists_fin_basis_subset_of_isField hF (DdR PD ρ : Set (V ⊗[Qp] F)) hspanD
  have hinv : ∀ y : V ⊗[Qp] F, y ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g y = y := by
    intro y
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hinv' : ∀ y : V' ⊗[Qp] F, y ∈ DdR PD ρ' ↔ ∀ g, actVdR PD ρ' g y = y := by
    intro y
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hact : ∀ g (c : F) (y : V ⊗[Qp] F),
      actVdR PD ρ g (c • y) = PD.actdR g c • actVdR PD ρ g y := by
    intro g c y
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul v a => simp [hsm, mulR, actVdR]
    | add y₁ y₂ h₁ h₂ => simp only [smul_add, map_add (f := _), h₁, h₂]
  have hcoord : ∀ g i (y : V ⊗[Qp] F), E.coord i (actVdR PD ρ g y) = PD.actdR g (E.coord i y) := by
    intro g i y
    have h1 : actVdR PD ρ g y = ∑ j, PD.actdR g (E.repr y j) • E j := by
      conv_lhs => rw [← E.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hact, (hinv _).1 (hE j) g]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    simp [Basis.coord_apply, Finsupp.single_apply]
  let e := LinearEquiv.ofBijective β.flip hb
  let w : Fin (Module.finrank Qp V) → V' := fun j => e.symm (bV.coord j)
  have hw : ∀ x j, β x (w j) = bV.coord j x := fun x j => by
    have h1 : β.flip (w j) = bV.coord j := e.apply_symm_apply (bV.coord j)
    exact LinearMap.congr_fun h1 x
  have hw' : ∀ v' : V', v' = ∑ j, β (bV j) v' • w j := by
    intro v'
    apply hb.1
    refine LinearMap.ext fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, hw, smul_eq_mul]
    conv_lhs => rw [← bV.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Basis.coord_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let π : V → (V' ⊗[Qp] F) →ₗ[Qp] F := fun x =>
    (TensorProduct.lid Qp F).toLinearMap ∘ₗ TensorProduct.map (β x) LinearMap.id
  have hπ : ∀ x v' (c : F), π x (v' ⊗ₜ c) = β x v' • c := fun x v' c => by simp [π]
  have hπmul : ∀ x (c : F) z, π x (mulR Qp F Qp V' c z) = c * π x z := by
    intro x c z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul v' a => simp only [mulR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, hπ, mul_smul_comm]
    | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂, mul_add]
  have hπact : ∀ g x z, π (ρ g x) (actVdR PD ρ' g z) = PD.actdR g (π x z) := by
    intro g x z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v' a =>
      simp [actVdR, hπ, hβ, Algebra.smul_def, IsScalarTower.algebraMap_apply Qp K F]
    | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  have hzdec : ∀ z : V' ⊗[Qp] F, z = ∑ j, w j ⊗ₜ π (bV j) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v' a =>
      simp only [hπ]
      conv_lhs => rw [hw' v']
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul]
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) h₁ h₂
  have hπext : ∀ z z' : V' ⊗[Qp] F, (∀ x, π x z = π x z') → z = z' := by
    intro z z' hz
    rw [hzdec z, hzdec z']
    simp only [hz]
  let d' : Fin m → V' ⊗[Qp] F := fun i => ∑ j, w j ⊗ₜ[Qp] E.coord i (bV j ⊗ₜ[Qp] (1 : F))
  have hπd' : ∀ x i, π x (d' i) = E.coord i (x ⊗ₜ[Qp] (1 : F)) := by
    intro x i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdec (x ⊗ₜ[Qp] (1 : F)), map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [d', map_sum, hπ, hw, hκ, map_smul, smul_eq_mul, smul_one_mul]
  have hd'inv : ∀ i g, actVdR PD ρ' g (d' i) = d' i := by
    intro i g
    apply hπext
    intro x
    have hx : ρ g (ρ g⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hx, hπact, hπd', hπd', ← hcoord]
    simp [actVdR]
  intro y'
  let c : Fin m → F := fun i => ∑ k, π (bV k) y' * κ k (E i)
  refine ⟨m, c, d', fun i => (hinv' _).2 (hd'inv i), ?_⟩
  apply hπext
  intro x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [hπmul, hπd']
  have hx1 : x ⊗ₜ[Qp] (1 : F) = ∑ i, E.coord i (x ⊗ₜ[Qp] (1 : F)) • E i := by
    simp only [Basis.coord_apply]
    exact (E.sum_repr _).symm
  have key : ∀ k, κ k (x ⊗ₜ[Qp] (1 : F)) = ∑ i, E.coord i (x ⊗ₜ[Qp] (1 : F)) * κ k (E i) := by
    intro k
    conv_lhs => rw [hx1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hκmul]
  calc π x y' = ∑ k, bV.coord k x • π (bV k) y' := by
        conv_lhs => rw [hzdec y']
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, hπ, hw]
    _ = ∑ k, π (bV k) y' * κ k (x ⊗ₜ[Qp] (1 : F)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hκ, mul_smul_comm, mul_one]
    _ = ∑ k, π (bV k) y' * ∑ i, E.coord i (x ⊗ₜ[Qp] (1 : F)) * κ k (E i) := by
        simp only [key]
    _ = ∑ i, c i * E.coord i (x ⊗ₜ[Qp] (1 : F)) := by
        simp only [c, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

variable (Qp) in
def resRep (ρ : Representation LL G V) : Representation Qp G V where
  toFun g := (ρ g).restrictScalars Qp
  map_one' := LinearMap.ext fun x => by simp
  map_mul' a b := LinearMap.ext fun x => by simp

theorem spans_resRep_iff (ρ : Representation LL G V) : Spans PD (resRep Qp ρ) ↔ Spans PD ρ := by
  have hm : ∀ (b : F) (y : V ⊗[Qp] F), mulR Qp F Qp V b y = mulR Qp F LL V b y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v c => simp [mulR]
    | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz]
  have hd : ∀ y : V ⊗[Qp] F, y ∈ DdR PD (resRep Qp ρ) ↔ y ∈ DdR PD ρ := by
    intro y
    have ha : ∀ g, actVdR PD (resRep Qp ρ) g y = actVdR PD ρ g y := by
      intro g
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v c => simp [actVdR, resRep]
      | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz]
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, ha]
  unfold Spans
  simp only [hd, hm]

theorem spans_dual [FiniteDimensional Qp LL] [CharZero Qp] [FiniteDimensional LL V]
    (ρ : Representation LL G V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL) (hF : IsField F)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hb : Function.Bijective β.flip)
    (h : Spans PD ρ) : Spans PD ρ' := by
  have hVf : FiniteDimensional Qp V := Module.Finite.trans LL V
  let e := LinearEquiv.ofBijective β.flip hb
  have hV'L : FiniteDimensional LL V' := Module.Finite.equiv e.symm
  have hV'f : FiniteDimensional Qp V' := Module.Finite.trans LL V'
  let tr : LL →ₗ[Qp] Qp := Algebra.trace Qp LL
  let β₀ : V →ₗ[Qp] V' →ₗ[Qp] Qp := LinearMap.mk₂ Qp (fun x y => tr (β x y))
    (fun x₁ x₂ y => by simp only [map_add (f := _), LinearMap.add_apply])
    (fun c x y => by
      simp only [LinearMap.map_smul_of_tower, LinearMap.smul_apply, map_smul])
    (fun x y₁ y₂ => by simp only [map_add (f := _)])
    (fun c x y => by simp only [LinearMap.map_smul_of_tower, map_smul])
  have hβ₀ : ∀ g x y, β₀ (resRep Qp ρ g x) (resRep Qp ρ' g y) = β₀ x y := by
    intro g x y
    show tr (β (ρ g x) (ρ' g y)) = tr (β x y)
    rw [hβ]
  have hinj : Function.Injective β₀.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : ∀ x, β x y = 0 := by
      intro x
      refine (traceForm_nondegenerate Qp LL).1 (β x y) (fun c => ?_)
      have := LinearMap.congr_fun hy (c • x)
      simp only [LinearMap.flip_apply, LinearMap.zero_apply] at this
      rw [Algebra.traceForm_apply, mul_comm]
      change tr (c * β x y) = 0
      rw [← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.map_smul]
      exact this
    apply hb.1
    rw [map_zero]
    ext x
    exact h1 x
  have hrank : Module.finrank Qp V' = Module.finrank Qp (V →ₗ[Qp] Qp) := by
    rw [← Module.finrank_mul_finrank Qp LL V', LinearEquiv.finrank_eq e,
      Subspace.dual_finrank_eq, Module.finrank_mul_finrank]
    exact (Subspace.dual_finrank_eq (K := Qp) (V := V)).symm
  have hb₀ : Function.Bijective β₀.flip :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj⟩
  have h₀ : Spans PD (resRep Qp ρ) := (spans_resRep_iff PD ρ).2 h
  exact (spans_resRep_iff PD ρ').1 (spans_dual_base PD (resRep Qp ρ) (resRep Qp ρ') β₀ hF hβ₀ hb₀ h₀)

end Period

theorem spans_dual_of_spans : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] [FiniteDimensional LL V'] (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL), IsField F → (∀ g x y, β (ρ g x) (ρ' g y) = β x y) → Function.Bijective β.flip → Spans PD ρ → Spans PD ρ' := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B F _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _ _ V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' β hF hβ hb h
  exact spans_dual PD ρ ρ' β hF hβ hb h

end GlobalTheory.DRFil
end
end

noncomputable section

namespace GlobalTheory.DRFil

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open scoped Formalism.Per

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
    [FiniteDimensional Qp K] [CharZero Qp] [FiniteDimensional Qp LL]

theorem exists_adapted_of_surjective (hF : IsField F) [FiniteDimensional LL V'] (ρ : Representation LL G V)
    (ρ' : Representation LL G V') [FiniteDimensional LL ↥(DdR PD ρ')] (g : V →ₗ[LL] V')
    (hg : ∀ σ v, g (ρ σ v) = ρ' σ (g v)) (hs : Function.Surjective g) (h : FilSpans PD ρ) (τ : K →ₐ[Qp] LL) :
    (∃ (m : ℕ) (d : Fin m → V' ⊗[Qp] F) (k : Fin m → ℤ), Adapted PD ρ' τ d k) ∧
      ∀ a, (FildR PD ρ τ a).map (ext Qp F g) = FildR PD ρ' τ a := by
  classical
  have hle : ∀ a, (FildR PD ρ τ a).map (ext Qp F g) ≤ FildR PD ρ' τ a := by
    rintro a _ ⟨x, hx, rfl⟩
    exact ext_mem_FildR PD ρ ρ' g hg τ hx
  obtain ⟨m, d, k, hli, hA⟩ := GlobalTheory.filtration_adapted_basis (fun a => (FildR PD ρ τ a).map (ext Qp F g))
    (fun a b hab => Submodule.map_mono (FildR_antitone PD ρ τ hab))
    (Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ') (iSup_le fun a y hy => (hle a hy).1.1))
    (fun x hx => eq_zero_of_forall_mem_FilV PD (LL := LL) x fun a => (hle a (hx a)).2)
  have hmem : ∀ i, d i ∈ FildR PD ρ' τ (k i) := fun i =>
    hle _ ((hA (k i)).ge (Submodule.subset_span ⟨i, le_refl (k i), rfl⟩))
  have had : Adapted PD ρ' τ d k := by
    refine ⟨hmem, GlobalTheory.DRFil.indep_of_linearIndependent_DdRE PD ρ' τ d hF (fun i => (hmem i).1) hli, fun n y hy => ?_⟩
    let q : V' ⊗[Qp] F → Prop := fun y => ∃ r : Fin m → LL ⊗[Qp] F,
      (∀ i, r i ∈ FilV PD (LL := LL) (V := LL) (n - k i)) ∧ y = ∑ i, sm Qp F LL V' (r i) (d i)
    have q0 : q 0 := ⟨0, fun _ => Submodule.zero_mem _, by simp⟩
    have qa : ∀ x y, q x → q y → q (x + y) := by
      rintro x y ⟨r, hr, hx⟩ ⟨s, hs, hy⟩
      exact ⟨r + s, fun p => Submodule.add_mem _ (hr p) (hs p), by
        simp only [map_add (f := _), hx, hy, Pi.add_apply, LinearMap.add_apply, Finset.sum_add_distrib]⟩
    have qs : ∀ (c : LL) x, q x → q (c • x) := by
      rintro c x ⟨r, hr, hx⟩
      exact ⟨c • r, fun p => Submodule.smul_mem _ _ (hr p), by
        simp only [map_smul, hx, Pi.smul_apply, LinearMap.smul_apply, Finset.smul_sum]⟩
    have qm : ∀ (a : ℤ) (b : F), b ∈ PD.Fil (n - a) → ∀ x ∈ Submodule.span LL (d '' {i | a ≤ k i}),
        q (mulR Qp F LL V' b x) := by
      intro a b hb x hx
      induction hx using Submodule.span_induction with
      | zero => simpa using q0
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact qa _ _ hx hy
      | smul c x _ hx => rw [map_smul]; exact qs _ _ hx
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        refine ⟨Pi.single i ((1 : LL) ⊗ₜ[Qp] b), fun j => ?_, ?_⟩
        · by_cases hj : j = i
          · subst hj
            rw [Pi.single_eq_same]
            exact tmul_mem_FilV PD _ (fil_antitone PD (sub_le_sub_left hi n) hb)
          · rw [Pi.single_eq_of_ne hj]
            exact Submodule.zero_mem _
        · rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp),
            Pi.single_eq_same, sm_one_tmul]
    obtain ⟨x, hx, rfl⟩ := exists_ext_mem_FilV PD g hs hy
    obtain ⟨m', k', b, e, he, rfl⟩ := h n x hx
    change q _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_induction _ q qa q0 fun i _ => ?_
    rw [ext_mulR, ← sm_one_tmul, sm_comm, sm_one_tmul, ← ext_sm]
    refine qm (k' i) (b i) (he i).2.2 _ ((hA (k' i)).le ⟨_, ⟨?_, ?_⟩, rfl⟩)
    · exact sm_idem_mem_DdRE PD ρ τ (he i).1
    · exact sm_idem_mem_FilV PD τ (he i).2.1
  exact ⟨⟨m, d, k, had⟩, fun a => (hA a).trans (had.fil_eq a).symm⟩

theorem exists_adapted (hF : IsField F) [FiniteDimensional LL V] (ρ : Representation LL G V)
    [FiniteDimensional LL ↥(DdR PD ρ)] (h : FilSpans PD ρ) (τ : K →ₐ[Qp] LL) :
    ∃ (m : ℕ) (d : Fin m → V ⊗[Qp] F) (k : Fin m → ℤ), Adapted PD ρ τ d k :=
  (exists_adapted_of_surjective PD hF ρ ρ LinearMap.id (fun _ _ => rfl) Function.surjective_id h τ).1

omit [FiniteDimensional Qp K] [CharZero Qp] [FiniteDimensional Qp LL] in
theorem twist_jumps (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (htw : IsTwistRep (cycLL PD LL) ρ ρ') (u : F) (hu : PD.ι PD.t * u = 1) (hu' : u ∈ PD.Fil (-1))
    (h : IsDR PD ρ) : IsDR PD ρ' ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (IsJumpV PD ρ' τ (a - 1) ↔ IsJumpV PD ρ τ a) ∧ multV PD ρ' τ (a - 1) = multV PD ρ τ a := by
  obtain ⟨Φ, hD, hF⟩ := exists_twist_equiv PD ρ ρ' htw u hu hu'
  refine ⟨?_, fun τ a => ?_⟩
  · obtain ⟨e, -⟩ := htw
    rw [IsDR, ← hD, LinearEquiv.finrank_map_eq, h, e.finrank_eq]
  · have e1 : a - 1 + 1 = a + 1 - 1 := by ring
    unfold IsJumpV multV
    rw [e1, ← hF, ← hF, LinearEquiv.finrank_map_eq, LinearEquiv.finrank_map_eq]
    exact ⟨(Submodule.map_injective_of_injective Φ.injective).ne_iff, rfl⟩

omit [FiniteDimensional Qp LL] in
theorem component_iso (h : TensInj PD) (ρ : Representation LL G V)
    (hs : ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (x : Fin m → V ⊗[Qp] B),
      (∀ i, x i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)))
    (τ : K →ₐ[Qp] LL) :
    ∃ e : ↥(DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) ≃ₗ[LL] ↥(DdRE PD ρ τ),
      ∀ x : ↥(DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))),
        ιV PD (LL := LL) (V := V) (x : V ⊗[Qp] B) - (e x : V ⊗[Qp] F) ∈ Submodule.span LL
          {z | ∃ (c : K), ∃ y ∈ DdR PD ρ,
            z = mulVdR (Qp := Qp) (K := K) (BdR := F) (LL := LL) (V := V) c y - τ c • y} := by
  obtain ⟨e, he⟩ := exists_component_equiv PD h ρ hs τ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K)) fun _ => rfl
  refine ⟨e, fun x => ?_⟩
  rw [he]
  exact sub_sm_idem_mem PD ρ τ (ιV_mem_DdR PD ρ x.2.1)

end Generic

theorem zpow_neg_mul_cancel {R : Type} [CommRing R] (u : Rˣ) (k : ℤ) (b : R) :
    ((u ^ (-k) : Rˣ) : R) * (((u ^ k : Rˣ) : R) * b) = b := by
  rw [zpow_neg, Units.inv_mul_cancel_left]

theorem sum_conv {ι ι' : Type} [Fintype ι] [Fintype ι'] (k : ι → ℤ) (k' : ι' → ℤ) (S : Finset ℤ)
    (hS : ∀ i, k i ∈ S) (c : ℤ) : (∑ p : ι × ι', if k p.1 + k' p.2 = c then (1 : ℤ) else 0) =
      ∑ a ∈ S, (∑ i, if k i = a then (1 : ℤ) else 0) * ∑ j, if k' j = c - a then (1 : ℤ) else 0 := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hS i)]
  exact Finset.sum_congr rfl fun j _ => if_congr (by omega) rfl rfl

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
include T

theorem isField_dR : IsField P.R.BdR := by
  obtain ⟨C, -⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨_, _, -, -, -, -, _⟩ := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
  exact T.eD.toMulEquiv.isField (IsFractionRing.toField (K := Per.BdR l) (Per.BdRp l)).toIsField

theorem inv_t_mem (K : FinExt l) (u : P.R.BdR) (hu : (P.PD K).ι (P.PD K).t * u = 1) :
    u ∈ (P.PD K).Fil (-1) := by
  obtain ⟨s, hs, h⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  rw [P.PD_ι, P.period_datum_t_eq] at hu
  have e : u = s := by
    rw [← one_mul u, ← h, mul_right_comm, hu, one_mul]
  rw [e]
  exact (T.fil K _ _).2 ((T.fil _ _ _).1 hs)

theorem tensInj (K : FinExt l) : TensInj (P.PD K) := fun m c hc b hb =>
  GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m c hc b (by simpa only [P.PD_ι] using hb)

section Rep

variable (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

theorem isDR_of_spans (h : Spans (P.PD K) ρ) : IsDR (P.PD K) ρ := by
  have := K.2
  have := LL.2
  obtain ⟨h1, h2⟩ := GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ
  exact le_antisymm h2 (GlobalTheory.DRFil.finrank_mul_le_finrank_DdR_of_spans (P.PD K) ρ h1 h)

theorem filSpans (h : IsDR (P.PD K) ρ) : FilSpans (P.PD K) ρ := GlobalTheory.T.deRham_comparison_isFiltered l P AI T K LL V ρ h

theorem crys (h : IsCrys (P.PD K) ρ) : IsDR (P.PD K) ρ ∧ ∀ y ∈ DdR (P.PD K) ρ,
    ∃ (m : ℕ) (c : Fin m → ↥K.1) (x : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, x i ∈ Dcris (P.PD K) ρ) ∧
      y = ∑ i, mulR ℚ_[l] P.R.BdR ↥LL.1 V (algebraMap ↥K.1 P.R.BdR (c i))
        (ιV (P.PD K) (LL := ↥LL.1) (V := V) (x i)) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ
  exact isDR_of_isCrys (P.PD K) (tensInj T K) ρ h2 h

end Rep

open GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

variable (K LL : FinExt l)

theorem crysDeRhamAt : CrysDeRhamAt P K LL := fun L h => (crys T K LL L.ρ h).1

theorem ddRSpanAt : DdRSpanAt P K LL := by
  intro L h
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, c, x, hx, rfl⟩ := (crys T K LL L.ρ h).2 y hy
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨c i, x i, hx i, rfl⟩
  · rintro _ ⟨c, x, hx, rfl⟩
    exact mulR_mem_DdR (P.PD K) L.ρ c (ιV_mem_DdR (P.PD K) L.ρ hx)

theorem componentIsoAt : ComponentIsoAt P K LL := by
  intro L h τ
  have := K.2
  exact component_iso (P.PD K) (tensInj T K) L.ρ (crys T K LL L.ρ h).2 τ

theorem unramOntoAt : UnramOntoAt P K LL := by
  intro hK L h
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ιV_mem_DdR (P.PD K) L.ρ hx
  · obtain ⟨m, c, x, hx, rfl⟩ := (crys T K LL L.ρ h).2 y hy
    refine Submodule.sum_mem _ fun i _ => ⟨_, mulR_mem_Dcris (P.PD K) L.ρ ⟨(c i).1, (c i).2, hK (c i).2⟩ (hx i), ?_⟩
    rw [ιV_mulR, AlgHom.commutes]
    rfl

theorem tdR_zpow_mem (a : ℤ) : ((tdR P K ^ a : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD K).Fil a := by
  have h1 : (tdR P K : P.R.BdR) ∈ (P.PD K).Fil 1 := (P.PD K).mem_filtration_one
  have h2 : ((tdR P K)⁻¹ : P.R.BdRˣ).1 ∈ (P.PD K).Fil (-1) := inv_t_mem T K _ (tdR P K).mul_inv
  induction a using Int.induction_on with
  | zero => simpa using (P.PD K).one_mem
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul]
    exact (P.PD K).Fil_mul _ _ _ _ ih h1
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul]
    exact (P.PD K).Fil_mul _ _ _ _ ih h2

theorem filZeroAt : FilZeroAt P K LL := by
  intro L h
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, k, b, d, hd, rfl⟩ := filSpans T K LL L.ρ h 0 y hy
    refine Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨k i, ((tdR P K ^ k i : P.R.BdRˣ) : P.R.BdR) * b i, ?_, d i, ⟨(hd i).1, (hd i).2.1⟩, ?_⟩
    · simpa using (P.PD K).Fil_mul _ _ _ _ (tdR_zpow_mem T K (k i)) (hd i).2.2
    · exact congrArg (fun c => mulVR L c (d i)) (zpow_neg_mul_cancel (tdR P K) (k i) (b i)).symm
  · rintro _ ⟨a, b, hb, d, hd, rfl⟩
    have := mulR_mem_FilV (P.PD K) (LL := ↥LL.1)
      ((P.PD K).Fil_mul _ _ _ _ (tdR_zpow_mem T K (-a)) hb) hd.2
    rwa [add_zero, neg_add_cancel] at this

theorem strictAt : StrictAt P K LL := by
  rintro L₀ L₁ L₂ f g ⟨hf, hg, hi, hex, hs⟩ - h₁ - τ a
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL L₂.V L₂.ρ).1
  refine ⟨fun x _ hx => ext_injective f hi (hx.trans (map_zero _).symm), fun y => ⟨?_, ?_⟩, fun z => ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ext_mem_FildR _ _ _ f hf τ hx, (ext_exact f g hex hs _).2 ⟨x, rfl⟩⟩
  · rintro ⟨hy, h0⟩
    obtain ⟨x, rfl⟩ := (ext_exact f g hex hs y).1 h0
    exact ⟨x, mem_FildR_of_ext _ _ _ f hf hi τ hy, rfl⟩
  · rw [← (exists_adapted_of_surjective (P.PD K) (isField_dR T) L₁.ρ L₂.ρ g hg hs
      (filSpans T K LL L₁.ρ h₁) τ).2 a]
    rfl

theorem dualJumpsAt : DualJumpsAt P K LL := by
  rintro L L' β ⟨hβ, hβ'⟩ h
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL L.V L.ρ).1
  have hs := filSpans T K LL L.ρ h
  refine ⟨isDR_of_spans T K LL L'.ρ
    (GlobalTheory.DRFil.spans_dual_of_spans (P.PD K) L.ρ L'.ρ β (isField_dR T) hβ hβ' (hs.spans _)), fun τ a => ?_⟩
  obtain ⟨m, d, k, had⟩ := exists_adapted (P.PD K) (isField_dR T) L.ρ hs τ
  obtain ⟨d', had'⟩ := had.dual L'.ρ β hβ hβ'
  rw [had.isJumpV_iff, had'.isJumpV_iff, had.multV_eq, had'.multV_eq]
  simp only [neg_eq_iff_eq_neg, and_self]

theorem tensorJumpsAt : TensorJumpsAt P K LL := by
  intro L₁ L₂ L₃ e he h₁ h₂
  have := K.2
  have := LL.2
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL L₁.V L₁.ρ).1
  have := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL L₂.V L₂.ρ).1
  have hs₁ := filSpans T K LL L₁.ρ h₁
  have hs₂ := filSpans T K LL L₂.ρ h₂
  refine ⟨isDR_of_spans T K LL L₃.ρ (Spans.tensor _ e he (hs₁.spans _) (hs₂.spans _)), fun τ c => ?_⟩
  obtain ⟨m, d, k, had⟩ := exists_adapted (P.PD K) (isField_dR T) L₁.ρ hs₁ τ
  obtain ⟨m', d', k', had'⟩ := exists_adapted (P.PD K) (isField_dR T) L₂.ρ hs₂ τ
  have had₃ := had.tensor had' L₃.ρ e he
  refine ⟨?_, fun S hS => ?_⟩
  · simp only [had.isJumpV_iff, had'.isJumpV_iff, had₃.isJumpV_iff]
    exact ⟨fun ⟨p, hp⟩ => ⟨_, _, ⟨p.1, rfl⟩, ⟨p.2, rfl⟩, hp⟩,
      fun ⟨_, _, ⟨i, hi⟩, ⟨j, hj⟩, h⟩ => ⟨(i, j), by rw [hi, hj, h]⟩⟩
  · simp only [had.multV_eq, had'.multV_eq, had₃.multV_eq]
    exact sum_conv k k' S (fun i => hS _ ((had.isJumpV_iff _).2 ⟨i, rfl⟩)) c

theorem twistJumpsAt : TwistJumpsAt P K LL := fun L L' htw h =>
  twist_jumps (P.PD K) L.ρ L'.ρ htw _ (tdR P K).mul_inv (inv_t_mem T K _ (tdR P K).mul_inv) h

theorem potCrysDeRhamAt : PotCrysDeRhamAt P K LL := fun L K' hK h =>
  isDR_of_spans T K LL L.ρ (GlobalTheory.DRFil.spans_descent l P K K' LL hK L.V L.ρ
    ((filSpans T K' LL _ (crys T K' LL _ h).1).spans _))


omit T in
theorem deRhamComparison (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (h : GlobalTheory.Per.IsStd P AI) : DeRhamComparison l P := by
  obtain ⟨T⟩ := h
  exact ⟨fun K _ LL _ => crysDeRhamAt T K LL, fun K _ LL _ => ddRSpanAt T K LL,
    fun K _ LL _ => componentIsoAt T K LL, fun K _ LL _ => unramOntoAt T K LL,
    fun K _ LL _ => filZeroAt T K LL, fun K _ LL _ => strictAt T K LL, fun K _ LL _ => dualJumpsAt T K LL,
    fun K _ LL _ => tensorJumpsAt T K LL, fun K _ LL _ => twistJumpsAt T K LL,
    fun K _ LL _ => potCrysDeRhamAt T K LL⟩

end GlobalTheory.DRFil
