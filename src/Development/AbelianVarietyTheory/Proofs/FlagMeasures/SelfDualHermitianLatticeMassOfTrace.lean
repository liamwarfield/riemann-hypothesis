module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassBounds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentOfGram
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.OverBasis

open Matrix GlobalTheory.HL.SelfDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_comb (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin m → Fin n → E)
    (c : Fin m → E) : (fun a => hf L Hm (∑ b, c b • y b) (y a)) = gramT L Hm y *ᵥ c := by
  funext a
  rw [hf_sum_l]
  simp [gramT, Matrix.mulVec, dotProduct, mul_comm]

theorem linearIndependent_of_gram (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (y : Fin m → Fin n → E) (h : IsUnit (gramT L Hm y).det) : LinearIndependent E y := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h1 := hf_comb L Hm y c
  rw [hc] at h1
  have h2 : gramT L Hm y *ᵥ c = 0 := by
    rw [← h1]; funext a; simp [hf]
  have h3 : (gramT L Hm y)⁻¹ *ᵥ (gramT L Hm y *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_zero] at h3
  exact fun i => congrFun h3.symm i

omit [TopologicalSpace E] in
theorem sum_smul_rmul {n m : ℕ} (y : Fin m → Fin n → E) (B : Matrix (Fin m) (Fin m) E)
    (c : Fin m → E) : ∑ j, c j • rmul y B j = ∑ i, (B *ᵥ c) i • y i := by
  simp only [rmul, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem exists_basis_overlattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (y : Fin m → Fin n → E), IsUnit (gramT L Hm y).det → ∀ Mh : Submodule L.O (Fin n → E), Submodule.span L.O (Set.range y) ≤ Mh → (∀ v ∈ Mh, v ∈ Submodule.span E (Set.range y)) → (∀ v ∈ Mh, ∀ w ∈ Mh, hf L Hm v w ∈ L.O) → LinearIndependent E y ∧ ∃ A : Matrix (Fin m) (Fin m) E, IsIntM L A ∧ IsUnit A.det ∧ Mh = Submodule.span L.O (Set.range (rmul y A⁻¹)) ∧ LinearIndependent E (rmul y A⁻¹) ∧ rmul (rmul y A⁻¹) A = y := by
  intro F _ _ _ _ _ E _ _ _ L n Hm _ m y hG Mh hy hsp hint
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  have hli := linearIndependent_of_gram L Hm y hG
  refine ⟨hli, ?_⟩
  have hyM : ∀ a, y a ∈ Mh := fun a => hy (Submodule.subset_span ⟨a, rfl⟩)
  let f : (Fin m → L.O) →ₗ[L.O] (Fin n → E) :=
    { toFun := fun w => ∑ i, ((gramT L Hm y)⁻¹ *ᵥ fun a => (w a : E)) i • y i
      map_add' := fun v w => by
        have : (fun a => ((v + w) a : E)) = (fun a => (v a : E)) + fun a => (w a : E) := rfl
        rw [this, Matrix.mulVec_add]
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        have : (fun a => ((c • v) a : E)) = (c : E) • fun a => (v a : E) := rfl
        rw [this, Matrix.mulVec_smul, RingHom.id_apply, Subring.smul_def, Finset.smul_sum]
        simp only [Pi.smul_apply, smul_assoc] }
  have hle : Mh ≤ LinearMap.range f := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (hsp v hv)
    refine ⟨fun a => ⟨_, hint _ hv _ (hyM a)⟩, ?_⟩
    show ∑ i, ((gramT L Hm y)⁻¹ *ᵥ fun a => hf L Hm (∑ b, c b • y b) (y a)) i • y i = _
    rw [hf_comb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]
  obtain ⟨b, hb⟩ := exists_eq_span_range m (Mh.comap f)
  let B : Matrix (Fin m) (Fin m) E :=
    Matrix.of fun i j => ((gramT L Hm y)⁻¹ *ᵥ fun a => (b j a : E)) i
  have hM : Mh = Submodule.span L.O (Set.range (rmul y B)) := by
    rw [← Submodule.map_comap_eq_of_le hle, hb, Submodule.map_span, ← Set.range_comp]
    rfl
  have hA : ∀ j, ∃ c : Fin m → L.O, ∑ i, c i • rmul y B i = y j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun L.O).1 (hM ▸ hyM j)
  choose c hc using hA
  let A : Matrix (Fin m) (Fin m) E := Matrix.of fun i j => (c j i : E)
  have hA : rmul (rmul y B) A = y := funext hc
  have hBA : B * A = 1 := by
    ext i j
    have h1 : ∑ i, (B *ᵥ fun k => A k j) i • y i = y j := by
      rw [← sum_smul_rmul]; exact hc j
    have h2 : ∑ i, ((B *ᵥ fun k => A k j) - (Pi.single j 1 : Fin m → E)) i • y i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1]
      simp [Pi.single_apply]
    have h3 := sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h2 i)
    rw [Matrix.one_apply, ← Pi.single_apply, ← h3]
    rfl
  have hinv : A⁻¹ = B := Matrix.inv_eq_left_inv hBA
  refine ⟨A, fun i j => (c j i).2, Matrix.isUnit_det_of_left_inverse hBA, ?_⟩
  rw [hinv]
  refine ⟨hM, ?_, hA⟩
  rw [Fintype.linearIndependent_iff]
  intro d hd
  rw [sum_smul_rmul] at hd
  have h1 : B *ᵥ d = 0 := funext (Fintype.linearIndependent_iff.1 hli _ hd)
  have h2 : A *ᵥ (B *ᵥ d) = d := by
    rw [Matrix.mulVec_mulVec, mul_eq_one_comm.1 hBA, Matrix.one_mulVec]
  rw [h1, Matrix.mulVec_zero] at h2
  exact fun i => congrFun h2.symm i

end GlobalTheory.HL.OverBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanEqMap
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.MatrixIndex

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_basis [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∃ b : Module.Basis (Fin 2) F E, (∀ x, x ∈ L.O ↔ ∀ i, b.repr x i ∈ 𝒪[F]) ∧
      ∀ x, algebraMap F E (Algebra.norm F x) = x * L.cj x := by
  obtain ⟨ω, hω, e, he, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hint : ∀ a : F, a ∈ 𝒪[F] → algebraMap F E a ∈ L.O := fun a h =>
    (GlobalTheory.UnramOrder.algebraMap_mem_iff L a).2 h
  have he' : (L.cj ω - ω) * L.cj e = 1 := by simpa [L.cj_cj] using congrArg L.cj hωe
  have hce : L.cj e = -e := by linear_combination (-e) * he' - (L.cj e) * hωe
  have hli : LinearIndependent F ![(1 : E), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    simp only [Algebra.smul_def, mul_one] at h
    have h' := congrArg L.cj h
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, map_zero] at h'
    have ht : algebraMap F E t = 0 := by
      linear_combination e * h - e * h' - algebraMap F E t * hωe
    have hs : algebraMap F E s = 0 := by rw [ht] at h; simpa using h
    exact ⟨GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using hs),
      GlobalTheory.UnramOrder.algebraMap_inj L (by simpa using ht)⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [L.rank])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = ω := by simp [b]
  have hx : ∀ x, x = algebraMap F E (b.repr x 0) + algebraMap F E (b.repr x 1) * ω := by
    intro x
    have := b.sum_repr x
    rw [Fin.sum_univ_two, hb0, hb1] at this
    simpa [Algebra.smul_def] using this.symm
  refine ⟨b, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · have h1 := hx x
    have h2 := congrArg L.cj h1
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes] at h2
    have h3 : algebraMap F E (b.repr x 1) = (x - L.cj x) * e := by
      linear_combination -e * h1 + e * h2 - algebraMap F E (b.repr x 1) * hωe
    have h4 : algebraMap F E (b.repr x 1) ∈ L.O := by
      rw [h3]
      exact L.O.mul_mem (L.O.sub_mem h (GlobalTheory.UnramOrder.cj_mem L h)) he
    have h5 : algebraMap F E (b.repr x 0) ∈ L.O := by
      have : algebraMap F E (b.repr x 0) = x - algebraMap F E (b.repr x 1) * ω := by
        linear_combination -h1
      rw [this]
      exact L.O.sub_mem h (L.O.mul_mem h4 hω)
    intro i
    fin_cases i
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h5
    · exact (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 h4
  · rw [hx x]
    exact L.O.add_mem (hint _ (h 0)) (L.O.mul_mem (hint _ (h 1)) hω)
  · rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, mul_one, map_sub, map_mul]
    have h1 := hx x
    have h2 := congrArg L.cj h1
    have h3 := hx (x * ω)
    have h4 := congrArg L.cj h3
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes] at h2 h4
    generalize algebraMap F E (b.repr x 0) = a at *
    generalize algebraMap F E (b.repr x 1) = c at *
    generalize algebraMap F E (b.repr (x * ω) 0) = a' at *
    generalize algebraMap F E (b.repr (x * ω) 1) = c' at *
    have key : (ω - L.cj ω) * (a * c' - a' * c - x * L.cj x) = 0 := by
      linear_combination (-(L.cj x)) * h3 + x * h4 + (a' + c' * L.cj ω) * h1 - (a' + c' * ω) * h2
    linear_combination e * key - (a * c' - a' * c - x * L.cj x) * hωe

theorem span_eq_map (L : LocE F E) {n m : ℕ} (y : Fin m → Fin n → E) :
    (Submodule.span L.O (Set.range y)).toAddSubgroup =
      (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup).map
        (Fintype.linearCombination E y).toAddMonoidHom := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun,
    AddSubgroup.mem_map, AddSubgroup.mem_pi, Set.mem_univ, forall_true_left,
    LinearMap.toAddMonoidHom_coe, Fintype.linearCombination_apply, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (c i).2, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => ⟨c i, hc i⟩, rfl⟩

theorem index_rmul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ A : Matrix (Fin m) (Fin m) E, IsIntM L A → IsUnit A.det → 0 ≤ vE L ϖ (A.det * L.cj A.det) ∧ (Submodule.span L.O (Set.range (rmul y A))).toAddSubgroup.relIndex (Submodule.span L.O (Set.range y)).toAddSubgroup = resQ ϖ ^ (vE L ϖ (A.det * L.cj A.det)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m y hy A hA hu
  obtain ⟨b, hbO, hnorm⟩ := exists_basis L
  have := L.free
  have : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨-, -, hv3, hv4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hdO : A.det ∈ L.O := by
    rw [Matrix.det_apply']
    exact L.O.sum_mem fun σ _ => L.O.mul_mem (intCast_mem _ _) (L.O.prod_mem fun i _ => hA _ _)
  have hN0 : Algebra.norm F A.det ≠ 0 := (hu.map (Algebra.norm F)).ne_zero
  have hNO : Algebra.norm F A.det ∈ 𝒪[F] := by
    rw [← GlobalTheory.UnramOrder.algebraMap_mem_iff L, hnorm]
    exact L.O.mul_mem hdO (GlobalTheory.UnramOrder.cj_mem L hdO)
  rw [← hnorm]
  have ha := (hv3 _ hN0).2 hNO
  obtain ⟨u, hu'⟩ := hv4 _ hN0
  refine ⟨ha, ?_⟩
  generalize vE L ϖ (algebraMap F E (Algebra.norm F A.det)) = a at *
  let φ : (Fin m → E) ≃ₗ[F] (Fin m → E) :=
    (Matrix.toLinearEquiv (Pi.basisFun E (Fin m)) A hu).restrictScalars F
  have hφ : ∀ v, φ v = A.mulVec v := fun v => by
    simp [φ, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin']
  have hdet : LinearMap.det (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = Algebra.norm F A.det := by
    have : (φ : (Fin m → E) →ₗ[F] (Fin m → E)) = (Matrix.toLin' A).restrictScalars F := by
      ext1 v; exact LinearMap.ext fun w => hφ _
    rw [this, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  set W0 := (AddSubgroup.pi Set.univ fun _ : Fin m => L.O.toAddSubgroup) with hW0
  have hmem : ∀ x, x ∈ W0 ↔ ∀ i, x i ∈ L.O := fun x => by
    simp [hW0, AddSubgroup.mem_pi]
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.relative_lattice_volume_of_det_valuation ϖ hϖ (Pi.basis fun _ : Fin m => b) φ a u (hdet.trans hu') W0
    (fun x => by
      simp only [hmem, hbO, Pi.basis_repr, Sigma.forall])
  have hle : W0.map φ.toAddEquiv.toAddMonoidHom ≤ W0 := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hmem]
    intro i
    change φ v i ∈ _
    rw [hφ, Matrix.mulVec, dotProduct]
    exact L.O.sum_mem fun j _ => L.O.mul_mem (hA _ _) ((hmem v).1 hv j)
  have hcomp : (Fintype.linearCombination E (rmul y A)).toAddMonoidHom =
      (Fintype.linearCombination E y).toAddMonoidHom.comp φ.toAddEquiv.toAddMonoidHom := by
    refine AddMonoidHom.ext fun v => ?_
    change Fintype.linearCombination E (rmul y A) v = Fintype.linearCombination E y (φ v)
    rw [hφ]
    simp only [Fintype.linearCombination_apply, rmul, Matrix.mulVec, dotProduct, Finset.smul_sum,
      Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hinj : Function.Injective (Fintype.linearCombination E y).toAddMonoidHom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact funext (Fintype.linearIndependent_iff.1 hy v hv)
  rw [span_eq_map, span_eq_map, ← hW0, hcomp, ← AddSubgroup.map_map,
    AddSubgroup.relIndex_map_map_of_injective _ _
      hinj]
  rw [relVol, AddSubgroup.relIndex_eq_one.2 hle] at h3
  lift a to ℕ using ha
  rw [zpow_neg, zpow_natCast, Nat.cast_one, one_div, inv_inj] at h3
  rw [Int.toNat_natCast]
  exact_mod_cast h3

end GlobalTheory.MatrixIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassOfTrace
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameMass

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

omit [TopologicalSpace E] in
theorem rmul_comp {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem hf_sum_left (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm (∑ i, c i • x i) y = ∑ i, c i * hf L Hm (x i) y := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem hf_sum_right (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm y (∑ i, c i • x i) = ∑ i, L.cj (c i) * hf L Hm y (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gram_rmul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_left, hf_sum_right, Matrix.mul_apply, cT,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_cT (L : LocE F E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (cT L A).det = L.cj A.det := by
  have h : cT L A = (L.cj.toRingEquiv.toRingHom.mapMatrix A).transpose := by
    ext i j; rfl
  rw [h, Matrix.det_transpose, ← RingHom.map_det]
  rfl

omit [TopologicalSpace E] in
theorem span_rmul {n m : ℕ} (x : Fin m → Fin n → E) (B : Matrix (Fin m) (Fin m) E)
    (hB : IsUnit B.det) :
    Submodule.span E (Set.range x) ≤ Submodule.span E (Set.range (rmul x B)) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h : rmul (rmul x B) B⁻¹ = x := by
    rw [rmul_comp, Matrix.mul_nonsing_inv _ hB]
    funext j
    simp [rmul, Matrix.one_apply]
  have h2 : x j = ∑ i, B⁻¹ i j • rmul x B i := (congrFun h j).symm
  rw [SetLike.mem_coe, h2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end

theorem mass_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 2 * r + 6 ≤ k → (∃ Λ, IsSD L S.Hm Λ) → ∃ κ : ℝ, 0 < κ ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (∀ x ∈ Mh, x ∈ S.ME) → (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) → ENNReal.ofReal (κ / 2 * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) ≤ S.massSig Mh ∧ S.massSig Mh ≤ ENNReal.ofReal (2 * κ * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk ⟨Λs, hΛs⟩
  obtain ⟨x, hx, hME, -, hlat, hmass, hcls⟩ := GlobalTheory.HL.FrameTuple.main L r k S
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.selfDual_hermitianLattice_mass_bounds L S.ϖ S.ϖ_irr S.Hm S.herm Λs hΛs (2 * r + 2) x hx
    (by omega) _ hlat
  refine ⟨κ, hκ, fun C hC p hp Mh hle hin hint => ?_⟩
  obtain ⟨y, B, hB, hy, hM⟩ := hcls C hC p hp
  have hBu : IsUnit B.det := IsUnit.of_mul_eq_one _ hB
  have hBc : IsUnit (L.cj B.det) := hBu.map L.cj
  have hyu : IsUnit (gramT L S.Hm y).det := by
    rw [hy, gram_rmul, Matrix.det_mul, Matrix.det_mul, det_cT]
    exact (hBc.mul hx).mul hBu
  obtain ⟨-, A, hAi, hAu, hMh, hli, hA⟩ := GlobalTheory.HL.OverBasis.exists_basis_overlattice L S.Hm S.herm
    (2 * r + 2) y hyu Mh (hM ▸ hle)
    (fun v hv => by rw [hy]; exact span_rmul x B hBu (hME ▸ hin v hv)) hint
  obtain ⟨hv, hidx⟩ := GlobalTheory.MatrixIndex.index_rmul L S.ϖ S.ϖ_irr _ hli A hAi hAu
  rw [hA, ← hM, ← hMh] at hidx
  have hinv : (A * B⁻¹)⁻¹ = B * A⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hBu]
  have hr : rmul x (A * B⁻¹)⁻¹ = rmul y A⁻¹ := by rw [hinv, hy, rmul_comp]
  have hBB : B⁻¹.det * B.det = 1 := Matrix.det_nonsing_inv_mul_det _ hBu
  have hdet : (A * B⁻¹).det * L.cj (A * B⁻¹).det = A.det * L.cj A.det := by
    have h1 : L.cj B⁻¹.det * L.cj B.det = 1 := by rw [← map_mul, hBB, map_one]
    rw [Matrix.det_mul, map_mul]
    linear_combination (-(A.det * L.cj A.det * B⁻¹.det * L.cj B⁻¹.det)) * hB
      + (A.det * L.cj A.det * L.cj B⁻¹.det * L.cj B.det) * hBB + (A.det * L.cj A.det) * h1
  have hu : IsUnit (A * B⁻¹).det := by
    rw [Matrix.det_mul]; exact hAu.mul (IsUnit.of_mul_eq_one _ hBB)
  have hI : IsIntM L (gramT L S.Hm (rmul x (A * B⁻¹)⁻¹)) := by
    rw [hr]
    intro a b
    refine hint _ ?_ _ ?_ <;> rw [hMh] <;> exact Submodule.subset_span ⟨_, rfl⟩
  have key := hU (A * B⁻¹) hu hI
  rw [hr, ← hMh, hdet, hME, ← hmass] at key
  have hpow : (resQ S.ϖ : ℝ) ^ (-(vE L S.ϖ (A.det * L.cj A.det) *
        (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)))) =
      (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹ := by
    rw [hidx, zpow_neg]
    congr 1
    have e : (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)) = ((k - 1 : ℕ) : ℤ) := by omega
    rw [e]
    conv_lhs => rw [← Int.toNat_of_nonneg hv]
    rw [← Nat.cast_mul, zpow_natCast, pow_mul]
    push_cast
    rfl
  rw [hpow] at key
  exact key

end GlobalTheory.HL.FrameMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassOfTraceStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualHermitianLattice_mass_of_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 2 * r + 6 ≤ k → (∃ Λ, IsSD L S.Hm Λ) → ∃ κ : ℝ, 0 < κ ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (∀ x ∈ Mh, x ∈ S.ME) → (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) → ENNReal.ofReal (κ / 2 * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) ≤ S.massSig Mh ∧ S.massSig Mh ≤ ENNReal.ofReal (2 * κ * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) := by
  first | exact @GlobalTheory.HL.FrameMass.mass_trace | exact GlobalTheory.HL.FrameMass.mass_trace | (intros; apply GlobalTheory.HL.FrameMass.mass_trace <;> assumption)
end
