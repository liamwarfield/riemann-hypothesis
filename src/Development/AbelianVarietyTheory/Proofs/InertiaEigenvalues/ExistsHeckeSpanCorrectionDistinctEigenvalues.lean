module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSpanCornerSeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCornerSeparableCharpolyOfIsInternal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCornerSeparableCharpolyOfIsInternal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem isInternal_map_of_corner {K : Type} [Field K] {n t : ℕ} (ι : Type) [Fintype ι]
    [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hV : DirectSum.IsInternal Vs) (hba : b * a = 1)
    (he : ∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) :
    DirectSum.IsInternal (fun j => (Vs j).map b.mulVecLin) := by
  classical
  have hfg : ∀ w : Fin t → K, b.mulVecLin (a.mulVecLin w) = w := fun w => by
    simp [Matrix.mulVec_mulVec, hba]
  have hE : (a * b).mulVecLin = a.mulVecLin ∘ₗ b.mulVecLin := Matrix.mulVecLin_mul a b

  have hback : ∀ S : Submodule K (Fin n → K), S.map (a * b).mulVecLin ≤ S →
      (S.map b.mulVecLin).map a.mulVecLin ≤ S := by
    intro S hS
    rwa [← Submodule.map_comp, ← hE]
  have hVj : ∀ j, (Vs j).map (a * b).mulVecLin ≤ Vs j := by
    rintro j _ ⟨v, hv, rfl⟩
    exact he j v hv
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hV ⊢
  obtain ⟨hind, htop⟩ := hV
  constructor
  · rw [iSupIndep_def] at hind ⊢
    intro j
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    have hrest : (⨆ k, ⨆ (_ : k ≠ j), Vs k).map (a * b).mulVecLin ≤ ⨆ k, ⨆ (_ : k ≠ j), Vs k := by
      simp_rw [Submodule.map_iSup]
      exact iSup₂_mono fun k _ => hVj k
    have hx2' : x ∈ (⨆ k, ⨆ (_ : k ≠ j), Vs k).map b.mulVecLin := by
      simp_rw [Submodule.map_iSup]
      exact hx2
    have h1 : a.mulVecLin x ∈ Vs j := hback _ (hVj j) (Submodule.mem_map_of_mem hx1)
    have h2 : a.mulVecLin x ∈ ⨆ k, ⨆ (_ : k ≠ j), Vs k :=
      hback _ hrest (Submodule.mem_map_of_mem hx2')
    rw [← hfg x, Submodule.disjoint_def.1 (hind j) _ h1 h2, map_zero]
  · rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
    exact fun w => ⟨a.mulVecLin w, hfg w⟩

theorem exists_separable_charpoly_of_isInternal {K : Type} [Field K] [Infinite K] {t : ℕ}
    (ι : Type) [Fintype ι] [DecidableEq ι] (W : ι → Submodule K (Fin t → K))
    (hW : DirectSum.IsInternal W) :
    ∃ D : Matrix (Fin t) (Fin t) K, (∀ j, ∀ w ∈ W j, D.mulVec w ∈ W j) ∧
      D.charpoly.Separable := by
  classical

  let v : ∀ j, Module.Basis (Fin (Module.finrank K (W j))) K (W j) := fun j => Module.finBasis K (W j)
  let B := hW.collectedBasis v
  let μ : (Σ j, Fin (Module.finrank K (W j))) → K :=
    fun s => Infinite.natEmbedding K (Fintype.equivFin _ s)
  have hμ : Function.Injective μ :=
    (Infinite.natEmbedding K).injective.comp (Fin.val_injective.comp (Fintype.equivFin _).injective)
  let φ : (Fin t → K) →ₗ[K] (Fin t → K) := B.constr K (fun s => μ s • B s)
  have hφB : ∀ s, φ (B s) = μ s • B s := fun s => B.constr_basis K _ s
  refine ⟨LinearMap.toMatrix' φ, ?_, ?_⟩
  · intro j w hw
    have hD : (LinearMap.toMatrix' φ).mulVec w = φ w := by
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    have hw' : w = ((∑ k, (v j).repr ⟨w, hw⟩ k • v j k : W j) : Fin t → K) := by
      rw [(v j).sum_repr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hD, hw', Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Submodule.coe_smul, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have hk : ((v j k : W j) : Fin t → K) = B ⟨j, k⟩ := by simp [B]
    rw [hk, hφB]
    exact Submodule.smul_mem _ _ (hW.collectedBasis_mem v ⟨j, k⟩)
  · have h1 : (LinearMap.toMatrix' φ).charpoly = φ.charpoly := by
      rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix]
    have h2 : LinearMap.toMatrix B B φ = Matrix.diagonal μ := by
      ext s s'
      rw [LinearMap.toMatrix_apply, hφB, map_smul, B.repr_self, Matrix.diagonal_apply]
      by_cases h : s = s'
      · subst h; simp
      · simp [h]
    rw [h1, ← LinearMap.charpoly_toMatrix φ B, h2, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.2 hμ

theorem exists_corner_separable_charpoly :
    ∀ {K : Type} [Field K] [Infinite K] {n t : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), DirectSum.IsInternal Vs → b * a = 1 → (∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) → ∃ m : Matrix (Fin n) (Fin n) K, (∀ j, ∀ v ∈ Vs j, m.mulVec v ∈ Vs j) ∧ (b * m * a).charpoly.Separable := by
  intro K _ _ n t ι _ _ Vs a b hV hba he
  obtain ⟨D, hD, hsep⟩ :=
    exists_separable_charpoly_of_isInternal ι _ (isInternal_map_of_corner ι Vs a b hV hba he)
  refine ⟨a * D * b, ?_, ?_⟩
  · intro j v hv
    obtain ⟨u, hu, hu'⟩ := hD j (b.mulVec v) (Submodule.mem_map_of_mem hv)
    have hm : (a * D * b).mulVec v = (a * b).mulVec u := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      congr 1
      exact hu'.symm
    rw [hm]
    exact he j u hu
  · have hc : b * (a * D * b) * a = D := by
      calc b * (a * D * b) * a = (b * a) * D * (b * a) := by simp only [Matrix.mul_assoc]
        _ = D := by rw [hba, Matrix.one_mul, Matrix.mul_one]
    rw [hc]
    exact hsep

end GlobalTheory.SpanRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCornerSeparableCharpolyOfIsInternalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_corner_separable_charpoly_of_isInternal : ∀ {K : Type} [Field K] [Infinite K] {n t : ℕ} (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K (Fin n → K)) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), DirectSum.IsInternal Vs → b * a = 1 → (∀ j, ∀ v ∈ Vs j, (a * b).mulVec v ∈ Vs j) → ∃ m : Matrix (Fin n) (Fin n) K, (∀ j, ∀ v ∈ Vs j, m.mulVec v ∈ Vs j) ∧ (b * m * a).charpoly.Separable := by
  first | exact @GlobalTheory.SpanRing.exists_corner_separable_charpoly | exact GlobalTheory.SpanRing.exists_corner_separable_charpoly | (intros; apply GlobalTheory.SpanRing.exists_corner_separable_charpoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSpanCornerSeparable
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem exists_mem_span_corner_separable {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ}
    (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (h : AbsIrrDistinct (matRep σ)) (hba : b * a = 1)
    (hab : a * b ∈ Submodule.span K (Set.range σ)) :
    ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  obtain ⟨ι, _, _, Vs, hs, hint, -, hspan, hdist⟩ := h
  have hstab : ∀ j, ∀ M ∈ Submodule.span K (Set.range σ), ∀ v ∈ Vs j, M.mulVec v ∈ Vs j := by
    intro j M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hs j g v hv
    | zero => intro v _; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.add_mulVec]
      exact (Vs j).add_mem (hx v hv) (hy v hv)
    | smul c x _ hx =>
      intro v hv
      rw [show (c • x).mulVec v = c • x.mulVec v by
        ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]]
      exact (Vs j).smul_mem c (hx v hv)
  obtain ⟨m, hm, hsep⟩ := GlobalTheory.T.exists_corner_separable_charpoly_of_isInternal ι Vs a b hint hba (fun j => hstab j _ hab)
  refine ⟨m, ?_, hsep⟩
  have hlin := GlobalTheory.T.span_representation_density_of_isInternal_constituents (matRep σ) ι Vs hs hint hspan hdist (Matrix.toLin' m)
    (fun j v hv => by simpa [Matrix.toLin'_apply] using hm j v hv)
  have hfun : (⇑(matRep σ)) = ⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) ∘ ⇑σ := rfl
  rw [hfun, Set.range_comp] at hlin
  have hle : Submodule.span K (⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) '' Set.range ⇑σ) ≤
      (Submodule.span K (Set.range σ)).map
        (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨M, hM, rfl⟩
    exact ⟨M, Submodule.subset_span hM, rfl⟩
  obtain ⟨y, hy, hye⟩ := hle hlin
  have hym : y = m := Matrix.toLin'.injective hye
  rwa [hym] at hy

end GlobalTheory.SpanRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSpanCornerSeparableStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_span_corner_charpoly_separable : ∀ {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ} (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), AbsIrrDistinct (matRep σ) → b * a = 1 → a * b ∈ Submodule.span K (Set.range σ) → ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  first | exact @GlobalTheory.SpanRing.exists_mem_span_corner_separable | exact GlobalTheory.SpanRing.exists_mem_span_corner_separable | (intros; apply GlobalTheory.SpanRing.exists_mem_span_corner_separable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSubmoduleAllCharpolySeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSubmoduleAllCharpolySeparable
open Polynomial

namespace GlobalTheory.SepGeneric

theorem separable_iff_resultant {K : Type} [Field K] {f : K[X]} (hf : f.Monic) {t : ℕ}
    (ht : f.natDegree = t) : f.Separable ↔ resultant f (derivative f) t t ≠ 0 := by
  have hle : (derivative f).natDegree ≤ t :=
    (natDegree_derivative_le f).trans (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have h1 : resultant f (derivative f) t t
      = resultant f (derivative f) f.natDegree (derivative f).natDegree := by
    have := resultant_add_right_deg f (derivative f) t (derivative f).natDegree k le_rfl
    rw [← hk] at this
    rw [this, ← ht, hf.coeff_natDegree]
    simp
  rw [h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hf]
  rfl

theorem finite_bad_base {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K)
    (hB : B.charpoly.Separable) : {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  classical
  let N : Matrix (Fin t) (Fin t) K[X] := B.map C + (X : K[X]) • A.map C
  let D : K[X] := resultant N.charpoly (derivative N.charpoly) t t
  have hN : ∀ l : K, N.map (evalRingHom l) = B + l • A := by
    intro l
    ext i j
    simp [N]
    ring
  have hD : ∀ l : K, (B + l • A).charpoly.Separable ↔ D.eval l ≠ 0 := by
    intro l
    rw [separable_iff_resultant (Matrix.charpoly_monic _)
      (t := t) (by simp), ← hN, Matrix.charpoly_map, derivative_map, resultant_map_map]
    rfl
  have hD0 : D ≠ 0 := by
    intro h
    have := (hD 0).1 (by simpa using hB)
    simp [h] at this
  refine (D.roots.toFinset.finite_toSet).subset ?_
  intro l hl
  simp only [Set.mem_setOf_eq, hD, not_not] at hl
  simp [hD0, hl]

theorem separable_smul {K : Type} [Field K] {t : ℕ} (A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : A.charpoly.Separable) : (c • A).charpoly.Separable := by
  classical
  have h1 : (c • A).charpoly = C c ^ t * A.charpoly.comp (C c⁻¹ * X) := by
    have : (c • A).charmatrix = (C c : K[X]) • (A.charmatrix.map (compRingHom (C c⁻¹ * X))) := by
      ext1 i j
      by_cases h : i = j
      · subst h
        have h3 : (C c : K[X]) * (C c⁻¹ * X) = X := by
          rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
        simp [mul_sub, h3]
      · simp [Matrix.charmatrix_apply_ne _ _ _ h]
    rw [Matrix.charpoly, this, Matrix.det_smul, Matrix.charpoly, Fintype.card_fin]
    congr 1
    exact ((compRingHom (C c⁻¹ * X)).map_det A.charmatrix).symm
  have h2 : (A.charpoly.comp (C c⁻¹ * X)).Separable := by
    rw [separable_def, derivative_comp]
    have hu : IsUnit (derivative (C c⁻¹ * X : K[X])) := by
      simpa using isUnit_C.2 (IsUnit.mk0 _ (inv_ne_zero hc))
    rw [isCoprime_mul_unit_left_right hu]
    exact ((separable_def _).1 hA).map (compRingHom (C c⁻¹ * X))
  rw [h1, mul_comm]
  exact h2.mul_unit ((isUnit_C.2 (IsUnit.mk0 _ hc)).pow t)

theorem finite_bad_dir {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : (c • A).charpoly.Separable) :
    {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  have hA' : A.charpoly.Separable := by
    have := separable_smul _ (inv_ne_zero hc) hA
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hf := (finite_bad_base A B hA').preimage (f := fun l : K => l⁻¹) inv_injective.injOn
  refine (hf.insert 0).subset ?_
  intro l hl
  by_cases h0 : l = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    intro h
    apply hl
    have := separable_smul _ h0 h
    rwa [smul_add, smul_smul, mul_inv_cancel₀ h0, one_smul, add_comm] at this

theorem exists_separable {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ)
    (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K)
    (h : ∀ x, (a x).charpoly.Separable ∨
      ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) :
    ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  classical
  have key : ∀ Y : Finset X, ∃ s ∈ M, ∀ x ∈ Y, (a x + s x).charpoly.Separable := by
    intro Y
    induction Y using Finset.induction_on with
    | empty => exact ⟨0, M.zero_mem, by simp⟩
    | insert x Y hx ih =>
      obtain ⟨s, hs, hY⟩ := ih
      have h1 : ∃ s' ∈ M, {l : K | ¬ (a x + s x + l • s' x).charpoly.Separable}.Finite := by
        rcases h x with h | ⟨s', hs', c, hc, h⟩
        · refine ⟨s, hs, ?_⟩
          have hf := (finite_bad_base (a x) (s x) h).preimage (f := fun l : K => 1 + l)
            (add_right_injective 1).injOn
          refine hf.subset ?_
          intro l hl
          simpa [add_smul, add_assoc] using hl
        · exact ⟨s', hs', finite_bad_dir _ _ hc h⟩
      obtain ⟨s', hs', h1⟩ := h1
      have h2 : (⋃ y ∈ insert x Y,
          {l : K | ¬ (a y + s y + l • s' y).charpoly.Separable}).Finite := by
        refine (insert x Y).finite_toSet.biUnion ?_
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact h1
        · exact finite_bad_base _ _ (hY y hy)
      have h3 := h2.preimage (f := algebraMap O K) (IsFractionRing.injective O K).injOn
      obtain ⟨l, hl⟩ := h3.exists_notMem
      refine ⟨s + l • s', M.add_mem hs (M.smul_mem l hs'), ?_⟩
      intro y hy
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hl
      have := hl y hy
      rwa [algebraMap_smul, add_assoc] at this
  have := Fintype.ofFinite X
  obtain ⟨s, hs, h⟩ := key Finset.univ
  exact ⟨s, hs, fun x => h x (Finset.mem_univ x)⟩

end GlobalTheory.SepGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSubmoduleAllCharpolySeparableStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_submodule_all_charpoly_separable : ∀ {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K] [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ) (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K), (∀ x, (a x).charpoly.Separable ∨ ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) → ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  first | exact @GlobalTheory.SepGeneric.exists_separable | exact GlobalTheory.SepGeneric.exists_separable | (intros; apply GlobalTheory.SepGeneric.exists_separable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeSpanCorrectionDistinctEigenvalues
noncomputable section

namespace GlobalTheory.SpanRing

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices Polynomial

theorem blockPol_map_ringHom {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (e M : Matrix (Fin n) (Fin n) A) : (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem map_mem_span_frac {Γ A : Type} [CommRing A] [IsDomain A] {n : ℕ}
    (σ : Γ → Matrix (Fin n) (Fin n) A) {w : Matrix (Fin n) (Fin n) A}
    (hw : w ∈ Submodule.span A (Set.range σ)) :
    w.map (toFr A) ∈ Submodule.span (FractionRing A) (Set.range fun g => (σ g).map (toFr A)) := by
  induction hw using Submodule.span_induction with
  | mem y hy => obtain ⟨h, rfl⟩ := hy; exact Submodule.subset_span ⟨h, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact add_mem hy hz
  | smul c y _ hy =>
    have : (c • y).map (toFr A) = toFr A c • y.map (toFr A) := by
      ext i j; simp
    rw [this]
    exact Submodule.smul_mem _ _ hy

theorem exists_denom_span_frac {Γ A : Type} [CommRing A] [IsDomain A] {n : ℕ}
    (σ : Γ → Matrix (Fin n) (Fin n) A) {m : Matrix (Fin n) (Fin n) (FractionRing A)}
    (hm : m ∈ Submodule.span (FractionRing A) (Set.range fun g => (σ g).map (toFr A))) :
    ∃ d : A, d ≠ 0 ∧ ∃ w ∈ Submodule.span A (Set.range σ), w.map (toFr A) = toFr A d • m := by
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    exact ⟨1, one_ne_zero, σ h, Submodule.subset_span ⟨h, rfl⟩, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, w, hw, e⟩ := hy
    obtain ⟨d', hd', w', hw', e'⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', d' • w + d • w',
      add_mem (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩
    ext i j
    have h1 := congrFun (congrFun e i) j
    have h2 := congrFun (congrFun e' i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, map_add (f := _),
      map_mul] at h1 h2 ⊢
    rw [h1, h2]; ring
  | smul c y _ hy =>
    obtain ⟨d, hd, w, hw, e⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap A (FractionRing A) q ≠ 0 := by simpa using hq0
    refine ⟨d * q, mul_ne_zero hd hq0, p • w, Submodule.smul_mem _ _ hw, ?_⟩
    ext i j
    have h1 := congrFun (congrFun e i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h1 ⊢
    rw [h1]
    simp only [toFr]
    field_simp

theorem exists_correction_distinct_eigenvalues {Γ X A : Type} [Group Γ] [Finite X] [CommRing A]
    [IsDomain A] [CharZero A] {n t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (π : X) (g0 : Γ) (eB : X → Matrix (Fin n) (Fin n) A) (z : A) (hz : z ≠ 0)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y)
    (hirr : ∀ x, AbsIrrDistinct (overK (rep x))) (hin : InRing T rep eB) (hid : eB * eB = eB)
    (hrk : ∀ x, ((eB x).map (toFr A)).rank = t)
    (hπ : ((blockPol (eB π) (eB π * mat (rep π) g0 * eB π)).map (toFr A)).Separable) :
    ∃ s, InMatrixCongruenceModule T rep π eB s ∧ ∀ x,
      (((blockPol (eB x) (eB x * mat (rep x) g0 * eB x + z • s x)).map (toFr A)).rootSet
        (AlgebraicClosure (FractionRing A))).ncard = t := by
  classical
  have hidx : ∀ x, eB x * eB x = eB x := fun x => congrFun hid x
  have hidK : ∀ x, (eB x).map (toFr A) * (eB x).map (toFr A) = (eB x).map (toFr A) := fun x => by
    rw [← Matrix.map_mul, hidx]
  choose a b hba hab hpol using fun x => GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image ((eB x).map (toFr A)) (hidK x) (hrk x)
  have hbe : ∀ x, b x * (eB x).map (toFr A) = b x := fun x => by
    rw [← hab, ← Matrix.mul_assoc, hba, Matrix.one_mul]
  have hea : ∀ x, (eB x).map (toFr A) * a x = a x := fun x => by
    rw [← hab, Matrix.mul_assoc, hba, Matrix.mul_one]
  have hpolA : ∀ x (M : Matrix (Fin n) (Fin n) A),
      (blockPol (eB x) (eB x * M * eB x)).map (toFr A) = (b x * M.map (toFr A) * a x).charpoly := by
    intro x M
    rw [blockPol_map_ringHom, Matrix.map_mul, Matrix.map_mul, hpol]
  let φ : (X → Matrix (Fin n) (Fin n) A) →ₗ[A] (X → Matrix (Fin t) (Fin t) (FractionRing A)) :=
    { toFun := fun s x => b x * (z • s x).map (toFr A) * a x
      map_add' := fun s s' => by
        funext x
        simp only [Pi.add_apply, smul_add, Matrix.map_add _ (map_add (toFr A)), Matrix.mul_add,
          Matrix.add_mul]
      map_smul' := fun c s => by
        funext x
        have : (z • c • s x).map (toFr A) = c • (z • s x).map (toFr A) := by
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
          rw [Algebra.smul_def, mul_left_comm]
        simp only [this, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Pi.smul_apply] }
  have hφ : ∀ s x, φ s x = b x * (z • s x).map (toFr A) * a x := fun _ _ => rfl
  obtain ⟨_, ⟨s, hs, rfl⟩, hsx⟩ := GlobalTheory.T.exists_mem_submodule_all_charpoly_separable (O := A) (K := FractionRing A) t
    ((spanRingCornerIdealModule T rep π eB).map φ) (fun x => b x * (mat (rep x) g0).map (toFr A) * a x) (by
      intro x
      by_cases hx : x = π
      · left
        subst hx
        rwa [hpolA] at hπ
      · right
        have hmem : a x * b x ∈ Submodule.span (FractionRing A)
            (Set.range fun g => (mat (rep x) g).map (toFr A)) := by
          rw [hab]
          exact map_mem_span_frac _ (eval_mem_span hin x)
        obtain ⟨m, hm, hms⟩ := GlobalTheory.T.exists_mem_span_corner_charpoly_separable (mapM (toFr A) ((Units.coeHom _).comp (rep x)))
          (a x) (b x) (hirr x) (hba x) hmem
        obtain ⟨d, hd, w, hw, hwm⟩ := exists_denom_span_frac (mat (rep x)) hm
        obtain ⟨w', hw', rfl⟩ := exists_inRing_eval (T := T) x hw
        obtain ⟨f, hf, hfx⟩ := hsep x π hx
        have hj : f - algebraMap A (X → A) (f π) ∈ T := T.sub_mem hf (T.algebraMap_mem _)
        have hjx : f x - f π ≠ 0 := sub_ne_zero.2 hfx
        have hc : toFr A (z * (f x - f π) * d) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2
            (mul_ne_zero (mul_ne_zero hz hjx) hd)
        refine ⟨_, ⟨fun y => (f - algebraMap A (X → A) (f π)) y • (eB y * w' y * eB y),
          Submodule.subset_span ⟨_, hj, by simp, w', hw', rfl⟩, rfl⟩,
          (toFr A (z * (f x - f π) * d))⁻¹, inv_ne_zero hc, ?_⟩
        have h1 : (z • ((f - algebraMap A (X → A) (f π)) x • (eB x * w' x * eB x))).map (toFr A) =
            toFr A (z * (f x - f π) * d) •
              ((eB x).map (toFr A) * m * (eB x).map (toFr A)) := by
          have h2 : ∀ (c : A) (M : Matrix (Fin n) (Fin n) A),
              (c • M).map (toFr A) = toFr A c • M.map (toFr A) := fun c M => by
            ext i j; simp
          rw [h2, h2, Matrix.map_mul, Matrix.map_mul, hwm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul, mul_assoc]
          simp
        rw [hφ, h1, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc, one_smul,
          ← Matrix.mul_assoc, ← Matrix.mul_assoc, hbe, Matrix.mul_assoc _ _ (a x), hea]
        exact hms)
  have hs' := (mem_spanRingCornerIdealModule_iff T rep π eB s).1 hs
  refine ⟨s, hs', fun x => ?_⟩
  have hc := InMatrixCongruenceModule.corner hid hs' x
  have h1 : eB x * mat (rep x) g0 * eB x + z • s x = eB x * (mat (rep x) g0 + z • s x) * eB x := by
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hc.1, hc.2]
  have h2 := hsx x
  rw [hφ, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add (toFr A))] at h2
  rw [h1, hpolA, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree h2 (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

end GlobalTheory.SpanRing

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeSpanCorrectionDistinctEigenvaluesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeSpan_correction_distinct_eigenvalues : ∀ {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [CharZero A] {n t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X) (g0 : Γ) (eB : X → Matrix (Fin n) (Fin n) A) (z : A), z ≠ 0 → (∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y) → (∀ x, AbsIrrDistinct (overK (rep x))) → InRing T rep eB → eB * eB = eB → (∀ x, ((eB x).map (toFr A)).rank = t) → ((blockPol (eB π) (eB π * mat (rep π) g0 * eB π)).map (toFr A)).Separable → ∃ s, InMatrixCongruenceModule T rep π eB s ∧ ∀ x, (((blockPol (eB x) (eB x * mat (rep x) g0 * eB x + z • s x)).map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t := by
  first | exact @GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues | exact GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues | (intros; apply GlobalTheory.SpanRing.exists_correction_distinct_eigenvalues <;> assumption)
end
