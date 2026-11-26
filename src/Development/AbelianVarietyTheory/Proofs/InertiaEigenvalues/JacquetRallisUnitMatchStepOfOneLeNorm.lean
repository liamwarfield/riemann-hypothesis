module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlOrbitalIntegralUnitLiftLastBasisReduce
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalIntegralLiftLastBasisReduce

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitNormalFormUnitInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitNormalFormUnitInvariant
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step.UNormal

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

theorem exists_algebraMap_of_star_eq (y : E) (hy : star y = y) : ∃ x : F, algebraMap F E x = y := by
  have hU : Unram F E := inferInstance
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  let S : Submodule F E :=
    { carrier := {z | star z = z}
      add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq] at *; rw [star_add, ha, hb]
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq] at *
        rw [Algebra.smul_def, star_mul, hz, hU.star_fix, mul_comm] }
  have h1 : (Submodule.span F {(1 : E)}) ≤ S := by
    rw [Submodule.span_le]; intro z hz; simp only [Set.mem_singleton_iff] at hz; subst hz
    show star (1 : E) = 1; exact star_one E
  have hne : S ≠ ⊤ := by
    obtain ⟨z, hz⟩ := hU.star_ne
    intro h; apply hz; have : z ∈ S := h ▸ Submodule.mem_top; exact this
  have hlt : Module.finrank F S < 2 := by
    rw [← hU.finrank_eq]; exact Submodule.finrank_lt hne
  have hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
  have heq : Submodule.span F {(1 : E)} = S :=
    Submodule.eq_of_le_of_finrank_le h1 (by omega)
  have hyS : y ∈ S := hy
  rw [← heq, Submodule.mem_span_singleton] at hyS
  obtain ⟨c, hc⟩ := hyS
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

end GlobalTheory.JR.Step.UNormal

noncomputable section

namespace GlobalTheory.JR.Step.UNormal

section Full
variable {r : ℕ} {k : Type} [CommRing k]

theorem full_cc (Y : Gl r k) (i j : Fin r) : full Y (Fin.castSucc i) (Fin.castSucc j) = Y.1 i j := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_cl (Y : Gl r k) (i : Fin r) : full Y (Fin.castSucc i) (Fin.last r) = Y.2.1 i := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_lc (Y : Gl r k) (j : Fin r) : full Y (Fin.last r) (Fin.castSucc j) = Y.2.2.1 j := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem full_ll (Y : Gl r k) : full Y (Fin.last r) (Fin.last r) = Y.2.2.2 := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

end Full

end GlobalTheory.JR.Step.UNormal

noncomputable section

namespace GlobalTheory.JR.Step


open GlobalTheory.JR.Step.UNormal in
theorem uNormal : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (X : Hn (r + 1) F E) (a : Inv (r + 1) F), HasInv X a →
    ‖a.2.1 0‖ = 1 → ∃ (g : Matrix.unitaryGroup (Fin (r + 1)) E) (X' : Hn r F E) (ν : E),
      ν * star ν = algebraMap F E (a.2.1 0) ∧ actU g X = GlobalTheory.JR.Step.liftH X' ν a.2.2 := by
  intro F E _ _ _ _ _ r X a hX ha
  have h0 : star X.2.1 ⬝ᵥ X.2.1 = algebraMap F E (a.2.1 0) := by
    have := congrArg (fun p => p.2.1 0) hX
    simpa [inv, mom, Hn.toGl, Inv.map] using this
  have hl : X.2.2 = a.2.2 := by
    have := congrArg (fun p => p.2.2) hX
    simp only [inv, Hn.toGl, Inv.map] at this
    exact (algebraMap F E).injective this
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E (a.2.1 0) ha
  have ha0 : algebraMap F E (a.2.1 0) ≠ 0 := by
    rw [map_ne_zero]
    intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hνn : star (ν • eL r E) ⬝ᵥ (ν • eL r E) = ν * star ν := by
    simp [eL, dotProduct, Pi.single_apply, mul_comm]
  have hv : star X.2.1 ⬝ᵥ X.2.1 = star (ν • eL r E) ⬝ᵥ (ν • eL r E) := by
    rw [h0, hνn, hν]
  obtain ⟨g, hg⟩ := GlobalTheory.unitary_transitive_of_norm F E (r + 1) X.2.1 _ hv (h0 ▸ ha0)
  set M := g.1 * X.1.1 * star g.1 with hMdef
  have hM : Mᴴ = M := IsSelfAdjoint.conjugate X.1.2 g.1
  have hMe : ∀ i j, M j i = star (M i j) := by
    intro i j
    have := congrFun (congrFun hM j) i
    rw [conjTranspose_apply] at this
    exact this.symm
  obtain ⟨l', hl'⟩ := exists_algebraMap_of_star_eq (F := F) (M (Fin.last r) (Fin.last r))
    (hMe _ _).symm
  have hsub : M.submatrix Fin.castSucc Fin.castSucc ∈ selfAdjoint (Matrix (Fin r) (Fin r) E) := by
    rw [selfAdjoint.mem_iff, star_eq_conjTranspose, conjTranspose_submatrix, hM]
  refine ⟨g, (⟨M.submatrix Fin.castSucc Fin.castSucc, hsub⟩, fun i => M (Fin.castSucc i) (Fin.last r), l'), ν, hν, ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply Subtype.ext
    show M = full _
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rw [full_ll]; simp [Hn.toGl, hl']
      | cast j => rw [full_lc]; simp [Hn.toGl, hMe (Fin.castSucc j) (Fin.last r)]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [full_cl]; simp [Hn.toGl]
      | cast j => rw [full_cc]; simp [Hn.toGl]
  · exact hg
  · exact hl

end GlobalTheory.JR.Step
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitNormalFormUnitInvariantStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_orbit_normal_form_unit_invariant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (X : Hn (r + 1) F E) (a : Inv (r + 1) F), HasInv X a → ‖a.2.1 0‖ = 1 → ∃ (g : Matrix.unitaryGroup (Fin (r + 1)) E) (X' : Hn r F E) (ν : E), ν * star ν = algebraMap F E (a.2.1 0) ∧ actU g X = GlobalTheory.JR.Step.liftH X' ν a.2.2 := by
  first | exact @GlobalTheory.JR.Step.uNormal | exact GlobalTheory.JR.Step.uNormal | (intros; apply GlobalTheory.JR.Step.uNormal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisHankelDetNeZeroOfLift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisHankelDetNeZeroOfLift
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DeltaLift

variable {k : Type} [Field k] {r : ℕ}

theorem full_cc (Z : Gl r k) (i j : Fin r) : full Z (Fin.castSucc i) (Fin.castSucc j) = Z.1 i j := by
  simp [full]

theorem full_cl (Z : Gl r k) (i : Fin r) : full Z (Fin.castSucc i) (Fin.last r) = Z.2.1 i := by
  simp [full]

theorem full_lc (Z : Gl r k) (j : Fin r) : full Z (Fin.last r) (Fin.castSucc j) = Z.2.2.1 j := by
  simp [full]

theorem full_mulVec_cs (Z : Gl r k) (V : Fin (r + 1) → k) (i : Fin r) :
    (full Z *ᵥ V) (Fin.castSucc i) = (Z.1 *ᵥ (fun j => V (Fin.castSucc j))) i + V (Fin.last r) * Z.2.1 i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, full_cc, full_cl]
  ring

theorem vecMul_full_cs (Z : Gl r k) (V : Fin (r + 1) → k) (j : Fin r) :
    (V ᵥ* full Z) (Fin.castSucc j) = ((fun i => V (Fin.castSucc i)) ᵥ* Z.1) j + V (Fin.last r) * Z.2.2.1 j := by
  simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, full_cc, full_lc]

theorem dot_split (W V : Fin (r + 1) → k) :
    W ⬝ᵥ V = (fun i => W (Fin.castSucc i)) ⬝ᵥ (fun i => V (Fin.castSucc i)) + W (Fin.last r) * V (Fin.last r) := by
  simp only [dotProduct, Fin.sum_univ_castSucc]

theorem dot_pow_all (A : Matrix (Fin r) (Fin r) k) (w b : Fin r → k)
    (h : ∀ i < r, w ⬝ᵥ (A ^ i *ᵥ b) = 0) (m : ℕ) : w ⬝ᵥ (A ^ m *ᵥ b) = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [dotProduct]
  have hP : A.charpoly.Monic := Matrix.charpoly_monic A
  have hdeg : A.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim A
  have hne : A.charpoly ≠ 1 := by
    intro h1; rw [h1, Polynomial.natDegree_one] at hdeg; omega
  have hlt : (Polynomial.X ^ m %ₘ A.charpoly).natDegree < r := by
    simpa [hdeg] using Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ m) hP hne
  rw [Matrix.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hlt]
  have key : ∀ (s : Finset ℕ), (∀ i ∈ s, i < r) → ∀ c : ℕ → k,
      w ⬝ᵥ ((∑ i ∈ s, c i • A ^ i) *ᵥ b) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ c; simp
    | insert a s ha ih =>
      intro hs c
      rw [Finset.sum_insert ha, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul,
        h a (hs a (Finset.mem_insert_self a s)), ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) c]
      simp
  exact key _ (fun i hi => Finset.mem_range.mp hi) _

theorem det_Bm_lift (Z : Gl r k) (μ l : k) (h : (Bm Z).det = 0) :
    (Bm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := Bm Z)).mpr h
  have hw' : ∀ m, w ⬝ᵥ (Z.1 ^ m *ᵥ Z.2.1) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hw ⟨i, hi⟩
    simpa [vecMul, Bm, dotProduct] using this
  set A' := full Z
  let x : ℕ → Fin r → k := fun j i => (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.castSucc i)
  have hx : ∀ j m, w ⬝ᵥ (Z.1 ^ m *ᵥ x j) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : x 0 = 0 := by
        funext i; simp [x, GlobalTheory.JR.Step.eL, Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, mulVec_zero, dotProduct_zero]
    | succ j ih =>
      intro m
      have hxs : x (j + 1) = Z.1 *ᵥ x j + (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.last r) • Z.2.1 := by
        funext i
        simp only [x, pow_succ', ← mulVec_mulVec]
        rw [full_mulVec_cs]
        simp [mul_comm]
      rw [hxs, mulVec_add, dotProduct_add, mulVec_mulVec, ← pow_succ, ih, mulVec_smul, dotProduct_smul, hw']
      simp
  refine (Matrix.exists_vecMul_eq_zero_iff (M := Bm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 w i, ?_, ?_⟩
  · intro h0
    apply hw0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · have e : (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ᵥ* Bm (GlobalTheory.JR.Step.lift Z μ l)
        = fun j : Fin (r + 1) => μ * (w ⬝ᵥ x (j : ℕ)) := by
      funext j
      show (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ⬝ᵥ (A' ^ (j : ℕ) *ᵥ (μ • GlobalTheory.JR.Step.eL r k)) = _
      rw [mulVec_smul, dotProduct_smul, dot_split]
      simp [x, smul_eq_mul]
    rw [e]
    funext j
    simpa using congrArg (μ * ·) (hx j 0)

theorem det_Cm_lift (Z : Gl r k) (μ l : k) (h : (Cm Z).det = 0) :
    (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Cm Z)).mpr h
  have hv' : ∀ m, Z.2.2.1 ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    rw [dotProduct_mulVec]
    simpa [mulVec, Cm, dotProduct] using this
  set A' := full Z
  let u : ℕ → Fin r → k := fun j i => (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.castSucc i)
  have hu : ∀ j m, u j ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : u 0 = 0 := by
        funext i
        simp only [u, pow_zero, vecMul_one, GlobalTheory.JR.Step.eL]
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, zero_dotProduct]
    | succ j ih =>
      intro m
      have hus : u (j + 1) = u j ᵥ* Z.1 + (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.last r) • Z.2.2.1 := by
        funext i
        simp only [u, pow_succ, ← vecMul_vecMul]
        rw [vecMul_full_cs]
        simp [mul_comm]
      rw [hus, add_dotProduct, ← dotProduct_mulVec, mulVec_mulVec, ← pow_succ', ih, smul_dotProduct, hv']
      simp
  refine (Matrix.exists_mulVec_eq_zero_iff (M := Cm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 v i, ?_, ?_⟩
  · intro h0
    apply hv0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · funext j
    simp only [mulVec, Cm, GlobalTheory.JR.Step.lift, Matrix.of_apply]
    rw [dot_split]
    simpa [u, A'] using hu j 0

end GlobalTheory.JR.DeltaLift


open GlobalTheory.JR.DeltaLift in
theorem GlobalTheory.JR.Step.delta_lift_ne : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k),
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  intro k _ r Z μ l h
  have e1 := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k (r + 1)).2.2.1 (GlobalTheory.JR.Step.lift Z μ l)
  have e0 := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants k r).2.2.1 Z
  unfold Delta at h ⊢
  rw [← e1, det_mul] at h
  rw [← e0, det_mul]
  have hC : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := left_ne_zero_of_mul h
  have hB : (Bm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := right_ne_zero_of_mul h
  exact mul_ne_zero (fun hc => hC (det_Cm_lift Z μ l hc)) (fun hb => hB (det_Bm_lift Z μ l hb))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisHankelDetNeZeroOfLiftStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k), Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  first | exact @GlobalTheory.JR.Step.delta_lift_ne | exact GlobalTheory.JR.Step.delta_lift_ne | (intros; apply GlobalTheory.JR.Step.delta_lift_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftMatch
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftMatch
open GlobalTheory.JR Matrix

noncomputable section

namespace GlobalTheory.JR.Step

section MapLemmas
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')

theorem mom_glMap (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by
  simp only [mom, glMap]
  rw [RingHom.map_dotProduct, ← Matrix.map_pow]
  congr 1
  ext j
  simp [RingHom.map_mulVec]
  rfl

theorem inv_glMap (Y : Gl r k) : inv (glMap φ Y) = (inv Y).map φ := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext i
    simp [inv, Inv.map, glMap, Matrix.charpoly_map]
  · ext i
    simp only [inv, Inv.map]
    exact mom_glMap φ Y i
  · rfl

theorem sec_map (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp only [sec, glMap, companion, Inv.map, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  · ext i
    simp only [sec, glMap]
    split_ifs <;> simp
  · rfl
  · rfl

theorem Delta_map (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  have : hankel (a.map φ) = (hankel a).map φ := by
    ext i j
    simp only [hankel, Matrix.of_apply, Matrix.map_apply, sec_map, mom_glMap]
  rw [Delta, Delta, this, RingHom.map_det]
  rfl

theorem full_glMap (Y : Gl r k) : full (glMap φ Y) = (full Y).map φ := by
  ext i j
  simp only [full, glMap, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rcases (finSumFinEquiv.symm i) with a | a <;> rcases (finSumFinEquiv.symm j) with b | b <;> simp

end MapLemmas

section Blocks
variable {r : ℕ} {k : Type} [CommRing k]

theorem blocks_full (Y : Gl r k) : blocks (full Y) = Y := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · ext i
    simp [blocks, full, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]
  · simp [blocks, full, finSumFinEquiv_symm_last]

theorem full_injective : Function.Injective (full : Gl r k → _) :=
  Function.LeftInverse.injective blocks_full

theorem full_act (g : GL (Fin r) k) (Y : Gl r k) :
    full (act g Y) = embHom r k g * full Y * embHom r k ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  simp only [full, embHom, act, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  congr 1
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]

theorem det_embHom (h : Matrix (Fin r) (Fin r) k) : (embHom r k h).det = h.det := by
  simp [embHom, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Blocks

theorem hasInv_of_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E),
    ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) → HasInv X (inv Z) := by
  intro F E _ _ _ _ _ r Z X μ l ν hν hμ hΔ hX
  have hφ : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hμ' : algebraMap F E μ ≠ 0 := fun h => hμ (hφ (h.trans (map_zero _).symm))
  have hsν : star ν ≠ 0 := by
    intro h; apply hμ'; rw [← hν, h, mul_zero]
  have hinv : inv (liftH X ν l).toGl = inv (glMap (algebraMap F E) (lift Z μ l)) := by
    rw [inv_glMap]; exact hX
  have hD : Delta (inv (glMap (algebraMap F E) (lift Z μ l))) ≠ 0 := by
    rw [inv_glMap, Delta_map]
    exact fun h => hΔ (hφ (h.trans (map_zero _).symm))
  obtain ⟨g, ⟨hg, -⟩, -⟩ := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E (r + 1)).2.2.2.2 _ _ hD hinv
  set G : Matrix (Fin (r + 1)) (Fin (r + 1)) E := (g : Matrix (Fin (r + 1)) (Fin (r + 1)) E) with hG
  set Gi : Matrix (Fin (r + 1)) (Fin (r + 1)) E := ((g⁻¹ : GL (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi, Units.inv_mul]
  have h1 : G * full (glMap (algebraMap F E) Z) * Gi = full X.toGl := by
    rw [full_glMap]; exact congrArg Prod.fst hg
  have h2 : G *ᵥ (fun i => algebraMap F E ((μ • eL r F) i)) = ν • eL r E := congrArg (fun Y => Y.2.1) hg
  have h3 : (fun i => algebraMap F E (eL r F i)) ᵥ* Gi = star (ν • eL r E) := congrArg (fun Y => Y.2.2.1) hg
  have hv1 : (fun i => algebraMap F E ((μ • eL r F) i)) = algebraMap F E μ • eL r E := by
    ext i; simp only [eL, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp
  have hv2 : (fun i => algebraMap F E (eL r F i)) = eL r E := by
    ext i; simp only [eL, Pi.single_apply]; split_ifs <;> simp
  have hv3 : star (ν • eL r E) = star ν • eL r E := by
    ext i; simp only [eL, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> simp
  rw [hv1] at h2
  rw [hv2, hv3] at h3
  have hcol : ∀ i, G i (Fin.last r) * algebraMap F E μ = ν * eL r E i := by
    intro i
    have := congrFun h2 i
    rw [Matrix.mulVec_smul, eL, Matrix.mulVec_single_one] at this
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply] at this
    rw [mul_comm]
    exact this
  have hrow : eL r E ᵥ* G = (star ν)⁻¹ • eL r E := by
    have hs : star ν • (eL r E ᵥ* G) = eL r E := by
      rw [← Matrix.smul_vecMul, ← h3, Matrix.vecMul_vecMul, hGiG, Matrix.vecMul_one]
    calc eL r E ᵥ* G = (star ν)⁻¹ • (star ν • (eL r E ᵥ* G)) := by
          rw [smul_smul, inv_mul_cancel₀ hsν, one_smul]
      _ = (star ν)⁻¹ • eL r E := by rw [hs]
  have eLL : G (Fin.last r) (Fin.last r) = (star ν)⁻¹ := by
    have := congrFun hrow (Fin.last r)
    simpa [eL, Matrix.single_one_vecMul] using this
  have eLc : ∀ b : Fin r, G (Fin.last r) (Fin.castSucc b) = 0 := by
    intro b
    have := congrFun hrow (Fin.castSucc b)
    simpa [eL, Matrix.single_one_vecMul, Fin.castSucc_ne_last] using this
  have ecL : ∀ a : Fin r, G (Fin.castSucc a) (Fin.last r) = 0 := by
    intro a
    have := hcol (Fin.castSucc a)
    simp only [eL, Pi.single_apply, Fin.castSucc_ne_last, if_false, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hμ'
  set H : Matrix (Fin (r + 1)) (Fin (r + 1)) E := star ν • G with hH
  set h' : Matrix (Fin r) (Fin r) E := H.submatrix Fin.castSucc Fin.castSucc with hh'
  have hHemb : H = embHom r E h' := by
    ext i j
    refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
    all_goals simp [embHom, H, h', finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last, eLL, eLc, ecL, hsν]
  have hdetG : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det G).mp g.isUnit).ne_zero
  have hdet : h'.det ≠ 0 := by
    rw [← det_embHom, ← hHemb, hH, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hsν) hdetG
  set u : GL (Fin r) E := Matrix.GeneralLinearGroup.mkOfDetNeZero h' hdet with hu_def
  have hu : (u : Matrix (Fin r) (Fin r) E) = h' := rfl
  have hGM : G * full (glMap (algebraMap F E) Z) = full X.toGl * G := by
    calc G * full (glMap (algebraMap F E) Z) = G * full (glMap (algebraMap F E) Z) * (Gi * G) := by
          rw [hGiG, Matrix.mul_one]
      _ = (G * full (glMap (algebraMap F E) Z) * Gi) * G := by
          rw [Matrix.mul_assoc (G * full (glMap (algebraMap F E) Z))]
      _ = full X.toGl * G := by rw [h1]
  have hHM : H * full (glMap (algebraMap F E) Z) = full X.toGl * H := by
    rw [hH, Matrix.smul_mul, Matrix.mul_smul, hGM]
  have key : full (act u (glMap (algebraMap F E) Z)) = full X.toGl := by
    rw [full_act, hu, ← hHemb, hHM, hHemb, Matrix.mul_assoc, ← map_mul (embHom r E), ← hu, Units.mul_inv,
      map_one, Matrix.mul_one]
  have hXeq : X.toGl = act u (glMap (algebraMap F E) Z) := (full_injective key).symm
  unfold HasInv
  rw [hXeq, (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants E r).1, inv_glMap]

end GlobalTheory.JR.Step
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockHasInvariantsOfLiftMatchStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianBlock_hasInvariants_of_lift_match : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E), ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) → HasInv X (inv Z) := by
  first | exact @GlobalTheory.JR.Step.hasInv_of_lift | exact GlobalTheory.JR.Step.hasInv_of_lift | (intros; apply GlobalTheory.JR.Step.hasInv_of_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorsMatchAtOfOneLtNormFirstMoment
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorsMatchAtOfOneLtNormFirstMoment
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.BigMoment

theorem norm_dot_le_one {n : ℕ} {k : Type} [NormedField k] [IsUltrametricDist k] (c b : Fin n → k)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) : ‖c ⬝ᵥ b‖ ≤ 1 := by
  unfold dotProduct
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro i _
  rw [norm_mul]
  exact mul_le_one₀ (hc i) (norm_nonneg _) (hb i)

theorem dot_act {n : ℕ} {k : Type} [CommRing k] (g : GL (Fin n) k) (Y : Gl n k) :
    (act g Y).2.2.1 ⬝ᵥ (act g Y).2.1 = Y.2.2.1 ⬝ᵥ Y.2.1 := by
  simp only [act]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem dot_sec {r : ℕ} {k : Type} [CommRing k] (a : Inv (r + 1) k) :
    (sec a).2.2.1 ⬝ᵥ (sec a).2.1 = a.2.1 0 := by
  simp [sec, dotProduct, Fin.sum_univ_succ]

theorem dot_actU {n : ℕ} {E : Type} [CommRing E] [StarRing E] (g : Matrix.unitaryGroup (Fin n) E)
    (b : Fin n → E) : star (g.1 *ᵥ b) ⬝ᵥ (g.1 *ᵥ b) = star b ⬝ᵥ b := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp g.2, Matrix.one_mulVec]

theorem matchAt_unit_of_one_lt_norm :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (a : Inv (r + 1) F), 1 < ‖a.2.1 0‖ →
      MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  intro F E _ _ _ _ hU r M a ha
  haveI := hU.ultraF
  haveI := hU.ultraE
  have hG : orbG M (unitG (r + 1) F) (sec a) = 0 := by
    have h : ∀ g, unitG (r + 1) F (act g (sec a)) = 0 := by
      intro g
      unfold unitG
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨-, hb, hc, -⟩
      have := norm_dot_le_one _ _ hc hb
      rw [dot_act, dot_sec] at this
      exact absurd ha (not_lt.mpr this)
    simp [orbG, h]
  refine ⟨fun X hX => ?_, fun _ => hG⟩
  rw [hG]
  have h0 : star X.2.1 ⬝ᵥ X.2.1 = algebraMap F E (a.2.1 0) := by
    have := congrArg (fun t : Inv (r + 1) E => t.2.1 0) hX
    simpa [inv, mom, Hn.toGl, Inv.map] using this
  have h : ∀ g, unitU (r + 1) F E (actU g X) = 0 := by
    intro g
    unfold unitU
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨-, hb, -⟩
    have := norm_dot_le_one (star (actU g X).2.1) (actU g X).2.1
      (fun i => by rw [Pi.star_apply, hU.norm_star]; exact hb i) hb
    simp only [actU] at this
    rw [dot_actU, h0, norm_algebraMap'] at this
    exact absurd ha (not_lt.mpr this)
  simp [orbU, h]

end GlobalTheory.JR.BigMoment
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorsMatchAtOfOneLtNormFirstMomentStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitIndicators_matchAt_of_one_lt_norm_firstMoment : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (a : Inv (r + 1) F), 1 < ‖a.2.1 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  first | exact @GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm | exact GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm | (intros; apply GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlConjugateLastBasisNormalFormOfNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlConjugateLastBasisNormalFormOfNeZero
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem full_blocks {r : ℕ} {k : Type} [CommRing k] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) k) :
    full (blocks A) = A := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [full, blocks, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castSucc,
      finSumFinEquiv_symm_last]

def nfMat {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k :=
  Matrix.of fun i j => if i = Fin.last r then c j else if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

theorem nfMat_mulVec_castSucc {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k)
    (i : Fin r) : (nfMat c *ᵥ v) (Fin.castSucc i) = v i.succ := by
  simp only [Matrix.mulVec, dotProduct, nfMat, Matrix.of_apply, Fin.castSucc_ne_last, if_false]
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [if_neg]; · simp
    intro h; apply hj; ext; simp [h]
  · simp

theorem nfMat_mulVec_last {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k) :
    (nfMat c *ᵥ v) (Fin.last r) = c ⬝ᵥ v := by
  simp [Matrix.mulVec, dotProduct, nfMat]

theorem nfMat_injective {r : ℕ} {k : Type} [Field k] (c : Fin (r + 1) → k) (h0 : c 0 ≠ 0) :
    Function.Injective (nfMat c).mulVec := by
  intro x y hxy
  set v := x - y with hv
  have key : nfMat c *ᵥ v = 0 := by rw [hv, Matrix.mulVec_sub, hxy, sub_self]
  have hs : ∀ i : Fin r, v i.succ = 0 := fun i => by
    rw [← nfMat_mulVec_castSucc c v i, key]; rfl
  have hl : c ⬝ᵥ v = 0 := by rw [← nfMat_mulVec_last c v, key]; rfl
  have h0v : v 0 = 0 := by
    rw [dotProduct, Fin.sum_univ_succ] at hl
    simp only [hs, mul_zero, Finset.sum_const_zero, add_zero] at hl
    exact (mul_eq_zero.mp hl).resolve_left h0
  have : v = 0 := by
    funext j
    induction j using Fin.cases with
    | zero => exact h0v
    | succ i => exact hs i
  exact sub_eq_zero.mp this

theorem eL_vecMul_nfMat {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    eL r k ᵥ* nfMat c = c := by
  funext j
  simp [eL, Matrix.vecMul, dotProduct, nfMat, Pi.single_apply, Fin.sum_univ_castSucc, Fin.castSucc_ne_last]

theorem shiftCompanionLastRowMatrix_mulVec_firstBasis {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    nfMat c *ᵥ (fun i : Fin (r + 1) => if (i : ℕ) = 0 then (1 : k) else 0) = c 0 • eL r k := by
  funext i
  induction i using Fin.lastCases with
  | last => simp [nfMat, Matrix.mulVec, dotProduct, eL]
  | cast i =>
    rw [nfMat_mulVec_castSucc]
    simp [eL, Pi.single_apply, Fin.castSucc_ne_last]

theorem glNormal_of_ne_zero : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 →
    ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  intro k _ r a h0
  have hu : IsUnit (GlobalTheory.JR.Step.nfMat a.2.1) :=
    Matrix.mulVec_injective_iff_isUnit.mp (GlobalTheory.JR.Step.nfMat_injective a.2.1 h0)
  refine ⟨hu.unit, GlobalTheory.JR.Step.blocks ((hu.unit : Matrix _ _ k) * companion a.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix _ _ k)), ?_⟩
  have hg : ((hu.unit : GL (Fin (r + 1)) k) : Matrix _ _ k) = GlobalTheory.JR.Step.nfMat a.2.1 := rfl
  have hinv : GlobalTheory.JR.Step.eL r k ᵥ* (GlobalTheory.JR.Step.nfMat a.2.1) = a.2.1 := GlobalTheory.JR.Step.eL_vecMul_nfMat a.2.1
  unfold act sec GlobalTheory.JR.Step.lift
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · exact (GlobalTheory.JR.Step.full_blocks _).symm
  · simp only [hg]; exact GlobalTheory.JR.Step.shiftCompanionLastRowMatrix_mulVec_firstBasis a.2.1
  · show a.2.1 ᵥ* _ = _
    have hgi : GlobalTheory.JR.Step.nfMat a.2.1 * ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = 1 := by
      exact hu.unit.mul_inv
    have e : (GlobalTheory.JR.Step.eL r k ᵥ* GlobalTheory.JR.Step.nfMat a.2.1) ᵥ*
        ((hu.unit⁻¹ : GL (Fin (r + 1)) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = GlobalTheory.JR.Step.eL r k := by
      rw [Matrix.vecMul_vecMul, hgi, Matrix.vecMul_one]
    rw [hinv] at e
    exact e

end GlobalTheory.JR.Step
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlConjugateLastBasisNormalFormOfNeZeroStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 → ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  first | exact @GlobalTheory.JR.Step.glNormal_of_ne_zero | exact GlobalTheory.JR.Step.glNormal_of_ne_zero | (intros; apply GlobalTheory.JR.Step.glNormal_of_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyJacquetRallisHaarMeasuresForallSize
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyJacquetRallisHaarMeasuresForallSize
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.HaarExist

variable (r : ℕ)

theorem entryBall_compact_open (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K] :
    IsCompact {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} ∧
      IsOpen {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  have e : {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} =
      Set.pi Set.univ fun _ : Fin r => Set.pi Set.univ fun _ : Fin r => Metric.closedBall (0 : K) 1 := by
    ext A
    exact ⟨fun h i _ j _ => mem_closedBall_zero_iff.2 (h i j),
      fun h i j => mem_closedBall_zero_iff.1 (h i (Set.mem_univ _) j (Set.mem_univ _))⟩
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero⟩

theorem norm_one_entry_le (K : Type) [NormedField K] (i j : Fin r) :
    ‖(1 : Matrix (Fin r) (Fin r) K) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem glO_isCompact_isOpen (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K] :
    IsCompact (glO r K) ∧ IsOpen (glO r K) ∧ (glO r K).Nonempty := by
  obtain ⟨hc, ho⟩ := entryBall_compact_open r K
  have e : glO r K = Units.embedProduct _ ⁻¹' ({A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ
      (MulOpposite.unop ⁻¹' {A : Matrix (Fin r) (Fin r) K | ∀ i j, ‖A i j‖ ≤ 1})) := by
    ext g
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  refine ⟨?_, ?_, 1, fun i j => ⟨norm_one_entry_le r K i j, by rw [inv_one]; exact norm_one_entry_le r K i j⟩⟩
  · rw [e]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hc.prod (MulOpposite.opHomeomorph.symm.isClosedEmbedding.isCompact_preimage hc))
  · rw [e]
    exact (ho.prod (ho.preimage MulOpposite.continuous_unop)).preimage Units.continuous_embedProduct

theorem continuousStar_of_norm_star (E : Type) [NormedField E] [StarRing E] (h : ∀ y : E, ‖star y‖ = ‖y‖) :
    ContinuousStar E :=
  ⟨(AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) h).continuous⟩

theorem uO_isCompact_isOpen (E : Type) [NontriviallyNormedField E] [StarRing E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [ContinuousStar E] :
    IsCompact (uO r E) ∧ IsOpen (uO r E) ∧ (uO r E).Nonempty := by
  obtain ⟨hc, ho⟩ := entryBall_compact_open r E
  have hcl : IsClosed (Matrix.unitaryGroup (Fin r) E : Set (Matrix (Fin r) (Fin r) E)) :=
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.mul continuous_star) continuous_const)
  exact ⟨hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hc, ho.preimage continuous_subtype_val,
    1, fun i j => norm_one_entry_le r E i j⟩

def positiveCompactsOf {X : Type} [TopologicalSpace X] (s : Set X) (h : IsCompact s ∧ IsOpen s ∧ s.Nonempty) :
    TopologicalSpace.PositiveCompacts X :=
  ⟨⟨s, h.1⟩, by simpa [h.2.1.interior_eq] using h.2.2⟩

theorem unitBall_isCompact_isOpen (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [LocallyCompactSpace K] :
    IsCompact (Metric.closedBall (0 : K) 1) ∧ IsOpen (Metric.closedBall (0 : K) 1) ∧
      (Metric.closedBall (0 : K) 1).Nonempty := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact ⟨isCompact_closedBall _ _, IsUltrametricDist.isOpen_closedBall _ one_ne_zero, 0, by simp⟩

theorem meas_nonempty : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by
  intro F E _ _ _ _ h r
  haveI := h.ultraF; haveI := h.ultraE; haveI := h.lcF; haveI := h.lcE
  haveI := continuousStar_of_norm_star E h.norm_star
  letI : MeasurableSpace (GL (Fin r) F) := borel _
  haveI : BorelSpace (GL (Fin r) F) := ⟨rfl⟩
  letI : MeasurableSpace (Matrix.unitaryGroup (Fin r) E) := borel _
  haveI : BorelSpace (Matrix.unitaryGroup (Fin r) E) := ⟨rfl⟩
  letI : MeasurableSpace F := borel _
  haveI : BorelSpace F := ⟨rfl⟩
  letI : MeasurableSpace E := borel _
  haveI : BorelSpace E := ⟨rfl⟩
  exact ⟨{ μG := Measure.haarMeasure (positiveCompactsOf _ (glO_isCompact_isOpen r F))
           μU := Measure.haarMeasure (positiveCompactsOf _ (uO_isCompact_isOpen r E))
           μF := Measure.addHaarMeasure (positiveCompactsOf _ (unitBall_isCompact_isOpen F))
           μE := Measure.addHaarMeasure (positiveCompactsOf _ (unitBall_isCompact_isOpen E))
           haarG := inferInstance, haarU := inferInstance, haarF := inferInstance, haarE := inferInstance
           volG := Measure.haarMeasure_self, volU := Measure.haarMeasure_self
           volF := Measure.addHaarMeasure_self, volE := Measure.addHaarMeasure_self }⟩

end GlobalTheory.JR.HaarExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyJacquetRallisHaarMeasuresForallSizeStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_jacquetRallisHaarMeasures_forall_size : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), Nonempty (Meas r F E) := by
  first | exact @GlobalTheory.JR.HaarExist.meas_nonempty | exact GlobalTheory.JR.HaarExist.meas_nonempty | (intros; apply GlobalTheory.JR.HaarExist.meas_nonempty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchStepOfOneLeNorm
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step

theorem mom_sec_zero {k : Type} [CommRing k] {r : ℕ} (a : Inv (r + 1) k) : mom (sec a) 0 = a.2.1 0 := by
  simp [mom, sec, dotProduct, Fin.sum_univ_succ]

theorem unitMatchAt_of_one_le_norm : ∀ r : ℕ, UnitMatch r → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (M : Meas (r + 1) F E) (a : Inv (r + 1) F), Delta a ≠ 0 → 1 ≤ ‖mom (sec a) 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  intro r hUM F E _ _ _ _ _ M a hΔ h1
  rw [mom_sec_zero] at h1
  rcases h1.lt_or_eq with hlt | heq
  · exact GlobalTheory.T.unitIndicators_matchAt_of_one_lt_norm_firstMoment F E r M a hlt
  set μ := a.2.1 0 with hμdef
  have hμ1 : ‖μ‖ = 1 := heq.symm
  have hμ0 : μ ≠ 0 := by intro h; rw [h, norm_zero] at hμ1; exact zero_ne_one hμ1
  obtain ⟨g, Z, hgZ⟩ := GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero F r a hμ0
  have hinvF := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F (r + 1)
  have hinvL : inv (GlobalTheory.JR.Step.lift Z μ a.2.2) = a := by
    rw [← hgZ, hinvF.1, hinvF.2.1]
  have hΔL : Delta (inv (GlobalTheory.JR.Step.lift Z μ a.2.2)) ≠ 0 := by rw [hinvL]; exact hΔ
  have hΔZ : Delta (inv Z) ≠ 0 := GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift F r Z μ a.2.2 hΔL
  obtain ⟨M'⟩ := GlobalTheory.T.nonempty_jacquetRallisHaarMeasures_forall_size F E r
  have hL7 := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E (r + 1) M
  have hL7' := GlobalTheory.T.jacquetRallisOrbitalIntegrals_invariant_locallyConstant F E r M'
  have hG : orbG M (unitG (r + 1) F) (sec a) = (if ‖a.2.2‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) (sec (inv Z)) := by
    rw [← hL7.1 _ g, hgZ, GlobalTheory.T.glOrbitalIntegral_unit_liftLastBasis_reduce F E r M M' Z μ a.2.2 hμ1 hΔL]
    obtain ⟨h, hh, -⟩ := (GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r).2.2.2.2 Z (sec (inv Z)) hΔZ ((GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r).2.1 (inv Z))
    rw [← hh.1, hL7'.1]
  have hIH := hUM F E M' (inv Z) hΔZ
  have hΔmap : ∀ (X : Hn (r + 1) F E), HasInv X a → Delta (inv X.toGl) ≠ 0 := by
    intro X hX
    rw [hX, (GlobalTheory.T.borderedInvariants_and_hankelDet_map_ringHom F E (algebraMap F E) (r + 1)).2]
    exact (map_ne_zero _).mpr hΔ
  refine ⟨fun X hX => ?_, fun hno => ?_⟩
  · obtain ⟨u, X', ν, hν, huX⟩ := GlobalTheory.T.unitary_orbit_normal_form_unit_invariant F E r X a hX hμ1
    have hν1 : ‖ν‖ = 1 := by
      have h2 : ‖ν‖ * ‖ν‖ = 1 := by
        have := congrArg norm hν
        rw [norm_mul, Unram.norm_star (F := F), norm_algebraMap'] at this
        rw [this, hμ1]
      nlinarith [norm_nonneg ν]
    have hXL : HasInv (GlobalTheory.JR.Step.liftH X' ν a.2.2) a := by
      rw [← huX]; exact (GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E (r + 1)).2.1 u X a hX
    have hU : orbU M (unitU (r + 1) F E) X = (if ‖a.2.2‖ ≤ 1 then 1 else 0) * orbU M' (unitU r F E) X' := by
      rw [← hL7.2.1 _ u, huX]
      exact GlobalTheory.T.unitaryOrbitalIntegral_liftLastBasis_reduce F E r M M' X' ν a.2.2 hν1 (hΔmap _ hXL)
    have hX' : HasInv X' (inv Z) :=
      GlobalTheory.T.hermitianBlock_hasInvariants_of_lift_match F E r Z X' μ a.2.2 ν hν hμ0 hΔL (by rw [hinvL]; exact hXL)
    rw [hG, hU, hIH.1 X' hX']
  · obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E μ hμ1
    have hno' : ¬ ∃ X' : Hn r F E, HasInv X' (inv Z) := by
      rintro ⟨X', hX'⟩
      exact hno ⟨_, hinvL ▸ GlobalTheory.T.hermitianBlock_hasInvariants_of_liftWithLastBasis F E r Z X' μ a.2.2 ν hν hμ0 hΔL hΔZ hX'⟩
    rw [hG, hIH.2 hno', mul_zero]

end GlobalTheory.JR.Step
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchStepOfOneLeNormStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_step_of_one_le_norm : ∀ r : ℕ, UnitMatch r → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (M : Meas (r + 1) F E) (a : Inv (r + 1) F), Delta a ≠ 0 → 1 ≤ ‖mom (sec a) 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  first | exact @GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm | exact GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm | (intros; apply GlobalTheory.JR.Step.unitMatchAt_of_one_le_norm <;> assumption)
end
