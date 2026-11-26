module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriMemParab

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricVectorTwoBlockProductExistsPermNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricVectorTwoBlockProductExistsPermNeZero
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
open GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim

noncomputable section

namespace GlobalTheory.ParahoricPerm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ₁ : Representation ℂ (GL (Fin r) k) V} {σ₂ : Representation ℂ (GL (Fin t) k) W}

theorem act_incl {χ : kˣ →* ℂˣ} {f : IndSp (part r t) ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)}
    (hf : IsParahoricVec χ (prod₂ σ₁ σ₂) f) {h : GL (Fin (r + t)) 𝒪[k]} {a : GL (Fin r) 𝒪[k]}
    {d : GL (Fin t) 𝒪[k]} (hb : HasBlocks h a d) :
    prod₂ σ₁ σ₂ (incl k (r + t) h) f = (χ (Matrix.GeneralLinearGroup.det (incl k t d)) : ℂ) • f := by
  refine hf (incl k (r + t) h) ⟨h, rfl⟩ (fun i j => ?_) _ ?_
  · rw [incl_val]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp (hb.2.2 i j)
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    congr 1
    exact Matrix.ext fun i j => by rw [Matrix.submatrix_apply, incl_val, incl_val, hb.2.1]

theorem val_mul_of_smul {f : IndSp (part r t) ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)}
    (x y : GL (Fin (r + t)) k) (c : ℂ) (hy : prod₂ σ₁ σ₂ y f = c • f) : f.1.1 (x * y) = c • f.1.1 x := by
  have : f.1.1 (x * y) = (prod₂ σ₁ σ₂ y f).1.1 x := rfl
  rw [this, hy]
  rfl

theorem exists_perm_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), f ≠ 0 → IsParahoricVec χ (prod₂ σ₁ σ₂) f → ∃ w : Equiv.Perm (Fin (r + t)), f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 := by
  intro k _ _ _ _ r t χ V _ _ W _ _ σ₁ σ₂ f hf0 hf
  by_contra hall
  push_neg at hall
  apply hf0
  have hg : ∀ g, f.1.1 g = 0 := by
    intro g
    obtain ⟨p, w, S, a, a₁, h, d, -, -, hb, rfl⟩ := GlobalTheory.TypeDim.Coset.coset k r t g
    have h1 : f.1.1 (GlobalTheory.Parabolic.permGL k w * diagOne k r t a) = 0 := by
      rw [← incl_diagO_one, val_mul_of_smul _ _ _ (act_incl hf (hasBlocks_diagO a 1)), hall w, smul_zero]
    have h2 : f.1.1 (GlobalTheory.Parabolic.permGL k w * diagOne k r t a * incl k (r + t) h) = 0 := by
      rw [val_mul_of_smul _ _ _ (act_incl hf hb), h1, smul_zero]
    rw [f.1.2 p _, h2]
    simp
  exact Subtype.ext (Subtype.ext (funext hg))

end GlobalTheory.ParahoricPerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricVectorTwoBlockProductExistsPermNeZeroStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricVector_twoBlockProduct_exists_perm_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), f ≠ 0 → IsParahoricVec χ (prod₂ σ₁ σ₂) f → ∃ w : Equiv.Perm (Fin (r + t)), f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 := by
  first | exact @GlobalTheory.ParahoricPerm.exists_perm_ne_zero | exact GlobalTheory.ParahoricPerm.exists_perm_ne_zero | (intros; apply GlobalTheory.ParahoricPerm.exists_perm_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriTorusCharVectorOfParahoricDetCharVect
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriTorusCharVectorOfParahoricDetCharVect
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameParahoric

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val_lt (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem val_det_sub_one_lt {m : Type} [Fintype m] [LinearOrder m] (A : Matrix m m 𝒪[k])
    (hl : ∀ i j, j < i → valuation k (algebraMap 𝒪[k] k (A i j)) < 1)
    (hd : ∀ i, valuation k (algebraMap 𝒪[k] k (A i i) - 1) < 1) :
    valuation k ((A.map (algebraMap 𝒪[k] k)).det - 1) < 1 := by
  have h1 : (A.map (IsLocalRing.residue 𝒪[k])).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have := (residue_eq_zero_iff_val_lt (A i i - 1)).2 (by simpa using hd i)
      rw [map_sub, map_one, sub_eq_zero] at this
      simpa using this
    · intro i j hij
      exact (residue_eq_zero_iff_val_lt _).2 (hl i j hij)
  have h2 : IsLocalRing.residue 𝒪[k] (A.det - 1) = 0 := by
    rw [map_sub, map_one, RingHom.map_det, sub_eq_zero]
    simpa using h1
  have := (residue_eq_zero_iff_val_lt _).1 h2
  rwa [map_sub, map_one, RingHom.map_det] at this

theorem isIwVec_of_isParahoricVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V) (hχ : IsTame χ) (hv : IsParahoricVec χ π v) :
    IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  have hlt : ∀ (i : Fin t) (j : Fin r), Fin.castAdd t j < Fin.natAdd r i := by
    intro i j
    rw [Fin.lt_iff_val_lt_val]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    omega
  refine ⟨fun h hK hl hd => ?_, fun s hs => ?_⟩
  · obtain ⟨h₀, hh⟩ := hK
    have hval : ∀ i j, h.val i j = algebraMap 𝒪[k] k (h₀.val i j) := by
      intro i j
      rw [← hh]
      rfl
    have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) =
        (h₀.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).map (algebraMap 𝒪[k] k) := by
      ext i j
      simp [hval]
    have hdet : valuation k ((h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
      rw [hsub]
      refine val_det_sub_one_lt _ (fun i j hij => ?_) (fun i => ?_)
      · simpa [hval] using hl (Fin.natAdd r i) (Fin.natAdd r j) (by simpa using hij)
      · simpa [hval] using hd (Fin.natAdd r i)
    have hne : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hdet
      exact lt_irrefl _ hdet
    have hu : χ (Units.mk0 _ hne) = 1 := hχ _ (by simpa using hdet)
    rw [hv h ⟨h₀, hh⟩ (fun i j => hl _ _ (hlt i j)) (Units.mk0 _ hne) rfl, hu]
    simp
  · have hD : ((∏ j : Fin t, s (Fin.natAdd r j) : kˣ) : k) =
        ((diagT k (Fin (r + t)) s).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
      rw [val_diagT, Matrix.submatrix_diagonal _ _ (Fin.natAdd_injective _ _), Matrix.det_diagonal]
      simp [Units.coe_prod]
    have hlow : ∀ (i : Fin t) (j : Fin r),
        valuation k ((diagT k (Fin (r + t)) s).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1 := by
      intro i j
      rw [val_diagT, Matrix.diagonal_apply_ne _ (hlt i j).ne']
      simp
    rw [hv _ (iwahori_le_KO k (Fin (r + t)) (diagT_mem_iwahori hs)) hlow _ hD]
    congr 2
    rw [GlobalTheory.SmGL.torusChar_apply, Fin.prod_univ_add, map_prod]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.TameParahoric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriTorusCharVectorOfParahoricDetCharVectStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsTame χ → IsParahoricVec χ π v → IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  first | exact @GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | exact GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | (intros; apply GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalFactorsOfParahoricVectorTwoBlockProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalFactorsOfParahoricVectorTwoBlockProduct
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ParahoricSph

open Matrix

section Contract

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

lemma rid_lTensor_map (φ : W →ₗ[ℂ] ℂ) (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) (y : V ⊗[ℂ] W) :
    TensorProduct.rid ℂ V (φ.lTensor V (TensorProduct.map A B y)) =
      A (TensorProduct.rid ℂ V ((φ ∘ₗ B).lTensor V y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

lemma lid_rTensor_map (ψ : V →ₗ[ℂ] ℂ) (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W) (y : V ⊗[ℂ] W) :
    TensorProduct.lid ℂ W (ψ.rTensor W (TensorProduct.map A B y)) =
      B (TensorProduct.lid ℂ W ((ψ ∘ₗ A).rTensor W y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

lemma exists_rid_ne_zero {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ φ : W →ₗ[ℂ] ℂ, TensorProduct.rid ℂ V (φ.lTensor V x) ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have he : e x ≠ 0 := by
    intro h; exact hx (e.injective (by rw [h, map_zero]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he
  refine ⟨b.coord i, ?_⟩
  have key : ∀ w : V ⊗[ℂ] W, TensorProduct.rid ℂ V ((b.coord i).lTensor V w) = e w i := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    | add y z hy hz => simp only [map_add (f := _), hy, hz, Finsupp.add_apply]
  rw [key]; simpa using hi

lemma exists_lid_ne_zero {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ ψ : V →ₗ[ℂ] ℂ, TensorProduct.lid ℂ W (ψ.rTensor W x) ≠ 0 := by
  have hc : TensorProduct.comm ℂ V W x ≠ 0 := fun h =>
    hx ((TensorProduct.comm ℂ V W).injective (by rw [h, map_zero]))
  obtain ⟨ψ, hψ⟩ := exists_rid_ne_zero hc
  refine ⟨ψ, ?_⟩
  have key : ∀ y : V ⊗[ℂ] W, TensorProduct.lid ℂ W (ψ.rTensor W y) =
      TensorProduct.rid ℂ W (ψ.lTensor W (TensorProduct.comm ℂ V W y)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  rw [key]; exact hψ

end Contract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_det_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ KO k n) : valuation k ((GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨g, rfl⟩ := hg
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem emb₂_mem_KO {r t : ℕ} {m₁ : GL (Fin r) k} {m₂ : GL (Fin t) k} (h₁ : m₁ ∈ KO k (Fin r))
    (h₂ : m₂ ∈ KO k (Fin t)) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂) ∈ KO k (Fin (r + t)) := by
  obtain ⟨g₁, rfl⟩ := h₁
  obtain ⟨g₂, rfl⟩ := h₂
  refine ⟨emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂), ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective i
  obtain ⟨j, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective j
  have hv := val_emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂)
  have hw := val_emb₂ k (stdSum (rfl : r + t = r + t)) (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₁, GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₂)
  show algebraMap 𝒪[k] k ((emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (g₁, g₂)).val _ _) = _
  rw [hv, hw]
  rcases i with i | i <;> rcases j with j | j <;> simp [GeneralLinearGroup.map]

theorem extTensor_apply_eq {r t : ℕ} {χ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ₁ : Representation ℂ (GL (Fin r) k) V}
    {σ₂ : Representation ℂ (GL (Fin t) k) W} {f : _} (hf : IsParahoricVec χ (prod₂ σ₁ σ₂) f)
    {m₁ : GL (Fin r) k} {m₂ : GL (Fin t) k} (h₁ : m₁ ∈ KO k (Fin r)) (h₂ : m₂ ∈ KO k (Fin t)) :
    extTensor σ₁ σ₂ (m₁, m₂) (f.1.1 1) = (χ (GeneralLinearGroup.det m₂) : ℂ) • f.1.1 1 := by
  have hmem := emb₂_mem_KO h₁ h₂
  have hv := val_emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)
  have hll : ∀ (i : Fin t) (j : Fin r),
      valuation k ((emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1 := by
    intro i j
    have h0 : (emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
      have hi : Fin.natAdd r i = (stdSum (rfl : r + t = r + t)) (Sum.inr i) := by ext; simp
      have hj : Fin.castAdd t j = (stdSum (rfl : r + t = r + t)) (Sum.inl j) := by ext; simp
      rw [hv, hi, hj]
      simp
    rw [h0, map_zero]
    exact zero_lt_one
  have hdet : ((GeneralLinearGroup.det m₂ : kˣ) : k) =
      ((emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    have hs : (emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)).val.submatrix (Fin.natAdd r) (Fin.natAdd r) = m₂.val := by
      ext i j
      have hi : Fin.natAdd r i = (stdSum (rfl : r + t = r + t)) (Sum.inr i) := by ext; simp
      have hj : Fin.natAdd r j = (stdSum (rfl : r + t = r + t)) (Sum.inr j) := by ext; simp
      rw [submatrix_apply, hv, hi, hj]
      simp
    rw [hs]
    rfl
  have H := congrArg (fun F => F.1.1 (1 : GL (Fin (r + t)) k)) (hf _ hmem hll _ hdet)
  let p : parab k (two (stdSum (rfl : r + t = r + t))) := ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) (leviTwo k (Fin r) (Fin t) (m₁, m₂)),
    leviEmb_mem_parab k (two (stdSum (rfl : r + t = r + t))) _⟩
  have H2 := parInd_law (two (stdSum (rfl : r + t = r + t)))
    ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) f p 1
  have hδ : (deltaHalf k (Two (Fin r) (Fin t)) (leviTwo k (Fin r) (Fin t) (m₁, m₂)) : ℂ) = 1 := by
    rw [deltaHalf_two, isUnram_absPow k _ _ (valuation_det_of_mem_KO h₁),
      isUnram_absPow k _ _ (valuation_det_of_mem_KO h₂), mul_one, Units.val_one]
  rw [leviProj_leviEmb, hδ, one_smul] at H2
  have E1 : f.1.1 ((p : GL (Fin (r + t)) k) * 1) = f.1.1 (1 * emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)) := by
    rw [mul_one, one_mul]; rfl
  rw [E1] at H2
  change f.1.1 (1 * emb₂ k (stdSum (rfl : r + t = r + t)) (m₁, m₂)) = (χ _ : ℂ) • f.1.1 1 at H
  rw [H] at H2
  rw [H2]
  simp

theorem isSpherical_of_isParahoricVec : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V)
    (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), IsParahoricVec χ (prod₂ σ₁ σ₂) f →
    f.1.1 1 ≠ 0 → IsSpherical σ₁ ∧ IsSpherical (GlobalTheory.SmGL.twist σ₂ (detChar (Fin t) χ⁻¹)) := by
  intro k _ _ _ _ r t χ V _ _ W _ _ σ₁ σ₂ f hf h0
  constructor
  · obtain ⟨φ, hφ⟩ := exists_rid_ne_zero h0
    refine (Submodule.ne_bot_iff _).2 ⟨_, ?_, hφ⟩
    rintro ⟨m, hm⟩
    have H := extTensor_apply_eq hf hm (one_mem (KO k (Fin t)))
    change TensorProduct.map (σ₁ m) (σ₂ 1) (f.1.1 1) = _ at H
    show σ₁ m _ = ((1 : KO k (Fin r) →* ℂˣ) ⟨m, hm⟩ : ℂ) • _
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    have H' := congrArg (fun y => TensorProduct.rid ℂ V (φ.lTensor V y)) H
    rw [rid_lTensor_map] at H'
    simpa [Module.End.one_eq_id] using H'
  · obtain ⟨ψ, hψ⟩ := exists_lid_ne_zero h0
    refine (Submodule.ne_bot_iff _).2 ⟨_, ?_, hψ⟩
    rintro ⟨m, hm⟩
    have H := extTensor_apply_eq hf (one_mem (KO k (Fin r))) hm
    change TensorProduct.map (σ₁ 1) (σ₂ m) (f.1.1 1) = _ at H
    show GlobalTheory.SmGL.twist σ₂ (detChar (Fin t) χ⁻¹) m _ = ((1 : KO k (Fin t) →* ℂˣ) ⟨m, hm⟩ : ℂ) • _
    rw [MonoidHom.one_apply, Units.val_one, one_smul, twist_apply]
    have H' := congrArg (fun y => TensorProduct.lid ℂ W (ψ.rTensor W y)) H
    rw [lid_rTensor_map] at H'
    simp [Module.End.one_eq_id] at H'
    rw [H', smul_smul, ← Units.val_mul]
    simp

end GlobalTheory.ParahoricSph
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalFactorsOfParahoricVectorTwoBlockProductStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_factors_of_parahoricVector_twoBlockProduct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), IsParahoricVec χ (prod₂ σ₁ σ₂) f → f.1.1 1 ≠ 0 → IsSpherical σ₁ ∧ IsSpherical (GlobalTheory.SmGL.twist σ₂ (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec | exact GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec | (intros; apply GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriVectorTwoBlockProductPermValueFirst
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriVectorTwoBlockProductPermValueFirst
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory.TameIwahori.PermCell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_val_le {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (h1 : ∀ i j, valuation k ((g : Matrix n n k) i j) ≤ 1)
    (h2 : ∀ i j, valuation k (((g⁻¹ : GL n k) : Matrix n n k) i j) ≤ 1) : g ∈ KO k n :=
  (GlobalTheory.SplitFlip.mem_KO_iff g).2 ⟨h1, h2⟩

theorem permGL_mem_KO {N : ℕ} (w : Equiv.Perm (Fin N)) : GlobalTheory.Parabolic.permGL k w ∈ KO k (Fin N) := by
  have key : ∀ v : Equiv.Perm (Fin N), ∀ i j,
      valuation k (((GlobalTheory.Parabolic.permGL k v : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
    intro v i j
    rw [GlobalTheory.Parabolic.permGL_apply]
    split_ifs <;> simp
  exact mem_KO_of_val_le (key w) (by rw [← map_inv]; exact key w⁻¹)

theorem val_det_of_mem_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k} (hg : g ∈ KO k m) :
    valuation k (GeneralLinearGroup.det g : k) = 1 := by
  obtain ⟨g, rfl⟩ := hg
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
      algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
    ((algebraMap 𝒪[k] k).map_det _).symm
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

theorem emb₂_one_apply {r t : ℕ} (m : GL (Fin r) k) (x y : Fin r ⊕ Fin t) :
    ((emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) : GL (Fin (r + t)) k) : Matrix (Fin (r + t)) (Fin (r + t)) k)
      (stdSum rfl x) (stdSum rfl y) = fromBlocks (m : Matrix (Fin r) (Fin r) k) 0 0 1 x y := by
  have same : ∀ (a : Bool) (i j : Two (Fin r) (Fin t) a),
      ((leviEmb k (two (stdSum (rfl : r + t = r + t))) (leviTwo k (Fin r) (Fin t) (m, 1)) : GL _ k) : Matrix _ _ k)
        (two (stdSum rfl) ⟨a, i⟩) (two (stdSum rfl) ⟨a, j⟩) =
        ((leviTwo k (Fin r) (Fin t) (m, 1) a : GL _ k) : Matrix _ _ k) i j := by
    intro a i j
    simp [leviEmb, blockDiagonal'_apply_eq]
  have ne : ∀ (a b : Bool), a ≠ b → ∀ (i : Two (Fin r) (Fin t) a) (j : Two (Fin r) (Fin t) b),
      ((leviEmb k (two (stdSum (rfl : r + t = r + t))) (leviTwo k (Fin r) (Fin t) (m, 1)) : GL _ k) : Matrix _ _ k)
        (two (stdSum rfl) ⟨a, i⟩) (two (stdSum rfl) ⟨b, j⟩) = 0 := by
    intro a b h i j
    simp [leviEmb, blockDiagonal'_apply, h]
  change ((leviEmb k (two (stdSum rfl)) (leviTwo k (Fin r) (Fin t) (m, 1)) : GL (Fin (r + t)) k) : Matrix (Fin (r + t)) (Fin (r + t)) k) _ _ = _
  rcases x with x | x <;> rcases y with y | y
  · exact same false x y
  · exact ne false true (by decide) x y
  · exact ne true false (by decide) x y
  · exact same true x y

theorem emb₂_one_mem_KO {r t : ℕ} {m : GL (Fin r) k} (hm : m ∈ KO k (Fin r)) :
    emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) ∈ KO k (Fin (r + t)) := by
  have key : ∀ g : GL (Fin r) k, g ∈ KO k (Fin r) → ∀ i j, valuation k
      (((emb₂ k (stdSum (rfl : r + t = r + t)) (g, 1) : GL (Fin (r + t)) k) :
        Matrix (Fin (r + t)) (Fin (r + t)) k) i j) ≤ 1 := by
    intro g hg i j
    obtain ⟨x, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective i
    obtain ⟨y, rfl⟩ := (stdSum (rfl : r + t = r + t)).surjective j
    rw [emb₂_one_apply]
    have hg1 := ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1
    rcases x with a | a <;> rcases y with b | b
    · exact hg1 a b
    · simp
    · simp
    · rw [fromBlocks_apply₂₂, Matrix.one_apply]
      split_ifs <;> simp
  refine mem_KO_of_val_le (key m hm) ?_
  have : (emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1))⁻¹ = emb₂ k (stdSum (rfl : r + t = r + t)) (m⁻¹, 1) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  rw [this]
  exact key _ (inv_mem hm)

theorem conj_apply {N : ℕ} (w : Equiv.Perm (Fin N)) (X : GL (Fin N) k) (p q : Fin N) :
    (((GlobalTheory.Parabolic.permGL k w)⁻¹ * X * GlobalTheory.Parabolic.permGL k w : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) p q = (X : Matrix (Fin N) (Fin N) k) (w p) (w q) := by
  have h := GlobalTheory.Parabolic.conj_permGL_apply (k := k) w⁻¹ X (w p) (w q)
  rw [map_inv, inv_inv] at h
  simpa using h

end GlobalTheory.TameIwahori.PermCell

namespace GlobalTheory.TameIwahori.PermCell

theorem exists_isIwVec_fst : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (θ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V)
    (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _) (w : Equiv.Perm (Fin (r + t))),
    IsIwVec θ (prod₂ σ₁ σ₂) f → f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 →
    ∃ (s : Equiv.Perm (Fin r)) (y : V), y ≠ 0 ∧
      IsIwVec (fun i => θ (w.symm (Fin.castAdd t (s i)))) σ₁ y := by
  intro k _ _ _ _ r t θ V _ _ W _ _ σ₁ σ₂ f w hf hx
  classical
  have he : ∀ i : Fin r, stdSum (rfl : r + t = r + t) (Sum.inl i) = Fin.castAdd t i :=
    fun i => Fin.ext (by simp)
  have hPK := permGL_mem_KO (k := k) w

  have law : ∀ (q : parab k (two (stdSum (rfl : r + t = r + t)))) (g : GL (Fin (r + t)) k),
      f.1.1 ((q : GL (Fin (r + t)) k) * g) =
        Stages.dat (stdSum (rfl : r + t = r + t)) (extTensor σ₁ σ₂) q (f.1.1 g) := fun q g => f.1.2 q g
  have step : ∀ m : GL (Fin r) k, m ∈ KO k (Fin r) →
      f.1.1 (emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) * GlobalTheory.Parabolic.permGL k w) =
        LinearMap.rTensor W (σ₁ m) (f.1.1 (GlobalTheory.Parabolic.permGL k w)) := by
    intro m hm
    have h := law (Stages.sec (stdSum (rfl : r + t = r + t)) (m, 1)) (GlobalTheory.Parabolic.permGL k w)
    rw [Stages.dat_apply, Stages.dl_apply, Stages.pr_sec] at h
    have hv := val_det_of_mem_KO hm
    simp only [isUnram_absPow k _ _ hv, map_one, one_mul, Units.val_one, one_smul] at h
    refine h.trans ?_
    show TensorProduct.map (σ₁ m) (σ₂ 1) _ = _
    rw [map_one]
    rfl

  set s := Tuple.sort (fun i => w.symm (Fin.castAdd t i)) with hs
  have hmono : StrictMono (fun i => w.symm (Fin.castAdd t (s i))) :=
    (Tuple.monotone_sort (fun i => w.symm (Fin.castAdd t i))).strictMono_of_injective
      ((w.symm.injective.comp (Fin.castAdd_injective r t)).comp s.injective)
  have hSK := permGL_mem_KO (k := k) s
  have hSapp : ∀ (g : GL (Fin r) k) (i j : Fin r),
      ((GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹ : GL (Fin r) k) :
        Matrix (Fin r) (Fin r) k) (s i) (s j) = (g : Matrix (Fin r) (Fin r) k) i j :=
    fun g i j => GlobalTheory.Parabolic.conj_permGL_apply s g i j
  have hent : ∀ (m : GL (Fin r) k) (a b : Fin r ⊕ Fin t),
      (((GlobalTheory.Parabolic.permGL k w)⁻¹ * emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) *
          GlobalTheory.Parabolic.permGL k w : GL (Fin (r + t)) k) : Matrix (Fin (r + t)) (Fin (r + t)) k)
        (w.symm (stdSum rfl a)) (w.symm (stdSum rfl b)) =
        fromBlocks (m : Matrix (Fin r) (Fin r) k) 0 0 1 a b := by
    intro m a b
    rw [conj_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, emb₂_one_apply]
  have hsurj : ∀ p : Fin (r + t), ∃ a, w.symm (stdSum (rfl : r + t = r + t) a) = p :=
    fun p => ⟨(stdSum (rfl : r + t = r + t)).symm (w p), by simp⟩
  have hmove : ∀ m : GL (Fin r) k,
      emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) * GlobalTheory.Parabolic.permGL k w =
        GlobalTheory.Parabolic.permGL k w * ((GlobalTheory.Parabolic.permGL k w)⁻¹ *
          emb₂ k (stdSum (rfl : r + t = r + t)) (m, 1) * GlobalTheory.Parabolic.permGL k w) := by
    intro m; group

  have fix : ∀ g ∈ KO k (Fin r), (∀ i j, j < i → valuation k ((g : Matrix (Fin r) (Fin r) k) i j) < 1) →
      (∀ i, valuation k ((g : Matrix (Fin r) (Fin r) k) i i - 1) < 1) →
      LinearMap.rTensor W (σ₁ (GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹))
        (f.1.1 (GlobalTheory.Parabolic.permGL k w)) = f.1.1 (GlobalTheory.Parabolic.permGL k w) := by
    intro g hg hlow hdiag
    have hm : GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹ ∈ KO k (Fin r) :=
      mul_mem (mul_mem hSK hg) (inv_mem hSK)
    have hK := mul_mem (mul_mem (inv_mem hPK) (emb₂_one_mem_KO (t := t) hm)) hPK
    have h1 := hf.1 _ hK ?_ ?_
    · rw [← step _ hm, hmove]
      exact congrArg (fun F => F.1.1 (GlobalTheory.Parabolic.permGL k w)) h1
    · intro p q hpq
      obtain ⟨a, rfl⟩ := hsurj p
      obtain ⟨b, rfl⟩ := hsurj q
      rw [hent]
      rcases a with a | a <;> rcases b with b | b
      · obtain ⟨i, rfl⟩ := s.surjective a
        obtain ⟨j, rfl⟩ := s.surjective b
        rw [fromBlocks_apply₁₁, hSapp]
        rw [he, he] at hpq
        exact hlow i j (hmono.lt_iff_lt.1 hpq)
      · simp
      · simp
      · have hab : a ≠ b := by
          rintro rfl; exact lt_irrefl _ hpq
        rw [fromBlocks_apply₂₂, one_apply_ne hab]
        simp
    · intro p
      obtain ⟨a, rfl⟩ := hsurj p
      rw [hent]
      rcases a with a | a
      · obtain ⟨i, rfl⟩ := s.surjective a
        rw [fromBlocks_apply₁₁, hSapp]
        exact hdiag i
      · simp

  have tor : ∀ τ ∈ torusO k (Fin r),
      LinearMap.rTensor W (σ₁ (GlobalTheory.Parabolic.permGL k s * diagT k (Fin r) τ * (GlobalTheory.Parabolic.permGL k s)⁻¹))
        (f.1.1 (GlobalTheory.Parabolic.permGL k w)) =
        (GlobalTheory.SmGL.torusChar (fun i => θ (w.symm (Fin.castAdd t (s i)))) τ : ℂ) • f.1.1 (GlobalTheory.Parabolic.permGL k w) := by
    intro τ hτ
    have hm : GlobalTheory.Parabolic.permGL k s * diagT k (Fin r) τ * (GlobalTheory.Parabolic.permGL k s)⁻¹ ∈ KO k (Fin r) :=
      mul_mem (mul_mem hSK (iwahori_le_KO k (Fin r) (diagT_mem_iwahori hτ))) (inv_mem hSK)
    let τ' : Fin (r + t) → kˣ := fun p =>
      Sum.elim (fun a => τ (s.symm a)) (fun _ => 1) ((stdSum (rfl : r + t = r + t)).symm (w p))
    have hτ'e : ∀ a, τ' (w.symm (stdSum (rfl : r + t = r + t) a)) = Sum.elim (fun a => τ (s.symm a)) (fun _ => 1) a :=
      fun a => by simp [τ']
    have hτ' : τ' ∈ torusO k (Fin (r + t)) := by
      intro p
      obtain ⟨a, rfl⟩ := hsurj p
      rw [hτ'e]
      rcases a with a | a
      · exact hτ _
      · simp
    have hh : (GlobalTheory.Parabolic.permGL k w)⁻¹ * emb₂ k (stdSum (rfl : r + t = r + t))
        (GlobalTheory.Parabolic.permGL k s * diagT k (Fin r) τ * (GlobalTheory.Parabolic.permGL k s)⁻¹, 1) *
          GlobalTheory.Parabolic.permGL k w = diagT k (Fin (r + t)) τ' := by
      ext p q
      obtain ⟨a, rfl⟩ := hsurj p
      obtain ⟨b, rfl⟩ := hsurj q
      rw [hent, val_diagT, diagonal_apply, hτ'e]
      rcases a with a | a <;> rcases b with b | b
      · obtain ⟨i, rfl⟩ := s.surjective a
        obtain ⟨j, rfl⟩ := s.surjective b
        rw [fromBlocks_apply₁₁, hSapp, val_diagT, diagonal_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg]
          intro h
          exact hij (s.injective (Sum.inl_injective ((stdSum (rfl : r + t = r + t)).injective
            (w.symm.injective h))))
      · simp
      · simp
      · rw [fromBlocks_apply₂₂]
        change (if a = b then (1 : k) else 0) = _
        by_cases hab : a = b
        · subst hab; simp
        · rw [if_neg hab, if_neg]
          intro h
          exact hab (Sum.inr_injective ((stdSum (rfl : r + t = r + t)).injective (w.symm.injective h)))
    have hc : GlobalTheory.SmGL.torusChar θ τ' = GlobalTheory.SmGL.torusChar (fun i => θ (w.symm (Fin.castAdd t (s i)))) τ := by
      rw [GlobalTheory.SmGL.torusChar_apply, GlobalTheory.SmGL.torusChar_apply]
      calc ∏ p, θ p (τ' p)
          = ∏ a : Fin r ⊕ Fin t, θ (w.symm (stdSum (rfl : r + t = r + t) a))
              (τ' (w.symm (stdSum (rfl : r + t = r + t) a))) :=
            (Equiv.prod_comp ((stdSum (rfl : r + t = r + t)).trans w.symm) (fun p => θ p (τ' p))).symm
        _ = ∏ a : Fin r, θ (w.symm (stdSum (rfl : r + t = r + t) (Sum.inl a))) (τ (s.symm a)) := by
            rw [Fintype.prod_sum_type]
            simp only [hτ'e, Sum.elim_inl, Sum.elim_inr, map_one, Finset.prod_const_one, mul_one]
        _ = ∏ i, θ (w.symm (Fin.castAdd t (s i))) (τ i) := by
            refine (Equiv.prod_comp s (fun a => θ (w.symm (stdSum (rfl : r + t = r + t) (Sum.inl a)))
              (τ (s.symm a)))).symm.trans ?_
            simp only [he, Equiv.symm_apply_apply]
    have h1 := hf.2 τ' hτ'
    rw [← hh] at h1
    rw [← step _ hm, hmove, ← hc]
    exact congrArg (fun F => F.1.1 (GlobalTheory.Parabolic.permGL k w)) h1

  let b := Module.Basis.ofVectorSpace ℂ W
  obtain ⟨i₀, hi₀⟩ : ∃ i, TensorProduct.equivFinsuppOfBasisRight b (f.1.1 (GlobalTheory.Parabolic.permGL k w)) i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((TensorProduct.equivFinsuppOfBasisRight b).map_eq_zero_iff.1 (Finsupp.ext h))
  set y₀ := TensorProduct.equivFinsuppOfBasisRight b (f.1.1 (GlobalTheory.Parabolic.permGL k w)) i₀ with hy₀
  have fix0 : ∀ g ∈ KO k (Fin r), (∀ i j, j < i → valuation k ((g : Matrix (Fin r) (Fin r) k) i j) < 1) →
      (∀ i, valuation k ((g : Matrix (Fin r) (Fin r) k) i i - 1) < 1) →
      σ₁ (GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹) y₀ = y₀ := by
    intro g hg hlow hdiag
    rw [hy₀, ← Stages.coord_rTensor, fix g hg hlow hdiag]
  have tor0 : ∀ τ ∈ torusO k (Fin r),
      σ₁ (GlobalTheory.Parabolic.permGL k s * diagT k (Fin r) τ * (GlobalTheory.Parabolic.permGL k s)⁻¹) y₀ =
        (GlobalTheory.SmGL.torusChar (fun i => θ (w.symm (Fin.castAdd t (s i)))) τ : ℂ) • y₀ := by
    intro τ hτ
    rw [hy₀, ← Stages.coord_rTensor, tor τ hτ, map_smul, Finsupp.smul_apply]
  have hback : ∀ (g : GL (Fin r) k) (v : V), σ₁ g (σ₁ (GlobalTheory.Parabolic.permGL k s)⁻¹ v) =
      σ₁ (GlobalTheory.Parabolic.permGL k s)⁻¹
        (σ₁ (GlobalTheory.Parabolic.permGL k s * g * (GlobalTheory.Parabolic.permGL k s)⁻¹) v) := by
    intro g v
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  refine ⟨s, σ₁ (GlobalTheory.Parabolic.permGL k s)⁻¹ y₀, ?_, ?_, ?_⟩
  · intro h0
    apply hi₀
    have := congrArg (σ₁ (GlobalTheory.Parabolic.permGL k s)) h0
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero,
      Module.End.one_apply] at this
  · intro g hg hlow hdiag
    rw [hback, fix0 g hg hlow hdiag]
  · intro τ hτ
    rw [hback, tor0 τ hτ, map_smul]

end GlobalTheory.TameIwahori.PermCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriVectorTwoBlockProductPermValueFirstStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameIwahoriVector_twoBlockProduct_perm_value_first : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (θ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _) (w : Equiv.Perm (Fin (r + t))), IsIwVec θ (prod₂ σ₁ σ₂) f → f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 → ∃ (s : Equiv.Perm (Fin r)) (y : V), y ≠ 0 ∧ IsIwVec (fun i => θ (w.symm (Fin.castAdd t (s i)))) σ₁ y := by
  first | exact @GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst | exact GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst | (intros; apply GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_of_eq_on_units {ψ θ : kˣ →* ℂˣ} (hθ : IsSmoothChar θ)
    (h : ∀ u : kˣ, valuation k (u : k) = 1 → ψ u = θ u) : IsSmoothChar ψ := by
  have h1 : IsUnram (ψ * θ⁻¹) := fun u hu => by simp [h u hu]
  have h2 : ψ = (ψ * θ⁻¹) * θ := by ext u; simp
  rw [h2]
  exact (isSmoothChar_of_isUnram h1).mul hθ

theorem exists_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {n : ℕ} (π : Irr k n) {v : π.V} {θ : Fin n → kˣ →* ℂˣ}
    (hθ : ∀ i, IsSmoothChar (θ i)) (hv : v ≠ 0) (h : IsIwVec θ π.π v) :
    ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u) ∧
      (∀ i, InSupport π.π (ψ i)) ∧ IsSubquotient π.π (prinSeries ψ) := by
  have hl : HasFiniteLength (jacB π.π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π.π π.smooth (hasFiniteLength_of_isIrreducible π.irr))
  obtain ⟨ψ, l, hl0, hψ, hu⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π.π) (Submodule.Quotient.mk v) θ
    (isSmooth_jacB π.smooth) hl hθ (GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero hD k n π v θ hv h) fun t ht => by
      rw [UnramFixed.jacB_apply, jacBU_mk, h.2 t ht]
      have : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t = 1 :=
        UnramFixed.deltaHalf_torusO k ht
      rw [this]
      simp
  exact ⟨ψ, hu, GlobalTheory.T.mem_supercuspidalSupport_of_torus_jacquet_eigenform k n _ π.π ψ l hl0 hψ,
    SatakeExists.isSubquotient_of_eigenform π.smooth π.irr _ l hl0 hψ⟩

theorem hasFiniteLength_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) : HasFiniteLength (prinSeries ψ) := by
  have hs : IsSmoothChar (GlobalTheory.SmGL.torusChar ψ) := by
    unfold GlobalTheory.SmGL.torusChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one fun a _ => ?_
    exact (hψ a).comp _ (continuous_apply a)
  refine (hBZ k).2.2.1 _ _ _ (points (Fin n)) _ _ ?_ ?_
  · refine isSmooth_comp ((isSmooth_ofChar_iff _).2 hs) _ (continuous_pi fun i => ?_)
    exact continuous_glDet.comp (continuous_apply i)
  · exact (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).symm.surjective).2
      (hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _))

theorem exists_model (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (A : Representation ℂ (GL (Fin n) k) V),
      Nonempty (A.Equiv (prinSeries ψ)) ∧ IsSmooth A ∧ HasFiniteLength A :=
  ⟨_, _, _, prinSeries ψ, ⟨.refl _⟩, isSmooth_parInd _ _, hasFiniteLength_prinSeries hBZ hψ⟩

theorem isCuspSupport_of_prinSeries {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) :
    IsCuspSupport σ.π (fun _ : Fin n => 1) fun a => (Irr.ofDet 1 (ψ a) (hψ a)).π :=
  ⟨σ.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hψ a)⟩, _,
    h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)⟩

theorem exists_eq_of_inSupport (hG : GlobalTheory.Published.GeometricLemma) {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) {μ : kˣ →* ℂˣ}
    (hμ : InSupport σ.π μ) : ∃ i, μ = ψ i := by
  have h1 := JacquetExact.inSupport_of_isSubquotient k _ _ _ _ _ μ (isSmooth_parInd _ _)
    (h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)) hμ
  obtain ⟨a, ha⟩ := ProdSupport.exists_inSupport_of_multiProd hG k _ _ _ _ _ _ μ
    (fun a => (Irr.ofDet 1 (ψ a) (hψ a)).smooth) (fun a => isIrreducible_ofChar _) h1
  exact ⟨a, (Model.inSupport_one_iff _ _).1 ha⟩

def twistIrr {n : ℕ} (σ : Irr k n) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := σ.V
  π := GlobalTheory.SmGL.twist σ.π (detChar (Fin n) χ)
  smooth := isSmooth_twist σ.smooth hχ.detChar
  irr := by
    have φ : Subrepresentation (GlobalTheory.SmGL.twist σ.π (detChar (Fin n) χ)) ≃o Subrepresentation σ.π :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          have := S.toSubmodule.smul_mem (((detChar (Fin n) χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          rwa [twist_apply, smul_smul, Units.inv_mul, one_smul] at this⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
          S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact φ.isSimpleOrder_iff.2 σ.irr

theorem tameSplit : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], TameSplit k := by
  intro hBZ hG hU hD k _ _ _ _ r t χ π v hχ htame hram hv hpar
  let θ : Fin (r + t) → kˣ →* ℂˣ := Fin.append (fun _ : Fin r => 1) fun _ : Fin t => χ
  have hθ : ∀ i, IsSmoothChar (θ i) := fun i => by
    induction i using Fin.addCases with
    | left i => simpa [θ] using isSmoothChar_one
    | right i => simpa [θ] using hχ
  obtain ⟨ψ, hψθ, -, hsub⟩ := exists_prinSeries hBZ hD π hθ hv (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ π.π v htame hpar)
  have hψ : ∀ i, IsSmoothChar (ψ i) := fun i => isSmoothChar_of_eq_on_units (hθ i) (hψθ i)
  let ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i)
  let ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i)
  have hψ₁ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₁ i u = 1 := fun i u hu => by
    simpa [θ] using hψθ (Fin.castAdd t i) u hu
  have hψ₂ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₂ i u = χ u := fun i u hu => by
    simpa [θ] using hψθ (Fin.natAdd r i) u hu
  have happ : Fin.append ψ₁ ψ₂ = ψ := Fin.append_castAdd_natAdd
  rw [← happ] at hsub
  obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ : ∃ (σ₁ : Irr k r) (σ₂ : Irr k t), IsSubquotient σ₁.π (prinSeries ψ₁) ∧
      IsSubquotient σ₂.π (prinSeries ψ₂) ∧ IsSubquotient π.π (prod₂ σ₁.π σ₂.π) := by
    obtain ⟨V, _, _, A, ⟨φA⟩, sA, lA⟩ := exists_model hBZ (ψ := ψ₁) fun i => hψ _
    obtain ⟨W, _, _, B, ⟨φB⟩, sB, lB⟩ := exists_model hBZ (ψ := ψ₂) fun i => hψ _
    obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ := GlobalTheory.T.exists_irreducible_subquotient_twoBlockConstituents k r t _ _ _ π.π A B π.irr sA sB lA lB
      (hsub.trans (GlobalTheory.T.prinSeries_append_isSubquotient_prod₂ k r t ψ₁ ψ₂ V W A B ⟨φA⟩ ⟨φB⟩))
    exact ⟨σ₁, σ₂, h₁.trans (.of_injective φA.toIntertwiningMap φA.injective),
      h₂.trans (.of_injective φB.toIntertwiningMap φB.injective), hπ⟩
  have hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible := by
    refine hU k r t r t σ₁ σ₂ _ _ _ _ (isCuspSupport_of_prinSeries σ₁ (fun i => hψ _) h₁)
      (isCuspSupport_of_prinSeries σ₂ (fun i => hψ _) h₂) ?_
    rintro a b h α ⟨φ⟩
    refine hram fun u hu => ?_
    let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.scalar (Fin 1) u
    have hg : Matrix.GeneralLinearGroup.det g = u := ProdSupport.det_scalar_one rfl u
    obtain ⟨c, hc⟩ : ∃ c : ℂ, φ (1 : ℂ) = c := ⟨_, rfl⟩
    have h0 : c ≠ 0 := fun h => one_ne_zero (α := ℂ) (φ.injective ((hc.trans h).trans (map_zero φ).symm))
    have h1 : φ (detRep (Fin 1) (ψ₁ a) g (1 : ℂ)) = (detChar (Fin 1) (unrChar k α) g : ℂ) •
        detRep (Fin 1) (ψ₂ b) g c := hc ▸ φ.toIntertwiningMap.isIntertwining _ _ g (1 : ℂ)
    simp only [detRep, ofChar_apply, detChar_apply, hg, hψ₁ a u hu, hψ₂ b u hu, isUnram_unrChar k α u hu,
      Units.val_one, one_mul, one_smul] at h1
    exact Units.ext ((mul_eq_right₀ h0).1 (h1.symm.trans hc))
  obtain ⟨φ⟩ := hπ.nonempty_equiv π.irr hirr
  let f := φ.symm v
  have hf0 : f ≠ 0 := fun h => hv (φ.symm.injective (h.trans (map_zero φ.symm).symm))
  have hf : IsParahoricVec χ (prod₂ σ₁.π σ₂.π) f := fun h hh hl u hu => by
    have := φ.symm.toIntertwiningMap.isIntertwining _ _ h v
    rw [hpar h hh hl u hu, map_smul] at this
    exact this.symm
  obtain ⟨w, hw⟩ := GlobalTheory.T.parahoricVector_twoBlockProduct_exists_perm_ne_zero k r t χ _ _ σ₁.π σ₂.π f hf0 hf
  obtain ⟨s, y, hy0, hy⟩ := GlobalTheory.T.tameIwahoriVector_twoBlockProduct_perm_value_first k r t θ _ _ σ₁.π σ₂.π f w (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ _ f htame hf) hw
  obtain ⟨μ, hμ, hμs, -⟩ := exists_prinSeries hBZ hD σ₁ (fun i => hθ _) hy0 hy
  have hwP : GlobalTheory.Parabolic.permGL k w ∈ parab k (two (stdSum (rfl : r + t = r + t))) := by
    have key : ∀ (i : Fin r) (j : Fin t), Fin.castAdd t i ≠ w (Fin.natAdd r j) := fun i j hij => by
      obtain ⟨i, rfl⟩ := s.surjective i
      obtain ⟨a, ha⟩ := exists_eq_of_inSupport hG σ₁ (fun i => hψ _) h₁ (hμs i)
      refine hram fun u hu => ?_
      have h1 := hμ i u hu
      rw [ha, hij, Equiv.symm_apply_apply] at h1
      simpa [θ] using h1.symm.trans (hψ₁ a u hu)
    refine (mem_parab_two k).2 fun j i => (GlobalTheory.Parabolic.permGL_apply w _ _).trans (if_neg fun hji => ?_)
    have hF : ∀ b, ∃ c, w (Fin.natAdd r b) = Fin.natAdd r c := fun b => by
      generalize hx : w (Fin.natAdd r b) = x
      induction x using Fin.addCases with
      | left a => exact absurd hx.symm (key a b)
      | right c => exact ⟨c, rfl⟩
    choose c hc using hF
    have hinj : Function.Injective c := fun b b' h =>
      Fin.natAdd_injective _ _ (w.injective (by rw [hc, hc, h]))
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective hinj j
    have h2 : w (Fin.natAdd r b) = w (Fin.castAdd t i) := by rw [hc, hb]; exact hji
    have h3 := congrArg Fin.val (w.injective h2)
    have := i.2
    simp at h3
    omega
  have hf1 : f.1.1 1 ≠ 0 := fun h => hw (by
    have := f.1.2 ⟨_, hwP⟩ 1
    rw [mul_one, h, map_zero] at this
    exact this)
  obtain ⟨s₁, s₂⟩ := GlobalTheory.T.spherical_factors_of_parahoricVector_twoBlockProduct k r t χ _ _ σ₁.π σ₂.π f hf hf1
  refine ⟨σ₁, twistIrr σ₂ χ⁻¹ hχ.inv, s₁, s₂, ?_⟩
  have e : GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ) = σ₂.π := by
    ext g x
    simp [smul_smul]
  show Nonempty (π.π.Equiv (prod₂ σ₁.π (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
  rw [e]
  exact ⟨φ.symm⟩

end GlobalTheory.TameIwahori
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProductStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameParahoricRep_splits_as_product : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], TameSplit k := by
  first | exact @GlobalTheory.TameIwahori.tameSplit | exact GlobalTheory.TameIwahori.tameSplit | (intros; apply GlobalTheory.TameIwahori.tameSplit <;> assumption)
end
