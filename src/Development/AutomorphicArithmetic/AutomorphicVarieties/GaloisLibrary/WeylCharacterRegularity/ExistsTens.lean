module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.IsRegConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.QdetRect

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IrrSub
open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.irrSub :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), 0 < d →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ) (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        0 < d' ∧ d' ≤ d ∧ B * A = 1 ∧ (∀ y, ρ' y = B * ρ y * A) ∧ (∀ y, ρ y * A = A * ρ' y) ∧
        ∀ W : Submodule ℂ (Fin d' → ℂ), (∀ y, ∀ v ∈ W, ρ' y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G _ d ρ hd
  classical
  have hex : ∃ m, ∃ S : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) ∧ S ≠ ⊥ ∧
      Module.finrank ℂ S = m := by
    refine ⟨_, ⊤, fun y v _ => Submodule.mem_top, ?_, rfl⟩
    intro h
    have h1 : Module.finrank ℂ (⊤ : Submodule ℂ (Fin d → ℂ)) = 0 := by
      rw [h]; exact finrank_bot ℂ (Fin d → ℂ)
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨S, hSinv, hSne, hSrank⟩ := Nat.find_spec hex
  obtain ⟨d', A, B, ρ', hd', hBA, -, hρ', hint⟩ := subMat G d ρ S hSinv
  have hSpos : Module.finrank ℂ S ≠ 0 := fun h => hSne (Submodule.finrank_eq_zero.mp h)
  refine ⟨d', A, B, ρ', ?_, ?_, hBA, hρ', hint, ?_⟩
  · omega
  · have hle := Submodule.finrank_le S
    rw [Module.finrank_fin_fun] at hle
    omega
  · intro W hW
    by_cases hWb : W = ⊥
    · exact Or.inl hWb
    right
    have hinj : Function.Injective A.mulVecLin := by
      intro v w h
      have h2 := congrArg (fun u => B *ᵥ u) h
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBA] using h2
    have hrank : Module.finrank ℂ (W.map A.mulVecLin) = Module.finrank ℂ W :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm
    have hW'inv : ∀ y, ∀ v ∈ W.map A.mulVecLin, ρ y *ᵥ v ∈ W.map A.mulVecLin := by
      intro y v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨ρ' y *ᵥ w, hW y w hw, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint]
    have hW'ne : W.map A.mulVecLin ≠ ⊥ := by
      intro h
      apply hWb
      rw [← Submodule.finrank_eq_zero, ← hrank, h]
      exact finrank_bot ℂ (Fin d → ℂ)
    have hmin := Nat.find_min' hex ⟨W.map A.mulVecLin, hW'inv, hW'ne, rfl⟩
    apply Submodule.eq_top_of_finrank_eq
    have hle := Submodule.finrank_le W
    rw [Module.finrank_fin_fun] at hle ⊢
    omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.FacApply
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh Topology

namespace UpperTheory.V.WeylC

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def fac (P : Weyl.Pre a) (N : ℕ) (τ : E →+* ℂ) : GL (Fin a) (Cinf E) →* Matrix (Fin P.d) (Fin P.d) ℂ where
  toFun y := (coord τ y.val.det)⁻¹ ^ N • P.mat (y.val.map (coord τ))
  map_one' := by simp
  map_mul' y z := by
    simp only [Units.val_mul, Matrix.det_mul, map_mul, Matrix.map_mul, mul_inv, mul_pow, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_comm]

omit [NumberField E] in
theorem fac_apply (P : Weyl.Pre a) (N : ℕ) (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) (i j : Fin P.d) :
    fac P N τ y i j = (coord τ y.val.det)⁻¹ ^ N * P.mat (y.val.map (coord τ)) i j := rfl

omit [NumberField E] in
theorem isReg_fac (P : Weyl.Pre a) (N : ℕ) (τ : E →+* ℂ) : IsReg (fac P N τ) := fun i j => by
  obtain ⟨p, hp⟩ := P.poly i j
  have h1 : ∀ q : MvPolynomial (Fin a × Fin a) ℂ, (fun y : GL (Fin a) (Cinf E) =>
      MvPolynomial.eval (fun ab => coord τ (y.val ab.1 ab.2)) q) ∈ regFun E a := fun q => by
    induction q using MvPolynomial.induction_on with
    | C c => simp only [MvPolynomial.eval_C]; exact (regFun E a).algebraMap_mem c
    | add p q hp hq => simp only [map_add (f := _)]; exact (regFun E a).add_mem hp hq
    | mul_X p n hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact (regFun E a).mul_mem hp (Algebra.subset_adjoin (Or.inl ⟨τ, n.1, n.2, rfl⟩))
  have h2 : (fun y : GL (Fin a) (Cinf E) => (coord τ y.val.det)⁻¹) ∈ regFun E a :=
    Algebra.subset_adjoin (Or.inr ⟨τ, rfl⟩)
  have h3 := (regFun E a).mul_mem ((regFun E a).pow_mem h2 N) (h1 p)
  convert h3 using 1
  funext y
  simp [fac_apply, hp]

theorem diff_coef (P : Weyl.Pre a) (i j : Fin P.d) : Differentiable ℂ (P.coef i j) := by
  obtain ⟨p, hp⟩ := P.poly i j
  have e : P.coef i j = fun x => MvPolynomial.eval (fun ab : Fin a × Fin a => x ab.1 ab.2) p := funext fun x => hp _
  rw [e]
  clear e hp
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p n hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (by fun_prop : Differentiable ℂ fun x : Fin a → Fin a → ℂ => x n.1 n.2)

theorem dOf_fac (P : Weyl.Pre a) (N : ℕ) (τ : E →+* ℂ) (X : Lie E a) :
    dOf (fac P N τ) X = P.D ((Matrix.of X).map (coord τ)) - ((N : ℂ) * coord τ (Matrix.of X).trace) • 1 := by
  ext i j
  let L : Lie E a →L[ℝ] (Fin a → Fin a → ℂ) :=
    ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun l => (coordL τ).comp ((ContinuousLinearMap.proj l).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) k))
  have hL : L (oneL E a) = Weyl.oneM a := by
    funext k l
    exact congrFun (congrFun (Matrix.map_one (coord τ) (map_zero _) (map_one _)) k) l
  have h1 : HasFDerivAt (fun x => P.coef i j (L x))
      (((fderiv ℂ (P.coef i j) (Weyl.oneM a)).restrictScalars ℝ).comp L) (oneL E a) :=
    HasFDerivAt.comp (g := P.coef i j) (oneL E a)
      (by rw [hL]; exact (diff_coef P i j _).hasFDerivAt.restrictScalars ℝ) L.hasFDerivAt
  have h2 := (coordL τ).hasFDerivAt.comp (oneL E a) (contDiff_det.differentiable (by simp) (oneL E a)).hasFDerivAt
  have hd : (Matrix.of (oneL E a)).det = 1 := Matrix.det_one
  have h3 := ((hasDerivAt_inv (x := coordL τ (Matrix.of (oneL E a)).det) (by simp [hd])).pow N).hasFDerivAt.restrictScalars ℝ
  have h4 := (h3.comp (oneL E a) h2).mul h1
  have h5 := h4.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => fac P N τ y i j)
    (fun y => rfl) (x := oneL E a) isUnit_one)
  rw [dOf, Matrix.of_apply, h5.fderiv]
  have h6 : P.coef i j (Weyl.oneM a) = (1 : Matrix _ _ ℂ) i j := congrFun (congrFun (map_one P.mat) i) j
  have h7 : P.D ((Matrix.of X).map (coord τ)) i j = fderiv ℂ (P.coef i j) (Weyl.oneM a) (L X) := rfl
  simp [hd, hL, h6, h7, fderiv_det_one]
  ring

open Classical in
theorem eOf_fac [_root_.NumberField.IsTotallyComplex E] (P : Weyl.Pre a) (N : ℕ) (τ' τ : E →+* ℂ) (i j : Fin a) :
    eOf (fac P N τ') τ i j =
      if τ' = τ then P.E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0) else 0 := by
  have h1 : ∀ x : Cinf E, dOf (fac P N τ') (toL (Matrix.single i j x)) =
      coord τ' x • (P.E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0)) := fun x => by
    have e0 : Matrix.of (toL (Matrix.single i j x)) = Matrix.single i j x := rfl
    have e : (Matrix.single i j x).map (coord τ') = coord τ' x • Matrix.single i j 1 := by
      ext k l
      simp [Matrix.single_apply, apply_ite (coord τ')]
    rw [dOf_fac, e0, e, map_smul, Weyl.Pre.E, smul_add, sub_eq_add_neg]
    congr 1
    split_ifs with h
    · subst h; simp [Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
    · simp [h]
  rw [eOf, h1, h1, smul_smul, ← sub_smul, smul_smul, coord_hol]
  split_ifs <;> simp

end UpperTheory.V.WeylC
end
end

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh Topology

namespace UpperTheory.V.WeylC

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem exists_irr {D : ℕ} (hD : 0 < D) (ρ : GL (Fin a) (Cinf E) →* Matrix (Fin D) (Fin D) ℂ) (hρ : IsReg ρ) (s : ℂ → ℂ)
    (hs : ∀ τ u, Formalism.REAL.qdet (eOf ρ τ) u = s u • 1) :
    ∃ Ξ : AlgRep E a, Ξ.d ≤ D ∧ ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = s u • 1 := by
  obtain ⟨d, A, B, ρ', h0, h1, hBA, h2, h3, h4⟩ := Weyl.irrSub _ D ρ hD
  have hρ' : IsReg ρ' := by
    have := isReg_conj hρ B A
    simpa only [← h2] using this
  refine ⟨⟨d, ρ', hρ', h0, h4⟩, h1, fun τ u => ?_⟩
  have h5 : ∀ i j, eOf ρ τ i j * A = A * eOf ρ' τ i j := fun i j => by
    have e1 := eOf_conj hρ (1 : Matrix (Fin D) (Fin D) ℂ) A τ i j
    have e2 := eOf_conj hρ' A (1 : Matrix (Fin d) (Fin d) ℂ) τ i j
    simp only [Matrix.one_mul, Matrix.mul_one, h3] at e1 e2
    rw [← e1, e2]
  have h6 := congrArg (B * ·) (Weyl.qdetRect a D d _ _ A h5 u)
  simp only [hs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hBA] at h6
  exact h6.symm

theorem exists_tens [_root_.NumberField.IsTotallyComplex E] (P : Weyl.Pre a) (hP : 0 < P.d) (ν : Fin a → ℂ) (hν : P.HasWt ν) (N : ℕ) :
    ∃ Ξ : AlgRep E a, Ξ.d ≤ P.d ^ Fintype.card (E →+* ℂ) ∧
      ∀ τ u, Formalism.REAL.qdet (eOf Ξ.mat τ) u = (∏ k : Fin a, (u - N - (k : ℂ) + ν k)) • 1 := by
  classical
  let e : ((E →+* ℂ) → Fin P.d) ≃ Fin (P.d ^ Fintype.card (E →+* ℂ)) := Fintype.equivFinOfCardEq (by simp)
  let r := Matrix.reindexAlgEquiv ℂ ℂ e
  let ρ : GL (Fin a) (Cinf E) →* Matrix _ _ ℂ :=
    (r.toAlgHom.toMonoidHom.comp piK).comp (MonoidHom.pi fun τ : E →+* ℂ => fac P N τ)
  have hr := isReg_piK (fun τ : E →+* ℂ => isReg_fac P N τ)
  refine exists_irr (pow_pos hP _) ρ (fun i j => hr _ _) _ fun τ u => ?_
  have h1 : eOf ρ τ = fun i j => (r.toAlgHom.comp (intersection_update_fsHerm_neg_one τ))
      (P.E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0)) := by
    funext i j
    have h2 : eOf ρ τ i j = r (eOf (fun y => piK fun t : E →+* ℂ => fac P N t y) τ i j) := rfl
    rw [h2, eOf_piK (fun τ => isReg_fac P N τ) (fun τ => map_one _), Finset.sum_eq_single τ]
    · rw [eOf_fac, if_pos rfl]; rfl
    · intro t _ ht
      rw [eOf_fac, if_neg ht, map_zero]
    · simp
  rw [h1, ← map_qdet, qdet_shift, hν, map_smul, map_one]
  simp only [sub_eq_add_neg]

end UpperTheory.V.WeylC
