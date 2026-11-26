module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhase
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.HermitianLocalGlobalExistence
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.HermitianFormLocalGlobal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LandherrStandardDefiniteHermitianCmField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryConjIffExistsCentralizerNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryConjIffExistsCentralizerNorm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryConj

theorem inv_h_form {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (h : GL (Fin n) K) :
    (h.val * cT σ h.val)⁻¹ = cT σ (h⁻¹).val * (h⁻¹).val := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul, cT_units]

theorem main : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ h : GL (Fin n) K), (∃ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) K), h⁻¹ * γ * h = g⁻¹ * γ * g) ↔ ∃ c : Matrix (Fin n) (Fin n) K, c * γ.val = γ.val * c ∧ cT σ c * c = (h.val * cT σ h.val)⁻¹ := by
  intro K _ σ n γ h
  rw [inv_h_form]
  constructor
  · rintro ⟨g, hg, hconj⟩
    have hg' : cT σ g.val * 1 * g.val = 1 := hg
    rw [Matrix.mul_one] at hg'
    refine ⟨(g * h⁻¹).val, ?_, ?_⟩
    · have e : g * h⁻¹ * γ = γ * (g * h⁻¹) := by
        calc g * h⁻¹ * γ = g * (h⁻¹ * γ * h) * h⁻¹ := by group
          _ = g * (g⁻¹ * γ * g) * h⁻¹ := by rw [hconj]
          _ = γ * (g * h⁻¹) := by group
      simpa only [Units.val_mul] using congrArg Units.val e
    · rw [Units.val_mul, cT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g.val), hg', Matrix.one_mul]
  · rintro ⟨c, hc, hcc⟩
    have hdet : c.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hcc
      rw [Matrix.det_mul, h0, mul_zero] at this
      have hne : (cT σ (h⁻¹).val * (h⁻¹).val).det ≠ 0 := det_ne σ h
      exact hne this.symm
    let cu : GL (Fin n) K := ((Matrix.isUnit_iff_isUnit_det c).mpr (isUnit_iff_ne_zero.mpr hdet)).unit
    have hcu : cu.val = c := rfl
    have hcom : cu⁻¹ * γ * cu = γ := by
      have e : cu * γ = γ * cu := Units.ext (by simpa only [Units.val_mul, hcu] using hc)
      calc cu⁻¹ * γ * cu = cu⁻¹ * (γ * cu) := by group
        _ = cu⁻¹ * (cu * γ) := by rw [e]
        _ = γ := by group
    refine ⟨cu * h, ?_, ?_⟩
    · show cT σ (cu * h).val * 1 * (cu * h).val = 1
      rw [Matrix.mul_one, Units.val_mul, cT_mul, hcu, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ c), hcc]
      simp only [Matrix.mul_assoc]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, ← cT_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, cT_one]
    · calc h⁻¹ * γ * h = h⁻¹ * (cu⁻¹ * γ * cu) * h := by rw [hcom]
        _ = (cu * h)⁻¹ * γ * (cu * h) := by group

end GlobalTheory.UnitaryConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryConjIffExistsCentralizerNormStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_conj_iff_exists_centralizer_norm : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ h : GL (Fin n) K), (∃ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) K), h⁻¹ * γ * h = g⁻¹ * γ * g) ↔ ∃ c : Matrix (Fin n) (Fin n) K, c * γ.val = γ.val * c ∧ cT σ c * c = (h.val * cT σ h.val)⁻¹ := by
  first | exact @GlobalTheory.UnitaryConj.main | exact GlobalTheory.UnitaryConj.main | (intros; apply GlobalTheory.UnitaryConj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionFixesPolynomialImage
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.NormHasseFixed

theorem cT_aeval {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    cT σ (aeval A p) = aeval (cT σ A) (p.map σ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
    unfold cT
    rw [Matrix.map_smul' _ _ _ (fun x y => map_mul σ x y), Matrix.map_pow, Matrix.transpose_smul, Matrix.transpose_pow]

theorem aeval_mulVec {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} (N : Matrix (Fin n) (Fin n) L)
    (μ : L) (v : Fin n → L) (hv : N *ᵥ v = μ • v) (p : K[X]) : (aeval N p) *ᵥ v = aeval μ p • v := by
  have hpow : ∀ k : ℕ, (N ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, Matrix.smul_mulVec, hpow,
      smul_assoc]

theorem aeval_inv_map_eq {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (γ : GL (Fin n) E)
    (hγ : cT σ γ.val * 1 * γ.val = 1) (m : E[X]) (hm : cT σ (aeval γ.val m) = aeval γ.val m)
    {L : Type} [Field L] [Algebra E L] (α : L) (hα0 : α ≠ 0) (hroot : aeval α γ.val.charpoly = 0) :
    aeval α⁻¹ (m.map σ) = aeval α m := by
  have hU' : cT σ γ.val = (γ⁻¹).val := by
    have h := congrArg (· * (γ⁻¹).val) hγ
    simpa [Matrix.mul_assoc] using h
  rw [aeval_def, ← eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hAv : (γ.val.map (algebraMap E L)) *ᵥ v = α • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hBA : ((γ⁻¹).val.map (algebraMap E L)) * (γ.val.map (algebraMap E L)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBv : ((γ⁻¹).val.map (algebraMap E L)) *ᵥ v = α⁻¹ • v := by
    have h : ((γ⁻¹).val.map (algebraMap E L)) *ᵥ ((γ.val.map (algebraMap E L)) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    rw [hAv, Matrix.mulVec_smul] at h
    conv_rhs => rw [← h, smul_smul, inv_mul_cancel₀ hα0, one_smul]
  have hmap : ∀ (M : Matrix (Fin n) (Fin n) E) (p : E[X]),
      (aeval M p).map (algebraMap E L) = aeval (M.map (algebraMap E L)) p := by
    intro M p
    have h := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E L)) M p
    have e : (⇑(Algebra.ofId E L) : E → L) = algebraMap E L := rfl
    simpa [AlgHom.mapMatrix_apply, e] using h.symm
  have h1 : (cT σ (aeval γ.val m)).map (algebraMap E L) *ᵥ v = (aeval γ.val m).map (algebraMap E L) *ᵥ v := by
    rw [hm]
  rw [cT_aeval, hU', hmap, hmap, aeval_mulVec _ _ v hBv, aeval_mulVec _ _ v hAv] at h1
  exact smul_left_injective L hv0 h1


open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField in
theorem invol_mk_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ.val m) = aeval γ.val m → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ n γ hγ _ m hm r Q hQ
  have hγ' : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val * 1 * γ.val = 1 := hγ
  have hroot : aeval (AdjoinRoot.root Q.1) γ.val.charpoly = 0 := by
    obtain ⟨c, hc⟩ := hQ
    rw [hc, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  have h := aeval_inv_map_eq (IsCMField.complexConj E).toRingEquiv.toRingHom γ hγ' m hm (AdjoinRoot.root Q.1) (root_ne_zero Q) hroot
  rw [aeval_def, eval₂_map, AdjoinRoot.aeval_eq] at h
  refine Eq.trans ?_ h
  show AdjoinRoot.lift ((AdjoinRoot.of Q.1).comp (IsCMField.complexConj E : E →+* E)) (AdjoinRoot.root Q.1)⁻¹
    (eval₂_conj_inv_root Q) (AdjoinRoot.mk Q.1 m) = _
  rw [AdjoinRoot.lift_mk]
  rfl

end GlobalTheory.NormHasseFixed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyPositiveRealPlaces
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealPlaceNorms

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField NumberField.InfinitePlace.Completion

theorem aeval_mulVec_of_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (z : ℂ)
    (h : A *ᵥ v = z • v) (p : ℂ[X]) : (aeval A p) *ᵥ v = p.eval z • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    have hk : (A ^ k) *ᵥ v = z ^ k • v := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mulVec,
      hk, smul_smul, eval_monomial]

theorem pos_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) {v : Fin n → ℂ}
    (hv : v ≠ 0) {c : ℂ} (h : M *ᵥ v = c • v) : 0 < c := by
  have h1 := hM.dotProduct_mulVec_pos hv
  rw [h, dotProduct_smul, smul_eq_mul] at h1
  have h2 : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.2 hv
  rw [Complex.lt_def] at h1 h2 ⊢
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨b1, b2⟩ := h2
  simp only [Complex.zero_re, Complex.zero_im, Complex.mul_re, Complex.mul_im] at a1 a2 b1 b2 ⊢
  rw [← b2] at a1 a2
  have hi : c.im = 0 := by
    have : c.im * (star v ⬝ᵥ v).re = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right b1.ne'
  refine ⟨?_, hi.symm⟩
  rw [hi] at a1
  have : 0 < c.re * (star v ⬝ᵥ v).re := by linarith
  exact (pos_iff_pos_of_mul_pos this).2 b1

theorem map_aeval {E : Type} [Field E] {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (m : E[X]) (τ : E →+* ℂ) :
    (aeval γ m).map τ = aeval (γ.map τ) (m.map τ) := by
  rw [← RingHom.mapMatrix_apply, aeval_def, hom_eval₂, aeval_def, eval₂_map]
  congr 1
  ext a i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]

section Fld

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)

theorem pos_at_embedding {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (m : E[X])
    (hpos : ∀ τ : E →+* ℂ, ((aeval γ m).map τ).PosDef) (hdvd : Q.1 ∣ γ.charpoly)
    (x : plus Q) (hx : (x : Fld Q) = AdjoinRoot.mk Q.1 m) (φ : plus Q →+* ℂ) : 0 < φ x := by
  letI : Algebra (plus Q) ℂ := φ.toAlgebra
  haveI : Module.Finite (plus Q) (Fld Q) :=
    Module.Finite.of_restrictScalars_finite (maximalRealSubfield E) (plus Q) (Fld Q)
  haveI : Module.IsTorsionFree (plus Q) ℂ := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree (plus Q) (Fld Q) := DivisionSemiring.to_moduleIsTorsionFree
  let ρ : Fld Q →ₐ[plus Q] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hρx : ρ (x : Fld Q) = φ x := ρ.commutes x
  let τ : E →+* ℂ := (ρ : Fld Q →+* ℂ).comp (algebraMap E (Fld Q))
  have hev : ∀ p : E[X], (p.map τ).eval (ρ (AdjoinRoot.root Q.1)) = ρ (AdjoinRoot.mk Q.1 p) := by
    intro p
    rw [eval_map, ← AdjoinRoot.aeval_eq, aeval_def]
    exact (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) (ρ : Fld Q →+* ℂ) (AdjoinRoot.root Q.1)).symm
  set z := ρ (AdjoinRoot.root Q.1)
  have hroot : ((γ.map τ).charpoly).eval z = 0 := by
    obtain ⟨g, hg⟩ := hdvd
    have h0 : (AdjoinRoot.mk Q.1 Q.1 : Fld Q) = 0 := AdjoinRoot.mk_self
    rw [Matrix.charpoly_map, hg, Polynomial.map_mul, eval_mul, hev, h0]
    exact mul_eq_zero_of_left (map_zero ρ) _
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  have hγv : (γ.map τ) *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hv0
    exact hv0.symm
  have hM : ((aeval γ m).map τ) *ᵥ v = φ x • v := by
    rw [map_aeval, aeval_mulVec_of_eigen _ v z hγv, hev, ← hx, hρx]
  exact pos_of_posDef (hpos τ) hv hM

end Fld

theorem exists_mul_self_of_pos {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (t : K)
    (ht : 0 < w.embedding t) : ∃ a : w.Completion, a * a = algebraMap K w.Completion t := by
  obtain ⟨h1, h2⟩ := Complex.lt_def.1 ht
  simp only [Complex.zero_re, Complex.zero_im] at h1 h2
  have hre : w.embedding t = ((w.embedding t).re : ℂ) := Complex.ext (by simp) (by simp [← h2])
  have key : ∃ a : w.Completion, extensionEmbedding w a = (Real.sqrt (w.embedding t).re : ℂ) := by
    by_cases hw : w.IsReal
    · refine ⟨(ringEquivRealOfIsReal hw).symm (Real.sqrt (w.embedding t).re), ?_⟩
      rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply,
        RingEquiv.apply_symm_apply]
    · exact surjective_extensionEmbedding_of_isComplex (InfinitePlace.not_isReal_iff_isComplex.1 hw) _
  obtain ⟨a, ha⟩ := key
  refine ⟨a, (extensionEmbedding w).injective ?_⟩
  rw [map_mul, ha, ← Complex.ofReal_mul, Real.mul_self_sqrt h1.le, ← hre]
  rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
  change w.embedding t = extensionEmbedding w ((WithAbs.toAbs w.1 t : WithAbs w.1) : w.Completion)
  rw [extensionEmbedding_coe]
  simp

theorem exists_norm_at_infinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X],
    (∀ τ : E →+* ℂ, ((aeval γ.val m).map τ).PosDef) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r),
    Q.1 ∣ γ.val.charpoly →
    GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) =
      (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) →
    ∀ v : InfinitePlace (maximalRealSubfield E),
      ∃ z : v.Completion ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q,
        z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ n γ _ _ m hpos r Q hdvd hfix v
  let x : plus Q := ⟨AdjoinRoot.mk Q.1 m, hfix⟩
  obtain ⟨ψ, h1, hb⟩ := GlobalTheory.TraceClasses.exists_infinite_decomp (maximalRealSubfield E) (plus Q)
  have hroot : ∀ w : {w : InfinitePlace (plus Q) // w.comap (algebraMap (maximalRealSubfield E) (plus Q)) = v},
      ∃ a : w.1.Completion, a * a = algebraMap (plus Q) _ x := fun w =>
    exists_mul_self_of_pos w.1 x (pos_at_embedding Q γ.val m hpos hdvd x rfl w.1.embedding)
  choose a ha using hroot
  obtain ⟨b, hb'⟩ := (hb v).2 a
  have hb2 : b * b = 1 ⊗ₜ x := (hb v).1 (funext fun w => by
    have hw : ψ v w b = a w := congrFun hb' w
    simp only
    rw [map_mul, hw, ha, h1])
  refine ⟨inclPlus Q _ b, ?_⟩
  rw [GlobalTheory.TraceClasses.involBase_inclPlus, ← map_mul, hb2]
  rfl

end GlobalTheory.RealPlaceNorms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormAtSplitPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocalNormSplit

theorem exists_sq_of_split (E : Type) [Field E] [NumberField E] [IsCMField E]
    (θ : E) (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧
      w'.under (𝓞 (maximalRealSubfield E)) = v)
    (d : maximalRealSubfield E) (hd : (d : E) = θ * θ) :
    ∃ s : v.adicCompletion (maximalRealSubfield E),
      s * s = algebraMap (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)) d := by
  classical
  by_contra hns
  push_neg at hns
  obtain ⟨w, w', hne, hw, hw'⟩ := hv
  obtain ⟨ψ, -, hb, -⟩ := GlobalTheory.TraceClasses.exists_finite_decomp (maximalRealSubfield E) E
  have hθF : ∀ a : maximalRealSubfield E, (a : E) ≠ θ := by
    intro a ha
    have h1 : IsCMField.complexConj E (a : E) = a := (IsCMField.complexConj_eq_self_iff E _).2 a.2
    rw [ha, hθ] at h1
    exact hθ0 (by linear_combination -h1 / 2)
  have hli : LinearIndependent (maximalRealSubfield E) ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro p q hpq
    by_cases hq : q = 0
    · subst hq
      simpa using hpq
    · exfalso
      refine hθF (-p / q) ?_
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hpq
      have hq' : (q : E) ≠ 0 := by simpa using hq
      change ((-p / q : maximalRealSubfield E) : E) = θ
      push_cast
      field_simp
      rw [show algebraMap _ E p = p from rfl, show algebraMap _ E q = q from rfl] at hpq
      linear_combination -hpq
  let b := basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two])
  set K := v.adicCompletion (maximalRealSubfield E)
  let bA := Algebra.TensorProduct.basis K b
  let t : K ⊗[maximalRealSubfield E] E := 1 ⊗ₜ θ
  have hb0 : bA 0 = 1 := by
    simp [bA, b, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.one_def]
  have hb1 : bA 1 = t := by
    simp [bA, b, Algebra.TensorProduct.basis_apply, t]
  have li : ∀ p q : K, algebraMap K _ p + algebraMap K _ q * t = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have := Fintype.linearIndependent_iff.1 bA.linearIndependent ![p, q] (by
      rw [Fin.sum_univ_two, hb0, hb1]
      simpa [Algebra.smul_def] using h)
    exact ⟨by simpa using this 0, by simpa using this 1⟩
  have sp : ∀ y, y = algebraMap K _ (bA.repr y 0) + algebraMap K _ (bA.repr y 1) * t := by
    intro y
    conv_lhs => rw [← bA.sum_repr y]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one]
  have htt : t * t = algebraMap K _ (algebraMap (maximalRealSubfield E) K d) := by
    rw [← IsScalarTower.algebraMap_apply]
    change (1 : K) ⊗ₜ θ * (1 : K) ⊗ₜ θ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd]
    exact (Algebra.TensorProduct.includeRight.commutes d)
  let W := {u : HeightOneSpectrum (𝓞 E) // u.under (𝓞 (maximalRealSubfield E)) = v}
  let w₀ : W := ⟨w, hw⟩
  let w₁ : W := ⟨w', hw'⟩
  have h01 : w₀ ≠ w₁ := fun h => hne (congrArg Subtype.val h)
  let e₀ : ∀ u : W, u.1.adicCompletion E := Pi.single (M := fun u : W => u.1.adicCompletion E) w₀ 1
  let e₁ : ∀ u : W, u.1.adicCompletion E := Pi.single (M := fun u : W => u.1.adicCompletion E) w₁ 1
  obtain ⟨u₀, hu₀⟩ := (hb v).2 e₀
  obtain ⟨u₁, hu₁⟩ := (hb v).2 e₁
  have hprod : u₀ * u₁ = 0 := by
    apply (hb v).1
    funext u
    simp only [map_mul, map_zero]
    rw [show ψ v u u₀ = e₀ u from congrFun hu₀ u, show ψ v u u₁ = e₁ u from congrFun hu₁ u]
    by_cases h : u = w₀
    · subst h
      simp [e₁, Pi.single_apply, h01]
    · simp [e₀, Pi.single_apply, h]
  have hn₀ : u₀ ≠ 0 := by
    rintro rfl
    have := congrFun hu₀ w₀
    simp [e₀] at this
  have hn₁ : u₁ ≠ 0 := by
    rintro rfl
    have := congrFun hu₁ w₁
    simp [e₁] at this
  obtain ⟨a, b', hu0⟩ : ∃ a b' : K, u₀ = algebraMap K _ a + algebraMap K _ b' * t := ⟨_, _, sp u₀⟩
  obtain ⟨c, e, hu1⟩ : ∃ c e : K, u₁ = algebraMap K _ c + algebraMap K _ e * t := ⟨_, _, sp u₁⟩
  set d' := algebraMap (maximalRealSubfield E) K d
  have ha : ¬ (a = 0 ∧ b' = 0) := by
    rintro ⟨h1, h2⟩
    apply hn₀
    rw [hu0, h1, h2]
    simp
  have hc : ¬ (c = 0 ∧ e = 0) := by
    rintro ⟨h1, h2⟩
    apply hn₁
    rw [hu1, h1, h2]
    simp
  have heq := li (a * c + d' * b' * e) (a * e + b' * c) (by
    rw [← hprod, hu0, hu1]
    simp only [map_add (f := _), map_mul]
    linear_combination (-(algebraMap K _ b' * algebraMap K _ e)) * htt)
  have hz : c * c - d' * e * e = 0 := by
    by_contra hz
    apply ha
    constructor
    · refine (mul_eq_zero.1 (?_ : a * (c * c - d' * e * e) = 0)).resolve_right hz
      linear_combination c * heq.1 - d' * e * heq.2
    · refine (mul_eq_zero.1 (?_ : b' * (c * c - d' * e * e) = 0)).resolve_right hz
      linear_combination -(e * heq.1) + c * heq.2
  by_cases he : e = 0
  · apply hc
    refine ⟨?_, he⟩
    rw [he] at hz
    simpa using hz
  · apply hns (c / e)
    field_simp
    linear_combination hz

theorem exists_norm_of_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r) (x : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q), GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q x = x → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v) → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ x := by
  intro E _ _ _ r Q x hx v hv
  obtain ⟨θ, hθ0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  have hθ' : IsCMField.complexConj E θ = -θ := hθ
  have hdmem : θ * θ ∈ maximalRealSubfield E :=
    (IsCMField.complexConj_eq_self_iff E _).1 (by rw [map_mul, hθ']; ring)
  let K := v.adicCompletion (maximalRealSubfield E)
  obtain ⟨d, hd⟩ : ∃ d : maximalRealSubfield E, (d : E) = θ * θ := ⟨⟨_, hdmem⟩, rfl⟩
  obtain ⟨s, hs⟩ := exists_sq_of_split E θ hθ0 hθ' v hv d hd
  let B := K ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero, eq_comm] at hs
    have h1 := (_root_.map_eq_zero (algebraMap (maximalRealSubfield E) K)).1 hs
    rw [h1] at hd
    exact hθ0 (mul_self_eq_zero.1 (by simpa using hd.symm))
  let uT : B := 1 ⊗ₜ algebraMap E _ θ
  have hTT : uT * uT = algebraMap K B (s * s) := by
    rw [hs, ← IsScalarTower.algebraMap_apply]
    change (1 : K) ⊗ₜ algebraMap E _ θ * (1 : K) ⊗ₜ algebraMap E _ θ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul, ← hd,
      show (d : E) = algebraMap (maximalRealSubfield E) E d from rfl,
      ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes _)
  let uc : B := algebraMap K B s⁻¹ * uT
  have hc : uc * uc = 1 := by
    have : uc * uc = algebraMap K B (s⁻¹ * s⁻¹ * (s * s)) := by
      rw [map_mul, map_mul, ← hTT]; ring
    rw [this, show s⁻¹ * s⁻¹ * (s * s) = 1 by rw [← mul_inv, inv_mul_cancel₀ (mul_ne_zero hs0 hs0)], map_one]
  have hiT : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K uT = -uT := by
    change Algebra.TensorProduct.map _ _ ((1 : K) ⊗ₜ algebraMap E _ θ) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol_algebraMap, hθ',
      map_neg, TensorProduct.tmul_neg]
  have hic : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K uc = -uc := by
    change GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K (algebraMap K B s⁻¹ * uT) = -(algebraMap K B s⁻¹ * uT)
    rw [map_mul, AlgHom.commutes, hiT, mul_neg]
  have hiX : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K (1 ⊗ₜ x) = 1 ⊗ₜ x := by
    change Algebra.TensorProduct.map _ _ ((1 : K) ⊗ₜ x) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hx]
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap (maximalRealSubfield E) K) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  let hf : B := algebraMap K B 2⁻¹
  have hh : hf * 2 = 1 := by
    rw [← map_ofNat (algebraMap K B) 2, ← map_mul, inv_mul_cancel₀ h2K, map_one]
  have hih : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q K hf = hf := AlgHom.commutes _ _
  refine ⟨hf * (1 + uc) * (1 ⊗ₜ x) + hf * (1 - uc), ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_mul, map_add (f := _), map_sub, map_one, hic, hiX, hih]
  linear_combination (hf ^ 2 * (2 * (1 ⊗ₜ x : B) - (1 ⊗ₜ x : B) ^ 2 - 1)) * hc + ((2 * hf + 1) * (1 ⊗ₜ x : B)) * hh

end GlobalTheory.LocalNormSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulPosDef
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryClasses

theorem posDef_cT_inv_mul_inv (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (h : GL (Fin n) E)
    (τ : E →+* ℂ) :
    ((cT (IsCMField.complexConj E).toRingEquiv.toRingHom (h⁻¹).val * (h⁻¹).val).map τ).PosDef := by
  set B : Matrix (Fin n) (Fin n) E := (h⁻¹).val with hB
  have hc : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom B).map τ = (B.map τ)ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]
  rw [Matrix.map_mul, hc]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  have hu : IsUnit B := (h⁻¹).isUnit
  exact hu.map (RingHom.mapMatrix τ)

end GlobalTheory.UnitaryClasses
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalNormOfLocalNorms
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HasseFld

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

theorem isValue_of_local {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Q : SelfRecip E r) {θ : E} (h0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ) {d : plus Q}
    (hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ)
    (k : Type) [Field k] [Algebra (maximalRealSubfield E) k]
    (x : plus Q) (hx : x ≠ 0) (z : k ⊗[maximalRealSubfield E] Fld Q)
    (hz : z * involBase Q k z = 1 ⊗ₜ (x : Fld Q)) :
    GlobalTheory.TraceClasses.IsValue (1 ⊗ₜ d) (1 ⊗ₜ x : k ⊗[maximalRealSubfield E] plus Q) := by
  let U : (k ⊗[maximalRealSubfield E] plus Q)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight :
      plus Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] plus Q).toMonoidHom (Units.mk0 x hx)
  have hU : (U : k ⊗[maximalRealSubfield E] plus Q) = 1 ⊗ₜ x := rfl
  have hi : inclPlus Q k (1 ⊗ₜ x) = 1 ⊗ₜ (x : Fld Q) := by simp [inclPlus]
  have hzu : IsUnit z := by
    have : IsUnit (z * involBase Q k z) := by
      rw [hz, ← hi, ← hU]; exact U.isUnit.map _
    exact isUnit_of_mul_isUnit_left this
  have hmem : U ∈ norms Q k := ⟨hzu.unit, Units.ext (by
      change z * involBase Q k z = inclPlus Q k (U : _)
      rw [hz, hU, hi])⟩
  rw [← hU]
  exact (GlobalTheory.TraceClasses.mem_norms_iff Q h0 hθ k hd U).1 hmem

theorem hasse_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (Q : SelfRecip E r) (x : Fld Q), invol Q x = x →
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] Fld Q,
        z * involBase Q _ z = 1 ⊗ₜ x) →
    (∀ v : InfinitePlace (maximalRealSubfield E),
      ∃ z : v.Completion ⊗[maximalRealSubfield E] Fld Q, z * involBase Q _ z = 1 ⊗ₜ x) →
    ∃ y : Fld Q, y * invol Q y = x := by
  intro E _ _ _ r Q x hxx hf hi
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨θ, h0, hθ⟩ : ∃ θ : E, θ ≠ 0 ∧ IsCMField.complexConj E θ = -θ := by
    obtain ⟨w, hw⟩ : ∃ w : E, IsCMField.complexConj E w ≠ w := by
      by_contra h
      push_neg at h
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
    exact ⟨w - IsCMField.complexConj E w, sub_ne_zero.mpr hw.symm, by simp⟩
  let x' : plus Q := ⟨x, hxx⟩
  have hx' : x' ≠ 0 := fun h => hx (congrArg Subtype.val h)
  let d : plus Q := ⟨algebraMap E _ θ * algebraMap E _ θ, by
    show invol Q _ = (AlgHom.id _ _) _
    rw [map_mul, GlobalTheory.TraceClasses.invol_theta Q hθ]
    simp⟩
  have hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ := rfl
  obtain ⟨e, e0, e1⟩ := GlobalTheory.TraceClasses.exists_basis_theta Q h0 hθ
  have := GlobalTheory.TraceClasses.isQuadraticExtension Q h0 hθ
  have e2 : e 1 * e 1 = algebraMap _ _ d := by rw [e1]; exact hd.symm
  obtain ⟨a, b, hab⟩ := GlobalTheory.TraceClasses.form_of_local (F := maximalRealSubfield E) e e0 e2
    (Units.mk0 x' hx')
    (fun v => by
      obtain ⟨z, hz⟩ := hf v
      exact isValue_of_local Q h0 hθ hd _ x' hx' z hz)
    (fun v => by
      obtain ⟨z, hz⟩ := hi v
      exact isValue_of_local Q h0 hθ hd _ x' hx' z hz)
  refine ⟨a + b * algebraMap E _ θ, ?_⟩
  have hx2 : x = (a : Fld Q) ^ 2 - d * b ^ 2 := by
    have := congrArg Subtype.val hab
    simpa using this
  rw [map_add (f := _), map_mul, GlobalTheory.TraceClasses.invol_coe, GlobalTheory.TraceClasses.invol_coe,
    GlobalTheory.TraceClasses.invol_theta Q hθ, hx2, hd]
  ring

end GlobalTheory.HasseFld
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.HermitianLocalDataAlmostAll
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.HermitianFormLocalGlobal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.hermitian_form_local_global : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H w = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := by
  first | exact @PositivityTheory.BCUSide.L.hermitian_form_local_global | exact PositivityTheory.BCUSide.L.hermitian_form_local_global
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.HermitianLocalGlobalExistence
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.hermitian_local_global_existence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H w = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val) := by first | exact @GlobalTheory.UsideLeaf.hermitian_local_global_existence.main | exact GlobalTheory.UsideLeaf.hermitian_local_global_existence.main
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ExistsGlobalHermitianForm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.exists_global_hermitian_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∃ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ ∧ H₀.det ≠ 0 ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) := by
  first | exact @GlobalTheory.RefForm.cT_mul | exact @GlobalTheory.RefForm.cT_cT_conj | exact @GlobalTheory.RefForm.det_cT_conj | exact @GlobalTheory.RefForm.cT_diag_mul_diag | exact @GlobalTheory.RefForm.assemble | exact @GlobalTheory.RefForm.exists_roots_enum | exact @GlobalTheory.RefForm.powBasis_apply | exact @GlobalTheory.RefForm.vandermonde_mul_compMat | exact @GlobalTheory.RefForm.charpoly_compMat | exact @GlobalTheory.RefForm.trace_semiconj | exact @GlobalTheory.RefForm.exists_model | exact @GlobalTheory.RefForm.map_cT_complexConj | exact @GlobalTheory.RefForm.exists_refForm | (intros; apply GlobalTheory.RefForm.exists_refForm <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.HermitianFormSignatureRealisation
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_signature_realisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) := by
  first | exact @GlobalTheory.UnitaryClasses.refSign_prod | exact GlobalTheory.UnitaryClasses.refSign_prod | (intros; apply GlobalTheory.UnitaryClasses.refSign_prod <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.HermitianLocalDataAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryClasses.ExistForm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := by
  intro E _ _ _ hU S hS n γ₀ hP H hH hlat hsg
  obtain ⟨H₀, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_global_hermitian_form E n γ₀ hP
  exact GlobalTheory.T.hermitian_form_local_global E hU S hS n γ₀ hP H₀ h1 h2 h3 h4 (GlobalTheory.T.hermitian_form_signature_realisation E hU S hS n γ₀ hP H₀ h1 h2 h3 h4) H hH
    (GlobalTheory.T.hermitian_local_global_existence E hU n γ₀ hP H₀ h1 h2 h3 H hH hlat) hsg

end GlobalTheory.UnitaryClasses.ExistForm
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.HermitianLocalDataAlmostAllStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.hermitian_local_data_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := by
  first | exact @GlobalTheory.UnitaryClasses.ExistForm.main | (intros; apply GlobalTheory.UnitaryClasses.ExistForm.main <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NonsplitPlaceNormCentraliser
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NonsplitCentraliserNormElement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.nonsplit_centraliser_norm_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E))) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∀ w w' : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v → w'.under (𝓞 (maximalRealSubfield E)) = v → w = w') → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  first | exact @GlobalTheory.NormInert.main | exact GlobalTheory.NormInert.main | (intros; apply GlobalTheory.NormInert.main <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ExistsNormSolutionFields
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.exists_norm_solution_fields : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → (∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, y * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q y = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q)) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = aeval γ.val m := by
  first | exact @GlobalTheory.NormAssemble.exists_norm_of_factors | exact GlobalTheory.NormAssemble.exists_norm_of_factors | (intros; apply GlobalTheory.NormAssemble.exists_norm_of_factors <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.InvolutionFixesPolynomialImage
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.involution_fixes_polynomial_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ.val m) = aeval γ.val m → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  first | exact @GlobalTheory.NormHasseFixed.invol_mk_eq | (intros; apply GlobalTheory.NormHasseFixed.invol_mk_eq <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.TotallyPositiveRealPlaces
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.totally_positive_real_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], (∀ τ : E →+* ℂ, ((aeval γ.val m).map τ).PosDef) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : InfinitePlace (maximalRealSubfield E), ∃ z : v.Completion ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  first | exact @GlobalTheory.RealPlaceNorms.exists_norm_at_infinite | exact GlobalTheory.RealPlaceNorms.exists_norm_at_infinite | (intros; apply GlobalTheory.RealPlaceNorms.exists_norm_at_infinite <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalNormAtSplitPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.local_norm_at_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r) (x : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q), GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q x = x → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v) → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ x := by
  first | exact @GlobalTheory.LocalNormSplit.exists_norm_of_split | exact GlobalTheory.LocalNormSplit.exists_norm_of_split | (intros; apply GlobalTheory.LocalNormSplit.exists_norm_of_split <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ConjTransposeMulPosDef
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.conj_transpose_mul_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (h : GL (Fin n) E) (τ : E →+* ℂ), ((cT (IsCMField.complexConj E).toRingEquiv.toRingHom (h⁻¹).val * (h⁻¹).val).map τ).PosDef := by
  first | exact @GlobalTheory.UnitaryClasses.posDef_cT_inv_mul_inv | (intros; apply GlobalTheory.UnitaryClasses.posDef_cT_inv_mul_inv <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.GlobalNormOfLocalNorms
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.global_norm_of_local_norms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r) (x : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q), GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q x = x → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ x) → (∀ v : InfinitePlace (maximalRealSubfield E), ∃ z : v.Completion ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ x) → ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, y * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q y = x := by
  first | exact @GlobalTheory.HasseFld.hasse_norm | (intros; apply GlobalTheory.HasseFld.hasse_norm <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NonsplitPlaceNormCentraliser
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormHasseCent

theorem inv_hh {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (k : GL (Fin n) K) : (k.val * cT σ k.val)⁻¹ = cT σ (k⁻¹).val * (k⁻¹).val :=
  Matrix.inv_eq_right_inv (by rw [Matrix.mul_assoc, cT_units_left', Units.mul_inv])

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := by
  intro E _ _ _ hU n γ h hγ hP hconj hloc
  set σ := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσdef
  have hσ : ∀ x, σ (σ x) = x := fun x => IsCMField.complexConj_apply_apply E x
  set N := cT σ (h⁻¹).val * (h⁻¹).val with hN
  have hγ' : cT σ γ.val * 1 * γ.val = 1 := hγ
  have hinv := inv_of_unit σ h γ hconj
  have hγγ : γ.val * cT σ γ.val = 1 := by
    rw [Matrix.mul_one] at hγ'; exact mul_eq_one_comm.1 hγ'
  have hcomm : γ.val * N = N * γ.val := by
    have := congrArg (γ.val * ·) hinv
    simp only [← Matrix.mul_assoc, hγγ, Matrix.one_mul] at this
    rw [hN]; simpa only [Matrix.mul_assoc] using this.symm
  obtain ⟨m, hm⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ.val N hP.2.2.1 hcomm
  have hherm : cT σ (aeval γ.val m) = aeval γ.val m := by
    rw [← hm]; exact herm_of σ hσ h
  have hM : (h.val * cT σ h.val)⁻¹ = aeval γ.val m := by rw [inv_hh, ← hN, hm]
  have hsr := GlobalTheory.T.isConjSelfReciprocal_of_dvd_elliptic_polynomial E n _ hP
  have hfix := GlobalTheory.T.involution_fixes_polynomial_image E n γ hγ hP m hherm
  have hloc' : ∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E)) := (fun w hw => by
    obtain ⟨c, hc1, hc2⟩ := hloc w hw
    refine ⟨c, hc1, ?_⟩
    rw [hc2, inv_hh, ← hm, hN, ← map_inv]
    rw [Matrix.map_mul, cT_map hU w hw]; rfl)
  have hfin : ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
    intro r Q hQ hx v
    by_cases hs : ∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v
    · exact GlobalTheory.T.local_norm_at_split_place E r Q _ hx v hs
    · refine GlobalTheory.T.nonsplit_centraliser_norm_element E hU n γ hγ hP m hloc' r Q hQ hx v (fun w w' hw hw' => ?_)
      by_contra hne
      exact hs ⟨w, w', hne, hw, hw'⟩
  have hinf := GlobalTheory.T.totally_positive_real_places E n γ hγ hP m (fun τ => by rw [← hm]; exact GlobalTheory.T.conj_transpose_mul_posDef E n h τ)
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_norm_solution_fields E n γ hγ hP hsr m (fun r Q hQ =>
    GlobalTheory.T.global_norm_of_local_norms E r Q _ (hfix r Q hQ) (hfin r Q hQ (hfix r Q hQ)) (hinf r Q hQ (hfix r Q hQ)))
  exact ⟨c, hc1, by rw [hc2, hM]⟩

end GlobalTheory.NormHasseCent
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NonsplitPlaceNormCentraliserStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.nonsplit_place_norm_centraliser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := by
  first | exact @GlobalTheory.NormHasseCent.main | (intros; apply GlobalTheory.NormHasseCent.main <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryConjugacySignProduct
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryClasses

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conjGL : ∀ (K : Type) [Field K] (n : ℕ) (a b : GL (Fin n) K), a.val.charpoly = b.val.charpoly → a.val.charpoly.Separable → ∃ h : GL (Fin n) K, b = h⁻¹ * a * h := GlobalTheory.T.exists_conj_GL_of_charpoly_eq_of_separable

theorem companionEll : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := GlobalTheory.T.exists_GL_charpoly_eq_of_mem_Ell

theorem unitConj : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ h : GL (Fin n) K), (∃ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) K), h⁻¹ * γ * h = g⁻¹ * γ * g) ↔ ∃ c : Matrix (Fin n) (Fin n) K, c * γ.val = γ.val * c ∧ cT σ c * c = (h.val * cT σ h.val)⁻¹ := GlobalTheory.T.exists_unitary_conj_iff_exists_centralizer_norm

theorem normHasse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := GlobalTheory.T.nonsplit_place_norm_centraliser

theorem signProd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := GlobalTheory.T.finprod_nonsplit_sign_totallyPositive_eq_one

theorem gramPos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (V : Submodule E (Fin n → E)), (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det ≠ 0 ∧ ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det = r := GlobalTheory.T.gram_det_hermitian_totally_positive

theorem sgnConj : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K), (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K), sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := GlobalTheory.T.sesquilinearDetOrdSignOnKernel_conj_GL

theorem baseChangeSign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E), (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E))) (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq

theorem existForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := GlobalTheory.T.hermitian_local_data_almost_all

theorem landherrStd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E), H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) → ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := GlobalTheory.T.landherr_standard_definite_hermitian_cmField

theorem part1 (hU : Unr E) {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n) (γ γ' : UE E n)
    (h1 : γ.1.val.charpoly = P) (h2 : γ'.1.val.charpoly = P)
    (hloc : ∀ w ∈ S, ∃ g : UL n w, locPt w γ' = g⁻¹ * locPt w γ * g) : ∃ g : UE E n, γ' = g⁻¹ * γ * g := by
  obtain ⟨h, hh⟩ := conjGL E n γ.1 γ'.1 (h1.trans h2.symm) (h1 ▸ hP.2.2.1)
  have hγ' : h⁻¹ * γ.1 * h ∈ UE E n := hh ▸ γ'.2
  obtain ⟨c, hc1, hc2⟩ := normHasse E hU n γ.1 h γ.2 (h1 ▸ hP) hγ' (fun w hw => by
    obtain ⟨g, hg⟩ := hloc w (mem_S hS hw)
    have hUL : UL n w = UJ (cj w) 1 := by unfold UL; rw [if_neg hw]
    refine (unitConj _ (cj w) n _ _).1 ⟨g.1, hUL ▸ g.2, ?_⟩
    have := congrArg Subtype.val hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, locPt_val hU] at this
    rw [← map_inv, ← map_mul, ← map_mul, ← hh]; exact this)
  obtain ⟨g, hg, hgg⟩ := (unitConj E _ n γ.1 h).2 ⟨c, hc1, hc2⟩
  exact ⟨⟨g, hg⟩, Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rw [hh, hgg])⟩

theorem part2 (hU : Unr E) {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) (γ : UE E n) (P₁ : E[X]) :
    ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (locPt w γ).1 = 1 := by
  obtain ⟨hd0, hdpos⟩ := gramPos E n (LinearMap.ker (Matrix.toLin' (aeval γ.1.val P₁)))
  rw [← signProd E hU S hS _ hd0 hdpos]
  apply finprod_mem_congr rfl
  intro w _
  by_cases hw : IsSplitAt w
  · rw [if_pos hw]; unfold kapSign; rw [if_pos hw]
  · rw [if_neg hw, kapSign_eq w hw, locPt_val hU]
    unfold sgnOn
    have hA := aeval_map_mat w γ.1.val P₁
    have := baseChangeSign E hU w hw n 1 (aeval γ.1.val P₁)
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [← this, ← hA]
    rfl

theorem part3 (hU : Unr E) {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n)
    (y : ∀ w : Pl E, UL n w) (hy : ∀ w, (y w).1.val.charpoly = atPl w P) (hK : ∀ᶠ w in cofinite, y w ∈ KL n w)
    (hsg : ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1) :
    ∃ γ : UE E n, γ.1.val.charpoly = P ∧ ∀ w ∈ S, ∃ g : UL n w, locPt w γ = g⁻¹ * y w * g := by
  obtain ⟨γ₀, hγ₀⟩ := companionEll E n P hP
  have hAcp : ∀ w : Pl E, (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀).val.charpoly = atPl w P :=
    fun w => by rw [← hγ₀]; exact Matrix.charpoly_map _ _
  have hsep : ∀ w : Pl E, (atPl w P).Separable := fun w => hP.2.2.1.map
  have hk : ∀ w : Pl E, ∃ k : GLw n w,
      (y w).1 = k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k := fun w =>
    conjGL _ n _ (y w).1 ((hAcp w).trans (hy w).symm) (hAcp w ▸ hsep w)
  choose k hk using hk
  have hinvol : ∀ w : Pl E, ∀ x, cj w (cj w x) = x := fun w => (GlobalTheory.ConjAtPlace.main E hU w).2.1
  have hval : ∀ w : Pl E, ∀ x, Valued.v (cj w x) = Valued.v x := fun w => (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  have hUL : ∀ w : Pl E, ¬ IsSplitAt w → UL n w = UJ (cj w) 1 := fun w hw => by unfold UL; rw [if_neg hw]
  have hyU : ∀ w : Pl E, ¬ IsSplitAt w → cT (cj w) (y w).1.val * 1 * (y w).1.val = 1 := fun w hw => by
    have h3 : ∀ z : GLw n w, z ∈ UL n w → cT (cj w) z.val * 1 * z.val = 1 := by
      intro z hz; unfold UL at hz; rw [if_neg hw] at hz; exact hz
    exact h3 _ (y w).2
  obtain ⟨H', hH'h, hH'i, hH'p, hH'l⟩ := existForm E hU S hS n γ₀ (hγ₀ ▸ hP)
    (fun w => cT (cj w) ((k w)⁻¹).val * ((k w)⁻¹).val)
    (fun w hw => ⟨herm_of _ (hinvol w) _, det_ne _ _,
      inv_of_unit _ (k w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀) (hk w ▸ hyU w hw)⟩)
    (hK.mono fun w hw _ => ⟨k w, 1, by rw [← hk w]; exact (Subgroup.mem_subgroupOf).1 hw, one_mem _,
      (one_of _ (k w)).symm⟩)
    (fun P₁ hm hd => by
      refine Eq.trans ?_ (hsg P₁ hm (hγ₀ ▸ hd))
      apply finprod_mem_congr rfl
      intro w _
      by_cases hw : IsSplitAt w
      · rw [if_pos hw]; unfold kapSign; rw [if_pos hw]
      · rw [if_neg hw, kapSign_eq w hw, hk w, sgnConj _ (cj w) (hval w)]
        rfl)
  obtain ⟨h, hh⟩ := landherrStd E hU n H' hH'h hH'p (fun w hw => by
    obtain ⟨c, -, hc⟩ := hH'l w hw
    exact ⟨((k w)⁻¹).val * c.val, by rw [hc, cT_mul]; simp only [Matrix.mul_assoc]⟩)
  have hγU : h * γ₀ * h⁻¹ ∈ UE E n := unit_of_form _ γ₀ h (by rw [← hh]; exact hH'i)
  refine ⟨⟨_, hγU⟩, ?_, fun w hwS => ?_⟩
  · show (h.val * γ₀.val * (h⁻¹).val).charpoly = P
    rw [Matrix.coe_units_inv, ← hγ₀]
    exact Matrix.charpoly_units_conj h γ₀.val
  · by_cases hw : IsSplitAt w
    · have hb : ((locPt w (⟨_, hγU⟩ : UE E n) : UL n w) : GLw n w).val.charpoly = (y w).1.val.charpoly := by
        rw [locPt_val hU, hy w, ← hAcp w]
        show ((h * γ₀ * h⁻¹ : GL (Fin n) E).val.map _).charpoly = (γ₀.val.map _).charpoly
        rw [Matrix.charpoly_map, Matrix.charpoly_map]
        congr 1
        show (h.val * γ₀.val * (h⁻¹).val).charpoly = _
        rw [Matrix.coe_units_inv]
        exact Matrix.charpoly_units_conj h γ₀.val
      obtain ⟨h', hh'⟩ := conjGL _ n (y w).1 _ hb.symm ((hy w) ▸ hsep w)
      have hmem : h' ∈ UL n w := by unfold UL; rw [if_pos hw]; trivial
      exact ⟨⟨h', hmem⟩, Subtype.ext (by simpa using hh')⟩
    · obtain ⟨c, hc1, hc2⟩ := hH'l w hw
      have hg : (k w)⁻¹ * c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h)⁻¹ ∈ UL n w := by
        rw [hUL w hw]
        refine unit_of_two _ (k w) c (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h) _ hc2 ?_
        rw [hh, Matrix.map_mul, cT_map hU w hw]; rfl
      refine ⟨⟨_, hg⟩, Subtype.ext ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [locPt_val hU, hk w]
      have hcA : c * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * c := Units.ext hc1
      have key : ∀ x : GLw n w, c⁻¹ * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * (c * x)) =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * x := fun x => by
        rw [← mul_assoc _ c x, ← hcA, mul_assoc, inv_mul_cancel_left]
      show GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (h * γ₀ * h⁻¹) = _
      simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, key]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, (∀ γ γ' : UE E n, γ.1.val.charpoly = P → γ'.1.val.charpoly = P → (∀ w ∈ S, ∃ g : UL n w, locPt w γ' = g⁻¹ * locPt w γ * g) → ∃ g : UE E n, γ' = g⁻¹ * γ * g) ∧ (∀ γ : UE E n, γ.1.val.charpoly = P → ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (locPt w γ).1 = 1) ∧ ∀ y : ∀ w : Pl E, UL n w, (∀ w, (y w).1.val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ KL n w) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1) → ∃ γ : UE E n, γ.1.val.charpoly = P ∧ ∀ w ∈ S, ∃ g : UL n w, locPt w γ = g⁻¹ * y w * g := by
  intro E _ _ _ hU n _ S hS P hP
  exact ⟨fun γ γ' h1 h2 hl => part1 hU hS hP γ γ' h1 h2 hl, fun γ _ P₁ _ _ => part2 hU hS γ P₁,
    fun y hy hK hsg => part3 hU hS hP y hy hK hsg⟩

end GlobalTheory.UnitaryClasses
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryConjugacySignProductStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.unitary_conjugacy_sign_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, (∀ γ γ' : UE E n, γ.1.val.charpoly = P → γ'.1.val.charpoly = P → (∀ w ∈ S, ∃ g : UL n w, locPt w γ' = g⁻¹ * locPt w γ * g) → ∃ g : UE E n, γ' = g⁻¹ * γ * g) ∧ (∀ γ : UE E n, γ.1.val.charpoly = P → ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (locPt w γ).1 = 1) ∧ ∀ y : ∀ w : Pl E, UL n w, (∀ w, (y w).1.val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ KL n w) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1) → ∃ γ : UE E n, γ.1.val.charpoly = P ∧ ∀ w ∈ S, ∃ g : UL n w, locPt w γ = g⁻¹ * y w * g := by
  first | exact @GlobalTheory.UnitaryClasses.main | (intros; apply GlobalTheory.UnitaryClasses.main <;> assumption)
end
