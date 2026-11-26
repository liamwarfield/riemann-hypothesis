module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTraceFromLocalInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassFirst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassThird
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveHermitianPolynomialStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveHermitianPolynomial
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder ComplexConjugate
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.PosDefNorm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_value_pos {r : ℕ} (Q : SelfRecip E r) (ρ : Fld Q →+* ℂ) (hn : ‖ρ (alpha Q)‖ = 1) (y : Fld Q)
    (hz : ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[maximalRealSubfield E] Fld Q)ˣ,
      (z : u.Completion ⊗[maximalRealSubfield E] Fld Q) *
        involBase Q u.Completion (z : u.Completion ⊗[maximalRealSubfield E] Fld Q) = 1 ⊗ₜ y) :
    0 < ρ y := by
  have hinv : ∀ x, ρ (invol Q x) = conj (ρ x) := by
    have h : (ρ.comp (invol Q : Fld Q →+* Fld Q)) = (starRingEnd ℂ).comp ρ := by
      refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
      · change ρ (invol Q (algebraMap E (Fld Q) e)) = conj (ρ (algebraMap E (Fld Q) e))
        rw [invol_algebraMap]
        exact IsCMField.complexEmbedding_complexConj E (ρ.comp (algebraMap E (Fld Q))) e
      · change ρ (invol Q (alpha Q)) = conj (ρ (alpha Q))
        rw [invol_alpha, map_inv₀]
        exact Complex.inv_eq_conj hn
    exact fun x => DFunLike.congr_fun h x
  let ρF : maximalRealSubfield E →+* ℂ := ρ.comp (algebraMap (maximalRealSubfield E) (Fld Q))
  let w := InfinitePlace.mk ρF
  have hw : w.IsReal := IsTotallyReal.isReal w
  letI : Algebra (maximalRealSubfield E) ℂ := ρF.toAlgebra
  let g : w.Completion →ₐ[maximalRealSubfield E] ℂ :=
    ⟨InfinitePlace.Completion.extensionEmbedding w, fun a => by
      change InfinitePlace.Completion.extensionEmbedding w (algebraMap (maximalRealSubfield E) w.Completion a) = ρF a
      simpa only [InfinitePlace.Completion.algebraMap_apply] using
        (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ a)).trans
          (DFunLike.congr_fun (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)) a)⟩
  have hg : ∀ a, conj (g a) = g a := fun a => by
    have : g a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw a : ℂ) :=
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a).symm
    rw [this, Complex.conj_ofReal]
  let f := (Algebra.TensorProduct.productMap g
    (⟨ρ, fun _ => rfl⟩ : Fld Q →ₐ[maximalRealSubfield E] ℂ)).toRingHom
  have hf : ∀ a e, f (a ⊗ₜ e) = g a * ρ e := fun _ _ => rfl
  have hfi : ∀ t, f (involBase Q w.Completion t) = conj (f t) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [involBase, Algebra.TensorProduct.map_tmul, hf, hf, map_mul, hg]
      exact congrArg _ (hinv e)
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  obtain ⟨z, hz⟩ := hz w
  have h1 := congrArg f hz
  rw [map_mul, hfi, hf, map_one, one_mul, Complex.mul_conj] at h1
  have h2 : f (z : w.Completion ⊗[maximalRealSubfield E] Fld Q) ≠ 0 := (z.isUnit.map f).ne_zero
  rw [← h1]
  exact_mod_cast Complex.normSq_pos.2 h2

theorem exists_irreducible_factor (P : E[X]) (hP : P.Monic) (τ : E →+* ℂ) (μ : ℂ) (h : eval₂ τ μ P = 0) :
    ∃ R : E[X], R.Monic ∧ Irreducible R ∧ R ∣ P ∧ eval₂ τ μ R = 0 := by
  letI : Algebra E ℂ := τ.toAlgebra
  have hi : IsIntegral E μ := ⟨P, hP, h⟩
  exact ⟨minpoly E μ, minpoly.monic hi, minpoly.irreducible hi, minpoly.dvd E μ h, minpoly.aeval E μ⟩

theorem aeval_units_conj {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ[X]) :
    aeval ((u : Matrix (Fin n) (Fin n) ℂ) * A * ((u⁻¹ : _ˣ) : Matrix (Fin n) (Fin n) ℂ)) p =
      (u : Matrix (Fin n) (Fin n) ℂ) * aeval A p * ((u⁻¹ : _ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, mul_add, add_mul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]

theorem posDef_aeval {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (hs : U.charpoly.Separable)
    (hn : ∀ μ : ℂ, U.charpoly.IsRoot μ → ‖μ‖ = 1) (p : ℂ[X])
    (hp : ∀ μ : ℂ, U.charpoly.IsRoot μ → 0 < p.eval μ) : (aeval U p).PosDef := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  obtain ⟨r, hr⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm U Uᴴ hs (hU'.trans hU.symm)
  have hdiv : U.charpoly ∣ X * r - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval U hs _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr, hU', map_one, sub_self]
  have hrv : ∀ μ : ℂ, U.charpoly.IsRoot μ → r.eval μ = conj μ := fun μ hμ => by
    obtain ⟨t, ht⟩ := hdiv
    have h1 := congrArg (eval μ) ht
    have h0 : eval μ U.charpoly = 0 := hμ
    rw [eval_mul, h0, zero_mul, eval_sub, eval_mul, eval_X, eval_one, sub_eq_zero] at h1
    rw [← Complex.inv_eq_conj (hn μ hμ)]
    exact eq_inv_of_mul_eq_one_right h1
  have hcT : (aeval U p)ᴴ = aeval U ((p.map (starRingEnd ℂ)).comp r) := by
    have h1 := GlobalTheory.NormInert.cT_aeval (starRingEnd ℂ) U p
    have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, cT (starRingEnd ℂ) M = Mᴴ := fun M => rfl
    rw [h2, h2, hr, ← aeval_comp] at h1
    exact h1
  have hzero : aeval U (p - (p.map (starRingEnd ℂ)).comp r) = 0 := by
    by_cases h0 : p - (p.map (starRingEnd ℂ)).comp r = 0
    · rw [h0, map_zero]
    have hd : U.charpoly ∣ p - (p.map (starRingEnd ℂ)).comp r := by
      refine (IsAlgClosed.splits _).dvd_of_roots_le_roots U.charpoly_monic.ne_zero ?_
      rw [Multiset.le_iff_subset (nodup_roots hs)]
      intro μ hμ
      have hμ' := isRoot_of_mem_roots hμ
      rw [mem_roots h0, IsRoot.def, eval_sub, eval_comp, hrv μ hμ', sub_eq_zero, eval_map]
      have h3 : eval₂ (starRingEnd ℂ) (conj μ) p = conj (eval μ p) := by
        rw [eval, Polynomial.hom_eval₂, RingHom.comp_id]
      rw [h3]
      exact (Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 (hp μ hμ')).2.symm).symm
    obtain ⟨t, ht⟩ := hd
    rw [ht, map_mul, Matrix.aeval_self_charpoly, zero_mul]
  have hH : (aeval U p).IsHermitian := by
    rw [Matrix.IsHermitian, hcT]
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  rw [hH.posDef_iff_eigenvalues_pos]
  intro i
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h1 : ((hH.eigenvalues i : ℝ) : ℂ) ∈ spectrum ℂ (aeval U p) := by
    have := hH.eigenvalues_mem_spectrum_real i
    rw [← spectrum.preimage_algebraMap ℂ] at this
    exact this
  rw [spectrum.map_polynomial_aeval_of_nonempty _ _ (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ U)] at h1
  obtain ⟨μ, hμ, e⟩ := h1
  have h2 := hp μ (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hμ)
  rw [show eval μ p = ((hH.eigenvalues i : ℝ) : ℂ) from e] at h2
  exact_mod_cast h2

open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem exists_factor {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.PosSemidef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, T = Sᴴ * S := by
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT.nonneg
  exact ⟨y, rfl⟩

theorem map_aeval {n : ℕ} (τ : E →+* ℂ) (A : Matrix (Fin n) (Fin n) E) (p : E[X]) :
    (aeval A p).map τ = aeval (A.map τ) (p.map τ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j
    simp
  | monomial k a =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial]
    have e : (A.map τ) ^ k = (A ^ k).map τ := by rw [Matrix.map_pow]
    rw [e]
    ext i j
    simp [Algebra.algebraMap_eq_smul_one]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ, (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q u.Completion (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : Fld Q)) → ∀ τ : E →+* ℂ, ∃ Q' : Matrix (Fin n) (Fin n) ℂ, Q'.det ≠ 0 ∧ (H₀ * aeval γ₀.val m).map τ = cT (starRingEnd ℂ) Q' * Q' := by
  intro E _ _ _ n γ₀ hell H₀ _ _ hiso hdef m _ hz τ
  obtain ⟨Q, hQ, hHQ⟩ := hdef τ
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, cT (starRingEnd ℂ) M = Mᴴ := fun M => rfl
  rw [h2] at hHQ
  set A := γ₀.val.map τ with hA
  have hiso' : Aᴴ * (Qᴴ * Q) * A = Qᴴ * Q := by
    have h := congrArg (fun M => M.map τ) hiso
    simp only [Matrix.map_mul] at h
    have e : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val).map τ = Aᴴ := by
      ext i j
      exact IsCMField.complexEmbedding_complexConj E τ (γ₀.val j i)
    rw [e, hHQ] at h
    exact h
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((Matrix.isUnit_iff_isUnit_det Q).2 (isUnit_iff_ne_zero.2 hQ)).unit
  have hu : (u : Matrix (Fin n) (Fin n) ℂ) = Q := rfl
  obtain ⟨Qi, hQi⟩ : ∃ Qi : Matrix (Fin n) (Fin n) ℂ, Qi = ((u⁻¹ : _ˣ) : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have e1 : Q * Qi = 1 := by rw [hQi, ← hu]; exact u.mul_inv
  have e2 : Qi * Q = 1 := by rw [hQi, ← hu]; exact u.inv_mul
  have hconj := aeval_units_conj u A (m.map τ)
  have hchar := Matrix.charpoly_units_conj u A
  rw [← Matrix.coe_units_inv] at hchar
  rw [hu, ← hQi] at hconj hchar
  have hAc : A.charpoly = γ₀.val.charpoly.map τ := Matrix.charpoly_map _ _
  obtain ⟨U, hUd⟩ : ∃ U, U = Q * A * Qi := ⟨_, rfl⟩
  rw [← hUd] at hconj hchar
  have hU : Uᴴ * U = 1 := by
    have e3 : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, e1, conjTranspose_one]
    calc Uᴴ * U = Qiᴴ * (Aᴴ * (Qᴴ * Q) * A) * Qi := by
          simp only [hUd, conjTranspose_mul, Matrix.mul_assoc]
      _ = (Qiᴴ * Qᴴ) * (Q * Qi) := by rw [hiso']; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, e3, Matrix.mul_one]
  have hroot : ∀ μ : ℂ, U.charpoly.IsRoot μ → (γ₀.val.charpoly.map τ).IsRoot μ := fun μ h => by
    rwa [hchar, hAc] at h
  have hnorm : ∀ μ : ℂ, U.charpoly.IsRoot μ → ‖μ‖ = 1 := fun μ h =>
    hell.2.2.2 τ μ ((mem_roots (Polynomial.map_ne_zero hell.1.ne_zero)).2 (hroot μ h))
  have hsep : U.charpoly.Separable := by
    rw [hchar, hAc]
    exact hell.2.2.1.map
  have hp : ∀ μ : ℂ, U.charpoly.IsRoot μ → 0 < (m.map τ).eval μ := fun μ h => by
    have h0 : eval₂ τ μ γ₀.val.charpoly = 0 := by
      rw [← eval_map]
      exact hroot μ h
    obtain ⟨R, Rm, Ri, Rd, Re⟩ := exists_irreducible_factor _ hell.1 τ μ h0
    let S : SelfRecip E R.natDegree := ⟨R, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell R Rm Ri Rd⟩
    let ρ : Fld S →+* ℂ := AdjoinRoot.lift τ μ Re
    have hα : ρ (alpha S) = μ := AdjoinRoot.lift_root Re
    have hm : ρ (AdjoinRoot.mk S.1 m : Fld S) = eval₂ τ μ m := AdjoinRoot.lift_mk Re m
    have := norm_value_pos S ρ (by rw [hα]; exact hnorm μ h) _ (hz _ S Rd)
    rwa [hm, ← eval_map] at this
  have hT := posDef_aeval U hU hsep hnorm (m.map τ) hp
  obtain ⟨S, hS⟩ := exists_factor hT.posSemidef
  have hdetS : S.det ≠ 0 := fun h => by
    have := hT.det_pos
    rw [hS, Matrix.det_mul, h, mul_zero] at this
    exact lt_irrefl _ this
  refine ⟨S * Q, by rw [Matrix.det_mul]; exact mul_ne_zero hdetS hQ, ?_⟩
  have e4 : Q * aeval A (m.map τ) = (Sᴴ * S) * Q := by
    rw [← hS, hconj, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [Matrix.map_mul, hHQ, map_aeval, h2, conjTranspose_mul, Matrix.mul_assoc, e4]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.PosDefNorm
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_hermitian_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ, (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q u.Completion (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : Fld Q)) → ∀ τ : E →+* ℂ, ∃ Q' : Matrix (Fin n) (Fin n) ℂ, Q'.det ≠ 0 ∧ (H₀ * aeval γ₀.val m).map τ = cT (starRingEnd ℂ) Q' * Q' := by
  first | exact @GlobalTheory.CompanionTheory.PosDefNorm.main | exact GlobalTheory.CompanionTheory.PosDefNorm.main | (intros; apply GlobalTheory.CompanionTheory.PosDefNorm.main <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvdOfPhiEqZero
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section
namespace GlobalTheory.CompanionTheory.LocAssembly

def tensorLift {R A B T : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing T] [Algebra R A] [Algebra R B]
    (a : A →+* T) (b : B →+* T) (h : ∀ x : R, a (algebraMap R A x) = b (algebraMap R B x)) : A ⊗[R] B →+* T :=
  letI : Algebra R T := (a.comp (algebraMap R A)).toAlgebra
  (Algebra.TensorProduct.lift (⟨a, fun _ => rfl⟩ : A →ₐ[R] T) (⟨b, fun x => (h x).symm⟩ : B →ₐ[R] T)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem tensorLift_tmul {R A B T : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing T] [Algebra R A]
    [Algebra R B] (a : A →+* T) (b : B →+* T) (h : ∀ x : R, a (algebraMap R A x) = b (algebraMap R B x))
    (x : A) (y : B) : tensorLift a b h (x ⊗ₜ y) = a x * b y := by
  letI : Algebra R T := (a.comp (algebraMap R A)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ x y

theorem exists_common {ι A : Type} [Finite ι] [CommRing A] {R : ι → Type} [∀ i, CommRing (R i)]
    (φ : ∀ i, A →+* R i) (hs : ∀ i, Function.Surjective (φ i)) (q : ι → A) (hq : ∀ i, φ i (q i) = 0)
    (hc : Pairwise (Function.onFun IsCoprime q)) (z : ∀ i, R i) : ∃ f : A, ∀ i, φ i f = z i := by
  choose x hx using fun i => hs i (z i)
  have hcop : Pairwise (Function.onFun IsCoprime fun i => Ideal.span {q i}) := by
    intro i i' hne
    simp only [Function.onFun]
    rw [Ideal.isCoprime_span_singleton_iff]
    exact hc hne
  obtain ⟨f, hf⟩ := Ideal.exists_forall_sub_mem_ideal hcop x
  refine ⟨f, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hf i)
  rw [← hx i, ← sub_eq_zero, ← map_sub, hd, map_mul, hq, zero_mul]

theorem aeval_intertwine {K : Type} [Field K] {n : ℕ} (B C H : Matrix (Fin n) (Fin n) K) (h : B * H = H * C)
    (p : K[X]) : aeval B p * H = H * aeval C p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial d a =>
    have hpow : B ^ d * H = H * C ^ d := by
      induction d with
      | zero => simp
      | succ d ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mul,
      Matrix.mul_smul, hpow]

theorem tmul_split {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (a : A) (y : B) :
    (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] y) = a ⊗ₜ[R] y := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {k : Type} [CommRing k] [Algebra (maximalRealSubfield E) k]
  {K : Type} [Field K] [Algebra E K]

def phi (j : K ≃+* k ⊗[maximalRealSubfield E] E) {r : ℕ} (Q : SelfRecip E r) :
    K[X] →+* k ⊗[maximalRealSubfield E] Fld Q :=
  eval₂RingHom ((inclBase Q k).toRingHom.comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q)

section
variable (j : K ≃+* k ⊗[maximalRealSubfield E] E) {r : ℕ} (Q : SelfRecip E r)

theorem phi_C (x : K) : phi j Q (C x) = inclBase Q k (j x) := eval₂_C _ _

theorem phi_X : phi j Q X = (1 : k) ⊗ₜ alpha Q := eval₂_X _ _

variable (hj1 : ∀ e : E, j (algebraMap E K e) = (1 : k) ⊗ₜ e)
include hj1

theorem phi_map (p : E[X]) : phi j Q (p.map (algebraMap E K)) = (1 : k) ⊗ₜ (AdjoinRoot.mk Q.1 p : Fld Q) := by
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have e : ((inclBase Q k).toRingHom.comp j.toRingHom).comp (algebraMap E K) = g.comp (algebraMap E (Fld Q)) :=
    RingHom.ext fun e => by
      change inclBase Q k (j (algebraMap E K e)) = _
      rw [hj1]
      simp [inclBase, g]
  change eval₂ ((inclBase Q k).toRingHom.comp j.toRingHom) ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E K)) = _
  rw [eval₂_map, e]
  refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
  change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
  rw [← aeval_def]
  congr 1
  exact AdjoinRoot.aeval_eq p

theorem phi_surjective : Function.Surjective (phi j Q) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩
  | tmul a y =>
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    refine ⟨C (j.symm (a ⊗ₜ 1)) * p.map (algebraMap E K), ?_⟩
    rw [map_mul, phi_C, phi_map j Q hj1, RingEquiv.apply_symm_apply]
    have h1 : inclBase Q k (a ⊗ₜ (1 : E)) = a ⊗ₜ[maximalRealSubfield E] (1 : Fld Q) := by simp [inclBase]
    rw [h1]
    exact tmul_split a _

omit hj1 in
theorem eval₂_root_map : eval₂ ((AdjoinRoot.of (Q.1.map (algebraMap E K))).comp (algebraMap E K))
    (AdjoinRoot.root (Q.1.map (algebraMap E K))) Q.1 = 0 := by
  have h := AdjoinRoot.eval₂_root (Q.1.map (algebraMap E K))
  rwa [eval₂_map] at h


omit hj1 in
def psiB : Fld Q →+* AdjoinRoot (Q.1.map (algebraMap E K)) :=
  AdjoinRoot.lift ((AdjoinRoot.of (Q.1.map (algebraMap E K))).comp (algebraMap E K))
    (AdjoinRoot.root (Q.1.map (algebraMap E K))) (eval₂_root_map Q)

omit hj1 in
theorem psiB_algebraMap (e : E) : psiB (K := K) Q (algebraMap E (Fld Q) e) = AdjoinRoot.of _ (algebraMap E K e) :=
  AdjoinRoot.lift_of (eval₂_root_map Q)

omit hj1 in
theorem psiB_alpha : psiB (K := K) Q (alpha Q) = AdjoinRoot.root _ :=
  AdjoinRoot.lift_root (eval₂_root_map Q)

def psi : k ⊗[maximalRealSubfield E] Fld Q →+* AdjoinRoot (Q.1.map (algebraMap E K)) :=
  tensorLift
    ((AdjoinRoot.of (Q.1.map (algebraMap E K))).comp
      (j.symm.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom : k →+* k ⊗[maximalRealSubfield E] E)))
    (psiB Q)
    (fun x => by
      have h1 : (algebraMap (maximalRealSubfield E) k x) ⊗ₜ[maximalRealSubfield E] (1 : E) =
          (1 : k) ⊗ₜ algebraMap (maximalRealSubfield E) E x := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      have h2 : j.symm ((1 : k) ⊗ₜ algebraMap (maximalRealSubfield E) E x) =
          algebraMap E K (algebraMap (maximalRealSubfield E) E x) := by
        rw [RingEquiv.symm_apply_eq, hj1]
      have h3 : algebraMap (maximalRealSubfield E) (Fld Q) x =
          algebraMap E (Fld Q) (algebraMap (maximalRealSubfield E) E x) := rfl
      change AdjoinRoot.of _ (j.symm ((algebraMap (maximalRealSubfield E) k x) ⊗ₜ 1)) = psiB Q _
      rw [h1, h2, h3, psiB_algebraMap])

theorem psi_tmul (a : k) (y : Fld Q) : psi j Q hj1 (a ⊗ₜ[maximalRealSubfield E] y) =
    AdjoinRoot.of _ (j.symm (a ⊗ₜ 1)) * psiB Q y :=
  tensorLift_tmul _ _ _ a y

theorem psi_inclBase (y : k ⊗[maximalRealSubfield E] E) :
    psi j Q hj1 (inclBase Q k y) = AdjoinRoot.of _ (j.symm y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    have h0 : inclBase Q k (a ⊗ₜ e) = a ⊗ₜ[maximalRealSubfield E] algebraMap E (Fld Q) e := by
      simp [inclBase]
    have h2 : j.symm ((1 : k) ⊗ₜ e) = algebraMap E K e := by rw [RingEquiv.symm_apply_eq, hj1]
    have h3 : j.symm (a ⊗ₜ e) = j.symm (a ⊗ₜ 1) * j.symm ((1 : k) ⊗ₜ e) := by
      rw [← map_mul, tmul_split]
    rw [h0, psi_tmul, psiB_algebraMap, h3, map_mul, h2]

theorem psi_phi (g : K[X]) : psi j Q hj1 (phi j Q g) = AdjoinRoot.mk _ g := by
  have : (psi j Q hj1).comp (phi j Q) = AdjoinRoot.mk (Q.1.map (algebraMap E K)) := by
    refine Polynomial.ringHom_ext (fun x => ?_) ?_
    · rw [RingHom.comp_apply, phi_C, psi_inclBase, RingEquiv.symm_apply_apply]
      rfl
    · rw [RingHom.comp_apply, phi_X, psi_tmul, psiB_alpha]
      have h2 : j.symm ((1 : k) ⊗ₜ[maximalRealSubfield E] (1 : E)) = 1 := by
        rw [RingEquiv.symm_apply_eq, map_one]; rfl
      rw [h2, map_one, one_mul]
      exact AdjoinRoot.mk_X.symm
  exact DFunLike.congr_fun this g

theorem dvd_of_phi_eq_zero {g : K[X]} (h : phi j Q g = 0) : Q.1.map (algebraMap E K) ∣ g := by
  have := psi_phi j Q hj1 g
  rw [h, map_zero] at this
  exact AdjoinRoot.mk_eq_zero.1 this.symm


omit hj1 in
theorem involBase_phi (cK : K →+* K)
    (hj2 : ∀ x, j (cK x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k)
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x))
    (R : K[X]) (hR : phi j Q R = (1 : k) ⊗ₜ (alpha Q)⁻¹) (f : K[X]) :
    involBase Q k (phi j Q f) = phi j Q ((f.map cK).comp R) := by
  let ι : K →+* k ⊗[maximalRealSubfield E] Fld Q := (inclBase Q k).toRingHom.comp j.toRingHom
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q := (involBase Q k).toRingHom
  have hιc : ∀ y, involBase Q k (ι y) = ι (cK y) := by
    intro y
    change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cK y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have e1 : ib.comp ι = ι.comp cK := RingHom.ext fun y => hιc y
  have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    change (1 : k) ⊗ₜ invol Q (alpha Q) = _
    rw [invol_alpha]
  change ib (eval₂ ι _ f) = eval₂ ι _ _
  rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
  exact congrArg (fun x => eval₂ (ι.comp cK) x f) hR.symm

end

theorem aeval_map_mat' {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (p : E[X]) :
    aeval (M.map (algebraMap E K)) (p.map (algebraMap E K)) = (aeval M p).map (algebraMap E K) := by
  rw [aeval_map_algebraMap]
  have := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E K)) M p
  have e : (⇑(Algebra.ofId E K) : E → _) = algebraMap E _ := rfl
  simpa [AlgHom.mapMatrix_apply, e] using this

theorem final_calc {K : Type} [Field K] {n : ℕ} (A H' : Matrix (Fin n) (Fin n) K) (cK : K →+* K) (f m R : K[X])
    (T : Matrix (Fin n) (Fin n) K) (hint : cT cK A * H' = H' * aeval A R)
    (hkey : aeval A ((f.map cK).comp R) * aeval A m * aeval A f = T) :
    H' * T = cT cK (aeval A f) * (H' * aeval A m) * aeval A f := by
  have e := aeval_intertwine _ _ _ hint (f.map cK)
  rw [← aeval_comp] at e
  rw [← hkey, GlobalTheory.NormInert.cT_aeval, ← Matrix.mul_assoc (aeval (cT cK A) _) H', e]
  simp only [Matrix.mul_assoc]

theorem assembly (j : K ≃+* k ⊗[maximalRealSubfield E] E) (hj1 : ∀ e : E, j (algebraMap E K e) = (1 : k) ⊗ₜ e)
    (cK : K →+* K)
    (hj2 : ∀ x, j (cK x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) k)
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x))
    {n : ℕ} (γ₀ : GL (Fin n) E) (hell : γ₀.val.charpoly ∈ Ell E n) (H₀ : Matrix (Fin n) (Fin n) E)
    (hinv : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (m : K[X]) (t : E[X])
    (hz : ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly →
      ∃ z : (k ⊗[maximalRealSubfield E] Fld Q)ˣ,
        phi j Q m * ((z : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k (z : k ⊗[maximalRealSubfield E] Fld Q)) =
          phi j Q (t.map (algebraMap E K))) :
    ∃ c : GL (Fin n) K, c.val * (γ₀.val.map (algebraMap E K)) = (γ₀.val.map (algebraMap E K)) * c.val ∧
      (H₀ * aeval γ₀.val t).map (algebraMap E K) =
        cT cK c.val * ((H₀.map (algebraMap E K)) * aeval (γ₀.val.map (algebraMap E K)) m) * c.val := by
  have hcK : ∀ e : E, cK (algebraMap E K e) = algebraMap E K (IsCMField.complexConj E e) := by
    intro e
    apply j.injective
    rw [hj2, hj1, hj1]
    simp
  set P := γ₀.val.charpoly with hPdef
  have hPsep : P.Separable := hell.2.2.1
  have hP0 : P ≠ 0 := hell.1.ne_zero
  have hself : ∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ P → IsSelfRecip E Q.natDegree Q :=
    GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n P hell
  have hXP : IsCoprime X P := by
    rw [Polynomial.irreducible_X.coprime_iff_not_dvd]
    intro hX
    exact (hself X monic_X irreducible_X hX).2.2.2.1 (by simp)
  obtain ⟨a, b, hab⟩ := hXP
  set S := (UniqueFactorizationMonoid.normalizedFactors P).toFinset with hS
  have hmem : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q ∧ Q ∣ P := by
    intro Q hQ
    rw [hS, Multiset.mem_toFinset] at hQ
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
    refine ⟨?_, hirr, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ⟩
    have hn := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
    rw [← hn]; exact Polynomial.monic_normalize hirr.ne_zero
  have hcopS : (S : Set E[X]).Pairwise (Function.onFun IsCoprime fun Q : E[X] => Q) := by
    intro Q hQ Q' hQ' hne
    simp only [Function.onFun]
    rw [(hmem Q hQ).2.1.coprime_iff_not_dvd]
    intro hd
    exact hne (eq_of_monic_of_associated (hmem Q hQ).1 (hmem Q' hQ').1
      ((hmem Q hQ).2.1.associated_of_dvd (hmem Q' hQ').2.1 hd))
  have hcopK : (S : Set E[X]).Pairwise (Function.onFun IsCoprime fun Q : E[X] => Q.map (algebraMap E K)) := by
    intro Q hQ Q' hQ' hne
    have := (hcopS hQ hQ' hne).map (mapRingHom (algebraMap E K))
    simpa [Function.onFun] using this
  have hassoc : Associated (∏ Q ∈ S, Q) P := by
    have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hPsep.squarefree
    rw [Finset.prod_eq_multiset_prod, hS, Multiset.toFinset_val, hnd.dedup, Multiset.map_id']
    exact UniqueFactorizationMonoid.prod_normalizedFactors hP0
  let Qs : ∀ Q : S, SelfRecip E Q.1.natDegree := fun Q =>
    ⟨Q.1, hself Q.1 (hmem Q.1 Q.2).1 (hmem Q.1 Q.2).2.1 (hmem Q.1 Q.2).2.2⟩
  have hQsP : ∀ Q : S, (Qs Q).1 ∣ P := fun Q => (hmem Q.1 Q.2).2.2
  choose z hzQ using fun Q : S => hz _ (Qs Q) (hQsP Q)
  have hcommon : ∀ y : ∀ Q : S, k ⊗[maximalRealSubfield E] Fld (Qs Q), ∃ f : K[X], ∀ Q : S, phi j (Qs Q) f = y Q := by
    intro y
    refine exists_common (fun Q : S => phi j (Qs Q)) (fun Q => phi_surjective j (Qs Q) hj1)
      (fun Q : S => Q.1.map (algebraMap E K)) (fun Q => ?_) (fun Q Q' hne => ?_) y
    · have h0 : (AdjoinRoot.mk (Qs Q).1 (Qs Q).1 : Fld (Qs Q)) = 0 := AdjoinRoot.mk_self
      have := phi_map j (Qs Q) hj1 (Qs Q).1
      rw [h0] at this
      exact this.trans (TensorProduct.tmul_zero _ _)
    · exact hcopK Q.2 Q'.2 (fun h => hne (Subtype.ext h))
  set A : Matrix (Fin n) (Fin n) K := γ₀.val.map (algebraMap E K) with hA
  have hCH : aeval A (P.map (algebraMap E K)) = 0 := by
    rw [hPdef, hA, ← Matrix.charpoly_map]
    exact Matrix.aeval_self_charpoly _
  have hvan : ∀ h : K[X], (∀ Q : S, phi j (Qs Q) h = 0) → aeval A h = 0 := by
    intro h hh
    have h1 : (∏ Q ∈ S, Q.map (algebraMap E K)) ∣ h :=
      Finset.prod_dvd_of_coprime hcopK fun Q hQ => dvd_of_phi_eq_zero j (Qs ⟨Q, hQ⟩) hj1 (hh ⟨Q, hQ⟩)
    rw [← Polynomial.map_prod] at h1
    obtain ⟨d, hd⟩ := (Polynomial.map_dvd (algebraMap E K) hassoc.symm.dvd).trans h1
    rw [hd, map_mul, hCH, zero_mul]
  obtain ⟨f, hf⟩ := hcommon fun Q => (z Q : k ⊗[maximalRealSubfield E] Fld (Qs Q))
  obtain ⟨g, hg⟩ := hcommon fun Q => ((z Q)⁻¹ : (k ⊗[maximalRealSubfield E] Fld (Qs Q))ˣ)
  have hfg : aeval A f * aeval A g = 1 := by
    have := hvan (f * g - 1) fun Q => by
      rw [map_sub, map_mul, hf, hg, Units.mul_inv, map_one, sub_self]
    rw [map_sub, map_mul, map_one] at this
    exact sub_eq_zero.1 this
  have hgf : aeval A g * aeval A f = 1 := by rw [← map_mul, mul_comm, map_mul, hfg]
  set R : K[X] := a.map (algebraMap E K) with hRdef
  have hBA : aeval A R * A = 1 := by
    have := congrArg (fun p : E[X] => aeval A (p.map (algebraMap E K))) hab
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, map_add (f := _), map_mul, hCH, Polynomial.map_X, aeval_X,
      Polynomial.map_one, map_one, mul_zero, add_zero, zero_mul] at this
    exact this
  have hAB : A * aeval A R = 1 := by
    rw [show A * aeval A R = aeval A (X * R) by simp, mul_comm, map_mul, aeval_X, hBA]
  have hphiR : ∀ Q : S, phi j (Qs Q) R = (1 : k) ⊗ₜ (alpha (Qs Q))⁻¹ := by
    intro Q
    rw [hRdef, phi_map j (Qs Q) hj1]
    congr 1
    have := congrArg (AdjoinRoot.mk (Qs Q).1) hab
    rw [map_add (f := _), map_mul, map_mul, map_one, AdjoinRoot.mk_X, AdjoinRoot.mk_eq_zero.2 (hQsP Q), mul_zero, add_zero] at this
    exact eq_inv_of_mul_eq_one_left this
  set H' : Matrix (Fin n) (Fin n) K := H₀.map (algebraMap E K) with hH'
  have hcTmap : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val).map (algebraMap E K) = cT cK A := by
    ext x y
    simp [cT, hA, hcK]
  have hmap : cT cK A * H' * A = H' := by
    have := congrArg (Matrix.map · (algebraMap E K)) hinv
    simp only [Matrix.map_mul] at this
    rw [hcTmap] at this
    exact this
  have hint : cT cK A * H' = H' * aeval A R := by
    calc cT cK A * H' = cT cK A * H' * (A * aeval A R) := by rw [hAB, Matrix.mul_one]
      _ = H' * aeval A R := by rw [← Matrix.mul_assoc, hmap]
  have hkey : aeval A ((f.map cK).comp R * m * f - t.map (algebraMap E K)) = 0 := by
    refine hvan _ fun Q => ?_
    have h1 := involBase_phi j (Qs Q) cK hj2 R (hphiR Q) f
    rw [map_sub, map_mul, map_mul, ← h1, hf, ← hzQ Q]
    ring
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at hkey
  refine ⟨⟨aeval A f, aeval A g, hfg, hgf⟩, ?_, ?_⟩
  · change aeval A f * A = A * aeval A f
    rw [show A * aeval A f = aeval A (X * f) by simp,
      show aeval A f * A = aeval A (f * X) by simp, mul_comm]
  · change _ = cT cK (aeval A f) * (H' * aeval A m) * aeval A f
    rw [Matrix.map_mul, ← aeval_map_mat']
    exact final_calc A H' cK f m R _ hint hkey

section Concrete

end Concrete

end GlobalTheory.CompanionTheory.LocAssembly
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.FiniteRefSign
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace PositivityTheory.BCUSide.HermitianLocalForms.Lem

theorem ratio_poly : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (A H₀ H : Matrix (Fin n) (Fin n) K), IsUnit A.det → A.charpoly.Separable → H₀.det ≠ 0 → cT σ A * H₀ * A = H₀ → cT σ A * H * A = H → ∃ m : K[X], H = H₀ * aeval A m := GlobalTheory.T.hermitian_form_polynomial_in

theorem sign_rel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ (m : (w.adicCompletion E)[X]) (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → sgnOn (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) = ((GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) (Units.map (Algebra.norm (v.adicCompletion (maximalRealSubfield E)) : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q →* (v.adicCompletion (maximalRealSubfield E))) x) : ℤ) : ℂ) * sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) := GlobalTheory.T.local_hermitian_class_first

theorem exists_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := GlobalTheory.T.local_hermitian_class_second

theorem norms_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E)), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val → (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → x ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := GlobalTheory.T.local_hermitian_class_third

theorem exists_crt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X], ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := GlobalTheory.T.exists_polynomial_chinese_remainder

theorem herm_of_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) := GlobalTheory.T.involution_compatible_polynomial

theorem posDef_of_inf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ, (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q u.Completion (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : Fld Q)) → ∀ τ : E →+* ℂ, ∃ Q' : Matrix (Fin n) (Fin n) ℂ, Q'.det ≠ 0 ∧ (H₀ * aeval γ₀.val m).map τ = cT (starRingEnd ℂ) Q' * Q' := GlobalTheory.T.positive_hermitian_polynomial

theorem norm_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r) (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k → Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := GlobalTheory.T.norm_mem_norm_group

theorem finite_ref_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := GlobalTheory.T.finite_nonsplit_sign_places

theorem local_assembly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (t : E[X]), (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ z : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)ˣ, locPhi hU w hw v hv Q m * ((z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q (v.adicCompletion (maximalRealSubfield E)) (z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)) = locPhi hU w hw v hv Q (atPl w t)) → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val ∧ (H₀ * aeval γ₀.val t).map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) * c.val := by
  intro E _ _ _ hU w hw v hv n γ₀ hP H₀ _ _ h3 m t hz
  exact GlobalTheory.CompanionTheory.LocAssembly.assembly (locJ hU w hw v hv) (locJ_algebraMap hU w hw v hv) (cj w)
    (locJ_cj hU w hw v hv) γ₀ hP H₀ h3 m t hz

end PositivityTheory.BCUSide.HermitianLocalForms.Lem
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace PositivityTheory.BCUSide.HermitianLocalForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sgnOn_mul_self {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (Q : K[X]) (A : Matrix (Fin n) (Fin n) K) :
    sgnOn σ H Q A * sgnOn σ H Q A = 1 := by
  unfold sgnOn
  rw [← mul_zpow]
  norm_num


omit [IsCMField E] in
theorem sec_eq {S : Set (Pl E)} (hS : IsSection S) {w u : Pl E} (hw : w ∈ S) (hu : u ∈ S)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w := by
  obtain ⟨a, -, ha⟩ := hS w
  exact (ha u ⟨hu, h⟩).trans (ha w ⟨hw, rfl⟩).symm

theorem conv_norm {r : ℕ} (Q : SelfRecip E r) {θ : E} (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    {d : plus Q} (hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ)
    (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (a : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) (t : (plus Q)ˣ)
    (h : GlobalTheory.TraceClasses.IsValue (1 ⊗ₜ d) ((a : k ⊗[(maximalRealSubfield E)] plus Q) * (1 ⊗ₜ ((t : plus Q))⁻¹))) :
    ∃ z : (k ⊗[(maximalRealSubfield E)] Fld Q)ˣ, inclPlus Q k (a : k ⊗[(maximalRealSubfield E)] plus Q) *
      ((z : k ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q k (z : k ⊗[(maximalRealSubfield E)] Fld Q)) = (1 : k) ⊗ₜ (((t : plus Q) : Fld Q)) := by
  let T : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : plus Q →ₐ[(maximalRealSubfield E)] k ⊗[(maximalRealSubfield E)] plus Q).toMonoidHom t
  have hT : ((T⁻¹ : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ) : k ⊗[(maximalRealSubfield E)] plus Q) = 1 ⊗ₜ ((t : plus Q))⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]; rfl
  have hmem : a * T⁻¹ ∈ norms Q k := by
    rw [GlobalTheory.TraceClasses.mem_norms_iff Q hθ0 hθ k hd, Units.val_mul, hT]
    exact h
  obtain ⟨c, hc⟩ := hmem
  have hc' : normHom Q k c = Units.map (inclPlus Q k).toMonoidHom (a * T⁻¹) := hc
  refine ⟨c⁻¹, ?_⟩
  have h4 : (c⁻¹ : (k ⊗[(maximalRealSubfield E)] Fld Q)ˣ).val * involBase Q k (c⁻¹ : (k ⊗[(maximalRealSubfield E)] Fld Q)ˣ).val =
      (normHom Q k c⁻¹ : k ⊗[(maximalRealSubfield E)] Fld Q) := rfl
  have h5 : normHom Q k c⁻¹ = (Units.map (inclPlus Q k).toMonoidHom a)⁻¹ *
      Units.map (inclPlus Q k).toMonoidHom T := by
    rw [map_inv, hc', map_mul, map_inv, mul_inv, inv_inv]
  rw [h4, h5]
  have h6 : inclPlus Q k (a : k ⊗[(maximalRealSubfield E)] plus Q) = (Units.map (inclPlus Q k).toMonoidHom a : k ⊗[(maximalRealSubfield E)] Fld Q) := rfl
  rw [h6, ← Units.val_mul, mul_inv_cancel_left]
  simp [T, inclPlus]

theorem factor_alt (hU : Unr E) {S : Set (Pl E)} (hS : IsSection S) {n : ℕ} {γ₀ : GL (Fin n) E}
    (hP : γ₀.val.charpoly ∈ Ell E n) {H₀ : Matrix (Fin n) (Fin n) E} (h1 : IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀) (h2 : H₀.det ≠ 0)
    (h3 : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (hpos : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q)
    (hsg0 : ∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1)
    {H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    (hH : ∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = H w)
    (hae : ∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val ∧ H w = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)
    (hsg : ∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1)
    (mw : ∀ w : Pl E, (w.adicCompletion E)[X]) (hmw : ∀ w, ¬ IsSplitAt w → H w = (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) (mw w))
    (wv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → Pl E) (hwvS : ∀ v, wv v ∈ S) (hwv : ∀ v, (wv v).under (𝓞 (maximalRealSubfield E)) = v)
    {r : ℕ} (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly) :
    ∃ t : (plus Q)ˣ,
      (∀ v (hw : ¬ IsSplitAt (wv v)), ∃ z : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)ˣ,
        locPhi hU (wv v) hw v (hwv v) Q (mw (wv v)) * ((z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q _ (z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)) =
          (1 : (v.adicCompletion (maximalRealSubfield E))) ⊗ₜ (((t : plus Q) : Fld Q))) ∧
      ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ,
        (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q _ (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (((t : plus Q) : Fld Q)) := by
  classical

  have hx : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ,
      (∀ hw : ¬ IsSplitAt (wv v), inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) =
        locPhi hU (wv v) hw v (hwv v) Q (mw (wv v))) ∧ (IsSplitAt (wv v) → x = 1) := by
    intro v
    by_cases hs : IsSplitAt (wv v)
    · exact ⟨1, fun h => absurd hs h, fun _ => rfl⟩
    · have hHw := hH (wv v) hs
      rw [hmw _ hs] at hHw
      obtain ⟨x, hx⟩ := Lem.exists_plus E hU (wv v) hs v (hwv v) n γ₀ hP H₀ h1 h2 h3 (mw (wv v)) hHw.1 hHw.2.1 r Q hQ
      exact ⟨x, fun _ => hx, fun h => absurd h hs⟩
  choose x hx1 hx2 using hx

  have hB := Filter.eventually_cofinite.1 hae
  set B := {w : Pl E | ¬ (¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val ∧
    H w = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val)} with hBdef
  set BV := (fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))) '' B with hBV
  have hBVf : BV.Finite := hB.image _
  have hgood : ∀ v, v ∉ BV → x v ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := by
    intro v hv
    by_cases hs : IsSplitAt (wv v)
    · rw [hx2 v hs]; exact one_mem _
    · have hnB : wv v ∉ B := fun h => hv ⟨wv v, h, hwv v⟩
      simp only [hBdef, Set.mem_ofPred_eq, not_not] at hnB
      obtain ⟨c, hc1, hc2⟩ := hnB hs
      rw [hmw _ hs] at hc2
      exact Lem.norms_of_conj E hU (wv v) hs v (hwv v) n γ₀ hP H₀ h1 h2 h3 (mw (wv v)) c hc1 hc2 r Q hQ (x v) (hx1 v hs)
  set X : GlobalTheory.QuadSymbol.FinFam (maximalRealSubfield E) := fun v => Units.map (Algebra.norm (v.adicCompletion (maximalRealSubfield E)) : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q →* (v.adicCompletion (maximalRealSubfield E))) (x v)
    with hXdef
  have hXn : ∀ v, v ∉ BV → X v ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) := fun v hv =>
    Lem.norm_mem E (v.adicCompletion (maximalRealSubfield E)) r Q (x v) (hgood v hv)
  have hA : GlobalTheory.QuadSymbol.AlmostNorm (maximalRealSubfield E) E X := hBVf.subset fun v hv => by
    by_contra h
    exact hv (hXn v h)

  set R : Pl E → ℂ := fun w => if IsSplitAt w then 1 else
    sgnOn (cj w) (H w) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) with hRdef
  have hXR : ∀ v, ((GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) (X v) : ℤ) : ℂ) = R (wv v) := by
    intro v
    by_cases hs : IsSplitAt (wv v)
    · have h1' : X v = 1 := by simp [hXdef, hx2 v hs]
      rw [h1', (GlobalTheory.QuadSymbol.eta_eq_one_iff).2 (one_mem _)]
      simp [hRdef, if_pos hs]
    · have key := Lem.sign_rel E hU (wv v) hs v (hwv v) n γ₀ hP H₀ h1 h2 h3 hpos (mw (wv v)) r Q hQ (x v) (hx1 v hs)
      rw [← hmw _ hs] at key
      simp only [hRdef, if_neg hs]
      rw [key, mul_assoc, sgnOn_mul_self, mul_one]

  have hwvw : ∀ w ∈ S, wv (w.under (𝓞 (maximalRealSubfield E))) = w := fun w hw => sec_eq hS hw (hwvS _) (hwv _)
  let cz : ℤˣ →* ℂ := (Int.castRingHom ℂ).toMonoidHom.comp (Units.coeHom ℤ)
  have hcz : ∀ a : ℤˣ, cz a = ((a : ℤ) : ℂ) := fun a => rfl
  have hRS : ∀ w ∈ S, R w ≠ 1 → w.under (𝓞 (maximalRealSubfield E)) ∈ BV := by
    intro w hw hR
    by_contra hv
    apply hR
    rw [← hwvw w hw, ← hXR, (GlobalTheory.QuadSymbol.eta_eq_one_iff).2 (hXn _ hv)]
    simp
  set Af : Pl E → ℂ := fun w => if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) with hAf
  set Bf : Pl E → ℂ := fun w => if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) with hBf
  have hRAB : ∀ w, R w = Af w * Bf w := fun w => by
    simp only [hRdef, hAf, hBf]
    split_ifs <;> simp
  have hBB : ∀ w, Bf w * Bf w = 1 := fun w => by
    simp only [hBf]
    split_ifs
    · simp
    · exact sgnOn_mul_self _ _ _ _
  have hBfin : (S ∩ Function.mulSupport Bf).Finite :=
    (Lem.finite_ref_sign E hU n γ₀ H₀ h1 h2 hpos Q.1).subset fun w hw => by
      obtain ⟨-, hw⟩ := hw
      simp only [Function.mem_mulSupport, hBf] at hw
      split_ifs at hw with hs
      · exact absurd rfl hw
      · exact ⟨hs, hw⟩
  have hRfin : (S ∩ Function.mulSupport R).Finite := by
    refine Set.Finite.of_finite_image (f := fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))) (hBVf.subset ?_)
      ((GlobalTheory.TotPosSign.bijOn_under hS).injOn.mono Set.inter_subset_left)
    rintro _ ⟨w, ⟨hw, hR⟩, rfl⟩
    exact hRS w hw hR
  have hAfin : (S ∩ Function.mulSupport Af).Finite := by
    refine (hRfin.union hBfin).subset fun w ⟨hw, hA⟩ => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_inter_iff, Function.mem_mulSupport, not_or, not_and, not_not] at h
    apply hA
    have e1 := hRAB w
    rw [h.1 hw, h.2 hw, mul_one] at e1
    exact e1.symm
  have hprodS : ∏ᶠ w ∈ S, R w = 1 := by
    rw [finprod_mem_congr rfl fun w _ => hRAB w, finprod_mem_mul_distrib' hAfin hBfin,
      hsg Q.1 Q.2.1 hQ, hsg0 Q.1 Q.2.1 hQ, one_mul]
  have hprod : GlobalTheory.QuadSymbol.etaProd (maximalRealSubfield E) E X 1 = 1 := by
    unfold GlobalTheory.QuadSymbol.etaProd
    have hinf : ∏ u : InfinitePlace (maximalRealSubfield E), GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E u.Completion
        ((1 : GlobalTheory.QuadSymbol.InfFam (maximalRealSubfield E)) u) = 1 :=
      Finset.prod_eq_one fun u _ => (GlobalTheory.QuadSymbol.eta_eq_one_iff).2 (one_mem _)
    rw [hinf, mul_one]
    have hinj : Function.Injective cz := fun a b h => by
      rw [hcz, hcz] at h
      exact Units.ext (by exact_mod_cast h)
    apply hinj
    rw [MonoidHom.map_finprod _ (GlobalTheory.QuadSymbol.AlmostNorm.finite_mulSupport hA), map_one, ← hprodS,
      finprod_mem_eq_of_bijOn _ (GlobalTheory.TotPosSign.bijOn_under hS)
        (g := fun v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) => R (wv v)) (fun w hw => by rw [hwvw w hw]),
      finprod_mem_univ]
    exact finprod_congr fun v => hXR v

  obtain ⟨δ, hδ⟩ := GlobalTheory.QuadSymbol.exists_everywhereNorm_div_of_etaProd_eq_one (maximalRealSubfield E) E X 1 hA hprod
  obtain ⟨θ, hθ0, hθ⟩ : ∃ θ : E, θ ≠ 0 ∧ IsCMField.complexConj E θ = -θ := by
    obtain ⟨a, ha⟩ : ∃ a : E, IsCMField.complexConj E a ≠ a := by
      by_contra h
      push Not at h
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
    exact ⟨a - IsCMField.complexConj E a, sub_ne_zero.mpr ha.symm, by simp⟩
  obtain ⟨e, e0, e1⟩ := GlobalTheory.TraceClasses.exists_basis_theta Q hθ0 hθ
  let d : plus Q := ⟨algebraMap E _ θ * algebraMap E _ θ, by
    show invol Q _ = (AlgHom.id _ _) _
    rw [map_mul, GlobalTheory.TraceClasses.invol_theta Q hθ]
    simp⟩
  have hd : (d : Fld Q) = algebraMap E _ θ * algebraMap E _ θ := rfl
  have := GlobalTheory.TraceClasses.isQuadraticExtension Q hθ0 hθ
  have e2 : e 1 * e 1 = algebraMap _ _ d := by rw [e1]; exact hd.symm
  have hadj := GlobalTheory.TraceClasses.adjoin_eq_top Q hθ0 hθ
  have hxfin : {v | ¬ GlobalTheory.TraceClasses.IsValue (1 ⊗ₜ d) (x v : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)}.Finite :=
    hBVf.subset fun v hv => by
      by_contra h
      exact hv ((GlobalTheory.TraceClasses.mem_norms_iff Q hθ0 hθ _ hd (x v)).1 (hgood v h))
  obtain ⟨t, htf, hti⟩ := GlobalTheory.TraceClasses.exists_global e e0 e2 hadj x 1 hxfin δ
    (fun v => hδ.1 v) (fun u => by simpa [GlobalTheory.QuadSymbol.infDiag] using hδ.2 u)
  refine ⟨t, fun v hw => ?_, fun u => ?_⟩
  · obtain ⟨z, hz⟩ := conv_norm Q hθ0 hθ hd _ (x v) t (htf v)
    exact ⟨z, by rw [← hx1 v hw]; exact hz⟩
  · obtain ⟨z, hz⟩ := conv_norm Q hθ0 hθ hd u.Completion 1 t (by simpa using hti u)
    refine ⟨z, ?_⟩
    simpa using hz

theorem transport (hU : Unr E) {w w' : Pl E} (e : w' = w) (hw : ¬ IsSplitAt w) (hw' : ¬ IsSplitAt w')
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} (hv : w.under (𝓞 (maximalRealSubfield E)) = v) (hv' : w'.under (𝓞 (maximalRealSubfield E)) = v)
    (mw : ∀ w : Pl E, (w.adicCompletion E)[X]) {r : ℕ} (Q : SelfRecip E r) (y : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)
    (h : ∃ z : (v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)ˣ, locPhi hU w' hw' v hv' Q (mw w') *
      ((z : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q _ (z : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)) = y) :
    ∃ z : (v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)ˣ, locPhi hU w hw v hv Q (mw w) *
      ((z : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q _ (z : v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] Fld Q)) = y := by
  subst e
  exact h

end PositivityTheory.BCUSide.HermitianLocalForms


open PositivityTheory.BCUSide.HermitianLocalForms in
theorem PositivityTheory.BCUSide.L.hermitian_form_local_global : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H w = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := by
  intro E _ _ _ hU S hS n γ₀ hP H₀ h1 h2 h3 hpos hsg0 H hH hae hsg
  classical

  have hm : ∀ w : Pl E, ∃ m : (w.adicCompletion E)[X], ¬ IsSplitAt w → H w = (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m := by
    intro w
    by_cases hs : IsSplitAt w
    · exact ⟨0, fun h => absurd hs h⟩
    · have hAdet : IsUnit (γ₀.val.map (algebraMap E (w.adicCompletion E))).det := by
        have e : (γ₀.val.map (algebraMap E (w.adicCompletion E))).det = algebraMap E _ γ₀.val.det :=
          (RingHom.map_det _ _).symm
        rw [e]
        exact (γ₀.isUnit.map Matrix.detMonoidHom).map _
      have hAsep : (γ₀.val.map (algebraMap E (w.adicCompletion E))).charpoly.Separable := by
        rw [Matrix.charpoly_map]; exact hP.2.2.1.map
      have hH0 : (H₀.map (algebraMap E (w.adicCompletion E))).det ≠ 0 := by
        have e : (H₀.map (algebraMap E (w.adicCompletion E))).det = algebraMap E _ H₀.det :=
          (RingHom.map_det _ _).symm
        rw [e]; exact (_root_.map_ne_zero _).2 h2
      have hinv0 : cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * (H₀.map (algebraMap E (w.adicCompletion E))) * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (H₀.map (algebraMap E (w.adicCompletion E))) := by
        have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h3
        simp only [Matrix.map_mul, cT_map hU w hs] at this
        exact this
      obtain ⟨m, hm⟩ := Lem.ratio_poly _ (cj w) n _ _ (H w) hAdet hAsep hH0 hinv0 (hH w hs).2.2
      exact ⟨m, fun _ => hm⟩
  choose mw hmw using hm

  have hsurj : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w, w ∈ S ∧ w.under (𝓞 (maximalRealSubfield E)) = v := fun v =>
    (GlobalTheory.TotPosSign.bijOn_under hS).surjOn (Set.mem_univ v)
  choose wv hwvS hwv using hsurj

  have ht := fun (r : ℕ) (Q : SelfRecip E r) (hQ : Q.1 ∣ γ₀.val.charpoly) =>
    factor_alt hU hS hP h1 h2 h3 hpos hsg0 hH hae hsg mw hmw wv hwvS hwv Q hQ
  choose! tt htt1 htt2 using ht
  obtain ⟨m, hmQ⟩ := Lem.exists_crt E n γ₀ hP (fun r Q => (((tt r Q : (plus Q)ˣ) : plus Q) : Fld Q))
  have hplus : ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly →
      invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q) := fun r Q hQ => by
    rw [hmQ r Q hQ]
    exact GlobalTheory.TraceClasses.invol_coe Q _
  refine ⟨H₀ * aeval γ₀.val m, Lem.herm_of_plus E n γ₀ hP H₀ h1 h2 h3 m hplus, ?_, ?_, ?_⟩
  ·
    have hc : aeval γ₀.val m * γ₀.val = γ₀.val * aeval γ₀.val m := by
      have := congrArg (aeval γ₀.val) (mul_comm m X)
      simpa only [map_mul, aeval_X] using this
    calc cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * (H₀ * aeval γ₀.val m) * γ₀.val
        = cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * (aeval γ₀.val m * γ₀.val) := by simp only [Matrix.mul_assoc]
      _ = cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val * aeval γ₀.val m := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = H₀ * aeval γ₀.val m := by rw [h3]
  ·
    refine Lem.posDef_of_inf E n γ₀ hP H₀ h1 h2 h3 hpos m hplus fun r Q hQ u => ?_
    obtain ⟨z, hz⟩ := htt2 r Q hQ u
    exact ⟨z, by rw [hmQ r Q hQ]; exact hz⟩
  ·
    intro w hw
    have hwS := mem_S hS hw
    have e : wv (w.under (𝓞 (maximalRealSubfield E))) = w := sec_eq hS hwS (hwvS _) (hwv _)
    obtain ⟨c, hc1, hc2⟩ := Lem.local_assembly E hU w hw (w.under (𝓞 (maximalRealSubfield E))) rfl n γ₀ hP H₀ h1 h2 h3 (mw w) m
      fun r Q hQ => by
        rw [locPhi_atPl, hmQ r Q hQ]
        have hw' : ¬ IsSplitAt (wv (w.under (𝓞 (maximalRealSubfield E)))) := by rw [e]; exact hw
        exact transport hU e hw hw' rfl (hwv _) mw Q _ (htt1 r Q hQ (w.under (𝓞 (maximalRealSubfield E))) hw')
    exact ⟨c, hc1, by rw [hc2, ← hmw w hw]⟩
