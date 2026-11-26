module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwistedDualRhoO

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.msetSep :
    ∀ m m' : Multiset ℂ, (∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) → m = m' :=
  _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.CohTransport
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.cohTransport :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ Ξ' : AlgRep E a) (T : (Fin Ξ.d → ℂ) ≃ₗ[ℂ] (Fin Ξ'.d → ℂ)),
      IsAlgIso Ξ Ξ' T → IsCohFor π Ξ → IsCohFor π Ξ' := by
  rintro E _ _ _ a π Ξ Ξ' T ⟨h1, h2⟩ H
  refine GlobalTheory.ConjCoh.hasCohomology_transport (σ := LinearMap.id) (s := id)
    (LinearEquiv.lTensor π.V T) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun k m => ?_) (fun X m => ?_) H
  · induction m using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v =>
      change π.op (.cpt k) φ ⊗ₜ[ℂ] T (Ξ.mat (Unitary.toUnits k) *ᵥ v) =
        π.op (.cpt k) φ ⊗ₜ[ℂ] (Ξ'.mat (Unitary.toUnits k) *ᵥ T v)
      rw [h1]
  · induction m using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v =>
      rw [GlobalTheory.GKCoh.tensorLie_tmul, map_add (f := _)]
      change π.op (.lie (toL X.1)) φ ⊗ₜ[ℂ] T v + φ ⊗ₜ[ℂ] T (Ξ.dmat (toL X.1) *ᵥ v) =
        π.op (.lie (toL X.1)) φ ⊗ₜ[ℂ] T v + φ ⊗ₜ[ℂ] (Ξ'.dmat (toL X.1) *ᵥ T v)
      rw [h2]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.SLApply
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible

open GlobalTheory.WignerGL

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {A : Type} [Ring A] [Algebra ℂ A] [Module ℝ A]


omit [Algebra ℂ A] in
private noncomputable def sL (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) : Cinf E →ₗ[ℝ] A where
  toFun x := L (toL (Matrix.single i j x))
  map_add' x y := by
    have h : toL (Matrix.single i j (x + y)) = toL (Matrix.single i j x) + toL (Matrix.single i j y) :=
      congrArg toL (Matrix.single_add i j x y)
    exact (congrArg L h).trans (L.map_add _ _)
  map_smul' c x := by
    have h : toL (Matrix.single i j (c • x)) = c • toL (Matrix.single i j x) :=
      congrArg toL (Matrix.smul_single c i j x).symm
    exact (congrArg L h).trans (L.map_smul _ _)

omit [Algebra ℂ A] in
private theorem sL_apply (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) (x : Cinf E) :
    sL L i j x = L (toL (Matrix.single i j x)) := rfl

omit [Algebra ℂ A] in
private theorem sL_comm (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) (i j k l : Fin a) (x y : Cinf E) :
    sL L i j x * sL L k l y - sL L k l y * sL L i j x =
      (if j = k then sL L i l (x * y) else 0) - (if l = i then sL L k j (x * y) else 0) := by
  have h := hL (Matrix.single i j x) (Matrix.single k l y)
  have e : ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), toL (X - Y) = toL X - toL Y := fun _ _ => rfl
  rw [e, map_sub] at h
  simp only [sL_apply]
  rw [h]
  have z : L (toL 0) = 0 := map_zero _
  congr 1
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, mul_comm y]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]

private theorem eL_comm_aux (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    eL L τ i j * eL L τ' k l - eL L τ' k l * eL L τ i j =
      (if j = k then (1 / 4 : ℂ) • (sL L i l (atEmb τ 1 * atEmb τ' 1) - sL L i l (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L i l (atEmb τ 1 * atEmb τ' .I) + sL L i l (atEmb τ .I * atEmb τ' 1))) else 0) -
      (if l = i then (1 / 4 : ℂ) • (sL L k j (atEmb τ 1 * atEmb τ' 1) - sL L k j (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L k j (atEmb τ 1 * atEmb τ' .I) + sL L k j (atEmb τ .I * atEmb τ' 1))) else 0) := by
  have h1 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' 1)
  have h2 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' .I)
  have h3 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' 1)
  have h4 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' .I)
  simp only [eL, ← sL_apply, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 - (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>
    match_scalars <;> ring_nf <;> simp

end

end UpperTheory.V.AlgRepEndIrreducible

open GlobalTheory.WignerGL in
theorem UpperTheory.V.AlgRepEndIrreducible.eLRel :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Module ℝ A] [IsScalarTower ℝ ℂ A] (L : Lie E a →ₗ[ℝ] A),
      IsLieHom L → IsMultiGl (eL L) := by
  intro E _ _ _ a A _ _ _ _ L hL
  refine ⟨fun τ i j k l => ?_, fun τ τ' h i j k l => ?_⟩
  · have e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1 := by
      rw [atEmb_eq]; simp
    rw [eL_comm_aux L hL]
    simp only [atEmb_mul, one_mul, mul_one, e, map_neg, eL, ← sL_apply]
    congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)
  · rw [← sub_eq_zero, eL_comm_aux L hL]
    by_cases hw : InfinitePlace.mk τ = InfinitePlace.mk τ'
    · obtain rfl : ComplexEmbedding.conjugate τ = τ' := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
      have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
        rw [atEmb_eq]; simp
      have e' : atEmb τ (-1) = -atEmb τ 1 := by
        rw [atEmb_eq]; simp
      simp [atEmb_conj, atEmb_mul, e, e']
    · simp [atEmb_mul_of_ne hw]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ActOpApply
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private noncomputable def actAlg (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private noncomputable def actOp (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (actAlg V d Nᵀ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.transpose_add]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

private theorem actOp_apply (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (N : Matrix (Fin d) (Fin d) ℂ) :
    actOp V d N = MulOpposite.op (actAlg V d Nᵀ) := rfl

set_option synthInstance.maxHeartbeats 100000 in
theorem UpperTheory.V.AlgRepEndIrreducible.tensB :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), IsLieHom (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) ∧
      (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), tensorK π Ξ k * lieB π Ξ (toL X) = lieB π Ξ (toL (k.1 * X * star k.1)) * tensorK π Ξ k) ∧
      ∀ (τ : E →+* ℂ) (m : Multiset ℂ), GlobalTheory.WignerGL.HasDualInfChar Ξ τ m → ∀ u : ℂ,
        Formalism.REAL.qdet (fun i j => -MulOpposite.op (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) τ i j)) (u + ((a : ℂ) - 1) / 2) =
          MulOpposite.op ((m.map (u + ·)).prod • (1 : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))) := by
  intro E _ _ _ a π Ξ
  have hB : ∀ X, lieB π Ξ X = actAlg π.V Ξ.d (Ξ.dmat X) := fun _ => rfl
  refine ⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩
  · rw [hB, hB, hB, ← GlobalTheory.AlgInfChar.dmat_bracket, map_sub, map_mul, map_mul]
  · refine TensorProduct.ext' fun φ v => ?_
    have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X) =
        Ξ.dmat (toL (k.1 * X * star k.1)) * Ξ.mat (Unitary.toUnits k) :=
      Ξ.mat_mul_dmat (Unitary.toUnits k) X
    simp only [mul_apply_eq_comp, tensorK, lieB_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
  · have h0 := map_qdet (A := Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (B := (Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))ᵐᵒᵖ)
      (actOp π.V Ξ.d) (GlobalTheory.WignerGL.dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)
    have h := h0.symm.trans (congrArg (actOp π.V Ξ.d) (hm.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, actOp π.V Ξ.d (GlobalTheory.WignerGL.dualE Ξ τ i j) =
        -MulOpposite.op (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg, actOp_apply, Matrix.transpose_transpose]
      simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h
    rw [h, MulOpposite.op_smul, MulOpposite.op_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.KCurve
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.kCurve :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z →
      ∃ k : ℝ → Kinf E a, k 0 = 1 ∧ HasDerivAt (fun t => toL (k t).1) (toL Z) 0 := by
  intro E _ _ _ a Z hZ
  open scoped Matrix.Norms.Operator in
  have hs : ∀ t : ℝ, star (NormedSpace.exp (t • Z)) = NormedSpace.exp (-(t • Z)) := fun t => by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, ← Matrix.star_eq_conjTranspose, star_smul,
      star_trivial, hZ, smul_neg]
  have hm : ∀ t : ℝ, NormedSpace.exp (t • Z) ∈ unitary (Matrix (Fin a) (Fin a) (Cinf E)) := fun t => by
    rw [Unitary.mem_iff, hs, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
    simp
  refine ⟨fun t => ⟨NormedSpace.exp (t • Z), hm t⟩, Subtype.ext (by simp), ?_⟩
  open scoped Matrix.Norms.Operator in
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HolEq
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.holEq :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) (x : Matrix (Fin a) (Fin a) ℂ),
      hol τ L x = (1 / 2 : ℂ) • (L (toL (x.map (atEmb τ))) - Complex.I • L (toL ((Complex.I • x).map (atEmb τ)))) := by
  intro E _ _ _ a N _ _ _ _ τ L x
  let L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N := L
  have hsum : ∀ y : Matrix (Fin a) (Fin a) ℂ,
      L' (y.map (atEmb τ)) = ∑ i, ∑ j, L' (Matrix.single i j (atEmb τ (y i j))) := fun y => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (y.map (atEmb τ))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Matrix.map_apply]
  have hL : ∀ (i j : Fin a) (w : ℂ), L' (Matrix.single i j (atEmb τ w)) =
      (w.re : ℂ) • L' (Matrix.single i j (atEmb τ 1)) +
        (w.im : ℂ) • L' (Matrix.single i j (atEmb τ Complex.I)) := fun i j w => by
    rw [atEmb_eq τ w, Matrix.single_add, ← Matrix.smul_single, ← Matrix.smul_single, map_add (f := _), map_smul, map_smul,
      ← algebraMap_smul ℂ w.re, ← algebraMap_smul ℂ w.im]
    rfl
  change ∑ i, ∑ j, x i j • ((1 / 2 : ℂ) • (L' (Matrix.single i j (atEmb τ 1)) -
      Complex.I • L' (Matrix.single i j (atEmb τ Complex.I)))) =
    (1 / 2 : ℂ) • (L' (x.map (atEmb τ)) - Complex.I • L' ((Complex.I • x).map (atEmb τ)))
  rw [hsum, hsum]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, hL i j (x i j), hL i j (Complex.I * x i j)]
  generalize x i j = c
  conv_lhs => rw [← Complex.re_add_im c]
  simp only [Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_neg]
  match_scalars
  · ring
  · linear_combination (-(c.im : ℂ) / 2) * Complex.I_mul_I
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HomId
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.homId :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M),
      dCo L ω = 0 → InfEq L ω → ∀ (X : Matrix (Fin a) (Fin a) (Cinf E)) (Y : Fin (q + 1) → Herm E a),
        ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • (L (toL (Y i).1) (ω (Matrix.vecCons (hp (toL X)) (i.removeNth Y))) -
          ω (Matrix.vecCons (hp (toL ((Y i).1 * X - X * (Y i).1))) (i.removeNth Y))) = L (toL X) (ω Y) := by
  intro E _ _ _ a M _ _ _ _ L q ω hd hinf X Y
  let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
  have hZ : star Z = -Z := by
    simp only [Z]
    rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
  have hX : toL X = toL (hp (toL X)).1 + toL Z := by
    have h : X = (hp (toL X)).1 + Z := by
      rw [hp_val]; simp only [Z]; module
    exact congrArg toL h
  have hb : ∀ U : Herm E a, hp (toL (U.1 * X - X * U.1)) = -brH Z hZ U := by
    intro U
    apply Subtype.ext
    have h : star U.1 = U.1 := U.2
    rw [hp_val]
    change _ = -(Z * U.1 - U.1 * Z)
    simp only [Z, star_sub, star_mul, h, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub]
    module
  have h1 := dCo_cons (L := L) ω (hp (toL X)) Y
  rw [hd, AlternatingMap.zero_apply, eq_comm, sub_eq_zero, dCo_apply] at h1
  rw [congrArg L hX, map_add (f := _), LinearMap.add_apply, h1, hinf Z hZ Y, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ω (Matrix.vecCons (-brH Z hZ (Y i)) (i.removeNth Y)) =
      -ω (Matrix.vecCons (brH Z hZ (Y i)) (i.removeNth Y)) := by
    rw [← AlternatingMap.curryLeft_apply_apply, ← AlternatingMap.curryLeft_apply_apply, map_neg,
      AlternatingMap.neg_apply]
  rw [hb, h2, sub_neg_eq_add, smul_add, ← Fin.insertNth_removeNth, AlternatingMap.map_insertNth,
    AlternatingMap.curryLeft_apply_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TensDer
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.tensDer :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), SepDer (tensorK π Ξ) (tensorLie π Ξ) := by
  intro E _ _ _ a π Ξ k Z h0 hk m' hm
  let e := TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d)
  have h1 : e m' ≠ 0 := fun h => hm (e.map_eq_zero_iff.1 h)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h1
  have h2 : (e m' j).1.1 ≠ 0 := fun h => hj (Subtype.ext (Subtype.ext h))
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : π.V ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (e m j).1.1 g
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hl : ∀ (φ : π.V) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1.1 g * v j := fun φ v => by
    have h : e (φ ⊗ₜ v) j = v j • φ := by
      simp only [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    change (e (φ ⊗ₜ v) j).1.1 g = _
    rw [h, mul_comm]
    rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simpa only [map_add (f := _)] using hx.fun_add hy
  | tmul φ v =>
    have h3 := GlobalTheory.CuspRep.hasDerivAt_curve φ.1 g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    simp only [tensorK, tensorLie_tmul, TensorProduct.map_tmul, map_add (f := _), hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5
    exact h5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGenC
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExpSq
theorem UpperTheory.Reformulated.B.Qf11.expSq :
    ∀ {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ),
    N * N = (0 : Matrix (Fin n) (Fin n) ℂ) → NormedSpace.exp N = (1 : Matrix (Fin n) (Fin n) ℂ) + N := by
  intro n N h
  have hz : ∀ k : ℕ, k ∉ Finset.range 2 → ((k.factorial : ℂ)⁻¹) • N ^ k = 0 := by
    intro k hk
    have hk2 : 2 ≤ k := by
      rw [Finset.mem_range] at hk
      omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
    rw [pow_add, pow_two, h, zero_mul, smul_zero]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ]
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem expSq {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (h : N * N = 0) :
    NormedSpace.exp N = 1 + N :=
  _root_.UpperTheory.Reformulated.B.Qf11.expSq N h

theorem UpperTheory.V.AlgRepEndIrreducible.expGenC :
    ∀ (n : ℕ) (H : Submonoid (Matrix (Fin n) (Fin n) ℂ)), (∀ X : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp X ∈ H) →
      ∀ g : Matrix (Fin n) (Fin n) ℂ, g.det ≠ 0 → g ∈ H := by
  intro n H hH g hg
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => M ∈ H) g hg ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := by
      rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD
      exact fun i => hD i (Finset.mem_univ i)
    have := hH (Matrix.diagonal fun i => Complex.log (D i))
    rw [Matrix.exp_diagonal] at this
    convert this using 2
    funext i
    rw [Pi.exp_def]
    simp only [← Complex.exp_eq_exp_ℂ]
    exact (Complex.exp_log (hD' i)).symm
  · intro t
    have := hH (Matrix.single t.i t.j t.c)
    rw [expSq _ (Matrix.single_mul_single_of_ne _ _ _ _ t.hij.symm _)] at this
    exact this
  · intro A B _ _ hA hB
    exact H.mul_mem hA hB
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.QdetIntertw
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem qdet_intertw {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {k : ℕ}
    (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q, R ∘ₗ X p q = Y p q ∘ₗ R) (v : ℂ) :
    R ∘ₗ Formalism.REAL.qdet X v = Formalism.REAL.qdet Y v ∘ₗ R := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | R ∘ₗ z.1 = z.2 ∘ₗ R}
      mul_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 ∘ₗ y.1) = (x.2 ∘ₗ y.2) ∘ₗ R
        rw [← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]
      add_mem' := fun {x y} hx hy => by
        change R ∘ₗ (x.1 + y.1) = (x.2 + y.2) ∘ₗ R
        rw [LinearMap.comp_add, LinearMap.add_comp, hx, hy]
      algebraMap_mem' := fun c => by
        change R ∘ₗ (algebraMap ℂ (Module.End ℂ M) c) = (algebraMap ℂ (Module.End ℂ M') c) ∘ₗ R
        ext φ; simp }
  let Z : Fin k → Fin k → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 = Formalism.REAL.qdet X v :=
    map_qdet ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((Formalism.REAL.qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 = Formalism.REAL.qdet Y v :=
    map_qdet ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]
  exact (Formalism.REAL.qdet Z v).2

set_option synthInstance.maxHeartbeats 100000 in
theorem UpperTheory.V.AlgRepEndIrreducible.tensA :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), IsLieHom (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) ∧
      (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), tensorK π Ξ k * lieA π Ξ (toL X) = lieA π Ξ (toL (k.1 * X * star k.1)) * tensorK π Ξ k) ∧
      ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ u : ℂ,
        Formalism.REAL.qdet (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ) (u + ((a : ℂ) - 1) / 2) =
          (m.map (u + ·)).prod • (1 : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) := by
  intro E _ _ _ a π Ξ
  let f : Module.End ℂ π.V →ₐ[ℂ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) := Module.End.rTensorAlgHom ℂ π.V (Fin Ξ.d → ℂ)
  have hf : ∀ X, lieA π Ξ X = f (lieOp π X) := fun _ => rfl
  refine ⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩
  · rw [hf, hf, hf, ← map_mul f, ← map_mul f, ← map_sub f]
    congr 1
    exact LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun ((lie_comm (toL X) (toL Y)).trans
      (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm) φ.1)
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : π.op (.cpt k) (lieOp π (toL X) φ) = lieOp π (toL (k.1 * X * star k.1)) (π.op (.cpt k) φ) :=
      Subtype.ext (LinearMap.congr_fun (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) X) φ.1)
    simp only [mul_apply_eq_comp, tensorK, lieA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · have e : eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ =
        fun i j => f (eL (N := Module.End ℂ π.V) (lieOp π) τ i j) := by
      funext i j
      simp only [eL, hf, map_smul, map_sub]
    have h := qdet_intertw π.V.subtype (eL (N := Module.End ℂ π.V) (lieOp π) τ) (Eop τ) (fun _ _ => rfl)
      (u + ((a : ℂ) - 1) / 2)
    have h2 : Formalism.REAL.qdet (eL (N := Module.End ℂ π.V) (lieOp π) τ) (u + ((a : ℂ) - 1) / 2) =
        (m.map (u + ·)).prod • (1 : Module.End ℂ π.V) :=
      LinearMap.ext fun φ => Subtype.ext ((LinearMap.congr_fun h φ).trans (hm.2 u φ.1 φ.2))
    rw [e, ← map_qdet, h2, map_smul, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpMat
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct


open scoped Matrix.Norms.Operator in
private theorem oneParam_eq_exp {n : ℕ} (F : ℝ → Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (h0 : F 0 = 1) (hadd : ∀ s t, F (s + t) = F s * F t) (hD : HasDerivAt F D 0) :
    F 1 = NormedSpace.exp D := by
  have h1 : ∀ t, HasDerivAt F (F t * D) t := by
    intro t
    have h2 : HasDerivAt (fun s => F (s - t)) D t := by
      have h := HasDerivAt.comp_sub_const (f := F) (f' := D) t t (by rw [sub_self]; exact hD)
      exact h
    have h3 := h2.const_mul (F t)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    change F s = F t * F (s - t)
    rw [← hadd, add_sub_cancel]
  have h4 : ∀ t, HasDerivAt (fun t : ℝ => F t * NormedSpace.exp (t • -D)) 0 t := by
    intro t
    have h := (h1 t).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-D) t)
    have e : F t * D * NormedSpace.exp (t • -D) + F t * (-D * NormedSpace.exp (t • -D)) = 0 := by
      rw [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
    exact h.congr_deriv e
  have h5 := is_const_of_deriv_eq_zero (fun t => (h4 t).differentiableAt) (fun t => (h4 t).deriv) 1 0
  simp only [one_smul, zero_smul, NormedSpace.exp_zero, h0, mul_one] at h5
  have h6 : NormedSpace.exp (-D) * NormedSpace.exp D = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl D).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  rw [← mul_one (F 1), ← h6, ← mul_assoc, h5, one_mul]

open scoped Matrix.Norms.Operator in
private theorem representation_exp_eq_exp_derivative {E : Type} [Field E] [NumberField E] {a : ℕ} (Ξ : AlgRep E a)
    (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    Ξ.mat (Matrix.isUnit_exp X).unit = NormedSpace.exp (Ξ.dmat (toL X)) := by
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • X)).unit
  have hc : ∀ t, (c t).val = NormedSpace.exp (t • X) := fun t => rfl
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hadd : ∀ s t, c (s + t) = c s * c t := fun s t => Units.ext (by
    rw [Units.val_mul, hc, hc, hc, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
  have h1 : HasDerivAt (fun t => (c t).val) X 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  have h2 := GlobalTheory.AlgInfChar.hasDerivAt_mat Ξ c (toL X) h0 h1
  have h3 := oneParam_eq_exp (fun t => Ξ.mat (c t)) _ (by simp only [h0, map_one])
    (fun s t => by simp only [hadd, map_mul]) h2
  have e : (Matrix.isUnit_exp X).unit = c 1 := Units.ext (by rw [hc, one_smul]; rfl)
  rw [e]
  exact h3

theorem UpperTheory.V.AlgRepEndIrreducible.expMat :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (X : Matrix (Fin a) (Fin a) (Cinf E)) (y : GL (Fin a) (Cinf E)),
      y.val = NormedSpace.exp X → Ξ.mat y = NormedSpace.exp (Ξ.dmat (toL X)) := by
  intro E _ _ _ a Ξ X y hy
  have e : y = (Matrix.isUnit_exp X).unit := Units.ext hy
  rw [e]
  exact representation_exp_eq_exp_derivative Ξ X
end
