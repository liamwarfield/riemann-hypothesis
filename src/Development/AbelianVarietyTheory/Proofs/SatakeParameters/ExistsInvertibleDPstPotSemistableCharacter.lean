module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToAStRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
noncomputable section

open Module

namespace GlobalTheory.Pst.UnitLetter

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (L : FinExt l)

def toA : ((Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) ≃ₗ[ℚ_[l]] Bst P ⊗[ℚ_[l]] ↥L.1 :=
  (TensorProduct.congr (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1) (LinearEquiv.refl ℚ_[l] (Bst P))).trans
    (TensorProduct.comm ℚ_[l] ↥L.1 (Bst P))

@[simp] theorem toA_tmul (v : Fin 1 → ↥L.1) (b : Bst P) : toA P L (v ⊗ₜ b) = b ⊗ₜ v 0 := rfl

variable {P L}

theorem toA_mulB (y' y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (GlobalTheory.Pst.TwistLetters.mulB (L := L) P (Fin 1 → ↥L.1) y' y) = toA P L y' * toA P L y := by
  induction y' using TensorProduct.inductionOn with
  | tmul v' b' =>
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      rw [GlobalTheory.Pst.TwistLetters.mulB_tmul, toA_tmul, toA_tmul, toA_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      simp
    | add x x' hx hx' => simp only [map_add, mul_add, hx, hx']
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, add_mul, hy, hy']

theorem toA_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (mulV P ↥L.1 (Fin 1 → ↥L.1) c y) = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c • toA P L y := by
  induction y using TensorProduct.inductionOn with
  | tmul v b =>
    rw [mulV_tmul, toA_tmul, toA_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x x' hx hx' => simp only [map_add, smul_add, hx, hx']

theorem toA_stRep {K : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)
    (hm : ∀ g v, ρm g v = χ g • v) (g : ↥(GK K)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (stRep P ρm g y) =
      Algebra.TensorProduct.map (actSt P (g : GQ l)) (AlgHom.id ℚ_[l] ↥L.1) (toA P L y) *
        ((1 : Bst P) ⊗ₜ[ℚ_[l]] χ g) := by
  induction y using TensorProduct.inductionOn with
  | tmul v b =>
    rw [stRep_tmul, toA_tmul, toA_tmul, hm, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp [mul_comm]
  | add x x' hx hx' => simp only [map_add, add_mul, hx, hx']

end GlobalTheory.Pst.UnitLetter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCombinationNormNeZeroOfLinearIndependentAl
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCombinationNormNeZeroOfLinearIndependentAl
open scoped TensorProduct
open Matrix

namespace GlobalTheory

theorem exists_combination_norm_ne_zero_of_linearIndependent
    {B A : Type} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] {d : ℕ} (hd : Module.finrank B A = d)
    (y : Fin d → A) (hy : LinearIndependent B y) :
    ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  classical
  let e := Module.finBasisOfFinrankEq B A hd
  let Y : Matrix (Fin d) (Fin d) B := fun i j => e.equivFun (y j) i
  have key : ∀ v : Fin d → B, e.equivFun (∑ j, v j • y j) = Y *ᵥ v := by
    intro v
    ext i
    simp [Y, Matrix.mulVec, dotProduct, mul_comm]
  have hdet : Y.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 : ∑ j, v j • y j = 0 := by
      apply e.equivFun.injective
      rw [key, hv, map_zero]
    exact hv0 (funext fun j => Fintype.linearIndependent_iff.mp hy v h1 j)
  refine ⟨Y.adjugate *ᵥ e.equivFun 1, ?_⟩
  have hsum : ∑ j, (Y.adjugate *ᵥ e.equivFun 1) j • y j = algebraMap B A Y.det := by
    apply e.equivFun.injective
    rw [key, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, Algebra.algebraMap_eq_smul_one, map_smul]
  rw [hsum, Algebra.norm_algebraMap]
  exact pow_ne_zero _ hdet

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCombinationNormNeZeroOfLinearIndependentAlStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent : ∀ {B A : Type} [inst : CommRing B] [IsDomain B] [inst_2 : CommRing A] [inst_3 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ}, Module.finrank B A = d → ∀ (y : Fin d → A), LinearIndependent B y → ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | exact GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFieldCombinationNormNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFieldCombinationNormNeZero
open scoped TensorProduct

namespace GlobalTheory


open MvPolynomial in
theorem exists_field_combination_norm_ne_zero {k B A : Type} [Field k] [Infinite k] [CommRing B]
    [IsDomain B] [Algebra k B] [CommRing A] [Algebra B A] [Module.Free B A] [Module.Finite B A]
    {d : ℕ} (y : Fin d → A) (hx : ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) :
    ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hx
  let b := Module.Free.chooseBasis B A
  let M : Matrix (Module.Free.ChooseBasisIndex B A) (Module.Free.ChooseBasisIndex B A)
      (MvPolynomial (Fin d) B) :=
    Matrix.of fun j l => ∑ i, X i * C (Algebra.leftMulMatrix b (y i) j l)
  have heval : ∀ x : Fin d → B, eval x M.det = Algebra.norm B (∑ i, x i • y i) := by
    intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j l
    set_option synthInstance.maxHeartbeats 100000 in
      simp [M, map_sum, Matrix.sum_apply, mul_comm]
  by_contra hcon
  push_neg at hcon
  have hinf : ∀ _ : Fin d, (Set.range (algebraMap k B)).Infinite := fun _ =>
    Set.infinite_range_of_injective (algebraMap k B).injective
  have hQ : M.det = 0 := by
    refine funext_set (fun _ => Set.range (algebraMap k B)) hinf fun x hx => ?_
    choose a ha using fun i => hx i (Set.mem_univ i)
    rw [heval, map_zero, ← hcon a]
    simp [ha]
  exact hx₀ (by rw [← heval, hQ, map_zero])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFieldCombinationNormNeZeroStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero : ∀ {k B A : Type} [inst : Field k] [Infinite k] [inst_2 : CommRing B] [IsDomain B] [inst_4 : Algebra k B] [inst_5 : CommRing A] [inst_6 : Algebra B A] [Module.Free B A] [Module.Finite B A] {d : ℕ} (y : Fin d → A), (∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) → ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by
  first | exact @GlobalTheory.exists_field_combination_norm_ne_zero | exact GlobalTheory.exists_field_combination_norm_ne_zero | (intros; apply GlobalTheory.exists_field_combination_norm_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTensorProductMapLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTensorProductMapLeft
open scoped TensorProduct

namespace GlobalTheory

theorem norm_tensorProduct_map_left {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L]
    [Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L) :
    Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  classical
  let e := Module.finBasis R L
  let b := Algebra.TensorProduct.basis B e
  let σ := Algebra.TensorProduct.map f (AlgHom.id R L)
  have hrepr : ∀ z : B ⊗[R] L, ∀ i, b.repr (σ z) i = f (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [σ, b, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  have hb : ∀ j, σ (b j) = b j := by
    intro j
    simp [σ, b, Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b (σ w) = (Algebra.leftMulMatrix b w).map f := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hb j, hrepr]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, hmat]
  exact (AlgHom.map_det f _).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTensorProductMapLeftStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_tensorProduct_map_id_right : ∀ {R B L : Type} [inst : Field R] [inst_1 : CommRing B] [inst_2 : Algebra R B] [inst_3 : Field L] [inst_4 : Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L), Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  first | exact @GlobalTheory.norm_tensorProduct_map_left | exact GlobalTheory.norm_tensorProduct_map_left | (intros; apply GlobalTheory.norm_tensorProduct_map_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvertibleDPstPotSemistableCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
noncomputable section
open Module

namespace GlobalTheory.NormBC

theorem norm_one_tmul {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    [FiniteDimensional R L] (x : L) :
    Algebra.norm B ((1 : B) ⊗ₜ[R] x) = algebraMap R B (Algebra.norm R x) := by
  have h : Algebra.lmul B (B ⊗[R] L) ((1 : B) ⊗ₜ[R] x) = (Algebra.lmul R L x).baseChange B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b z
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, Algebra.norm_apply]

theorem isUnit_of_isUnit_norm {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Module.Free B A]
    [Module.Finite B A] {z : A} (h : IsUnit (Algebra.norm B z)) : IsUnit z := by
  rw [Algebra.norm_apply] at h
  have hu : IsUnit (LinearMap.mul B A z) := (LinearMap.isUnit_iff_isUnit_det _).2 h
  obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
  exact IsUnit.of_mul_eq_one y (by simpa using hy)

end GlobalTheory.NormBC

namespace GlobalTheory.Pst.UnitLetter

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def toAlg (L : FinExt l) : Bst P ⊗[ℚ_[l]] (Fin 1 → ↥L.1) ≃ₗ[Bst P] Bst P ⊗[ℚ_[l]] ↥L.1 :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Bst P) (Bst P))
    (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1)

theorem toAlg_comm (L : FinExt l) (z : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toAlg P L (TensorProduct.comm ℚ_[l] (Fin 1 → ↥L.1) (Bst P) z) = toA P L z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    set_option synthInstance.maxHeartbeats 200000 in
      simp only [map_zero]
  | tmul v b => rfl
  | add x x' hx hx' => simp only [map_add (f := _), hx, hx']

theorem linearIndependent_toA {K L : FinExt l} (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) {d : ℕ}
    (b : Basis (Fin d) ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)) :
    LinearIndependent ↥(MaximalUnramifiedExtension l)
      (fun i => toA P L (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) := by
  have h := b.linearIndependent.map' (((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ
    GlobalTheory.PstRank.toB P ρ) (LinearMap.ker_eq_bot.mpr ((toAlg P L).injective.comp (GlobalTheory.PstRank.toB_injective P ρ)))
  have hf : (fun i => toA P L (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P)) =
      ⇑(((toAlg P L).toLinearMap.restrictScalars ↥(MaximalUnramifiedExtension l)) ∘ₗ GlobalTheory.PstRank.toB P ρ) ∘ ⇑b :=
    funext fun i => (toAlg_comm P L _).symm
  rw [hf]
  exact h

end GlobalTheory.Pst.UnitLetter

namespace GlobalTheory.Pst.UnitLetter

open GlobalTheory.NormBC

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem exists_common_fixed {K L : FinExt l} (ρ : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) {d : ℕ}
    (y : Fin d → (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (hy : ∀ i, y i ∈ Dpst P ρ) :
    ∃ K' : FinExt l, ∀ i (g : ↥(GK K)), (g : GQ l) ∈ GK K' → stRep P ρ g (y i) = y i := by
  suffices h : ∀ s : Finset (Fin d), ∃ K' : FinExt l, ∀ i ∈ s, ∀ (g : ↥(GK K)), (g : GQ l) ∈ GK K' →
      stRep P ρ g (y i) = y i by
    obtain ⟨K', hK'⟩ := h Finset.univ
    exact ⟨K', fun i => hK' i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨K, by simp⟩
  | insert j s hj ih =>
    obtain ⟨K₁, h₁⟩ := ih
    obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρ).mp (hy j)
    refine ⟨supExt K₁ K₂, fun i hi g hg => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)
    · exact h₁ i hi g (GK_le (K' := supExt K₁ K₂) le_sup_left hg)

end GlobalTheory.Pst.UnitLetter


set_option maxHeartbeats 1000000 in
open GlobalTheory.Pst.UnitLetter GlobalTheory.NormBC in
theorem GlobalTheory.Pst.UnitLetter.exists_unit_Dpst : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ {K L : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1), (∀ g v, ρm g v = χ g • v) → IsPst P ρm → ∃ y ∈ Dpst P ρm, ∃ y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, GlobalTheory.Pst.TwistLetters.mulB (L := L) P (Fin 1 → ↥L.1) y' y = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  intro l _ P AI hT K L ρm χ hm hpst
  haveI := L.2
  obtain ⟨hdom, hfrac, hline⟩ := GlobalTheory.Pst.stRegular l P AI hT
  obtain ⟨hfd, hrank⟩ := (isPst_iff P ρm).mp hpst
  set d := finrank ℚ_[l] ↥L.1 with hddef
  have hd : finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) = d := by
    rw [hrank]; exact (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1).finrank_eq
  let bD := Module.finBasisOfFinrankEq ↥(MaximalUnramifiedExtension l) (DpstUr P ρm) hd
  let y : Fin d → (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P := fun i => ((toUr P ρm).symm (bD i) : ↥(Dpst P ρm)).1
  have hyD : ∀ i, y i ∈ Dpst P ρm := fun i => ((toUr P ρm).symm (bD i)).2

  obtain ⟨K', hK'⟩ := exists_common_fixed P ρm y hyD
  let w : Fin d → Bst P ⊗[ℚ_[l]] ↥L.1 := fun i => toA P L (y i)
  let G := {g : ↥(GK K) // (g : GQ l) ∈ GK K'}
  let σ : G → (Bst P ⊗[ℚ_[l]] ↥L.1) →+ (Bst P ⊗[ℚ_[l]] ↥L.1) := fun g => AddMonoidHom.mk' (fun z =>
      Algebra.TensorProduct.map (actSt P ((g.1 : ↥(GK K)) : GQ l)) (AlgHom.id ℚ_[l] ↥L.1) z *
        ((1 : Bst P) ⊗ₜ[ℚ_[l]] χ g.1)) (fun a b => by simp [map_add (f := _), add_mul])
  have hσ : ∀ (g : G) (b : Bst P) (z : Bst P ⊗[ℚ_[l]] ↥L.1),
      σ g (b • z) = actSt P ((g.1 : ↥(GK K)) : GQ l) b • σ g z := by
    intro g b z
    simp only [σ, AddMonoidHom.mk'_apply, Algebra.smul_def, map_mul, mul_assoc]
    congr 1
  have hreg : ∀ b b' : Bst P, b ≠ 0 → (∀ g : G, b * actSt P ((g.1 : ↥(GK K)) : GQ l) b' =
      actSt P ((g.1 : ↥(GK K)) : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b := by
    intro b b' hb h
    obtain ⟨c, -, hc⟩ := hfrac (supExt K K') b b' hb fun g =>
      h ⟨⟨g, GK_le (K' := supExt K K') le_sup_left g.2⟩, GK_le (K' := supExt K K') le_sup_right g.2⟩
    exact ⟨c, hc⟩
  have hv : ∀ (g : G) i, σ g (w i) = w i := by
    intro g i
    simp only [σ, w, AddMonoidHom.mk'_apply]
    rw [← toA_stRep ρm χ hm, hK' i g.1 g.2]
  have hK : LinearIndependent ↥(MaximalUnramifiedExtension l) w := linearIndependent_toA P ρm bD
  have hB : LinearIndependent (Bst P) w := by
    have := GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P)
      (W := Bst P ⊗[ℚ_[l]] ↥L.1)
      (G := G) (fun g => actSt P ((g.1 : ↥(GK K)) : GQ l)) σ hσ hreg w hv Finset.univ
      (hK.linearIndepOn _)
    rw [Finset.coe_univ] at this
    exact linearIndepOn_univ_iff.mp this
  have hfin : finrank (Bst P) (Bst P ⊗[ℚ_[l]] ↥L.1) = d := Module.finrank_baseChange
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_field_coeff_norm_sum_smul_ne_zero (k := ↥(MaximalUnramifiedExtension l)) w (GlobalTheory.T.exists_norm_sum_smul_ne_zero_of_linearIndependent hfin w hB)
  let ys := ∑ i, mulV P ↥L.1 (Fin 1 → ↥L.1) (a i) (y i)
  have hys : ys ∈ Dpst P ρm := Submodule.sum_mem _ fun i _ => mulV_mem_Dpst P ρm (a i) (y i) (hyD i)
  have hysA : toA P L ys = ∑ i, algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) (a i) • w i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ys, map_sum, toA_mulV, w]
  have hn : Algebra.norm (Bst P) (toA P L ys) ≠ 0 := by rw [hysA]; exact ha
  obtain ⟨K₂, hK₂⟩ := (mem_Dpst P ρm).mp hys
  have hχ : ∀ g : ↥(GK K), χ g ≠ 0 := by
    intro g h0
    have h1 : ρm (g * g⁻¹) (fun _ => (1 : ↥L.1)) = fun _ => 1 := by rw [mul_inv_cancel, map_one]; rfl
    rw [map_mul, Module.End.mul_apply, hm g, h0, zero_smul] at h1
    exact zero_ne_one (congrFun h1 0)
  have hunit : IsUnit (Algebra.norm (Bst P) (toA P L ys)) := by
    refine hline (supExt K K₂) _ hn fun g => ?_
    let g0 : ↥(GK K) := ⟨g, GK_le (K' := supExt K K₂) le_sup_left g.2⟩
    have hfix := hK₂ g0 (GK_le (K' := supExt K K₂) le_sup_right g.2)
    have h1 : Algebra.norm (Bst P) (toA P L (stRep P ρm g0 ys)) = Algebra.norm (Bst P) (toA P L ys) := by
      rw [hfix]
    rw [toA_stRep ρm χ hm, map_mul, GlobalTheory.T.norm_tensorProduct_map_id_right, norm_one_tmul] at h1
    have hν : Algebra.norm ℚ_[l] (χ g0) ≠ 0 := Algebra.norm_ne_zero_iff.mpr (hχ g0)
    refine ⟨(Algebra.norm ℚ_[l] (χ g0))⁻¹, ?_⟩
    change actSt P ((g0 : ↥(GK K)) : GQ l) _ = _
    conv_rhs => rw [← h1]
    rw [mul_comm, mul_assoc, ← map_mul, mul_inv_cancel₀ hν, map_one, mul_one]
  obtain ⟨v, hv'⟩ := (isUnit_of_isUnit_norm hunit).exists_right_inv
  refine ⟨ys, hys, (toA P L).symm v, ?_⟩
  apply (toA P L).injective
  rw [toA_mulB, LinearEquiv.apply_symm_apply, toA_tmul, mul_comm, hv']
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvertibleDPstPotSemistableCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invertible_dPst_potSemistableCharacter : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ {K L : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1), (∀ g v, ρm g v = χ g • v) → IsPst P ρm → ∃ y ∈ Dpst P ρm, ∃ y' : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P, GlobalTheory.Pst.TwistLetters.mulB (L := L) P (Fin 1 → ↥L.1) y' y = (fun _ => (1 : ↥L.1)) ⊗ₜ (1 : Bst P) := by
  first | exact @GlobalTheory.Pst.UnitLetter.exists_unit_Dpst | exact GlobalTheory.Pst.UnitLetter.exists_unit_Dpst | (intros; apply GlobalTheory.Pst.UnitLetter.exists_unit_Dpst <;> assumption)
end
