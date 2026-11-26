module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardTorsionTrivialOfTorsorsHaveSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFormOfPicTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFormOfPicTorsion
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PicTorsionForm

open CommRing Module

variable {B : Type} [CommRing B]

theorem exists_local_generator (M : Type) [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (p : Ideal B) [p.IsPrime] : ∃ e : M, ∀ x : M, ∃ w a : B, w ∉ p ∧ w • x = a • e := by
  have ⟨f⟩ := Invertible.free_iff_linearEquiv.mp
    (inferInstance : Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
  obtain ⟨e, s, he⟩ : ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = f.symm 1 :=
    LocalizedModule.induction_on (β := fun y => ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = y)
      (fun e s => ⟨e, s, rfl⟩) (f.symm 1)
  refine ⟨e, fun x => ?_⟩
  obtain ⟨a, t, ht⟩ : ∃ (a : B) (t : p.primeCompl), Localization.mk a t = f (LocalizedModule.mk x 1) :=
    Localization.induction_on (f (LocalizedModule.mk x 1)) fun z => ⟨z.1, z.2, rfl⟩
  have key : LocalizedModule.mk x (1 : p.primeCompl) = LocalizedModule.mk (a • e) (t * s) := by
    rw [← f.symm_apply_apply (LocalizedModule.mk x 1), ← ht, ← mul_one (Localization.mk a t),
      ← smul_eq_mul, map_smul, ← he, LocalizedModule.mk_smul_mk]
  obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq).mp key
  refine ⟨(u : B) * ((t : B) * s), u * a, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem t.2 s.2)
  · simpa only [Submonoid.smul_def, Submonoid.coe_mul, OneMemClass.coe_one, one_smul, smul_smul] using hu

theorem tensorPow_equiv (c : Pic B) (n : ℕ) :
    Nonempty (Pic.AsModule (c ^ n) ≃ₗ[B] ⨂[B] _ : Fin n, Pic.AsModule c) := by
  induction n with
  | zero =>
    have ⟨e⟩ := Pic.ext_iff.mp (pow_zero c)
    have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
    exact ⟨e ≪≫ₗ g ≪≫ₗ (PiTensorProduct.isEmptyEquiv (Fin 0)).symm⟩
  | succ n ih =>
    obtain ⟨ih⟩ := ih
    have ⟨e1⟩ := Pic.ext_iff.mp (pow_succ c n)
    have ⟨e2⟩ := Pic.ext_iff.mp (Pic.mul_eq_tensor (c ^ n) c)
    exact ⟨e1 ≪≫ₗ e2 ≪≫ₗ Pic.mk.linearEquiv B _ ≪≫ₗ TensorProduct.congr ih
      (PiTensorProduct.subsingletonEquiv (R := B) (s := fun _ : Fin 1 => Pic.AsModule c) 0).symm ≪≫ₗ
      PiTensorProduct.tmulEquiv B (Pic.AsModule c) ≪≫ₗ PiTensorProduct.reindex B _ finSumFinEquiv⟩

theorem exists_form : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 →
    ∃ φ : (Π _ : Fin q, CommRing.Pic.AsModule c) →ₘₗ[B] B,
      ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := by
  intro B _ q c hc
  obtain ⟨T⟩ := tensorPow_equiv c q
  have ⟨e1⟩ := Pic.ext_iff.mp hc
  have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
  let ψ : (⨂[B] _ : Fin q, Pic.AsModule c) ≃ₗ[B] B := T.symm ≪≫ₗ e1 ≪≫ₗ g
  refine ⟨ψ.toLinearMap.compMultilinearMap (PiTensorProduct.tprod B), fun p hp => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin q → Pic.AsModule c, ψ (PiTensorProduct.tprod B x) ∉ p := by
    by_contra! h
    have hall : ∀ t, ψ t ∈ p := fun t => by
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r x => rw [map_smul, smul_eq_mul]; exact p.mul_mem_left r (h x)
      | add a b ha hb => rw [map_add (f := _)]; exact p.add_mem ha hb
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (by simpa using hall (ψ.symm 1)))
  obtain ⟨e, he⟩ := exists_local_generator (Pic.AsModule c) p
  choose w a hw hwa using fun i => he (x i)
  refine ⟨e, fun hmem => ?_⟩
  have hmem' : ψ (PiTensorProduct.tprod B fun _ => e) ∈ p := hmem
  have h1 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, w i) * ψ (PiTensorProduct.tprod B x) := by
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply, map_smul, smul_eq_mul]
  have h2 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, a i) * ψ (PiTensorProduct.tprod B (fun _ => e)) := by
    simp_rw [hwa]
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply, map_smul, smul_eq_mul]
  have hin : (∏ i, w i) * ψ (PiTensorProduct.tprod B x) ∈ p := by
    rw [← h1, h2]; exact p.mul_mem_left _ hmem'
  rcases hp.mem_or_mem hin with h | h
  · exact (p.primeCompl.prod_mem fun i _ => hw i) h
  · exact hx h

end GlobalTheory.PicTorsionForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFormOfPicTorsionStatement
open scoped TensorProduct
open CommRing Module

variable {B : Type} [CommRing B] in
private theorem exists_local_generator (M : Type) [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (p : Ideal B) [p.IsPrime] : ∃ e : M, ∀ x : M, ∃ w a : B, w ∉ p ∧ w • x = a • e := by
  have ⟨f⟩ := Invertible.free_iff_linearEquiv.mp
    (inferInstance : Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
  obtain ⟨e, s, he⟩ : ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = f.symm 1 :=
    LocalizedModule.induction_on (β := fun y => ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = y)
      (fun e s => ⟨e, s, rfl⟩) (f.symm 1)
  refine ⟨e, fun x => ?_⟩
  obtain ⟨a, t, ht⟩ : ∃ (a : B) (t : p.primeCompl), Localization.mk a t = f (LocalizedModule.mk x 1) :=
    Localization.induction_on (f (LocalizedModule.mk x 1)) fun z => ⟨z.1, z.2, rfl⟩
  have key : LocalizedModule.mk x (1 : p.primeCompl) = LocalizedModule.mk (a • e) (t * s) := by
    rw [← f.symm_apply_apply (LocalizedModule.mk x 1), ← ht, ← mul_one (Localization.mk a t),
      ← smul_eq_mul, map_smul, ← he, LocalizedModule.mk_smul_mk]
  obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq).mp key
  refine ⟨(u : B) * ((t : B) * s), u * a, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem t.2 s.2)
  · simpa only [Submonoid.smul_def, Submonoid.coe_mul, OneMemClass.coe_one, one_smul, smul_smul] using hu

variable {B : Type} [CommRing B] in
private theorem tensorPow_equiv (c : Pic B) (n : ℕ) :
    Nonempty (Pic.AsModule (c ^ n) ≃ₗ[B] ⨂[B] _ : Fin n, Pic.AsModule c) := by
  induction n with
  | zero =>
    have ⟨e⟩ := Pic.ext_iff.mp (pow_zero c)
    have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
    exact ⟨e ≪≫ₗ g ≪≫ₗ (PiTensorProduct.isEmptyEquiv (Fin 0)).symm⟩
  | succ n ih =>
    obtain ⟨ih⟩ := ih
    have ⟨e1⟩ := Pic.ext_iff.mp (pow_succ c n)
    have ⟨e2⟩ := Pic.ext_iff.mp (Pic.mul_eq_tensor (c ^ n) c)
    exact ⟨e1 ≪≫ₗ e2 ≪≫ₗ Pic.mk.linearEquiv B _ ≪≫ₗ TensorProduct.congr ih
      (PiTensorProduct.subsingletonEquiv (R := B) (s := fun _ : Fin 1 => Pic.AsModule c) 0).symm ≪≫ₗ
      PiTensorProduct.tmulEquiv B (Pic.AsModule c) ≪≫ₗ PiTensorProduct.reindex B _ finSumFinEquiv⟩

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_form_of_pic_torsion :
    ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 →
      ∃ φ : (Π _ : Fin q, CommRing.Pic.AsModule c) →ₘₗ[B] B,
        ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := by
  intro B _ q c hc
  obtain ⟨T⟩ := tensorPow_equiv c q
  have ⟨e1⟩ := Pic.ext_iff.mp hc
  have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
  let ψ : (⨂[B] _ : Fin q, Pic.AsModule c) ≃ₗ[B] B := T.symm ≪≫ₗ e1 ≪≫ₗ g
  refine ⟨ψ.toLinearMap.compMultilinearMap (PiTensorProduct.tprod B), fun p hp => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin q → Pic.AsModule c, ψ (PiTensorProduct.tprod B x) ∉ p := by
    by_contra! h
    have hall : ∀ t, ψ t ∈ p := fun t => by
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r x => rw [map_smul, smul_eq_mul]; exact p.mul_mem_left r (h x)
      | add a b ha hb => rw [map_add (f := _)]; exact p.add_mem ha hb
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (by simpa using hall (ψ.symm 1)))
  obtain ⟨e, he⟩ := exists_local_generator (Pic.AsModule c) p
  choose w a hw hwa using fun i => he (x i)
  refine ⟨e, fun hmem => ?_⟩
  have hmem' : ψ (PiTensorProduct.tprod B fun _ => e) ∈ p := hmem
  have h1 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, w i) * ψ (PiTensorProduct.tprod B x) := by
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply, map_smul, smul_eq_mul]
  have h2 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, a i) * ψ (PiTensorProduct.tprod B (fun _ => e)) := by
    simp_rw [hwa]
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply, map_smul, smul_eq_mul]
  have hin : (∏ i, w i) * ψ (PiTensorProduct.tprod B x) ∈ p := by
    rw [← h1, h2]; exact p.mul_mem_left _ hmem'
  rcases hp.mem_or_mem hin with h | h
  · exact (p.primeCompl.prod_mem fun i _ => hw i) h
  · exact hx h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraFiniteProjectiveFaithfullyFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraFiniteProjectiveFaithfullyFlat
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerAlg

open MvPolynomial

theorem smul_comm_of_invertible {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (ψ : L →ₗ[B] B) (e ℓ : L) : ψ e • ℓ = ψ ℓ • e := by
  let T : L ⊗[B] L →ₗ[B] L := TensorProduct.lift ((LinearMap.lsmul B L).compl₁₂ ψ LinearMap.id)
  have h := congrArg T (Module.Invertible.tmul_comm (R := B) (m₁ := e) (m₂ := ℓ))
  simpa [T] using h

variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

def intersection_update_fsHerm_neg_one (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) : L →ₗ[B] B :=
  φ.toLinearMap (fun _ => e) 0

theorem position_apply (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e ℓ : L) :
    intersection_update_fsHerm_neg_one φ e ℓ = φ (Function.update (fun _ => e) 0 ℓ) := rfl

theorem position_self (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) :
    intersection_update_fsHerm_neg_one φ e e = φ (fun _ => e) := by
  rw [position_apply, Function.update_eq_self]

theorem pow_mul_eq_mul_prod_position [Module.Invertible B L]
    (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) (ℓ : Fin (q + 1) → L) :
    φ (fun _ => e) ^ (q + 1) * φ ℓ = φ (fun _ => e) * ∏ i, intersection_update_fsHerm_neg_one φ e (ℓ i) := by
  have h1 : φ (fun i => φ (fun _ => e) • ℓ i) = φ (fun _ => e) ^ (q + 1) * φ ℓ := by
    rw [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, RingHom.id_apply]
  have h2 : φ (fun i => intersection_update_fsHerm_neg_one φ e (ℓ i) • e) = (∏ i, intersection_update_fsHerm_neg_one φ e (ℓ i)) * φ (fun _ => e) := by
    simp only [MultilinearMap.map_smul_univ, smul_eq_mul, RingHom.id_apply]
  have h3 : (fun i => φ (fun _ => e) • ℓ i) = (fun i => intersection_update_fsHerm_neg_one φ e (ℓ i) • e) := by
    funext i
    rw [← position_self φ e]
    exact smul_comm_of_invertible (intersection_update_fsHerm_neg_one φ e) e (ℓ i)
  rw [← h1, h3, h2, mul_comm]

theorem algebraMap_mul_gen (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e ℓ : L) :
    algebraMap B (Alg φ) (φ (fun _ => e)) * gen φ ℓ =
      algebraMap B (Alg φ) (intersection_update_fsHerm_neg_one φ e ℓ) * gen φ e := by
  have hA := prod_gen φ (fun _ => e)
  have hB := prod_gen φ (Function.update (fun _ => e) 0 ℓ)
  rw [Fin.prod_univ_succ] at hA hB
  simp only [Function.update_self, ne_eq, Fin.succ_ne_zero, not_false_eq_true,
    Function.update_of_ne] at hB
  rw [position_apply, ← hB, ← hA]
  ring

end GlobalTheory.KummerAlg

namespace GlobalTheory.KummerAlg
open MvPolynomial
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

theorem algHom_ext_of_isUnit (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L)
    {R : Type} [CommRing R] [Algebra B R] (hu : IsUnit (algebraMap B R (φ (fun _ => e))))
    {g₁ g₂ : Alg φ →ₐ[B] R} (h : g₁ (gen φ e) = g₂ (gen φ e)) : g₁ = g₂ := by
  refine Ideal.Quotient.algHom_ext B (MvPolynomial.algHom_ext fun ℓ => ?_)
  change g₁ (gen φ ℓ) = g₂ (gen φ ℓ)
  have k₁ := congrArg g₁ (algebraMap_mul_gen φ e ℓ)
  have k₂ := congrArg g₂ (algebraMap_mul_gen φ e ℓ)
  simp only [map_mul, AlgHom.commutes] at k₁ k₂
  apply hu.mul_left_cancel
  rw [k₁, k₂, h]

def liftRoot [Module.Invertible B L] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L)
    {R : Type} [CommRing R] [Algebra B R] (hu : IsUnit (algebraMap B R (φ (fun _ => e))))
    (x : R) (hx : x ^ (q + 1) = algebraMap B R (φ (fun _ => e))) : Alg φ →ₐ[B] R :=
  Ideal.Quotient.liftₐ (ideal φ)
    (MvPolynomial.aeval fun ℓ => algebraMap B R (intersection_update_fsHerm_neg_one φ e ℓ) * ↑hu.unit⁻¹ * x) <| by
    intro a ha
    have hle : ideal φ ≤ RingHom.ker (MvPolynomial.aeval (R := B) fun ℓ : L =>
        algebraMap B R (intersection_update_fsHerm_neg_one φ e ℓ) * ↑hu.unit⁻¹ * x) := ?_
    · exact hle ha
    refine Ideal.span_le.2 ?_
    rintro r ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨c, a⟩, rfl⟩) | ⟨ℓ, rfl⟩)
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, aeval_X, map_add]
      ring
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, map_mul, aeval_X, aeval_C, map_smul, smul_eq_mul]
      ring
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, map_prod, aeval_X, aeval_C]
      rw [sub_eq_zero, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hx]
      have key := congrArg (algebraMap B R) (pow_mul_eq_mul_prod_position φ e ℓ)
      simp only [map_mul, map_pow, map_prod] at key
      set u := hu.unit
      have hu' : (u : R) = algebraMap B R (φ (fun _ => e)) := rfl
      rw [← hu'] at key ⊢
      have hv : (↑u⁻¹ : R) ^ (q + 1) * (u : R) ^ (q + 1) = 1 := by
        rw [← mul_pow, Units.inv_mul, one_pow]
      apply (u ^ (q + 1)).isUnit.mul_right_cancel
      rw [Units.val_pow_eq_pow_val]
      calc (∏ i, algebraMap B R (intersection_update_fsHerm_neg_one φ e (ℓ i))) * ↑u⁻¹ ^ (q + 1) * ↑u * ↑u ^ (q + 1)
          = (↑u * ∏ i, algebraMap B R (intersection_update_fsHerm_neg_one φ e (ℓ i))) * (↑u⁻¹ ^ (q + 1) * ↑u ^ (q + 1)) := by ring
        _ = algebraMap B R (φ ℓ) * ↑u ^ (q + 1) := by rw [hv, mul_one, ← key]; ring

theorem liftRoot_gen [Module.Invertible B L] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B)
    (e : L) {R : Type} [CommRing R] [Algebra B R] (hu : IsUnit (algebraMap B R (φ (fun _ => e))))
    (x : R) (hx : x ^ (q + 1) = algebraMap B R (φ (fun _ => e))) :
    liftRoot φ e hu x hx (gen φ e) = x := by
  have h0 : liftRoot φ e hu x hx (gen φ e) =
      MvPolynomial.aeval (fun ℓ => algebraMap B R (intersection_update_fsHerm_neg_one φ e ℓ) * ↑hu.unit⁻¹ * x) (X e) := rfl
  rw [h0, aeval_X, position_self]
  have : algebraMap B R (φ (fun _ => e)) * ↑hu.unit⁻¹ = 1 := by
    exact hu.mul_val_inv
  rw [this, one_mul]

end GlobalTheory.KummerAlg

namespace GlobalTheory.KummerAlg
open MvPolynomial
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

theorem smul_top_ne_top [Module.Invertible B L]
    (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (m : Ideal B) [hm : m.IsMaximal]
    (e : L) (he : φ (fun _ => e) ∉ m) : m • (⊤ : Submodule B (Alg φ)) ≠ ⊤ := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  let K := AlgebraicClosure (B ⧸ m)
  have hK : ∀ b : B, algebraMap B K b = algebraMap (B ⧸ m) K (Ideal.Quotient.mk m b) := fun b =>
    IsScalarTower.algebraMap_apply B (B ⧸ m) K b
  have hu : IsUnit (algebraMap B K (φ (fun _ => e))) := by
    rw [hK, isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (algebraMap (B ⧸ m) K).injective,
      Ideal.Quotient.eq_zero_iff_mem]
    exact he
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap B K (φ (fun _ => e)))
    (Nat.succ_pos q)
  let g := liftRoot φ e hu x hx
  intro htop
  have hle : m • (⊤ : Submodule B (Alg φ)) ≤ Submodule.comap g.toLinearMap ⊥ := by
    refine Submodule.smul_le.2 fun r hr n _ => ?_
    rw [Submodule.mem_comap, Submodule.mem_bot, AlgHom.toLinearMap_apply, map_smul,
      Algebra.smul_def, hK, (Ideal.Quotient.eq_zero_iff_mem).2 hr, map_zero, zero_mul]
  have h1 : (1 : Alg φ) ∈ Submodule.comap g.toLinearMap ⊥ := hle (by rw [htop]; exact Submodule.mem_top)
  simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_one, Submodule.mem_bot] at h1
  exact one_ne_zero h1

def awayEquiv [Module.Invertible B L] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) :
    Localization.Away (φ (fun _ => e)) ⊗[B] Alg φ ≃ₐ[Localization.Away (φ (fun _ => e))]
      AdjoinRoot (Polynomial.X ^ (q + 1) - Polynomial.C
        (algebraMap B (Localization.Away (φ (fun _ => e))) (φ (fun _ => e)))) := by
  set f := φ (fun _ => e)
  set Bf := Localization.Away f
  set P : Polynomial Bf := Polynomial.X ^ (q + 1) - Polynomial.C (algebraMap B Bf f)
  set A := AdjoinRoot P
  set T := Bf ⊗[B] Alg φ
  have hfu : IsUnit (algebraMap B Bf f) := IsLocalization.Away.algebraMap_isUnit f
  have huA : IsUnit (algebraMap B A f) := by
    rw [IsScalarTower.algebraMap_apply B Bf A]; exact hfu.map _
  have huT : IsUnit (algebraMap B T f) := by
    rw [IsScalarTower.algebraMap_apply B Bf T]; exact hfu.map _
  have hxA : AdjoinRoot.root P ^ (q + 1) = algebraMap B A f := by
    have h := AdjoinRoot.eval₂_root P
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    rw [IsScalarTower.algebraMap_apply B Bf A]
    exact sub_eq_zero.1 h
  have hxT : P.eval₂ (algebraMap Bf T) ((1 : Bf) ⊗ₜ[B] gen φ e : T) = 0 := by
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    rw [sub_eq_zero, Algebra.TensorProduct.tmul_pow, one_pow, ← IsScalarTower.algebraMap_apply,
      ← Algebra.TensorProduct.includeRight.commutes]
    congr 1
    have := prod_gen φ (fun _ => e)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  let fwd : T →ₐ[Bf] A := Algebra.TensorProduct.lift (Algebra.ofId Bf A)
    (liftRoot φ e huA (AdjoinRoot.root P) hxA) (fun _ _ => Commute.all _ _)
  let bwd : A →ₐ[Bf] T := AdjoinRoot.liftAlgHom P (Algebra.ofId Bf T) ((1 : Bf) ⊗ₜ[B] gen φ e) hxT
  have hf : fwd ((1 : Bf) ⊗ₜ[B] gen φ e) = AdjoinRoot.root P := by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact liftRoot_gen φ e huA _ hxA
  have hb : bwd (AdjoinRoot.root P) = (1 : Bf) ⊗ₜ[B] gen φ e := AdjoinRoot.liftAlgHom_root _ _ _ _
  refine AlgEquiv.ofAlgHom fwd bwd ?_ ?_
  · exact AdjoinRoot.algHom_ext (by simp only [AlgHom.comp_apply, hb, hf, AlgHom.id_apply])
  · refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    exact algHom_ext_of_isUnit φ e huT (by
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
        hf, hb, AlgHom.id_apply])

theorem away_finite_projective [Module.Invertible B L]
    (φ : MultilinearMap (RingHom.id B) (fun _ : Fin (q + 1) => L) B) (e : L) :
    Module.Finite (Localization.Away (φ (fun _ => e))) (Localization.Away (φ (fun _ => e)) ⊗[B] Alg φ) ∧
    Module.Projective (Localization.Away (φ (fun _ => e))) (Localization.Away (φ (fun _ => e)) ⊗[B] Alg φ) := by
  set Bf := Localization.Away (φ (fun _ => e))
  have hmon : (Polynomial.X ^ (q + 1) - Polynomial.C (algebraMap B Bf (φ (fun _ => e)))).Monic :=
    Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero q)
  let pb := AdjoinRoot.powerBasis' hmon
  haveI := Module.Free.of_basis pb.basis
  haveI := Module.Finite.of_basis pb.basis
  let eq := (awayEquiv φ e).toLinearEquiv
  exact ⟨Module.Finite.equiv eq.symm, Module.Projective.of_equiv eq.symm⟩

end GlobalTheory.KummerAlg

namespace GlobalTheory.KummerAlg

theorem finite_projective_faithfullyFlat : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L]
    [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B),
    0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) →
    Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧
      Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := by
  intro B _ L _ _ _ q φ hq hφ
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  let s : Set B := Set.range (fun e : L => φ (fun _ => e))
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨e, he⟩ := hφ m hm.isPrime
    exact he (hsm (Ideal.subset_span ⟨e, rfl⟩))
  let F : s → Type := fun g => Localization.Away g.1 ⊗[B] Alg φ
  let ϕ : ∀ g : s, Alg φ →ₗ[B] F g := fun g => TensorProduct.mk B (Localization.Away g.1) (Alg φ) 1
  have hfp : ∀ g : s, Module.Finite (Localization.Away g.1) (F g) ∧
      Module.Projective (Localization.Away g.1) (F g) := by
    rintro ⟨_, e, rfl⟩
    exact away_finite_projective φ e
  haveI (g : s) : Module.Finite (Localization.Away g.1) (F g) := (hfp g).1
  haveI (g : s) : Module.Projective (Localization.Away g.1) (F g) := (hfp g).2
  haveI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (ϕ g) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.1) (Localization.Away g.1) (ϕ g)).2
      (TensorProduct.isBaseChange B (Alg φ) (Localization.Away g.1))
  haveI (g : s) : Module.Flat B (F g) := by
    haveI : Module.Flat B (Localization.Away g.1) := IsLocalization.flat _ (Submonoid.powers g.1)
    haveI : Module.Flat (Localization.Away g.1) (F g) := Module.Flat.of_projective
    exact Module.Flat.trans B (Localization.Away g.1) (F g)
  haveI : Module.FinitePresentation B (Alg φ) :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat B (Alg φ) :=
    Module.flat_of_isLocalized_span B (Alg φ) s hs F ϕ fun _ => inferInstance
  refine ⟨inferInstance, Module.Flat.projective_of_finitePresentation, ?_⟩
  constructor
  intro m hm
  obtain ⟨e, he⟩ := hφ m hm.isPrime
  exact smul_top_ne_top φ m e he

end GlobalTheory.KummerAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraFiniteProjectiveFaithfullyFlatStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerAlgebra_finite_projective_faithfullyFlat : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), 0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := by
  first | exact @GlobalTheory.KummerAlg.finite_projective_faithfullyFlat | exact GlobalTheory.KummerAlg.finite_projective_faithfullyFlat | (intros; apply GlobalTheory.KummerAlg.finite_projective_faithfullyFlat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijective
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerTorsor

open GlobalTheory.KummerAlg

section
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {n : ℕ}
  (φ : (Π _ : Fin (n + 1), L) →ₘₗ[B] B)

theorem gen_pow (f : L) : gen φ f ^ (n + 1) = algebraMap B (Alg φ) (φ fun _ => f) := by
  rw [← prod_gen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem smul_gen (e f : L) :
    (φ fun _ => f) • gen φ e = φ (Fin.cons e (fun _ => f) : Fin (n + 1) → L) • gen φ f := by
  rw [Algebra.smul_def, Algebra.smul_def, ← gen_pow, ← prod_gen, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem one_mem_span_pow (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) (k : ℕ) :
    (1 : B) ∈ Submodule.span B (Set.range fun f : L => (φ fun _ => f) ^ k) := by
  have : Ideal.span (Set.range fun f : L => (φ fun _ => f) ^ k) = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf⟩ := hφ p hp.isPrime
    exact hf (hp.isPrime.mem_of_pow_mem _ (hle (Ideal.subset_span ⟨f, rfl⟩)))
  change (1 : B) ∈ Ideal.span _
  rw [this]; exact Submodule.mem_top

theorem swap (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) (e ℓ : L) :
    (gen φ e ⊗ₜ[B] gen φ ℓ : Alg φ ⊗[B] Alg φ) = gen φ ℓ ⊗ₜ gen φ e := by
  have key : ∀ f a b : L, ((φ fun _ => f) ^ 2) • (gen φ a ⊗ₜ[B] gen φ b : Alg φ ⊗[B] Alg φ) =
      (φ (Fin.cons a (fun _ => f) : Fin (n + 1) → L) *
        φ (Fin.cons b (fun _ => f) : Fin (n + 1) → L)) • (gen φ f ⊗ₜ[B] gen φ f) := by
    intro f a b
    rw [pow_two, ← TensorProduct.smul_tmul_smul, smul_gen φ a f, smul_gen φ b f,
      TensorProduct.smul_tmul_smul]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (one_mem_span_pow φ hφ 2)
  rw [← sub_eq_zero, ← one_smul B (_ - _), ← hc, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_eq_zero fun f _ => ?_
  rw [smul_assoc, smul_sub, key, key, mul_comm (φ _), sub_self, smul_zero]

theorem one_tmul_algebraMap (r : B) :
    (1 : Alg φ) ⊗ₜ[B] algebraMap B (Alg φ) r = algebraMap B (Alg φ ⊗[B] Alg φ) r := by
  rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r, TensorProduct.tmul_smul,
    Algebra.TensorProduct.one_def]

theorem algebraMap_tmul_one (r : B) :
    algebraMap B (Alg φ) r ⊗ₜ[B] (1 : Alg φ) = algebraMap B (Alg φ ⊗[B] Alg φ) r := by
  rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r,
    ← TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

def T (c : L →₀ B) (j : ℕ) : Alg φ ⊗[B] Alg φ :=
  c.sum fun f a => a • ((gen φ f ^ (n + 1 - j)) ⊗ₜ[B] (gen φ f ^ j))

theorem T_zero (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) : T φ c 0 = 1 := by
  rw [← map_one (algebraMap B (Alg φ ⊗[B] Alg φ)), ← hc, map_finsuppSum, T]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [Nat.sub_zero, pow_zero, gen_pow, algebraMap_tmul_one, smul_eq_mul, map_mul, Algebra.smul_def]

theorem T_top (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) : T φ c (n + 1) = 1 := by
  rw [← map_one (algebraMap B (Alg φ ⊗[B] Alg φ)), ← hc, map_finsuppSum, T]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [Nat.sub_self, pow_zero, gen_pow, one_tmul_algebraMap, smul_eq_mul, map_mul, Algebra.smul_def]

end

section
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {n : ℕ}
  (φ : (Π _ : Fin (n + 1), L) →ₘₗ[B] B)

theorem T_shift
    (hsw : ∀ e ℓ : L, (gen φ e ⊗ₜ[B] gen φ ℓ : Alg φ ⊗[B] Alg φ) = gen φ ℓ ⊗ₜ gen φ e)
    (c : L →₀ B) (ℓ : L) (j : ℕ) (hj : j ≤ n) :
    T φ c j * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ) = T φ c (j + 1) * (gen φ ℓ ⊗ₜ[B] (1 : Alg φ)) := by
  simp only [T, Finsupp.sum, Finset.sum_mul, smul_mul_assoc]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  have h1 : n + 1 - j = (n - j) + 1 := by omega
  have h2 : n + 1 - (j + 1) = n - j := by omega
  calc (gen φ f ^ (n + 1 - j)) ⊗ₜ[B] (gen φ f ^ j) * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ)
      = ((gen φ f ^ (n - j)) ⊗ₜ[B] (gen φ f ^ j)) * (gen φ f ⊗ₜ[B] gen φ ℓ) := by
        rw [h1, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          pow_succ, mul_one]
    _ = ((gen φ f ^ (n - j)) ⊗ₜ[B] (gen φ f ^ j)) * (gen φ ℓ ⊗ₜ[B] gen φ f) := by rw [hsw]
    _ = _ := by
        rw [h2, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          pow_succ, mul_one]

def ev (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) :
    Alg φ ⊗[B] Alg φ →ₐ[B] Alg φ :=
  Algebra.TensorProduct.productMap (AlgHom.id B (Alg φ)) (act φ ζ hζ g).toAlgHom

theorem ev_tmul (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) (a b : Alg φ) :
    ev φ ζ hζ g (a ⊗ₜ b) = a * act φ ζ hζ g b := rfl

theorem act_gen' (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) (f : L) :
    act φ ζ hζ g (gen φ f) = tw ζ g.toAdd • gen φ f :=
  act_gen φ ζ hζ g.toAdd f

theorem kummerTensorEvalAction_powerRatio (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1)
    (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) (j : ℕ) (hj : j ≤ n + 1) :
    ev φ ζ hζ g (T φ c j) = algebraMap B (Alg φ) (tw ζ g.toAdd ^ j) := by
  rw [T, map_finsuppSum]
  calc (c.sum fun f a => ev φ ζ hζ g (a • ((gen φ f ^ (n + 1 - j)) ⊗ₜ[B] (gen φ f ^ j))))
      = c.sum (fun f a => algebraMap B (Alg φ) (tw ζ g.toAdd ^ j * (a • φ fun _ => f))) := by
        refine Finsupp.sum_congr fun f _ => ?_
        rw [map_smul, ev_tmul, map_pow, act_gen', smul_pow, mul_smul_comm, ← pow_add,
          Nat.sub_add_cancel hj, gen_pow, smul_eq_mul, map_mul, map_mul, Algebra.smul_def,
          Algebra.smul_def, mul_left_comm]
    _ = algebraMap B (Alg φ) (tw ζ g.toAdd ^ j * c.sum fun f a => a • φ fun _ => f) := by
        rw [Finsupp.mul_sum, map_finsuppSum]
    _ = _ := by rw [hc, mul_one]

theorem geom_zero (z : B) (hz : z ^ (n + 1) = 1) (hu : IsUnit (1 - z)) :
    ∑ i ∈ Finset.range (n + 1), z ^ i = 0 := by
  have h := geom_sum_mul z (n + 1)
  rw [hz, sub_self] at h
  have hu' : IsUnit (z - 1) := by rw [← neg_sub]; exact hu.neg
  exact hu'.mul_left_eq_zero.1 h

theorem shift_sum {M : Type} [AddCommGroup M] [Module B M] (v w : B) (hvw : w * v = 1)
    (hw : w ^ (n + 1) = 1) (A : ℕ → M) (hA : A (n + 1) = A 0) :
    ∑ j ∈ Finset.range (n + 1), w ^ j • A (j + 1) =
      ∑ j ∈ Finset.range (n + 1), (w ^ j * v) • A j := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun j => (w ^ j * v) • A j), hA]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ, mul_assoc, hvw, mul_one]
  · rw [pow_zero, one_mul]
    congr 1
    calc w ^ n = w ^ n * (w * v) := by rw [hvw, mul_one]
      _ = w ^ (n + 1) * v := by ring
      _ = v := by rw [hw, one_mul]

def E (c : L →₀ B) (s w : B) : Alg φ ⊗[B] Alg φ :=
  s • ∑ j ∈ Finset.range (n + 1), w ^ j • T φ c j

theorem ext_gen (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1)))
    (X : Alg φ ⊗[B] Alg φ)
    (hX : ∀ ℓ, X * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ) = X * (act φ ζ hζ g (gen φ ℓ) ⊗ₜ[B] (1 : Alg φ)))
    (b : Alg φ) : X * ((1 : Alg φ) ⊗ₜ[B] b) = X * (act φ ζ hζ g b ⊗ₜ[B] (1 : Alg φ)) := by
  have hm : ∀ a d : Alg φ, (a * d) ⊗ₜ[B] (1 : Alg φ) = (a ⊗ₜ[B] (1 : Alg φ)) * (d ⊗ₜ[B] 1) := by
    intro a d; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h1 : ∀ a d : Alg φ, (1 : Alg φ) ⊗ₜ[B] (a * d) = ((1 : Alg φ) ⊗ₜ[B] a) * (1 ⊗ₜ[B] d) := by
    intro a d; rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on
  next r =>
    rw [← algebraMap_eq_mk, AlgEquiv.commutes, one_tmul_algebraMap, algebraMap_tmul_one]
  next p p' hp hp' =>
    rw [map_add (f := _), map_add (f := _), TensorProduct.tmul_add, TensorProduct.add_tmul, mul_add, mul_add, hp, hp']
  next p ℓ hp =>
    have : Ideal.Quotient.mk (ideal φ) (p * MvPolynomial.X ℓ) =
        Ideal.Quotient.mk (ideal φ) p * gen φ ℓ := by rw [map_mul]; rfl
    rw [this, map_mul, hm, h1]
    calc X * (((1 : Alg φ) ⊗ₜ[B] Ideal.Quotient.mk (ideal φ) p) * (1 ⊗ₜ[B] gen φ ℓ))
        = (X * ((1 : Alg φ) ⊗ₜ[B] Ideal.Quotient.mk (ideal φ) p)) * (1 ⊗ₜ[B] gen φ ℓ) :=
          (mul_assoc _ _ _).symm
      _ = (X * (act φ ζ hζ g (Ideal.Quotient.mk (ideal φ) p) ⊗ₜ[B] (1 : Alg φ))) *
            (1 ⊗ₜ[B] gen φ ℓ) := by rw [hp]
      _ = (act φ ζ hζ g (Ideal.Quotient.mk (ideal φ) p) ⊗ₜ[B] (1 : Alg φ)) *
            (X * (1 ⊗ₜ[B] gen φ ℓ)) := by ring
      _ = (act φ ζ hζ g (Ideal.Quotient.mk (ideal φ) p) ⊗ₜ[B] (1 : Alg φ)) *
            (X * (act φ ζ hζ g (gen φ ℓ) ⊗ₜ[B] (1 : Alg φ))) := by rw [hX]
      _ = _ := by ring

end

section
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {n : ℕ}
  (φ : (Π _ : Fin (n + 1), L) →ₘₗ[B] B)

theorem tw_neg_mul (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g h : ZMod (n + 1)) :
    tw ζ (-h) * tw ζ g = tw ζ (g - h) := by
  rw [← tw_add hζ, sub_eq_neg_add]

theorem E_gen
    (hsw : ∀ e ℓ : L, (gen φ e ⊗ₜ[B] gen φ ℓ : Alg φ ⊗[B] Alg φ) = gen φ ℓ ⊗ₜ gen φ e)
    (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) (s : B)
    (ζ : B) (hζ : ζ ^ (n + 1) = 1) (g : Multiplicative (ZMod (n + 1))) (ℓ : L) :
    E φ c s (tw ζ (-g.toAdd)) * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ) =
      E φ c s (tw ζ (-g.toAdd)) * (act φ ζ hζ g (gen φ ℓ) ⊗ₜ[B] (1 : Alg φ)) := by
  have hvw : tw ζ (-g.toAdd) * tw ζ g.toAdd = 1 := by
    rw [tw_neg_mul ζ hζ, sub_self, tw_zero]
  rw [act_gen', ← TensorProduct.smul_tmul', E, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [Finset.sum_mul, Finset.sum_mul, Finset.smul_sum]
  have h1 : ∀ j ∈ Finset.range (n + 1), (tw ζ (-g.toAdd) ^ j • T φ c j) * ((1 : Alg φ) ⊗ₜ[B] gen φ ℓ)
      = tw ζ (-g.toAdd) ^ j • (T φ c (j + 1) * (gen φ ℓ ⊗ₜ[B] (1 : Alg φ))) := by
    intro j hj
    rw [smul_mul_assoc, T_shift φ hsw c ℓ j (by simp at hj; omega)]
  rw [Finset.sum_congr rfl h1, shift_sum (tw ζ g.toAdd) (tw ζ (-g.toAdd)) hvw (tw_pow hζ _)
    (fun j => T φ c j * (gen φ ℓ ⊗ₜ[B] (1 : Alg φ))) (by simp only [T_top φ c hc, T_zero φ c hc])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, smul_smul, mul_comm]

theorem sum_tw_pow (ζ : B) (hζ : ζ ^ (n + 1) = 1)
    (hk : ∀ k : ℕ, 0 < k → k < n + 1 → IsUnit (1 - ζ ^ k)) (j : ℕ) (hj : j < n + 1) :
    ∑ h : Multiplicative (ZMod (n + 1)), tw ζ (-h.toAdd) ^ j = if j = 0 then ((n + 1 : ℕ) : B) else 0 := by
  rw [Fintype.sum_equiv (Multiplicative.toAdd.trans (Equiv.neg (ZMod (n + 1))))
    (fun h => tw ζ (-h.toAdd) ^ j) (fun k => (ζ ^ j) ^ k.val) (fun h => by
      simp only [Equiv.trans_apply, Equiv.neg_apply, tw, ← pow_mul, mul_comm])]
  have : ∑ k : ZMod (n + 1), (ζ ^ j) ^ k.val = ∑ i ∈ Finset.range (n + 1), (ζ ^ j) ^ i := by
    rw [Finset.sum_range]; rfl
  rw [this]
  split_ifs with h0
  · subst h0; simp
  · refine geom_zero (ζ ^ j) ?_ (hk j (Nat.pos_of_ne_zero h0) hj)
    rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem sum_E (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) (s : B)
    (hs : s * ((n + 1 : ℕ) : B) = 1) (ζ : B) (hζ : ζ ^ (n + 1) = 1)
    (hk : ∀ k : ℕ, 0 < k → k < n + 1 → IsUnit (1 - ζ ^ k)) :
    ∑ h : Multiplicative (ZMod (n + 1)), E φ c s (tw ζ (-h.toAdd)) = 1 := by
  simp only [E]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single 0]
  · rw [sum_tw_pow ζ hζ hk 0 (Nat.succ_pos n), if_pos rfl, T_zero φ c hc, smul_smul, hs, one_smul]
  · intro j hj hj0
    rw [sum_tw_pow ζ hζ hk j (Finset.mem_range.1 hj), if_neg hj0, zero_smul]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h

theorem ev_E (c : L →₀ B) (hc : (c.sum fun f a => a • φ fun _ => f) = 1) (s : B)
    (hs : s * ((n + 1 : ℕ) : B) = 1) (ζ : B) (hζ : ζ ^ (n + 1) = 1)
    (hk : ∀ k : ℕ, 0 < k → k < n + 1 → IsUnit (1 - ζ ^ k))
    (g h : Multiplicative (ZMod (n + 1))) :
    ev φ ζ hζ g (E φ c s (tw ζ (-h.toAdd))) = if g = h then 1 else 0 := by
  have h1 : ev φ ζ hζ g (E φ c s (tw ζ (-h.toAdd))) = algebraMap B (Alg φ)
      (s * ∑ j ∈ Finset.range (n + 1), tw ζ (g.toAdd - h.toAdd) ^ j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [E, map_smul, map_sum, Finset.mul_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_smul, kummerTensorEvalAction_powerRatio φ c hc ζ hζ g j (by simp at hj; omega), ← tw_neg_mul ζ hζ, mul_pow,
      Algebra.smul_def, Algebra.smul_def, map_mul, map_mul]
  rw [h1]
  split_ifs with hgh
  · subst hgh
    simp only [sub_self, tw_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    rw [hs, map_one]
  · have hne : g.toAdd - h.toAdd ≠ 0 := by
      intro h0; exact hgh (Multiplicative.toAdd.injective (sub_eq_zero.1 h0))
    rw [geom_zero (tw ζ (g.toAdd - h.toAdd)) (tw_pow hζ _)
      (hk _ ((ZMod.val_pos).2 hne) (ZMod.val_lt _)), mul_zero, map_zero]

end

section
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {n : ℕ}
  (φ : (Π _ : Fin (n + 1), L) →ₘₗ[B] B)

theorem bijective_succ (hq : IsUnit ((n + 1 : ℕ) : B))
    (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) (ζ : B) (hζ : ζ ^ (n + 1) = 1)
    (hk : ∀ k : ℕ, 0 < k → k < n + 1 → IsUnit (1 - ζ ^ k)) :
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ) (fun _ => AlgHom.id B (Alg φ)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ)
        (fun g => (act φ ζ hζ g).toAlgHom))) := by
  set Φ := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ) (fun _ => AlgHom.id B (Alg φ)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod (n + 1)) => Alg φ)
        (fun g => (act φ ζ hζ g).toAlgHom)) with hΦ
  have hΦev : ∀ t g, Φ t g = ev φ ζ hζ g t := by
    intro t g
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), Pi.add_apply, hx, hy]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (one_mem_span_pow φ hφ 1)
  simp only [pow_one] at hc
  have hsw := swap φ hφ
  set s : B := ((hq.unit⁻¹ : Bˣ) : B) with hs_def
  have hs : s * ((n + 1 : ℕ) : B) = 1 := hq.val_inv_mul
  set Eh : Multiplicative (ZMod (n + 1)) → Alg φ ⊗[B] Alg φ :=
    fun h => E φ c s (tw ζ (-h.toAdd)) with hEh
  have hsum : ∑ h, Eh h = 1 := sum_E φ c hc s hs ζ hζ hk
  have hEb : ∀ h b, Eh h * ((1 : Alg φ) ⊗ₜ[B] b) = Eh h * (act φ ζ hζ h b ⊗ₜ[B] (1 : Alg φ)) :=
    fun h b => ext_gen φ ζ hζ h (Eh h) (E_gen φ hsw c hc s ζ hζ h) b
  let ψ : (Multiplicative (ZMod (n + 1)) → Alg φ) → Alg φ ⊗[B] Alg φ :=
    fun d => ∑ h, Eh h * (d h ⊗ₜ[B] (1 : Alg φ))
  have hψadd : ∀ d d', ψ (d + d') = ψ d + ψ d' := by
    intro d d'
    simp only [ψ, Pi.add_apply, TensorProduct.add_tmul, mul_add, Finset.sum_add_distrib]
  refine Function.bijective_iff_has_inverse.2 ⟨ψ, ?_, ?_⟩
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [ψ]
    | tmul a b =>
      have hab : ∀ h, Φ (a ⊗ₜ b) h = a * act φ ζ hζ h b := fun h => rfl
      calc ψ (Φ (a ⊗ₜ b)) = ∑ h, Eh h * ((a * act φ ζ hζ h b) ⊗ₜ[B] (1 : Alg φ)) := by
            simp only [ψ, hab]
        _ = ∑ h, (a ⊗ₜ[B] (1 : Alg φ)) * (Eh h * (act φ ζ hζ h b ⊗ₜ[B] (1 : Alg φ))) := by
            refine Finset.sum_congr rfl fun h _ => ?_
            rw [← mul_one (1 : Alg φ), ← Algebra.TensorProduct.tmul_mul_tmul]; ring_nf
        _ = ∑ h, (a ⊗ₜ[B] (1 : Alg φ)) * (Eh h * ((1 : Alg φ) ⊗ₜ[B] b)) := by
            simp only [hEb]
        _ = (a ⊗ₜ[B] (1 : Alg φ)) * ((1 : Alg φ) ⊗ₜ[B] b) * ∑ h, Eh h := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun h _ => ?_; ring
        _ = a ⊗ₜ b := by rw [hsum, mul_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add (f := _), hψadd, hx, hy]
  · intro d
    funext g
    rw [hΦev]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ψ, map_sum, map_mul, ev_tmul, map_one, mul_one, hEh,
      ev_E φ c hc s hs ζ hζ hk, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]

end

theorem bijective : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : (Π _ : Fin q, L) →ₘₗ[B] B),
    IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) →
    ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) →
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ)
        (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ)))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ)
        (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := by
  intro B _ L _ _ _ q _ φ hq hφ ζ hζ hk
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos q)).symm⟩
  exact bijective_succ φ hq hφ ζ hζ hk

end GlobalTheory.KummerTorsor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraZmodTorsorBijectiveStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := by
  first | exact @GlobalTheory.KummerTorsor.bijective | exact GlobalTheory.KummerTorsor.bijective | (intros; apply GlobalTheory.KummerTorsor.bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardTorsionTrivialOfTorsorsHaveSections
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerStep

open GlobalTheory.KummerAlg

theorem p1 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), 0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := GlobalTheory.T.kummerAlgebra_finite_projective_faithfullyFlat
theorem p2 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective
theorem p4 : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 → ∃ φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => CommRing.Pic.AsModule c) B, ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := GlobalTheory.T.exists_multilinear_form_of_pic_torsion

theorem free_of_section (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B) (hq : 0 < q)
    (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p)
    (s : Alg φ →ₐ[B] B) : Module.Free B L := by
  let f : L →ₗ[B] B := s.toLinearMap ∘ₗ gen φ
  have hf : ∀ e : L, f e ^ q = φ (fun _ => e) := fun e => by
    have := congrArg s (prod_gen φ (fun _ => e))
    simpa [f, map_prod, Finset.prod_const, AlgHom.commutes] using this
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (LinearMap.range f) h
    obtain ⟨e, he⟩ := hφ m hm.isPrime
    apply he
    rw [← hf e]
    exact Ideal.pow_mem_of_mem _ (hle ⟨e, rfl⟩) q hq
  exact Module.Free.of_equiv
    (LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hsurj)).symm

theorem kummer_step : ∀ (B : Type) [CommRing B] (q : ℕ), 0 < q → IsUnit (q : B) →
    (∃ ζ : B, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) →
    (∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
      Module.FaithfullyFlat B D → ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
      Function.Bijective (Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) → Nonempty (D →ₐ[B] B)) →
    ∀ c : CommRing.Pic B, c ^ q = 1 → c = 1 := by
  intro B _ q hq hqu ⟨ζ, hζ, hζk⟩ hT c hc
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨φ, hφ⟩ := p4 B q c hc
  obtain ⟨hfin, hproj, hff⟩ := p1 B (CommRing.Pic.AsModule c) q φ hq hφ
  obtain ⟨s⟩ := hT (Alg φ) hfin hproj hff (act φ ζ hζ) (p2 B (CommRing.Pic.AsModule c) q φ hqu hφ ζ hζ hζk)
  have := free_of_section B (CommRing.Pic.AsModule c) q φ hq hφ s
  rw [← CommRing.Pic.mk_eq_self (M := c), CommRing.Pic.mk_eq_one_iff_free]
  exact this

end GlobalTheory.KummerStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardTorsionTrivialOfTorsorsHaveSectionsStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picard_torsion_trivial_of_torsors_have_sections : ∀ (B : Type) [CommRing B] (q : ℕ), 0 < q → IsUnit (q : B) →
    (∃ ζ : B, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) →
    (∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
      Module.FaithfullyFlat B D → ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
      Function.Bijective (Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) → Nonempty (D →ₐ[B] B)) →
    ∀ c : CommRing.Pic B, c ^ q = 1 → c = 1 := by
  first | (exact @GlobalTheory.KummerStep.kummer_step) | (exact GlobalTheory.KummerStep.kummer_step) | (intros; apply GlobalTheory.KummerStep.kummer_step  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneIsUnitOneSubPow
namespace GlobalTheory

theorem exists_pow_eq_one_isUnit_one_sub_pow (T : Type) [CommRing T] [IsDomain T] (q : ℕ) (hq0 : 0 < q) (hq : IsUnit (q : T))
    (hT : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    ∃ ζ : T, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k) := by
  classical
  haveI : NeZero (q : T) := ⟨hq.ne_zero⟩
  obtain ⟨x, hx⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T)
    (by rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 hq0)
  have hprim : IsPrimitiveRoot x q := (Polynomial.isRoot_cyclotomic_iff).1 hx
  refine ⟨x, hprim.pow_eq_one, fun k hk hkq => ?_⟩
  set S := Polynomial.nthRootsFinset q (1 : T) with hS
  have h1S : (1 : T) ∈ S := (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (one_pow _)
  have hprod := Polynomial.X_pow_sub_one_eq_prod hq0 hprim
  rw [← Finset.mul_prod_erase S _ h1S] at hprod
  have hgeom : (Polynomial.X - Polynomial.C (1 : T)) * ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_1]; exact mul_geom_sum _ _
  have hne : (Polynomial.X - Polynomial.C (1 : T)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hcan : ∑ i ∈ Finset.range q, (Polynomial.X : Polynomial T) ^ i
      = ∏ ζ ∈ S.erase 1, (Polynomial.X - Polynomial.C ζ) :=
    mul_left_cancel₀ hne (hgeom.trans hprod)
  have hev := congrArg (Polynomial.eval (1 : T)) hcan
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_C] at hev
  have hmem : x ^ k ∈ S.erase 1 := by
    refine Finset.mem_erase.2 ⟨hprim.pow_ne_one_of_pos_of_lt hk.ne' hkq, ?_⟩
    exact (Polynomial.mem_nthRootsFinset hq0 (1 : T)).2 (by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow])
  have hdvd : (1 - x ^ k) ∣ (q : T) := hev ▸ Finset.dvd_prod_of_mem _ hmem
  exact isUnit_of_dvd_unit hdvd hq

end GlobalTheory
end

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pic_localization_strictHenselisation_no_torsion : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ c : CommRing.Pic (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))), c ^ q = 1 → c = 1 := by
  intro T O _ _ _ _ _ _ _ _ _ q hT hq hq0 hSi c hc
  obtain ⟨P, hP, φ, hφ, hsh⟩ := GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hSi
  haveI : IsLocalRing O := hsh.1.toIsLocalRing
  obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.exists_pow_eq_one_isUnit_one_sub_pow T q hq0 hq hT.2
  refine GlobalTheory.T.picard_torsion_trivial_of_torsors_have_sections _ q hq0 ?_ ⟨algebraMap T _ ζ, ?_, ?_⟩ ?_ c hc
  · simpa using hq.map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · rw [← map_pow, hζ, map_one]
  · intro k hk hkq
    simpa using (hζu k hk hkq).map (algebraMap T (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  · intro D _ _ h1 h2 h3 act hact
    exact GlobalTheory.LocAcyc.torsor_trivial T O hT.2 P φ hφ hsh q hq0 hq D h1 h2 h3 act hact

end GlobalTheory
