module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceTopEqKerSmulStatement
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul :
    ∀ (k : Type) [Field k] (C : Type) [CommRing C] (H : Type u) [AddCommGroup H]
      [Module k H] (σ : C →+* Module.End k H) (χ : C →+* k),
      letI : Module (k ⊗[ℤ] C) H := Module.compHom H
        (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
          (fun _ _ => Algebra.commutes _ _)).toRingHom;
      ∀ x : H, x ∈ GlobalTheory.HTRho.mSub σ χ ⊤ ↔
        x ∈ (RingHom.ker (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
          (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) • ⊤ : Submodule (k ⊗[ℤ] C) H) := by
  intro k _ C _ H _ _ σ χ
  let L := Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
    (fun _ _ => Algebra.commutes _ _)
  let φ := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
    (fun _ _ => Commute.all _ _)
  let : Module (k ⊗[ℤ] C) H := Module.compHom H L.toRingHom
  let X := GlobalTheory.HTRho.mSub σ χ ⊤
  let Y : Submodule (k ⊗[ℤ] C) H := RingHom.ker φ • ⊤
  change ∀ x : H, x ∈ X ↔ x ∈ Y
  have hsmul (a : k ⊗[ℤ] C) (y : H) : a • y = L a y := rfl
  have hL (l : k) (c : C) (y : H) : L (l ⊗ₜ c) y = l • σ c y := by
    exact congrArg (fun f : Module.End k H => f y)
      (Algebra.TensorProduct.lift_tmul (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
        (fun _ _ => Algebra.commutes _ _) l c)
  have hφ (l : k) (c : C) : φ (l ⊗ₜ c) = l * χ c := by
    simp [φ]
  have hSub (a : k ⊗[ℤ] C) (y : H) : L a y - φ a • y ∈ X := by
    induction a using TensorProduct.inductionOn with
    | tmul l c =>
      rw [hL, hφ, mul_smul, ← smul_sub]
      exact Submodule.smul_mem X l (Submodule.subset_span ⟨c, y, trivial, by simp⟩)
    | add a b ha hb =>
      rw [map_add L, map_add φ, LinearMap.add_apply, add_smul, add_sub_add_comm]
      exact add_mem ha hb
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, -, rfl⟩ := hz
      let a : k ⊗[ℤ] C := 1 ⊗ₜ c - χ c ⊗ₜ (1 : C)
      have ha : a ∈ RingHom.ker φ := by
        change φ a = 0
        simp [a, hφ]
      have hy : a • y ∈ Y := Submodule.smul_mem_smul ha (Submodule.mem_top (x := y))
      have hay : a • y = σ (algebraMap C C c) y - χ c • y := by
        rw [hsmul]
        simp [a, hL]
      exact hay ▸ hy
    | zero => exact Y.zero_mem
    | add a b _ _ ha hb => exact Y.add_mem ha hb
    | smul l z _ hz =>
      have hl : (l ⊗ₜ (1 : C) : k ⊗[ℤ] C) • z = l • z := by
        rw [hsmul, hL, map_one, one_apply_eq_self]
      exact hl ▸ Y.smul_mem _ hz
  · intro hx
    refine Submodule.smul_induction_on (show x ∈ RingHom.ker φ • ⊤ from hx) ?_ ?_
    · intro a ha y _
      rw [hsmul]
      simpa only [RingHom.mem_ker.mp ha, zero_smul, sub_zero] using hSub a y
    · intro a b ha hb
      exact X.add_mem ha hb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLocalOfCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLocalOfCharacter
open scoped TensorProduct
universe u

namespace GlobalTheory

theorem exists_idem_local_of_character :
    ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A]
      (φ : A →ₐ[k] k), ∃ e : A, IsIdempotentElem e ∧ φ e = 1 ∧
        ∀ a, φ a = 0 → IsNilpotent (e * a) := by
  intro k _ A _ _ _ φ
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  set m : Ideal A := RingHom.ker φ with hm
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := A) (M := A)
    ⟨fun n => OrderDual.toDual (m ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  have hst : ∀ j, n ≤ j → m ^ n = m ^ j := fun j hj => hn j hj
  set N := n + 1 with hN
  have hI : IsIdempotentElem (m ^ N) := by
    show m ^ N * m ^ N = m ^ N
    rw [← pow_add, ← hst (N + N) (by omega), hst N (by omega)]
  have hfg : (m ^ N).FG := IsNoetherian.noetherian _
  obtain ⟨f, hf, hIf⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).1 hI
  refine ⟨1 - f, hf.one_sub, ?_, ?_⟩
  · have hfm : f ∈ m := by
      have : f ∈ m ^ N := by rw [hIf]; exact Ideal.subset_span rfl
      exact Ideal.pow_le_self (by omega) this
    have : φ f = 0 := hfm
    simp [this]
  · intro a ha
    have ham : a ∈ m := ha
    have haN : a ^ N ∈ m ^ N := Ideal.pow_mem_pow ham N
    rw [hIf, Ideal.mem_span_singleton'] at haN
    obtain ⟨y, hy⟩ := haN
    refine ⟨N, ?_⟩
    rw [mul_pow, hf.one_sub.pow_succ_eq n, ← hy]
    have : (1 - f) * f = 0 := by rw [sub_mul, one_mul, hf.eq, sub_self]
    calc (1 - f) * (y * f) = y * ((1 - f) * f) := by ring
      _ = 0 := by rw [this, mul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLocalOfCharacterStatement
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_local_of_character : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k), ∃ e : A, IsIdempotentElem e ∧ φ e = 1 ∧ ∀ a, φ a = 0 → IsNilpotent (e * a) := by
  first | (exact @GlobalTheory.exists_idem_local_of_character) | (exact GlobalTheory.exists_idem_local_of_character) | (intros; apply GlobalTheory.exists_idem_local_of_character <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceIffIdempotentFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceIffIdempotentFixed
open scoped TensorProduct
universe u

namespace GlobalTheory

theorem weightSpace_iff_idempotent_fixed : ∀ (k : Type) [Field k] (C : Type) [CommRing C] (M : Type u) [AddCommGroup M] [Module k M] [Module (k ⊗[ℤ] C) M] [IsScalarTower k (k ⊗[ℤ] C) M] [FiniteDimensional k M] (χ : C →+* k) (e : k ⊗[ℤ] C), IsIdempotentElem e → (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) e = 1 → (∀ a, (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) a = 0 → IsNilpotent (e * a)) → ∀ m : M, m ∈ (⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c)) ↔ e • m = m := by
  intro k _ C _ M _ _ _ _ _ χ e he he1 hnil m
  set φ : k ⊗[ℤ] C →ₐ[k] k := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) with hφ
  have hφt : ∀ (x : k) (c : C), φ (x ⊗ₜ[ℤ] c) = x * χ c := by
    intro x c
    simp [hφ]
  let ρ : k ⊗[ℤ] C →ₐ[k] Module.End k M := Algebra.lsmul k k M
  let T : C → k ⊗[ℤ] C := fun c => (1 : k) ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (χ c)
  have hφT : ∀ c, φ (T c) = 0 := by
    intro c
    simp [T, hφt, AlgHom.commutes]
  have hρT : ∀ c, ρ (T c) = DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c) - χ c • (1 : Module.End k M) := by
    intro c
    simp only [T]
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    rfl
  constructor
  · intro hm
    set X := ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c) with hX
    have hstab : ∀ (a : k ⊗[ℤ] C) (x : M), x ∈ X → a • x ∈ X := by
      intro a x hx
      rw [hX, Submodule.mem_iInf] at hx ⊢
      intro c
      have hc : Commute (ρ ((1 : k) ⊗ₜ[ℤ] c)) (ρ a) := (Commute.all _ _).map ρ
      exact Module.End.mapsTo_maxGenEigenspace_of_comm hc (χ c) (hx c)
    let X' : Submodule (k ⊗[ℤ] C) M :=
      { carrier := X
        add_mem' := fun ha hb => X.add_mem ha hb
        zero_mem' := X.zero_mem
        smul_mem' := fun a x hx => hstab a x hx }
    let ρX : k ⊗[ℤ] C →ₐ[k] Module.End k X' := Algebra.lsmul k k X'
    have hT : ∀ c, IsNilpotent (ρX (T c)) := by
      intro c
      refine ⟨Module.End.maxGenEigenspaceIndex (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c), ?_⟩
      ext ⟨x, hx⟩
      have hx' : x ∈ Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
        (Submodule.mem_iInf _).1 hx c
      rw [Module.End.maxGenEigenspace_eq, Module.End.mem_genEigenspace_nat] at hx'
      rw [← hρT, ← map_pow] at hx'
      rw [LinearMap.mem_ker] at hx'
      rw [← map_pow, LinearMap.zero_apply]
      exact hx'
    have hall : ∀ a, IsNilpotent (ρX (a - algebraMap k (k ⊗[ℤ] C) (φ a))) := by
      intro a
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        have : x ⊗ₜ[ℤ] c - algebraMap k (k ⊗[ℤ] C) (φ (x ⊗ₜ[ℤ] c)) = x • T c := by
          simp only [T, hφt, smul_sub, Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul]
          rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
          simp
        rw [this, map_smul]
        exact (hT c).smul x
      | add a b ha hb =>
        have : a + b - algebraMap k (k ⊗[ℤ] C) (φ (a + b)) =
            (a - algebraMap k (k ⊗[ℤ] C) (φ a)) + (b - algebraMap k (k ⊗[ℤ] C) (φ b)) := by
          rw [map_add (f := _), map_add (f := _)]; abel
        rw [this, map_add (f := _)]
        exact Commute.isNilpotent_add ((Commute.all _ _).map ρX) ha hb
    have h1e : IsNilpotent (ρX (1 - e)) := by
      have := hall (1 - e)
      rwa [show φ (1 - e) = 0 by rw [map_sub, map_one, he1, sub_self], map_zero, sub_zero] at this
    have hid : IsIdempotentElem (ρX (1 - e)) := he.one_sub.map ρX
    have h0 := hid.eq_zero_of_isNilpotent h1e
    have := congrArg (fun f => (f ⟨m, hm⟩ : X')) h0
    simp only [LinearMap.zero_apply] at this
    have := congrArg Subtype.val this
    change (1 - e) • m = 0 at this
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  · intro hm
    rw [Submodule.mem_iInf]
    intro c
    rw [Module.End.mem_maxGenEigenspace]
    obtain ⟨n, hn⟩ := hnil (T c) (hφT c)
    refine ⟨n, ?_⟩
    have hen : ∀ j : ℕ, e ^ j • m = m := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, mul_smul, hm, ih]
    rw [← hρT, ← map_pow]
    change T c ^ n • m = 0
    rw [← hen n, smul_smul, mul_comm, ← mul_pow, hn, zero_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSpaceIffIdempotentFixedStatement
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq : ∀ (k : Type) [Field k] (C : Type) [CommRing C] (M : Type u) [AddCommGroup M] [Module k M] [Module (k ⊗[ℤ] C) M] [IsScalarTower k (k ⊗[ℤ] C) M] [FiniteDimensional k M] (χ : C →+* k) (e : k ⊗[ℤ] C), IsIdempotentElem e → (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) e = 1 → (∀ a, (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) a = 0 → IsNilpotent (e * a)) → ∀ m : M, m ∈ (⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k M ((1 : k) ⊗ₜ[ℤ] c)) (χ c)) ↔ e • m = m := by
  first | (exact @GlobalTheory.weightSpace_iff_idempotent_fixed) | (exact GlobalTheory.weightSpace_iff_idempotent_fixed) | (intros; apply GlobalTheory.weightSpace_iff_idempotent_fixed  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotOneSubIdempotentEqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotOneSubIdempotentEqMul
open scoped TensorProduct
universe u

namespace GlobalTheory

theorem finrank_quot_one_sub_idem_eq_mul : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k) (e : A), IsIdempotentElem e → φ e = 1 → (∀ a, φ a = 0 → IsNilpotent (e * a)) → ∀ (H : Type u) [AddCommGroup H] [Module A H] [Module k H] [IsScalarTower k A H] [FiniteDimensional k H] [Module.Projective A H], Module.finrank k (H ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A H)) = Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) * Module.finrank k (A ⧸ Ideal.span {1 - e}) := by
  intro k _ A _ _ _ φ e he hφe hnil H _ _ _ _ _ _
  have : Module.Finite A H := Module.Finite.of_restrictScalars_finite k A H
  set I : Ideal A := Ideal.span {1 - e} with hI
  have hIφ : ∀ a ∈ I, φ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hφe]
  have hItop : I ≠ ⊤ := by
    intro h
    have := hIφ 1 (h ▸ Submodule.mem_top)
    simp at this
  let B := A ⧸ I
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hItop
  have hloc : IsLocalRing B := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    have key : ∀ x : A, φ x ≠ 0 → IsUnit (Ideal.Quotient.mk I x) := by
      intro x hx
      have he1 : Ideal.Quotient.mk I e = 1 := by
        rw [eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      set a := x - algebraMap k A (φ x) with ha
      have hφa : φ a = 0 := by simp [ha]
      have hxa : x = algebraMap k A (φ x) + a := by simp [ha]
      rw [hxa, map_add (f := _)]
      have hn : IsNilpotent (Ideal.Quotient.mk I a) := by
        have : Ideal.Quotient.mk I a = Ideal.Quotient.mk I (e * a) := by rw [map_mul, he1, one_mul]
        rw [this]; exact (hnil a hφa).map _
      apply hn.isUnit_add_left_of_commute _ (Commute.all _ _)
      have : IsUnit (algebraMap k B (φ x)) := (isUnit_iff_ne_zero.mpr hx).map _
      simpa [Ideal.Quotient.mk_algebraMap] using this
    intro b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_cases hx : φ x = 0
    · right
      rw [← map_one (Ideal.Quotient.mk I), ← map_sub]
      exact key _ (by simp [hx])
    · left; exact key x hx
  let T := B ⊗[A] H
  have : Module.Free B T := Module.free_of_flat_of_isLocalRing

  have h3 : Module.finrank k (H ⧸ (I • ⊤ : Submodule A H)) = Module.finrank B T * Module.finrank k B := by
    let b := Module.Free.chooseBasis B T
    let e1 : T ≃ₗ[A] H ⧸ (I • ⊤ : Submodule A H) := TensorProduct.quotTensorEquivQuotSMul H I
    let e3 : (H ⧸ (I • ⊤ : Submodule A H)) ≃ₗ[A] (Module.Free.ChooseBasisIndex B T → B) :=
      e1.symm.trans (b.equivFun.restrictScalars A)
    rw [(e3.restrictScalars k).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Module.finrank_eq_card_chooseBasisIndex (R := B) (M := T)]
  have h4 : Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) = Module.finrank B T := by
    have hsurj : Function.Surjective φ := fun c => ⟨algebraMap k A c, φ.commutes c⟩
    let φB : B →ₐ[k] k := Ideal.Quotient.liftₐ I φ hIφ
    letI : Algebra A k := φ.toRingHom.toAlgebra
    letI : Algebra B k := φB.toRingHom.toAlgebra
    haveI : IsScalarTower A B k := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : IsScalarTower k A k := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    let f := Ideal.quotientKerAlgEquivOfSurjective hsurj
    let g : (A ⧸ RingHom.ker φ) ≃ₗ[A] k :=
      { f.toLinearEquiv with
        map_smul' := by
          intro a x
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
          change f (Ideal.Quotient.mk _ (a * y)) = φ a * f (Ideal.Quotient.mk _ y)
          simp [f, Ideal.quotientKerAlgEquivOfSurjective_apply] }
    let e6 : (k ⊗[A] H) ≃ₗ[A] H ⧸ (RingHom.ker φ • ⊤ : Submodule A H) :=
      (LinearEquiv.rTensor H g.symm).trans (TensorProduct.quotTensorEquivQuotSMul H (RingHom.ker φ))
    rw [← (e6.restrictScalars k).finrank_eq,
      ← (TensorProduct.AlgebraTensorModule.cancelBaseChange A B k k H).finrank_eq,
      Module.finrank_baseChange]
  rw [h3, h4]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotOneSubIdempotentEqMulStatement
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k) (e : A), IsIdempotentElem e → φ e = 1 → (∀ a, φ a = 0 → IsNilpotent (e * a)) → ∀ (H : Type u) [AddCommGroup H] [Module A H] [Module k H] [IsScalarTower k A H] [FiniteDimensional k H] [Module.Projective A H], Module.finrank k (H ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A H)) = Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) * Module.finrank k (A ⧸ Ideal.span {1 - e}) := by
  first | (exact @GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (exact GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (intros; apply GlobalTheory.finrank_quot_one_sub_idem_eq_mul  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWeightSpaceProjectiveTensorEq
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.WtRank

abbrev chr (k : Type) [Field k] (C : Type) [CommRing C] (χ : C →+* k) : k ⊗[ℤ] C →ₐ[k] k :=
  Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem finrank_fix {k A M : Type*} [Field k] [CommRing A] [Algebra k A] [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] (e : A) (W : Submodule k M)
    (hW : ∀ m, m ∈ W ↔ e • m = m) :
    Module.finrank k W = Module.finrank k (M ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A M)) := by
  set f : M →ₗ[k] M := DistribSMul.toLinearMap k M (1 - e)
  have hker : W = LinearMap.ker f := by
    ext m
    rw [hW, LinearMap.mem_ker]
    simp only [f, DistribSMul.toLinearMap_apply, sub_smul, one_smul, sub_eq_zero, eq_comm]
  have hrange : (Ideal.span {1 - e} • ⊤ : Submodule A M).restrictScalars k = LinearMap.range f := by
    ext m
    rw [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul, LinearMap.mem_range,
      Submodule.mem_smul_pointwise_iff_exists]
    simp [f]
  have e1 := (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {1 - e} • ⊤ : Submodule A M)).finrank_eq
  rw [← e1, hrange, hker]
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  omega

theorem weight_finrank_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ H _ _ _ σ
  letI inst : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift
    (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom
  intro hP χ
  have hP' : Module.Projective (k ⊗[ℤ] C) H := hP
  have hact : ∀ (a : k ⊗[ℤ] C) (h : H), a • h = (Algebra.TensorProduct.lift
      (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)) a h := fun _ _ => rfl
  haveI : IsScalarTower k (k ⊗[ℤ] C) H := ⟨fun l a h => by
    rw [hact, hact, map_smul, LinearMap.smul_apply]⟩
  obtain ⟨e, he, h1, hn⟩ := GlobalTheory.T.exists_idempotent_local_of_character k (k ⊗[ℤ] C) (chr k C χ)
  have hσ : ∀ c, σ c = DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext h
    rw [DistribSMul.toLinearMap_apply, hact]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hlm : ∀ c, ((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c =
      DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext x
    simp [Algebra.TensorProduct.includeRight_apply]
  have eH : (⨅ c : C, (σ c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hσ]
  have eA : (⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hlm]
  rw [eH, eA]
  rw [finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C H χ e he h1 hn), finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C (k ⊗[ℤ] C) χ e he h1 hn),
    GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul k (k ⊗[ℤ] C) (chr k C χ) e he h1 hn H]
  have hq : Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) =
      Module.finrank k (H ⧸ (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H)) := by
    have heq : GlobalTheory.HTRho.mSub σ χ ⊤ = (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H).restrictScalars k := by
      ext x; rw [Submodule.restrictScalars_mem]; exact GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul k C H σ χ x
    rw [heq]; exact (Submodule.Quotient.restrictScalarsEquiv k _).finrank_eq
  rw [hq]
  congr 1
  have hI : (Ideal.span {1 - e} • ⊤ : Submodule (k ⊗[ℤ] C) (k ⊗[ℤ] C)) = Ideal.span {1 - e} := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact ((Submodule.quotEquivOfEq _ _ hI).restrictScalars k).finrank_eq.symm

end GlobalTheory.WtRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWeightSpaceProjectiveTensorEqStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_weightSpace_projective_tensor_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  first | (exact @GlobalTheory.WtRank.weight_finrank_eq) | (exact GlobalTheory.WtRank.weight_finrank_eq) | (intros; apply GlobalTheory.WtRank.weight_finrank_eq  <;> assumption)
end
