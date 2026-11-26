module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericModelComplexSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHarrisTaylorDatumAtPrimeCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapFCoe
noncomputable section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT.Gen.SplitAE

variable (G : GDatum)

def toCenter : 𝓞 G.F →+* Subring.center (ℚ ⊗[ℤ] G.O) where
  toFun c := ⟨(1 : ℚ) ⊗ₜ[ℤ] algebraMap (𝓞 G.F) G.O c, Subring.mem_center_iff.mpr fun g => by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul q o => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        Algebra.commutes]
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]⟩
  map_one' := by ext; simp [Algebra.TensorProduct.one_def]
  map_mul' a b := by ext; simp [Algebra.TensorProduct.tmul_mul_tmul]
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [TensorProduct.tmul_add]

theorem toCenter_isUnit (c : nonZeroDivisors (𝓞 G.F)) : IsUnit (toCenter G c) := by
  have hc0 : (c : 𝓞 G.F) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have hI := Ideal.comap_ne_bot_of_integral_mem hc0 (Ideal.mem_span_singleton_self (c : 𝓞 G.F))
    (Algebra.IsIntegral.isIntegral (R := ℤ) (c : 𝓞 G.F))
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hk
  obtain ⟨d, hd⟩ := hk
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
  have hu : IsUnit ((k : Subring.center (ℚ ⊗[ℤ] G.O))) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap ℚ _ (k : ℚ)⁻¹,
      Subring.mem_center_iff.mpr fun g => (Algebra.commutes _ g).symm⟩, ?_⟩
    apply Subtype.ext
    show ((k : Subring.center (ℚ ⊗[ℤ] G.O)) : ℚ ⊗[ℤ] G.O) * algebraMap ℚ _ (k : ℚ)⁻¹ = 1
    rw [Subring.coe_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] G.O)), ← map_mul, mul_inv_cancel₀ hk', map_one]
  have hm : toCenter G d * toCenter G c = (k : Subring.center (ℚ ⊗[ℤ] G.O)) := by
    rw [← map_mul, hd, eq_intCast (algebraMap ℤ (𝓞 G.F)) k, map_intCast]
  exact isUnit_of_mul_isUnit_right (hm ▸ hu)

def fMap : G.F →+* ℚ ⊗[ℤ] G.O :=
  (Subring.center (ℚ ⊗[ℤ] G.O)).subtype.comp
    (IsLocalization.lift (M := nonZeroDivisors (𝓞 G.F)) (S := G.F) (toCenter_isUnit G))

theorem fMap_mem_center (x : G.F) : fMap G x ∈ Subring.center (ℚ ⊗[ℤ] G.O) :=
  (IsLocalization.lift (M := nonZeroDivisors (𝓞 G.F)) (S := G.F) (toCenter_isUnit G) x).2

instance instAlgebraF : Algebra G.F (ℚ ⊗[ℤ] G.O) :=
  (fMap G).toAlgebra' fun x y => ((Subring.mem_center_iff.mp (fMap_mem_center G x)) y).symm

theorem algebraMap_F_coe (c : 𝓞 G.F) :
    algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F) = (1 : ℚ) ⊗ₜ[ℤ] algebraMap (𝓞 G.F) G.O c := by
  show fMap G (algebraMap (𝓞 G.F) G.F c) = _
  simp only [fMap, RingHom.comp_apply, IsLocalization.lift_eq]
  rfl

instance instTowerF : IsScalarTower ℚ G.F (ℚ ⊗[ℤ] G.O) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    have := RingHom.ext_rat (algebraMap ℚ (ℚ ⊗[ℤ] G.O)) ((algebraMap G.F (ℚ ⊗[ℤ] G.O)).comp (algebraMap ℚ G.F))
    exact congrArg (fun f : ℚ →+* ℚ ⊗[ℤ] G.O => f q) this

def ordB : Subring (ℚ ⊗[ℤ] G.O) := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom.range

end GlobalTheory.UPel.HT.Gen.SplitAE
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTensorPadicIntEquivAdjoinOfFreeFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTensorPadicIntEquivAdjoinOfFreeFinite
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

namespace GlobalTheory.LocIso

theorem tensor_padicInt_equiv_locOrder : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (ℓ : ℕ) [Fact ℓ.Prime], ∃ ι : O ⊗[ℤ] ℤ_[ℓ] ≃+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range, ∀ o : O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
  intro O _ _ _ ℓ _
  let g1 : O →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeRight : (ℚ ⊗[ℤ] O) →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom).toIntAlgHom
  let g2 : ℤ_[ℓ] →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := ℚ_[ℓ]) (B := ℚ ⊗[ℤ] O)).comp
      PadicInt.Coe.ringHom).toIntAlgHom
  have hg1 : ∀ x, g1 x = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) := fun _ => rfl
  have hg2 : ∀ y : ℤ_[ℓ], g2 y = (y : ℚ_[ℓ]) ⊗ₜ[ℚ] (1 : ℚ ⊗[ℤ] O) := fun _ => rfl
  have hg : ∀ x y, Commute (g1 x) (g2 y) := by
    intro x y
    simp only [hg1, hg2, Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  let f := Algebra.TensorProduct.lift g1 g2 hg
  have hf : ∀ (o : O) (a : ℤ_[ℓ]), f (o ⊗ₜ a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
    intro o a
    simp only [f, Algebra.TensorProduct.lift_tmul, hg1, hg2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hinj : Function.Injective f := by
    have hl : Function.Injective (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b h => Subtype.ext h)
    have heq : (f : O ⊗[ℤ] ℤ_[ℓ] → ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] O).symm ∘
          (TensorProduct.comm ℤ O ℚ_[ℓ]) ∘
          (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul o a =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, TensorProduct.comm_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, hf]
        rfl
      | add x y hx hy =>
        simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢
        rw [hx, hy]
    rw [heq]
    exact (LinearEquiv.injective _).comp ((LinearEquiv.injective _).comp hl)
  have hmem : ∀ x, f x ∈ locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o a =>
      rw [hf]
      have h1 : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) =
          algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) a * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [h1]
      refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (Algebra.subset_adjoin ?_)
      exact ⟨(1 : ℚ) ⊗ₜ[ℤ] o, ⟨o, rfl⟩, rfl⟩
    | add x y hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  let g : O ⊗[ℤ] ℤ_[ℓ] →+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range :=
    (f.toRingHom).codRestrict _ hmem
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range).toSubring := hy
    rw [locOrder, Algebra.adjoin_eq_ring_closure] at hy'
    have hle : Subring.closure (Set.range (algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O))) ∪
        ((fun b => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' ((Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range : Set (ℚ ⊗[ℤ] O)))) ≤ f.toRingHom.range := by
      rw [Subring.closure_le]
      rintro _ (⟨a, rfl⟩ | ⟨_, ⟨o, rfl⟩, rfl⟩)
      · refine ⟨(1 : O) ⊗ₜ a, ?_⟩
        change f _ = _
        rw [hf, Algebra.TensorProduct.algebraMap_apply]
        rfl
      · refine ⟨o ⊗ₜ (1 : ℤ_[ℓ]), ?_⟩
        change f _ = _
        rw [hf]
        simp
    obtain ⟨x, hx⟩ := hle hy'
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective g ⟨fun x y h => hinj (congrArg Subtype.val h), hsurj⟩, fun o => ?_⟩
  change f (o ⊗ₜ 1) = _
  rw [hf]
  simp

end GlobalTheory.LocIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTensorPadicIntEquivAdjoinOfFreeFiniteStatement
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (ℓ : ℕ) [Fact ℓ.Prime], ∃ ι : O ⊗[ℤ] ℤ_[ℓ] ≃+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range, ∀ o : O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
  first | (exact @GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder) | (exact GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder) | (intros; apply GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingOfIntegersTensorPadicEquivAdjoin
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingOfIntegersTensorPadicEquivAdjoin
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CenOrderIso

def toLocal (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    𝓞 F ⊗[ℤ] ℤ_[ℓ] →+* ℚ_[ℓ] ⊗[ℚ] F :=
  (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] F).symm.toRingEquiv.toRingHom.comp
    ((Algebra.TensorProduct.comm ℤ F ℚ_[ℓ]).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
        (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom).toRingHom)

theorem toLocal_tmul (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (c : 𝓞 F) (a : ℤ_[ℓ]) :
    toLocal F ℓ (c ⊗ₜ[ℤ] a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := rfl

theorem toLocal_injective (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (toLocal F ℓ) := by
  have h1 : Function.Injective
      ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])
  have h2 : Function.Injective
      ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ]) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective (𝓞 F) F)
  have hmap : Function.Injective (Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
      (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom) := by
    have : ⇑(Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
        (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom) =
        ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ]) ∘
        ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F)) := by
      funext w
      induction w using TensorProduct.inductionOn with
      | tmul a b => rfl
      | add a b ha hb => simp only [map_add (f := _), Function.comp_apply] at ha hb ⊢; rw [ha, hb]
    rw [this]; exact h2.comp h1
  intro x y hxy
  apply hmap
  apply (Algebra.TensorProduct.comm ℤ F ℚ_[ℓ]).injective
  exact (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] F).symm.injective hxy

theorem toLocal_mem (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (x : 𝓞 F ⊗[ℤ] ℤ_[ℓ]) :
    toLocal F ℓ x ∈ cenOrder ℓ F := by
  induction x using TensorProduct.inductionOn with
  | tmul c a =>
    rw [toLocal_tmul]
    have hc : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) ∈ cenOrder ℓ F :=
      Algebra.subset_adjoin ⟨c, rfl⟩
    have : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) = a • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F)) := by
      rw [TensorProduct.smul_tmul']
      congr 1
      show (a : ℚ_[ℓ]) = a • (1 : ℚ_[ℓ])
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]
    exact Subalgebra.smul_mem _ hc a
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem cenOrder_le_range (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∀ y ∈ cenOrder ℓ F, ∃ x, toLocal F ℓ x = y := by
  let S : Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) :=
    { (toLocal F ℓ).range with
      algebraMap_mem' := fun r => ⟨(1 : 𝓞 F) ⊗ₜ[ℤ] r, by
        rw [toLocal_tmul]; rfl⟩ }
  have hle : cenOrder ℓ F ≤ S := by
    apply Algebra.adjoin_le
    rintro _ ⟨c, rfl⟩
    exact ⟨c ⊗ₜ[ℤ] (1 : ℤ_[ℓ]), by rw [toLocal_tmul]; simp⟩
  intro y hy
  exact hle hy

theorem cenOrder_equiv : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ κ : 𝓞 F ⊗[ℤ] ℤ_[ℓ] ≃+* cenOrder ℓ F,
      ∀ c : 𝓞 F, (κ (c ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := by
  intro F _ _ ℓ _
  let g : 𝓞 F ⊗[ℤ] ℤ_[ℓ] →+* cenOrder ℓ F := (toLocal F ℓ).codRestrict (cenOrder ℓ F) (toLocal_mem F ℓ)
  have hbij : Function.Bijective g := by
    refine ⟨fun x y h => toLocal_injective F ℓ (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := cenOrder_le_range F ℓ y y.2
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective g hbij, fun c => ?_⟩
  show toLocal F ℓ (c ⊗ₜ[ℤ] 1) = _
  rw [toLocal_tmul]; simp

end GlobalTheory.CenOrderIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingOfIntegersTensorPadicEquivAdjoinStatement
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringOfIntegersTensorPadic_equiv_adjoin : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime], ∃ κ : 𝓞 F ⊗[ℤ] ℤ_[ℓ] ≃+* cenOrder ℓ F, ∀ c : 𝓞 F, (κ (c ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := by
  first | (exact @GlobalTheory.CenOrderIso.cenOrder_equiv) | (exact GlobalTheory.CenOrderIso.cenOrder_equiv) | (intros; apply GlobalTheory.CenOrderIso.cenOrder_equiv  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimes
namespace GlobalTheory.UPel.HT.Gen.SplitAE
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

theorem finrank_eq (G : GDatum) : Module.finrank G.F (ℚ ⊗[ℤ] G.O) = G.m ^ 2 := by
  haveI := G.freeO
  haveI := G.finO
  have h1 : Module.finrank ℚ (ℚ ⊗[ℤ] G.O) = Module.finrank ℤ G.O := Module.finrank_baseChange
  haveI : Module.Finite ℚ (ℚ ⊗[ℤ] G.O) := inferInstance
  haveI : Module.Finite G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  have h2 := Module.finrank_mul_finrank ℚ G.F (ℚ ⊗[ℤ] G.O)
  rw [h1, G.rankO] at h2
  have hd : 0 < Module.finrank ℚ G.F := Module.finrank_pos
  have : Module.finrank ℚ G.F * Module.finrank G.F (ℚ ⊗[ℤ] G.O) = Module.finrank ℚ G.F * G.m ^ 2 := by
    rw [h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hd this

theorem isCentral (G : GDatum) : Algebra.IsCentral G.F (ℚ ⊗[ℤ] G.O) := by
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G z
  have hxc : ∀ y : G.O, x * y = y * x := by
    intro y
    apply GDatum.tmul_one_injective G
    have e1 : (1:ℚ) ⊗ₜ[ℤ] (x*y) = N • (z * (1 ⊗ₜ y)) := by
      rw [← smul_mul_assoc, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e2 : (1:ℚ) ⊗ₜ[ℤ] (y*x) = N • ((1 ⊗ₜ y) * z) := by
      rw [← mul_smul_comm, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    show (1:ℚ) ⊗ₜ[ℤ] (x*y) = (1:ℚ) ⊗ₜ[ℤ] (y*x)
    rw [e1, e2, hz]
  obtain ⟨c, e, he, hec⟩ := G.central x hxc
  have hM : ((e * N : ℤ) : ℚ) • z = algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F) := by
    rw [algebraMap_F_coe, ← hec, Int.cast_smul_eq_zsmul, mul_smul, hx, TensorProduct.tmul_smul]
  have hq : ((e * N : ℤ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero he hN
  refine ⟨((e * N : ℤ) : ℚ)⁻¹ • (c : G.F), ?_⟩
  show algebraMap G.F (ℚ ⊗[ℤ] G.O) (((e * N : ℤ) : ℚ)⁻¹ • (c : G.F)) = z
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, ← hM, smul_smul, inv_mul_cancel₀ hq, one_smul]

theorem ordB_finite (G : GDatum) : Module.Finite ℤ (ordB G) := by
  haveI := G.finO
  let f := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom
  exact Module.Finite.of_surjective f.rangeRestrict.toIntAlgHom.toLinearMap f.rangeRestrict_surjective

theorem ordB_denom (G : GDatum) (b : ℚ ⊗[ℤ] G.O) : ∃ n : ℕ, 0 < n ∧ (n : ℚ ⊗[ℤ] G.O) * b ∈ ordB G := by
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G b
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
  · refine ⟨n, by omega, x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] x = _
    rw [← hx, natCast_zsmul, nsmul_eq_mul]
  · refine ⟨n, by omega, -x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] (-x) = _
    rw [TensorProduct.tmul_neg, ← hx, neg_smul, neg_neg, natCast_zsmul, nsmul_eq_mul]

theorem splitAE : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M →
    Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  intro G
  haveI := G.freeO
  haveI := G.finO
  haveI := isCentral G
  haveI := GDatum.isSimpleRing G
  haveI : FiniteDimensional G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  obtain ⟨N, hN, hloc⟩ := GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F (ℚ ⊗[ℤ] G.O) G.m (finrank_eq G) (ordB G) (ordB_finite G) (ordB_denom G)
  refine ⟨N, hN, fun p _ hp => ?_⟩
  obtain ⟨ψ, hψ⟩ := hloc p hp
  obtain ⟨ι, hι⟩ : ∃ ι : G.O ⊗[ℤ] ℤ_[p] ≃+* locOrder p (ordB G),
      ∀ o : G.O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) = (1 : ℚ_[p]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) :=
    GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite G.O p
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_ringOfIntegersTensorPadic_equiv_adjoin G.F p
  let Φ : G.O ⊗[ℤ] ℤ_[p] ≃+* Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p]) :=
    ι.trans (ψ.toRingEquiv.trans κ.symm.mapMatrix)
  refine ⟨AlgEquiv.ofRingEquiv (f := Φ) fun c => ?_⟩
  obtain ⟨h, hh⟩ := hψ (κ (c ⊗ₜ[ℤ] 1))
  have e1 : ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) = ⟨_, h⟩ := by
    apply Subtype.ext
    show (ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) =
      cenMap p G.F (ℚ ⊗[ℤ] G.O) (κ (c ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] G.F)
    rw [Algebra.TensorProduct.algebraMap_apply, hι, hκ, cenMap, Algebra.TensorProduct.map_tmul]
    show _ = (1 : ℚ_[p]) ⊗ₜ[ℚ] algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F)
    rw [algebraMap_F_coe]
  show κ.symm.mapMatrix (ψ (ι _)) = _
  rw [e1]
  erw [hh]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.algebraMap_eq_diagonal]
  split_ifs <;> simp [RingEquiv.symm_apply_apply]

end GlobalTheory.UPel.HT.Gen.SplitAE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimesStatement
open NumberField
open GlobalTheory.UPel.HT.Gen
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  first | (exact @GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (exact GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (intros; apply GlobalTheory.UPel.HT.Gen.SplitAE.splitAE  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BilinFormInjectiveExistsNsmulMemRange
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BilinFormInjectiveExistsNsmulMemRange
namespace GlobalTheory

open Matrix

theorem bilinForm_injective_exists_mul_mem_range (La : Type) [AddCommGroup La]
    [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La)
    (hEF : Function.Injective EF) :
    ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  classical
  set ι := Module.Free.ChooseBasisIndex ℤ La
  let b : Module.Basis ι ℤ La := Module.Free.chooseBasis ℤ La
  let A : Matrix ι ι ℤ := fun i j => EF (b i) (b j)

  have key : ∀ (c : ι → ℤ) (j : ι), EF (∑ i, c i • b i) (b j) = (c ᵥ* A) j := by
    intro c j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, LinearMap.sum_apply, vecMul, dotProduct, A, smul_eq_mul]
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvA⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := A)).2 h0
    have hx : EF (∑ i, v i • b i) = 0 := by
      refine b.ext fun j => ?_
      rw [key, hvA]; simp
    have : (∑ i, v i • b i) = 0 := hEF (by rw [hx, map_zero])
    apply hv
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v this i
  set d := A.det
  refine ⟨d.natAbs * d.natAbs, ?_, ?_⟩
  · have : 0 < d.natAbs := Int.natAbs_pos.2 hdet
    positivity
  · intro f
    let w : ι → ℤ := fun j => f (b j)
    refine ⟨∑ i, ((d • w) ᵥ* adjugate A) i • b i, ?_⟩
    refine b.ext fun j => ?_
    rw [key, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
    have hc : ((d.natAbs * d.natAbs : ℕ) : ℤ) = d * d := by
      rw [Nat.cast_mul]; exact Int.natAbs_mul_self' d
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, w]
    rw [← Nat.cast_smul_eq_nsmul ℤ, hc, smul_eq_mul]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BilinFormInjectiveExistsNsmulMemRangeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bilinForm_injective_exists_nsmul_mem_range : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La), Function.Injective EF → ∃ e : ℕ, 0 < e ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f := by
  first | (exact @GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (exact GlobalTheory.bilinForm_injective_exists_mul_mem_range) | (intros; apply GlobalTheory.bilinForm_injective_exists_mul_mem_range  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHarrisTaylorDatumAtPrimeCoprime
open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open scoped TensorProduct

namespace GlobalTheory.GoodPrime

theorem schur (tr nm : ℤ) (M : ℕ) (hM : 0 < M) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - tr * r + nm := by
  by_cases hnm : nm = 0
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := M + 1) (by omega)
    refine ⟨p, hp, fun h => hp.one_lt.ne' ?_, 0, by simp [hnm]⟩
    exact Nat.dvd_one.1 ((Nat.dvd_add_right h).1 hpd)
  · set t : ℤ := |tr| + 3
    set g : ℤ := (M : ℤ) ^ 2 * nm * t ^ 2 - tr * M * t + 1
    have ht : 3 ≤ t := by have := abs_nonneg tr; omega
    have hMz : (1 : ℤ) ≤ M := by exact_mod_cast hM
    have hnm1 : 1 ≤ |nm| := Int.one_le_abs hnm
    have hg : 2 ≤ |g| := by
      have h1 : |(M : ℤ) ^ 2 * nm * t ^ 2| = (M : ℤ) ^ 2 * |nm| * t ^ 2 := by
        rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (by omega : (0:ℤ) < M), abs_of_pos (by omega : (0:ℤ) < t)]
      have h2 : |tr * M * t| = |tr| * M * t := by
        rw [abs_mul, abs_mul, abs_of_pos (by omega : (0:ℤ) < M), abs_of_pos (by omega : (0:ℤ) < t)]
      have h3 : |(M : ℤ) ^ 2 * nm * t ^ 2| ≤ |g| + |tr * M * t| + 1 := by
        have : (M : ℤ) ^ 2 * nm * t ^ 2 = g + tr * M * t - 1 := by simp only [g]; ring
        rw [this]
        calc |g + tr * M * t - 1| ≤ |g + tr * M * t| + |(1:ℤ)| := abs_sub _ _
          _ ≤ |g| + |tr * M * t| + 1 := by simpa using abs_add_le g (tr * M * t)
      rw [h1, h2] at h3
      have hat : |tr| = t - 3 := by simp only [t]; ring
      rw [hat] at h3
      have hMt : 3 ≤ (M : ℤ) * t := by nlinarith
      have hk : (M : ℤ) ^ 2 * t ^ 2 ≤ (M : ℤ) ^ 2 * |nm| * t ^ 2 := by
        have := mul_le_mul_of_nonneg_right hnm1 (by positivity : (0:ℤ) ≤ (M : ℤ) ^ 2 * t ^ 2)
        linarith
      have hq : 3 ≤ t * ((M : ℤ) - 1) + 3 := by nlinarith
      have hr : 9 ≤ ((M : ℤ) * t) * (t * ((M : ℤ) - 1) + 3) := by nlinarith
      have e : ((M : ℤ) * t) * (t * ((M : ℤ) - 1) + 3) = (M : ℤ) ^ 2 * t ^ 2 - (t - 3) * M * t := by ring
      linarith
    have hg' : (2 : ℤ) ≤ (g.natAbs : ℤ) := by rw [← Int.abs_eq_natAbs]; exact hg
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := g.natAbs) (by omega)
    have hpg : (p : ℤ) ∣ g := Int.natCast_dvd.2 hpd
    refine ⟨p, hp, fun h => hp.one_lt.ne' ?_, M * nm * t, ?_⟩
    · have hpM : (p : ℤ) ∣ M := Int.natCast_dvd_natCast.2 h
      have : (p : ℤ) ∣ g - M * (M * nm * t ^ 2 - tr * t) := dvd_sub hpg (dvd_mul_of_dvd_left hpM _)
      have e : g - M * (M * nm * t ^ 2 - tr * t) = 1 := by simp only [g]; ring
      rw [e] at this
      exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this
    · have e : ((M : ℤ) * nm * t) ^ 2 - tr * (M * nm * t) + nm = nm * g := by simp only [g]; ring
      rw [e]; exact dvd_mul_of_dvd_right hpg _

theorem exists_datum (G : GDatum) (N : ℕ) (hN : 0 < N) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (D : Datum p), N.Coprime p ∧ D.toG = G := by
  haveI := G.freeLa; haveI := G.finLa
  obtain ⟨e, he, hperf⟩ := GlobalTheory.T.bilinForm_injective_exists_nsmul_mem_range G.La G.EF G.nondeg
  obtain ⟨M, hM, hsplit⟩ := GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes G
  have hd : 0 < (G.tr ^ 2 - 4 * G.nm).natAbs := Int.natAbs_pos.2 (ne_of_lt G.disc_neg)
  obtain ⟨p, hp, hpM, r, hr⟩ := schur G.tr G.nm (N * e * M * (G.tr ^ 2 - 4 * G.nm).natAbs) (by positivity)
  haveI : Fact p.Prime := ⟨hp⟩
  have hN' : ¬ p ∣ N := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _) _)
  have he' : ¬ p ∣ e := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _) _)
  have hM' : ¬ p ∣ M := fun h => hpM (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have hd' : ¬ (p : ℤ) ∣ G.tr ^ 2 - 4 * G.nm := fun h => hpM (Dvd.dvd.mul_left (Int.natCast_dvd.1 h) _)
  refine ⟨p, inferInstance,
    { F := G.F, fld := G.fld, nf := G.nf, cm := G.cm, bar := G.bar, bar_eq := G.bar_eq, ω := G.ω,
      tr := G.tr, nm := G.nm, tr_eq := G.tr_eq, nm_eq := G.nm_eq, disc_neg := G.disc_neg, disc_p := hd',
      split := ⟨r, hr⟩, O := G.O, rng := G.rng, alg := G.alg, freeO := G.freeO, finO := G.finO,
      m := G.m, m_pos := G.m_pos, rankO := G.rankO, central := G.central, star := G.star,
      star_star := G.star_star, star_F := G.star_F, splitP := hsplit p hM', La := G.La, acg := G.acg,
      modO := G.modO, freeLa := G.freeLa, finLa := G.finLa, n := G.n, n_pos := G.n_pos, rankLa := G.rankLa,
      EF := G.EF, alt := G.alt, nondeg := G.nondeg,
      perfP := ⟨e, Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 he'), hperf⟩,
      adj := G.adj, a := G.a, ρc := G.ρc, ρc_root := G.ρc_root, tau := G.tau, tau_ω := G.tau_ω,
      dom := G.dom },
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hN'), rfl⟩

end GlobalTheory.GoodPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHarrisTaylorDatumAtPrimeCoprimeStatement
open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorDatum_at_prime_coprime : ∀ (G : GDatum) (N : ℕ), 0 < N → ∃ (p : ℕ) (_ : Fact p.Prime) (D : Datum p), N.Coprime p ∧ D.toG = G := by
  first | (exact @GlobalTheory.GoodPrime.exists_datum) | (exact GlobalTheory.GoodPrime.exists_datum) | (intros; apply GlobalTheory.GoodPrime.exists_datum  <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPel.HT.Gen.CxSmooth

theorem of_geomFibres {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (g : ℕ)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Y), SmoothOfRelativeDimension g (pullback.snd f t)) :
    SmoothOfRelativeDimension g f := by
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  have key : ∀ x, n x = g := by
    intro x
    let κ := Y.residueField (f x)
    let k := AlgebraicClosure κ
    let t : Sp k ⟶ Y := spMap (algebraMap κ k) ≫ Y.fromSpecResidueField (f x)
    have ht : f x = t (IsLocalRing.closedPoint k) := by
      show f x = (Y.fromSpecResidueField (f x)) ((spMap (algebraMap κ k)) (IsLocalRing.closedPoint k))
      rw [Scheme.fromSpecResidueField_apply]
    obtain ⟨z, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := t) x (IsLocalRing.closedPoint k) ht
    have sq := IsPullback.paste_vert (isPullback_morphismRestrict (pullback.fst f t) (W x))
      (IsPullback.of_hasPullback f t)
    have h₁ : SmoothOfRelativeDimension (n x) (((pullback.fst f t) ⁻¹ᵁ W x).ι ≫ pullback.snd f t) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback sq (hd x)
    have h₂ : SmoothOfRelativeDimension g (((pullback.fst f t) ⁻¹ᵁ W x).ι ≫ pullback.snd f t) :=
      IsZariskiLocalAtSource.comp (h k t) _
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h₁ h₂ ⟨z, show pullback.fst f t z ∈ W x by rw [hz.1]; exact hW x⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← key x]; exact hd x

def baseOfG {p : ℕ} [Fact p.Prime] {D : Datum p} (gb : GBase D.toG ℂ) : Base D ℂ where
  unit k hk := by
    refine Ne.isUnit (Nat.cast_ne_zero.2 ?_)
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hk)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    have h1 : IsUnit ((p : ℂ)) := Ne.isUnit (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    have h2 := h1.map β
    rw [map_natCast, CharP.cast_eq_zero] at h2
    exact not_isUnit_zero h2

theorem genericModel_complex_smooth {p : ℕ} [Fact p.Prime] (D : Datum p) (gb : GBase D.toG ℂ) (N : ℕ) (hN : 3 ≤ N)
    (hNp : N.Coprime p) (X : GenModel gb N) : ∃ d, SmoothOfRelativeDimension d X.s := by
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D ℂ (baseOfG gb) N hN hNp
  obtain ⟨j, hj, -, hjs, -⟩ := GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre p D ℂ (baseOfG gb) ℂ (RingHom.id ℂ) gb rfl
    (fun i => (RingHom.id_comp _).symm) N hN hNp M X
  have h1 : SmoothOfRelativeDimension (D.a * (D.n - 1)) (pullback.snd M.s (spMap (RingHom.id ℂ))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) M.smooth
  have : IsOpenImmersion j := hj
  have h0 : SmoothOfRelativeDimension 0 j := inferInstance
  refine ⟨0 + D.a * (D.n - 1), ?_⟩
  rw [← hjs]
  infer_instance

theorem card_torsion_of_gTateIso (G : GDatum) {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    Nat.card {q : Q // q ^ ℓ = 1} = ℓ ^ Module.finrank ℤ G.La := by
  haveI := G.freeLa
  haveI := G.finLa
  haveI : NeZero ℓ := ⟨hℓ.ne'⟩
  set r := Module.finrank ℤ G.La
  let B := Module.finBasis ℤ G.La
  let v : (Fin r → ZMod ℓ) → G.La := fun c => ∑ i, ((c i).val : ℤ) • B i
  have evneg : ∀ x y : G.La, I.ev ℓ (x - y) = I.ev ℓ x * (I.ev ℓ y)⁻¹ := fun x y => by
    rw [eq_mul_inv_iff_mul_eq, ← I.add, sub_add_cancel]
  have hrep : ∀ c i, B.repr (v c) i = ((c i).val : ℤ) := fun c i => by
    simp [v, Module.Basis.repr_self, Finsupp.single_apply]
  let F : (Fin r → ZMod ℓ) → {q : Q // q ^ ℓ = 1} := fun c => ⟨I.ev ℓ (v c), (I.onto ℓ hℓ _).2 ⟨_, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro c c' hcc
      have h1 : I.ev ℓ (v c - v c') = 1 := by
        rw [evneg, mul_inv_eq_one]; exact congrArg Subtype.val hcc
      obtain ⟨y, hy⟩ := (I.ker ℓ hℓ _).1 h1
      funext i
      have h2 := congrArg (fun z => B.repr z i) hy
      simp only [map_sub, Finsupp.sub_apply, hrep, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at h2
      have h3 := congrArg (fun z : ℤ => (z : ZMod ℓ)) h2
      simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul,
        ZMod.natCast_self, zero_mul] at h3
      exact sub_eq_zero.1 h3
    · rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := (I.onto ℓ hℓ q).1 hq
      let c : Fin r → ZMod ℓ := fun i => (B.repr x i : ZMod ℓ)
      have hdiv : ∀ i, (ℓ : ℤ) ∣ ((c i).val : ℤ) - B.repr x i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp [c]
      choose y hy using hdiv
      refine ⟨c, Subtype.ext ?_⟩
      show I.ev ℓ (v c) = I.ev ℓ x
      have e1 : v c = x + ℓ • ∑ i, y i • B i := by
        refine B.ext_elem fun i => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hrep, map_add (f := _), map_nsmul, Finsupp.add_apply, Finsupp.smul_apply, map_sum]
        simp only [map_zsmul, Module.Basis.repr_self, Finset.sum_apply', Finsupp.smul_apply,
          Finsupp.single_apply, smul_eq_mul, nsmul_eq_mul]
        simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linear_combination hy i
      rw [e1, I.add, (I.ker ℓ hℓ _).2 ⟨_, rfl⟩, _root_.mul_one]
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem relDim_A {G : GDatum} (gb : GBase G ℂ) (N : ℕ) (X : GenModel gb N) :
    SmoothOfRelativeDimension (G.m * G.n * Module.finrank ℚ G.F / 2) X.univ.A.hom := by
  have hab := X.univ.ab
  have : Smooth X.univ.A.hom := hab.smooth
  have : IsProper X.univ.A.hom := hab.proper
  have : GeometricallyConnected X.univ.A.hom := hab.geomConnected
  refine of_geomFibres X.univ.A.hom _ fun k _ _ t => ?_
  let B := (Over.pullback t).obj X.univ.A
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := by show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have : Smooth B.hom := hB.smooth
  have : GeometricallyConnected B.hom := hB.geomConnected
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton (f := B.hom)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected B.hom (Classical.arbitrary _)
  suffices e : d = G.m * G.n * Module.finrank ℚ G.F / 2 by rw [← e]; exact hd
  obtain ⟨β, hβ⟩ := Spec.map_surjective (t ≫ X.s)
  obtain ⟨I, -⟩ := X.univ.geom k t β.hom hβ.symm
  have h2k : ((2 : ℕ) : k) ≠ 0 := by
    have h : IsUnit ((2 : ℕ) : ℂ) := Ne.isUnit (by norm_num)
    have := h.map β.hom
    rw [map_natCast] at this
    exact this.ne_zero
  have c₁ := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B d 2 hB hd h2k
  have c₂ := card_torsion_of_gTateIso G I (ℓ := 2) two_pos
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback X.univ.A t) (𝟙 _) t
    (Category.id_comp t).symm
  have c₃ : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ 2 = 1} =
      Nat.card {q : Over.mk t ⟶ X.univ.A // q ^ 2 = 1} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
      show x ^ 2 = 1 ↔ e x ^ 2 = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  rw [c₁, c₂, G.rankLa] at c₃
  have := Nat.pow_right_injective le_rfl c₃
  omega

theorem genModel_smooth : ∀ (G : GDatum) (gb : GBase G ℂ) (N : ℕ), 3 ≤ N → ∀ X : GenModel gb N,
    (∃ d : ℕ, SmoothOfRelativeDimension d X.s) ∧
      SmoothOfRelativeDimension (G.m * G.n * Module.finrank ℚ G.F / 2) X.univ.A.hom := by
  intro G gb N hN X
  refine ⟨?_, relDim_A gb N X⟩
  obtain ⟨p, _, D, hNp, rfl⟩ := GlobalTheory.T.exists_harrisTaylorDatum_at_prime_coprime G N (by omega)
  exact genericModel_complex_smooth D gb N hN hNp X

end GlobalTheory.UPel.HT.Gen.CxSmooth
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.WeightTwoHeckePower

namespace GlobalTheory.WeightTwoHeckePower

theorem sPow_smooth : ∀ (G : GDatum) (gb : GBase G ℂ) (N : ℕ), 3 ≤ N → ∀ (X : GenModel gb N) (r : ℕ),
    ∃ d : ℕ, SmoothOfRelativeDimension d (sPow X r) := by
  intro G gb N hN X r
  obtain ⟨⟨d, hd⟩, hA⟩ := GlobalTheory.UPel.HT.Gen.CxSmooth.genModel_smooth G gb N hN X
  have h := GlobalTheory.FibPow.smoothOfRelativeDimension_pow X.univ.A _ hA r
  exact ⟨_, (inferInstance : SmoothOfRelativeDimension (r * (G.m * G.n * Module.finrank ℚ G.F / 2) + d)
    ((GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s))⟩

end GlobalTheory.WeightTwoHeckePower
