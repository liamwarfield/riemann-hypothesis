module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfIrr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrrRepHarishChandraDistinctCuspidalLabels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviPiTensorRepresentationIsIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviPiTensorRepresentationIsIrreducible
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr

namespace GlobalTheory.HcIrr

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)]

theorem map_mem_of_position_stable (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ (c : ι) (f : V c →ₗ[ℂ] V c), ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W)
    (f : ∀ i, V i →ₗ[ℂ] V i) : ∀ x ∈ W, PiTensorProduct.map f x ∈ W := by
  suffices H : ∀ S : Finset ι, ∀ x ∈ W,
      PiTensorProduct.map (fun c => if c ∈ S then f c else LinearMap.id) x ∈ W by
    intro x hx
    simpa using H Finset.univ x hx
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro x hx
    simpa [PiTensorProduct.map_id] using hx
  | insert a S ha ih =>
    intro x hx
    have e : (fun c => if c ∈ insert a S then f c else (LinearMap.id : V c →ₗ[ℂ] V c)) = fun c =>
        (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) a (f a)) c ∘ₗ
          (if c ∈ S then f c else LinearMap.id) := by
      funext c
      by_cases hc : c = a
      · subst hc
        simp [ha]
      · simp [hc, Function.update_of_ne]
    rw [e, PiTensorProduct.map_comp]
    exact h a (f a) _ (ih x hx)

theorem position_stable_of_span {c : ι} {G : Type} [Group G] (ρ : Representation ℂ G (V c))
    (hs : Submodule.span ℂ (Set.range ρ) = ⊤) (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ g : G, ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (ρ g)) x ∈ W)
    (f : V c →ₗ[ℂ] V c) : ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W := by
  have hf : f ∈ Submodule.span ℂ (Set.range ρ) := hs ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact h g
  | zero =>
    intro x _
    have := PiTensorProduct.map_update_smul (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (0 : ℂ)
      LinearMap.id
    rw [zero_smul, zero_smul] at this
    rw [this]
    simp
  | add u v _ _ hu hv =>
    intro x hx
    rw [PiTensorProduct.map_update_add, LinearMap.add_apply]
    exact add_mem (hu x hx) (hv x hx)
  | smul a u _ hu =>
    intro x hx
    rw [PiTensorProduct.map_update_smul, LinearMap.smul_apply]
    exact W.smul_mem _ (hu x hx)

theorem eq_bot_or_top_of_map_stable [∀ i, FiniteDimensional ℂ (V i)]
    (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ f : ∀ i, V i →ₗ[ℂ] V i, ∀ x ∈ W, PiTensorProduct.map f x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  let e := fun c => Module.finBasis ℂ (V c)
  let B := Basis.piTensorProduct e
  obtain ⟨I, hI⟩ : ∃ I, B.repr x I ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext hc))
  have hJ : ∀ J, B J ∈ W := by
    intro J
    let f : ∀ c, V c →ₗ[ℂ] V c := fun c => ((e c).coord (I c)).smulRight (e c (J c))
    have hf : PiTensorProduct.map f = (B.coord I).smulRight (B J) := by
      refine B.ext fun p => ?_
      have hc : ∀ c, f c (e c (p c)) = (if p c = I c then (1 : ℂ) else 0) • e c (J c) := by
        intro c
        simp [f, Finsupp.single_apply]
      have hq : (∏ c, if p c = I c then (1 : ℂ) else 0) = if p = I then 1 else 0 := by
        rw [Finset.prod_ite_zero]
        simp [funext_iff]
      rw [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [B, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, hc,
        MultilinearMap.map_smul_univ, RingHom.id_apply, hq]
    have hm := h f x hx
    rw [hf, LinearMap.smulRight_apply, Module.Basis.coord_apply] at hm
    exact (W.smul_mem_iff hI).1 hm
  refine eq_top_iff.2 ?_
  rw [← B.span_eq]
  exact Submodule.span_le.2 (by rintro _ ⟨J, rfl⟩; exact hJ J)

theorem nontrivial_piTensorProduct [∀ i, FiniteDimensional ℂ (V i)] [∀ i, Nontrivial (V i)] :
    Nontrivial (PiTensorProduct ℂ V) := by
  let B := Basis.piTensorProduct fun c => Module.finBasis ℂ (V c)
  exact ⟨B fun c => ⟨0, Module.finrank_pos⟩, 0, B.ne_zero _⟩

end General

theorem leviTensor_isIrreducible : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ)
    (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    (∀ c, Simple (lam c)) → (leviTensor b lam).IsIrreducible := by
  intro K _ _ _ r s b lam hs
  have hirr := fun c => GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple (lam c) (hs c)
  have hspan := fun c => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ (lam c).ρ (hirr c)
  haveI : ∀ c, Nontrivial (lam c : Type) := fun c =>
    GlobalTheory.OuterTensor.nontrivial_of_isIrreducible _ (hirr c)
  haveI : Nontrivial (PiTensorProduct ℂ (fun c => (lam c : Type))) := nontrivial_piTensorProduct
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h :
      (⊥ : Submodule ℂ (PiTensorProduct ℂ (fun c => (lam c : Type)))) = ⊤)
  have hstable : ∀ (c : Fin s) (f : (lam c : Type) →ₗ[ℂ] (lam c : Type)), ∀ x ∈ S.toSubmodule,
      PiTensorProduct.map (Function.update
        (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c f) x ∈ S.toSubmodule := by
    intro c
    refine position_stable_of_span (lam c).ρ (hspan c) S.toSubmodule fun g x hx => ?_
    rw [← leviTensor_blockExt b lam c g]
    exact S.apply_mem_toSubmodule _ hx
  rcases eq_bot_or_top_of_map_stable S.toSubmodule (map_mem_of_position_stable _ hstable) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end GlobalTheory.HcIrr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviPiTensorRepresentationIsIrreducibleStatement
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviPiTensorRepresentation_isIrreducible : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, Simple (lam c)) → (leviTensor b lam).IsIrreducible := by
  first | exact @GlobalTheory.HcIrr.leviTensor_isIrreducible | exact GlobalTheory.HcIrr.leviTensor_isIrreducible | (intros; apply GlobalTheory.HcIrr.leviTensor_isIrreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCuspidalFactorAtBlockLeviPiTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCuspidalFactorAtBlockLeviPiTensor
noncomputable section

namespace GlobalTheory.HcIrr.Factor

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr Representation

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem tprod_update_injective (v : ∀ i, M i) (hv : ∀ i, v i ≠ 0) (i : ι) :
    Function.Injective ((PiTensorProduct.tprod ℂ).toLinearMap v i) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  by_contra hx0
  have hw : ∀ j, Function.update v i x j ≠ 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hx0
    · rw [Function.update_of_ne hj]; exact hv j
  have hφ : ∀ j, ∃ φ : Module.Dual ℂ (M j), φ (Function.update v i x j) ≠ 0 := by
    intro j
    by_contra hc
    push_neg at hc
    exact hw j ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  choose φ hφ using hφ
  have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) hx
  rw [MultilinearMap.toLinearMap_apply, PiTensorProduct.lift.tprod, map_zero,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
  exact (Finset.prod_ne_zero_iff.2 fun j _ => hφ j) h1

end Tensor

section Blocks

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def blockIdx (b : Fin r → Fin s) (c : Fin s) : {i // b i = c} ≃ Block (natBlocks b) (c : ℕ) :=
  Equiv.subtypeEquivRight fun i => by simp [natBlocks, Fin.val_inj]

def blockNum (b : Fin r → Fin s) (c : Fin s) {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) :
    {i // b i = c} ≃ Fin d :=
  (blockIdx b c).trans (monoEquivOfFin _ h).toEquiv.symm

theorem monoEquivOfFin_blockNum (b : Fin r → Fin s) (c : Fin s) {d : ℕ}
    (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) (x : {i // b i = c}) :
    ((monoEquivOfFin (Block (natBlocks b) (c : ℕ)) h (blockNum b c h x) : Block (natBlocks b) (c : ℕ)) : Fin r) = x.1 := by
  simp [blockNum, blockIdx]

theorem blockEmb_eq (b : Fin r → Fin s) (c : Fin s) {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d)
    (g : GL (Fin d) K) :
    blockEmb (natBlocks b) (c : ℕ) h g = blockExt b c ((glEquiv K (blockNum b c h)).symm g) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  by_cases hij : b i = c ∧ b j = c
  · have h1 := blockEmb_in (natBlocks b) (c : ℕ) h g (blockNum b c h ⟨i, hij.1⟩) (blockNum b c h ⟨j, hij.2⟩)
    rw [monoEquivOfFin_blockNum, monoEquivOfFin_blockNum] at h1
    have h2 := blockExt_in b c ((glEquiv K (blockNum b c h)).symm g) ⟨i, hij.1⟩ ⟨j, hij.2⟩
    rw [h1, h2]
    rfl
  · have hn : ¬ (natBlocks b i = (c : ℕ) ∧ natBlocks b j = (c : ℕ)) := by
      simpa [natBlocks, Fin.val_inj] using hij
    rw [blockEmb_out (natBlocks b) (c : ℕ) h g i j hn, blockExt_out b c _ i j hij]

end Blocks

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem blockRes_leviTensor (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s)
    {d : ℕ} (h : Fintype.card (Block (natBlocks b) (c : ℕ)) = d) (g : GL (Fin d) K) :
    blockRes (natBlocks b) (leviTensor b lam) (c : ℕ) h g = PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c
        ((lam c).ρ ((glEquiv K (blockNum b c h)).symm g))) := by
  show leviTensor b lam (blockEmb (natBlocks b) (c : ℕ) h g) = _
  rw [blockEmb_eq, leviTensor_blockExt]

theorem map_update_tprod {s : ℕ} {M : Fin s → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (c : Fin s) (A : M c →ₗ[ℂ] M c) (v : ∀ i, M i) (x : M c) :
    PiTensorProduct.map (Function.update (fun c' => (LinearMap.id : M c' →ₗ[ℂ] M c')) c A)
      (PiTensorProduct.tprod ℂ (Function.update v c x)) = PiTensorProduct.tprod ℂ (Function.update v c (A x)) := by
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext c'
  by_cases hc : c' = c
  · subst hc; simp
  · simp [Function.update_of_ne hc]

theorem factor_iso : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, Simple (lam c)) → ∀ (c : Fin s) (d : ℕ)
    (h : Fintype.card (GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.Block (natBlocks b) (c : ℕ)) = d) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin d) K) W), GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.HasFactor (natBlocks b) (leviTensor b lam) (c : ℕ) h ρ →
    ∃ (e : {i // b i = c} ≃ Fin d) (L : W ≃ₗ[ℂ] (lam c : Type)),
      ∀ g v, L (ρ g v) = (lam c).ρ ((glEquiv K e).symm g) (L v) := by
  intro K _ _ _ r s b lam hsimp c d h W _ _ ρ hF
  refine ⟨blockNum b c h, ?_⟩
  set e := blockNum b c h
  let ρ' : Representation ℂ (GL (Fin d) K) (lam c) := (Formalism.IrreducibleCountingLemmas.TYPES.transp e (lam c)).ρ
  have hirr : ρ'.IsIrreducible := GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple _ (Formalism.L2.PT.simple_transp e (hsimp c))
  have hnt : ∀ c', Nontrivial (lam c') := fun c' =>
    PI.GreenLabelSurjWork.nontrivial_of_simple _ (hsimp c')
  choose v hv using fun c' => exists_ne (0 : (lam c' : Type))
  let f : IntertwiningMap ρ' (blockRes (natBlocks b) (leviTensor b lam) (c : ℕ) h) :=
    ((PiTensorProduct.tprod ℂ).toLinearMap v c).intertwiningMap_of_isIntertwiningMap _ _ (fun g x => by
      rw [blockRes_leviTensor, MultilinearMap.toLinearMap_apply, MultilinearMap.toLinearMap_apply,
        map_update_tprod]
      rfl)
  have hinj : Function.Injective (IntertwiningMap.equivLinearMapAsModule ρ' _ f) :=
    tprod_update_injective v hv c
  have hiso := hF.2.of_injective _ hinj
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL (Fin d) K)) ρ'.asModule :=
    (irreducible_iff_isSimpleModule_asModule ρ').1 hirr
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL (Fin d) K)) (⊤ : Submodule (MonoidAlgebra ℂ (GL (Fin d) K)) ρ'.asModule) :=
    IsSimpleModule.congr (Submodule.topEquiv)
  let E : ρ.asModule ≃ₗ[MonoidAlgebra ℂ (GL (Fin d) K)] ρ'.asModule := ((hiso ⊤).some.symm.trans Submodule.topEquiv)
  let F : IntertwiningMap ρ ρ' := (IntertwiningMap.equivLinearMapAsModule ρ ρ').symm E.toLinearMap
  refine ⟨LinearEquiv.ofBijective F.toLinearMap E.bijective, fun g x => ?_⟩
  exact IntertwiningMap.isIntertwining ρ ρ' F g x

end Main

end GlobalTheory.HcIrr.Factor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCuspidalFactorAtBlockLeviPiTensorStatement
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, Simple (lam c)) → ∀ (c : Fin s) (d : ℕ) (h : Fintype.card (GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.Block (natBlocks b) (c : ℕ)) = d) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin d) K) W), GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.HasFactor (natBlocks b) (leviTensor b lam) (c : ℕ) h ρ → ∃ (e : {i // b i = c} ≃ Fin d) (L : W ≃ₗ[ℂ] (lam c : Type)), ∀ g v, L (ρ g v) = (lam c).ρ ((glEquiv K e).symm g) (L v) := by
  first | exact @GlobalTheory.HcIrr.Factor.factor_iso | exact GlobalTheory.HcIrr.Factor.factor_iso | (intros; apply GlobalTheory.HcIrr.Factor.factor_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalPiTensorNoBlockUnipotentFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalPiTensorNoBlockUnipotentFixed
noncomputable section

namespace GlobalTheory.HcIrr

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

section UnipGroup

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem unip_diag_mul (b : ι → Fin s) {g h : GL ι K} (hg : g ∈ unip K b) (hh : h ∈ unip K b)
    (i j : ι) (hij : b i = b j) : ((g * h : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hg.2 i i rfl, if_pos rfl, one_mul, hh.2 i j hij]
  · intro k _ hki
    rcases lt_trichotomy (b k) (b i) with hlt | heq | hgt
    · rw [hg.1.1 i k hlt, zero_mul]
    · rw [hg.2 i k heq.symm, if_neg (Ne.symm hki), zero_mul]
    · rw [hh.1.1 k j (by rw [← hij]; exact hgt), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem unip_diag_inv (b : ι → Fin s) {g : GL ι K} (hg : g ∈ unip K b)
    (i j : ι) (hij : b i = b j) : ((g⁻¹ : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
  have h1 : ((g⁻¹ * g : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single j] at h1
  · rwa [hg.2 j j rfl, if_pos rfl, mul_one] at h1
  · intro k _ hkj
    rcases lt_trichotomy (b k) (b i) with hlt | heq | hgt
    · rw [hg.1.2 i k hlt, zero_mul]
    · rw [hg.2 k j (heq.trans hij), if_neg hkj, mul_zero]
    · rw [hg.1.1 k j (by rw [← hij]; exact hgt), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

def cuspUnipGroup (b : ι → Fin s) : Subgroup (GL ι K) where
  carrier := unip K b
  one_mem' := ⟨one_mem _, fun i j _ => by rw [Units.val_one, Matrix.one_apply]⟩
  mul_mem' hg hh := ⟨mul_mem hg.1 hh.1, unip_diag_mul b hg hh⟩
  inv_mem' hg := ⟨inv_mem hg.1, unip_diag_inv b hg⟩

end UnipGroup

theorem tensor_eq_zero_of_fixed {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s)
    (U : Subgroup (GL {i // b i = c} K))
    (hU : ∀ v : (lam c : Type), (∀ u ∈ U, (lam c).ρ u v = v) → v = 0)
    (y : PiTensorProduct ℂ (fun c => (lam c : Type)))
    (hy : ∀ u ∈ U, PiTensorProduct.map (Function.update
      (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c ((lam c).ρ u)) y = y) :
    y = 0 := by
  classical
  let f : U → ((lam c : Type) →ₗ[ℂ] (lam c : Type)) := fun u => (lam c).ρ u
  have hinv : ∀ (g : U) (v : (lam c : Type)), f g (∑ u : U, f u v) = ∑ u : U, f u v := by
    intro g v
    have hm : ∀ u : U, f g (f u v) = f (g * u) v := fun u => by
      simp only [f, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [hm]
    exact Equiv.sum_comp (Equiv.mulLeft g) (fun u => f u v)
  have hA : (∑ u : U, f u) = 0 := by
    ext v
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    exact hU _ fun u hu => hinv ⟨u, hu⟩ v
  let F := PiTensorProduct.mapMultilinear ℂ (fun c => (lam c : Type)) (fun c => (lam c : Type))
  let m : ∀ c', (lam c' : Type) →ₗ[ℂ] (lam c' : Type) := fun c' => LinearMap.id
  have h1 : F (Function.update m c (∑ u : U, f u)) y = (Fintype.card U) • y := by
    rw [MultilinearMap.map_update_sum, LinearMap.sum_apply]
    have : ∀ u : U, F (Function.update m c (f u)) y = y := fun u => hy u u.2
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ]
  rw [hA, MultilinearMap.map_update_zero, LinearMap.zero_apply] at h1
  have hcard : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hcard

theorem cuspidal_tensor_no_unip_fixed : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → ∀ S : Finset (Fin r), (∃ i j, natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : PiTensorProduct ℂ (fun c => (lam c : Type)), (∀ u : blockTri (κ := K) (natBlocks b), (∀ i j, ((u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ≠ (1 : Matrix (Fin r) (Fin r) K) i j → natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → leviTensor b lam u y = y) → y = 0 := by
  intro K _ _ _ r s b lam hcusp S ⟨i, j, hb, hi, hj⟩ y hy
  have hb' : b i = b j := Fin.ext hb
  let c := b i
  let b₂ : {k // b k = c} → Fin 2 := fun k => if k.1 ∈ S then 0 else 1
  have hsurj : Function.Surjective b₂ := by
    intro t
    fin_cases t
    · exact ⟨⟨i, rfl⟩, by simp [b₂, hi]⟩
    · exact ⟨⟨j, hb'.symm⟩, by simp [b₂, hj]⟩
  refine tensor_eq_zero_of_fixed b lam c (cuspUnipGroup b₂)
    (fun v hv => hcusp c 2 b₂ hsurj le_rfl v hv) y ?_
  intro u' hu'
  have hu : u' ∈ unip K b₂ := hu'
  rw [← leviTensor_blockExt b lam c u']
  apply hy
  intro x z hxz
  by_cases hin : b x = c ∧ b z = c
  · refine ⟨by simp only [natBlocks, hin.1, hin.2], ?_⟩
    have e := blockExt_in b c u' ⟨x, hin.1⟩ ⟨z, hin.2⟩
    dsimp only at e
    rw [e] at hxz
    by_contra hcon
    apply hxz
    by_cases hxS : x ∈ S <;> by_cases hzS : z ∈ S
    · rw [hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]
      simp [Matrix.one_apply, Subtype.ext_iff]
    · exact absurd ⟨hxS, hzS⟩ hcon
    · rw [hu.1.1 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS]),
        Matrix.one_apply_ne (by rintro rfl; exact hxS hzS)]
    · rw [hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]
      simp [Matrix.one_apply, Subtype.ext_iff]
  · exact absurd (blockExt_out b c u' x z hin) hxz

end GlobalTheory.HcIrr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalPiTensorNoBlockUnipotentFixedStatement
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → ∀ S : Finset (Fin r), (∃ i j, natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : PiTensorProduct ℂ (fun c => (lam c : Type)), (∀ u : blockTri (κ := K) (natBlocks b), (∀ i j, ((u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ≠ (1 : Matrix (Fin r) (Fin r) K) i j → natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → leviTensor b lam u y = y) → y = 0 := by
  first | exact @GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed | exact GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed | (intros; apply GlobalTheory.HcIrr.cuspidal_tensor_no_unip_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrrRepHarishChandraDistinctCuspidalLabels
noncomputable section
namespace GlobalTheory.HcIrr
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV Polynomial CategoryTheory

theorem isIrrRep_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (A : G → G) (hA : Function.Surjective A)
    (Ψ : V ≃ₗ[ℂ] V') (h : ∀ g v, Ψ (ρ (A g) v) = ρ' g (Ψ v)) (hirr : IsIrrRep ρ') : IsIrrRep ρ := by
  obtain ⟨hn, hW⟩ := hirr
  refine ⟨Ψ.toEquiv.nontrivial, fun W hinv => ?_⟩
  have hinv' : ∀ g, ∀ v ∈ W.map (Ψ : V →ₗ[ℂ] V'), ρ' g v ∈ W.map (Ψ : V →ₗ[ℂ] V') := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨ρ (A g) w, hinv _ _ hw, h g w⟩
  rcases hW _ hinv' with h0 | h1
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hv' : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot] at hv'
    simpa using hv'
  · right
    refine eq_top_iff.2 fun v _ => ?_
    have : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := h1 ▸ Submodule.mem_top
    obtain ⟨w, hw, hwv⟩ := this
    rwa [← Ψ.injective hwv]

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem isIrrRep_hcRep_of_parInd (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (h : (GlobalTheory.FinGL.parInd (natBlocks b) (leviTensor b lam)).IsIrreducible) : IsIrrRep (hcRep K b lam) := by
  let L : hcSpace K b lam ≃ₗ[ℂ] Representation.coindV (blockTri (κ := K) (natBlocks b)).subtype (leviTensor b lam) :=
    { toFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (blockTri_le_parab b) p) x⟩
      invFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (parab_le_blockTri b) p) x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact isIrrRep_of_equiv (hcRep K b lam) _ id Function.surjective_id L (fun _ _ => rfl)
    (isIrrRep_of_isIrreducible _ h)

theorem exists_sorted {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hb : Function.Surjective b)
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) :
    ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧
      Monotone b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ (∀ c, labO O (lam' c) = labO O (lam c)) ∧
      (IsIrrRep (hcRep K b' lam') → IsIrrRep (hcRep K b lam)) := by
  let e : Fin r ≃ Fin r := (Tuple.sort b).symm
  let b' : Fin r → Fin s := b ∘ e.symm
  let ec : ∀ c, {i // b i = c} ≃ {k // b' k = c} := fun c => e.subtypeEquiv (fun i => by simp [b'])
  let lam' : ∀ c : Fin s, FDRep ℂ (GL {k // b' k = c} K) := fun c => transp (ec c) (lam c)
  let A : GL (Fin r) K ≃* GL (Fin r) K := (glEquiv K e).symm
  have hpar : ∀ p : parab K b', A p.1 ∈ parab K b := by
    intro p
    obtain ⟨h1, h2⟩ := p.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e.symm e.symm (p.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h1 _ _ (by simpa [b'] using hij)
    · rw [← map_inv]
      show Matrix.reindex e.symm e.symm ((p.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h2 _ _ (by simpa [b'] using hij)
  have hpar' : ∀ q : parab K b, A.symm q.1 ∈ parab K b' := by
    intro q
    obtain ⟨h1, h2⟩ := q.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e e (q.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h1 _ _ hij
    · rw [← map_inv]
      show Matrix.reindex e e ((q.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h2 _ _ hij
  have hlevi : ∀ (p : parab K b') (c : Fin s),
      levi K b c ⟨A p.1, hpar p⟩ = (glEquiv K (ec c)).symm (levi K b' c p) := by
    intro p c
    apply Units.ext
    ext i j
    rfl
  have hinfl : ∀ p : parab K b', infl K b lam ⟨A p.1, hpar p⟩ = infl K b' lam' p := by
    intro p
    unfold infl
    congr 1
  have hinfl' : ∀ q : parab K b, infl K b lam q = infl K b' lam' ⟨A.symm q.1, hpar' q⟩ := by
    intro q
    rw [← hinfl]
    congr 2
    exact Subtype.ext (A.apply_symm_apply q.1).symm
  let Ψ : hcSpace K b lam ≃ₗ[ℂ] hcSpace K b' lam' :=
    { toFun := fun F => ⟨fun x => F.1 (A x), fun p x => by
        show F.1 (A (p.1 * x)) = infl K b' lam' p (F.1 (A x))
        rw [map_mul, ← hinfl]
        exact F.2 ⟨A p.1, hpar p⟩ (A x)⟩
      invFun := fun F => ⟨fun x => F.1 (A.symm x), fun q x => by
        show F.1 (A.symm (q.1 * x)) = infl K b lam q (F.1 (A.symm x))
        rw [map_mul, hinfl']
        exact F.2 ⟨A.symm q.1, hpar' q⟩ (A.symm x)⟩
      map_add' := fun F G => rfl
      map_smul' := fun a F => rfl
      left_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.apply_symm_apply x))
      right_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.symm_apply_apply x)) }
  refine ⟨b', lam', hb.comp e.symm.surjective, ?_, fun c => ⟨Formalism.L2.PT.simple_transp _ (hl c).1,
    Formalism.L2.PT.isCuspidal_transp _ (hl c).2⟩, fun c => GlobalTheory.SerOSys.TranspLabel.labO_transp O (ec c) (lam c), ?_⟩
  · exact Tuple.monotone_sort b
  · refine isIrrRep_of_equiv _ _ A A.surjective Ψ fun g F => ?_
    apply Subtype.ext
    funext x
    show F.1 (A x * A g) = F.1 (A (x * g))
    rw [map_mul]

theorem labO_eq_of_readings {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (d : ℕ) (e : α ≃ Fin d) (e' : β ≃ Fin d) (σ : FDRep ℂ (GL α K))
    (σ' : FDRep ℂ (GL β K)) (M : (σ : Type) ≃ₗ[ℂ] (σ' : Type))
    (hM : ∀ g v, M (σ.ρ ((glEquiv K e).symm g) v) = σ'.ρ ((glEquiv K e').symm g) (M v)) :
    labO O σ = labO O σ' := by
  rw [← GlobalTheory.SerOSys.TranspLabel.labO_transp O e σ, ← GlobalTheory.SerOSys.TranspLabel.labO_transp O e' σ']
  unfold labO
  apply O.lab_iso
  exact ⟨GlobalTheory.SerOSys.TranspLabel.repIsoOf _ _ M fun γ v => hM _ v⟩

theorem distinctFactors {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hs : ∀ c, Simple (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.DistinctFactors (natBlocks b) (leviTensor b lam) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne ⟨d, h, h', W, _, _, ρ, hf, hf'⟩
  obtain ⟨e, L, hL⟩ := GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b i) d h W ρ hf
  obtain ⟨e', L', hL'⟩ := GlobalTheory.T.hasCuspidalFactorAtBlock_leviPiTensor K r s b lam hs (b j) d h' W ρ hf'
  have hlab : labO O (lam (b i)) = labO O (lam (b j)) := by
    refine labO_eq_of_readings O d e e' _ _ (L.symm.trans L') fun g v => ?_
    obtain ⟨w, rfl⟩ := L.surjective v
    rw [← hL]
    simp [hL']
  exact hne (congrArg (fun c : Fin s => (c : ℕ)) (hinj hlab))

theorem isIrrRep_of_monotone {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) (hm : Monotone b) : IsIrrRep (hcRep K b lam) := by
  have hd : GlobalTheory.FinGL.IsCuspDatum (natBlocks b) (leviTensor b lam) :=
    { mono := fun i j hij => hm hij
      irr := GlobalTheory.T.leviPiTensorRepresentation_isIrreducible K r s b lam fun c => (hl c).1
      infl := fun p hp => by
        rw [leviTensor_apply]
        have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) = LinearMap.id := by
          intro c
          have h1 : levi K b c (Subgroup.inclusion (blockTri_le_parab b) p) = 1 := by
            apply Units.ext
            ext x y
            have := hp x.1 y.1 (by simp [natBlocks, x.2, y.2])
            show ((p : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 = (1 : Matrix _ _ K) x y
            rw [this]
            simp [Matrix.one_apply, Subtype.ext_iff]
          rw [h1, map_one]
          rfl
        simp only [this]
        exact PiTensorProduct.map_id
      cusp := fun S hS y hy => GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed K r s b lam (fun c => (hl c).2) S hS y hy }
  exact isIrrRep_hcRep_of_parInd b lam
    ((GlobalTheory.CuspFactor.irrPar_iff_cuspidalProduct.1 GlobalTheory.FinGL.IrrProduct.irrPar).1 K r _ _ _ hd
      (distinctFactors O b lam (fun c => (hl c).1) hinj))

theorem isIrrRep_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∀ (C : LabelConv K) (O : LabelMap K C),
    Function.Injective (fun c => labO O (lam c)) → IsIrrRep (hcRep K b lam) := by
  intro K _ _ _ r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hm, hl', hlab, hback⟩ := exists_sorted O b lam hb hl
  exact hback (isIrrRep_of_monotone O b' lam' hl'
    (fun c c' h => hinj (by simpa [hlab] using h)) hm)

end GlobalTheory.HcIrr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrrRepHarishChandraDistinctCuspidalLabelsStatement
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrrRep_harishChandra_distinct_cuspidal_labels : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∀ (C : LabelConv K) (O : LabelMap K C), Function.Injective (fun c => labO O (lam c)) → IsIrrRep (hcRep K b lam) := by
  first | exact @GlobalTheory.HcIrr.isIrrRep_hcRep | exact GlobalTheory.HcIrr.isIrrRep_hcRep | (intros; apply GlobalTheory.HcIrr.isIrrRep_hcRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonotoneBlocksSameHarishChandraCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonotoneBlocksSameHarishChandraCharacter
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.HCSort

open Formalism.L2.PT GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem trace_conj_rep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (P g : G) : LinearMap.trace ℂ V (ρ (P * g * P⁻¹)) = LinearMap.trace ℂ V (ρ g) := by
  let E : V ≃ₗ[ℂ] V := LinearEquiv.ofLinearMap (ρ P) (ρ P⁻¹)
    (LinearMap.ext fun v => by
      show (ρ P * ρ P⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (LinearMap.ext fun v => by
      show (ρ P⁻¹ * ρ P) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl)
  have h : E.conj (ρ g) = ρ (P * g * P⁻¹) := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply, map_mul, map_mul]
    rfl
  rw [← h, LinearMap.trace_conj']

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {s : ℕ}

def blockEquiv (e : ι ≃ κ) (b : ι → Fin s) (c : Fin s) : {i // b i = c} ≃ {k // (b ∘ e.symm) k = c} :=
  e.subtypeEquiv (fun i => by simp)

def lamT (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s) :
    FDRep ℂ (GL {k // (b ∘ e.symm) k = c} K) :=
  Formalism.IrreducibleCountingLemmas.TYPES.transp (blockEquiv e b c) (lam c)

theorem mem_parab_symm (e : ι ≃ κ) (b : ι → Fin s) (p : parab K (b ∘ e.symm)) :
    (glEquiv K e).symm p.1 ∈ parab K b := by
  obtain ⟨h1, h2⟩ := p.2
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · show Matrix.reindex e.symm e.symm (p.1 : Matrix κ κ K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    exact h1 _ _ (by simpa using hij)
  · rw [← map_inv]
    show Matrix.reindex e.symm e.symm ((p.1⁻¹ : GL κ K) : Matrix κ κ K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
    exact h2 _ _ (by simpa using hij)

theorem mem_parab (e : ι ≃ κ) (b : ι → Fin s) (p : parab K b) :
    glEquiv K e p.1 ∈ parab K (b ∘ e.symm) := by
  obtain ⟨h1, h2⟩ := p.2
  refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
  · show Matrix.reindex e e (p.1 : Matrix ι ι K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact h1 _ _ (by simpa using hij)
  · rw [← map_inv]
    show Matrix.reindex e e ((p.1⁻¹ : GL ι K) : Matrix ι ι K) i j = 0
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact h2 _ _ (by simpa using hij)

theorem infl_symm (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (p : parab K (b ∘ e.symm)) :
    infl K b lam ⟨(glEquiv K e).symm p.1, mem_parab_symm e b p⟩ = infl K (b ∘ e.symm) (lamT e b lam) p := by
  unfold infl
  congr 1

def hcEquiv (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) :
    hcSpace K b lam ≃ₗ[ℂ] hcSpace K (b ∘ e.symm) (lamT e b lam) where
  toFun F := ⟨fun x => F.1 ((glEquiv K e).symm x), fun p x => by
    show F.1 ((glEquiv K e).symm (p.1 * x)) = infl K (b ∘ e.symm) (lamT e b lam) p (F.1 ((glEquiv K e).symm x))
    rw [map_mul, ← infl_symm]
    exact F.2 ⟨_, mem_parab_symm e b p⟩ _⟩
  map_add' F G := rfl
  map_smul' a F := rfl
  invFun F := ⟨fun y => F.1 (glEquiv K e y), fun p y => by
    show F.1 (glEquiv K e (p.1 * y)) = infl K b lam p (F.1 (glEquiv K e y))
    have hp : (⟨(glEquiv K e).symm (glEquiv K e p.1), mem_parab_symm e b ⟨_, mem_parab e b p⟩⟩ : parab K b) = p :=
      Subtype.ext ((glEquiv K e).symm_apply_apply p.1)
    have hi : infl K b lam p = infl K b lam ⟨(glEquiv K e).symm (glEquiv K e p.1), _⟩ := congrArg _ hp.symm
    rw [map_mul, hi]
    exact (F.2 ⟨_, mem_parab e b p⟩ (glEquiv K e y)).trans
      (LinearMap.congr_fun (infl_symm e b lam ⟨_, mem_parab e b p⟩).symm _)⟩
  left_inv F := by
    apply Subtype.ext
    funext y
    show F.1 ((glEquiv K e).symm (glEquiv K e y)) = F.1 y
    rw [MulEquiv.symm_apply_apply]
  right_inv F := by
    apply Subtype.ext
    funext x
    show F.1 (glEquiv K e ((glEquiv K e).symm x)) = F.1 x
    rw [MulEquiv.apply_symm_apply]

theorem trace_hcRep_lamT (e : ι ≃ κ) (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (g : GL κ K) :
    LinearMap.trace ℂ _ (hcRep K (b ∘ e.symm) (lamT e b lam) g) =
      LinearMap.trace ℂ _ (hcRep K b lam ((glEquiv K e).symm g)) := by
  have hconj : (hcEquiv e b lam).conj (hcRep K b lam ((glEquiv K e).symm g)) = hcRep K (b ∘ e.symm) (lamT e b lam) g := by
    apply LinearMap.ext
    intro F
    rw [LinearEquiv.conj_apply_apply]
    apply Subtype.ext
    funext x
    show F.1 (glEquiv K e ((glEquiv K e).symm x * (glEquiv K e).symm g)) = F.1 (x * g)
    rw [← map_mul, MulEquiv.apply_symm_apply]
  rw [← hconj, LinearMap.trace_conj']

end GlobalTheory.HCSort

namespace GlobalTheory.HCSort

theorem exists_monotone_same_trace : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ Monotone b' ∧ ∀ x : GL (Fin r) K, LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) = LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) := by
  intro K _ _ _ r s b lam hb hl
  let e : Fin r ≃ Fin r := (Tuple.sort b).symm
  refine ⟨b ∘ e.symm, lamT e b lam, hb.comp e.symm.surjective,
    fun c => ⟨Formalism.L2.PT.simple_transp _ (hl c).1, Formalism.L2.PT.isCuspidal_transp _ (hl c).2⟩, ?_, fun x => ?_⟩
  · show Monotone (b ∘ (Tuple.sort b).symm.symm)
    rw [Equiv.symm_symm]
    exact Tuple.monotone_sort b
  · rw [trace_hcRep_lamT]
    let P : GL (Fin r) K := ⟨e.toPEquiv.toMatrix, e.symm.toPEquiv.toMatrix,
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl],
      by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]⟩
    have h : (glEquiv K e).symm x = P * x * P⁻¹ := by
      apply Units.ext
      change Matrix.reindex e.symm e.symm (x : Matrix (Fin r) (Fin r) K) =
        e.toPEquiv.toMatrix * (x : Matrix (Fin r) (Fin r) K) * e.symm.toPEquiv.toMatrix
      rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
      rfl
    rw [h, trace_conj_rep]

end GlobalTheory.HCSort
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonotoneBlocksSameHarishChandraCharacterStatement
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monotone_blocks_same_harishChandra_character : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ Monotone b' ∧ ∀ x : GL (Fin r) K, LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) = LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) := by
  first | exact @GlobalTheory.HCSort.exists_monotone_same_trace | exact GlobalTheory.HCSort.exists_monotone_same_trace | (intros; apply GlobalTheory.HCSort.exists_monotone_same_trace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeLabelIsCuspidalParabolicProductCharact
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.SqfreeCuspProd

theorem labO_irreducible {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}
    (O : LabelMap K C) {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {σ : FDRep ℂ (GL κ K)} (hs : Simple σ) (hc : IsCuspidal K σ) : Irreducible (labO O σ) :=
  (O.lab_spec _ _ (Nat.succ_le_of_lt Fintype.card_pos) (Formalism.L2.PT.simple_transp _ hs)
    (Formalism.L2.PT.isCuspidal_transp _ hc)).2.1

theorem injective_of_squarefree {R : Type} [CommMonoid R] {s : ℕ} (F : Fin s → R)
    (hF : ∀ c, Irreducible (F c)) (hsq : Squarefree (∏ c, F c)) : Function.Injective F := by
  intro c c' h
  by_contra hne
  have hd : F c * F c' ∣ ∏ x, F x := by
    rw [← Finset.mul_prod_erase Finset.univ F (Finset.mem_univ c),
      ← Finset.mul_prod_erase (Finset.univ.erase c) F
        (Finset.mem_erase.2 ⟨fun h' => hne h'.symm, Finset.mem_univ c'⟩), ← mul_assoc]
    exact dvd_mul_right _ _
  rw [h] at hd
  exact (hF c').not_isUnit (hsq _ hd)

theorem character_eq_of_constituent {Γ : Type} [Group Γ] (τ : FDRep ℂ Γ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ Γ V) (hτ : Simple τ) (hρ : IsIrrRep ρ) (hc : IsConstituent τ ρ)
    (x : Γ) : τ.character x = LinearMap.trace ℂ V (ρ x) := by
  obtain ⟨φ, hφ, hne⟩ := hc
  have hirr := (PI.GreenHCLabel.simple_irreducible Γ τ).1 hτ
  have hker : LinearMap.ker φ = ⊥ := by
    rcases hirr.2 (LinearMap.ker φ) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have := congrArg (fun k => k v) (hφ g)
      simp only [LinearMap.comp_apply] at this
      rw [this, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hne
  have hran : LinearMap.range φ = ⊤ := by
    rcases hρ.2 (LinearMap.range φ) (fun g v hv => by
      obtain ⟨y, rfl⟩ := hv
      exact ⟨τ.ρ g y, by simpa using congrArg (fun k => k y) (hφ g)⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.1 h) hne
    · exact h
  let e : τ ≃ₗ[ℂ] V :=
    LinearEquiv.ofBijective φ ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩
  haveI : Module.Finite ℂ V := Module.Finite.equiv e
  have hconj : e.conj (τ.ρ x) = ρ x := by
    ext v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    show e (τ.ρ x (e.symm (e w))) = ρ x (e w)
    rw [e.symm_apply_apply]
    exact congrArg (fun k => k w) (hφ x)
  rw [FDRep.character, ← hconj, LinearMap.trace_conj']

theorem isCuspProdChar_of_squarefree : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K)
    (O : LabelMap K C) (r : ℕ) (τ : FDRep ℂ (GL (Fin r) K)) (f : K[X]), Simple τ → HasLabelO O τ f →
    Squarefree f → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => τ.character x) := by
  intro K _ _ _ C O r τ f hτ hL hsq
  obtain ⟨s, b, lam, hb, hl, hc, rfl⟩ := hL
  have hirrF : ∀ c, Irreducible (labO O (lam c)) := fun c => by
    obtain ⟨i, hi⟩ := hb c
    haveI : Nonempty {i // b i = c} := ⟨⟨i, hi⟩⟩
    exact labO_irreducible O (hl c).1 (hl c).2
  have hinj := injective_of_squarefree _ hirrF hsq
  have hirr := GlobalTheory.T.isIrrRep_harishChandra_distinct_cuspidal_labels K r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hl', hmono, htr⟩ := GlobalTheory.T.exists_monotone_blocks_same_harishChandra_character K r s b lam hb hl
  have hcp := GlobalTheory.T.harishChandraInduction_cuspidalParabolicProduct K r s b' lam' hb' hl' hmono
  have hfun : (fun x : GL (Fin r) K => τ.character x) =
      fun x => LinearMap.trace ℂ (hcSpace K b' lam') (hcRep K b' lam' x) := by
    funext x
    rw [htr x]
    exact character_eq_of_constituent τ _ hτ hirr hc x
  rw [hfun]
  exact hcp

end GlobalTheory.SqfreeCuspProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeLabelIsCuspidalParabolicProductCharactStatement
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabel_isCuspidalParabolicProductCharacter : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (O : LabelMap K C) (r : ℕ) (τ : FDRep ℂ (GL (Fin r) K)) (f : K[X]), Simple τ → HasLabelO O τ f → Squarefree f → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => τ.character x) := by
  first | exact @GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree | exact GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree | (intros; apply GlobalTheory.SqfreeCuspProd.isCuspProdChar_of_squarefree <;> assumption)
end
