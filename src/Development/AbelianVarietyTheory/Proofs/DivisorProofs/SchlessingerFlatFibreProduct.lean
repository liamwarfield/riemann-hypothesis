module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorInjectiveOfPowSmulEqBot
open TensorProduct LinearMap Function

namespace GlobalTheory.NilpotentFlat

theorem rTensor_lTensor_apply {R : Type} [CommRing R] {M M' A A' : Type} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup A] [Module R A] [AddCommGroup A']
    [Module R A'] (g : M →ₗ[R] M') (f : A →ₗ[R] A') (x : M ⊗[R] A) :
    rTensor A' g (lTensor M f x) = lTensor M' f (rTensor A g x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor]

theorem rTensor_injective_of_flat_baseChange {A C M N' N : Type} [CommRing A] [CommRing C]
    [Algebra A C] [AddCommGroup M] [Module A M] [Module.Flat C (C ⊗[A] M)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A N'] [Module A N]
    [IsScalarTower A C N'] [IsScalarTower A C N] (ι : N' →ₗ[C] N) (hι : Injective ι) :
    Injective ((ι.restrictScalars A).rTensor M) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C N' M
  let e := AlgebraTensorModule.cancelBaseChange A C C N M
  have h1 : Injective (ι.rTensor (C ⊗[A] M)) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have key : ∀ z, (ι.restrictScalars A).rTensor M (e' z) = e (ι.rTensor (C ⊗[A] M) z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul n t =>
      induction t with
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

theorem lTensor_injective_of_flat {A C F N' N : Type} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup F] [Module A F] [Module C F] [IsScalarTower A C F] [Module.Flat C F]
    [AddCommGroup N'] [AddCommGroup N] [Module A N'] [Module A N] (ι : N' →ₗ[A] N)
    (hι : Injective (ι.rTensor C)) : Injective (ι.lTensor F) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C F N'
  let e := AlgebraTensorModule.cancelBaseChange A C C F N
  have hι' : Injective (ι.baseChange C) := (LinearMap.lTensor_inj_iff_rTensor_inj (M := C) ι).mpr hι
  have h1 : Injective ((ι.baseChange C).lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hι'
  have key : ∀ z, ι.lTensor F (e' z) = e ((ι.baseChange C).lTensor F z) := by
    intro z
    induction z with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul n t =>
      induction t with
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

variable {B : Type} [CommRing B]

theorem rTensor_injective_of_extension {K L : Type} [AddCommGroup K] [Module B K]
    [AddCommGroup L] [Module B L] [Module.Flat B L] (i : K →ₗ[B] L)
    {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module B N₁] [AddCommGroup N₂] [Module B N₂]
    [AddCommGroup N₃] [Module B N₃] (g₁ : N₁ →ₗ[B] N₂) (g₂ : N₂ →ₗ[B] N₃)
    (hg : Exact g₁ g₂) (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : Injective (i.rTensor N₁)) (h₃ : Injective (i.rTensor N₃)) :
    Injective (i.rTensor N₂) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have h2 : g₂.lTensor K x = 0 := by
    apply (injective_iff_map_eq_zero _).mp h₃
    rw [rTensor_lTensor_apply, hx, map_zero]
  obtain ⟨x₁, rfl⟩ := (lTensor_exact K hg hg₂ x).mp h2
  have h4 : i.rTensor N₁ x₁ = 0 := by
    apply (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := L) g₁ hg₁)
    rw [← rTensor_lTensor_apply, hx]
  simp [(injective_iff_map_eq_zero _).mp h₁ _ h4]

theorem rTensor_injective_quotient (I : Ideal B) {K L M : Type} [AddCommGroup K] [Module B K]
    [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M] (i : K →ₗ[B] L) (π : L →ₗ[B] M)
    (hi : Injective i) (hex : Exact i π) (hπ : Surjective π)
    (hIM : Injective (I.subtype.rTensor M)) : Injective (i.rTensor (B ⧸ I)) := by
  have h := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I) hex hπ hIM
    (Module.Flat.lTensor_preserves_injective_linearMap (M := B) i hi)
  exact (lTensor_inj_iff_rTensor_inj (B ⧸ I) i).mp h

theorem rTensor_injective_of_quotient_module (I : Ideal B) {K L M : Type} [AddCommGroup K]
    [Module B K] [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M] (i : K →ₗ[B] L)
    (π : L →ₗ[B] M) (hex : Exact i π) (hπ : Surjective π)
    [Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M)] (hI : Injective (i.rTensor (B ⧸ I)))
    (N : Type) [AddCommGroup N] [Module (B ⧸ I) N] [Module B N] [IsScalarTower B (B ⧸ I) N] :
    Injective (i.rTensor N) := by
  let p : (N →₀ (B ⧸ I)) →ₗ[B ⧸ I] N := Finsupp.linearCombination (B ⧸ I) id
  have hp : Surjective p := fun n => ⟨Finsupp.single n 1, by simp [p]⟩
  have h := lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (f₁ := (LinearMap.ker p).subtype.restrictScalars B) (f₂ := p.restrictScalars B)
    (LinearMap.exact_subtype_ker_map p) hp hex hπ
    (rTensor_injective_of_flat_baseChange (LinearMap.ker p).subtype (Submodule.injective_subtype _))
    (lTensor_injective_of_flat (C := B ⧸ I) (F := N →₀ (B ⧸ I)) i hI)
  exact (lTensor_inj_iff_rTensor_inj N i).mp h

theorem rTensor_injective_of_pow_smul_eq_bot (I : Ideal B) {K L : Type} [AddCommGroup K]
    [Module B K] [AddCommGroup L] [Module B L] [Module.Flat B L] (i : K →ₗ[B] L)
    (hbase : ∀ (N : Type) [AddCommGroup N] [Module (B ⧸ I) N] [Module B N]
      [IsScalarTower B (B ⧸ I) N], Injective (i.rTensor N)) (n : ℕ) :
    ∀ (N : Type) [AddCommGroup N] [Module B N], (I ^ n • ⊤ : Submodule B N) = ⊥ →
      Injective (i.rTensor N) := by
  induction n with
  | zero =>
    intro N _ _ hN
    have h0 : ∀ x : N, x = 0 := fun x => by
      have hx : x ∈ (I ^ 0 • ⊤ : Submodule B N) := by
        rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; trivial
      rw [hN] at hx
      simpa using hx
    have hz : ∀ z : K ⊗[B] N, z = 0 := fun z => by
      induction z with
      | tmul k x => rw [h0 x, tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    intro a b _
    rw [hz a, hz b]
  | succ n ih =>
    intro N _ _ hN
    let S : Submodule B N := I • ⊤
    refine rTensor_injective_of_extension i S.subtype S.mkQ (LinearMap.exact_subtype_mkQ S)
      S.injective_subtype (Submodule.mkQ_surjective S) (ih S ?_) (hbase (N ⧸ S))
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_smul'', Submodule.map_bot, Submodule.map_subtype_top, ← Submodule.mul_smul,
      ← pow_succ, hN]

theorem flat_of_isNilpotent : ∀ (B : Type) [CommRing B] (I : Ideal B), IsNilpotent I →
    ∀ (M : Type) [AddCommGroup M] [Module B M],
      Module.Flat (B ⧸ I) (M ⧸ (I • ⊤ : Submodule B M)) →
      Function.Injective (TensorProduct.lift ((LinearMap.lsmul B M).comp I.subtype)) →
      Module.Flat B M := by
  intro B _ I hI M _ _ hflat hinj
  obtain ⟨n, hn⟩ := hI
  let π : (M →₀ B) →ₗ[B] M := Finsupp.linearCombination B id
  have hπ : Surjective π := fun m => ⟨Finsupp.single m 1, by simp [π]⟩
  let K := LinearMap.ker π
  have hex : Exact K.subtype π := LinearMap.exact_subtype_ker_map π
  have hIM : Injective (I.subtype.rTensor M) := by
    have e : TensorProduct.lift ((LinearMap.lsmul B M).comp I.subtype) =
        (TensorProduct.lid B M).toLinearMap ∘ₗ I.subtype.rTensor M := by
      ext a m
      simp
    rw [e, LinearMap.coe_comp] at hinj
    exact hinj.of_comp
  let e : ((B ⧸ I) ⊗[B] M) ≃ₗ[B ⧸ I] (M ⧸ (I • ⊤ : Submodule B M)) :=
    (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  haveI : Module.Flat (B ⧸ I) ((B ⧸ I) ⊗[B] M) := Module.Flat.of_linearEquiv e
  have hq := rTensor_injective_quotient I K.subtype π K.injective_subtype hex hπ hIM
  have hall := rTensor_injective_of_pow_smul_eq_bot I K.subtype
    (rTensor_injective_of_quotient_module I K.subtype π hex hπ hq) n
  rw [Module.Flat.iff_lTensor_injective']
  intro J
  refine lTensor_injective_of_exact_of_exact_of_rTensor_injective hex hπ
    (LinearMap.exact_subtype_mkQ J) (Submodule.mkQ_surjective J) (hall (B ⧸ J) ?_)
    (Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype)
  rw [hn, Submodule.zero_eq_bot, Submodule.bot_smul]

end GlobalTheory.NilpotentFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTensorInjectiveOfFlatBaseChangeKerInf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTensorInjectiveOfFlatBaseChangeKerInf
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open TensorProduct

namespace GlobalTheory.TorStep

theorem mul_tensor_injective : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B]
    [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂),
    Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ →
    RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ →
    a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := by
  intro P R₂ B B₂ _ _ _ _ _ K₁ f₂ a₂ c₂ hf hc hcomp hker hK hflat
  letI := a₂.toAlgebra
  haveI : Module.Flat R₂ B₂ := hflat
  have hc' : ∀ p : P, c₂ (algebraMap P B p) = a₂ (f₂ p) := fun p => by
    simpa using congrArg (fun g : P →+* B₂ => g p) hcomp
  have hsmulB : ∀ (p : P) (b : B), c₂ (p • b) = f₂ p • c₂ b := fun p b => by
    rw [Algebra.smul_def, map_mul, hc', Algebra.smul_def, RingHom.algebraMap_toAlgebra]

  have hzero : ∀ x : P, x ∈ K₁ → f₂ x = 0 → x = 0 := fun x h1 h2 => by
    have : x ∈ K₁ ⊓ RingHom.ker f₂ := ⟨h1, h2⟩
    rw [hK] at this
    simpa using this

  have L0 : ∀ x : B, x ∈ RingHom.ker c₂ → ∀ k : K₁, (k ⊗ₜ[P] x : K₁ ⊗[P] B) = 0 := by
    intro x hx
    rw [hker, Ideal.map] at hx
    suffices H : ∀ (k : K₁) (y : B), (k ⊗ₜ[P] (y * x) : K₁ ⊗[P] B) = 0 by
      intro k; simpa using H k 1
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨κ, hκ, rfl⟩ := hz
      intro k y
      have e1 : y * algebraMap P B κ = κ • y := by rw [Algebra.smul_def, mul_comm]
      rw [e1, ← smul_tmul]
      have e2 : κ • k = 0 := by
        apply Subtype.ext
        apply hzero
        · exact (κ • k).2
        · simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
          rw [RingHom.mem_ker.mp hκ, zero_mul]
      rw [e2, zero_tmul]
    | zero => intro k y; rw [mul_zero, tmul_zero]
    | add u v _ _ hu hv => intro k y; rw [mul_add, tmul_add, hu, hv, add_zero]
    | smul b u _ hu => intro k y; rw [smul_eq_mul, ← mul_assoc]; exact hu k (y * b)
  have L1 : ∀ (k : K₁) (x y : B), c₂ x = c₂ y → (k ⊗ₜ[P] x : K₁ ⊗[P] B) = k ⊗ₜ[P] y := by
    intro k x y h
    rw [← sub_eq_zero, ← tmul_sub]
    exact L0 _ (by rw [RingHom.mem_ker, map_sub, h, sub_self]) k
  let s := Function.surjInv hc
  have hs : ∀ β, c₂ (s β) = β := Function.surjInv_eq hc
  let J₂ : Ideal R₂ := K₁.map f₂
  let ej : K₁ → J₂ := fun k => ⟨f₂ k, Ideal.mem_map_of_mem f₂ k.2⟩
  have hpre : ∀ j : J₂, ∃ k : P, k ∈ K₁ ∧ f₂ k = j := fun j =>
    (Ideal.mem_map_iff_of_surjective f₂ hf).mp j.2
  let einv : J₂ → K₁ := fun j => ⟨Classical.choose (hpre j), (Classical.choose_spec (hpre j)).1⟩
  have hE' : ∀ j : J₂, f₂ (einv j) = j := fun j => (Classical.choose_spec (hpre j)).2
  have hE : ∀ (k : K₁) (j : J₂), f₂ k = j → einv j = k := by
    intro k j h
    apply Subtype.ext
    rw [← sub_eq_zero]
    apply hzero
    · exact (einv j - k).2
    · rw [map_sub, hE', h, sub_self]

  let ψ0 : K₁ →+ B →+ J₂ ⊗[R₂] B₂ :=
    AddMonoidHom.mk' (fun k => AddMonoidHom.mk' (fun b => ej k ⊗ₜ[R₂] c₂ b)
      (fun b b' => by rw [map_add (f := _), tmul_add]))
      (fun k k' => by
        ext b
        have : ej (k + k') = ej k + ej k' := Subtype.ext (by simp [ej])
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, this, add_tmul])
  let ψ : K₁ ⊗[P] B →+ J₂ ⊗[R₂] B₂ := liftAddHom ψ0 (by
    intro p k b
    simp only [ψ0, AddMonoidHom.mk'_apply]
    have : ej (p • k) = f₂ p • ej k := Subtype.ext (by simp [ej])
    rw [this, hsmulB, smul_tmul])

  let χ0 : J₂ →+ B₂ →+ K₁ ⊗[P] B :=
    AddMonoidHom.mk' (fun j => AddMonoidHom.mk' (fun β => einv j ⊗ₜ[P] s β)
      (fun β β' => by rw [← tmul_add]; exact L1 _ _ _ (by rw [map_add (f := _), hs, hs, hs])))
      (fun j j' => by
        ext β
        have : einv (j + j') = einv j + einv j' :=
          hE _ _ (by rw [Submodule.coe_add, map_add (f := _), hE', hE', Submodule.coe_add])
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, this, add_tmul])
  let χ : J₂ ⊗[R₂] B₂ →+ K₁ ⊗[P] B := liftAddHom χ0 (by
    intro r j β
    simp only [χ0, AddMonoidHom.mk'_apply]
    obtain ⟨p, rfl⟩ := hf r
    have e1 : einv (f₂ p • j) = p • einv j :=
      hE _ _ (by simp [hE'])
    rw [e1, smul_tmul]
    exact L1 _ _ _ (by rw [hsmulB, hs, hs]))
  have hχψ : ∀ t, χ (ψ t) = t := by
    intro t
    induction t with
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
    | tmul k b =>
      simp only [ψ, χ, liftAddHom_tmul, ψ0, χ0, AddMonoidHom.mk'_apply]
      rw [hE k (ej k) rfl]
      exact L1 _ _ _ (hs _)

  let ν : J₂ ⊗[R₂] B₂ →ₗ[R₂] B₂ :=
    (TensorProduct.lid R₂ B₂).toLinearMap ∘ₗ J₂.subtype.rTensor B₂
  have hν : Function.Injective ν :=
    (TensorProduct.lid R₂ B₂).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ J₂.injective_subtype)
  set μ := TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype) with hμ
  have key : ∀ t, ν (ψ t) = c₂ (μ t) := by
    intro t
    induction t with
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _), map_add (f := _)]
    | tmul k b =>
      simp only [ψ, liftAddHom_tmul, ψ0, AddMonoidHom.mk'_apply, ν, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, hμ, TensorProduct.lift.tmul, LinearMap.coe_comp,
        LinearMap.lsmul_apply]
      rw [hsmulB]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have h1 : ψ t = 0 := hν (by rw [key, ht, map_zero, map_zero])
  rw [← hχψ t, h1, map_zero]

end GlobalTheory.TorStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTensorInjectiveOfFlatBaseChangeKerInfStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_tensor_injective_of_flat_baseChange_ker_inf : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B] [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂), Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ → RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ → a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := by
  first | exact @GlobalTheory.TorStep.mul_tensor_injective | exact GlobalTheory.TorStep.mul_tensor_injective | (intros; apply GlobalTheory.TorStep.mul_tensor_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatQuotientSmulTopOfSurjectiveFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatQuotientSmulTopOfSurjectiveFlat
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem flat_quot_smul_top_of_surj_flat :
    ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B]
      (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ →
      Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ →
      RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat →
      Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := by
  intro P R₁ B B₁ _ _ _ _ _ f₁ a₁ c₁ hf hc hcomp hker ha
  set K := RingHom.ker f₁ with hK
  let σ : P ⧸ K ≃+* R₁ := RingHom.quotientKerEquivOfSurjective hf
  have hσ : ((a₁.comp (σ : P ⧸ K →+* R₁))).Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective σ.bijective) ha
  letI : Algebra (P ⧸ K) B₁ := (a₁.comp (σ : P ⧸ K →+* R₁)).toAlgebra
  haveI : Module.Flat (P ⧸ K) B₁ := hσ
  letI : Algebra P B₁ := (c₁.comp (algebraMap P B)).toAlgebra
  let g : B →ₗ[P] B₁ :=
    { toFun := c₁
      map_add' := c₁.map_add
      map_smul' := fun p b => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
        rfl }
  have hg : ∀ b, g b = c₁ b := fun _ => rfl
  have hkerg : LinearMap.ker g = (K • ⊤ : Submodule P B) := by
    ext b
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← hker, LinearMap.mem_ker,
      RingHom.mem_ker, hg]
  have hle : (K • ⊤ : Submodule P B) ≤ LinearMap.ker g := hkerg.ge
  let e₀ := (K • ⊤ : Submodule P B).liftQ g hle
  have he₀ : Function.Bijective e₀ := by
    constructor
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ hkerg.le
    · rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
      exact hc
  let e : (B ⧸ (K • ⊤ : Submodule P B)) ≃ₗ[P ⧸ K] B₁ :=
    LinearEquiv.ofBijective
      { toFun := e₀
        map_add' := e₀.map_add
        map_smul' := fun q x => by
          obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
          have h1 : (Ideal.Quotient.mk K p) • x = p • x := by
            rw [← IsScalarTower.algebraMap_smul (P ⧸ K) p x]
            rfl
          rw [h1, e₀.map_smul, RingHom.id_apply]
          change (c₁.comp (algebraMap P B)) p * e₀ x = a₁ (σ (Ideal.Quotient.mk K p)) * e₀ x
          rw [RingHom.quotientKerEquivOfSurjective_apply_mk, hcomp]
          rfl }
      he₀
  exact Module.Flat.of_linearEquiv e

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatQuotientSmulTopOfSurjectiveFlatStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_quotient_smul_top_of_surjective_flat : ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B] (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ → Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ → RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat → Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := by
  first | exact @GlobalTheory.flat_quot_smul_top_of_surj_flat | exact GlobalTheory.flat_quot_smul_top_of_surj_flat | (intros; apply GlobalTheory.flat_quot_smul_top_of_surj_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchlessingerFlatFibreProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.SchlessingerFlat

theorem exists_unique_of_isPullback : ∀ {P R₁ R₂ R₀ : CommRingCat.{0}} (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → ∀ (x : R₁) (y : R₂), g₁.hom x = g₂.hom y → ∃! p : P, f₁.hom p = x ∧ f₂.hom p = y := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h x y hxy
  have H := (Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))
  obtain ⟨p, hp₁, hp₂⟩ := H.2.2 x y hxy
  exact ⟨p, ⟨hp₁, hp₂⟩, fun q hq => H.2.1 q p ⟨hq.1.trans hp₁.symm, hq.2.trans hp₂.symm⟩⟩

theorem isPushout_of_surjective_of_ker : ∀ {P R B C : CommRingCat.{0}} (a : P ⟶ B) (f : P ⟶ R) (c : B ⟶ C) (a' : R ⟶ C), a ≫ c = f ≫ a' → Function.Surjective f → Function.Surjective c → RingHom.ker c.hom = (RingHom.ker f.hom).map a.hom → IsPushout a f c a' := by
  intro P R B C a f c a' w hf hc hk
  have hw : ∀ p, c.hom (a.hom p) = a'.hom (f.hom p) := fun p => congr($(w) p)
  have key : ∀ (s : PushoutCocone a f), RingHom.ker c.hom ≤ RingHom.ker s.inl.hom := by
    intro s
    rw [hk, Ideal.map_le_iff_le_comap]
    intro p hp
    have e : s.inl.hom (a.hom p) = s.inr.hom (f.hom p) := congr($(s.condition) p)
    rw [Ideal.mem_comap, RingHom.mem_ker, e, (RingHom.mem_ker).mp hp, map_zero]
  let d : ∀ (s : PushoutCocone a f), C ⟶ s.pt := fun s =>
    CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker c.hom) s.inl.hom (fun x hx => key s hx)).comp
      (RingHom.quotientKerEquivOfSurjective hc).symm.toRingHom)
  have hd : ∀ (s : PushoutCocone a f) (b : B), (d s).hom (c.hom b) = s.inl.hom b := by
    intro s b
    have : (RingHom.quotientKerEquivOfSurjective hc).symm (c.hom b) = Ideal.Quotient.mk _ b := by
      apply (RingHom.quotientKerEquivOfSurjective hc).injective
      simp
    simp [d, this]
    rfl
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_⟩⟩
  · intro s; ext b; exact hd s b
  · intro s; ext r
    obtain ⟨p, rfl⟩ := hf r
    change (d s).hom (a'.hom (f.hom p)) = s.inr.hom (f.hom p)
    rw [← hw, hd]
    exact congr($(s.condition) p)
  · intro s m h1 _
    ext x
    obtain ⟨b, rfl⟩ := hc x
    rw [hd]
    exact congr($(h1) b)

theorem surjective_ker_of_isPushout : ∀ {R₁ R₀ B₁ B₀ : CommRingCat.{0}} (a₁ : R₁ ⟶ B₁) (g₁ : R₁ ⟶ R₀) (b₁ : B₁ ⟶ B₀) (a₀ : R₀ ⟶ B₀), IsPushout a₁ g₁ b₁ a₀ → Function.Surjective g₁ → Function.Surjective b₁ ∧ RingHom.ker b₁.hom = (RingHom.ker g₁.hom).map a₁.hom := by
  intro R₁ R₀ B₁ B₀ a₁ g₁ b₁ a₀ h hg
  let J : Ideal B₁ := (RingHom.ker g₁.hom).map a₁.hom
  let q : B₁ ⟶ CommRingCat.of (B₁ ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let a' : R₀ ⟶ CommRingCat.of (B₁ ⧸ J) := CommRingCat.ofHom
    ((Ideal.quotientMap J a₁.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hg).symm.toRingHom)
  have w : a₁ ≫ q = g₁ ≫ a' := by
    ext r
    have e0 : (RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r) = Ideal.Quotient.mk _ r := by
      apply (RingHom.quotientKerEquivOfSurjective hg).injective
      simp
    change Ideal.Quotient.mk J (a₁.hom r) = Ideal.quotientMap J a₁.hom Ideal.le_comap_map ((RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r))
    rw [e0]
    rfl
  have h' := isPushout_of_surjective_of_ker a₁ g₁ q a' w hg Ideal.Quotient.mk_surjective Ideal.mk_ker
  have e := IsPushout.inl_isoIsPushout_hom _ _ h h'
  let φ := h.isoIsPushout _ _ h'
  have hb : ∀ x, φ.hom.hom (b₁.hom x) = Ideal.Quotient.mk J x := fun x => congr($(e) x)
  have hinj : Function.Injective φ.hom.hom := fun x y hxy => by
    simpa using congrArg φ.inv.hom hxy
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ.hom.hom y)
    exact ⟨x, hinj (by rw [hb, hx])⟩
  · ext x
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← hb]
    constructor
    · intro h0; rw [h0, map_zero]
    · intro h0; exact hinj (h0.trans (map_zero _).symm)

theorem ker_eq_map_of_fibre : ∀ (P R₁ R₂ B B₁ B₂ : Type) [CommRing P] [CommRing R₁] [CommRing R₂] [CommRing B] [CommRing B₁] [CommRing B₂] (f₁ : P →+* R₁) (f₂ : P →+* R₂) (a : P →+* B) (a₁ : R₁ →+* B₁) (a₂ : R₂ →+* B₂) (c₁ : B →+* B₁) (c₂ : B →+* B₂) (I₂ : Ideal R₂), c₁.comp a = a₁.comp f₁ → c₂.comp a = a₂.comp f₂ → Function.Surjective c₂ → (∀ k ∈ I₂, ∃ p : P, f₁ p = 0 ∧ f₂ p = k) → (∀ x : B, c₁ x = 0 → c₂ x = 0 → x = 0) → (∀ x : B, c₁ x = 0 → c₂ x ∈ I₂.map a₂) → RingHom.ker c₁ = (RingHom.ker f₁).map a := by
  intro P R₁ R₂ B B₁ B₂ _ _ _ _ _ _ f₁ f₂ a a₁ a₂ c₁ c₂ I₂ w₁ w₂ hc₂ hlift hj hker
  have w₁' : ∀ p, c₁ (a p) = a₁ (f₁ p) := fun p => by simpa using RingHom.congr_fun w₁ p
  have w₂' : ∀ p, c₂ (a p) = a₂ (f₂ p) := fun p => by simpa using RingHom.congr_fun w₂ p
  have claim : ∀ y ∈ I₂.map a₂, ∃ z ∈ (RingHom.ker f₁).map a, c₁ z = 0 ∧ c₂ z = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨p, hp1, hp2⟩ := hlift k hk
      exact ⟨a p, Ideal.mem_map_of_mem _ hp1, by rw [w₁', hp1, map_zero], by rw [w₂', hp2]⟩
    | zero => exact ⟨0, Ideal.zero_mem _, map_zero _, map_zero _⟩
    | add u v _ _ hu hv =>
      obtain ⟨z1, h1, e1, e1'⟩ := hu
      obtain ⟨z2, h2, e2, e2'⟩ := hv
      exact ⟨z1 + z2, Ideal.add_mem _ h1 h2, by rw [map_add (f := _), e1, e2, add_zero], by rw [map_add (f := _), e1', e2']⟩
    | smul s u _ hu =>
      obtain ⟨z, hz, e, e'⟩ := hu
      obtain ⟨t, rfl⟩ := hc₂ s
      exact ⟨t * z, Ideal.mul_mem_left _ _ hz, by rw [map_mul, e, mul_zero], by rw [map_mul, e', smul_eq_mul]⟩
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨z, hz, e, e'⟩ := claim _ (hker x hx)
    have h0 : x - z = 0 := hj _ (by rw [map_sub, hx, e, sub_zero]) (by rw [map_sub, e', sub_self])
    rw [sub_eq_zero.mp h0]
    exact hz
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, w₁', (RingHom.mem_ker).mp hp, map_zero]

theorem isNilpotent_ker_of_fibre : ∀ (P R₁ R₂ R₀ : Type) [CommRing P] [CommRing R₁] [CommRing R₂] [CommRing R₀] (f₁ : P →+* R₁) (f₂ : P →+* R₂) (g₁ : R₁ →+* R₀) (g₂ : R₂ →+* R₀), g₁.comp f₁ = g₂.comp f₂ → RingHom.ker f₁ ⊓ RingHom.ker f₂ = ⊥ → IsNilpotent (RingHom.ker g₂) → IsNilpotent (RingHom.ker f₁) := by
  intro P R₁ R₂ R₀ _ _ _ _ f₁ f₂ g₁ g₂ w hj hn
  obtain ⟨n, hn⟩ := hn
  refine ⟨n + 1, ?_⟩
  rw [Submodule.zero_eq_bot, eq_bot_iff]
  intro x hx
  have h1 : x ∈ RingHom.ker f₁ := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
  have hle : (RingHom.ker f₁).map f₂ ≤ RingHom.ker g₂ := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, ← w, RingHom.comp_apply,
      (RingHom.mem_ker).mp hy, map_zero]
  have h2 : f₂ x ∈ (RingHom.ker g₂) ^ (n + 1) := by
    have := Ideal.mem_map_of_mem f₂ hx
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle _ this
  rw [pow_succ, hn, Submodule.zero_eq_bot, Submodule.bot_mul] at h2
  have h3 : x ∈ RingHom.ker f₁ ⊓ RingHom.ker f₂ := ⟨h1, by simpa using h2⟩
  rw [hj] at h3
  exact h3

theorem mul_injective_of_flat : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B] [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂), Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ → RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ → a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := GlobalTheory.T.mul_tensor_injective_of_flat_baseChange_ker_inf

theorem flat_quotient_of_flat : ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B] (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ → Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ → RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat → Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := GlobalTheory.T.flat_quotient_smul_top_of_surjective_flat

theorem schlessinger_flat : ∀ (P R₁ R₂ R₀ B₁ B₂ B₀ B : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (a₁ : R₁ ⟶ B₁) (a₂ : R₂ ⟶ B₂) (a₀ : R₀ ⟶ B₀) (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₀) (c₁ : B ⟶ B₁) (c₂ : B ⟶ B₂) (a : P ⟶ B), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → IsPushout a₁ g₁ b₁ a₀ → IsPushout a₂ g₂ b₂ a₀ → a₁.hom.Flat → a₂.hom.Flat → IsPullback c₁ c₂ b₁ b₂ → a ≫ c₁ = f₁ ≫ a₁ → a ≫ c₂ = f₂ ≫ a₂ → a.hom.Flat ∧ IsPushout a f₁ c₁ a₁ ∧ IsPushout a f₂ c₂ a₂ := by
  intro P R₁ R₂ R₀ B₁ B₂ B₀ B f₁ f₂ g₁ g₂ a₁ a₂ a₀ b₁ b₂ c₁ c₂ a hP hg₁ hg₂ hn₁ hn₂ hA₁ hA₂ hfl₁ hfl₂ hB hac₁ hac₂
  have eP := exists_unique_of_isPullback f₁ f₂ g₁ g₂ hP
  have eB := exists_unique_of_isPullback c₁ c₂ b₁ b₂ hB
  obtain ⟨hb₁, hkb₁⟩ := surjective_ker_of_isPushout a₁ g₁ b₁ a₀ hA₁ hg₁
  obtain ⟨hb₂, hkb₂⟩ := surjective_ker_of_isPushout a₂ g₂ b₂ a₀ hA₂ hg₂
  have wP : g₁.hom.comp f₁.hom = g₂.hom.comp f₂.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hP.w]
  have wB : ∀ x, b₁.hom (c₁.hom x) = b₂.hom (c₂.hom x) := fun x => by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hB.w]
  have w₁ : c₁.hom.comp a.hom = a₁.hom.comp f₁.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₁]
  have w₂ : c₂.hom.comp a.hom = a₂.hom.comp f₂.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₂]
  have sf₁ : Function.Surjective f₁.hom := fun x => by
    obtain ⟨y, hy⟩ := hg₂ (g₁.hom x)
    obtain ⟨p, hp, -⟩ := eP x y hy.symm
    exact ⟨p, hp.1⟩
  have sf₂ : Function.Surjective f₂.hom := fun y => by
    obtain ⟨x, hx⟩ := hg₁ (g₂.hom y)
    obtain ⟨p, hp, -⟩ := eP x y hx
    exact ⟨p, hp.2⟩
  have sc₁ : Function.Surjective c₁.hom := fun x => by
    obtain ⟨y, hy⟩ := hb₂ (b₁.hom x)
    obtain ⟨p, hp, -⟩ := eB x y hy.symm
    exact ⟨p, hp.1⟩
  have sc₂ : Function.Surjective c₂.hom := fun y => by
    obtain ⟨x, hx⟩ := hb₁ (b₂.hom y)
    obtain ⟨p, hp, -⟩ := eB x y hx
    exact ⟨p, hp.2⟩
  have jB : ∀ x : B, c₁.hom x = 0 → c₂.hom x = 0 → x = 0 := fun x h1 h2 => by
    obtain ⟨p, -, hu⟩ := eB 0 0 (by simp)
    rw [hu x ⟨h1, h2⟩, hu 0 ⟨by simp, by simp⟩]
  have jP : RingHom.ker f₁.hom ⊓ RingHom.ker f₂.hom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨p, -, hu⟩ := eP 0 0 (by simp)
    rw [Ideal.mem_bot, hu x ⟨hx.1, hx.2⟩, hu 0 ⟨by simp, by simp⟩]
  have kc₁ : RingHom.ker c₁.hom = (RingHom.ker f₁.hom).map a.hom :=
    ker_eq_map_of_fibre P R₁ R₂ B B₁ B₂ f₁.hom f₂.hom a.hom a₁.hom a₂.hom c₁.hom c₂.hom (RingHom.ker g₂.hom) w₁ w₂ sc₂
      (fun k hk => by
        obtain ⟨p, hp, -⟩ := eP 0 k (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk).symm)
        exact ⟨p, hp.1, hp.2⟩) jB
      (fun x hx => by
        rw [← hkb₂, RingHom.mem_ker, ← wB, hx, map_zero])
  have kc₂ : RingHom.ker c₂.hom = (RingHom.ker f₂.hom).map a.hom :=
    ker_eq_map_of_fibre P R₂ R₁ B B₂ B₁ f₂.hom f₁.hom a.hom a₂.hom a₁.hom c₂.hom c₁.hom (RingHom.ker g₁.hom) w₂ w₁ sc₁
      (fun k hk => by
        obtain ⟨p, hp, -⟩ := eP k 0 (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk))
        exact ⟨p, hp.2, hp.1⟩) (fun x h2 h1 => jB x h1 h2)
      (fun x hx => by
        rw [← hkb₁, RingHom.mem_ker, wB, hx, map_zero])
  have nil₁ : IsNilpotent (RingHom.ker f₁.hom) :=
    isNilpotent_ker_of_fibre P R₁ R₂ R₀ f₁.hom f₂.hom g₁.hom g₂.hom wP jP hn₂
  refine ⟨?_, isPushout_of_surjective_of_ker a f₁ c₁ a₁ hac₁ sf₁ sc₁ kc₁, isPushout_of_surjective_of_ker a f₂ c₂ a₂ hac₂ sf₂ sc₂ kc₂⟩
  letI : Algebra P B := a.hom.toAlgebra
  change Module.Flat P B
  exact GlobalTheory.NilpotentFlat.flat_of_isNilpotent P (RingHom.ker f₁.hom) nil₁ B
    (flat_quotient_of_flat P R₁ B B₁ f₁.hom a₁.hom c₁.hom sf₁ sc₁ w₁ kc₁ hfl₁)
    (mul_injective_of_flat P R₂ B B₂ (RingHom.ker f₁.hom) f₂.hom a₂.hom c₂.hom sf₂ sc₂ w₂ kc₂ jP hfl₂)

end GlobalTheory.SchlessingerFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchlessingerFlatFibreProductStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schlessinger_flat_fibreProduct : ∀ (P R₁ R₂ R₀ B₁ B₂ B₀ B : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (a₁ : R₁ ⟶ B₁) (a₂ : R₂ ⟶ B₂) (a₀ : R₀ ⟶ B₀) (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₀) (c₁ : B ⟶ B₁) (c₂ : B ⟶ B₂) (a : P ⟶ B), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → IsPushout a₁ g₁ b₁ a₀ → IsPushout a₂ g₂ b₂ a₀ → a₁.hom.Flat → a₂.hom.Flat → IsPullback c₁ c₂ b₁ b₂ → a ≫ c₁ = f₁ ≫ a₁ → a ≫ c₂ = f₂ ≫ a₂ → a.hom.Flat ∧ IsPushout a f₁ c₁ a₁ ∧ IsPushout a f₂ c₂ a₂ := by
  first | exact @GlobalTheory.SchlessingerFlat.schlessinger_flat | exact GlobalTheory.SchlessingerFlat.schlessinger_flat | (intros; apply GlobalTheory.SchlessingerFlat.schlessinger_flat <;> assumption)
end
