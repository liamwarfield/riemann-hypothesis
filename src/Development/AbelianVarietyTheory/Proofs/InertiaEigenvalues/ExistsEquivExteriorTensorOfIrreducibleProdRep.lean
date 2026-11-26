module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRep
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def homSpace : Submodule ℂ (Y →ₗ[ℂ] X) where
  carrier := {φ | ∀ h v, φ (ρ h v) = τ (1, h) (φ v)}
  add_mem' := by
    intro a b ha hb h v
    simp [ha h v, hb h v]
  zero_mem' := by intro h v; simp
  smul_mem' := by
    intro c a ha h v
    simp [ha h v]

theorem commute_apply (g : G) (h : H) (x : X) : τ (g, 1) (τ (1, h) x) = τ (1, h) (τ (g, 1) x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

theorem apply_pair (g : G) (h : H) (x : X) : τ (g, h) x = τ (g, 1) (τ (1, h) x) := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp

def homRep : Representation ℂ G (homSpace τ ρ) where
  toFun g :=
    { toFun := fun φ => ⟨(τ (g, 1)).comp φ.1, fun h v => by
        simp only [LinearMap.comp_apply]
        rw [φ.2 h v, commute_apply]⟩
      map_add' := fun φ ψ => by ext; simp
      map_smul' := fun c φ => by ext; simp }
  map_one' := by
    ext φ v
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    simp [this]
  map_mul' a b := by
    ext φ v
    have : ((a * b, (1 : H)) : G × H) = (a, 1) * (b, 1) := by simp
    show τ (a * b, 1) _ = τ (a, 1) (τ (b, 1) _)
    rw [this, map_mul, Module.End.mul_apply]

@[simp] theorem homRep_apply_coe (g : G) (φ : homSpace τ ρ) :
    ((homRep τ ρ g φ : homSpace τ ρ) : Y →ₗ[ℂ] X) = (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) := rfl

def evMap : (extTensor (homRep τ ρ) ρ).IntertwiningMap τ where
  toLinearMap := TensorProduct.lift (homSpace τ ρ).subtype
  isIntertwining' gh := by
    apply TensorProduct.ext'
    intro φ v
    obtain ⟨g, h⟩ := gh
    simp only [LinearMap.comp_apply, extTensor_tmul, TensorProduct.lift.tmul, Submodule.subtype_apply,
      homRep_apply_coe]
    rw [φ.2 h v, ← apply_pair]

end GlobalTheory.TensorFactor

namespace GlobalTheory.TensorFactor

variable {G H X Y : Type} [Group G] [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
  [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y)

def diffMap (g : G) (φ : homSpace τ ρ) :
    ρ.IntertwiningMap (τ.comp (MonoidHom.inr G H)) where
  toLinearMap := (τ (g, 1)).comp (φ : Y →ₗ[ℂ] X) - (φ : Y →ₗ[ℂ] X)
  isIntertwining' h := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.inr_apply, map_sub]
    rw [φ.2 h v, commute_apply]

theorem homRep_eq_of_apply_eq [ρ.IsIrreducible] {g : G} {φ : homSpace τ ρ} {y : Y} (hy : y ≠ 0)
    (h : τ (g, 1) ((φ : Y →ₗ[ℂ] X) y) = (φ : Y →ₗ[ℂ] X) y) : homRep τ ρ g φ = φ := by
  rcases Representation.IsIrreducible.injective_or_eq_zero (diffMap τ ρ g φ) with hi | h0
  · refine absurd (hi (a₁ := y) (a₂ := 0) ?_) hy
    simp [diffMap, h]
  · apply Subtype.ext
    ext v
    have := congrArg (fun f => f v) h0
    simpa [diffMap, sub_eq_zero] using this

end GlobalTheory.TensorFactor


open GlobalTheory.TensorFactor in
theorem GlobalTheory.TensorFactor.exists_equiv_extTensor : ∀ (G H X Y : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y), IsSmooth τ → τ.IsIrreducible → ρ.IsIrreducible → (∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ (1, g) (φ v)) → Function.Injective (TensorProduct.lift M.subtype)) → (∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ (1, g) (ι v)) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W), IsSmooth σ ∧ σ.IsIrreducible ∧ Nonempty (τ.Equiv (extTensor σ ρ)) := by
  intro G H X Y _ _ _ _ _ _ _ _ _ _ τ ρ hτs hτ hρ hinj hex
  obtain ⟨ι, hι0, hι⟩ := hex
  haveI := hτ
  haveI := hρ
  have hev : Function.Injective (evMap τ ρ) := hinj (homSpace τ ρ) fun φ hφ => hφ
  let ι' : homSpace τ ρ := ⟨ι, hι⟩
  obtain ⟨y0, hy0⟩ : ∃ v, ι v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hι0 (LinearMap.ext h)
  have hy0' : y0 ≠ 0 := fun h => hy0 (by simp [h])
  have hsurj : Function.Surjective (evMap τ ρ) :=
    (Representation.IsIrreducible.surjective_or_eq_zero (evMap τ ρ)).resolve_right fun h0 =>
      hy0 (by simpa [evMap, ι'] using congrArg (fun f => f (ι' ⊗ₜ y0)) h0)
  refine ⟨homSpace τ ρ, inferInstance, inferInstance, homRep τ ρ, ?_, ?_,
    ⟨(Representation.IntertwiningMap.ofBijective (evMap τ ρ) ⟨hev, hsurj⟩).symm⟩⟩
  · refine isSmooth_of_nhds fun φ => ?_
    have hc : Continuous fun g : G => ((g, (1 : H)) : G × H) := by fun_prop
    refine Filter.mem_of_superset (((hτs ((φ : Y →ₗ[ℂ] X) y0)).preimage hc).mem_nhds ?_)
      fun g hg => homRep_eq_of_apply_eq τ ρ hy0' hg
    have : ((1 : G), (1 : H)) = (1 : G × H) := rfl
    show τ ((1 : G), (1 : H)) _ = _
    simp [this]
  · haveI : Nontrivial (Subrepresentation (homRep τ ρ)) := ⟨⊥, ⊤, fun h => by
      have h1 : ι' ∈ (⊤ : Subrepresentation (homRep τ ρ)).toSubmodule := Submodule.mem_top
      rw [← h] at h1
      have h2 : ι' = 0 := (Submodule.mem_bot ℂ).1 h1
      exact hι0 (congrArg Subtype.val h2)⟩
    refine ⟨fun S => ?_⟩
    let U : Subrepresentation τ :=
      { toSubmodule :=
          LinearMap.range ((evMap τ ρ).toLinearMap ∘ₗ LinearMap.rTensor Y S.toSubmodule.subtype)
        apply_mem_toSubmodule := by
          rintro ⟨g, h⟩ _ ⟨t, rfl⟩
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul ψ z =>
            refine ⟨⟨homRep τ ρ g ψ, S.apply_mem_toSubmodule g ψ.2⟩ ⊗ₜ ρ h z, ?_⟩
            show ((homRep τ ρ g ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) (ρ h z) =
              τ (g, h) (((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z)
            rw [homRep_apply_coe, LinearMap.comp_apply, (ψ : homSpace τ ρ).2 h z, ← apply_pair]
          | add a b ha hb =>
            rw [map_add (f := _), map_add (f := _)]
            exact add_mem ha hb }
    rcases IsSimpleOrder.eq_bot_or_eq_top U with hU | hU
    · left
      apply Subrepresentation.toSubmodule_injective
      refine eq_bot_iff.2 fun ψ hψ => (Submodule.mem_bot ℂ).2 (Subtype.ext (LinearMap.ext fun z => ?_))
      have hm : (evMap τ ρ).toLinearMap (LinearMap.rTensor Y S.toSubmodule.subtype (⟨ψ, hψ⟩ ⊗ₜ z)) ∈
          U.toSubmodule := ⟨⟨ψ, hψ⟩ ⊗ₜ z, rfl⟩
      rw [hU] at hm
      have h2 := (Submodule.mem_bot ℂ).1 hm
      have h3 : ((ψ : homSpace τ ρ) : Y →ₗ[ℂ] X) z = 0 := by simpa [evMap] using h2
      simpa using h3
    · right
      apply Subrepresentation.toSubmodule_injective
      refine eq_top_iff.2 fun φ _ => ?_
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hy0'
      let P : homSpace τ ρ ⊗[ℂ] Y →ₗ[ℂ] homSpace τ ρ :=
        (TensorProduct.rid ℂ (homSpace τ ρ)).toLinearMap ∘ₗ LinearMap.lTensor (homSpace τ ρ) l
      have hP : ∀ t, P (LinearMap.rTensor Y S.toSubmodule.subtype t) ∈ S.toSubmodule := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul ψ z => simpa [P] using S.toSubmodule.smul_mem (l z) ψ.2
        | add a b ha hb =>
          rw [map_add (f := _), map_add (f := _)]
          exact add_mem ha hb
      have hmem : evMap τ ρ (φ ⊗ₜ y0) ∈ U.toSubmodule := by
        rw [hU]
        exact Submodule.mem_top
      obtain ⟨t, ht⟩ := hmem
      have ht' : LinearMap.rTensor Y S.toSubmodule.subtype t = φ ⊗ₜ y0 :=
        hev (a₁ := LinearMap.rTensor Y S.toSubmodule.subtype t) (a₂ := φ ⊗ₜ y0) ht
      have := hP t
      rw [ht'] at this
      simpa [P, hl] using this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivExteriorTensorOfIrreducibleProdRepStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_exteriorTensor_of_irreducible_prod_rep : ∀ (G H X Y : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (G × H) X) (ρ : Representation ℂ H Y), IsSmooth τ → τ.IsIrreducible → ρ.IsIrreducible → (∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ (1, g) (φ v)) → Function.Injective (TensorProduct.lift M.subtype)) → (∃ ι : Y →ₗ[ℂ] X, ι ≠ 0 ∧ ∀ g v, ι (ρ g v) = τ (1, g) (ι v)) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ G W), IsSmooth σ ∧ σ.IsIrreducible ∧ Nonempty (τ.Equiv (extTensor σ ρ)) := by
  first | exact @GlobalTheory.TensorFactor.exists_equiv_extTensor | exact GlobalTheory.TensorFactor.exists_equiv_extTensor | (intros; apply GlobalTheory.TensorFactor.exists_equiv_extTensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeckeSumPreservesPrincipalLevelForms
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeckeSumPreservesPrincipalLevelForms
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.LocalHeckeLevel

theorem sum_mul_left_eq {Gp M : Type} [Group Gp] [AddCommMonoid M] (K : Subgroup Gp) (α : Gp) (C : Finset Gp)
    (h1 : ∀ γ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : Gp, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ C ∧ γ⁻¹ * x ∈ K)
    (F : Gp → M) (hF : ∀ x, ∀ κ ∈ K, F (x * κ) = F x) {k₀ : Gp} (hk₀ : k₀ ∈ K) :
    ∑ δ ∈ C, F (k₀ * δ) = ∑ δ ∈ C, F δ := by
  classical
  have hmem : ∀ k ∈ K, ∀ δ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ := by
    intro k hk δ hδ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h1 δ hδ
    exact ⟨k * k₁, K.mul_mem hk hk₁, k₂, hk₂, by simp only [mul_assoc]⟩
  let s : Gp → Gp → Gp := fun k δ =>
    if h : ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ then (h2 _ h).exists.choose else δ
  have hs : ∀ k ∈ K, ∀ δ ∈ C, s k δ ∈ C ∧ (s k δ)⁻¹ * (k * δ) ∈ K := by
    intro k hk δ hδ
    have h := hmem k hk δ hδ
    have e : s k δ = (h2 _ h).exists.choose := dif_pos h
    rw [e]
    exact (h2 _ h).exists.choose_spec
  have huniq : ∀ k ∈ K, ∀ δ ∈ C, ∀ γ ∈ C, γ⁻¹ * (k * δ) ∈ K → s k δ = γ := by
    intro k hk δ hδ γ hγ hγK
    exact (h2 _ (hmem k hk δ hδ)).unique (hs k hk δ hδ) ⟨hγ, hγK⟩
  have hinv : ∀ δ ∈ C, s k₀⁻¹ (s k₀ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀ hk₀ δ hδ
    apply huniq _ (K.inv_mem hk₀) _ hm _ hδ
    have e : δ⁻¹ * (k₀⁻¹ * s k₀ δ) = ((s k₀ δ)⁻¹ * (k₀ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  have hinv' : ∀ δ ∈ C, s k₀ (s k₀⁻¹ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀⁻¹ (K.inv_mem hk₀) δ hδ
    apply huniq _ hk₀ _ hm _ hδ
    have e : δ⁻¹ * (k₀ * s k₀⁻¹ δ) = ((s k₀⁻¹ δ)⁻¹ * (k₀⁻¹ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  refine Finset.sum_nbij' (s k₀) (s k₀⁻¹) (fun δ hδ => (hs k₀ hk₀ δ hδ).1)
    (fun δ hδ => (hs _ (K.inv_mem hk₀) δ hδ).1) hinv hinv' ?_
  intro δ hδ
  obtain ⟨_, hK⟩ := hs k₀ hk₀ δ hδ
  calc F (k₀ * δ) = F (s k₀ δ * ((s k₀ δ)⁻¹ * (k₀ * δ))) := by rw [mul_inv_cancel_left]
    _ = F (s k₀ δ) := hF _ _ hK

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_injective (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem suppF_mul {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : SuppF V f b) :
    SuppF V f (a * b) := by
  intro i j
  have e : mt V (a * b) - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by
    rw [mt_mul, sub_mul, one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, ha i l]

theorem suppF_inv {V : HSp D} {f : AE D} {a : GA D V} (ha : SuppF V f a) : SuppF V f a⁻¹ := by
  intro i j
  have e : mt V a⁻¹ - 1 = -(mt V a⁻¹ * (mt V a - 1)) := by
    rw [mul_sub, ← mt_mul, inv_mul_cancel, mt_one, mul_one]; abel
  rw [e, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, ha l j]

theorem suppF_one (V : HSp D) (f : AE D) : SuppF V f (1 : GA D V) := by
  intro i j
  simp [mt_one]

def suppSub (V : HSp D) (f : AE D) : Subgroup (GA D V) where
  carrier := {g | SuppF V f g}
  mul_mem' := suppF_mul
  one_mem' := suppF_one V f
  inv_mem' := suppF_inv

theorem comm_of_suppF_trivAt {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_injective
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul, mt_mul, e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem heckeOn_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ (α : GA D (Wc D i)), SuppF (Wc D i) f α → ∀ (C : Finset (GA D (Wc D i))), (∀ γ ∈ C, SuppF (Wc D i) f γ) → IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C → ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hLP v f hf α _ C hC hrep Tm hT
  obtain ⟨hle, hchi, cmp, hcmp1, hcmp2⟩ := hLP
  have hT' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) Tm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2
    (GlobalTheory.HeckeParts.isMultMap_heckeOn hT' (fun γ hγ => (hrep.1 γ hγ).1) ?_)
  intro w κ hκ g
  have hκ' : κ ∈ levW R i := hκ
  rw [hchi κ hκ', one_mul]
  show ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * δ)
  have hF : ∀ x, ∀ c ∈ levW R i, Tm w (x * c) = Tm w x := fun x c hc => by
    rw [hT'.lev w c hc x, hchi c hc, one_mul]
  obtain ⟨hs, ht⟩ := hcmp1 v f hf κ
  have hkv : cmp v κ ∈ levW R i := ((hcmp2 κ (hle hκ')).1.1 hκ') v
  have hk' : κ * (cmp v κ)⁻¹ ∈ levW R i := mul_mem hκ' (inv_mem hkv)
  calc ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * (cmp v κ * δ)) :=
        Finset.sum_congr rfl fun δ _ => by group
    _ = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * δ) :=
        sum_mul_left_eq (levW R i ⊓ suppSub (Wc D i) f) α C (fun γ hγ => (hrep.1 γ hγ).2)
          (fun x hx => hrep.2 x hx) (fun x => Tm w (g * (κ * (cmp v κ)⁻¹) * x))
          (fun x c hc => by simp only [← mul_assoc]; exact hF _ c hc.1) (k₀ := cmp v κ) ⟨hkv, hs⟩
    _ = ∑ δ ∈ C, Tm w (g * δ) := Finset.sum_congr rfl fun δ hδ => by
        rw [mul_assoc, ← comm_of_suppF_trivAt (hC δ hδ) ht, ← mul_assoc, hF _ _ hk']

end GlobalTheory.LocalHeckeLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeckeSumPreservesPrincipalLevelFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hecke_sum_preserves_principal_level_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ (α : GA D (Wc D i)), SuppF (Wc D i) f α → ∀ (C : Finset (GA D (Wc D i))), (∀ γ ∈ C, SuppF (Wc D i) f γ) → IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C → ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  first | exact @GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall | exact GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall | (intros; apply GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall <;> assumption)
end
end
