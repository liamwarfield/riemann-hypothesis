module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
public import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement
public import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
noncomputable section

open MeasureTheory

namespace Formalism.IndefR.Lift

section Chars

variable {C : Type*} [CommGroup C]

def tup (μ0 : ℕ → C) (ξ : C) (j : ℕ) : C := μ0 j * ξ

def attChr (μj η : C) (n : ℕ) : C := if Odd n then μj * η⁻¹ else μj

def chrStep (μ : ℕ → C) (η : C) (j : ℕ) : C × C :=
  if Odd j then (μ j * η⁻¹, μ j) else (μ j, μ j * η⁻¹)

def chrTh (μ : ℕ → C) (η : C) (j : ℕ) : C × C := (μ j, μ j * η⁻¹)

theorem chrStep_eq_att (μ : ℕ → C) (η : C) {r t j : ℕ} (hr : Odd r) (ht : Odd t) (hj : 1 ≤ j) :
    chrStep μ η j = (attChr (μ j) η (r + (j - 1) * t), attChr (μ j) η (r + j * t)) := by
  have hr' : r % 2 = 1 := Nat.odd_iff.mp hr
  have ht' : t % 2 = 1 := Nat.odd_iff.mp ht
  have e1 : (r + (j - 1) * t) % 2 = (r % 2 + (j - 1) % 2) % 2 := by
    rw [Nat.add_mod, Nat.mul_mod, ht', mul_one, Nat.mod_mod]
  have e2 : (r + j * t) % 2 = (r % 2 + j % 2) % 2 := by
    rw [Nat.add_mod, Nat.mul_mod, ht', mul_one, Nat.mod_mod]
  simp only [chrStep, attChr, Nat.odd_iff, e1, e2, hr']
  split_ifs <;> first | rfl | (exfalso; omega)

end Chars

section Step

variable {G H S Sinf Ds Dt : Type*} [MeasurableSpace H]
  [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt]

def liftInt (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (s : S) (F : H → ℂ) (g : G) : ℂ :=
  ∫ h in 𝓕, th g h s * F h ∂ν

structure IsIo (ν : Measure H) (𝓕 : Set H) (th : G → H → S → ℂ) (pt : Sinf → S)
    (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (io : CCs →ₗ[ℂ] CCt) : Prop where

  integ : ∀ F : CCs, ∀ φ v g,
    IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν

  eq : ∀ F : CCs, ∀ φ v g,
    liftInt ν 𝓕 th (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) g = ((io F : CCt) : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) g

def IsTPlus (ipDs : Ds →ₗ[ℂ] Ds →ₗ⋆[ℂ] ℂ) (ipDt : Dt →ₗ[ℂ] Dt →ₗ⋆[ℂ] ℂ) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt)
    (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds) : Prop :=
  ∀ φ v' v, ipDt (T φ v') v = ipDs v' (Tp φ v)

structure IsIoUp [MeasurableSpace G] (νG : Measure G) (𝓕G : Set G) (th : G → H → S → ℂ) (pt : Sinf → S)
    (Tp : Sinf →ₗ⋆[ℂ] Dt →ₗ[ℂ] Ds) (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) (up : CCt →ₗ[ℂ] CCs) : Prop where

  integ : ∀ u : CCt, ∀ φ v h,
    IntegrableOn (fun g => starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g) 𝓕G νG

  eq : ∀ u : CCt, ∀ φ v h,
    ∫ g in 𝓕G, starRingEnd ℂ (th g h (pt φ)) * (u : Dt →ₗ[ℂ] (G → ℂ)) v g ∂νG =
      ((up u : CCs) : Ds →ₗ[ℂ] (H → ℂ)) (Tp φ v) h

end Step

section Adj

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

end Adj

section Chain

variable {G : ℕ → Type*} {D : ℕ → Type*} [∀ j, AddCommGroup (D j)] [∀ j, Module ℂ (D j)]
  (CC : ∀ j, Submodule ℂ (D j →ₗ[ℂ] (G j → ℂ)))

def dnFrom (io : ∀ k, CC (k + 1) →ₗ[ℂ] CC k) : ∀ n, CC n →ₗ[ℂ] CC 0
  | 0 => LinearMap.id
  | n + 1 => dnFrom io n ∘ₗ io n

def thetaDn (io : ∀ k, CC (k + 1) →ₗ[ℂ] CC k) (m : ℕ) : CC m →ₗ[ℂ] CC 0 := dnFrom CC io m

def IsChainIo {S Sinf : ℕ → Type*} [∀ j, MeasurableSpace (G j)] [∀ j, AddCommGroup (Sinf j)]
    [∀ j, Module ℂ (Sinf j)] (m : ℕ) (ν : ∀ j, Measure (G j)) (𝓕 : ∀ j, Set (G j))
    (th : ∀ k, G k → G (k + 1) → S k → ℂ) (pt : ∀ k, Sinf k → S k)
    (T : ∀ k, Sinf k →ₗ[ℂ] D (k + 1) →ₗ[ℂ] D k) (io : ∀ k, CC (k + 1) →ₗ[ℂ] CC k) : Prop :=
  ∀ k < m, IsIo (ν (k + 1)) (𝓕 (k + 1)) (th k) (pt k) (T k) (CC (k + 1)) (CC k) (io k)

end Chain

section Rows

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

end Rows

section ThetaP

variable {G' H' S' Sinf' TK Tau : Type*} [MeasurableSpace H']
  [AddCommGroup Sinf'] [Module ℂ Sinf'] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]

def thetaPInt (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf' → S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf') (f : H' → Tau) (e : TK) (g : G') : ℂ :=
  ∫ h in 𝓕, th g h (pt (io e (f h))) ∂ν

structure IsThetaP (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf' → S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf') (A : Submodule ℂ (H' → Tau))
    (thP : A →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))) : Prop where

  integ : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν

  eq : ∀ f : A, ∀ e g, thP f e g = thetaPInt ν 𝓕 th pt io f e g

variable {A Amb : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb]

def IsLamP {Sig : Type*} (thW : A →ₗ[ℂ] Amb) (adj : Amb →ₗ[ℂ] A) (part : Sig → Submodule ℂ Amb)
    (lam : Sig → ℝ) : Prop :=
  ∀ σ, ∀ x ∈ part σ, thW (adj x) = (lam σ : ℂ) • x

end ThetaP

section Kap

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

def IsKap {Tup Sig : Type*} (m : ℕ) (dnup : Tup → N →ₗ[ℂ] N) (partE : Sig → Submodule ℂ N)
    (lam : Tup → ℕ → Sig → ℝ) (κ : ℝ) : Prop :=
  ∀ μ σ, ∀ x ∈ partE σ, dnup μ x = ((κ * ∏ j ∈ Finset.Icc 1 m, lam μ j σ : ℝ) : ℂ) • x

theorem IsKap.unique {Tup Sig : Type*} {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam : Tup → ℕ → Sig → ℝ} {κ κ' : ℝ} (h : IsKap m dnup partE lam κ) (h' : IsKap m dnup partE lam κ')
    (μ : Tup) (σ : Sig) (hσ : partE σ ≠ ⊥) (hl : ∏ j ∈ Finset.Icc 1 m, lam μ j σ ≠ 0) : κ = κ' := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have e := (h μ σ x hx).symm.trans (h' μ σ x hx)
  have e2 : (((κ * ∏ j ∈ Finset.Icc 1 m, lam μ j σ : ℝ) : ℂ) -
      ((κ' * ∏ j ∈ Finset.Icc 1 m, lam μ j σ : ℝ) : ℂ)) • x = 0 := by
    rw [sub_smul, e, sub_self]
  rcases smul_eq_zero.mp e2 with h0 | h0
  · have h1 : κ * ∏ j ∈ Finset.Icc 1 m, lam μ j σ = κ' * ∏ j ∈ Finset.Icc 1 m, lam μ j σ := by
      exact_mod_cast sub_eq_zero.mp h0
    exact mul_right_cancel₀ hl h1
  · exact absurd h0 hx0

end Kap

section Bu

variable {M N Mu : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

end Bu

section Statements

variable {M N Mu : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

def IoExists {G H S Sinf Ds Dt : Type*} [MeasurableSpace H] [AddCommGroup Sinf] [Module ℂ Sinf]
    [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt] (ν : Measure H) (𝓕 : Set H)
    (th : G → H → S → ℂ) (pt : Sinf → S) (T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt)
    (CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))) (CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))) : Prop :=
  ∃ io, IsIo ν 𝓕 th pt T CCs CCt io

def pet {X : Type*} [MeasurableSpace X] (ν : Measure X) (𝓕 : Set X) (f₁ f₂ : X → ℂ) : ℂ :=
  ∫ x in 𝓕, f₁ x * starRingEnd ℂ (f₂ x) ∂ν

def IsSchur {X Dm : Type*} [MeasurableSpace X] [AddCommGroup Dm] [Module ℂ Dm] (ν : Measure X) (𝓕 : Set X)
    (ipD : Dm →ₗ[ℂ] Dm →ₗ⋆[ℂ] ℂ) (CC : Submodule ℂ (Dm →ₗ[ℂ] (X → ℂ))) (ip : CC →ₗ[ℂ] CC →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ F₁ F₂ : CC, ∀ v v', pet ν 𝓕 ((F₁ : Dm →ₗ[ℂ] (X → ℂ)) v) ((F₂ : Dm →ₗ[ℂ] (X → ℂ)) v') = ip F₁ F₂ * ipD v v'

end Statements

section Kernels

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsPairKernel (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (V W : HSp D)
    (th : GA D V → GA D W → (Formalism.IndefR.Datum.WO V W → ℂ) → ℂ) : Prop :=
  ∃ ω : GA D V × GA D W →* Module.End ℂ (Formalism.IndefR.Datum.WO V W → ℂ),
    Formalism.IndefR.Datum.IsWeilDatumO ψ V W χS χT ω ∧ th = fun g h f => Formalism.IndefR.Datum.thetaKO ω g h f

def CharsOK (μ : ℕ → (AE D)ˣ →* Circle) (η : (AE D)ˣ →* Circle) (m : ℕ) : Prop :=
  IsHeckeChar D η ∧ UnramEverywhere D η ∧ ResEta D η 1 ∧ (∀ τ, HasInfExp D η τ (1 / 2)) ∧
    ∀ j ∈ Finset.Icc 1 m, IsHeckeChar D (μ j) ∧ ResEta D (μ j) 0

def PtTheta {Sinf : Type*} (ψ : AddChar (AF D.host.F) ℂ) (Vj Wj : HSp D)
    (pt : Sinf → (Formalism.IndefR.Datum.WO Vj Wj → ℂ)) : Prop :=
  ∀ φ, Formalism.IndefR.Datum.IsThetaFunO ψ Vj Wj (pt φ)

end Kernels

end Formalism.IndefR.Lift

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisFC

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

instance isModTopAE : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

instance topRingAE : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

abbrev bA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    Module.Basis (Fin (Module.finrank F E)) (AF F) (AF F ⊗[F] E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

def cE (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    (AF F ⊗[F] E) ≃L[AF F] (Fin (Module.finrank F E) → AF F) :=
  { (bA F E).equivFun with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (bA F E).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (bA F E).equivFun.symm.toLinearMap }

theorem cE_tmul (e : E) (k : Fin (Module.finrank F E)) :
    cE F E ((1 : AF F) ⊗ₜ[F] e) k = algebraMap F (AF F) ((Module.finBasis F E).repr e k) := by
  change (bA F E).equivFun ((1 : AF F) ⊗ₜ[F] e) k = _
  rw [Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

instance lcAE : LocallyCompactSpace (AF F ⊗[F] E) :=
  (cE F E).toHomeomorph.isClosedEmbedding.locallyCompactSpace

instance t2AE : T2Space (AF F ⊗[F] E) :=
  T2Space.of_injective_continuous (cE F E).injective (cE F E).continuous

end Tens

section D7

variable {D : D7}

abbrev nE (D : D7) : ℕ := Module.finrank D.host.F D.host.E

def Phi (V W : HSp D) (x : WA V W) : Fin V.rank → Fin W.rank → Fin (nE D) → AF D.host.F :=
  fun i j => cE D.host.F D.host.E (x i j)

theorem Phi_add (V W : HSp D) (x y : WA V W) (i j k) : Phi V W (x + y) i j k = Phi V W x i j k + Phi V W y i j k := by
  simp only [Phi, Matrix.add_apply, map_add (f := _), Pi.add_apply]

theorem Phi_rat (V W : HSp D) (e : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (i j k) :
    Phi V W (e.map (incA D)) i j k = algebraMap D.host.F (AF D.host.F) ((Module.finBasis D.host.F D.host.E).repr (e i j) k) := by
  exact cE_tmul (e i j) k

theorem cont_Phi (V W : HSp D) (i j k) : Continuous fun x : WA V W => Phi V W x i j k := by
  unfold Phi
  exact (continuous_apply k).comp ((cE D.host.F D.host.E).continuous.comp
    ((continuous_apply j).comp (continuous_apply i)))

def FD (V W : HSp D) : Set (WA V W) := {x | ∀ i j k, Phi V W x i j k ∈ F0 D.host.F}

theorem exU (V W : HSp D) (x : WA V W) : ∃! g : ratL V W, g +ᵥ x ∈ FD V W := by
  classical
  choose q hq using fun i j k => PHeisFC.ad_exU (F := D.host.F) (Phi V W x i j k)
  let b := Module.finBasis D.host.F D.host.E
  let e : Matrix (Fin V.rank) (Fin W.rank) D.host.E := fun i j => b.equivFun.symm (q i j)
  have hrep : ∀ i j k, b.repr (e i j) k = q i j k := by
    intro i j k
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]

  have hshift : ∀ (e' : Matrix (Fin V.rank) (Fin W.rank) D.host.E) i j k,
      Phi V W (e'.map (incA D) + x) i j k =
        algebraMap D.host.F (AF D.host.F) (b.repr (e' i j) k) + Phi V W x i j k := by
    intro e' i j k
    rw [Phi_add, Phi_rat]
  refine ⟨⟨e.map (incA D), ⟨e, rfl⟩⟩, ?_, ?_⟩
  · intro i j k
    show Phi V W (e.map (incA D) + x) i j k ∈ F0 D.host.F
    rw [hshift, hrep]
    exact (hq i j k).1
  · rintro ⟨g, e', rfl⟩ hg
    apply Subtype.ext
    show e'.map (incA D) = e.map (incA D)
    have he : e' = e := by
      ext i j
      refine b.ext_elem fun k => ?_
      rw [hrep]
      have h1 := hg i j k
      change Phi V W (e'.map (incA D) + x) i j k ∈ F0 D.host.F at h1
      rw [hshift] at h1
      exact (hq i j k).2 _ h1
    rw [he]

instance borelWA (V W : HSp D) : BorelSpace (WA V W) := ⟨rfl⟩

open scoped Classical in
theorem meas_FD (V W : HSp D) : MeasurableSet (FD V W) := by
  classical
  have heM : Continuous (eM D.host.F) := by
    rw [show (⇑(eM D.host.F)) = _ from funext (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply D.host.F)]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous.comp
        (continuous_apply _)
    · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding _).continuous.comp
        (continuous_apply _)
  have hset : FD V W = ⋂ i, ⋂ j, ⋂ k,
      ((fun x => eM D.host.F (Phi V W x i j k).1) ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis D.host.F) ∩
        (fun x => (Phi V W x i j k).2) ⁻¹' Ohat D.host.F) := by
    ext x
    simp only [FD, F0, Pinf, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff]
  rw [hset]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => ?_
  refine MeasurableSet.inter ?_ ?_
  · exact (heM.comp (continuous_fst.comp (cont_Phi V W i j k))).measurable (measurableSet_Pinf D.host.F)
  · exact ((isOpen_Ohat D.host.F).preimage (continuous_snd.comp (cont_Phi V W i j k))).measurableSet

theorem FD_sub_compact (V W : HSp D) : ∃ K : Set (WA V W), IsCompact K ∧ FD V W ⊆ K := by
  obtain ⟨K0, hK0, hF0⟩ := fundamental_set_subset_compact (F := D.host.F)
  let g : (Fin V.rank → Fin W.rank → Fin (nE D) → AF D.host.F) → WA V W :=
    fun φ i j => (cE D.host.F D.host.E).symm (φ i j)
  have hg : Continuous g :=
    continuous_pi fun i => continuous_pi fun j =>
      (cE D.host.F D.host.E).symm.continuous.comp ((continuous_apply j).comp (continuous_apply i))
  refine ⟨g '' Set.univ.pi (fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => K0), ?_, ?_⟩
  · exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK0).image hg
  · intro x hx
    refine ⟨fun i j => cE D.host.F D.host.E (x i j), ?_, ?_⟩
    · intro i _ j _ k _
      exact hF0 (hx i j k)
    · funext i j
      exact (cE D.host.F D.host.E).symm_apply_apply (x i j)

instance tagWA (V W : HSp D) : IsTopologicalAddGroup (WA V W) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin V.rank → Fin W.rank → AE D))

instance lcWA (V W : HSp D) : LocallyCompactSpace (WA V W) :=
  inferInstanceAs (LocallyCompactSpace (Fin V.rank → Fin W.rank → AE D))

instance t2WA (V W : HSp D) : T2Space (WA V W) :=
  inferInstanceAs (T2Space (Fin V.rank → Fin W.rank → AE D))

instance measAddWA (V W : HSp D) : MeasurableAdd (WA V W) :=
  ⟨fun _ => (continuous_const.add continuous_id).measurable, fun _ => (continuous_id.add continuous_const).measurable⟩

theorem countable_ratL (V W : HSp D) : Countable (ratL V W) := by
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin V.rank) (Fin W.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin W.rank → D.host.E))
  have h : (ratL V W : Set (WA V W)).Countable := by
    unfold ratL
    rw [AddMonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem finCovol {D : D7} (V W : HSp D) : Formalism.IndefR.Heis.FinCovol V W := by
  haveI := countable_ratL V W
  obtain ⟨K, hK, hFK⟩ := FD_sub_compact V W
  have hfd : ∀ μ : Measure (WA V W), IsAddFundamentalDomain (ratL V W) (FD V W) μ :=
    fun μ => IsAddFundamentalDomain.mk' (meas_FD V W).nullMeasurableSet (exU V W)
  refine ⟨⟨Measure.addHaar, FD V W, inferInstance, hfd _⟩, fun μ 𝓕 hμ h𝓕 => ?_⟩
  set_option synthInstance.maxHeartbeats 200000 in
    rw [h𝓕.measure_eq (hfd μ)]
  exact (measure_mono hFK).trans_lt hK.measure_lt_top

end D7

end Formalism.IndefR.PHeisFC

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas
noncomputable section

open Matrix

namespace Formalism.IndefR.Datum

end Formalism.IndefR.Datum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace Formalism.IndefR.Datum.Brg

section Gen
variable {R : Type*} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem hO_tr (I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a = (I * (y.map c)ᵀ * K * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a
      = ∑ b, ∑ d, ∑ c', I a b * c (y c' b) * K c' d * x d a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c', I a b * c (y c' b) * K c' d * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem small_gen (G I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (hIG : I * G = 1)
    (hI : (I.map c)ᵀ = I) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c ((y * I)ᵀ i j) * G k i * K j l * (x * I)ᵀ k l =
      ∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a := by
  rw [sum_eq_trace, hO_tr, ← Matrix.trace_transpose]
  have e : ((y * I)ᵀ).map c = I * (y.map c)ᵀ := by
    rw [Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hI]
  rw [e]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = (K * (x * ((I * G) * I * (y.map c)ᵀ))).trace := by simp only [Matrix.mul_assoc]
    _ = ((K * x) * (I * (y.map c)ᵀ)).trace := by rw [hIG, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

theorem inv_gen (G I g g' : Matrix (Fin n) (Fin n) R) (hIG : I * G = 1) (hGI : G * I = 1) (hg : g * g' = 1)
    (h : (g.map c)ᵀ * G * g = G) : g' * I = I * (g.map c)ᵀ := by
  calc g' * I = (I * G) * g' * I := by rw [hIG, Matrix.one_mul]
    _ = I * ((g.map c)ᵀ * G * g) * g' * I := by rw [h]
    _ = I * (g.map c)ᵀ * (G * (g * g') * I) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, Matrix.mul_one, hGI, Matrix.mul_one]

theorem small_act (I g g' : Matrix (Fin n) (Fin n) R) (k : Matrix (Fin m) (Fin m) R) (h : g' * I = I * (g.map c)ᵀ)
    (x : Matrix (Fin m) (Fin n) R) : (k * x * g' * I)ᵀ = g.map c * (x * I)ᵀ * kᵀ := by
  rw [Matrix.mul_assoc (k * x), h]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem large_gen (hc : ∀ a, c (c a) = a) (G I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (hGI : G * I = 1) (hI : (I.map c)ᵀ = I) (hK : (K.map c)ᵀ = K) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c ((I * (y.map c)ᵀ)ᵀ i j) * K k i * G j l * (I * (x.map c)ᵀ)ᵀ k l =
      c (∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a) := by
  have e0 : (y.map c).map c = y := by ext i j; simp [hc]
  have t : ∀ M : Matrix (Fin n) (Fin n) R, c M.trace = ((M.map c)ᵀ).trace := by
    intro M; simp [Matrix.trace, map_sum]
  have e : ((I * (y.map c)ᵀ)ᵀ).map c = y * I := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, e0, Matrix.transpose_map, hI]
  have e2 : ((I * (y.map c)ᵀ * K * x).map c)ᵀ = (x.map c)ᵀ * K * y * I := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, hI, hK, Matrix.transpose_map, e0, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [sum_eq_trace, hO_tr, t, e2, ← Matrix.trace_transpose, e]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = ((G * I) * ((x.map c)ᵀ * K * y * I)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hGI, Matrix.one_mul]

theorem large_act (I g g' : Matrix (Fin n) (Fin n) R) (k : Matrix (Fin m) (Fin m) R) (h : g * I = I * (g'.map c)ᵀ)
    (x : Matrix (Fin m) (Fin n) R) :
    (I * ((k * x * g').map c)ᵀ)ᵀ = k.map c * (I * (x.map c)ᵀ)ᵀ * gᵀ := by
  have k' : g'.map c * Iᵀ = Iᵀ * gᵀ := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this.symm
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.mul_assoc]
  rw [k']

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev GG (S : HSp D) : Matrix (Fin S.rank) (Fin S.rank) (AE D) := S.gram.map (incA D)
abbrev GI (S : HSp D) : Matrix (Fin S.rank) (Fin S.rank) (AE D) := (S.gram⁻¹).map (incA D)

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, CMData.sig, inclR]; rfl

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun i j => S.herm.eq _ _

theorem GG_GI (S : HSp D) : GG S * GI S = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne S))]
  simp

theorem GI_GG (S : HSp D) : GI S * GG S = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne S))]
  simp

theorem GI_herm (S : HSp D) : ((GI S).map (cA D))ᵀ = GI S := by
  have h : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_herm]
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun h i) j))

theorem GG_herm (S : HSp D) : ((GG S).map (cA D))ᵀ = GG S := by
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun (gram_herm S) i) j))

theorem mt_mul_inv (S : HSp D) (g : GA D S) : Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem inv_GI (S : HSp D) (g : GA D S) :
    Formalism.L2.Theta.mt S g⁻¹ * GI S = GI S * ((Formalism.L2.Theta.mt S g).map (cA D))ᵀ :=
  inv_gen (cA D) (GG S) (GI S) _ _ (GI_GG S) (GG_GI S) (mt_mul_inv S g) (mt_rel S g)

theorem bridgeSmall : BridgeSmall D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · have : hHom S T (toTWsmall S T y) (toTWsmall S T x) = hO S T x y := by
      unfold hHom; rw [if_pos hr]
      exact small_gen (cA D) (GG S) (GI S) (GG T) (GI_GG S) (GI_herm S) x y
    unfold symplO sympl; rw [this]
  · unfold actHom; rw [if_pos hr]
    exact small_act (cA D) (GI S) _ _ _ (inv_GI S g) x

theorem trace_cA (a : AE D) :
    Algebra.trace (AF D.host.F) (AE D) (cA D a) = Algebra.trace (AF D.host.F) (AE D) a := by
  let f : AE D →ₐ[AF D.host.F] AE D := Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig
  have hf : ∀ a, f a = cA D a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [f, cA, sigR]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hff : f.comp f = AlgHom.id _ _ := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hf, hf, cA_cA]; rfl
  let g : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom f f hff hff
  rw [← hf]
  exact Algebra.trace_eq_of_algEquiv g a

theorem bridgeLarge (hxi : star D.host.xi0 = -D.host.xi0) : BridgeLarge D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · have : hHom T S (toTWlarge S T y) (toTWlarge S T x) = cA D (hO S T x y) := by
      unfold hHom; rw [if_pos hr.le]
      exact large_gen (cA D) cA_cA (GG S) (GI S) (GG T) (GG_GI S) (GI_herm S) (GG_herm T) x y
    unfold symplO sympl
    rw [this, ← trace_cA (incA D D.host.xi0 * hO S T x y), map_mul, cA_inc, hxi, map_neg, neg_mul, map_neg]
  · unfold actHom; rw [if_pos hr.le]
    have k := inv_GI S g⁻¹
    rw [inv_inv] at k
    exact large_act (cA D) (GI S) _ _ _ k x

theorem star_purely_imaginary_eq_neg : star D.host.xi0 = -D.host.xi0 := by
  have hs : ∀ x : D.host.E, D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) := fun x => by
    haveI := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  apply D.host.φ₀.injective
  rw [hs, map_neg]
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, hd]
  simp [div_neg]

theorem bridgeLarge' : BridgeLarge D := bridgeLarge star_purely_imaginary_eq_neg

end Formalism.IndefR.Datum.Brg

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.CxPass
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.IndefiniteEpsilonOperator
open Module NumberField

noncomputable section

namespace Formalism.IndefR.IndefiniteEpsilonOperator

structure Pair (G K : Type) [Group G] [Field K] where

  H : Subgroup G

  χ : H →* Kˣ

section Ops

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module K U]

def epOp [Finite G] (σ : Representation K G U) (P : Pair G K) : U →ₗ[K] U :=
  letI : Fintype P.H := Fintype.ofFinite P.H
  (Nat.card P.H : K)⁻¹ • ∑ h : P.H, ((P.χ h⁻¹ : Kˣ) : K) • σ (h : G)

def epSp [Finite G] (σ : Representation K G U) (P : Pair G K) : Submodule K U :=
  LinearMap.range (epOp σ P)

def nOf [Finite G] {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W)
    (P : Pair G K) : ℕ :=
  finrank K (epSp τ P)

end Ops

def la (G : Type) [Fintype G] : ℝ := Real.log (Fintype.card G)

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  [Fintype κ] [DecidableEq κ]

end Lat

def M1 {K : Type} [Field K] {G : Type} [Group G] [Finite G] {S : Type} {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] (τ : ∀ s, Representation K G (Ws s))
    (P0 : Pair G K) : Prop :=
  ∀ s, nOf (τ s) P0 = 1

end Formalism.IndefR.IndefiniteEpsilonOperator
end
end

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def prin {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) : CxData A := { X with nP := fun _ => 1 }

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

section Prims

variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

def GUnit (gE : Representation ℂ G X.EE) : Prop := ∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ

def GEquiv (gE : Representation ℂ G X.EE) : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), X.Θ t (X.jR t (A.fam.amb.opR t (Sum.inr g) x)) = gE g (X.Θ t (X.jR t x))

variable {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
    {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

def PrincipalInjectiveCommonRange : Prop :=
  Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0) ∧
    ∀ t, Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) ∧
      LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) =
        LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0)

end Prims

section Group

variable {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]

def CharsX (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K)) : Prop :=
  ∀ χ : G → K, χ ∈ Xc ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ

def NearConstantMultiplicities (τ : ∀ s, Representation K G (Ws s)) (P1 : Formalism.IndefR.IndefiniteEpsilonOperator.Pair G K) (nbar de : ℝ) : Prop :=
  ∀ s, (1 - de) * nbar ≤ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ∧ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ≤ (1 + de) * nbar

end Group

end Formalism.IndefR.CxPass
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartOfDefinite
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace CSDForm

variable (S : CSD K)

def csumForm : S.Forms →ₗ⋆[K] S.Forms →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun f g => S.csum (f : S.Cl → S.V) (g : S.Cl → S.V))
    (fun f f' g => by
      simp only [CSD.csum, Submodule.coe_add, Pi.add_apply, map_add (f := _), LinearMap.add_apply, mul_add,
        Finset.sum_add_distrib])
    (fun a f g => by
      simp only [CSD.csum, Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => by ring)
    (fun f g g' => by
      simp only [CSD.csum, Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib])
    (fun a f g => by
      simp only [CSD.csum, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      refine Finset.sum_congr rfl fun c _ => by ring)

theorem csumForm_apply (f g : S.Forms) : csumForm S f g = S.csum (f : S.Cl → S.V) (g : S.Cl → S.V) := rfl

end CSDForm

namespace BlockGood

variable {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0)

def goodR (ℓ : Lvl K G) : Submodule K B.S.Forms :=
  LinearMap.range ((B.S.basis.equivFun.symm : (Fin B.S.dim → K) →ₗ[K] B.S.Forms) ∘ₗ (B.vE ℓ).mulVecLin)

theorem toF_mem_goodR (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ goodR B ℓ := by
  unfold goodR
  exact LinearMap.mem_range.2 ⟨(B.zE ℓ Z).mulVecLin y, rfl⟩

theorem toF_mem (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z y ∈ Z := by
  have hs := (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  have hy : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
    rw [← hs]
    exact ⟨y, rfl⟩
  obtain ⟨f, hf, he⟩ := hy
  have : B.toF ℓ Z y = f := by
    have he' : B.S.basis.equivFun f = (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) := he
    change B.S.basis.equivFun.symm ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y)) = f
    rw [← he', LinearEquiv.symm_apply_apply]
  rw [this]
  exact hf

theorem csum_toF (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (x y : Fin (B.dZ ℓ Z) → K) :
    B.S.csum (B.toF ℓ Z x : B.S.Cl → B.S.V) (B.toF ℓ Z y : B.S.Cl → B.S.V) =
      (Nat.card ℓ.P : K) * (star x ⬝ᵥ (B.HZ ℓ Z).mulVec y) := by
  change B.S.csum (B.S.I ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec x))) (B.S.I ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y))) = _
  rw [B.S.csum_sum]
  have h1 : ∀ u w : Fin B.S.dim → K, (∑ i, ∑ j, star (u i) * B.S.H i j * w j) = star u ⬝ᵥ B.S.H.mulVec w := by
    intro u w
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hP : (Nat.card ℓ.P : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h2 : (B.vE ℓ * B.zE ℓ Z)ᴴ * (B.S.H * B.vE ℓ) * B.zE ℓ Z = (Nat.card ℓ.P : K) • B.HZ ℓ Z := by
    simp only [BlockDat.HZ, BlockDat.HV, BlockDat.vE, CSD.goodPartHermitianForm, CSD.cutH, CSD.V0E, Matrix.conjTranspose_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hP, one_smul, Matrix.mul_assoc]
  rw [h2]
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem csum_toF_at {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (ℓ : Lvl K G)
    (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (x y : Fin (B.dZ ℓ Z) → K) :
    v0.embedding (CSDForm.csumForm B.S (B.toF ℓ Z x) (B.toF ℓ Z y)) =
      ((Nat.card ℓ.P : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v0 x y := by
  rw [CSDForm.csumForm_apply, csum_toF, map_mul, map_natCast, Formalism.L2.DIV.majAt_eq]
  have hm : metOf (B.XQ ℓ Z v0) = (B.HZ ℓ Z).map v0.embedding := (BlockDat.XQ_herm hv0 h hX (Z := Z)).2
  rw [hm]
  push_cast
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv0]
  rfl

end BlockGood

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

theorem opC_adjoint (hK : X.KFormR) (cv : CrdV A) (hJ : X.JIsoR cv) (t : Bs.Tup) (i i' : A.OpR t)
    (h : ∀ f g, cv.hR t (A.opR t i f) g = cv.hR t f (A.opR t i' g)) :
    X.opC t i' = LinearMap.adjoint (X.opC t i) := by
  have h1 : X.opC t i = LinearMap.adjoint (X.opC t i') := by
    rw [LinearMap.eq_adjoint_iff_basis (Basis.mk (hK t).1 (hK t).2.ge) (Basis.mk (hK t).1 (hK t).2.ge)]
    intro k l
    simp only [Basis.mk_apply]
    rw [← jR_opR X hK, ← jR_opR X hK, hJ, hJ, h]
  rw [h1, LinearMap.adjoint_adjoint]

theorem opLC_adjoint (hK : X.KFormL) (cv : CrdV A) (hJ : X.JIsoL cv) (j : Bs.J) (t : Bs.Tup) (i i' : A.OpL j t)
    (h : ∀ f g, cv.hL j t (A.opL j t i f) g = cv.hL j t f (A.opL j t i' g)) :
    X.opLC j t i' = LinearMap.adjoint (X.opLC j t i) := by
  have h1 : X.opLC j t i = LinearMap.adjoint (X.opLC j t i') := by
    rw [LinearMap.eq_adjoint_iff_basis (Basis.mk (hK j t).1 (hK j t).2.ge) (Basis.mk (hK j t).1 (hK j t).2.ge)]
    intro k l
    simp only [Basis.mk_apply]
    rw [← jL_opL X hK, ← jL_opL X hK, hJ, hJ, h]
  rw [h1, LinearMap.adjoint_adjoint]

end CxData

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def cvOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) : CrdV A.fam.amb where
  v0R _ b t := match b with
    | false => BlockGood.goodR (A.fam.R t) (A.fam.lvl P0 ψ0)
    | true => BlockGood.goodR (A.fam.R t) (A.fam.lvl P1 ψ1)
  v0L _ b j t := match b with
    | false => BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P0 ψ0)
    | true => BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P1 ψ1)
  hR t := CSDForm.csumForm (A.fam.R t).S
  hL j t := CSDForm.csumForm (A.fam.L j t).S

variable {A : FamIn K G Pl0 T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
  {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

theorem csum_act_inv {B : BlockDat K G Pl0} (h : B.S.ActGood B.r) (g : G) (f f' : B.S.Forms) :
    B.S.csum (B.r g f : B.S.Cl → B.S.V) (f' : B.S.Cl → B.S.V) =
      B.S.csum (f : B.S.Cl → B.S.V) (B.r g⁻¹ f' : B.S.Cl → B.S.V) := by
  have h1 := h.unitary g f (B.r g⁻¹ f')
  have h2 : B.r g (B.r g⁻¹ f') = f' := by
    show (B.r g * B.r g⁻¹) f' = f'
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [h2] at h1
  exact h1

end Concrete

end Formalism.IndefR.Cx
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.DatumFock
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {m n : ℕ}

section Subst

def dExp (m : ℕ) (p : D.what₂.Tau → ℕ) (e : D.what₂.Tau → ℤ) (τ : D.what₂.Tau) : ℤ := (p τ : ℤ) - ((m + 1) / 2 : ℕ) - e τ

end Subst

section Equiv

end Equiv

end Formalism.IndefR.Datum

end
end
