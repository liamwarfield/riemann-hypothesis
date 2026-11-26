module

public import GroundTheory.AutomorphicForms.TraceNormComp
public import GroundTheory.AutomorphicForms.StableConjCyclic

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.TraceStrongLimit
namespace GroundTheory.Automorphic

open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section FinProj

variable {ι : Type*} [Fintype ι]

def finProj (u : ι → H) : H →L[ℂ] H := ∑ i, rankOne ℂ (u i) (u i)

variable {u : ι → H}

end FinProj

section Limits

variable [CompleteSpace H]

end Limits

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.HermitianWitt
noncomputable section

namespace GroundTheory.Automorphic

open Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]

theorem bijective_of_injective_sesq [FiniteDimensional E V]
    (B : V →ₛₗ[conjHom F E] V →ₗ[E] E) (hB : Function.Injective B) : Function.Bijective B := by
  set b := Module.finBasis E V
  set G := gram B b
  let sx : (Fin (finrank E V) → E) → V := fun c => b.equivFun.symm (fun i => conj F E (c i))
  have key : ∀ c j, B (sx c) (b j) = Matrix.vecMul c G j := by
    intro c j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [sx, Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ₂, conjHom_apply,
      conj_conj, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Matrix.vecMul,
      dotProduct, G, gram_apply]
  have hinj : Function.Injective (Matrix.vecMulLinear G) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : B (sx c) = 0 := b.ext fun j => by
      rw [key, LinearMap.zero_apply]
      exact congrFun hc j
    have h2 : sx c = 0 := hB (by rw [h1, map_zero])
    funext i
    have h3 := congrArg (fun v => b.equivFun v i) h2
    simp only [sx, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] at h3
    rw [← conj_conj (F := F) (c i), h3, map_zero, Pi.zero_apply]
  refine ⟨hB, fun f => ?_⟩
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.1 hinj (fun j => f (b j))
  refine ⟨sx c, b.ext fun j => ?_⟩
  rw [key]
  exact congrFun hc j

namespace HermitianForm

end HermitianForm

end GroundTheory.Automorphic

end
end

section -- merged from GroundTheory.AutomorphicForms.StableConjTorus
namespace GroundTheory.Automorphic

open Module

section CommuteField

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem commute_of_commute_of_separable_charpoly {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  classical
  set n := finrank E V
  let b : Basis (Fin n) E V := Module.finBasis E V
  let K := AlgebraicClosure E
  let φ : E →+* K := algebraMap E K
  let Φ : Module.End E V →+* Matrix (Fin n) (Fin n) K :=
    φ.mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom
  let Ψ : Matrix (Fin n) (Fin n) K →+* Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toRingEquiv.toRingHom
  have hsep : (Ψ (Φ f)).charpoly.Separable := by
    change (Matrix.toLin' ((LinearMap.toMatrix b b f).map φ)).charpoly.Separable
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    exact hf.map
  have hc := commute_of_commute_of_separable hsep ((hg.map Φ).map Ψ) ((hg'.map Φ).map Ψ)
  have hinj : Function.Injective (Ψ.comp Φ) := by
    intro x y hxy
    have h1 : Φ x = Φ y := (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective hxy
    have h2 : LinearMap.toMatrixAlgEquiv b x = LinearMap.toMatrixAlgEquiv b y := by
      ext i j
      exact φ.injective (congrFun (congrFun h1 i) j)
    exact (LinearMap.toMatrixAlgEquiv b).injective h2
  change g * g' = g' * g
  apply hinj
  rw [map_mul, map_mul]
  exact hc.eq

end CommuteField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]

namespace HermitianForm

variable (h : HermitianForm F E V)

noncomputable def adjoint (A : Module.End E V) : Module.End E V where
  toFun y := (Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)
  map_add' x y := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, map_add (f := _), LinearMap.add_comp]
  map_smul' c x := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, LinearMap.map_smulₛₗ, LinearMap.smul_comp,
      RingHom.id_apply]

theorem toSesq_adjoint_left (A : Module.End E V) (y x : V) :
    h.toSesq (h.adjoint A y) x = h.toSesq y (A x) := by
  change h.toSesq ((Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)) x = _
  rw [Equiv.ofBijective_apply_symm_apply (⇑h.toSesq) h.nonsingular]
  rfl

theorem eq_adjoint_iff (A B : Module.End E V) :
    B = h.adjoint A ↔ ∀ y x, h.toSesq (B y) x = h.toSesq y (A x) := by
  refine ⟨fun hB y x => hB ▸ h.toSesq_adjoint_left A y x, fun hB => LinearMap.ext fun y => ?_⟩
  apply h.nonsingular.1
  ext x
  rw [hB, toSesq_adjoint_left]

theorem adjoint_mul (A B : Module.End E V) : h.adjoint (A * B) = h.adjoint B * h.adjoint A := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rw [Module.End.mul_apply, toSesq_adjoint_left, toSesq_adjoint_left, Module.End.mul_apply]

theorem adjoint_one : h.adjoint 1 = 1 := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rfl

noncomputable def adjointEquiv (g : V ≃ₗ[E] V) : V ≃ₗ[E] V where
  toLinearMap := h.adjoint g.toLinearMap
  invFun := h.adjoint g.symm.toLinearMap
  left_inv x := by
    change (h.adjoint g.symm.toLinearMap * h.adjoint g.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.toLinearMap * g.symm.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl
  right_inv x := by
    change (h.adjoint g.toLinearMap * h.adjoint g.symm.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.symm.toLinearMap * g.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl

end HermitianForm

section Stable

variable [FiniteDimensional E V]

def IsRegularSemisimple (γ : V ≃ₗ[E] V) : Prop :=
  (γ.toLinearMap).charpoly.Separable

def torusE (γ : V ≃ₗ[E] V) : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.centralizer {γ}



def TorusE (γ : V ≃ₗ[E] V) : Type _ := torusE γ

namespace TorusE

variable {γ : V ≃ₗ[E] V}




variable [Fact (IsRegularSemisimple γ)]

end TorusE

end Stable

end GroundTheory.Automorphic
end
