module

public import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.SharpRestriction.SmoothDesignExistence.LinkGLOBALPk
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJClassFin
public import Formalism.LocalToGlobal.GlobalTheory.GL5.LocalEndomorphismContinuous
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountFib
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountIdx
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevD
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryClassMassHermitian

@[expose] public section

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountStab
section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.MassIntegralClass
noncomputable section

open NumberField

namespace Formalism.MainNotions.Gaps.MI

open Formalism.MainNotions.Inhab Formalism.BasicNotions Formalism.MainNotions.StandardLattice

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

variable (hc : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))





end Std

end Formalism.MainNotions.Gaps.MI
end
end

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Stab

open Formalism.UG Formalism.UG.CS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem exists_place_two : ∃ v : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hpZ : Prime ((2 : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨Q, hQ, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F)
    (Ideal.span {((2 : ℕ) : ℤ)})
  have hmem : ((2 : ℕ) : 𝓞 F) ∈ Q := by
    have : ((2 : ℕ) : ℤ) ∈ Q.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : ((2 : ℕ) : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

instance finiteAdeleRing_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨v, -⟩ := exists_place_two (F := F)
  exact (evalV F v).toRingHom.domain_nontrivial

section Herm

variable [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
  (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E)







section Mass

variable (hsymm : h.IsSymm) (hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
  (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
  (hIn : ∀ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ ∈ Formalism.HermitianLatticesTheory.genus h Λ)
  (hSurj : ∀ M ∈ Formalism.HermitianLatticesTheory.genus h Λ, ∃ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ = M)






end Mass

end Herm

section Std

open Formalism.MainNotions.StandardLattice

variable {k : ℕ} [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)


variable (hc : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))





end Std

end Formalism.MainNotions.Gaps.CC.Stab
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.SingleMemLam
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lam {k : ℕ} (L : Submodule (SS F E) (Fin k → AE F E)) : Submodule (𝓞 E) (Fin k → E) where
  carrier := {x | (fun i => inclE (F := F) (AF F) (x i)) ∈ L}
  add_mem' := by
    intro a b ha hb
    have h : (fun i => inclE (F := F) (AF F) ((a + b) i)) =
        (fun i => inclE (F := F) (AF F) (a i)) + (fun i => inclE (F := F) (AF F) (b i)) := by
      funext i; simp
    show (fun i => inclE (F := F) (AF F) ((a + b) i)) ∈ L
    rw [h]
    exact L.add_mem ha hb
  zero_mem' := by
    have h : (fun i => inclE (F := F) (AF F) ((0 : Fin k → E) i)) = 0 := by
      funext i; simp
    show (fun i => inclE (F := F) (AF F) ((0 : Fin k → E) i)) ∈ L
    rw [h]
    exact L.zero_mem
  smul_mem' := by
    intro r x hx
    have h : (fun i => inclE (F := F) (AF F) ((r • x) i)) =
        (⟨inclE (F := F) (AF F) (r : E), incl_mem_SS ⟨r, rfl⟩⟩ : SS F E) •
          (fun i => inclE (F := F) (AF F) (x i)) := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Algebra.smul_def, map_mul]
    show (fun i => inclE (F := F) (AF F) ((r • x) i)) ∈ L
    rw [h]
    exact L.smul_mem _ hx

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL5.PClassItems
section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL5.PClassSteps
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassMass Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

end Gen

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_sig_ne (D : D7) : ∃ θ : D.host.E, D.sp.cm.sig θ ≠ θ := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (NumberField.RingOfIntegers D.host.E)
  obtain ⟨θ, t, e, h⟩ := D.sp.cm.cmUnram.2.2 P hP
  refine ⟨algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ, fun h' => h ?_⟩
  have h'' : star (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ) =
      algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E θ := h'
  rw [h''] at e
  have : t = θ := NumberField.RingOfIntegers.coe_injective e
  rw [this, sub_self]
  exact P.zero_mem

theorem classFin_of_UJ (hF : PI.UJClassFin.UJClassFin) (D : D7) : ClassFin D := by
  intro W hW hsig
  exact hF D.host.F D.host.E D.sp.cm.sig W.rank W.gram (L0c D W) (fun _ => rfl)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1)
    (StabFin.crd_up (F := D.host.F) W) (StabFin.crd_low (F := D.host.F) W)

theorem class_number_finite (D : D7) : ClassFin D := classFin_of_UJ unitary_class_set_finite D

theorem class_number_finite_rank (D : D7) (n : ℕ) : ClassFinAt D n := classFinAt_of D (class_number_finite D) n

theorem class_mass_of_genus_classes (hM : PI.UJClassMass2.UJClassMass) (D : D7) : ClassMass D := by
  intro W hW hsig n g hcov hdisj
  classical
  have hL : Submodule.IsFullLattice D.host.E W.L0 := by
    refine { toIsLattice := W.standardTuple_isLattice, span_eq_top := ?_ }
    obtain ⟨c, hc, hlow⟩ := StabFin.crd_low (F := D.host.F) W
    let a : D.host.E := (c : D.host.F) • (1 : D.host.E)
    have ha : a ≠ 0 := by
      change (c : D.host.F) • (1 : D.host.E) ≠ 0
      rw [Algebra.smul_def, mul_one]
      exact (algebraMap D.host.F D.host.E).injective.ne (NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hc)
    rw [eq_top_iff, ← W.frame.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : a • W.frame i ∈ W.L0 := by
      have h := hlow i 1 isIntegral_one
      change ∑ j, (Pi.single i a : Fin W.rank → D.host.E) j • W.frame j ∈ W.L0 at h
      rwa [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same] at h
    have hframe : W.frame i = a⁻¹ • (a • W.frame i) := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hframe]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hi)
  exact hM D.host.F D.host.E D.sp.cm.sig W.V W.hT W.rank W.frame W.L0 (fun _ => rfl) (exists_sig_ne D)
    (fun τ => D.sp.cm.cmUnram.2.1 τ) W.herm W.nondeg hL
    (fun τ => by have h1 := hW τ; rw [hsig τ] at h1; exact h1) n g hcov hdisj



end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem genus_class_mass : PI.UJClassMass2.UJClassMass := _root_.unitary_class_mass_hermitian

theorem classMass_of_D7 (D : D7) : ClassMass D := class_mass_of_genus_classes genus_class_mass D

theorem volume_mass_of_genus_rank (D : D7) (n : ℕ) (hT : VolTie D) (hG : GenusMassAt D n) : volumeAtLevelZero D n :=
  volume_mass_of_class_data D n hT hG (class_number_finite_rank D n) (classMassAt_of D (classMass_of_D7 D) n)

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice



end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClosedKudlaFamilyStandardLattice

end
