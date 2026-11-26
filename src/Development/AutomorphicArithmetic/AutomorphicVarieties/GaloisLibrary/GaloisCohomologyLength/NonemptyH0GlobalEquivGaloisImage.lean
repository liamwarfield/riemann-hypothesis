module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.RestrictScalarsTwistInvOver

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Ranges
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem cyclotomicCharacter_conj_ringEquiv {L M : Type} [Field L] [Field M] (p : ℕ) [Fact p.Prime]
    (φ : L ≃+* M) (g : L ≃+* L) :
    cyclotomicCharacter L p g = cyclotomicCharacter M p (φ.symm.trans (g.trans φ)) := by
  by_cases H : ∀ i : ℕ, ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
  · have hL (i : ℕ) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
    have hM (i : ℕ) : HasEnoughRootsOfUnity M (p ^ i) := by
      obtain ⟨ζ, hζ⟩ := H i
      exact ⟨⟨φ ζ, hζ.map_of_injective φ.injective⟩, rootsOfUnity.isCyclic _ _⟩
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
    rw [cyclotomicCharacter.toZModPow, cyclotomicCharacter.toZModPow]
    refine modularCyclotomicCharacter.unique M
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity M (p ^ n)) _ fun t ht ↦ ?_
    have hs : Units.map φ.symm.toMonoidHom t ∈ rootsOfUnity (p ^ n) L := by
      rw [mem_rootsOfUnity] at ht ⊢
      rw [← map_pow, ht, map_one]
    have key := modularCyclotomicCharacter.spec L
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)) g hs
    simp only [Units.coe_map, Units.val_pow_eq_pow_val] at key
    change g (φ.symm (t : M)) = (φ.symm (t : M)) ^ _ at key
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, key, map_pow, RingEquiv.apply_symm_apply]
  · have H' : ¬ ∀ i : ℕ, ∃ ζ : M, IsPrimitiveRoot ζ (p ^ i) := by
      intro hM
      apply H
      intro i
      obtain ⟨ζ, hζ⟩ := hM i
      exact ⟨φ.symm ζ, hζ.map_of_injective φ.symm.injective⟩
    ext1
    simp [cyclotomicCharacter, cyclotomicCharacter.toFun, H, H']

theorem UpperTheory.V.LDataCardLeFinrank.ranges :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l), (cycZ F Ω l).range = KStar.TotallyRealRoots.galImage l F ∧ D.chi.range = KStar.TotallyRealRoots.galImage l F ∧ ∀ v : D.S, (D.chi.comp (locFam D.S D.A v)).range = decImage F l (D.A v) := by
  intro F Ω _ _ _ _ _ l _ D
  have hcyc : (cycZ F Ω l).range = KStar.TotallyRealRoots.galImage l F := by
    let e : Ω ≃ₐ[F] AlgebraicClosure F := IsAlgClosure.equiv F Ω (AlgebraicClosure F)
    have hpt : ∀ σ : Gal(Ω/F), cycZ F Ω l σ = KStar.TotallyRealRoots.eps l F (AlgEquiv.autCongr e σ) := by
      intro σ
      simp only [cycZ, KStar.TotallyRealRoots.eps, MonoidHom.comp_apply]
      exact cyclotomicCharacter_conj_ringEquiv l e.toRingEquiv _
    ext x
    simp only [MonoidHom.mem_range, KStar.TotallyRealRoots.galImage]
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨_, (hpt σ).symm⟩
    · rintro ⟨τ, rfl⟩
      exact ⟨(AlgEquiv.autCongr e).symm τ, by rw [hpt, MulEquiv.apply_symm_apply]⟩
  have hchi : D.chi.range = (cycZ F Ω l).range := by
    have htop : (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    rw [← D.hchi, MonoidHom.range_comp, htop, ← MonoidHom.range_eq_map]
  refine ⟨hcyc, hchi.trans hcyc, fun v ↦ ?_⟩
  have hcomp : D.chi.comp (locFam D.S D.A v) = (cycZ F Ω l).comp (Dec (D.A v)).subtype := by
    rw [← D.hchi]
    rfl
  rw [hcomp, MonoidHom.range_comp, Subgroup.range_subtype]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LenTwist
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.lenTwist :
    ∀ (l : ℕ) [Fact l.Prime] (U : Subgroup ℤ_[l]ˣ) (tr : ℕ), Module.length ℤ_[l] (KStar.TotallyRealRoots.twistInv l (QZ l) U tr) = KStar.TotallyRealRoots.nu l U tr ∧ Nonempty (KStar.TotallyRealRoots.twistInv l (QZ l) U tr ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.H0 l U tr) := by
  intro l _ U tr
  have e : ZlSub l = (1 : Submodule ℤ_[l] ℚ_[l]) := Submodule.one_eq_range.symm
  let f : QZ l ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.QmodZ l := Submodule.quotEquivOfEq _ _ e
  have hmap : (KStar.TotallyRealRoots.twistInv l (QZ l) U tr).map (f : QZ l →ₗ[ℤ_[l]] KStar.TotallyRealRoots.QmodZ l) =
      KStar.TotallyRealRoots.twistInv l (KStar.TotallyRealRoots.QmodZ l) U tr := by
    ext y
    simp only [Submodule.mem_map, KStar.TotallyRealRoots.mem_twistInv]
    constructor
    · rintro ⟨x, hx, rfl⟩ u hu
      rw [LinearEquiv.coe_coe, ← f.map_smul, hx u hu]
    · intro hy
      refine ⟨f.symm y, fun u hu => ?_, by simp⟩
      rw [← f.symm.map_smul, hy u hu]
  let g : KStar.TotallyRealRoots.twistInv l (QZ l) U tr ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.H0 l U tr :=
    (f.submoduleMap _).trans (LinearEquiv.ofEq _ _ hmap)
  have hnu : ¬IsUnit ((l : ℕ) : ℤ_[l]) := PadicInt.irreducible_p.not_isUnit
  have h := KStar.TotallyRealRoots.length_twistInvOver (O := ℤ_[l]) ℚ_[l] hnu U tr
  have hv : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p
  rw [hv, mul_one] at h
  have hsame : KStar.TotallyRealRoots.twistInvOver l ℤ_[l] (KStar.Selmer.FracMod ℤ_[l] ℚ_[l]) U tr =
      KStar.TotallyRealRoots.twistInv l (KStar.TotallyRealRoots.QmodZ l) U tr := by
    ext x
    rw [KStar.TotallyRealRoots.mem_twistInv]
    rfl
  rw [hsame] at h
  refine ⟨?_, ⟨g⟩⟩
  rw [g.length_eq]
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.H0ScalRepInvPowEqTwistInv
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem units_zpow_neg_smul_eq_self_iff (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Module ℤ_[l] A]
    (v : ℤ_[l]ˣ) (e : ℤ) (x : A) :
    ((v ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔ ((v : ℤ_[l]) ^ e.natAbs) • x = x := by
  have key : ∀ n : ℕ, ((v ^ (-(n:ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔ ((v : ℤ_[l]) ^ n) • x = x := by
    intro n
    rw [← Units.val_pow_eq_pow_val, ← Units.smul_def, ← Units.smul_def, zpow_neg, zpow_natCast]
    constructor
    · intro h
      conv_lhs => rw [← h]
      simp
    · intro h
      conv_lhs => rw [← h]
      simp
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · simpa using key n
  · simp [← Units.val_pow_eq_pow_val]

theorem UpperTheory.V.LDataCardLeFinrank.H0_scalRep_inv_pow_eq_twistInv :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (ψ : Γ →* ℤ_[l]ˣ) (e : ℤ), H0 (scalRep (QZ l) (ψ ^ (-e))) = KStar.TotallyRealRoots.twistInv l (QZ l) ψ.range e.natAbs := by
  intro l _ Γ _ ψ e
  ext x
  rw [KStar.TotallyRealRoots.mem_twistInv]
  change (∀ g : Γ, (scalRep (QZ l) (ψ ^ (-e))) g x = x) ↔ _
  simp only [scalRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply,
    MonoidHom.zpow_apply]
  constructor
  · rintro h u ⟨g, rfl⟩
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mp (h g)
  · intro h g
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mpr (h _ ⟨g, rfl⟩)
end

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

theorem contTw : ContTw := fun _ _ _ _ _ _ _ l _ D e =>
  ⟨contScal l _ _ (GlobalTheory.TateLimit.continuous_chi D (-e)), GlobalTheory.TateLimit.contAction_zlTw D e⟩

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem contAction_qzG (e : ℤ) : ContAction (qzG F Ω l e) :=
  contScal l _ _ (Units.continuous_val.comp ((continuous_cycZ F Ω l).zpow (-e)))

omit [IsAlgClosure F Ω] in
theorem above_of_mem (D : LData F Ω l) (v : D.S) : v.1 ∈ Above F l := by
  rw [← D.hS]
  exact Finset.mem_coe.2 v.2

theorem global_fixed_points_eq_twist_fixed_points (D : LData F Ω l) (e : ℤ) :
    H0 (qzTw D e) = KStar.TotallyRealRoots.twistInv l (QZ l) (KStar.TotallyRealRoots.galImage l F) e.natAbs := by
  rw [← (ranges F Ω l D).2.1]
  exact H0_scalRep_inv_pow_eq_twistInv l _ D.chi e

theorem local_fixed_points_eq_twist_fixed_points (D : LData F Ω l) (e : ℤ) (v : D.S) :
    H0 ((qzTw D e).comp (locFam D.S D.A v)) = KStar.TotallyRealRoots.twistInv l (QZ l) (decImage F l (D.A v)) e.natAbs := by
  show H0 (scalRep (QZ l) ((D.chi.comp (locFam D.S D.A v)) ^ (-e))) = _
  rw [H0_scalRep_inv_pow_eq_twistInv, (ranges F Ω l D).2.2 v]

theorem length_H0_global_eq_nu (D : LData F Ω l) (e : ℤ) :
    Module.length ℤ_[l] (H0 (qzTw D e)) = KStar.TotallyRealRoots.nuGal l F e.natAbs := by
  rw [global_fixed_points_eq_twist_fixed_points, KStar.TotallyRealRoots.nuGal_eq_nu]
  exact (lenTwist l _ _).1

theorem length_H0_local_eq_nu (D : LData F Ω l) (e : ℤ) (v : D.S) :
    Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v))) =
      KStar.TotallyRealRoots.nu l (decImage F l (D.A v)) e.natAbs := by
  rw [local_fixed_points_eq_twist_fixed_points]
  exact (lenTwist l _ _).1

theorem local_H0_length_eq_sum (D : LData F Ω l) (e : ℤ) :
    sumLocalH0TwistLength D e = ∑ v : D.S, KStar.TotallyRealRoots.nu l (decImage F l (D.A v)) e.natAbs :=
  Finset.sum_congr rfl fun v _ => length_H0_local_eq_nu D e v

theorem isOpen_decImage {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hv : v ∈ Above F l)
    (hA : IsPlaceOver A v) : IsOpen (decImage F l A : Set ℤ_[l]ˣ) :=
  Subgroup.isOpen_mono (ineImage_le_decImage F l A) (ineOpen F Ω l v A hv hA).1

end

end UpperTheory.V.LDataCardLeFinrank

end
