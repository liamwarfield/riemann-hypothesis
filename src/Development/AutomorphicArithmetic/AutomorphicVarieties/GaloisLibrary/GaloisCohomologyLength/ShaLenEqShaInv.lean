module

public import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaInfl

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaAbsRes
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.shaAbsRes :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 F'))) (φ : G F' Ω' →* G F Ω) (hφ : Continuous φ),
      (∀ (v' : HeightOneSpectrum (𝓞 F')) (A' : ValuationSubring Ω'), IsPlaceOver A' v' → ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v ∧ (v ∈ S ↔ v' ∈ S') ∧
        (∀ g ∈ Dec (F := F') A', φ g ∈ Dec (F := F) A) ∧ ∀ g ∈ Ine (F := F') A', φ g ∈ Ine (F := F) A) →
      ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R (G F Ω) M), (∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S') ∧
        (Function.Surjective φ → Module.length R (ShaAbs ρ S) ≤ Module.length R (ShaAbs (ρ.comp φ) S')) := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ S S' φ hφ h R _ M _ _ _ _ _ ρ
  have h1 : ∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S' := by
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨ha, hb⟩ := (mk_mem_ShaAbs ρ S z).1 hx
    refine (mk_mem_ShaAbs (ρ.comp φ) S' (restrictCocycles1 ρ φ hφ z)).2 ⟨?_, ?_⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, hD, -⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := ha v (hS.2 hv') A hA
      exact ⟨m, fun g hg => hm (φ g) (hD g hg)⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, -, hI⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := hb v (fun hv => hv' (hS.1 hv)) A hA
      exact ⟨m, fun g hg => hm (φ g) (hI g hg)⟩
  refine ⟨h1, fun hs => ?_⟩
  have hinj : Function.Injective (resH1 ρ φ hφ) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : (Submodule.Quotient.mk (restrictCocycles1 ρ φ hφ z) : H1 (ρ.comp φ)) = 0 := hx
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx')
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩)
    obtain ⟨g', rfl⟩ := hs g
    exact hm g'
  refine Module.length_le_of_injective ((resH1 ρ φ hφ).restrict h1) ?_
  intro x y hxy
  exact Subtype.ext (hinj (congrArg Subtype.val hxy))
end

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem map_Sha (D : LData F Ω l) (e : ℤ) :
    (Sha D e).map (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) =
      ShaAbs ((qzTw D e).comp (toGS Ω _)) (Above F l) := by
  rw [← D.hS]
  exact shaInfl F Ω D.S D.A D.hA _ _ _ (contTw F Ω l D e).1

theorem injective_infl (D : LData F Ω l) (e : ℤ) :
    Function.Injective (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) :=
  (infUnram F Ω _ _ _ _ (contTw F Ω l D e).1).1

theorem shaLen_eq_abs (D : LData F Ω l) (e : ℤ) :
    shaLen D e = Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) := by
  rw [← qzTw_comp_toGS D e, ← map_Sha]
  exact (Submodule.equivMapOfInjective _ (injective_infl D e) _).length_eq

variable {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω']

theorem length_ShaAbs_le (f : F ≃+* F') (e : ℤ) :
    Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) ≤
      Module.length ℤ_[l] (ShaAbs (qzG F' Ω' l e) (Above F' l)) := by
  let σ : Ω ≃+* Ω' := IsAlgClosure.equivOfEquiv Ω Ω' f
  have hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f.toRingHom x) :=
    fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω' f x
  obtain ⟨φ, h1, h2, h3, -, h5⟩ := galTransport F Ω F' Ω' f.toRingHom σ hσ
  have e1 : (qzG F Ω l e).comp φ = qzG F' Ω' l e := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [MonoidHom.comp_apply, qzG_apply, qzG_apply, h3]
  rw [← e1]
  refine (shaAbsRes F Ω F' Ω' _ _ φ h1 (fun v' A' hA' => ?_) _ _ _).2 (h5 f.surjective)
  obtain ⟨v, A, a, b, -, c, d⟩ := placeTransport F Ω F' Ω' f.toRingHom σ hσ φ h2 v' A' hA'
  exact ⟨v, A, a, b l, fun g hg => (c g).2 hg, fun g hg => (d g).2 hg⟩

theorem shaLen_eq_shaInv (D : LData F Ω l) (e : ℤ) : shaLen D e = shaInv F l e := by
  rw [shaLen_eq_abs]
  exact le_antisymm (length_ShaAbs_le (RingEquiv.refl F) e) (length_ShaAbs_le (RingEquiv.refl F) e)

theorem shaInv_congr (f : F ≃+* F') (e : ℤ) : shaInv F l e = shaInv F' l e :=
  le_antisymm (length_ShaAbs_le f e) (length_ShaAbs_le f.symm e)

end

end UpperTheory.V.LDataCardLeFinrank

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Formula
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.VFormula
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem length_add_coker {R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) :
    Module.length R X + Module.length R (Y ⧸ LinearMap.range f) =
      Module.length R (LinearMap.ker f) + Module.length R Y := by
  have hX := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hY := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [hX, hY, (f.quotKerEquivRange).length_eq, add_assoc]

theorem UpperTheory.V.LDataCardLeFinrank.vFormula :
    Formalism.GaloisCohomology.VFormula := by
  intro F Ω _ _ _ _ _ l _ D e hcase hcoker hsha hloc
  have hker : LinearMap.ker (localH2 D e) = Sha2Zl D e := by
    unfold localH2
    rw [LinearMap.ker_pi]
    rfl
  have key := length_add_coker (localH2 D e)
  rw [hcoker hcase, hker, hsha hcase, Module.length_pi_of_fintype] at key
  unfold VLen sumLocalH0TwistLength
  rw [key]
  congr 1
  exact Finset.sum_congr rfl (fun v _ => hloc v)
end

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem vFormula_of_classicalTheorems (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) :
    VLen D e + KStar.TotallyRealRoots.nuGal l F e.natAbs = shaLen D e + sumLocalH0TwistLength D e := by
  have hfl := fun r (hr : 0 < r) => GlobalTheory.TateLimit.finite_level D e hP hc r hr
  have hcok := GlobalTheory.TateLimit.ptCokerAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have hsha := GlobalTheory.TateLimit.ptShaAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have length_add_coker {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X]
      [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) :
      Module.length R X + Module.length R (Y ⧸ LinearMap.range f) =
        Module.length R (LinearMap.ker f) + Module.length R Y := by
    have hX := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    have hY := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
    rw [hX, hY, (f.quotKerEquivRange).length_eq, add_assoc]
  have h : Formalism.GaloisCohomology.VFormula := by
    exact _root_.UpperTheory.V.LDataCardLeFinrank.vFormula
  have h := h F Ω l D e hc hcok hsha (GlobalTheory.TateLimit.local_tate_duality_h2_limit hF hT D e)
  rwa [length_H0_global_eq_nu] at h

theorem ptCase_of_isTotallyComplex (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] (l : ℕ) : PTCase F l :=
  Or.inr (NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance)

theorem VLen_le_shaLen_add (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) : VLen D e ≤ shaLen D e + sumLocalH0TwistLength D e := by
  rw [← vFormula_of_classicalTheorems hP hF hT hc]
  exact le_self_add

end

end UpperTheory.V.LDataCardLeFinrank

end
end
