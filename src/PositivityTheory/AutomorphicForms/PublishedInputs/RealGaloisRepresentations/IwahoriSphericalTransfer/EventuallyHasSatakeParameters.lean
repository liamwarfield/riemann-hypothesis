module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InfiniteQuadraticFieldsSplitInertia

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EventuallyHasSatakeParameters
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsBis
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.SatAeProof

theorem main : AdmissibleReal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat v B := by
  intro hA F _ _ _ a π
  have : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  have hsm : GlobalTheory.PRep.IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff
  exact sat_ae_of_smooth GlobalTheory.RealGal.SatLocProof.main π.finPart hsm fun w =>
    let ⟨⟨σ, hσ⟩, hiso⟩ := GlobalTheory.RealGal.locCompR_of_admissibleReal hA F a π w
    ⟨σ, hiso σ hσ⟩

end GlobalTheory.RealGal.SatAeProof
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_has_satake_parameters : AdmissibleReal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, π.HasSat v B := by
  first | exact @GlobalTheory.RealGal.SatAeProof.main | exact GlobalTheory.RealGal.SatAeProof.main | (intros; apply GlobalTheory.RealGal.SatAeProof.main <;> assumption)
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.MemRangeResIff
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.GaloisRepTowerRestriction
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_rep_tower_restriction : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower F K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)), AttRes π ι K r → AttRes π ι M (r.comp (res K Ω M)) := by
  first | exact @GlobalTheory.AttResTower.attRes_comp_res | exact GlobalTheory.AttResTower.attRes_comp_res | (intros; apply GlobalTheory.AttResTower.attRes_comp_res <;> assumption)
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGalCompat

theorem mem_range_res_iff {K M Ω : Type} [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] (x : G K Ω) :
    x ∈ (res K Ω M).range ↔ ∀ m : M, x (algebraMap M Ω m) = algebraMap M Ω m := by
  constructor
  · rintro ⟨y, rfl⟩ m
    exact y.commutes m
  · intro h
    refine ⟨{ x.toRingEquiv with commutes' := fun m => h m }, ?_⟩
    ext z
    rfl

theorem range_res_normal {F K M Ω : Type} [Field F] [Field K] [Field M] [Field Ω] [Algebra F K] [Algebra F M]
    [Algebra F Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower F K Ω] [IsScalarTower F M Ω]
    [IsScalarTower K M Ω] [Normal F M] : (res K Ω M).range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_range_res_iff] at hn ⊢
  intro m
  obtain ⟨m', hm'⟩ : ∃ m' : M, algebraMap M Ω m' = g⁻¹ (algebraMap M Ω m) :=
    ⟨((AlgEquiv.restrictScalars F (g⁻¹ : G K Ω)).toAlgHom).restrictNormal M m,
      AlgHom.restrictNormal_commutes _ _ _⟩
  show g (n (g⁻¹ (algebraMap M Ω m))) = algebraMap M Ω m
  rw [← hm', hn m', hm', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

end GlobalTheory.RealGalCompat

open GlobalTheory.RealGalCompat in
theorem GlobalTheory.RealGalCompat.trace_eq : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Q Q' : QCM F Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)) (r' : G ↥Q'.K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι ↥Q.K r → AttRes π ι ↥Q'.K r' → ∀ (s : G ↥Q.K Ω) (s' : G ↥Q'.K Ω), res F Ω ↥Q.K s = res F Ω ↥Q'.K s' → ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r' s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  intro F Ω _ _ _ _ _ _ Q Q' l _ ι a π r r' hr hr' hs hs' ha ha' s s' hss
  let M : IntermediateField F Ω := Q.K ⊔ Q'.K
  haveI : FiniteDimensional F Q.K := Module.finite_of_finrank_pos (by rw [Q.two]; norm_num)
  haveI : FiniteDimensional F Q'.K := Module.finite_of_finrank_pos (by rw [Q'.two]; norm_num)
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : Module.IsTorsionFree M Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed F,
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := F) _⟩
  haveI : Algebra.IsQuadraticExtension F Q.K := { finrank_eq_two' := Q.two }
  haveI : Algebra.IsQuadraticExtension F Q'.K := { finrank_eq_two' := Q'.two }
  haveI : Normal F M := IntermediateField.normal_sup F Ω Q.K Q'.K
  letI : Algebra Q.K M := (IntermediateField.inclusion (le_sup_left : Q.K ≤ M)).toRingHom.toAlgebra
  letI : Algebra Q'.K M := (IntermediateField.inclusion (le_sup_right : Q'.K ≤ M)).toRingHom.toAlgebra
  haveI : IsScalarTower F Q.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower F Q'.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower Q.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower Q'.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl

  have hA := GlobalTheory.T.galois_rep_tower_restriction F Ω Q.K M l ι a π r ha
  have hA' := GlobalTheory.T.galois_rep_tower_restriction F Ω Q'.K M l ι a π r' ha'
  have hS := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r (res Q.K Ω M) (range_res_normal (F := F)) hs
  have hS' := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r' (res Q'.K Ω M) (range_res_normal (F := F)) hs'
  have hC := hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q.K M Ω)
  have hC' := hr'.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q'.K M Ω)
  obtain ⟨g, hg⟩ := GlobalTheory.T.attached_galois_rep_unique F Ω M l ι a π _ _ hC hC' hS hS' hA hA'

  set σ : G F Ω := res F Ω Q.K s with hσ
  have hfix : σ ∈ M.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact s.commutes x
    · rw [hss]; exact s'.commutes x
  let t : G M Ω := IntermediateField.fixingSubgroupEquiv M ⟨σ, hfix⟩
  have ht : res Q.K Ω M t = s := by ext z; rfl
  have ht' : res Q'.K Ω M t = s' := by
    ext z
    exact congrArg (fun u : G F Ω => u z) hss
  have e := hg t
  simp only [MonoidHom.comp_apply, ht, ht'] at e
  rw [e, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RestrictGaloisConjugate
section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AttachedRepConjugateInvariant
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GaloisLiftFixedPoints

open scoped Pointwise

section

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem exists_of_fixed (y : Ω) (hy : ∀ s : Formalism.ConjugateSelfDual.G K Ω, s y = y) : ∃ x : K, algebraMap K Ω x = y :=
  IntermediateField.mem_bot.1 ((InfiniteGalois.mem_bot_iff_fixed y).2 hy)

end

section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

noncomputable def liftEquiv (φ : Ω ≃+* Ω) (h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ (algebraMap K Ω x))
    (h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ.symm (algebraMap K Ω x)) : K ≃+* K where
  toFun x := (h1 x).choose
  invFun x := (h2 x).choose
  left_inv x := (algebraMap K Ω).injective (by
    rw [(h2 _).choose_spec, (h1 x).choose_spec, φ.symm_apply_apply])
  right_inv x := (algebraMap K Ω).injective (by
    rw [(h1 _).choose_spec, (h2 x).choose_spec, φ.apply_symm_apply])
  map_mul' x y := (algebraMap K Ω).injective (by
    rw [(h1 _).choose_spec, map_mul, map_mul, map_mul, (h1 x).choose_spec, (h1 y).choose_spec])
  map_add' x y := (algebraMap K Ω).injective (by
    rw [(h1 _).choose_spec, map_add (f := _), map_add (f := _), map_add (f := _), (h1 x).choose_spec, (h1 y).choose_spec])

theorem liftEquiv_spec (φ : Ω ≃+* Ω) (h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ (algebraMap K Ω x))
    (h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = φ.symm (algebraMap K Ω x)) (x : K) :
    algebraMap K Ω (liftEquiv φ h1 h2 x) = φ (algebraMap K Ω x) :=
  (h1 x).choose_spec

end

end GlobalTheory.GaloisLiftFixedPoints

open scoped Pointwise
open GlobalTheory.GaloisLiftFixedPoints in
theorem _root_.GlobalTheory.T.attached_rep_conjugate_invariant : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)) (g : G F Ω) (c : G K Ω →* G K Ω), (∀ s, res F Ω K (c s) = g * res F Ω K s * g⁻¹) → Function.Surjective c → AttRes π ι K r → AttRes π ι K (r.comp c) := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ l _ ι a π r g c hc hsurj hr
  have ginv : ∀ z : Ω, g⁻¹ (g z) = z := fun z => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have gg : ∀ z : Ω, g (g⁻¹ z) = z := fun z => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hcx : ∀ (s : G K Ω) (x : Ω), c s x = g (s (g⁻¹ x)) := fun s x => by
    have := congrArg (fun φ : G F Ω => φ x) (hc s)
    exact this
  set σ' : Ω ≃+* Ω := (g⁻¹ : G F Ω).toRingEquiv with hσ'
  have hsymm : ∀ z : Ω, σ'.symm z = g z := fun z => by
    rw [RingEquiv.symm_apply_eq]
    exact (ginv z).symm
  have h1 : ∀ x : K, ∃ y : K, algebraMap K Ω y = σ' (algebraMap K Ω x) := fun x => by
    refine exists_of_fixed _ fun s => ?_
    have e := hcx s (algebraMap K Ω x)
    rw [AlgEquiv.commutes] at e
    show s (g⁻¹ (algebraMap K Ω x)) = g⁻¹ (algebraMap K Ω x)
    have e2 := congrArg (fun z => g⁻¹ z) e
    simp only [ginv] at e2
    exact e2.symm
  have h2 : ∀ x : K, ∃ y : K, algebraMap K Ω y = σ'.symm (algebraMap K Ω x) := fun x => by
    rw [hsymm]
    refine exists_of_fixed _ fun s => ?_
    obtain ⟨t, rfl⟩ := hsurj s
    rw [hcx, ginv, AlgEquiv.commutes]
  set τ : K ≃+* K := liftEquiv σ' h1 h2 with hτ
  have hL : IsLift τ σ' := fun x => (liftEquiv_spec σ' h1 h2 x).symm
  have hτF : ∀ y : F, τ (algebraMap F K y) = algebraMap F K y := fun y => (algebraMap K Ω).injective (by
    rw [← hL, ← IsScalarTower.algebraMap_apply]
    exact AlgEquiv.commutes _ _)
  have hconj : ∀ s : G K Ω, c s = conjGal hL s := fun s => AlgEquiv.ext fun x => by
    rw [UpperTheory.V.conjGal_apply, hsymm, hcx]
    rfl
  have hσA : ∀ A : ValuationSubring Ω, ∀ x, σ' x ∈ A ↔ x ∈ g • A := fun A x => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    rfl
  have hfrob : ∀ (A : ValuationSubring Ω) (q : ℕ) (s : G K Ω), IsFrob A q s → IsFrob (g • A) q (c s) :=
    fun A q s hs => by
      rw [hconj]
      refine ⟨conjGal_mem_Dec hL (hσA A) hs.1, fun x hx => ?_⟩
      rw [← val_lt_one (hσA A), map_sub, map_pow, apply_conjGal]
      exact hs.2 _ ((A.valuation_le_one_iff _).2 ((hσA A x).2 (((g • A).valuation_le_one_iff _).1 hx)))
  have hine : ∀ (A : ValuationSubring Ω) (s : G K Ω), s ∈ Ine (F := K) A → c s ∈ Ine (F := K) (g • A) :=
    fun A s hs => by
      rw [hconj]
      exact conjGal_mem_Ine hL (hσA A) hs
  set e : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv τ with he
  have hunder : ∀ w : HeightOneSpectrum (𝓞 K), (preplace τ w).under (𝓞 F) = w.under (𝓞 F) := fun w => by
    apply HeightOneSpectrum.ext
    ext x
    have hx : e (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 K) x := RingOfIntegers.ext (hτF (x : F))
    show algebraMap (𝓞 F) (𝓞 K) x ∈ (preplace τ w).asIdeal ↔ algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal
    rw [mem_preplace, ← he, hx]
  have hnorm : ∀ w : HeightOneSpectrum (𝓞 K), normV (preplace τ w) = normV w := fun w => by
    show Nat.card (𝓞 K ⧸ (w.asIdeal.comap (e : 𝓞 K →+* 𝓞 K))) = Nat.card (𝓞 K ⧸ w.asIdeal)
    exact Nat.card_congr (Ideal.quotientEquiv _ _ e
      (Ideal.map_comap_of_surjective (e : 𝓞 K →+* 𝓞 K) e.surjective _).symm).toEquiv
  have hinj : Function.Injective (preplace τ) := fun u v huv =>
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ)).symm.injective huv
  unfold AttRes at hr ⊢
  filter_upwards [hinj.tendsto_cofinite.eventually hr] with w hw f hf
  have hf' : normV (preplace τ w) = normV ((preplace τ w).under (𝓞 F)) ^ f := by
    rw [hnorm, hunder]
    exact hf
  obtain ⟨B, hB, hE⟩ := hw f hf'
  rw [hunder] at hB hE
  refine ⟨B, hB, fun A hA => ?_⟩
  obtain ⟨k1, k2⟩ := hE (g • A) (isPlaceOver_preplace hL (hσA A) hA)
  refine ⟨fun s hs => k1 _ (hine A s hs), fun s hs => ?_⟩
  have := k2 (c s) (by rw [hnorm]; exact hfrob A _ s hs)
  rw [MonoidHom.comp_apply, map_inv]
  exact this
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealGal.TrInv

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra F K] [Algebra K Ω]
  [IsScalarTower F K Ω] [Normal F K]

def galoisConjugate (g : G F Ω) (t : G K Ω) : G K Ω :=
  AlgEquiv.ofRingEquiv (f := ((g * res F Ω K t * g⁻¹ : G F Ω) : Ω ≃+* Ω)) (fun x => by
    obtain ⟨y, hy⟩ : ∃ y : K, (g⁻¹ : G F Ω) (algebraMap K Ω x) = algebraMap K Ω y :=
      ⟨(g⁻¹ : G F Ω).restrictNormal K x, (AlgEquiv.restrictNormal_commutes _ K x).symm⟩
    change g ((res F Ω K t) ((g⁻¹ : G F Ω) (algebraMap K Ω x))) = algebraMap K Ω x
    rw [hy]
    change g (t (algebraMap K Ω y)) = algebraMap K Ω x
    rw [t.commutes, ← hy]
    change (g * g⁻¹) (algebraMap K Ω x) = _
    simp)

theorem restrict_galois_conjugate (g : G F Ω) (t : G K Ω) : res F Ω K (galoisConjugate K g t) = g * res F Ω K t * g⁻¹ := by
  ext z; rfl

theorem galois_conjugate_apply (g : G F Ω) (t : G K Ω) (z : Ω) : galoisConjugate K g t z = g (t (g⁻¹ z)) := rfl

def conj (g : G F Ω) : G K Ω →* G K Ω where
  toFun := galoisConjugate K g
  map_one' := by ext z; simp [galois_conjugate_apply]
  map_mul' s t := by ext z; simp [galois_conjugate_apply, AlgEquiv.mul_apply]

theorem res_conj (g : G F Ω) (t : G K Ω) : res F Ω K (conj K g t) = g * res F Ω K t * g⁻¹ := restrict_galois_conjugate K g t

theorem conj_surjective (g : G F Ω) : Function.Surjective (conj K g) := by
  intro u
  refine ⟨conj K g⁻¹ u, ?_⟩
  ext z
  simp [conj, galois_conjugate_apply]

theorem res_injective : Function.Injective (res F Ω K) := AlgEquiv.restrictScalars_injective F

end GlobalTheory.RealGal.TrInv

end

noncomputable section

namespace GlobalTheory.RealGal.TrInv

theorem continuous_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [CharZero F] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] [Normal F K] (g : G F Ω) : Continuous (conj K g) := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois K Ω := inferInstance
  haveI : T2Space (G F Ω) := krullTopology_t2
  have hc : Continuous (res F Ω K) := UpperTheory.V.Af.continuous_restrictScalarsHom F K Ω
  have he := hc.isClosedEmbedding (res_injective (F := F) (Ω := Ω) K)
  rw [he.isEmbedding.continuous_iff]
  have : (res F Ω K) ∘ (conj K g) = fun t => g * res F Ω K t * g⁻¹ := funext (res_conj K g)
  rw [this]
  exact (continuous_const.mul hc).mul continuous_const

theorem isSSRep_comp {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (r : Γ →* GL (Fin a) k) (c : Γ →* Γ)
    (hc : Function.Surjective c) (hr : IsSSRep r) : IsSSRep (r.comp c) := by
  intro W hW
  have hW' : IsInv r W := by
    intro s v hv
    obtain ⟨t, rfl⟩ := hc s
    exact hW t v hv
  obtain ⟨W', h1, h2⟩ := hr W hW'
  exact ⟨W', fun t v hv => h1 (c t) v hv, h2⟩

end GlobalTheory.RealGal.TrInv

namespace GlobalTheory.RealGal


open TrInv in
theorem trace_conj_of_attRes : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r → AttRes π ι K r → ∀ (g : G F Ω) (s s' : G K Ω), res F Ω K s' = g * res F Ω K s * g⁻¹ → ((r s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ h2 l _ ι a π r hr hss hatt g s s' hs
  haveI : Algebra.IsQuadraticExtension F K := ⟨h2⟩
  haveI : Normal F K := Algebra.IsQuadraticExtension.normal F K
  have hsur := conj_surjective (F := F) (Ω := Ω) K g
  have hatt' : AttRes π ι K (r.comp (conj K g)) :=
    GlobalTheory.T.attached_rep_conjugate_invariant F Ω K l ι a π r g (conj K g) (res_conj K g) hsur hatt
  obtain ⟨h, hh⟩ := GlobalTheory.T.attached_galois_rep_unique F Ω K l ι a π r (r.comp (conj K g)) hr (hr.comp (continuous_conj K g)) hss
    (isSSRep_comp r _ hsur hss) hatt hatt'
  have hs' : s' = conj K g s := res_injective (F := F) (Ω := Ω) K (by rw [hs, res_conj])
  subst hs'
  rw [← MonoidHom.comp_apply, hh s]
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle]
  simp

end GlobalTheory.RealGal

end
end
