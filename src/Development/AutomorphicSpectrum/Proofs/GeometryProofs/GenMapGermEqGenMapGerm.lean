module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_genMap_germ {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (s : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp s) = genMap ξ q (X.presheaf.germ U q.1 hq s) := by
  have h : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr s) =
      (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.isOpen hr) s) := by
    intro r hr
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom
      (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hr r.2 s)
  rw [h p hp, h q hq]

theorem exists_open_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : Ω) (ha : a ∈ regAt ξ p) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq g
  exact ⟨U, hU, fun q hq => ⟨_, genMap_germ_eq_genMap_germ ξ U q p hq hU s⟩⟩

theorem regAt_unitAt_open : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω), (a ∈ regAt ξ p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) ∧ (unitAt ξ p a → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → unitAt ξ q a) := by
  intro X Ω _ ξ p a
  refine ⟨exists_open_mem_regAt ξ p a, ?_⟩
  rintro ⟨h0, h1, h2⟩
  obtain ⟨U, hU, HU⟩ := exists_open_mem_regAt ξ p a h1
  obtain ⟨V, hV, HV⟩ := exists_open_mem_regAt ξ p _ h2
  exact ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq => ⟨h0, HU q hq.1, HV q hq.2⟩⟩

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_stalk_closed {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (U : X.Opens) (hp : p.1 ∈ U)
    (hη : genPt ξ ∈ U) (r : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp r) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := U) hp p.2
  have h2 := congr(($h).hom r)
  have e : ∀ x, genMap ξ p x =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes p.2).hom x) := fun _ => rfl
  rw [e]
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom h2

theorem stalk_eq_germ_div_of_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (b : X.presheaf.stalk x.1) :
    ∃ r t : Γ(X, U), b * X.presheaf.germ U x.1 x.2 t = X.presheaf.germ U x.1 x.2 r ∧
      IsUnit (X.presheaf.germ U x.1 x.2 t) := by
  have hl := hU.isLocalization_stalk x
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj (hU.primeIdealOf x).asIdeal.primeCompl b
  exact ⟨r, t.1, hrt, IsLocalization.map_units (X.presheaf.stalk x.1)
    (M := (hU.primeIdealOf x).asIdeal.primeCompl) t⟩

theorem regAt_isLocalRing_isFractionRing_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ →
      ∀ p : Cpt ξ, IsLocalRing (regAt ξ p) ∧ IsFractionRing (regAt ξ p) Ω ∧
        Nonempty (X.presheaf.stalk p.1 ≃+* regAt ξ p) := by
  intro X Ω _ ξ hξ p
  have hsurj : Function.Surjective (genMap ξ p).rangeRestrict := (genMap ξ p).rangeRestrict_surjective
  have hinj : Function.Injective (genMap ξ p).rangeRestrict := fun a b h =>
    hξ.inj p (congrArg Subtype.val h)
  have e : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
    RingEquiv.ofBijective (genMap ξ p).rangeRestrict ⟨hinj, hsurj⟩
  have hloc : IsLocalRing (regAt ξ p) :=
    IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict hsurj
  refine ⟨hloc, ?_, ⟨e⟩⟩
  apply IsFractionRing.of_field
  intro a
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := p.1) trivial
  have hη : genPt ξ ∈ U := p.2.mem_open U.2 hpU
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = a :=
    hξ.bij.2 a
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨⟨_, X.presheaf.germ U p.1 hpU r, rfl⟩, ⟨_, X.presheaf.germ U p.1 hpU t, rfl⟩, ?_⟩
  show _ = genMap ξ p (X.presheaf.germ U p.1 hpU r) / genMap ξ p (X.presheaf.germ U p.1 hpU t)
  rw [genMap_germ_eq_stalk_closed ξ p U hpU hη, genMap_germ_eq_stalk_closed ξ p U hpU hη, eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_existsUnique_equiv :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (M' : LieModel G x E'), ∃! f : E ≃ₗ[R] E', ∀ e, M'.pt (f e) = M.pt e := by
  intro S G _ R _ x E E' _ _ _ _ M M'

  choose f hf using fun e => M'.onto (M.pt e) (M.tan e)
  choose g hg using fun e' => M.onto (M'.pt e') (M'.tan e')
  let φ : E ≃ₗ[R] E' :=
    { toFun := f
      invFun := g
      map_add' := fun e e' => M'.inj (by rw [M'.add, hf, hf, hf, M.add])
      map_smul' := fun c e => by
        show f (c • e) = c • f e
        apply M'.inj
        apply Over.OverMorphism.ext
        rw [M'.smul, hf, hf, M.smul]
      left_inv := fun e => M.inj (by rw [hg, hf])
      right_inv := fun e' => M'.inj (by rw [hf, hg]) }
  refine ⟨φ, fun e => hf e, fun ψ hψ => ?_⟩
  exact LinearEquiv.ext fun e => M'.inj ((hψ e).trans (hf e).symm)

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.lie_model_existsUnique_equiv := GlobalTheory.CompanionTheory.Ar.lieModel_existsUnique_equiv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

private theorem eq_specMap_comp_of_apply_eq {X : Scheme.{0}} {B K Ω : Type} [CommRing B] [Field K]
    [Field Ω] (h : X ⟶ Spec (CommRingCat.of B)) (β : B →+* K)
    (hβ : ∀ x : K, ∃ r u : B, β u ≠ 0 ∧ x * β u = β r)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ h = Spec.map (CommRingCat.ofHom β))
    (k : K →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ X)
    (hy : y ≫ h = Spec.map (CommRingCat.ofHom (k.comp β)))
    (a : Spec (CommRingCat.of Ω)) (b : Spec (CommRingCat.of K)) (hab : y a = s b) :
    y = Spec.map (CommRingCat.ofHom k) ≫ s := by
  have hpt : ∀ (L : Type) [Field L] (p q : Spec (CommRingCat.of L)), p = q := by
    intro L _ p q
    let p' : PrimeSpectrum L := p
    let q' : PrimeSpectrum L := q
    exact (PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p'.asIdeal).trans
      (Ideal.eq_bot_of_prime q'.asIdeal).symm) : p' = q')
  obtain ⟨W, hW, hbW, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (s b))
  haveI := hW.isOpenImmersion_fromSpec
  have hrange : ∀ {Y : Scheme.{0}} (e : Y ⟶ X) (z : Y), (∀ z', z' = z) → e z ∈ W →
      Set.range e ⊆ Set.range hW.fromSpec := by
    intro Y e z hz he
    rintro _ ⟨z', rfl⟩
    rw [hW.range_fromSpec, hz z']
    exact he
  have hyW := hrange y a (fun z' => hpt Ω z' a) (by rw [hab]; exact hbW)
  have hsW := hrange s b (fun z' => hpt K z' b) hbW
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec y hyW)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec s hsW)
  obtain ⟨α, hα⟩ := Spec.map_surjective (hW.fromSpec ≫ h)
  have hσβ : α ≫ σ = CommRingCat.ofHom β := Spec.map_injective (by
    rw [Spec.map_comp, hσ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hs])
  have hψβ : α ≫ ψ = CommRingCat.ofHom (k.comp β) := Spec.map_injective (by
    rw [Spec.map_comp, hψ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hy])
  have hpts : (Spec.map ψ) a = (Spec.map σ) b := by
    apply (Scheme.Hom.isOpenEmbedding hW.fromSpec).injective
    rw [← Scheme.Hom.comp_apply (Spec.map ψ) hW.fromSpec a,
      ← Scheme.Hom.comp_apply (Spec.map σ) hW.fromSpec b, hψ, hσ, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, hab]
  have hker : ∀ x, σ.hom x = 0 → ψ.hom x = 0 := by
    intro x hx
    let a' : PrimeSpectrum Ω := a
    let b' : PrimeSpectrum K := b
    have ha : a'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have hb : b'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have e := congrArg PrimeSpectrum.asIdeal hpts
    have hmem : x ∈ PrimeSpectrum.asIdeal ((Spec.map σ) b) := by
      rw [Spec.map_apply]
      change σ.hom x ∈ b'.asIdeal
      rw [hb, Ideal.mem_bot]
      exact hx
    rw [← e, Spec.map_apply] at hmem
    change ψ.hom x ∈ a'.asIdeal at hmem
    rwa [ha, Ideal.mem_bot] at hmem
  have hψσ : ψ = σ ≫ CommRingCat.ofHom k := by
    apply CommRingCat.hom_ext
    ext x
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    obtain ⟨r, u, hu, hxu⟩ := hβ (σ.hom x)
    have hσα : ∀ z, σ.hom (α.hom z) = β z := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hσβ, CommRingCat.hom_ofHom]
    have hψα : ∀ z, ψ.hom (α.hom z) = k (β z) := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hψβ, CommRingCat.hom_ofHom,
        RingHom.comp_apply]
    have h0 : ψ.hom (x * α.hom u - α.hom r) = 0 := hker _ (by
      rw [map_sub, map_mul, hσα, hσα, hxu, sub_self])
    rw [map_sub, map_mul, hψα, hψα, sub_eq_zero] at h0
    have hku : k (β u) ≠ 0 := (map_ne_zero k).mpr hu
    apply mul_right_cancel₀ hku
    rw [h0, ← map_mul, hxu]
  calc y = IsOpenImmersion.lift hW.fromSpec y hyW ≫ hW.fromSpec :=
        (IsOpenImmersion.lift_fac _ _ _).symm
    _ = Spec.map ψ ≫ hW.fromSpec := by rw [hψ]
    _ = Spec.map (CommRingCat.ofHom k) ≫ s := by
        rw [hψσ, Spec.map_comp, Category.assoc, hσ, IsOpenImmersion.lift_fac]

theorem QFGroup.exists_eq_comp_pt : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
    (Ω : Type) [Field Ω] (k : FractionRing R →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ Γ.G.left),
    y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) →
    ∃ t, y = Spec.map (CommRingCat.ofHom k) ≫ (Γ.pt t).left := by
  intro R _ _ T _ Γ
  cases Γ
  rename_i pt _ pt_onto _
  dsimp only
  intro Ω _ k y hy
  let a0 : Spec (CommRingCat.of Ω) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
  obtain ⟨t, x, hx⟩ := pt_onto (y a0) (by
    rw [← Scheme.Hom.comp_apply y _ a0, hy, Spec.map_apply]
    change Ideal.comap (k.comp (algebraMap R (FractionRing R))) (⊥ : Ideal Ω) = ⊥
    exact Ideal.comap_bot_of_injective _ (k.injective.comp (IsFractionRing.injective R (FractionRing R))))
  refine ⟨t, eq_specMap_comp_of_apply_eq _ (algebraMap R (FractionRing R)) ?_ (pt t).left
    (Over.w (pt t)) k y hy a0 x hx.symm⟩
  intro z
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) z
  exact ⟨n, d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hnd⟩

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
alias GlobalTheory.T.torus_point_over_fraction_field := GlobalTheory.CompanionTheory.Ar.BT.QFGroup.exists_eq_comp_pt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem IsTanAt.comp_monHom {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {v : epsAt x ⟶ G} (hv : IsTanAt G x v) (f : G ⟶ G') [IsMonHom f] :
    IsTanAt G' x (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem lieModel_exists_unique_diff :
    ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (R : Type) [CommRing R]
      (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E']
      [Module R E'] (M : LieModel G x E) (M' : LieModel G' x E') (f : G ⟶ G') [IsMonHom f],
      ∃! A : E →ₗ[R] E', ∀ e, M'.pt (A e) = M.pt e ≫ f := by
  intro S G G' _ _ R _ x E E' _ _ _ _ M M' f _
  have hex : ∀ e, ∃ e', M'.pt e' = M.pt e ≫ f := fun e => M'.onto _ ((M.tan e).comp_monHom f)
  choose A hA using hex
  have hadd : ∀ e₁ e₂, A (e₁ + e₂) = A e₁ + A e₂ := fun e₁ e₂ => M'.inj (by
    rw [hA, M'.add, hA, hA, M.add, MonObj.mul_comp])
  have hsmul : ∀ (c : R) e, A (c • e) = c • A e := fun c e => M'.inj (by
    rw [hA]
    apply Over.OverMorphism.ext
    rw [M'.smul, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc])
  refine ⟨⟨⟨A, hadd⟩, hsmul⟩, fun e => hA e, ?_⟩
  intro B hB
  ext e
  exact M'.inj ((hB e).trans (hA e).symm)

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.lie_model_functorial_map := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_diff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegAtMono

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (x : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes h).hom x) = genMap ξ p x := by
  have e := X.presheaf.stalkSpecializes_comp q.2 h
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (congrArg (fun φ => φ.hom x) e)

theorem genMap_germ_eq (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ) (h : q.1 ⤳ p.1)
    (U : X.Opens) (hp : p.1 ∈ U) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom t) = genMap ξ p ((X.presheaf.germ U p.1 hp).hom t) := by
  rw [← genMap_stalkSpecializes ξ p q h, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]

theorem unitAt_of_isUnit (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) {x : X.presheaf.stalk q.1}
    (hx : IsUnit x) : unitAt ξ q (genMap ξ q x) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨(u.isUnit.map (genMap ξ q)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ), ?_⟩⟩
  exact map_units_inv (genMap ξ q) u

theorem regAt_mono :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p q : Cpt ξ), q.1 ⤳ p.1 →
      regAt ξ p ≤ regAt ξ q ∧
        (IsCptGen ξ → ∀ a ∈ regAt ξ q, ∃ s ∈ regAt ξ p, unitAt ξ q s ∧ s * a ∈ regAt ξ p) := by
  intro X Ω _ ξ p q h
  refine ⟨?_, fun _ => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, genMap_stalkSpecializes ξ p q h x⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hp, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p.1) isOpen_univ
    have hU : IsAffineOpen U := hU
    have hq : q.1 ∈ U := h.mem_open U.2 hp
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q.1, hq⟩ : U)
    have hloc := hU.isLocalization_stalk ⟨q.1, hq⟩
    obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) x
    have hu : IsUnit ((X.presheaf.germ U q.1 hq).hom t.1) :=
      IsLocalization.map_units (X.presheaf.stalk q.1) t
    have e' : x * (X.presheaf.germ U q.1 hq).hom t.1 = (X.presheaf.germ U q.1 hq).hom r := e
    refine ⟨genMap ξ q ((X.presheaf.germ U q.1 hq).hom t.1), ?_, unitAt_of_isUnit ξ q hu, ?_⟩
    · exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩
    · rw [mul_comm, ← map_mul, e']
      exact ⟨_, (genMap_germ_eq ξ p q h U hp hq _).symm⟩

end GlobalTheory.CompanionTheory.Ar.RegAtMono
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptInh

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem dom (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) := by
  exact Function.Injective.isDomain (genMap ξ p) (h.inj p)

theorem nogen (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hy
  obtain ⟨q, hq⟩ := hy'
  obtain ⟨f, hf⟩ : ∃ f : X.presheaf.stalk (genPt ξ) →+* Ω, Function.Bijective f :=
    ⟨(Scheme.stalkClosedPointTo ξ).hom, h.bij⟩
  have hmax : ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (genPt ξ)), x = 0 := by
    intro x hx
    by_contra hne
    have h1 : f x ≠ 0 := by
      intro h0
      apply hne
      apply hf.1
      rw [h0, map_zero]
    obtain ⟨v, hv⟩ := hf.2 (f x)⁻¹
    have hxv : x * v = 1 := hf.1 (by rw [map_mul, hv, mul_inv_cancel₀ h1, map_one])
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx) (IsUnit.of_mul_eq_one v hxv)
  have hq' : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime q).ne_top
    · intro x hx
      rw [hmax x hx]
      exact zero_mem _
  rw [← hq, hq']
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.CompanionTheory.Ar.CptInh
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAt
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegSec

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

noncomputable def val (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) {q : X} (hq : genPt ξ ⤳ q) (hqU : q ∈ U)
    (s : Γ(X, U)) :
    genMap ξ ⟨q, hq⟩ ((X.presheaf.germ U q hqU).hom s) = val ξ U h s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold genMap val
  rw [← X.presheaf.germ_stalkSpecializes hqU hq]
  exact (key (X.presheaf.stalkSpecializes hq) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.germ U q hqU) (X.presheaf.stalkSpecializes hq) s).symm).trans
      (key (X.presheaf.germ U q hqU ≫ X.presheaf.stalkSpecializes hq)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_res {V U : X.Opens} (i : V ⟶ U) (hV : genPt ξ ∈ V) (hU : genPt ξ ∈ U) (s : Γ(X, U)) :
    val ξ V hV ((X.presheaf.map i.op).hom s) = val ξ U hU s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold val
  rw [← X.presheaf.germ_res i (genPt ξ) hV]
  exact (key (X.presheaf.germ V (genPt ξ) hV) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.map i.op) (X.presheaf.germ V (genPt ξ) hV) s).symm).trans
      (key (X.presheaf.map i.op ≫ X.presheaf.germ V (genPt ξ) hV)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_injective (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) : Function.Injective (val ξ U h) := by
  intro s t hst
  refine TopCat.Presheaf.section_ext X.sheaf U s t (fun q hq => ?_)
  have hq' := hU q hq
  apply hξ.inj ⟨q, hq'⟩
  exact (genMap_germ ξ U h hq' hq s).trans (hst.trans (genMap_germ ξ U h hq' hq t).symm)

theorem mem_range_val_iff (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω) :
    a ∈ (val ξ U h).range ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  constructor
  · intro ha q hqU
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom s, genMap_germ ξ U h q.2 hqU s⟩
  · intro H
    have loc : ∀ q : U, ∃ (W : X.Opens) (t : Γ(X, W)) (_ : (q : X) ∈ W) (hg : genPt ξ ∈ W),
        val ξ W hg t = a := by
      rintro ⟨q, hq⟩
      have hq' : genPt ξ ⤳ q := hU q hq
      obtain ⟨x, hx⟩ := RingHom.mem_range.mp (H ⟨q, hq'⟩ hq)
      obtain ⟨W, hqW, t, ht⟩ := TopCat.Presheaf.germ_exist X.presheaf x
      have hg : genPt ξ ∈ W := hq'.mem_open W.isOpen hqW
      refine ⟨W, t, hqW, hg, ?_⟩
      rw [← genMap_germ ξ W hg hq' hqW t]
      exact (congrArg (genMap ξ ⟨q, hq'⟩) ht).trans hx
    choose W t hqW hg hval using loc
    let V : U → X.Opens := fun q => W q ⊓ U
    have hgV : ∀ q, genPt ξ ∈ V q := fun q => ⟨hg q, h⟩
    let sf : ∀ q : U, Γ(X, V q) := fun q =>
      (X.presheaf.map (homOfLE inf_le_left : V q ⟶ W q).op).hom (t q)
    have hsf : ∀ q, val ξ (V q) (hgV q) (sf q) = a := fun q =>
      (val_res ξ (homOfLE inf_le_left : V q ⟶ W q) (hgV q) (hg q) (t q)).trans (hval q)
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V sf := by
      intro i j
      apply val_injective ξ hξ (V i ⊓ V j) ⟨hgV i, hgV j⟩ (fun q hq => hU q hq.1.2)
      exact ((val_res ξ (TopologicalSpace.Opens.infLELeft (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV i) (sf i)).trans (hsf i)).trans
        ((val_res ξ (TopologicalSpace.Opens.infLERight (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV j) (sf j)).trans (hsf j)).symm
    have hcover : U ≤ iSup V := by
      intro q hq
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hqW ⟨q, hq⟩, hq⟩
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := X.sheaf) (U := V) U
      (fun q => homOfLE inf_le_right) hcover sf hcompat
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    have i0 : U := ⟨genPt ξ, h⟩
    exact (val_res ξ (homOfLE inf_le_right : V i0 ⟶ U) (hgV i0) h s).symm.trans
      ((congrArg (val ξ (V i0) (hgV i0)) (hs i0)).trans (hsf i0))

end GlobalTheory.CompanionTheory.Ar.RegSec

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_sections : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X),
    IsCptGen ξ → ∀ (U : X.Opens) (h : genPt ξ ∈ U), (∀ q : X, q ∈ U → genPt ξ ⤳ q) →
      Function.Injective (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom ∧
      ∀ a : Ω, a ∈ (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom.range ↔
        ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  intro X Ω _ ξ hξ U h hU
  exact ⟨RegSec.val_injective ξ hξ U h hU, RegSec.mem_range_val_iff ξ hξ U h hU⟩

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.germ_genPt_injective_range_regAt := GlobalTheory.CompanionTheory.Ar.regAt_sections
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DomBy
noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.OrVert

def DomBy {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (W : Subring Ω') (i : Ω →+* Ω')
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) : Prop :=
  (∀ a ∈ regAt ξ q, i a ∈ W) ∧ ∀ a ∈ regAt ξ q, a ≠ 0 → (i a)⁻¹ ∈ W → a⁻¹ ∈ regAt ξ q

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGeneric
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_closedPointTo {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (V : X.Opens) (hy : p.1 ∈ V) (hx : genPt ξ ∈ V) (b : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hy b) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hx b) := by
  have h : X.presheaf.germ V (genPt ξ) hx = X.presheaf.germ V p.1 hy ≫ X.presheaf.stalkSpecializes p.2 :=
    (X.presheaf.germ_stalkSpecializes hy p.2).symm
  rw [h]
  rfl

theorem exists_frac_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ b c : X.presheaf.stalk p.1, genMap ξ p c ≠ 0 ∧ a * genMap ξ p c = genMap ξ p b := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (genPt ξ)) := (X.presheaf.germ U (genPt ξ) hgU).hom.toAlgebra
  have _ : IsLocalization.AtPrime (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨genPt ξ, hgU⟩
  obtain ⟨s, rfl⟩ : ∃ s : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s = a := hξ.bij.2 a
  obtain ⟨⟨r, d⟩, rfl⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal.primeCompl s
  refine ⟨X.presheaf.germ U p.1 hpU r, X.presheaf.germ U p.1 hpU d, ?_, ?_⟩
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have hu := IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) d
    exact (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU, genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have h := congrArg (Scheme.stalkClosedPointTo ξ).hom (IsLocalization.mk'_spec (X.presheaf.stalk (genPt ξ)) r d)
    exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans h

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStalkFractionOfGenericStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.exists_stalk_fraction_of_generic := GlobalTheory.CompanionTheory.Ar.exists_frac_genMap
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieInh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem stdSmooth_mvPolynomial (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  have hker : (Algebra.Generators.mvPolynomial R (Fin n)).ker = ⊥ := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val, Algebra.Generators.mvPolynomial_val]
    exact (RingHom.injective_iff_ker_eq_bot _).1 fun a b h => by
      simpa only [MvPolynomial.aeval_X_left_apply] using h
  let P : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨Algebra.Generators.mvPolynomial R (Fin n), Empty.elim, by rw [hker]; simp⟩
  let P' : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P, Empty.elim, fun a => a.elim⟩
  let P'' : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P', by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty, map_one]
      exact isUnit_one⟩
  refine Algebra.IsStandardSmoothOfRelativeDimension.mk ⟨Fin n, Empty, inferInstance, inferInstance, P'', ?_⟩
  simp [Algebra.Presentation.dimension]

variable {X : Scheme.{0}}

variable {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)

end GlobalTheory.CompanionTheory.Ar.LieInh

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem injective_of_maximal_point {X : Scheme.{0}} {Ω : Type} [Field Ω] (p : X)
    [IsDomain (X.presheaf.stalk p)] (φ : X.presheaf.stalk p ⟶ CommRingCat.of Ω)
    (h : ∀ y : X, y ⤳ (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) →
      y = (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω)) :
    Function.Injective φ.hom := by
  let z : PrimeSpectrum (X.presheaf.stalk p) := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum (X.presheaf.stalk p) := PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint Ω)
  have hs : z ⤳ q := (PrimeSpectrum.le_iff_specializes z q).1 bot_le
  have hq : (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) = X.fromSpecStalk p q := rfl
  rw [hq] at h
  have h1 : X.fromSpecStalk p z = X.fromSpecStalk p q :=
    h _ (hs.map (X.fromSpecStalk p).continuous)
  have h2 : z = q := (X.fromSpecStalk p).isEmbedding.injective h1
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  have h3 : a ∈ q.asIdeal := by
    change φ.hom a ∈ (IsLocalRing.closedPoint Ω).asIdeal
    rw [ha]
    exact Ideal.zero_mem _
  rw [← h2] at h3
  exact h3

theorem isCptGen_of_maximal_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : ∀ y : X, y ⤳ genPt ξ → y = genPt ξ)
    (hs : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) : IsCptGen ξ := by
  refine ⟨⟨?_, hs⟩, fun p => ?_⟩
  · have := hX (ξ (IsLocalRing.closedPoint Ω))
    refine injective_of_maximal_point _ (Scheme.stalkClosedPointTo ξ) ?_
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact h
  · obtain ⟨p, hp⟩ := p
    have := hX p
    have hp' : ξ (IsLocalRing.closedPoint Ω) ⤳ p := hp
    refine injective_of_maximal_point p
      (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ?_
    have e : Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫
        X.fromSpecStalk p = ξ := by
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    rw [e]
    exact h

theorem isCptGen_of_maximal : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X,
    (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  intro X hX x h
  have e : genPt (Ω := X.residueField x) (X.fromSpecResidueField x) = x :=
    X.fromSpecResidueField_apply x _
  refine isCptGen_of_maximal_of_surjective hX _ (by rw [e]; exact h) ?_
  unfold Scheme.stalkClosedPointTo
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso _).hom).2.comp
    ((X.fromSpecResidueField x).stalkMap_surjective _)

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.isCptGen_residue_field_generic := GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersion
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isClosedImmersion_torsion_lift {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsSeparated G.hom]
    (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
    (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (i : Γ.G.left ⟶ G.left)
    (h : Γ.IsTorsionAlong G x N i) :
    IsClosedImmersion (pullback.lift i Γ.G.hom h.isOver : Γ.G.left ⟶ pullback G.hom x) := by
  obtain ⟨i', hi'⟩ : ∃ i' : Γ.G.left ⟶ pullback G.hom x, i' = pullback.lift i Γ.G.hom h.isOver :=
    ⟨_, rfl⟩
  rw [← hi']
  have i'fst : i' ≫ pullback.fst G.hom x = i := by rw [hi']; exact pullback.lift_fst _ _ _
  have i'snd : i' ≫ pullback.snd G.hom x = Γ.G.hom := by
    rw [hi']
    exact pullback.lift_snd _ _ _
  let PO : Over X := Over.mk (pullback.snd G.hom x ≫ x)
  let u : PO ⟶ G := Over.homMk (pullback.fst G.hom x) pullback.condition
  obtain ⟨f, hfdef⟩ : ∃ f : pullback G.hom x ⟶ G.left, f = (u ^ N).left := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : pullback G.hom x ⟶ G.left, g = (1 : PO ⟶ G).left := ⟨_, rfl⟩
  have hf : f ≫ G.hom = pullback.snd G.hom x ≫ x := by rw [hfdef]; exact Over.w (u ^ N)
  have hg : g ≫ G.hom = pullback.snd G.hom x ≫ x := by rw [hgdef]; exact Over.w (1 : PO ⟶ G)
  have hfg : f ≫ G.hom = g ≫ G.hom := hf.trans hg.symm

  let jq : pullback (pullback.diagonal G.hom) (pullback.lift f g hfg) ⟶ pullback G.hom x :=
    pullback.snd _ _
  haveI : IsClosedImmersion jq := inferInstance
  have l1 : pullback.lift f g hfg ≫ pullback.fst G.hom G.hom = f := pullback.lift_fst _ _ _
  have l2 : pullback.lift f g hfg ≫ pullback.snd G.hom G.hom = g := pullback.lift_snd _ _ _
  have cond := pullback.condition (f := pullback.diagonal G.hom) (g := pullback.lift f g hfg)
  have jqf : jq ≫ f = pullback.fst _ _ := by
    have := congrArg (· ≫ pullback.fst G.hom G.hom) cond
    simpa [jq, l1] using this.symm
  have jqg : jq ≫ g = pullback.fst _ _ := by
    have := congrArg (· ≫ pullback.snd G.hom G.hom) cond
    simpa [jq, l2] using this.symm
  have jqeq : jq ≫ f = jq ≫ g := jqf.trans jqg.symm

  have key : i' ≫ f = i' ≫ g := by
    let g₀ : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
    have h0 : g₀ ^ N = 1 := (h.kernel Γ.G g₀).2 ⟨𝟙 _, by simp [g₀]⟩
    let ψ : Over.mk (Γ.G.hom ≫ x) ⟶ PO :=
      Over.homMk i' (by simp [PO, reassoc_of% i'snd])
    have h1 : ψ ≫ u = g₀ := by
      ext1
      simpa [ψ, u, g₀] using i'fst
    have h2 : ψ ≫ u ^ N = ψ ≫ 1 := by rw [MonObj.comp_pow, h1, h0, MonObj.comp_one]
    have h3 : i' ≫ (u ^ N).left = i' ≫ (1 : PO ⟶ G).left := congrArg (fun m => m.left) h2
    rw [hfdef, hgdef]
    exact h3
  let b : Γ.G.left ⟶ pullback (pullback.diagonal G.hom) (pullback.lift f g hfg) :=
    pullback.lift (i' ≫ f) i' (by
      apply pullback.hom_ext
      · simp [l1]
      · simp [l2, key])
  have bjq : b ≫ jq = i' := pullback.lift_snd _ _ _

  let Qs : Over (Spec (CommRingCat.of R)) := Over.mk (jq ≫ pullback.snd G.hom x)
  let g' : Over.mk (Qs.hom ≫ x) ⟶ G := Over.homMk (jq ≫ pullback.fst G.hom x)
    (by simp [Qs, pullback.condition])
  have hg' : g' ^ N = 1 := by
    let φ : Over.mk (Qs.hom ≫ x) ⟶ PO := Over.homMk jq (by simp [PO, Qs])
    have h1 : φ ≫ u = g' := by
      ext1
      simp [φ, u, g']
    have h2 : φ ≫ u ^ N = φ ≫ 1 := by
      apply Over.OverMorphism.ext
      change jq ≫ (u ^ N).left = jq ≫ (1 : PO ⟶ G).left
      rw [← hfdef, ← hgdef]
      exact jqeq
    rw [← h1, ← MonObj.comp_pow, h2, MonObj.comp_one]
  obtain ⟨y, hy⟩ := (h.kernel Qs g').1 hg'
  have hyl : y.left ≫ i = jq ≫ pullback.fst G.hom x := hy
  have hys : y.left ≫ Γ.G.hom = jq ≫ pullback.snd G.hom x := Over.w y
  have yi' : y.left ≫ i' = jq := by
    apply pullback.hom_ext
    · simp [i'fst, hyl]
    · simp [i'snd, hys]
  have ab : y.left ≫ b = 𝟙 _ := by
    rw [← cancel_mono jq]
    simp [bjq, yi']
  have ba : b ≫ y.left = 𝟙 _ := by
    have e : (Over.homMk (b ≫ y.left) (by
        change (b ≫ y.left) ≫ Γ.G.hom = Γ.G.hom
        rw [Category.assoc, hys, ← Category.assoc, bjq, i'snd]) : Γ.G ⟶ Γ.G) = 𝟙 Γ.G := by
      apply h.inj Γ.G
      change (b ≫ y.left) ≫ i = 𝟙 _ ≫ i
      rw [Category.assoc, hyl, ← Category.assoc, bjq, i'fst, Category.id_comp]
    exact congrArg (fun m => m.left) e
  haveI : IsIso b := ⟨y.left, ba, ab⟩
  rw [← bjq]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
alias GlobalTheory.T.torsion_lift_is_closed_immersion := GlobalTheory.CompanionTheory.Ar.BT.isClosedImmersion_torsion_lift
end
end
