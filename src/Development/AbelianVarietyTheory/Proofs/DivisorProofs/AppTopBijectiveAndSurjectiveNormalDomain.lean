module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem jK_appTop_injective (R : Type) [CommRing R] [IsDomain R] :
    Function.Injective (jK R).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom h
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom x) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) := fun x =>
    congrArg (fun f => f.hom x) e
  rw [h3, h3] at h2
  have h4 := IsFractionRing.injective R (FractionRing R) h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h4
  simpa using this

theorem Modif.gp_appTop_injective {R : Type} [CommRing R] [IsDomain R] (M : Modif R) :
    Function.Injective M.gp.appTop.hom := by
  haveI := M.integral
  haveI := M.dominant
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← AlgebraicGeometry.basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := M.gp.denseRange.exists_mem_open (M.S.basicOpen s).isOpen ⟨x, hx⟩
  have : y ∈ M.gp ⁻¹ᵁ M.S.basicOpen s := hy
  rw [Scheme.preimage_basicOpen_top, hs, Scheme.basicOpen_zero] at this
  exact absurd this (by simp)

theorem Modif.appTop_comp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (a : Γ(Sp R, ⊤)) :
    M.gp.appTop.hom (M.π.appTop.hom a) = (jK R).appTop.hom a := by
  rw [← M.gp_π, Scheme.Hom.comp_appTop]
  rfl

theorem Modif.appTop_bijective_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (M : Modif R), Function.Bijective M.π.appTop.hom ∧ Surjective M.π := by
  intro R _ _ _ _ M
  haveI := M.proper
  haveI := M.integral
  have hinj : Function.Injective M.π.appTop.hom := fun a b h => jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  refine ⟨⟨hinj, fun b => ?_⟩, ⟨?_⟩⟩
  ·
    obtain ⟨p, hpm, hp⟩ := isIntegral_appTop_of_universallyClosed M.π b
    let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let eK := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv
    have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    have h3 : ∀ x, eK ((jK R).appTop.hom x) = algebraMap R (FractionRing R) (eR x) := fun x =>
      congrArg (fun f => f.hom x) e
    have hc : IsIntegral R (eK (M.gp.appTop.hom b)) := by
      refine ⟨p.map eR.toRingHom, hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : (algebraMap R (FractionRing R)).comp eR.toRingHom =
          (eK.toRingHom.comp M.gp.appTop.hom).comp M.π.appTop.hom := by
        ext x
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [M.appTop_comp, h3]
      rw [this]
      calc _ = (eK.toRingHom.comp M.gp.appTop.hom) (p.eval₂ M.π.appTop.hom b) :=
            (Polynomial.hom_eval₂ _ _ _ _).symm
        _ = 0 := by rw [hp, map_zero]
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc
    refine ⟨eR.symm r, M.gp_appTop_injective (eK.injective ?_)⟩
    rw [M.appTop_comp, h3, RingEquiv.apply_symm_apply, hr]
  ·
    have hcl : IsClosed (Set.range M.π) := (M.π.isClosedMap).isClosed_range
    have hd : Dense (Set.range (jK R)) := (Modif.self R).dominant.denseRange
    have hsub : Set.range (jK R) ⊆ Set.range M.π := by
      rintro _ ⟨y, rfl⟩
      exact ⟨M.gp y, by rw [← Scheme.Hom.comp_apply, M.gp_π]⟩
    have := (hd.mono hsub).closure_eq
    rw [hcl.closure_eq] at this
    exact Set.range_eq_univ.1 this

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appTop_bijective_and_surjective_normalDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (M : Modif R), Function.Bijective M.π.appTop.hom ∧ Surjective M.π := by
  first | exact @GlobalTheory.Mum.Modif.appTop_bijective_surjective | exact GlobalTheory.Mum.Modif.appTop_bijective_surjective | (intros; apply GlobalTheory.Mum.Modif.appTop_bijective_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGenerated
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem fg_ringOn_of_isAffineOpen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → (M.ringOn U).FG :=
  fun _ _ _ _ _ _ _ hU hne => GlobalTheory.ZH.RatModel.fg_ringOn hU hne

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGeneratedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringOn_affineOpen_finitelyGenerated : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → (M.ringOn U).FG := by
  first | exact @GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen | exact GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen | (intros; apply GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagEndIsMonHom
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj GrpObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

def diagPrecomp {T : Scheme.{0}} {X Y M : Over T} [MonObj M] (f : X ⟶ Y) : (Y ⟶ M) →* (X ⟶ M) where
  toFun := (f ≫ ·)
  map_one' := by
    change f ≫ toUnit Y ≫ η = toUnit X ≫ η
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit Y)]
  map_mul' g h := by
    change f ≫ lift g h ≫ μ = lift (f ≫ g) (f ≫ h) ≫ μ
    rw [← Category.assoc, comp_lift]

theorem exists_diagEnd_isMonHom (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Scheme.{0})
    (P : PolAV T) (u : T ⟶ F.X) (h : SharpOver F W P u) :
    ∃ ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A), IsDiagEnd F W P u ε ∧ ∀ E, IsMonHom (ε E) := by
  obtain ⟨c, hc, pr, hpr, huniq, hL⟩ := h
  choose ε hε _ using fun E : Matrix (Fin 8) (Fin 8) ℤ =>
    huniq P.A (fun a => ((List.finRange 8).map fun b => pr b ^ E a b).prod)
  have ext : ∀ (T' : Over T) (x x' : T' ⟶ P.A), (∀ a, x ≫ pr a = x' ≫ pr a) → x = x' := fun T' x x' hx =>
    (huniq T' (fun a => x' ≫ pr a)).unique hx (fun _ => rfl)
  refine ⟨ε, ⟨c, hc, pr, hpr, huniq, hL, hε⟩, fun E => ?_⟩
  have key : ∀ (T' : Over T) (x : T' ⟶ P.A) (a : Fin 8),
      (x ≫ ε E) ≫ pr a = ((List.finRange 8).map fun b => (x ≫ pr b) ^ E a b).prod := by
    intro T' x a
    rw [Category.assoc, hε]
    change diagPrecomp (M := c.A) x _ = _
    rw [map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    exact map_zpow (diagPrecomp (M := c.A) x) (pr b) (E a b)
  refine isMonHom_of_mul _ fun T' x z => ext T' _ _ fun a => ?_
  have hm : ∀ (b : Fin 8) (x z : T' ⟶ P.A), (x * z) ≫ pr b = (x ≫ pr b) * (z ≫ pr b) := fun b x z =>
    map_mul (IsMonHom.monoidHom (pr b) T') x z
  have hm' : ((x ≫ ε E) * (z ≫ ε E)) ≫ pr a = ((x ≫ ε E) ≫ pr a) * ((z ≫ ε E) ≫ pr a) :=
    map_mul (IsMonHom.monoidHom (pr a) T') (x ≫ ε E) (z ≫ ε E)
  rw [key, hm', key, key, ← List.prod_map_mul]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  rw [hm, mul_zpow]

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem Obs.sig_basic : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → (∀ y, σ y ∈ I.map (algebraMap R B)) ∧ (∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y) ∧ (∀ b₀ : B₀, σ (1 ⊗ₜ b₀) = 0) ∧ ∀ x ∈ I.map (algebraMap R B), ∃ y, α.KerQ y ∧ σ y = x := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker σ hσ
  have h2 : ∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← map_mul, hσ, hσ, mul_smul_comm]
    | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  refine ⟨?_, h2, ?_, ?_⟩
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [hσ, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem y'))
    | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
  · intro b₀
    obtain ⟨b', rfl⟩ := hp b₀
    rw [hσ, α.one, zero_smul]
  · intro x hx
    rw [Ideal.map, Ideal.span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨y, hy0, hyk⟩ := α.surj i hi
      refine ⟨y ⊗ₜ 1, ?_, ?_⟩
      · simp [Obs.Aug.KerQ, hy0]
      · rw [← map_one p, hσ, hyk, Algebra.smul_def, _root_.mul_one]
    | zero => exact ⟨0, by simp [Obs.Aug.KerQ], by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hx'
      refine ⟨y + y', ?_, by rw [map_add (f := _)]⟩
      simp only [Obs.Aug.KerQ, map_add (f := _)] at *; rw [hy, hy', add_zero]
    | smul b x _ hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨(1 ⊗ₜ p b) * y, ?_, by rw [h2, smul_eq_mul]⟩
      simp only [Obs.Aug.KerQ, map_mul] at *; rw [hy, mul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicPropertiesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_sigma_map_basic_properties : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → (∀ y, σ y ∈ I.map (algebraMap R B)) ∧ (∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y) ∧ (∀ b₀ : B₀, σ (1 ⊗ₜ b₀) = 0) ∧ ∀ x ∈ I.map (algebraMap R B), ∃ y, α.KerQ y ∧ σ y = x := by
  first | exact @GlobalTheory.Obs.sig_basic | exact GlobalTheory.Obs.sig_basic | (intros; apply GlobalTheory.Obs.sig_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauOfPerFactor
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

variable {R : Type} [CommRing R] [IsDomain R]

theorem gm_jK_unitOn (w : Rˣ) (z : (TK R).left) :
    gm (toUnit (TK R)).left z ⊤ (unitOn w) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)) := by
  have e : (toUnit (TK R)).left = 𝟙 _ ≫ jK R := by simp
  rw [e, ← gm_pull (𝟙 _) (jK R) z ⊤ trivial]
  congr 1
  apply Units.ext
  have := congrArg (fun q => q.hom (w : R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

theorem tauCoord_mul_unit {Q : Data R} {a b : Q.X} {k : (FractionRing R)ˣ} (h : Q.TauCoord a b k) (w : Rˣ) :
    Q.TauCoord a b (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := by
  obtain ⟨u, hu, hv⟩ := h
  let ρ : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ := unitOn w⁻¹
  refine ⟨⟨fun j => res le_top ρ * u.s j⟩, fun i j => ?_, fun z J hJ => ?_⟩
  · show res _ (res le_top ρ * u.s i) = _ * res _ (res le_top ρ * u.s j)
    rw [map_mul, map_mul, InhTate.res_res, InhTate.res_res, hu i j]
    exact mul_left_comm _ _ _
  · rw [hv z J hJ]
    have hm := hJ.mem (lamPts (Q.c a) (Q.c b)) (toUnit (TK R)).left
    show _ = _ * gm _ z _ (res le_top ρ * u.s _)
    erw [MonoidHom.map_mul, gm_res _ z le_top hm]
    have e3 : gm (toUnit (TK R)).left z ⊤ ρ =
        (gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)))⁻¹ := by
      rw [← gm_jK_unitOn, ← MonoidHom.map_inv]
      exact congrArg _ (MonoidHom.map_inv _ _)
    have e4 : unitOn (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) =
        unitOn k * unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := MonoidHom.map_mul _ _ _
    rw [e3, e4, MonoidHom.map_mul]
    have : val u (toUnit (TK R)).left z J = gm (toUnit (TK R)).left z _ (u.s _) := rfl
    rw [this, _root_.mul_assoc, mul_inv_cancel_left]
    rfl

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneRanksFieldCharP
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} [hp : Fact p.Prime]

theorem finrank_eq_of_semilinear_surjective {W k M V : Type} [CommRing W] [Nontrivial W] [Field k]
    [AddCommGroup M] [Module W M] [Module.Free W M] [Module.Finite W M] [AddCommGroup V] [Module k V]
    {σ : W →+* k} (hσ : Function.Surjective σ) {q : ℕ} (hq : (q : k) = 0) (r : M →ₛₗ[σ] V)
    (hr : Function.Surjective r) (hk : ∀ m, r m = 0 → ∃ n, m = q • n) :
    Module.Finite k V ∧ Module.finrank k V = Module.finrank W M := by
  let b := Module.finBasis W M
  have h1 : LinearIndependent k fun i => r (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    choose w hw using fun i => hσ (c i)
    obtain ⟨n, hn⟩ := hk (∑ i, w i • b i) (by simpa only [map_sum, map_smulₛₗ, hw] using hc)
    have e := congrArg (fun m => σ (b.repr m i)) hn
    simpa [hq, hw, Finsupp.single_apply] using e
  have h2 : ⊤ ≤ Submodule.span k (Set.range fun i => r (b i)) := fun v _ => by
    obtain ⟨m, rfl⟩ := hr v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr m, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨.of_basis (.mk h1 h2), by rw [Module.finrank_eq_card_basis (.mk h1 h2), Fintype.card_fin]⟩

section BaseChange

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S] {G H : PDivGroup p R}

end BaseChange

variable (hW : Published.BarsottiTateDieudonne.WittModule) {K : Type} [Field K] (h : (p : K) = 0)
include hW h


omit hW in
theorem range_rigExtMap_relFrob (G : PDivGroup p K) :
    LinearMap.range (rigExtMap (relFrob h G)) =
      Submodule.span K (Set.range ⇑(SemiHom.rig (absFrob h G))) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, rfl⟩
    have induct (P : (frobTwist h G).RigExt → Prop)
        (htmul : ∀ (r : K) y, P (r • (frobProj h G).rig y))
        (hadd : ∀ x y, P x → P y → P (x + y)) : P x := by
      letI := (frobRing h).toAlgebra
      obtain ⟨y, rfl⟩ := (liftSemi_rig_bijective (R := K) K G h
        (.inl (@Module.Flat.of_free K K _ _ (_) (@Module.Free.of_divisionRing K K _ _ (_))))).2 x
      induction y using TensorProduct.inductionOn with
      | tmul r y => exact htmul r y
      | add x y hx hy => exact (congrArg P (map_add _ _ _)).mpr (hadd _ _ hx hy)
    refine induct (fun x => rigExtMap (relFrob h G) x ∈ _) (fun r y => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, rigExtMap_relFrob_rig]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
    · rw [map_add (rigExtMap (relFrob h G))]
      exact add_mem hx hy
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, rigExtMap_relFrob_rig h G y⟩


end PDivGroup

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem isLab_onto_and_ker : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy → Function.Surjective yy ∧ yy.ker = X₁.S.HH X₁.M z₁ := by
  intro g n F W Z i X₁ _ _ _ _ _ _ _ ε₁ _ p _ z₁ c yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR', y₀, hy₀, u, l, j, -, hyy, -⟩ := hl
  have hm : NeZero (X₁.S.r * X₁.S.N) :=
    ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)⟩
  refine ⟨?_, ?_⟩
  · intro m
    obtain ⟨χ', rfl⟩ := QuotientAddGroup.mk_surjective m
    obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm χ'))
    exact ⟨a, by rw [hyy a _ ha, j.apply_symm_apply]⟩
  have hker : yy.ker = l.yy.ker := by
    ext a
    simp only [AddMonoidHom.mem_ker]
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [hyy a χ hχ.symm, ← hχ, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨j.symm v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv, j.symm_apply_apply]
    · rintro ⟨v, hv⟩
      refine ⟨j v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv]
  have hint : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one c.cen ((X₁.M.O z₁).algebraMap_mem a)
  have hcl := GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint
  rw [hker, ← hcl.2]

  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  set val := X₁.M.val (gPt p ≫ c.y) with hval
  have hsp : ∀ w, (gPt p ≫ c.y) w ⤳ (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ z₁ :=
    RatModel.gPt_specializes c.cen _
  have hy : ∀ x, y₀ ⟨c₀ * X₁.S.th x, hth x⟩ = val (c₀ * X₁.S.th x) := fun x => hy₀ _
  have hmul : ∀ x, ‖val (c₀ * X₁.S.th x)‖ = ‖val (X₁.S.th x / X₁.S.th x₀)‖ * ‖val (c₀ * X₁.S.th x₀)‖ := by
    intro x
    rw [← norm_mul, hval, ← RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth x₀))]
    congr 2
    have := hx₀.1
    field_simp
  have hδ : ‖val (c₀ * X₁.S.th x₀)‖ = (X₁.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    apply le_antisymm
    · rw [← hy]
      exact le_ciSup (f := fun x => ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖) (Set.finite_range _).bddAbove x₀
    · obtain ⟨x₁, hx₁⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖)
      change ⨆ x, ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖ ≤ _
      rw [← hx₁, hy, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one c.cen (hx₀.2 x₁))
  have key : ∀ x, x ∈ X₁.S.supI X₁.M z₁ ↔
      ‖y₀ ⟨c₀ * X₁.S.th x, hth x⟩‖ = (X₁.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    intro x
    change X₁.M.Div X₁.S.th x z₁ ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff c.cen (hx₀.2 x), hy, hmul x, hδ]
    exact (mul_eq_right₀ hcl.1.ne').symm
  rw [ThetaSys.HH]
  congr 1
  ext x
  exact (key x).symm

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem dvd_of_forall_height_one_exists_dvd_mul {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {h z : A} (hh : h ≠ 0)
    (H : ∀ P : Ideal A, P.IsPrime → P.height = 1 → ∃ s ∉ P, h ∣ s * z) : h ∣ z := by
  let K := FractionRing A
  have hhK : algebraMap A K h ≠ 0 := fun h0 =>
    hh (IsFractionRing.injective A K (by rw [h0, map_zero]))
  have hmem : algebraMap A K z / algebraMap A K h ∈ (algebraMap A K).range := by
    refine ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := A) _ ?_
    intro P hP h1
    obtain ⟨s, hs, t, ht⟩ := H P hP h1
    refine ⟨s, hs, t, ?_⟩
    rw [← mul_div_assoc, eq_div_iff hhK, ← map_mul, ← map_mul, ht, mul_comm]
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hc, mul_div_assoc', eq_div_iff hhK, mul_comm]

section SquareIdeal

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

theorem dvd_mul_of_dvd_sq_of_dvd_sq {h x y : A} (hx : h ∣ x ^ 2) (hy : h ∣ y ^ 2) : h ∣ x * y := by
  have : h ^ 2 ∣ (x * y) ^ 2 := by
    rw [mul_pow, sq h]; exact mul_dvd_mul hx hy
  exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 this

def sqDvdIdeal (h : A) : Ideal A where
  carrier := {x | h ∣ x ^ 2}
  add_mem' := by
    intro x y hx hy
    have hxy := dvd_mul_of_dvd_sq_of_dvd_sq hx hy
    show h ∣ (x + y) ^ 2
    have e : (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
    rw [e]
    exact dvd_add (dvd_add hx (dvd_mul_of_dvd_right hxy _)) hy
  zero_mem' := by show h ∣ (0 : A) ^ 2; simp
  smul_mem' := by
    intro c x hx
    show h ∣ (c * x) ^ 2
    rw [mul_pow]; exact dvd_mul_of_dvd_right hx _

theorem mem_sqDvdIdeal {h x : A} : x ∈ sqDvdIdeal h ↔ h ∣ x ^ 2 := Iff.rfl

end SquareIdeal

theorem isUnit_mul_sq_of_faithfullyFlat : ∀ (C C' : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing C'] [IsDomain C'] [IsNoetherianRing C'] [IsIntegrallyClosed C'] [Algebra C C'] [Module.FaithfullyFlat C C'] (h : C), h ≠ 0 → (∃ (u : C'ˣ) (f : C'), algebraMap C C' h = u * f ^ 2) → (∀ p : Ideal C, p.IsPrime → p.height = 1 → ∃ a b c : C, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2) → ∃ (u : Cˣ) (a : C), h = u * a ^ 2 := by
  intro C C' _ _ _ _ _ _ _ _ _ _ _ h hh hsq Hp
  obtain ⟨u, f, hf⟩ := hsq
  have hflat : (algebraMap C C').Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let J := sqDvdIdeal h

  have hJf : J.map (algebraMap C C') ≤ Ideal.span {f} := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨z, hz⟩ := mem_sqDvdIdeal.1 hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1
    refine ⟨(u : C') * algebraMap C C' z, ?_⟩
    rw [← map_pow, hz, map_mul, hf]; ring

  have hcol : (Ideal.span {h}).colon (J : Set C) ≤ J := by
    intro y hy
    rw [Submodule.mem_colon] at hy
    apply mem_sqDvdIdeal.2
    apply dvd_of_forall_height_one_exists_dvd_mul hh
    intro P hP h1
    obtain ⟨a, b, c, hb, hc, habc⟩ := Hp P hP h1
    have hac : a * c ∈ J := mem_sqDvdIdeal.2 ⟨b * c, by linear_combination (-c) * habc⟩
    have hy' := hy (a * c) hac
    rw [smul_eq_mul, Ideal.mem_span_singleton] at hy'
    obtain ⟨t, ht⟩ := hy'
    refine ⟨b * c, fun hm => (hP.mem_or_mem hm).elim hb hc, t ^ 2, ?_⟩
    have e : h * (b * c * y ^ 2) = h * (h * t ^ 2) := by
      linear_combination (c * y ^ 2) * habc + (y * (a * c) + h * t) * ht
    exact mul_left_cancel₀ hh e

  have hfJ : f ∈ J.map (algebraMap C C') := by
    have hm : f ∈ ((Ideal.span {h}).colon (J : Set C)).map (algebraMap C C') := by
      rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_span, Set.image_singleton,
        Submodule.mem_colon]
      intro p hp
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 (hJf hp)
      rw [smul_eq_mul, Ideal.mem_span_singleton, hf]
      exact ⟨((u⁻¹ : C'ˣ) : C') * w, by linear_combination (-(f ^ 2 * w)) * u.mul_inv⟩
    exact Ideal.map_mono hcol hm
  have hJeq : J.map (algebraMap C C') = Ideal.span {f} :=
    le_antisymm hJf ((Ideal.span_singleton_le_iff_mem _).2 hfJ)

  have hY : ((J * J).colon (Ideal.span {h} : Set C)).map (algebraMap C C') = ⊤ := by
    rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_mul, hJeq, Ideal.map_span,
      Set.image_singleton, Ideal.span_singleton_mul_span_singleton, Ideal.eq_top_iff_one,
      Submodule.mem_colon]
    intro p hp
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 hp
    rw [smul_eq_mul, _root_.one_mul, Ideal.mem_span_singleton, hf]
    exact ⟨(u : C') * w, by ring⟩
  have hhJJ : h ∈ J * J := by
    have e := Ideal.comap_map_eq_self_of_faithfullyFlat (B := C')
      ((J * J).colon (Ideal.span {h} : Set C))
    rw [hY, Ideal.comap_top] at e
    have h1 : (1 : C) ∈ (J * J).colon (Ideal.span {h} : Set C) := e ▸ Submodule.mem_top
    rw [Submodule.mem_colon] at h1
    simpa using h1 h (Ideal.mem_span_singleton_self h)

  by_contra hne
  have hle : J * J ≤ Ideal.span {h} * maximalIdeal C := by
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨e, he⟩ := dvd_mul_of_dvd_sq_of_dvd_sq (mem_sqDvdIdeal.1 hx) (mem_sqDvdIdeal.1 hy)
    by_cases hem : e ∈ maximalIdeal C
    · rw [he]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self h) hem
    · exfalso
      have heu : IsUnit e := by
        rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hem; exact hem
      obtain ⟨a, ha⟩ := mem_sqDvdIdeal.1 hx
      obtain ⟨b, hb⟩ := mem_sqDvdIdeal.1 hy
      have hab : a * b = e ^ 2 := by
        have e2 : h ^ 2 * (a * b) = h ^ 2 * e ^ 2 := by
          linear_combination (-(h * b)) * ha - x ^ 2 * hb + (x * y + h * e) * he
        exact mul_left_cancel₀ (pow_ne_zero 2 hh) e2
      have hau : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ heu.pow 2)
      exact hne ⟨hau.unit⁻¹, x, by rw [ha]; linear_combination (-h) * hau.val_inv_mul⟩
  obtain ⟨z, hz, hz'⟩ := Ideal.mem_span_singleton_mul.1 (hle hhJJ)
  have hz1 : z = 1 := mul_left_cancel₀ hh (by rw [hz', _root_.mul_one])
  exact (maximalIdeal.isMaximal C).ne_top ((Ideal.eq_top_iff_one _).2 (hz1 ▸ hz))

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace GlobalTheory.RealMultChart

theorem comp_mulN {S : Scheme.{0}} (B : Over S) [GrpObj B] {T : Over S} (x : T ⟶ B) (n : ℕ) :
    x ≫ mulN B n = x ^ n := by
  induction n with
  | zero =>
    show x ≫ (toUnit B ≫ η[B]) = x ^ 0
    rw [pow_zero, Hom.one_def, ← Category.assoc, toUnit_unique (x ≫ toUnit B) (toUnit T)]
  | succ n ih =>
    show x ≫ (lift (mulN B n) (𝟙 B) ≫ μ[B]) = x ^ (n + 1)
    rw [pow_succ, Hom.mul_def, ← ih, ← Category.assoc, comp_lift, Category.comp_id]

theorem mulN_eq_mulA {S : Scheme.{0}} (B : Over S) [GrpObj B] (n : ℕ) : mulN B n = Out.mulA B n := by
  have h1 := comp_mulN B (𝟙 B) n
  rw [Category.id_comp] at h1
  rw [h1]

theorem exists_pow_eq (B : Over (Sp ℂ)) [GrpObj B] (hB : IsAbelianScheme B) (a₀ : 𝟙_ (Over (Sp ℂ)) ⟶ B)
    (n : ℕ) (hn : n ≠ 0) : ∃ b : 𝟙_ (Over (Sp ℂ)) ⟶ B, b ^ n = a₀ := by
  have hn' : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hsurj : Surjective (mulN B n).left := surjective_mulN_of_isAbelianScheme ℂ B hB n hn'
  have hfin : IsFinite (mulN B n).left := by
    rw [mulN_eq_mulA]
    exact MulFiniteAny.isFinite_mulA ℂ B hB n (Nat.one_le_iff_ne_zero.2 hn)
  obtain ⟨t, ht⟩ := H1.SectionDivision.exists_section (pullback.snd (mulN B n).left a₀.left)
  have hb' : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ (mulN B n).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (mulN B n).left a₀.left) ≫ B.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [← Over.w (mulN B n), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  rw [← comp_mulN]
  exact Over.OverMorphism.ext hb'

theorem compactSpace_points (A : Over (Sp ℂ)) (L : LB A.left) (hL : Out.RelAmple A L) :
    @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) (PointsCompact.pointTopology A) := by
  have h1 : PointsCompact.ValueRules := valAt'_rules
  have h2 : PointsCompact.AffinePoints := existsUnique_point_of_ringHom
  obtain ⟨N, -, M, s, hcov, H⟩ := hL ⊤ (isAffineOpen_top _)
  let Y : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  let φ : Y ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι A.hom ⊤).symm
  let c₀ : ℂ →+* Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤) :=
    ((⊤ : (Sp ℂ).Opens).ι.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hc₀ : Function.Surjective c₀ := by
    have : IsIso (⊤ : (Sp ℂ).Opens).ι := inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
  have hY : @CompactSpace _ (PointsCompact.pointTopology Y) := by
    refine PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov fun i => ⟨(H i).1, ?_⟩
    obtain ⟨r, hr, hs⟩ := (H i).2
    refine ⟨r, hr, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom.comp c₀,
      fun a => ?_, fun f => ?_⟩
    · have := Scheme.Hom.comp_appLE (A.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤
        (Out.nonzeroLocus (s i)) le_top
      exact (congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) this).symm
    · obtain ⟨p, rfl⟩ := hs f
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective c₀ hc₀ p
      exact ⟨q, (MvPolynomial.eval₂_map c₀ r _ q).symm⟩
  letI := PointsCompact.pointTopology Y
  letI := PointsCompact.pointTopology A
  have hsurj : Function.Surjective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ Y => x ≫ φ := by
    intro x
    have hrange : Set.range x.left ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
      rw [Scheme.Opens.range_ι]
      intro _ _
      trivial
    have hl := IsOpenImmersion.lift_fac (A.hom ⁻¹ᵁ ⊤).ι x.left hrange
    refine ⟨Over.homMk (IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hrange) ?_, ?_⟩
    · have := Over.w x
      rw [← hl, Category.assoc, ← morphismRestrict_ι] at this
      exact this
    · ext1
      exact hl
  exact hsurj.compactSpace (PointsCompact.continuous_comp h1 φ)

def trivLB (A : Over (Sp ℂ)) : LB A.left := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩


open AbelianExp in
theorem exists_holUnif_of_compact (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hs : SmoothOfRelativeDimension g A.hom)
    (hcpt : @CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) (PointsCompact.pointTopology A))
    (hdiv : ∀ (a : 𝟙_ (Over (Sp ℂ)) ⟶ A) (n : ℕ), n ≠ 0 → ∃ b, b ^ n = a) :
    Nonempty (HolUnif A (trivLB A) g) := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hprod := @holFamily_lift hval
  have hchart := HolChart.exists_holomorphic_chart hval hvalaff exists_holomorphic_section_of_etale
  letI := pointTopology A
  have := isTopologicalGroup_complexPoints hval A
  have : CompactSpace (𝟙_ (Over (Sp ℂ)) ⟶ A) := hcpt
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A g hs 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin g → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x => hdiv x.toMul n hn
  obtain ⟨W', L, hW', h0', hL, hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ))
      (L : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ L W' ∧
      Set.MapsTo L W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (L v) := by
    have ha := hφ.isLocalCommGroupLaw.analyticAt_logChart_symm
    have h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W :=
      ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))
    obtain ⟨W', h2, h3, h4⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)
    exact ⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt,
      fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩
  refine ⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj,
    hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top,
    HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _,
    fun _ _ _ => one_ne_zero, fun i j z hz => ?_⟩⟩
  · have hs : Continuous fun v : Fin g → ℂ => v - z := continuous_sub_right z
    have hWz : IsOpen ((fun v => v - z) ⁻¹' W') := hW'.preimage hs
    refine ⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (L (v - z)), by simpa using h0',
      hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL hLm) hWz
        (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩
    filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv
    rw [← hv, ← toMul_add, ← map_add (f := _), add_sub_cancel]
  · obtain ⟨e, he⟩ := (hval _ _).2.1 _ hz
    rw [he]
    show (1 : ℂ) = e (((1 : Γ(A.left, ⊤ ⊓ ⊤)ˣ)) : Γ(A.left, ⊤ ⊓ ⊤)) * 1
    rw [Units.val_one]
    exact ((_root_.mul_one _).trans e.map_one).symm

end GlobalTheory.RealMultChart

namespace GlobalTheory.RealMult


end GlobalTheory.RealMult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Cell

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section Mat

variable {R : Type} [CommRing R] {m : ℕ}

def IsLowInv (L : Matrix (Fin m) (Fin m) R) : Prop := (∀ i j, i < j → L i j = 0) ∧ ∀ i, IsUnit (L i i)

end Mat

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

end Geo

end GlobalTheory.ShFam.Cell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polAV_g_eq_of_isGrpPullback : ∀ (K : Type) [Field K] (T : Scheme.{0}) (P : PolAV T) (P₀ : PolAV (Sp K)) (f : Sp K ⟶ T) (a : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A f a → P₀.g = P.g := by
  intro K _ T P P₀ f a h
  have h2 : SmoothOfRelativeDimension P.g P₀.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ P₀.smoothDim h2 (eSec P₀.A (default : PrimeSpectrum K))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polAV_dim_eq_of_grpPullback_field : ∀ (K : Type) [Field K] (T : Scheme.{0}) (P : PolAV T) (P₀ : PolAV (Sp K)) (f : Sp K ⟶ T) (a : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A f a → P₀.g = P.g := by
  first | exact @GlobalTheory.polAV_g_eq_of_isGrpPullback | exact GlobalTheory.polAV_g_eq_of_isGrpPullback | (intros; apply GlobalTheory.polAV_g_eq_of_isGrpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersSurjectiveOfRankOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integers_surjective_of_rank_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  first | (exact @GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one) | (exact GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one) | (intros; apply GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one  <;> assumption)
end
