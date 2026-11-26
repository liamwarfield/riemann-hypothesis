module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointHalfLevelLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfLevelSubmodulePermutation
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.SqZeroDiff

variable {R R₀ B B₀ B' : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B]
  [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B']

theorem algHom_mem {I : Ideal R} (φ : B →ₐ[R] B') {b : B} (hb : b ∈ I.map (algebraMap R B)) :
    φ b ∈ I.map (algebraMap R B') := by
  have := Ideal.mem_map_of_mem (φ : B →+* B') hb
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem mul_eq_zero_of_mem {I : Ideal R} (hI : I ^ 2 = 0) {x y : B'} (hx : x ∈ I.map (algebraMap R B'))
    (hy : y ∈ I.map (algebraMap R B')) : x * y = 0 := by
  have := Ideal.mul_mem_mul hx hy
  rw [← pow_two, map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact this

structure Setup (I : Ideal R) (π : R →+* R₀) (p : B →+* B₀) (α : B →ₐ[R] B') : Prop where
  sq : I ^ 2 = 0
  semi : SemiHom π p
  surj : Function.Surjective p
  ker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)

variable {I : Ideal R} {π : R →+* R₀} {p : B →+* B₀} {α : B →ₐ[R] B'}

theorem Setup.sub_mem (h : Setup I π p α) {b c : B} (e : p b = p c) : b - c ∈ I.map (algebraMap R B) :=
  (h.ker _).1 (by rw [map_sub, e, sub_self])

theorem Setup.mul_wd (h : Setup I π p α) {b c : B} (e : p b = p c) {x : B'}
    (hx : x ∈ I.map (algebraMap R B')) : α b * x = α c * x := by
  have := mul_eq_zero_of_mem h.sq (algHom_mem α (h.sub_mem e)) hx
  rwa [map_sub, sub_mul, sub_eq_zero] at this

def J (_h : Setup I π p α) : Type := ↥(I.map (algebraMap R B'))

instance (h : Setup I π p α) : AddCommGroup (J h) :=
  inferInstanceAs (AddCommGroup ↥(I.map (algebraMap R B')))

def J.val {h : Setup I π p α} (x : J h) : B' := Subtype.val (x : ↥(I.map (algebraMap R B')))

theorem J.mem {h : Setup I π p α} (x : J h) : x.val ∈ I.map (algebraMap R B') :=
  Subtype.property (x : ↥(I.map (algebraMap R B')))

def J.mk (h : Setup I π p α) (x : B') (hx : x ∈ I.map (algebraMap R B')) : J h := (⟨x, hx⟩ : ↥(I.map (algebraMap R B')))

theorem J.ext {h : Setup I π p α} {x y : J h} (e : x.val = y.val) : x = y := Subtype.ext e

@[simp] theorem J.val_add {h : Setup I π p α} (x y : J h) : (x + y).val = x.val + y.val := rfl
@[simp] theorem J.val_zero {h : Setup I π p α} : (0 : J h).val = 0 := rfl

def Setup.sec (h : Setup I π p α) : B₀ → B := Function.surjInv h.surj

theorem Setup.p_sec (h : Setup I π p α) (x : B₀) : p (h.sec x) = x := Function.surjInv_eq h.surj x

instance (h : Setup I π p α) : SMul B₀ (J h) :=
  ⟨fun x y ↦ J.mk h (α (h.sec x) * y.val) (Ideal.mul_mem_left _ _ y.mem)⟩

theorem smul_val (h : Setup I π p α) {b : B} {x : B₀} (e : p b = x) (y : J h) :
    (x • y).val = α b * y.val :=
  h.mul_wd (by rw [h.p_sec, e]) y.mem

instance (h : Setup I π p α) : Module B₀ (J h) where
  one_smul y := J.ext (by rw [smul_val h (map_one p), map_one, one_mul])
  mul_smul x z y := J.ext (by
    rw [smul_val h (b := h.sec x * h.sec z) (by rw [map_mul, h.p_sec, h.p_sec]), smul_val h (h.p_sec x),
      smul_val h (h.p_sec z), map_mul, mul_assoc])
  smul_zero x := J.ext (by rw [smul_val h (h.p_sec x), J.val_zero, mul_zero])
  smul_add x y z := J.ext (by rw [smul_val h (h.p_sec x), J.val_add, J.val_add, smul_val h (h.p_sec x),
    smul_val h (h.p_sec x), mul_add])
  add_smul x z y := J.ext (by
    rw [smul_val h (b := h.sec x + h.sec z) (by rw [map_add (f := _), h.p_sec, h.p_sec]), J.val_add, smul_val h (h.p_sec x),
      smul_val h (h.p_sec z), map_add, add_mul])
  zero_smul y := J.ext (by rw [smul_val h (map_zero p), map_zero, zero_mul, J.val_zero])

instance (h : Setup I π p α) : Module R₀ (J h) := Module.compHom (J h) (algebraMap R₀ B₀)

instance (h : Setup I π p α) : IsScalarTower R₀ B₀ (J h) :=
  ⟨fun r x y ↦ by
    change (r • x) • y = (algebraMap R₀ B₀ r) • (x • y)
    rw [Algebra.smul_def, mul_smul]⟩

theorem eq_on_ideal (h : Setup I π p α) (β : B →ₐ[R] B') (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B'))
    {x : B} (hx : x ∈ I.map (algebraMap R B)) : α x = β x := by
  have hx' : x ∈ Submodule.span B (⇑(algebraMap R B) '' (I : Set R)) := hx
  refine Submodule.span_induction (p := fun z _ ↦ α z = β z) ?_ ?_ ?_ ?_ hx'
  · rintro z ⟨r, -, rfl⟩; rw [AlgHom.commutes, AlgHom.commutes]
  · rw [map_zero, map_zero]
  · intro y z _ _ hy hz; rw [map_add (f := _), map_add (f := _), hy, hz]
  · intro c z hzI hz
    have hzI' : z ∈ I.map (algebraMap R B) := hzI
    rw [smul_eq_mul, map_mul, map_mul, hz]
    have := mul_eq_zero_of_mem h.sq (hβ c) (algHom_mem β hzI')
    rwa [sub_mul, sub_eq_zero] at this

theorem diff_wd (h : Setup I π p α) (β : B →ₐ[R] B') (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B'))
    {b c : B} (e : p b = p c) : α b - β b = α c - β c := by
  have := eq_on_ideal h β hβ (h.sub_mem e)
  rw [map_sub, map_sub] at this
  linear_combination this

def dfun (h : Setup I π p α) (β : B →ₐ[R] B') (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) (x : B₀) : J h :=
  J.mk h (α (h.sec x) - β (h.sec x)) (hβ _)

theorem dfun_val (h : Setup I π p α) (β : B →ₐ[R] B') (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B'))
    {b : B} {x : B₀} (e : p b = x) : (dfun h β hβ x).val = α b - β b :=
  diff_wd h β hβ (by rw [h.p_sec, e])

end GlobalTheory.LiftSys.SqZeroDiff

namespace GlobalTheory.LiftSys.SqZeroDiff

variable {R R₀ B B₀ B' : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B]
  [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B']
variable {I : Ideal R} {π : R →+* R₀} {p : B →+* B₀} {α : B →ₐ[R] B'}

def der (h : Setup I π p α) (hπ : Function.Surjective π) (β : B →ₐ[R] B')
    (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) : Derivation R₀ B₀ (J h) :=
  Derivation.mk'
    { toFun := dfun h β hβ
      map_add' x y := by
        obtain ⟨b, rfl⟩ := h.surj x
        obtain ⟨c, rfl⟩ := h.surj y
        refine J.ext ?_
        rw [J.val_add, dfun_val h β hβ (map_add p b c), dfun_val h β hβ rfl, dfun_val h β hβ rfl,
          map_add, map_add]
        ring
      map_smul' r x := by
        obtain ⟨s, rfl⟩ := hπ r
        obtain ⟨b, rfl⟩ := h.surj x
        refine J.ext ?_
        have e : p (algebraMap R B s * b) = π s • p b := by
          rw [map_mul, h.semi.map_algebraMap, Algebra.smul_def]
        change _ = ((algebraMap R₀ B₀ (π s)) • dfun h β hβ (p b)).val
        rw [dfun_val h β hβ e, smul_val h (h.semi.map_algebraMap s), dfun_val h β hβ rfl, map_mul, map_mul,
          AlgHom.commutes, AlgHom.commutes]
        ring }
    (fun x y ↦ by
      obtain ⟨b, rfl⟩ := h.surj x
      obtain ⟨c, rfl⟩ := h.surj y
      refine J.ext ?_
      change (dfun h β hβ _).val = (p b • dfun h β hβ (p c) + p c • dfun h β hβ (p b)).val
      rw [J.val_add, smul_val h rfl, smul_val h rfl, dfun_val h β hβ (map_mul p b c),
        dfun_val h β hβ rfl, dfun_val h β hβ rfl, map_mul, map_mul]
      have := mul_eq_zero_of_mem h.sq (hβ b) (hβ c)
      linear_combination -this)

theorem der_val (h : Setup I π p α) (hπ : Function.Surjective π) (β : B →ₐ[R] B')
    (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) (b : B) : (der h hπ β hβ (p b)).val = α b - β b :=
  dfun_val h β hβ rfl

def theta (h : Setup I π p α) (hπ : Function.Surjective π) (β : B →ₐ[R] B')
    (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) : Ω[B₀⁄R₀] →+ B' where
  toFun w := ((der h hπ β hβ).liftKaehlerDifferential w).val
  map_zero' := by rw [map_zero]; rfl
  map_add' x y := by rw [map_add (f := _)]; rfl

theorem isTheta_theta (h : Setup I π p α) (hπ : Function.Surjective π) (β : B →ₐ[R] B')
    (hβ : ∀ b, α b - β b ∈ I.map (algebraMap R B')) : IsTheta I p α β (theta h hπ β hβ) := by
  refine ⟨?_, ?_, fun w ↦ J.mem _⟩
  · intro b w
    change ((der h hπ β hβ).liftKaehlerDifferential (p b • w)).val = _
    rw [LinearMap.map_smul, smul_val h rfl]; rfl
  · intro b
    change ((der h hπ β hβ).liftKaehlerDifferential (D R₀ B₀ (p b))).val = _
    rw [Derivation.liftKaehlerDifferential_comp_D, der_val]

theorem theta_unique (h : Setup I π p α) {β : B →ₐ[R] B'} {θ₁ θ₂ : Ω[B₀⁄R₀] →+ B'}
    (h₁ : IsTheta I p α β θ₁) (h₂ : IsTheta I p α β θ₂) : θ₁ = θ₂ := by
  ext w
  have hw : w ∈ Submodule.span B₀ (Set.range (D R₀ B₀)) := by
    rw [span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun z _ ↦ θ₁ z = θ₂ z) ?_ ?_ ?_ ?_ hw
  · rintro z ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := h.surj y
    rw [h₁.der, h₂.der]
  · rw [map_zero, map_zero]
  · intro y z _ _ hy hz; rw [map_add (f := _), map_add (f := _), hy, hz]
  · intro c z _ hz
    obtain ⟨b, rfl⟩ := h.surj c
    rw [h₁.smul, h₂.smul, hz]

def betaOf (h : Setup I π p α) (θ : Ω[B₀⁄R₀] →+ B') (hs : ∀ b w, θ (p b • w) = α b * θ w)
    (hm : ∀ w, θ w ∈ I.map (algebraMap R B')) : B →ₐ[R] B' where
  toFun b := α b - θ (D R₀ B₀ (p b))
  map_one' := by rw [map_one, map_one, Derivation.map_one_eq_zero, map_zero, sub_zero]
  map_mul' b c := by
    rw [map_mul, map_mul, Derivation.leibniz, map_add (f := _), hs, hs]
    have := mul_eq_zero_of_mem h.sq (hm (D R₀ B₀ (p b))) (hm (D R₀ B₀ (p c)))
    linear_combination -this
  map_zero' := by rw [map_zero, map_zero, map_zero, map_zero, sub_zero]
  map_add' b c := by
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    ring
  commutes' r := by
    rw [AlgHom.commutes, h.semi.map_algebraMap, Derivation.map_algebraMap, map_zero, sub_zero]

theorem isTheta_betaOf (h : Setup I π p α) (θ : Ω[B₀⁄R₀] →+ B') (hs : ∀ b w, θ (p b • w) = α b * θ w)
    (hm : ∀ w, θ w ∈ I.map (algebraMap R B')) : IsTheta I p α (betaOf h θ hs hm) θ := by
  refine ⟨hs, ?_, hm⟩
  intro b
  change _ = α b - (α b - θ (D R₀ B₀ (p b)))
  ring

end GlobalTheory.LiftSys.SqZeroDiff

namespace GlobalTheory.LiftSys

theorem theta_classify : ∀ (R R₀ B B₀ B' : Type) [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B]
    [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] (I : Ideal R), I ^ 2 = 0 →
    ∀ (π : R →+* R₀), Function.Surjective π → ∀ p : B →+* B₀, SemiHom π p → Function.Surjective p →
    (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) → ∀ α : B →ₐ[R] B',
    (∀ β : B →ₐ[R] B', (∀ b, α b - β b ∈ I.map (algebraMap R B')) → ∃! θ : Ω[B₀⁄R₀] →+ B', IsTheta I p α β θ) ∧
    ∀ θ : Ω[B₀⁄R₀] →+ B', (∀ b w, θ (p b • w) = α b * θ w) → (∀ w, θ w ∈ I.map (algebraMap R B')) →
      ∃ β : B →ₐ[R] B', IsTheta I p α β θ := by
  intro R R₀ B B₀ B' _ _ _ _ _ _ _ _ I hI π hπ p hp hs hk α
  have h : SqZeroDiff.Setup I π p α := ⟨hI, hp, hs, hk⟩
  refine ⟨fun β hβ ↦ ⟨SqZeroDiff.theta h hπ β hβ, SqZeroDiff.isTheta_theta h hπ β hβ,
    fun θ hθ ↦ SqZeroDiff.theta_unique h hθ (SqZeroDiff.isTheta_theta h hπ β hβ)⟩,
    fun θ hθs hθm ↦ ⟨SqZeroDiff.betaOf h θ hθs hθm, SqZeroDiff.isTheta_betaOf h θ hθs hθm⟩⟩

end GlobalTheory.LiftSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentialsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials : ∀ (R R₀ B B₀ B' : Type) [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] (I : Ideal R), I ^ 2 = 0 → ∀ (π : R →+* R₀), Function.Surjective π → ∀ p : B →+* B₀, SemiHom π p → Function.Surjective p → (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) → ∀ α : B →ₐ[R] B', (∀ β : B →ₐ[R] B', (∀ b, α b - β b ∈ I.map (algebraMap R B')) → ∃! θ : Ω[B₀⁄R₀] →+ B', IsTheta I p α β θ) ∧ ∀ θ : Ω[B₀⁄R₀] →+ B', (∀ b w, θ (p b • w) = α b * θ w) → (∀ w, θ w ∈ I.map (algebraMap R B')) → ∃ β : B →ₐ[R] B', IsTheta I p α β θ := by
  first | exact @GlobalTheory.LiftSys.theta_classify | exact GlobalTheory.LiftSys.theta_classify | (intros; apply GlobalTheory.LiftSys.theta_classify <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupRepresentationTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceTwistedComplexificatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceTwistedComplexificatio
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.DefRead

theorem bcLin_sub_smul_apply {K W : Type} [Field K] [AddCommGroup W] [Module K W] (σ : K →+* ℂ)
    (f : W →ₗ[K] W) (a : K) (v : VC σ W) :
    bcLin σ (f - a • LinearMap.id) v = bcLin σ f v - σ a • v := by
  letI : Algebra K ℂ := σ.toAlgebra
  revert v
  show ∀ v : ℂ ⊗[K] W, LinearMap.baseChange ℂ (f - a • LinearMap.id) v = LinearMap.baseChange ℂ f v - σ a • v
  intro v
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  congr 1

theorem bcLin_sum_smul {K W G : Type} [Field K] [AddCommGroup W] [Module K W] [Fintype G] (σ : K →+* ℂ)
    (f : G → W →ₗ[K] W) (a : G → K) :
    bcLin σ (∑ g, a g • f g) = ∑ g, σ (a g) • bcLin σ (f g) := by
  letI : Algebra K ℂ := σ.toAlgebra
  show LinearMap.baseChangeHom K ℂ W W (∑ g, a g • f g) = ∑ g, σ (a g) • LinearMap.baseChange ℂ (f g)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  show LinearMap.baseChange ℂ (a g • f g) = _
  rw [LinearMap.baseChange_smul]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, ← algebraMap_smul ℂ (a g)]
  rfl

end GlobalTheory.DefRead

namespace GlobalTheory.DefRead

theorem finrank_eig_twBC : ∀ (K W G : Type) [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Group G] [Fintype G]
    (σ : K →+* ℂ) (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) (J : Subgroup G) (μ : J →* Kˣ) (c : G → K),
    Module.finrank K (⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ)) ∧
    Module.finrank K ((⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id)) ⊓
        LinearMap.ker (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) ⊓
        LinearMap.ker (Representation.asAlgebraHom (GlobalTheory.DefRead.twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g)))) :
          Submodule ℂ (GlobalTheory.DefRead.VC σ W)) := by
  intro K W G _ _ _ _ _ _ σ ρ0 χ J μ c
  letI : Algebra K ℂ := σ.toAlgebra
  set a : J → W →ₗ[K] W := fun p => ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id with ha
  have hker : ∀ p : J, LinearMap.ker (twBC σ ρ0 χ (p : G) -
      ((((Units.map σ.toMonoidHom).comp μ) p : ℂˣ) : ℂ) • LinearMap.id) = LinearMap.ker (bcLin σ (a p)) := by
    intro p
    ext v
    have hμ : ((((Units.map σ.toMonoidHom).comp μ) p : ℂˣ) : ℂ) = σ (μ p) := rfl
    have hu : σ (((χ p)⁻¹ : Kˣ) : K) * σ ((χ p * μ p : Kˣ) : K) = σ (μ p) := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel_left]
    have hu0 : σ (((χ p)⁻¹ : Kˣ) : K) ≠ 0 := (map_ne_zero σ).2 (Units.ne_zero _)
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ha, bcLin_sub_smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, twBC_apply, LinearMap.smul_apply, hμ, ← hu, ← smul_smul, ← smul_sub, smul_eq_zero,
      or_iff_right hu0]
  have heig : eig (twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) = ⨅ p : J, LinearMap.ker (bcLin σ (a p)) :=
    iInf_congr hker
  have halg : Representation.asAlgebraHom (twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g))) =
      bcLin σ (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, bcLin_sum_smul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.asAlgebraHom_single, twBC_apply, smul_smul, map_mul]
  have hbc := TensorProduct.isBaseChange K W ℂ
  have h1 := finrank_iInf_ker_baseChange K ℂ W (ℂ ⊗[K] W) J (TensorProduct.mk K ℂ W 1) hbc a
    (fun p => (bcLin σ (a p) : ℂ ⊗[K] W →ₗ[ℂ] ℂ ⊗[K] W)) (fun p v => complexificationBaseChangeLinear_one_tmul σ (a p) v)
  set b : Option J → W →ₗ[K] W := fun o => o.elim (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) a with hb
  have h2 := finrank_iInf_ker_baseChange K ℂ W (ℂ ⊗[K] W) (Option J) (TensorProduct.mk K ℂ W 1) hbc b
    (fun o => (bcLin σ (b o) : ℂ ⊗[K] W →ₗ[ℂ] ℂ ⊗[K] W)) (fun o v => complexificationBaseChangeLinear_one_tmul σ (b o) v)
  rw [iInf_option, iInf_option] at h2
  refine ⟨?_, ?_⟩
  · rw [heig]
    exact h1.1.symm
  · rw [heig, halg, inf_comm]
    conv_rhs => rw [inf_comm]
    exact h2.1.symm

end GlobalTheory.DefRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceTwistedComplexificatioStatement
open GlobalTheory.BadCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_characterEigenspace_twistedComplexification : ∀ (K W G : Type) [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Group G] [Fintype G]
    (σ : K →+* ℂ) (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) (J : Subgroup G) (μ : J →* Kˣ) (c : G → K),
    Module.finrank K (⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ)) ∧
    Module.finrank K ((⨅ p : J, LinearMap.ker (ρ0 p - ((χ p * μ p : Kˣ) : K) • LinearMap.id)) ⊓
        LinearMap.ker (∑ g, (c g * ((χ g)⁻¹ : Kˣ)) • ρ0 g) : Submodule K W) =
      Module.finrank ℂ (eig (GlobalTheory.DefRead.twBC σ ρ0 χ) J ((Units.map σ.toMonoidHom).comp μ) ⊓
        LinearMap.ker (Representation.asAlgebraHom (GlobalTheory.DefRead.twBC σ ρ0 χ) (∑ g, MonoidAlgebra.single g (σ (c g)))) :
          Submodule ℂ (GlobalTheory.DefRead.VC σ W)) := by
  first | exact @GlobalTheory.DefRead.finrank_eig_twBC | exact GlobalTheory.DefRead.finrank_eig_twBC | (intros; apply GlobalTheory.DefRead.finrank_eig_twBC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormsSpanInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroSmulMemSpan
namespace GlobalTheory.NonzeroMultipleInSpan

open NumberField

theorem exists_ne_zero_smul_mem_span {LL : Type} [Field LL] [NumberField LL] {n : ℕ}
    (T : Set (Fin n → LL)) :
    ∀ x ∈ Submodule.span LL T, ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm b a]
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ b hay) (Submodule.smul_mem _ a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 LL)) c
    refine ⟨(q : 𝓞 LL) * a, mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩
    have h : ((q : 𝓞 LL) * a) • (c • y) = p • (a • y) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      simp only at hpq
      rw [← hpq]
      ring
    rw [h]
    exact Submodule.smul_mem _ p hay

end GlobalTheory.NonzeroMultipleInSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormsSpanInvariant
open NumberField

namespace GlobalTheory.IntFormsRank

variable {LL : Type} [Field LL] [NumberField LL] {n : ℕ}

theorem smul_eq_algebraMap_smul (r : 𝓞 LL) (z : Fin n → LL) : r • z = (algebraMap (𝓞 LL) LL r) • z :=
  (algebraMap_smul LL r z).symm

theorem exists_den_smul_mem (T : Set (Fin n → LL)) (x : Fin n → LL) (hx : x ∈ Submodule.span LL T) :
    ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  first
  | exact @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | (apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span ..)

theorem span_inf_eq (T : Set (Fin n → LL)) (hT : Submodule.span LL T = ⊤) (S : Submodule LL (Fin n → LL)) :
    Submodule.span LL ((Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) :
      Set (Fin n → LL)) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    have hxT : x ∈ Submodule.span LL T := by rw [hT]; exact Submodule.mem_top
    obtain ⟨d, hd, hdx⟩ := exists_den_smul_mem T x hxT
    have hdL : algebraMap (𝓞 LL) LL d ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 LL) LL)]; exact hd
    have hmem : d • x ∈ (Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) := by
      refine ⟨hdx, ?_⟩
      show d • x ∈ S
      rw [smul_eq_algebraMap_smul]; exact S.smul_mem _ hx
    have hx' : x = (algebraMap (𝓞 LL) LL d)⁻¹ • (d • x) := by
      rw [smul_eq_algebraMap_smul, smul_smul, inv_mul_cancel₀ hdL, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.IntFormsRank

theorem GlobalTheory.IntFormsRank.rkK_Mall : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  intro LL Ks _ _ _ _ _ n Wσ _ _ G0 _ _ A J0 lam0 f hsp
  constructor
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    rw [GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    have e : (Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓ (A.typeP J0 lam0).restrictScalars (𝓞 LL) ⊓
        (LinearMap.ker f).restrictScalars (𝓞 LL)) =
        Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓
          (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)).restrictScalars (𝓞 LL) := by
      rw [inf_assoc]; rfl
    rw [e, GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormsSpanInvariantStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_forms_span_invariant : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  first | exact @GlobalTheory.IntFormsRank.rkK_Mall | exact GlobalTheory.IntFormsRank.rkK_Mall | (intros; apply GlobalTheory.IntFormsRank.rkK_Mall <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.DefRead

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem typeSubspace_eq_iInf_ker {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] {n : ℕ}
    {Wσ : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) :
    A.typeP J0 lam0 = ⨅ p : J0, LinearMap.ker (A.ρ p - ((A.chi p * lam0 p : LLˣ) : LL) • LinearMap.id) := by
  ext F
  simp [Formalism.IndefR.Arith.FormsL.mem_typeP, Submodule.mem_iInf, sub_eq_zero]


end GlobalTheory.DefRead

namespace GlobalTheory.DefRead


end GlobalTheory.DefRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MulEqOneOfComb
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.RealCompare
open GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds hiding fn PsiNorm
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem one_le_rN (S : ThetaSys o Ω) : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)

end GlobalTheory.RealCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_qkPt_of_utest : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : S.Gam), ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left := by
  intro o Ω _ _ _ S ρ p _ y₀ u a
  haveI : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  obtain ⟨x, hx, hadd, -⟩ := utest_torsion_points o Ω S ρ p y₀ u
  obtain ⟨f, f₁, f₂, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) _ (GlobalTheory.RealCompare.one_le_rN S)
  have hx1 : x a ^ (S.r * S.N) = 1 := by
    have := u.A.isAb.comm
    obtain ⟨h0, hsm⟩ := ThetaReal.pt_nsmul x hadd
    rw [← hsm, ThetaReal.nsmul_self, h0]
  obtain ⟨q, hq⟩ := f₂ _ hx1
  exact ⟨q, x a, (f₁ _ _).2 hq.symm, hx a⟩

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaTorsion_preimage_uniformised_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : S.Gam), ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left := by
  first | exact @GlobalTheory.Poinc.exists_qkPt_of_utest | exact GlobalTheory.Poinc.exists_qkPt_of_utest | (intros; apply GlobalTheory.Poinc.exists_qkPt_of_utest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearLiftOfProjective
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_semilinear_lift_of_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (P : Type) [AddCommGroup P] [Module R₀ P], Module.Projective R₀ P → ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (W : Submodule R M), (∀ r, π r = 0 → ∀ m ∈ W, r • m = 0) → ∀ (q : M →ₗ[R] M') (v : P →+ M'), (∀ r w, v (π r • w) = r • v w) → (∀ w, ∃ m ∈ W, q m = v w) → ∃ u : P →+ M, (∀ r w, u (π r • w) = r • u w) ∧ (∀ w, u w ∈ W) ∧ ∀ w, q (u w) = v w := by
  intro R R₀ _ _ π hπ P _ _ hP M M' _ _ _ _ W hW q v hv hq
  classical
  choose m hmW hmq using hq
  choose σ hσ using hπ
  have key : ∀ (r s : R) (x : M), x ∈ W → π r = π s → r • x = s • x := by
    intro r s x hx h
    have := hW (r - s) (by rw [map_sub, h, sub_self]) x hx
    rwa [sub_smul, sub_eq_zero] at this
  let f : P → R₀ →+ M := fun w => AddMonoidHom.mk' (fun c => σ c • m w) (by
    intro a b
    rw [← add_smul]
    exact key _ _ _ (hmW w) (by rw [map_add (f := _), hσ, hσ, hσ]))
  have hf : ∀ w c, f w c = σ c • m w := fun _ _ => rfl
  let g : (P →₀ R₀) →+ M := Finsupp.liftAddHom f
  have hg : ∀ w c, g (Finsupp.single w c) = σ c • m w := by
    intro w c
    simp only [g, Finsupp.liftAddHom_apply_single, hf]
  have g1 : ∀ r x, g (π r • x) = r • g x := by
    intro r x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]
    | single w c =>
      rw [Finsupp.smul_single, hg, hg, smul_smul]
      exact key _ _ _ (hmW w) (by rw [map_mul, hσ, hσ, smul_eq_mul])
  have g2 : ∀ x, g x ∈ W := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _)]; exact W.add_mem ha hb
    | single w c => rw [hg]; exact W.smul_mem _ (hmW w)
  have g3 : ∀ x, q (g x) = v (Finsupp.linearCombination R₀ id x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single w c =>
      rw [hg, Finsupp.linearCombination_single, map_smul, hmq, ← hv, hσ]
      rfl
  obtain ⟨s, hs⟩ := hP.out
  refine ⟨g.comp s.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro r w
    show g (s (π r • w)) = r • g (s w)
    rw [map_smul, g1]
  · intro w
    exact g2 _
  · intro w
    show q (g (s w)) = v w
    rw [g3, hs]

end GlobalTheory.LiftSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLAlgebraMap
noncomputable section
set_option autoImplicit false

namespace GlobalTheory.LogDerProj

def logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) :
    Submodule A (Derivation ℤ A A) where
  carrier := {D | (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J}
  zero_mem' := ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  add_mem' := fun {D D'} h h' =>
    ⟨fun a => by simp [h.1 a, h'.1 a], fun g hg => add_mem (h.2 g hg) (h'.2 g hg)⟩
  smul_mem' := fun r D h =>
    ⟨fun a => by simp [h.1 a], fun g hg => Ideal.mul_mem_left _ r (h.2 g hg)⟩

theorem mem_logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) (D : Derivation ℤ A A) :
    D ∈ logSub φ J ↔ (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J := Iff.rfl

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S]
include f

def ext (D : Derivation ℤ R R) : Derivation ℤ S S :=
  Classical.choose (GlobalTheory.LogDerLoc.exists_extension (B := S) f D)

theorem ext_algebraMap (D : Derivation ℤ R R) (r : R) :
    ext (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  Classical.choose_spec (GlobalTheory.LogDerLoc.exists_extension (B := S) f D) r

theorem der_ext (D₁ D₂ : Derivation ℤ S S) (h : ∀ r, D₁ (algebraMap R S r) = D₂ (algebraMap R S r)) :
    D₁ = D₂ := by
  ext y
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) y
  have hu : IsUnit (algebraMap R S t) := IsLocalization.map_units S t
  have e' : y * algebraMap R S t = algebraMap R S r := e
  have h1 := congrArg D₁ e'
  have h2 := congrArg D₂ e'
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [h r, h t] at h1
  have : algebraMap R S t * D₁ y = algebraMap R S t * D₂ y := by linear_combination h1 - h2
  exact hu.mul_left_cancel this

def extL : Derivation ℤ R R →ₗ[R] Derivation ℤ S S where
  toFun := ext f
  map_add' D D' := der_ext f _ _ fun r => by
    rw [ext_algebraMap, Derivation.add_apply, Derivation.add_apply, ext_algebraMap, ext_algebraMap, map_add (f := _)]
  map_smul' c D := der_ext f _ _ fun r => by
    rw [ext_algebraMap, RingHom.id_apply, Derivation.smul_apply, Derivation.smul_apply, ext_algebraMap,
      smul_eq_mul, map_mul, Algebra.smul_def]

theorem extL_algebraMap (D : Derivation ℤ R R) (r : R) :
    extL (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  ext_algebraMap f D r

variable {k : Type} [CommRing k]

def res (φ : k →+* R) (J : Ideal R) :
    logSub φ J →ₗ[R] (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R where
  toFun D := ⟨extL f D.1, fun a => by
      rw [RingHom.comp_apply, extL_algebraMap, D.2.1 a, map_zero],
    GlobalTheory.LogDerLoc.map_mem_map (algebraMap R S) D.1 (extL f D.1) (extL_algebraMap f D.1) J D.2.2⟩
  map_add' D D' := Subtype.ext (map_add (extL (S := S) f) D.1 D'.1)
  map_smul' c D := Subtype.ext (map_smul (extL (S := S) f) c D.1)

theorem res_apply (φ : k →+* R) (J : Ideal R) (D : logSub φ J) (r : R) :
    (res (S := S) f φ J D).1 (algebraMap R S r) = algebraMap R S (D.1 r) :=
  ext_algebraMap f D.1 r

end GlobalTheory.LogDerProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRationalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRationalPoints
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ModelChangeTo

theorem change_to_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (M₁ : Model σ X W) (om₁ : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c₀ : ℂ),
      M₁.co = co ∧ IsPair B M₁ χX χW om₁ r s r' s' ∧ c₀ ≠ 0 ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d) ∧ thetaSum F (e Φ) = c₀ * thetaSum F Φ ∧
        ∀ x, e (om x Φ) = om₁ x (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair co hco
  obtain ⟨e, ei, ev, hei, hmaps, hheis, hSB, hvac, hstd, hpure, hbij⟩ :=
    GlobalTheory.T.darboux_coords_good_model F E σ B n d X W M r s r' s' hpair.base hpair.herm hpair.skew hpair.good co hco
  let M₁ : Model σ X W := ⟨co, fun v => ev v (M.vac v), M.μ, M.dom⟩
  have hM₁ : M₁.IsGood B.ψ := ⟨hco, hvac, hstd, hpair.good.haar, hpair.good.dom⟩
  have hne : ∃ f : SInf F (Fin n × Fin d), f ≠ 0 := by
    by_contra hall
    push_neg at hall
    obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
    have hle : schA F (Fin n × Fin d) ≤ ⊥ := by
      refine Submodule.span_le.2 ?_
      rintro Φ ⟨f, g, -, rfl⟩
      rw [hall f]
      show pureA F 0 g = 0
      funext x
      simp [pureA]
    have h0 : φ = 0 := (Submodule.mem_bot ℂ).1 (hle hφ)
    exact hθ (by rw [h0]; simp [thetaSum])
  have hev : IsEv B M M₁ 1 1 ∅ e := by
    refine ⟨hmaps, fun z Φ hΦ => ?_, fun u hu => hu.elim, ei, ev, ?_, fun v => ⟨rfl, hSB v⟩, hpure⟩
    · have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      exact hheis z Φ hΦ
    · obtain ⟨f, hf⟩ := hne
      obtain ⟨g, rfl⟩ := hei f
      intro h
      exact hf (by rw [h]; rfl)
  obtain ⟨om₁, hW, hint⟩ := GlobalTheory.T.weil_eigen_bijective_schwartz F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨c₀, hc₀, hth⟩ := GlobalTheory.T.weil_eigen_schwartz_surjective F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  exact ⟨M₁, om₁, e, c₀, rfl, ⟨hpair.base, hpair.herm, hpair.skew, hM₁, hpair.hX, hpair.hW, hpair.resX, hpair.resW, hW⟩,
    hc₀, fun Φ hΦ => ⟨hmaps Φ hΦ, hth Φ hΦ, fun x => hint x Φ hΦ⟩⟩

end GlobalTheory.ModelChangeTo

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRationalPointsStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_coords_rational_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (M₁ : Model σ X W) (om₁ : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c₀ : ℂ),
      M₁.co = co ∧ IsPair B M₁ χX χW om₁ r s r' s' ∧ c₀ ≠ 0 ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d) ∧ thetaSum F (e Φ) = c₀ * thetaSum F Φ ∧
        ∀ x, e (om x Φ) = om₁ x (e Φ) := by
  first | exact @GlobalTheory.ModelChangeTo.change_to_coordinates | exact GlobalTheory.ModelChangeTo.change_to_coordinates | (intros; apply GlobalTheory.ModelChangeTo.change_to_coordinates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOfBijectiveLiftSemi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecEquivResM
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AffGlue

structure Data (T : Scheme.{0}) where

  M : ∀ V : T.Opens, IsAffineOpen V → Type

  grp : ∀ V hV, AddCommGroup (M V hV)

  mod : ∀ V hV, Module Γ(T, V) (M V hV)

  ρ : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V'), V' ≤ V → M V hV →+ M V' hV'
  ρ_smul : ∀ {V V' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (a : Γ(T, V)) (m : M V hV), ρ hV hV' h (a • m) = resG T h a • ρ hV hV' h m
  ρ_self : ∀ {V : T.Opens} (hV : IsAffineOpen V) (h : V ≤ V) (m : M V hV), ρ hV hV h m = m
  ρ_ρ : ∀ {V V' V'' : T.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hV'' : IsAffineOpen V'') (h : V' ≤ V) (h' : V'' ≤ V') (m : M V hV),
    ρ hV' hV'' h' (ρ hV hV' h m) = ρ hV hV'' (h'.trans h) m

  loc_surj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (m : M (T.basicOpen f) hD), ∃ (n : ℕ) (x : M V hV),
      resG T (T.basicOpen_le f) f ^ n • m = ρ hV hD (T.basicOpen_le f) x

  loc_inj : ∀ {V : T.Opens} (hV : IsAffineOpen V) (f : Γ(T, V)) (hD : IsAffineOpen (T.basicOpen f))
    (x : M V hV), ρ hV hD (T.basicOpen_le f) x = 0 → ∃ n : ℕ, f ^ n • x = 0

attribute [instance] Data.grp Data.mod

variable {T : Scheme.{0}} (D : Data T)

variable {D}

end GlobalTheory.AffGlue
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

section Data

variable {A} (H : GlobalTheory.Published.AbelianDeRham) {g : ℕ} (hA : IsAbelianScheme A)
  (hg : SmoothOfRelativeDimension g A.hom)

include hA in
theorem isAbelianScheme_onAff {V : T.Opens} (hV : IsAffineOpen V) : IsAbelianScheme (onAff A hV) :=
  isAbelianScheme_pullback_obj hV.fromSpec A hA



end Data

end GlobalTheory.DeRhamSheaf

namespace GlobalTheory.AffGlue

variable {T : Scheme.{0}}

end GlobalTheory.AffGlue

namespace GlobalTheory.DeRhamSheaf

end GlobalTheory.DeRhamSheaf
end
end
