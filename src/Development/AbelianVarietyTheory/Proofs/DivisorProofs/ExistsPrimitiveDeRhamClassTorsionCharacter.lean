module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAdditionTwoPointFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionMulDifference
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecMul

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (f : T' ⟶ T)
    (x : T ⟶ A) (n : ℕ) : f ≫ x ^ n = (f ≫ x) ^ n :=
  MonObj.comp_pow x n f

end GlobalTheory.SecMul

namespace GlobalTheory

theorem sec_mul_diff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D)
    (s s' s'' : RootFn A D), IsSec n b x s → IsSec n b y s' → IsSec n b (x * y) s'' → ∃! e : D,
    ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → s'' D' φ (z * w) - s D' φ z - s' D' φ w = φ e := by
  intro R _ A _ _ n hR b hb D _ _ x y s s' s'' hs hs' hs''
  have hroot : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (p : Pt A D) (z : Pt A E), z ^ n = spOver φ ≫ p →
      (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ p := by
    intro E _ _ E' _ _ φ ψ p z hz
    rw [← SecMul.comp_pow_pt, hz, ← Category.assoc, spOver_comp]
  have hmul : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z w : Pt A E), z ^ n = spOver φ ≫ x →
      w ^ n = spOver φ ≫ y → (z * w) ^ n = spOver φ ≫ (x * y) := by
    intro E _ _ φ z w hz hw
    rw [mul_pow, hz, hw, comp_mul]
  have hinv : ∀ (E : Type) [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (z z' w w' : Pt A E),
      z ^ n = spOver φ ≫ x → z' ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y → w' ^ n = spOver φ ≫ y →
      s'' E φ (z' * w') - s E φ z' - s' E φ w' = s'' E φ (z * w) - s E φ z - s' E φ w := by
    intro E _ _ φ z z' w w' hz hz' hw hw'
    obtain ⟨t, rfl⟩ : ∃ t, z' = z * t := ⟨z⁻¹ * z', (mul_inv_cancel_left z z').symm⟩
    obtain ⟨u, rfl⟩ : ∃ u, w' = w * u := ⟨w⁻¹ * w', (mul_inv_cancel_left w w').symm⟩
    have ht : t ^ n = 1 := by rw [mul_pow, hz] at hz'; exact mul_eq_left.mp hz'
    have hu : u ^ n = 1 := by rw [mul_pow, hw] at hw'; exact mul_eq_left.mp hw'
    rw [_root_.mul_mul_mul_comm, hs''.2 E φ _ _ (hmul E φ z w hz hw) (by rw [mul_pow, ht, hu, _root_.one_mul]),
      hb.2 E t u ht hu, hs.2 E φ z t hz ht, hs'.2 E φ w u hw hu]
    ring
  have hnat : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (φ : D →ₐ[R] E)
      (ψ : E →ₐ[R] E') (z w : Pt A E), z ^ n = spOver φ ≫ x → w ^ n = spOver φ ≫ y →
      s'' E' (ψ.comp φ) (spOver ψ ≫ z * spOver ψ ≫ w) - s E' (ψ.comp φ) (spOver ψ ≫ z) -
        s' E' (ψ.comp φ) (spOver ψ ≫ w) = ψ (s'' E φ (z * w) - s E φ z - s' E φ w) := by
    intro E _ _ E' _ _ φ ψ z w hz hw
    rw [← comp_mul, hs''.1 E E' φ ψ _ (hmul E φ z w hz hw), hs.1 E E' φ ψ z hz, hs'.1 E E' φ ψ w hw,
      map_sub, map_sub]
  obtain ⟨D2, _, _, ψ, z0, w0, hf, hz0, hw0⟩ : ∃ (D2 : Type) (_ : CommRing D2) (_ : Algebra R D2)
      (ψ : D →ₐ[R] D2) (z0 w0 : Pt A D2), (ψ : D →+* D2).FaithfullyFlat ∧ z0 ^ n = spOver ψ ≫ x ∧
      w0 ^ n = spOver ψ ≫ y := by
    obtain ⟨D1, _, _, ψ1, z1, hf1, hz1⟩ := hR D x
    obtain ⟨D2, _, _, ψ2, w2, hf2, hw2⟩ := hR D1 (spOver ψ1 ≫ y)
    refine ⟨D2, inferInstance, inferInstance, ψ2.comp ψ1, spOver ψ2 ≫ z1, w2,
      RingHom.FaithfullyFlat.stableUnderComposition ψ1.toRingHom ψ2.toRingHom hf1 hf2,
      hroot D1 D2 ψ1 ψ2 x z1 hz1, ?_⟩
    rw [hw2, ← Category.assoc, spOver_comp]
  have hinjψ : Function.Injective ψ := RingHom.FaithfullyFlat.injective hf
  obtain ⟨e, he, -⟩ := ff_descent_pairs R D D2 ψ hf
    (s'' D2 ψ (z0 * w0) - s D2 ψ z0 - s' D2 ψ w0) (fun E _ _ α β hαβ ↦ by
      rw [← hnat D2 E ψ α z0 w0 hz0 hw0, ← hnat D2 E ψ β z0 w0 hz0 hw0]
      have h1 := hroot D2 E ψ α x z0 hz0
      have h2 := hroot D2 E ψ α y w0 hw0
      rw [hαβ] at h1 h2 ⊢
      exact hinv E (β.comp ψ) _ _ _ _ (hroot D2 E ψ β x z0 hz0) h1 (hroot D2 E ψ β y w0 hw0) h2)
  refine ⟨e, fun E _ _ φ z w hz hw ↦ ?_, fun e' he' ↦ hinjψ ((he' D2 ψ z0 w0 hz0 hw0).symm.trans he.symm)⟩
  obtain ⟨E', _, _, ψ', φ', hf', hcomm⟩ := exists_pushout_faithfullyFlat R D D2 E ψ φ hf
  apply RingHom.FaithfullyFlat.injective hf'
  have hR2 : ψ' (φ e) = s'' E' (φ'.comp ψ) (spOver φ' ≫ z0 * spOver φ' ≫ w0) - s E' (φ'.comp ψ) (spOver φ' ≫ z0) -
      s' E' (φ'.comp ψ) (spOver φ' ≫ w0) := by
    rw [hnat D2 E' ψ φ' z0 w0 hz0 hw0, ← he]
    change (ψ'.comp φ) e = (φ'.comp ψ) e
    rw [hcomm]
  change ψ' (s'' E φ (z * w) - s E φ z - s' E φ w) = ψ' (φ e)
  rw [← hnat E E' φ ψ' z w hz hw, hR2]
  have h1 := hroot E E' φ ψ' x z hz
  have h2 := hroot E E' φ ψ' y w hw
  rw [hcomm] at h1 h2 ⊢
  exact hinv E' (φ'.comp ψ) _ _ _ _ (hroot D2 E' ψ φ' x z0 hz0) h1 (hroot D2 E' ψ φ' y w0 hw0) h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAdditionTwoPointFunction
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_isSecAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∃ g : Fn2 A, IsSecAdd n S g := by
  intro R _ A _ _ n hr b hb S hS
  have difference (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) :=
    (GlobalTheory.sec_mul_diff R A n hr b hb D x y (S D x) (S D y) (S D (x * y))
      (hS D x) (hS D y) (hS D (x * y))).exists
  refine ⟨fun D _ _ x y ↦ (difference D x y).choose, ?_⟩
  intro D _ _ x y E _ _ ψ z w hz hw
  exact ((difference D x y).choose_spec E ψ z w hz hw).symm

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAdditionTwoPointFunctionStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_sectionAddition_two_point_function :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
        (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) →
        ∃ g : Fn2 A, IsSecAdd n S g :=
  @GlobalTheory.PtExt.exists_isSecAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDifferenceOneCochain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePushoutTorsorSectionDifference
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem isSec_sub_root_eq {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (z z' : Pt A D') (hz : z ^ n = spOver φ ≫ x) (hz' : z' ^ n = spOver φ ≫ x) :
    s D' φ z' - s' D' φ z' = s D' φ z - s' D' φ z := by
  have hw : (z⁻¹ * z') ^ n = 1 := by rw [mul_pow, inv_pow, hz, hz', inv_mul_cancel]
  have e : z' = z * (z⁻¹ * z') := (mul_inv_cancel_left z z').symm
  rw [e, hs.2 D' φ z _ hz hw, hs'.2 D' φ z _ hz hw]
  abel

theorem isSec_sub_natural {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {b : Fn0 A} {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {s s' : RootFn A D}
    (hs : IsSec n b x s) (hs' : IsSec n b x s') {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) :
    s D'' (ψ.comp φ) (spOver ψ ≫ z) - s' D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z - s' D' φ z) := by
  rw [hs.1 D' D'' φ ψ z hz, hs'.1 D' D'' φ ψ z hz, map_sub]

theorem root_spOver {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {D : Type} [CommRing D] [Algebra R D] {x : Pt A D} {D' : Type} [CommRing D'] [Algebra R D']
    {D'' : Type} [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D') (ψ : D' →ₐ[R] D'')
    (z : Pt A D') (hz : z ^ n = spOver φ ≫ x) : (spOver ψ ≫ z) ^ n = spOver (ψ.comp φ) ≫ x := by
  rw [← MonObj.comp_pow z n (spOver ψ), hz, ← Category.assoc, spOver_comp]

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt

theorem isSec_sub_existsUnique : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ (b : Fn0 A) (D : Type) [CommRing D] [Algebra R D] (x : Pt A D) (s s' : RootFn A D),
    IsSec n b x s → IsSec n b x s' → ∃! e : D, ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (z : Pt A D'), z ^ n = spOver φ ≫ x → s D' φ z - s' D' φ z = φ e := by
  intro R _ A _ _ n hR b D _ _ x s s' hs hs'
  obtain ⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩ := hR D x
  have hdesc := GlobalTheory.ff_descent_pairs R D D₁ ψ hψ (s D₁ ψ z₀ - s' D₁ ψ z₀) (fun E _ _ α β hαβ ↦ by
    rw [← isSec_sub_natural hs hs' ψ α z₀ hz₀, ← isSec_sub_natural hs hs' ψ β z₀ hz₀]
    have hα := root_spOver ψ α z₀ hz₀
    have hβ := root_spOver ψ β z₀ hz₀
    rw [hαβ] at hα ⊢
    exact isSec_sub_root_eq hs hs' (β.comp ψ) (spOver β ≫ z₀) (spOver α ≫ z₀) hβ hα)
  obtain ⟨e, he, heu⟩ := hdesc
  have key : ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D'), z ^ n = spOver φ ≫ x →
      s D' φ z - s' D' φ z = φ e := by
    intro D' _ _ φ z hz
    obtain ⟨E', _, _, ψ', φ', hψ', hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
    have hinj : Function.Injective ψ' := by
      letI : Algebra D' E' := (ψ' : D' →+* E').toAlgebra
      haveI : Module.FaithfullyFlat D' E' := hψ'
      exact FaithfulSMul.algebraMap_injective D' E'
    apply hinj
    have h1 := root_spOver φ ψ' z hz
    have h2 := root_spOver ψ φ' z₀ hz₀
    rw [← isSec_sub_natural hs hs' φ ψ' z hz]
    rw [hsq] at h1 ⊢
    rw [isSec_sub_root_eq hs hs' _ _ _ h2 h1, isSec_sub_natural hs hs' ψ φ' z₀ hz₀, ← he]
    exact (congrArg (fun f : D →ₐ[R] E' ↦ f e) hsq).symm
  exact ⟨e, key, fun e' he' ↦ heu e' ((he' D₁ ψ z₀ hz₀).symm)⟩

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDifferenceOneCochain
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem isSec_pull {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (n : ℕ) (b : Fn0 A)
    {D : Type} [CommRing D] [Algebra R D] {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
    (x : Pt A D) (s : RootFn A D) (hs : IsSec n b x s) :
    IsSec n b (D := D') (spOver φ ≫ x) (fun E _ _ ψ z ↦ s E (ψ.comp φ) z) := by
  refine ⟨?_, ?_⟩
  · intro E _ _ E' _ _ α β z hz
    have hz' : z ^ n = spOver (α.comp φ) ≫ x := by rw [hz, ← spOver_comp, Category.assoc]
    exact hs.1 E E' (α.comp φ) β z hz'
  · intro E _ _ α z w hz hw
    have hz' : z ^ n = spOver (α.comp φ) ≫ x := by rw [hz, ← spOver_comp, Category.assoc]
    exact hs.2 E (α.comp φ) z w hz' hw

theorem exists_isSecDiff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∃ u : Fn1 A, IsSecDiff n S u := by
  intro R _ A _ _ n hR b _ S hS
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt A D),
      let x' : Pt A D' := spOver φ ≫ x
      ∃ e : D', ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E)
        (z : Pt A E), z ^ n = spOver ψ ≫ spOver φ ≫ x →
          S D' x' E ψ z - S D x E (ψ.comp φ) z = ψ e := by
    intro D _ _ D' _ _ φ x x'
    exact (isSec_sub_existsUnique R A n hR b D' x' (S D' x')
      (fun E _ _ ψ z ↦ S D x E (ψ.comp φ) z) (hS D' x')
      (isSec_pull n b φ x (S D x) (hS D x))).exists
  refine ⟨fun D _ _ D' _ _ φ x ↦ Classical.choose (key D D' φ x), ?_⟩
  intro D _ _ D' _ _ φ x E _ _ ψ z hz
  exact (Classical.choose_spec (key D D' φ x) E ψ z hz).symm

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDifferenceOneCochainStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_sectionDifference_one_cochain :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
        (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) →
        ∃ u : Fn1 A, IsSecDiff n S u :=
  @GlobalTheory.PtExt.exists_isSecDiff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorSectionEveryPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleDescends
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleIsCoboundary
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmitsurCohomologyH1

noncomputable def d0 (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] :
    D' →ₗ[D] D' ⊗[D] D' :=
  TensorProduct.mk D D' D' 1 - (TensorProduct.mk D D' D').flip 1

theorem amitsur_d0_apply (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] (a : D') :
    d0 D D' a = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  simp [d0]

theorem cocycle_is_coboundary : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (c : D' ⊗[D] D'),
    (∀ (E : Type) [CommRing E] [Algebra D E] (f₁ f₂ f₃ : D' →ₐ[D] E),
      Algebra.TensorProduct.lift f₁ f₃ (fun _ _ ↦ Commute.all _ _) c =
        Algebra.TensorProduct.lift f₁ f₂ (fun _ _ ↦ Commute.all _ _) c +
          Algebra.TensorProduct.lift f₂ f₃ (fun _ _ ↦ Commute.all _ _) c) →
    ∃ a : D', c = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  intro D D' _ _ _ _ c hc
  let i1 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') := Algebra.TensorProduct.includeLeft
  let i2 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeLeft
  let i3 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeRight
  have h := hc (D' ⊗[D] (D' ⊗[D] D')) i1 i2 i3
  have k1 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i1 i3 (fun _ _ ↦ Commute.all _ _) x -
        Algebra.TensorProduct.lift i1 i2 (fun _ _ ↦ Commute.all _ _) x =
        LinearMap.lTensor D' (d0 D D') x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i1, i2, i3, amitsur_d0_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), ← hx, ← hy]; abel
  have k2 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i2 i3 (fun _ _ ↦ Commute.all _ _) x = (1 : D') ⊗ₜ[D] x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      rw [map_add (f := _), hx, hy, TensorProduct.tmul_add]
  have key : (1 : D') ⊗ₜ[D] c = LinearMap.lTensor D' (d0 D D') c := by
    rw [← k1, ← k2, h]; abel
  let q := (LinearMap.range (d0 D D')).mkQ
  have hq : (1 : D') ⊗ₜ[D] q c = 0 := by
    have : (1 : D') ⊗ₜ[D] q c = LinearMap.lTensor D' q ((1 : D') ⊗ₜ[D] c) := by simp
    rw [this, key, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have hz : q ∘ₗ d0 D D' = 0 := by
      ext a; simp [q]
    rw [hz]; simp
  have hq0 : q c = 0 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff D _ (A := D') _).1 hq
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hq0
  exact ⟨a, by rw [← ha, amitsur_d0_apply]⟩

end GlobalTheory.AmitsurCohomologyH1
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlatDescent

def restrictR {R D A E : Type} [CommRing R] [CommRing D] [CommRing A] [CommRing E]
    [Algebra R D] [Algebra R A] [Algebra R E] [Algebra D A] [Algebra D E]
    (hA : ∀ r, algebraMap D A (algebraMap R D r) = algebraMap R A r)
    (hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r)
    (f : A →ₐ[D] E) : A →ₐ[R] E :=
  ⟨f.toRingHom, fun r => by
    show f (algebraMap R A r) = algebraMap R E r
    rw [← hA r, ← hE r]; exact f.commutes _⟩

theorem cocycle_descends : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D'), (ψ : D →+* D').FaithfullyFlat → ∀ (c : ∀ (E : Type) [CommRing E] [Algebra R E], (D' →ₐ[R] E) → (D' →ₐ[R] E) → E), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (α β : D' →ₐ[R] E) (ρ : E →ₐ[R] E'), α.comp ψ = β.comp ψ → c E' (ρ.comp α) (ρ.comp β) = ρ (c E α β)) → (∀ (E : Type) [CommRing E] [Algebra R E] (f₁ f₂ f₃ : D' →ₐ[R] E), f₁.comp ψ = f₂.comp ψ → f₂.comp ψ = f₃.comp ψ → c E f₁ f₃ = c E f₁ f₂ + c E f₂ f₃) → ∃ a : D', ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → c E α β = β a - α a := by
  intro R _ D D' _ _ _ _ ψ hψ c hnat hcoc
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  letI instRT : Algebra R (D' ⊗[D] D') :=
    ((algebraMap D (D' ⊗[D] D')).comp (algebraMap R D)).toAlgebra
  have h' : ∀ r, algebraMap D D' (algebraMap R D r) = algebraMap R D' r := fun r => ψ.commutes r
  have hT : ∀ r, algebraMap D (D' ⊗[D] D') (algebraMap R D r) = algebraMap R (D' ⊗[D] D') r :=
    fun _ => rfl
  let i₁ : D' →ₐ[R] D' ⊗[D] D' := restrictR h' hT Algebra.TensorProduct.includeLeft
  let i₂ : D' →ₐ[R] D' ⊗[D] D' := restrictR h' hT Algebra.TensorProduct.includeRight
  have h12 : i₁.comp ψ = i₂.comp ψ := by
    ext d
    exact ((Algebra.TensorProduct.includeLeft (R := D) (S := D) (A := D') (B := D')).commutes d).trans
      ((Algebra.TensorProduct.includeRight (R := D) (A := D') (B := D')).commutes d).symm
  obtain ⟨a, ha⟩ := GlobalTheory.AmitsurCohomologyH1.cocycle_is_coboundary D D' (c (D' ⊗[D] D') i₁ i₂) (by
    intro E _ _ f₁ f₂ f₃
    letI : Algebra R E := ((algebraMap D E).comp (algebraMap R D)).toAlgebra
    have hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r := fun _ => rfl
    have key : ∀ f g : D' →ₐ[D] E,
        Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _) (c (D' ⊗[D] D') i₁ i₂) =
          c E (restrictR h' hE f) (restrictR h' hE g) := by
      intro f g
      let ρ : D' ⊗[D] D' →ₐ[R] E :=
        restrictR hT hE (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _))
      have hn := hnat (D' ⊗[D] D') E i₁ i₂ ρ h12
      have e1 : ρ.comp i₁ = restrictR h' hE f := by
        ext x; simp [ρ, i₁, restrictR]
      have e2 : ρ.comp i₂ = restrictR h' hE g := by
        ext x; simp [ρ, i₂, restrictR]
      rw [e1, e2] at hn
      exact hn.symm
    have hc : ∀ f g : D' →ₐ[D] E, (restrictR h' hE f).comp ψ = (restrictR h' hE g).comp ψ := by
      intro f g; ext d
      exact (f.commutes d).trans (g.commutes d).symm
    rw [key, key, key]
    exact hcoc E _ _ _ (hc _ _) (hc _ _))
  refine ⟨a, ?_⟩
  intro E _ _ α β hαβ
  letI : Algebra D E := ((α.comp ψ : D →ₐ[R] E) : D →+* E).toAlgebra
  let α' : D' →ₐ[D] E := ⟨α.toRingHom, fun _ => rfl⟩
  let β' : D' →ₐ[D] E := ⟨β.toRingHom, fun d => by
    show β (ψ d) = α (ψ d)
    exact (DFunLike.congr_fun hαβ d).symm⟩
  have hE : ∀ r, algebraMap D E (algebraMap R D r) = algebraMap R E r := fun r => by
    show α (ψ _) = _
    rw [ψ.commutes, α.commutes]
  let ρ : D' ⊗[D] D' →ₐ[R] E :=
    restrictR hT hE (Algebra.TensorProduct.lift α' β' (fun _ _ ↦ Commute.all _ _))
  have hn := hnat (D' ⊗[D] D') E i₁ i₂ ρ h12
  have e1 : ρ.comp i₁ = α := by
    ext x; simp [ρ, i₁, α', restrictR]
  have e2 : ρ.comp i₂ = β := by
    ext x; simp [ρ, i₂, β', restrictR]
  rw [e1, e2] at hn
  rw [hn]
  show Algebra.TensorProduct.lift α' β' (fun _ _ ↦ Commute.all _ _) (c (D' ⊗[D] D') i₁ i₂) = _
  rw [ha]
  simp [α', β']

end GlobalTheory.FlatDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorSectionEveryPoint
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.PushSec

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]

theorem injective_of_ff {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (ψ : D →ₐ[R] D') (h : (ψ : D →+* D').FaithfullyFlat) : Function.Injective ψ := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := h
  exact FaithfulSMul.algebraMap_injective D D'

theorem root_map {n : ℕ} {D D' E : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E]
    [Algebra R E] (φ : D →ₐ[R] D') (ρ : D' →ₐ[R] E) (x : Pt A D) (z : Pt A D')
    (hz : (z ^ n : Pt A D') = spOver φ ≫ x) :
    ((spOver ρ ≫ z) ^ n : Pt A E) = spOver (ρ.comp φ) ≫ x := by
  rw [← MonObj.comp_pow z n (spOver ρ), hz, ← Category.assoc, spOver_comp]

theorem pow_mul_inv_eq_one {n : ℕ} {E : Type} [CommRing E] [Algebra R E] {y w u : Pt A E} (hy : y ^ n = u)
    (hw : w ^ n = u) : (y * w⁻¹) ^ n = 1 := by
  rw [mul_pow, inv_pow, hy, hw, mul_inv_cancel]

section Fixed

variable {n : ℕ} {b : Fn0 A} {D D₁ : Type} [CommRing D] [Algebra R D] [CommRing D₁] [Algebra R D₁]

def val (b : Fn0 A) (z₀ : Pt A D₁) (a : D₁) {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F]
    (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F) (z : Pt A D') : F :=
  φ' a + b F ((spOver ρ ≫ z) * (spOver φ' ≫ z₀)⁻¹)

variable (hb : IsTorsChar n b) (ψ : D →ₐ[R] D₁) (x : Pt A D) (z₀ : Pt A D₁)
  (hz₀ : (z₀ ^ n : Pt A D₁) = spOver ψ ≫ x)
  (a : D₁)
  (ha : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D₁ →ₐ[R] E), α.comp ψ = β.comp ψ →
    b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) = β a - α a)


include hz₀ in
theorem val_tors {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] (φ : D →ₐ[R] D')
    (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F)
    (h : ρ.comp φ = φ'.comp ψ) :
    ((spOver ρ ≫ z) * (spOver φ' ≫ z₀)⁻¹) ^ n = 1 :=
  pow_mul_inv_eq_one (root_map φ ρ x z hz) (by rw [root_map ψ φ' x z₀ hz₀, h])


include hb hz₀ in
theorem map_val {D' F G : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] [CommRing G] [Algebra R G]
    (φ : D →ₐ[R] D') (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F)
    (h : ρ.comp φ = φ'.comp ψ) (g₁ : F →ₐ[R] G) :
    g₁ (val b z₀ a ρ φ' z) = val b z₀ a (g₁.comp ρ) (g₁.comp φ') z := by
  unfold val
  rw [map_add (f := _), ← hb.1 F G g₁ _ (val_tors ψ x z₀ hz₀ φ z hz ρ φ' h), MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]
  rfl


include hb hz₀ ha in
theorem val_indep {D' F : Type} [CommRing D'] [Algebra R D'] [CommRing F] [Algebra R F] (φ : D →ₐ[R] D')
    (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) (ρ : D' →ₐ[R] F) (α β : D₁ →ₐ[R] F)
    (hα : ρ.comp φ = α.comp ψ)
    (hβ : ρ.comp φ = β.comp ψ) : val b z₀ a ρ α z = val b z₀ a ρ β z := by
  unfold val
  have t1 := val_tors ψ x z₀ hz₀ φ z hz ρ β hβ
  have t2 : ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) ^ n = 1 :=
    pow_mul_inv_eq_one (by rw [root_map ψ β x z₀ hz₀, ← hβ]) (by rw [root_map ψ α x z₀ hz₀, ← hα])
  have e : (spOver ρ ≫ z) * (spOver α ≫ z₀)⁻¹ =
      ((spOver ρ ≫ z) * (spOver β ≫ z₀)⁻¹) * ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) := by
    rw [_root_.mul_assoc, _root_.inv_mul_cancel_left]
  rw [e, hb.2 F _ _ t1 t2, ha F α β (hα.symm.trans hβ)]
  abel

def IsVal {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D') (e : D') : Prop :=
  ∀ (F : Type) [CommRing F] [Algebra R F] (ρ : D' →ₐ[R] F) (φ' : D₁ →ₐ[R] F), ρ.comp φ = φ'.comp ψ →
    ρ e = val b z₀ a ρ φ' z


include hb hz₀ ha in
theorem exists_isVal (hψ : (ψ : D →+* D₁).FaithfullyFlat) {D' : Type} [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (z : Pt A D') (hz : (z ^ n : Pt A D') = spOver φ ≫ x) :
    ∃ e : D', IsVal (b := b) ψ z₀ a φ z e := by
  obtain ⟨E', _, _, ρ₀, φ₀, hff, hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
  obtain ⟨e, he, -⟩ := GlobalTheory.ff_descent_pairs R D' E' ρ₀ hff (val b z₀ a ρ₀ φ₀ z) (by
    intro G _ _ g₁ g₂ hg₁g₂
    rw [map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq g₁, map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq g₂, ← hg₁g₂]
    refine val_indep hb ψ x z₀ hz₀ a ha φ z hz _ _ _ ?_ ?_
    · rw [AlgHom.comp_assoc, hsq, AlgHom.comp_assoc]
    · rw [hg₁g₂, AlgHom.comp_assoc, hsq, AlgHom.comp_assoc])
  refine ⟨e, fun F _ _ ρ φ' h ↦ ?_⟩
  obtain ⟨G, _, _, ρ₀', ρ', hff', hsq'⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D' E' F ρ₀ ρ hff
  apply injective_of_ff ρ₀' hff'
  rw [map_val hb ψ x z₀ hz₀ a φ z hz ρ φ' h ρ₀']
  change (ρ₀'.comp ρ) e = _
  rw [hsq', AlgHom.comp_apply, he, map_val hb ψ x z₀ hz₀ a φ z hz ρ₀ φ₀ hsq ρ']
  refine val_indep hb ψ x z₀ hz₀ a ha φ z hz _ _ _ ?_ ?_
  · rw [AlgHom.comp_assoc, hsq, AlgHom.comp_assoc]
  · rw [← hsq', AlgHom.comp_assoc, h, AlgHom.comp_assoc]

theorem isVal_unique (hψ : (ψ : D →+* D₁).FaithfullyFlat) {D' : Type} [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (z : Pt A D') {e e' : D'} (he : IsVal (b := b) ψ z₀ a φ z e) (he' : IsVal (b := b) ψ z₀ a φ z e') : e = e' := by
  obtain ⟨E', _, _, ρ₀, φ₀, hff, hsq⟩ := GlobalTheory.exists_pushout_faithfullyFlat R D D₁ D' ψ φ hψ
  exact injective_of_ff ρ₀ hff ((he E' ρ₀ φ₀ hsq).trans (he' E' ρ₀ φ₀ hsq).symm)

end Fixed

section Sec

variable {n : ℕ} {b : Fn0 A} {D D₁ : Type} [CommRing D] [Algebra R D] [CommRing D₁] [Algebra R D₁]
  (hb : IsTorsChar n b) (ψ : D →ₐ[R] D₁) (x : Pt A D) (z₀ : Pt A D₁)
  (hz₀ : (z₀ ^ n : Pt A D₁) = spOver ψ ≫ x)
  (a : D₁)
  (ha : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D₁ →ₐ[R] E), α.comp ψ = β.comp ψ →
    b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) = β a - α a)
  (hψ : (ψ : D →+* D₁).FaithfullyFlat)


open Classical in
def sec : RootFn A D := fun D' _ _ φ z ↦
  if h : (z ^ n : Pt A D') = spOver φ ≫ x then Classical.choose (exists_isVal hb ψ x z₀ hz₀ a ha hψ φ z h) else 0

theorem sec_spec {D' : Type} [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z : Pt A D')
    (hz : (z ^ n : Pt A D') = spOver φ ≫ x) : IsVal (b := b) ψ z₀ a φ z (sec hb ψ x z₀ hz₀ a ha hψ D' φ z) := by
  unfold sec
  rw [dite_eq_left hz]
  exact Classical.choose_spec (exists_isVal hb ψ x z₀ hz₀ a ha hψ φ z hz)

theorem isSec_sec : IsSec n b x (sec hb ψ x z₀ hz₀ a ha hψ) := by
  refine ⟨fun D' _ _ D'' _ _ φ ψ₂ z hz ↦ ?_, fun D' _ _ φ z w hz hw ↦ ?_⟩
  · have hz' := root_map φ ψ₂ x z hz
    refine isVal_unique ψ z₀ a hψ (ψ₂.comp φ) _ (sec_spec hb ψ x z₀ hz₀ a ha hψ _ _ hz') ?_
    intro F _ _ ρ φ' h
    change (ρ.comp ψ₂) _ = _
    rw [sec_spec hb ψ x z₀ hz₀ a ha hψ φ z hz F (ρ.comp ψ₂) φ' (by rw [AlgHom.comp_assoc]; exact h)]
    unfold val
    rw [← Category.assoc, spOver_comp]
  · have hzw : ((z * w) ^ n : Pt A D') = spOver φ ≫ x := by rw [mul_pow, hz, hw, _root_.mul_one]
    refine isVal_unique ψ z₀ a hψ φ _ (sec_spec hb ψ x z₀ hz₀ a ha hψ _ _ hzw) ?_
    intro F _ _ ρ φ' h
    have tw : (spOver ρ ≫ w) ^ n = 1 := by rw [← MonObj.comp_pow, hw, MonObj.comp_one]
    rw [map_add (f := _), sec_spec hb ψ x z₀ hz₀ a ha hψ φ z hz F ρ φ' h, ← hb.1 D' F ρ w hw]
    unfold val
    rw [add_assoc, ← hb.2 F _ _ (val_tors ψ x z₀ hz₀ φ z hz ρ φ' h) tw, MonObj.comp_mul, _root_.mul_right_comm]

end Sec

theorem exists_isSec : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n →
    ∀ b : Fn0 A, IsTorsChar n b → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ s : RootFn A D, IsSec n b x s := by
  intro R _ A _ _ n hR b hb D _ _ x
  obtain ⟨D₁, _, _, ψ, z₀, hψ, hz₀⟩ := hR D x
  obtain ⟨a, ha⟩ := GlobalTheory.FlatDescent.cocycle_descends R D D₁ ψ hψ
    (fun E _ _ α β ↦ b E ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹)) (by
      intro E _ _ E' _ _ α β g hαβ
      have t : ((spOver β ≫ z₀) * (spOver α ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ β x z₀ hz₀) (by rw [root_map ψ α x z₀ hz₀, hαβ])
      show b E' _ = g (b E _)
      rw [← hb.1 E E' g _ t, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, spOver_comp,
        spOver_comp]) (by
      intro E _ _ f₁ f₂ f₃ h12 h23
      have t1 : ((spOver f₂ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ f₂ x z₀ hz₀) (by rw [root_map ψ f₁ x z₀ hz₀, h12])
      have t2 : ((spOver f₃ ≫ z₀) * (spOver f₂ ≫ z₀)⁻¹) ^ n = 1 :=
        pow_mul_inv_eq_one (root_map ψ f₃ x z₀ hz₀) (by rw [root_map ψ f₂ x z₀ hz₀, h23])
      have e : (spOver f₃ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹ =
          ((spOver f₂ ≫ z₀) * (spOver f₁ ≫ z₀)⁻¹) * ((spOver f₃ ≫ z₀) * (spOver f₂ ≫ z₀)⁻¹) := by
        rw [_root_.mul_comm ((spOver f₂ ≫ z₀) * _), _root_.mul_assoc, _root_.inv_mul_cancel_left]
      show b E _ = b E _ + b E _
      rw [e, hb.2 E _ _ t1 t2])
  exact ⟨_, isSec_sec hb ψ x z₀ hz₀ a (fun E _ _ α β h ↦ ha E α β h) hψ⟩

end GlobalTheory.PtExt.PushSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorSectionEveryPointStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pushoutTorsorSection_every_point :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      GlobalTheory.PtExt.HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b →
        ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ s : RootFn A D, IsSec n b x s :=
  @GlobalTheory.PtExt.PushSec.exists_isSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocOfIsSecDiff
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isCoc_of_isSecDiff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) →
    ∀ u : Fn1 A, IsSecDiff n S u → IsCoc (whole A) u := by
  intro R _ A _ _ n hR b _ S _ u hu
  unfold IsCoc
  intro D _ _ D' _ _ D'' _ _ φ ψ x _
  obtain ⟨E, _, _, χ, z, hχ, hz⟩ := hR D'' (spOver ψ ≫ spOver φ ≫ x)
  apply (show Function.Injective χ from hχ.injective)
  have h1 := hu D D'' (ψ.comp φ) x E χ z (by rw [hz, ← spOver_comp, Category.assoc])
  have h2 := hu D D' φ x E (χ.comp ψ) z (by rw [hz, ← spOver_comp, Category.assoc])
  have h3 := hu D' D'' ψ (spOver φ ≫ x) E χ z hz
  rw [AlgHom.comp_apply] at h2
  rw [map_add χ, h1, h2, h3, ← spOver_comp, Category.assoc, AlgHom.comp_assoc]
  abel

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAddOfIsSecDiffIsSecAdd
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isAdd_of_isSecDiff_isSecAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ), HasRoots A n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A, (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ (u : Fn1 A) (g : Fn2 A), IsSecDiff n S u → IsSecAdd n S g → IsAdd u g := by
  intro R _ A _ _ n hR b _ S _ u g hu hg D _ _ D' _ _ φ x y
  let x' : Pt A D' := spOver φ ≫ x
  let y' : Pt A D' := spOver φ ≫ y
  obtain ⟨D1, _, _, ψ1, z1, h1, hz1⟩ := hR D' x'
  obtain ⟨E, _, _, ψ2, w, h2, hw⟩ := hR D1 (spOver ψ1 ≫ y')
  let ψ : D' →ₐ[R] E := ψ2.comp ψ1
  let z : Pt A E := spOver ψ2 ≫ z1
  have hψ : spOver ψ = spOver ψ2 ≫ spOver ψ1 := (spOver_comp ψ1 ψ2).symm
  have hz : z ^ n = spOver ψ ≫ x' := by
    rw [show z = spOver ψ2 ≫ z1 from rfl, ← comp_pow, hz1, hψ, Category.assoc]
  have hw' : w ^ n = spOver ψ ≫ y' := by rw [hw, hψ, Category.assoc]
  have hmul : spOver φ ≫ (x * y) = (spOver φ ≫ x) * (spOver φ ≫ y) := comp_mul _ _ _
  have hzw : (z * w) ^ n = spOver ψ ≫ spOver φ ≫ (x * y) := by
    rw [mul_pow, hz, hw', hmul, comp_mul]
  have hc (t : Pt A D) : spOver ψ ≫ spOver φ ≫ t = spOver (ψ.comp φ) ≫ t := by
    rw [← Category.assoc, spOver_comp]
  have hinj : Function.Injective ψ := fun _ _ h ↦ h1.injective (h2.injective h)
  apply hinj
  have e1 := hg D' x' y' E ψ z w hz hw'
  have e2 := hg D x y E (ψ.comp φ) z w (hz.trans (hc x)) (hw'.trans (hc y))
  rw [AlgHom.comp_apply] at e2
  have e3 := hu D D' φ (x * y) E ψ (z * w) hzw
  rw [hmul] at e3
  have e4 := hu D D' φ x E ψ z hz
  have e5 := hu D D' φ y E ψ w hw'
  simp only [map_sub]
  linear_combination e1 - e2 - e3 + e4 + e5

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiEqOfTorsion
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (x : T ⟶ A) (m : ℕ) : ρ ≫ x ^ m = (ρ ≫ x) ^ m :=
  MonObj.comp_pow x m ρ

theorem chi_eq_of_torsion : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    (n : R) = 0 → HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ g : Fn2 A, IsSecAdd n S g →
    ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → chi n g D x = b D x := by
  intro R _ A _ _ n hn hR b hb S hS g hg D _ _ x hx
  obtain ⟨E, _, _, ψ, z, hff, hz⟩ := hR D x
  apply hff.injective
  change ψ (chi n g D x) = ψ (b D x)
  have hpow : ∀ i : ℕ, (z ^ i) ^ n = spOver ψ ≫ x ^ i := by
    intro i
    rw [← pow_mul, mul_comm, pow_mul, hz, comp_pow_pt]

  have hterm : ∀ i : ℕ, ψ (g D (x ^ i) x) =
      (S D (x ^ (i + 1)) E ψ (z ^ (i + 1)) - S D (x ^ i) E ψ (z ^ i)) - S D x E ψ z := by
    intro i
    have h := hg D (x ^ i) x E ψ (z ^ i) z (hpow i) hz
    rw [← pow_succ, ← pow_succ] at h
    rw [h]
  have hnE : (n : E) = 0 := by
    rw [← map_natCast (algebraMap R E), hn, map_zero]
  have hsum : ψ (chi n g D x) = S D (x ^ n) E ψ (z ^ n) - S D (x ^ 0) E ψ (z ^ 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [chi, map_sum, hterm, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ S D (x ^ i) E ψ (z ^ i)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnE, zero_mul, sub_zero]
  rw [hsum, hx, pow_zero, pow_zero]

  have h1 : (1 : Pt A E) ^ n = spOver ψ ≫ (1 : Pt A D) := by rw [one_pow, MonObj.comp_one]
  have h2 : (z ^ n) ^ n = 1 := by rw [hpow n, hx, MonObj.comp_one]
  have hs := (hS D 1).2 E ψ 1 (z ^ n) h1 h2
  rw [_root_.one_mul] at hs
  rw [hs, add_sub_cancel_left, hz]
  exact hb.1 D E ψ x hx

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacter
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem exists_pushout_torsor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (hn : (n : R) = 0) (hR : HasRoots A n) (b : Fn0 A) (hb : IsTorsChar n b) :
    ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), (x ^ n : Pt A D) = 1 →
        chi n g D x = b D x := by
  have hSec := GlobalTheory.T.exists_pushoutTorsorSection_every_point R A n hR b hb
  let S : SecFam A := fun D _ _ x ↦ Classical.choose (hSec D x)
  have hS : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x) :=
    fun D _ _ x ↦ Classical.choose_spec (hSec D x)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sectionDifference_one_cochain R A n hR b hb S hS
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_sectionAddition_two_point_function R A n hR b hb S hS
  exact ⟨u, g, isCoc_of_isSecDiff R A n hR b hb S hS u hu,
    isAdd_of_isSecDiff_isSecAdd R A n hR b hb S hS u g hu hg,
    chi_eq_of_torsion R A n hn hR b hb S hS g hg⟩

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacterStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.exists_pushout_torsor_nTorsion_character :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      (n : R) = 0 → HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b →
        ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧
          ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), (x ^ n : Pt A D) = 1 →
            GlobalTheory.PtExt.chi n g D x = b D x :=
  @GlobalTheory.PtExt.exists_pushout_torsor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAddChiEq
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CobChi

theorem exists_isAdd_chi_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (n : ℕ),
    (n : R) = 0 → ∀ (u f : Fn1 A) (g : Fn2 A), IsAdd u g → Cohom (whole A) u f →
    ∃ g' : Fn2 A, IsAdd f g' ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      (x ^ n : Pt A D) = 1 → GlobalTheory.PtExt.chi n g' D x = GlobalTheory.PtExt.chi n g D x := by
  intro R _ A _ n hn u f g hu ⟨k, hk⟩
  have hf : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (x : Pt A D), f D D' φ x = u D D' φ x - (k D' (spOver φ ≫ x) - φ (k D x)) := by
    intro D _ _ D' _ _ φ x
    have h := hk D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg] at h
    linear_combination -h
  refine ⟨fun D _ _ x y ↦ g D x y - (k D (x * y) - k D x - k D y), ?_, ?_⟩
  · intro D _ _ D' _ _ φ x y
    have h1 := hu D D' φ x y
    simp only [hf, comp_mul, map_sub]
    linear_combination h1
  · intro D _ _ x hx
    have hnD : (n : D) = 0 := by
      rw [← map_natCast (algebraMap R D) n, hn, map_zero]
    have hs : ∑ i ∈ Finset.range n, (k D (x ^ i * x) - k D (x ^ i) - k D x) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      simp_rw [← pow_succ]
      rw [Finset.sum_range_sub (fun i ↦ k D (x ^ i)), hx, pow_zero, sub_self, zero_sub, neg_eq_zero, nsmul_eq_mul,
        hnD, zero_mul]
    simp only [GlobalTheory.PtExt.chi]
    rw [Finset.sum_sub_distrib, hs, sub_zero]

end GlobalTheory.CobChi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatOfIsAdd
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem exists_dat_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f = c.1 →
    ∀ g : Fn2 A, IsAdd (fv f) g → ∃ d : Dat t c, d.f = f ∧ d.g = g := by
  intro R _ A _ p G t c f hf g hg
  choose liftRes liftRes_spec using fun n ↦ G.res_surjective n
  let value (n : ℕ) : G.A n :=
    fv f (G.A (n + 1)) (G.A n) (G.res n).toAlgHom (t.y (n + 1))
  let h : ∀ n, G.A n := Nat.rec (motive := G.A) 0 (fun n a ↦ liftRes n (a - value n))
  refine ⟨⟨f, hf, g, hg, h, ?_⟩, rfl, rfl⟩
  intro n
  have hres : G.res n (h (n + 1)) = h n - value n := liftRes_spec n _
  change value n = h n - G.res n (h (n + 1))
  rw [hres, sub_sub_cancel]

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveDeRhamClassTorsionCharacter
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_dat_chi_eq (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (N : ℕ) (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (hP : AllPrim (dp0 R) (𝟙 _) A)
    (hs : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)))
    (G : PDivGroup p R) (t : G.TorsionTower A) (b : Fn0 A) (hb : IsTorsChar (p ^ N) b) :
    ∃ (c : primDR A) (d : Dat t c), ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      (x ^ (p ^ N) : Pt A D) = 1 → GlobalTheory.PtExt.chi (p ^ N) d.g D x = b D x := by
  have : IsCommMonObj A := hA.comm
  have hn : ((p ^ N : ℕ) : R) = 0 := by
    simpa only [Nat.cast_pow] using hN
  have hR : GlobalTheory.PtExt.HasRoots A (p ^ N) := fun D _ _ x ↦
    GlobalTheory.PtCover.exists_faithfullyFlat_pow_eq R A hA (p ^ N) (pow_pos (Fact.out : p.Prime).pos N) D x
  obtain ⟨u, g, hu, hg, hchi⟩ := GlobalTheory.T.exists_pushout_torsor_nTorsion_character R A (p ^ N) hn hR b hb
  obtain ⟨f, hf⟩ := GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective R A hs u hu
  obtain ⟨g', hg', hchi'⟩ := GlobalTheory.CobChi.exists_isAdd_chi_eq R A (p ^ N) hn u (fv f) g hg hf
  let c : primDR A := ⟨H1.mk _ f, by rw [show primDR A = ⊤ from hP]; exact Submodule.mem_top⟩
  obtain ⟨d, -, hd⟩ := GlobalTheory.PtExt.exists_dat_of_isAdd R A p G t c f rfl g' hg'
  refine ⟨c, d, fun D _ _ x hx ↦ ?_⟩
  rw [hd, hchi' D x hx, hchi D x hx]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveDeRhamClassTorsionCharacterStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_primitive_deRham_class_torsion_character
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ) (hN : (p : R) ^ N = 0)
    (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A) (hP : AllPrim (dp0 R) (𝟙 _) A)
    (hs : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)))
    (G : PDivGroup p R) (t : G.TorsionTower A) (b : Fn0 A) (hb : IsTorsChar (p ^ N) b) :
    ∃ (c : primDR A) (d : Dat t c), ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      x ^ (p ^ N) = 1 → chi (p ^ N) d.g D x = b D x :=
  GlobalTheory.PtExt.exists_dat_chi_eq p R N hN A hA hP hs G t b hb
end
