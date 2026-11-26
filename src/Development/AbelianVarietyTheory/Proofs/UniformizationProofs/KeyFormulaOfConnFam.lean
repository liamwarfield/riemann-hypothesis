module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyRuleCharHalf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ChiGen
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FiniteAbsLeOneMulMemRange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSmoothThrough

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDomainTensorOfIsAlgClosed
namespace GlobalTheory.ThetaEquiv

section Algebra
open Polynomial TensorProduct AlgebraicGeometry CategoryTheory Limits

theorem isDomain_tensor_of_isAlgClosed (K A : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] (F : Type) [Field F] [Algebra K F] : IsDomain (F ⊗[K] A) := by
  let f : Spec (.of A) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K A))
  have hf : LocallyOfFiniteType f := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hi : IsIntegral (Over.mk f).left := inferInstanceAs (IsIntegral (Spec (.of A)))
  have hg : GeometricallyIntegral f :=
    GlobalTheory.geometricallyIntegral_of_isIntegral_of_isAlgClosed K (Over.mk f) hf
  let y := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have : IsIntegral (pullback y f) :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F y
  have : IsIntegral (Spec (.of (F ⊗[K] A))) := IsIntegral.of_isIso (pullbackSpecIso K F A).hom
  exact (affine_isIntegral_iff (.of (F ⊗[K] A))).mp this

theorem exists_baseChange {K F : Type} [Field K] [Field F] (e : K →+* F) (A : Type) [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] (h : ∀ (L : Type) [Field L] [Algebra K L], IsDomain (L ⊗[K] A)) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra F B) (_ : Algebra.Smooth F B) (ψ : A →+* B),
      ∀ p : A →+* F, p.comp (algebraMap K A) = e → ∃ q : B →ₐ[F] F, q.toRingHom.comp ψ = p := by
  letI := e.toAlgebra
  refine ⟨F ⊗[K] A, inferInstance, h F, inferInstance, inferInstance,
    (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := A)).toRingHom, fun p hp => ?_⟩
  let p' : A →ₐ[K] F := { p with commutes' := fun a => congr($hp a) }
  refine ⟨Algebra.TensorProduct.lift (AlgHom.id F F) p' fun _ _ => .all _ _, ?_⟩
  ext a
  simp [p']

theorem exists_root_prime (K : Type) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : n.Prime)
    (R : Type) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.Smooth K R] (κ : R) (hκ : IsUnit κ)
    (p₀ p : R →ₐ[K] K) (u₀ : K) (hu : u₀ ^ n = p₀ κ) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra K B) (_ : Algebra.Smooth K B) (φ : R →ₐ[K] B)
      (r : B) (q₀ q : B →ₐ[K] K), r ^ n = φ κ ∧ q₀.comp φ = p₀ ∧ q.comp φ = p ∧ q₀ r = u₀ := by
  by_cases h : ∃ ρ : R, ρ ^ n = κ
  · obtain ⟨ρ, hρ⟩ := h
    have h₁ : p₀ κ ≠ 0 := (hκ.map p₀).ne_zero
    have h₂ : p₀ ρ ≠ 0 := by
      intro h0
      apply h₁
      rw [← hρ, map_pow, h0, zero_pow hn.ne_zero]
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, AlgHom.id K R,
      algebraMap K R (u₀ / p₀ ρ) * ρ, p₀, p, ?_, rfl, rfl, ?_⟩
    · rw [mul_pow, ← map_pow, div_pow, hu, ← map_pow, hρ, div_self h₁]
      simp
    · simp [h₂]
  · have hic : IsIntegrallyClosed R := GlobalTheory.isIntegrallyClosed_of_smooth K R
    let L := FractionRing R
    let f : R[X] := X ^ n - C κ
    have hf : f.Monic := monic_X_pow_sub_C κ hn.ne_zero
    have hmap : f.map (algebraMap R L) = X ^ n - C (algebraMap R L κ) := by simp [f]
    have hirr : Irreducible (f.map (algebraMap R L)) := by
      rw [hmap]
      refine X_pow_sub_C_irreducible_of_prime hn fun b hb => h ?_
      have hb' : IsIntegral R b := by
        refine ⟨f, hf, ?_⟩
        simp [f, hb]
      obtain ⟨ρ, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
      exact ⟨ρ, IsFractionRing.injective R L (by rw [map_pow, hb])⟩
    have hpr : Prime f := by
      refine ⟨hf.ne_zero, fun hu => hirr.not_isUnit (hu.map (mapRingHom (algebraMap R L))), fun a b hab => ?_⟩
      rw [← map_dvd_map (algebraMap R L) (IsFractionRing.injective R L) hf, Polynomial.map_mul] at hab
      rw [← map_dvd_map (algebraMap R L) (IsFractionRing.injective R L) hf,
        ← map_dvd_map (algebraMap R L) (IsFractionRing.injective R L) hf]
      exact hirr.prime.dvd_or_dvd hab
    have hdom : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hpr
    have hroot : AdjoinRoot.root f ^ n = algebraMap R (AdjoinRoot f) κ := by
      have := AdjoinRoot.aeval_eq f (f := f)
      rw [AdjoinRoot.mk_self] at this
      simpa [f, sub_eq_zero] using this
    have hru : IsUnit (AdjoinRoot.root f) := by
      rw [← isUnit_pow_iff hn.ne_zero, hroot]
      exact hκ.map _
    have het : Algebra.Etale R (AdjoinRoot f) := by
      refine GlobalTheory.etale_adjoinRoot_of_isUnit_derivative hf ?_
      have : AdjoinRoot.mk f f.derivative =
          algebraMap K (AdjoinRoot f) (n : K) * AdjoinRoot.root f ^ (n - 1) := by
        simp [f, derivative_X_pow]
      rw [this]
      exact ((Ne.isUnit (Nat.cast_ne_zero.2 hn.ne_zero)).map _).mul (hru.pow _)
    have hsm : Algebra.Smooth K (AdjoinRoot f) := Algebra.Smooth.comp K R (AdjoinRoot f)
    have lift : ∀ (s : R →ₐ[K] K) (u : K), u ^ n = s κ → ∃ q : AdjoinRoot f →ₐ[K] K,
        q.comp (IsScalarTower.toAlgHom K R (AdjoinRoot f)) = s ∧ q (AdjoinRoot.root f) = u := by
      intro s u hs
      refine ⟨AdjoinRoot.liftAlgHom f s u (by simp [f, hs]), ?_, ?_⟩
      · ext a
        simp
      · simp
    obtain ⟨u, hu'⟩ := IsAlgClosed.exists_pow_nat_eq (p κ) hn.pos
    obtain ⟨q₀, h₀, h₀'⟩ := lift p₀ u₀ hu
    obtain ⟨q, h₁, -⟩ := lift p u hu'
    exact ⟨AdjoinRoot f, inferInstance, hdom, inferInstance, hsm, IsScalarTower.toAlgHom K R _,
      AdjoinRoot.root f, q₀, q, hroot, h₀, h₁, h₀'⟩

theorem exists_root (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ) : n ≠ 0 →
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.Smooth K R] (κ : R) (_ : IsUnit κ)
    (p₀ p : R →ₐ[K] K) (u₀ : K) (_ : u₀ ^ n = p₀ κ),
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra K B) (_ : Algebra.Smooth K B) (φ : R →ₐ[K] B)
      (r : B) (q₀ q : B →ₐ[K] K), r ^ n = φ κ ∧ q₀.comp φ = p₀ ∧ q.comp φ = p ∧ q₀ r = u₀ := by
  induction n using induction_on_primes with
  | zero => exact fun h => (h rfl).elim
  | one =>
    intro _ R _ _ _ _ κ _ p₀ p u₀ hu
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, AlgHom.id K R, κ, p₀, p,
      by simp, rfl, rfl, by simpa using hu.symm⟩
  | prime_mul l a hl ih =>
    intro hn R _ _ _ _ κ hκ p₀ p u₀ hu
    obtain ⟨B, _, _, _, _, φ, r, q₀, q, h₁, h₂, h₃, h₄⟩ :=
      exists_root_prime K hl R κ hκ p₀ p (u₀ ^ a) (by rw [← pow_mul, mul_comm, hu])
    have hr : IsUnit r := by
      rw [← isUnit_pow_iff hl.ne_zero, h₁]
      exact hκ.map _
    obtain ⟨B', _, _, _, _, φ', r', q₀', q', g₁, g₂, g₃, g₄⟩ :=
      ih (right_ne_zero_of_mul hn) B r hr q₀ q u₀ h₄.symm
    refine ⟨B', inferInstance, inferInstance, inferInstance, inferInstance, φ'.comp φ, r', q₀', q', ?_, ?_, ?_, g₄⟩
    · rw [mul_comm, pow_mul, g₁, ← map_pow, h₁, AlgHom.comp_apply]
    · rw [← AlgHom.comp_assoc, g₂, h₂]
    · rw [← AlgHom.comp_assoc, g₃, h₃]

end Algebra

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

def IsVal (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8

theorem exists_isVal (hU : ThetaUnifAV) (x : KeyIn ℂ) : ∃ t, IsVal x t := by
  obtain ⟨τ, M, a, b, c, h₁, h₂, -, h₃⟩ := (GlobalTheory.KeyNormalExists.exists_normalAt hU x).1
  exact ⟨_, τ, M, a, b, c, h₁, h₂, h₃, rfl⟩

theorem val_eq_root (hL : Out.Laws) (hU : ThetaUnifAV) (hI : Key.Chi.InversionStatement) {S : Type} [CommRing S]
    (y : KeyIn S) {n : ℕ} (hn : 1 ≤ n) (κ : Sˣ)
    (hκ : ∀ (s : S →+* ℂ) (x : KeyIn ℂ) (t : ℂ), KeyPB x y s → IsVal x t → t ^ n = s κ)
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (ψ : S →+* B) (r : B)
    (hr : r ^ n = ψ κ) (q₀ q : B →ₐ[ℂ] ℂ)
    (h₀ : ∀ x₀ : KeyIn ℂ, KeyPB x₀ y (q₀.toRingHom.comp ψ) → IsVal x₀ (q₀ r))
    (x : KeyIn ℂ) (t : ℂ) (hx : KeyPB x y (q.toRingHom.comp ψ)) (ht : IsVal x t) : t = q r := by
  obtain ⟨yB, hyB⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange S B y ψ
  have hex : ∀ p : B →ₐ[ℂ] ℂ, ∃ u : ℂ, (∃ z : KeyIn ℂ, KeyPB z yB p.toRingHom ∧ IsVal z u) ∧ (p = q → u = t) := by
    intro p
    by_cases hp : p = q
    · subst hp
      exact ⟨t, ⟨x, GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y yB x ψ _ hyB hx, ht⟩, fun _ => rfl⟩
    · obtain ⟨z, hz⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange B ℂ yB p.toRingHom
      obtain ⟨u, hu⟩ := exists_isVal hU z
      exact ⟨u, ⟨z, hz, hu⟩, fun h => (hp h).elim⟩
  choose T hT hTq using hex
  have hru : IsUnit r := by
    rw [← isUnit_pow_iff (Nat.one_le_iff_ne_zero.1 hn), hr]
    exact κ.isUnit.map ψ
  obtain ⟨r, rfl⟩ := hru
  rw [← hTq q rfl]
  refine GlobalTheory.T.thetaFrame_value_eq_unit_smooth_connected_base hL hU hI B yB n r T q₀ hn hT (fun p => ?_) ?_ q
  · obtain ⟨z, hz, hu⟩ := hT p
    rw [hκ _ z _ (GlobalTheory.keyPB_trans _ _ _ y yB z ψ _ hyB hz) hu, ← map_pow, hr]
    rfl
  · obtain ⟨z, hz, hu⟩ := hT q₀
    exact GlobalTheory.T.thetaFrame_value_independent_normalForm hU hI z _ _ hu (h₀ z (GlobalTheory.keyPB_trans _ _ _ y yB z ψ _ hyB hz))

theorem val_equivariant : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → (∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf) → (∀ x : KeyIn ℂ, ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (y : KeyIn S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (t₀ : k), Algebra.Smooth k S ∧ (∀ (K : Type) [Field K] [Algebra k K], IsDomain (TensorProduct k K S)) ∧ KeyPB x y s ∧ ∀ (e : k →+* ℂ) (x₀ : KeyIn ℂ), KeyPB x₀ y (e.comp s₀.toRingHom) → (∃ (τ M : Matrix (Fin x₀.P.g) (Fin x₀.P.g) ℂ) (a b : Fin x₀.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x₀ τ M a b c ∧ e t₀ = M.det ^ 4 / c ^ 8)) → ∀ (f : ℂ →+* ℂ) (x x' : KeyIn ℂ) (t t' : ℂ), KeyPB x' x f → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → (∃ (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x' τ M a b c ∧ t' = M.det ^ 4 / c ^ 8) → t' = f t := by
  rintro hL hU hI ⟨N, hN, hR⟩ hfam f x x' t t' hx' ht ht'
  obtain ⟨k, _, _, S, _, _, y, s, s₀, t₀, hsm, hdom, hx, h₀⟩ := hfam x
  have : IsDomain S := by
    have := hdom k
    exact (Algebra.TensorProduct.lid k S).symm.toMulEquiv.isDomain _
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_unit_thetaKeyRule_smooth_base hU hL.polBaseChange N hR k S y
  have hn := hN y.P.g
  let e : k →+* ℂ := s.comp (algebraMap k S)
  obtain ⟨R, _, _, _, _, ψ₁, hψ₁⟩ := exists_baseChange e S hdom
  obtain ⟨p, hp⟩ := hψ₁ s rfl
  obtain ⟨p₀, hp₀⟩ := hψ₁ (e.comp s₀.toRingHom) (by ext a; simp)
  have hu : e t₀ ^ N y.P.g = p₀ (ψ₁ κ) := by
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange S ℂ y (e.comp s₀.toRingHom)
    rw [hκ _ x₀ _ hx₀ (h₀ e x₀ hx₀), ← hp₀]
    rfl
  obtain ⟨B, _, _, _, _, φ, r, q₀, q, hr, hq₀, hq, hq₀r⟩ :=
    exists_root ℂ (N y.P.g) (Nat.one_le_iff_ne_zero.1 hn) R (ψ₁ κ) (κ.isUnit.map ψ₁) p₀ p (e t₀) hu
  have key : ∀ (g : ℂ →+* ℂ) (z : KeyIn ℂ) (u : ℂ), KeyPB z y (g.comp s) → IsVal z u → u = g (q r) := by
    intro g z u hz hu
    obtain ⟨B', _, _, _, _, ψ₂, hψ₂⟩ := exists_baseChange g B fun L _ _ => isDomain_tensor_of_isAlgClosed ℂ B L
    obtain ⟨Q, hQ⟩ := hψ₂ (g.comp q.toRingHom) (by ext a; simp)
    obtain ⟨Q₀, hQ₀⟩ := hψ₂ (g.comp q₀.toRingHom) (by ext a; simp)
    have a₁ : Q.toRingHom.comp (ψ₂.comp (φ.toRingHom.comp ψ₁)) = g.comp s := by
      rw [← RingHom.comp_assoc, hQ, ← hp, ← hq]
      rfl
    have a₀ : Q₀.toRingHom.comp (ψ₂.comp (φ.toRingHom.comp ψ₁)) = (g.comp e).comp s₀.toRingHom := by
      rw [← RingHom.comp_assoc, hQ₀, RingHom.comp_assoc s₀.toRingHom, ← hp₀, ← hq₀]
      rfl
    have b₁ : Q (ψ₂ r) = g (q r) := congr($hQ r)
    have b₀ : Q₀ (ψ₂ r) = (g.comp e) t₀ := by
      rw [RingHom.comp_apply, ← hq₀r]
      exact congr($hQ₀ r)
    rw [← b₁]
    refine val_eq_root hL hU hI y hn κ hκ B' (ψ₂.comp (φ.toRingHom.comp ψ₁)) (ψ₂ r) ?_ Q₀ Q
      (fun x₀ hx₀ => ?_) z u (a₁ ▸ hz) hu
    · rw [← map_pow, hr]
      rfl
    · rw [b₀]
      exact h₀ _ x₀ (a₀ ▸ hx₀)
  have c₁ : t = q r := key (RingHom.id ℂ) x t hx ht
  rw [c₁]
  exact key f x' t' (GlobalTheory.keyPB_trans _ _ _ y x x' s f hx hx') ht'

end GlobalTheory.ThetaEquiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCommonCountable
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBOfKeyViaField
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyDesc

open GlobalTheory.KeyCancel

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMapR_algebraMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    Chart.dualMapR f (algebraMap A _ a) = algebraMap B _ (f a) := by
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMapR_eps {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Chart.dualMapR f DualNumber.eps = DualNumber.eps := by
  ext <;> simp [Chart.dualMapR]

theorem keyPB_of_keyVia_field : ∀ (R k K : Type) [CommRing R] [Field k] [Field K] (α : R →+* k) (β : k →+* K)
    (y : KeyIn R) (z : KeyIn k) (x : KeyIn K) (φ : x.P.A.left ⟶ z.P.A.left) (w₀ : LB.Iso x.P.L (z.P.L.pull φ))
    (ψ : z.P.A.left ⟶ y.P.A.left) (w₁ : LB.Iso x.P.L (y.P.L.pull (φ ≫ ψ))), KeyVia x z β φ w₀ →
    KeyVia x y (β.comp α) (φ ≫ ψ) w₁ → IsGrpPullback z.P.A y.P.A (spMap α) ψ → LBIso z.P.L (y.P.L.pull ψ) →
    KeyPB z y α := by
  intro R k K _ _ _ α β y z x φ w₀ ψ w₁ ⟨he₀, hg₀, F₀, hc₀, hw₀, hr₀, hs₀, hF₀, hFe₀, hv₀⟩
    ⟨he₁, hg₁, F₁, hc₁, hw₁, hr₁, hs₁, hF₁, hFe₁, hv₁⟩ hψ ⟨u, hu⟩
  have he : eSec z.P.A ≫ ψ = spMap α ≫ eSec y.P.A := PolBaseChange.eSec_comm hψ
  obtain ⟨w, g, m⟩ := KeyPow.exists_rescale y.P.isLB z.P.isLB ((isGen_iff u).1 hu) (p := z.P.A.hom)
    (Over.w η[z.P.A]) he z.rig_gen y.rig_gen
  have g₀ := (isGen_iff w₀).1 hw₀
  obtain ⟨w₂, T⟩ := exists_comp z.P.isLB w w₀ g g₀ y.P.isLB x.P.isLB
  have r₀ := (maps_iff w₀ _ (fun _ => eSec z.P.A) _ x.rig z.rig (spMap β) _ (rigPull_le φ (spMap β) he₀ z.P.L)
    (fun _ => rfl)).1 hr₀
  have r₂ := T.pmaps_comp z.P.isLB (fun _ => he₀) m r₀
  rw [← spMap_comp] at r₂
  obtain rfl : w₂ = w₁ := rigidified_iso_unique globalFns_holds x.P y.P.isLB (φ ≫ ψ) w₂ w₁
    ((isGen_iff _).2 (T.pgen_comp z.P.isLB g g₀)) hw₁ x.rig _
    ((maps_iff w₂ _ (fun _ => eSec y.P.A) _ x.rig y.rig (spMap (β.comp α)) _
      (rigPull_le (φ ≫ ψ) (spMap (β.comp α)) he₁ y.P.L) (fun _ => rfl)).2 r₂) hr₁
  have := z.P.isAb.smooth
  have := y.P.isAb.proper
  have : IsSchemeTheoreticallyDominant (spMap β) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom β) β.injective
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hc₀.1.flip
  have : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact) hc₀.1.flip inferInstance
  obtain rfl : F₀ = Chart.dualMapR β := dualNumber_ringHom_ext
    (fun a => (hF₀ a).trans (dualMapR_algebraMap β a).symm) (hFe₀.trans (dualMapR_eps β).symm)
  obtain rfl : F₁ = (Chart.dualMapR β).comp (Chart.dualMapR α) := dualNumber_ringHom_ext
    (fun a => by rw [hF₁, RingHom.comp_apply, RingHom.comp_apply, dualMapR_algebraMap, dualMapR_algebraMap])
    (by rw [hFe₁, RingHom.comp_apply, dualMapR_eps, dualMapR_eps])
  refine ⟨ψ, he, w, hg₀.symm.trans hg₁, Chart.dualMapR α, hψ, (isGen_iff w).2 g,
    (maps_iff w _ (fun _ => eSec y.P.A) _ z.rig y.rig (spMap α) _ (rigPull_le ψ (spMap α) he y.P.L)
      (fun _ => rfl)).2 m, fun j i hle => φ.app_injective _ (fn_ext fun q hq => ?_), dualMapR_algebraMap α,
    dualMapR_eps α, fun i => ?_⟩
  · have hq' : φ ((𝟙 x.P.A.left : _ ⟶ _) q) ∈ (y.P.L.pull ψ).U j ⊓ z.P.L.U i := hq
    obtain ⟨l, hl⟩ := exists_chart x.P.isLB q
    have a := (appLE_eq_iff_stalk w₀ z.th x.th).1 hs₀ _ (𝟙 _) q i l hq'.2 hl
    have b := (appLE_eq_iff_stalk w₂ y.th x.th).1 hs₁ _ (𝟙 _) q (j PUnit.unit) l ((mem_pull (F := ψ)).1 hq'.1) hl
    rw [T _ (𝟙 _) q (j PUnit.unit) i l (mem_pull.1 hq'.1) hq'.2 hl, Units.val_mul, _root_.mul_assoc, ← a,
      ← Category.assoc] at b
    refine (gs_pull (𝟙 _) φ q _ hq' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) φ q _ hq' _).symm)
    refine (gs_appLE ψ _ _ hle (𝟙 _ ≫ φ) q hq' _).trans (b.trans ?_)
    rw [gs_mul (𝟙 _ ≫ φ) q _ hq', gs_res (𝟙 _ ≫ φ) q _ hq']
    exact congrArg (· * _) (gs_unit (𝟙 _ ≫ φ) q _ hq' _).symm
  · refine Spread.tangent_ext β β.injective y.P.A.hom ?_ ?_
    · rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext fun a => (dualMapR_algebraMap α a).symm
    · have a := hv₀ (i.cast hg₀.symm)
      have b := hv₁ (i.cast hg₀.symm)
      rw [← Category.assoc, a, spMap_comp, Category.assoc, Category.assoc] at b
      exact b

end GlobalTheory.KeyDesc
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.KeyRoot


open GlobalTheory.KeyCancel in
theorem keyVia_cancel {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'}
    {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''} {φ w φ'' w''} (H : KeyVia x' x f φ w)
    (H'' : KeyVia x'' x (f'.comp f) φ'' w'') : ∃ φ' w', φ' ≫ φ = φ'' ∧ KeyVia x'' x' f' φ' w' := by
  obtain ⟨he, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  obtain ⟨he'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := H''
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', w', rfl, he', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem keyPB_iff {R R' : Type} [CommRing R] [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R') :
    KeyPB x' x f ↔ ∃ φ w, KeyVia x' x f φ w := (KeyVia.main R R' x x' f).1

theorem exists_keyVia {R R' : Type} [CommRing R] [CommRing R'] (x : KeyIn R) (f : R →+* R') :
    ∃ x' φ w, KeyVia x' x f φ w :=
  (KeyPow.exists_keyPB_ring x f).imp fun x' h => (keyPB_iff x' x f).1 h

theorem exists_factor {S K : Type} [CommRing S] [Countable S] [Field K] (i : S →+* K) (s : Set K)
    (hs : s.Countable) : ∃ (k : Subfield K) (j : S →+* k), Countable k ∧ s ⊆ k ∧ k.subtype.comp j = i := by
  have hc : (s ∪ Set.range i).Countable := hs.union (Set.countable_range i)
  refine ⟨Subfield.closure (s ∪ Set.range i),
    i.codRestrict (Subfield.closure (s ∪ Set.range i)) fun a => Subfield.subset_closure (Or.inr ⟨a, rfl⟩), ?_,
    fun a ha => Subfield.subset_closure (Or.inl ha), rfl⟩
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (Subfield.cardinalMk_closure_le_max _).trans
    (max_le (Cardinal.le_aleph0_iff_set_countable.2 hc) le_rfl)

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_common_countable {k K : Type} [Field k] [Countable k] [Field K] (σ : k →+* K) (y₀ y₁ : KeyIn k)
    (x : KeyIn K) (h₀ : KeyPB x y₀ σ) (h₁ : KeyPB x y₁ σ) :
    ∃ (k' : Subfield K) (α : k →+* k') (z : KeyIn k'), Countable k' ∧ KeyPB z y₀ α ∧ KeyPB z y₁ α := by
  obtain ⟨φ₀, w₀, V₀⟩ := (keyPB_iff _ _ _).1 h₀
  obtain ⟨φ₁, w₁, V₁⟩ := (keyPB_iff _ _ _).1 h₁
  have G₀ : IsGrpPullback x.P.A y₀.P.A (spMap σ) φ₀ := V₀.choose_spec.choose_spec.choose_spec.1
  have G₁ : IsGrpPullback x.P.A y₁.P.A (spMap σ) φ₁ := V₁.choose_spec.choose_spec.choose_spec.1
  have px := x.P.isAb.proper
  obtain ⟨s, hs⟩ := hom_descends_to_subfield_containing_finset k K σ x.P.A x.P.A y₀.P.A y₁.P.A φ₀ φ₁ G₀.1 G₁.1
    inferInstance inferInstance inferInstance (𝟙 _)
  obtain ⟨k₁, α₁, c₁, hs₁, rfl⟩ := exists_factor σ s s.countable_toSet
  obtain ⟨z₁, χ₁, u₁, U₁⟩ := exists_keyVia y₀ α₁
  obtain ⟨z₁', ω, u₁', U₁'⟩ := exists_keyVia y₁ α₁
  obtain ⟨φ', w', e', W'⟩ := keyVia_cancel U₁ V₀
  obtain ⟨ψ₁, w₁', e₁', W₁'⟩ := keyVia_cancel U₁' V₁
  have gU₁ : IsGrpPullback _ _ _ χ₁ := U₁.choose_spec.choose_spec.choose_spec.1
  have gU₁' : IsGrpPullback _ _ _ ω := U₁'.choose_spec.choose_spec.choose_spec.1
  have gW' : IsGrpPullback _ _ _ φ' := W'.choose_spec.choose_spec.choose_spec.1
  have gW₁' : IsGrpPullback _ _ _ ψ₁ := W₁'.choose_spec.choose_spec.choose_spec.1
  obtain ⟨f₁, hf₁⟩ := hs k₁ α₁ k₁.subtype rfl (fun a ha => ⟨⟨a, hs₁ ha⟩, rfl⟩) z₁.P.A z₁'.P.A φ' χ₁ ψ₁ ω gU₁.1 gU₁'.1
    e' e₁' gW'.1.w gW₁'.1.w
  have hψ : φ' ≫ f₁.left ≫ ω = φ₁ := by
    rw [← Category.assoc, hf₁, Over.id_left, Category.id_comp, e₁']
  have hψ' : (f₁.left ≫ ω) ≫ y₁.P.A.hom = z₁.P.A.hom ≫ spMap α₁ := by
    rw [Category.assoc, gU₁'.1.w, ← Category.assoc, Over.w]
  generalize f₁.left ≫ ω = ψ at hψ hψ'
  have pz := z₁.P.isAb.proper
  have lN := LB.isLB_pull y₁.P.isLB ψ
  have iso₁ : LBIso (z₁.P.L.pull φ') ((y₁.P.L.pull ψ).pull φ') :=
    LBIso.trans (LB.isLB_pull z₁.P.isLB _) x.P.isLB (LB.isLB_pull lN _)
      (LBIso.symm ⟨w', W'.choose_spec.choose_spec.choose_spec.2.1⟩)
      (LBIso.trans x.P.isLB (LB.isLB_pull y₁.P.isLB _) (LB.isLB_pull lN _)
        ⟨w₁, V₁.choose_spec.choose_spec.choose_spec.2.1⟩ (GenSpread.lbIso_pull_pull y₁.P.isLB φ' hψ.symm))
  obtain ⟨s', hs'⟩ := lbIso_descends_to_subfield_containing_finset k₁ K k₁.subtype z₁.P.A x.P.A φ' z₁.P.L (y₁.P.L.pull ψ) gW'.1 inferInstance
    inferInstance z₁.P.isLB lN iso₁
  obtain ⟨k₂, α₂, c₂, hs₂, e₂⟩ := exists_factor k₁.subtype s' s'.countable_toSet
  obtain ⟨z₂, χ₂, u₂, U₂⟩ := exists_keyVia z₁ α₂
  have gU₂ : IsGrpPullback _ _ _ χ₂ := U₂.choose_spec.choose_spec.choose_spec.1
  have iso₂ := hs' k₂ α₂ k₂.subtype e₂ (fun a ha => ⟨⟨a, hs₂ ha⟩, rfl⟩) z₂.P.A χ₂ gU₂.1
  obtain ⟨φ'', w'', e'', W''⟩ := keyVia_cancel U₂ (e₂.symm ▸ W' : KeyVia x z₁ (k₂.subtype.comp α₂) φ' w')
  have gW'' : IsGrpPullback _ _ _ φ'' := W''.choose_spec.choose_spec.choose_spec.1
  have eσ : k₁.subtype.comp α₁ = k₂.subtype.comp (α₂.comp α₁) := by rw [← RingHom.comp_assoc, e₂]
  have eφ : φ₁ = φ'' ≫ χ₂ ≫ ψ := by rw [← Category.assoc, e'', hψ]
  subst eφ
  rw [eσ] at V₁ G₁
  have fl : Flat (spMap k₂.subtype) := inferInstance
  have su : Surjective (spMap k₂.subtype) := ⟨Function.surjective_to_subsingleton _⟩
  refine ⟨k₂, α₂.comp α₁, z₂, c₂, keyPB_trans _ _ _ _ _ _ _ _ ((keyPB_iff _ _ _).2 ⟨_, _, U₁⟩)
    ((keyPB_iff _ _ _).2 ⟨_, _, U₂⟩), GlobalTheory.KeyDesc.keyPB_of_keyVia_field k k₂ K _ _ y₁ z₂ x φ'' w'' (χ₂ ≫ ψ) w₁ W'' V₁ ?_ ?_⟩
  · refine isGrpPullback_of_fpqc _ _ _ _ _ _ _ _ φ'' _ fl su inferInstance gW'' (G₁.congr (spMap_comp' _ _) rfl) ?_
    rw [Category.assoc, hψ', ← Category.assoc, gU₂.1.w, Category.assoc, spMap_comp']
  · exact LBIso.trans z₂.P.isLB (LB.isLB_pull z₁.P.isLB _) (LB.isLB_pull y₁.P.isLB _)
      ⟨u₂, U₂.choose_spec.choose_spec.choose_spec.2.1⟩
      (LBIso.trans (LB.isLB_pull z₁.P.isLB _) (LB.isLB_pull lN _) (LB.isLB_pull y₁.P.isLB _) iso₂
        (GenSpread.lbIso_pull_pull y₁.P.isLB χ₂ rfl).symm)

def InFamilies (t : KeyIn ℂ → ℂ) : Prop :=
  ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsPrincipalIdealRing S] (x₀ : KeyIn S) (f f' : S →+* ℂ)
    (u : S) (x x' : KeyIn ℂ), Function.Injective f → KeyPB x x₀ f → KeyPB x' x₀ f' → t x = f u → t x' = f' u

def IsValAt (t : KeyIn ℂ → ℂ) {S : Type} [CommRing S] (y : KeyIn S) (u : S) : Prop :=
  ∀ (f : S →+* ℂ) (x : KeyIn ℂ), KeyPB x y f → t x = f u

def IsVal (t : KeyIn ℂ → ℂ) {K : Type} [CommRing K] (x : KeyIn K) (u : K) : Prop :=
  ∃ (S : Type) (_ : CommRing S) (_ : Countable S) (i : S →+* K) (y : KeyIn S) (u₀ : S),
    KeyPB x y i ∧ IsValAt t y u₀ ∧ u = i u₀

variable {t : KeyIn ℂ → ℂ}

theorem trans' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'}
    {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''} (h : KeyPB x' x f) (h' : KeyPB x'' x' f') :
    KeyPB x'' x (f'.comp f) := keyPB_trans _ _ _ _ _ _ _ _ h h'

theorem cancel' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'}
    {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''} {g : R →+* R''} (h : KeyPB x' x f) (h' : KeyPB x'' x g)
    (e : f'.comp f = g) : KeyPB x'' x' f' := KeyCancel.keyPB_cancel _ _ _ _ _ _ _ _ h (e ▸ h')

theorem IsValAt.map {S S' : Type} [CommRing S] [CommRing S'] {y : KeyIn S} {u : S} (h : IsValAt t y u)
    {y' : KeyIn S'} {j : S →+* S'} (hy : KeyPB y' y j) : IsValAt t y' (j u) :=
  fun f x hx => h (f.comp j) x (trans' hy hx)

theorem IsVal.map {K K' : Type} [CommRing K] [CommRing K'] {x : KeyIn K} {u : K} (h : IsVal t x u)
    {x' : KeyIn K'} {f : K →+* K'} (hx : KeyPB x' x f) : IsVal t x' (f u) := by
  obtain ⟨S, _, _, i, y, u₀, h₁, h₂, rfl⟩ := h
  exact ⟨S, _, ‹_›, f.comp i, y, u₀, trans' h₁ hx, h₂, rfl⟩

theorem nonempty_complex (k : Type) [Field k] [CharZero k] [Countable k] : Nonempty (k →+* ℂ) :=
  (nonempty_algHom_complex_of_countable ℤ k).map AlgHom.toRingHom

theorem IsVal.unique {K : Type} [Field K] [CharZero K] {x : KeyIn K} {u u' : K} (h : IsVal t x u)
    (h' : IsVal t x u') : u = u' := by
  obtain ⟨S, _, _, i, y, u₀, h₁, h₂, rfl⟩ := h
  obtain ⟨S', _, _, i', y', u₀', h₁', h₂', rfl⟩ := h'
  obtain ⟨k, j, _, hs, rfl⟩ := exists_factor i (Set.range i') (Set.countable_range i')
  let j' : S' →+* k := i'.codRestrict k fun a => hs ⟨a, rfl⟩
  obtain ⟨z, hz⟩ := exists_keyPB_ring y j
  obtain ⟨z', hz'⟩ := exists_keyPB_ring y' j'
  obtain ⟨k', α, w, _, hw, hw'⟩ := exists_common_countable k.subtype z z' x (cancel' hz h₁ rfl) (cancel' hz' h₁' rfl)
  obtain ⟨g⟩ := nonempty_complex k'
  obtain ⟨c, hc⟩ := exists_keyPB_ring w g
  have e := (((h₂.map hz).map hw) g c hc).symm.trans (((h₂'.map hz').map hw') g c hc)
  exact congrArg k.subtype (α.injective (g.injective e))

theorem exists_isValAt (ht : InFamilies t) (k : Type) [Field k] [CharZero k] [Countable k] (y : KeyIn k) :
    ∃ u, IsValAt t y u := by
  obtain ⟨s⟩ := nonempty_complex k
  obtain ⟨x, hx⟩ := exists_keyPB_ring y s
  letI := s.toAlgebra
  obtain ⟨u, hu⟩ := (FixedPoint.defined_over_of_fixed (K₀ := k) (K₁ := k) (L := ℂ)).1 (t x) fun σ => by
    obtain ⟨x', hx'⟩ := exists_keyPB_ring x (σ : ℂ →+* ℂ)
    have h₁ := ht ℂ x (RingHom.id ℂ) σ (t x) x x' Function.injective_id (keyPB_id _ x) hx' rfl
    have e : (σ : ℂ →+* ℂ).comp s = s := RingHom.ext σ.commutes
    have h₂ := ht ℂ x (RingHom.id ℂ) (RingHom.id ℂ) (t x) x x' Function.injective_id (keyPB_id _ x)
      (cancel' hx (trans' hx hx') (by rw [e]; rfl)) rfl
    exact h₁.symm.trans h₂
  exact ⟨u, fun f x' hx' => ht k y s f u x x' s.injective hx hx' hu.symm⟩

def Descent : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] [CharZero R] (x : KeyIn R) (s : Set R),
    s.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (x₀ : KeyIn R₀),
      Countable R₀ ∧ s ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ KeyPB x x₀ R₀.subtype

theorem Descent.field (hD : Descent) {K : Type} [Field K] [CharZero K] (x : KeyIn K) (s : Set K) (hs : s.Countable) :
    ∃ (k : Subfield K) (y : KeyIn k), Countable k ∧ s ⊆ k ∧ KeyPB x y k.subtype := by
  obtain ⟨R₀, -, -, x₀, _, -, -, h⟩ := hD K x ∅ Set.countable_empty
  obtain ⟨k, j, c, hk, e⟩ := exists_factor R₀.subtype s hs
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ j
  exact ⟨k, y, c, hk, cancel' hy h e⟩

theorem IsValAt.ne_zero (h0 : ∀ x, t x ≠ 0) {k : Type} [Field k] [CharZero k] [Countable k] {y : KeyIn k} {u : k}
    (h : IsValAt t y u) : u ≠ 0 := by
  obtain ⟨s⟩ := nonempty_complex k
  obtain ⟨x, hx⟩ := exists_keyPB_ring y s
  rintro rfl
  exact h0 x ((h s x hx).trans (map_zero s))

theorem exists_isVal (hD : Descent) (ht : InFamilies t) (h0 : ∀ x, t x ≠ 0) (K : Type) [Field K] [CharZero K]
    (x : KeyIn K) : ∃ u : Kˣ, IsVal t x (u : K) := by
  obtain ⟨k, y, _, -, hy⟩ := hD.field x ∅ Set.countable_empty
  obtain ⟨u, hu⟩ := exists_isValAt ht k y
  exact ⟨Units.mk0 (k.subtype u) ((map_ne_zero k.subtype).2 (hu.ne_zero h0)), k, _, ‹_›, k.subtype, y, u, hy, hu, rfl⟩

theorem IsVal.complex {x : KeyIn ℂ} {u : ℂ} (h : IsVal t x u) : u = t x := by
  obtain ⟨S, _, _, i, y, u₀, h₁, h₂, rfl⟩ := h
  exact (h₂ i x h₁).symm

theorem g_eq {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'}
    (h : KeyPB x' x f) : x'.P.g = x.P.g := by
  obtain ⟨_, _, _, hg, _⟩ := h
  exact hg

theorem IsVal.pow (hD : Descent) (ht : InFamilies t) {N : ℕ → ℕ}
    (ρ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ)
    (hF : ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
      1 ≤ x.P.g → KeyPB x' x f → (ρ K' x' : K') = f (ρ K x))
    (hC : ∀ x : KeyIn ℂ, (ρ ℂ x : ℂ) = t x ^ N x.P.g) {K : Type} [Field K] [CharZero K] {x : KeyIn K} {u : K}
    (h : IsVal t x u) : u ^ N x.P.g = ρ K x := by
  obtain ⟨k, y, _, -, hy⟩ := hD.field x ∅ Set.countable_empty
  obtain ⟨u₀, hu⟩ := exists_isValAt ht k y
  obtain rfl : u = k.subtype u₀ := h.unique ⟨k, _, ‹_›, k.subtype, y, u₀, hy, hu, rfl⟩
  obtain ⟨s⟩ := nonempty_complex k
  obtain ⟨c, hc⟩ := exists_keyPB_ring y s
  rw [hF k K _ y x y.g_pos hy, ← map_pow, g_eq hy]
  refine congrArg _ (s.injective ?_)
  rw [← hF k ℂ s y c y.g_pos hc, hC, hu s c hc, g_eq hc, map_pow]

theorem IsVal.special (hD : Descent) (ht : InFamilies t) {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsPrincipalIdealRing R] [Field K] [CharZero K] {a : R →+* K} (ha : Function.Injective a) {x : KeyIn R}
    {xK : KeyIn K} (hx : KeyPB xK x a) {u : R} (h : IsVal t xK (a u)) : IsVal t x u := by
  have := a.charZero
  obtain ⟨R₀, _, _, x₀, _, hu, -, h₀⟩ := hD R x {u} (Set.countable_singleton u)
  let u₀ : R₀ := ⟨u, hu rfl⟩
  obtain ⟨k, j, _, -, e⟩ := exists_factor (a.comp R₀.subtype) ∅ Set.countable_empty
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ j
  obtain ⟨u₁, hu₁⟩ := exists_isValAt ht k y
  have e₁ : a u = k.subtype u₁ := h.unique ⟨k, _, ‹_›, k.subtype, y, u₁, cancel' hy (trans' h₀ hx) e, hu₁, rfl⟩
  have hj : ∀ r, k.subtype (j r) = a r := fun r => congrArg (fun g : R₀ →+* K => g r) e
  obtain rfl : j u₀ = u₁ := k.subtype.injective ((hj u₀).trans e₁)
  have ij : Function.Injective j := fun r r' hr =>
    Subtype.ext (ha ((hj r).symm.trans ((congrArg k.subtype hr).trans (hj r'))))
  obtain ⟨s⟩ := nonempty_complex k
  obtain ⟨c, hc⟩ := exists_keyPB_ring y s
  exact ⟨R₀, _, ‹_›, R₀.subtype, x₀, u₀, h₀, fun f x' hx' => ht R₀ x₀ (s.comp j) f u₀ c x' (s.injective.comp ij)
    (trans' hy hc) hx' (hu₁ s c hc), rfl⟩

theorem exists_scale {K : Type} [Field K] (x : KeyIn K) {a : K} (ha : a ≠ 0) {M : Matrix (Fin x.P.g) (Fin x.P.g) K}
    (hM : M.det ≠ 0) : ∃ (th' : x.P.L.Sec) (_ : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th')
      (v' : Fin x.P.g → (epsR K ⟶ x.P.A)) (_ : IsLieBasis v'),
      (∀ i, th'.f i = constFn x.P.A.hom _ a * x.th.f i) ∧ ∀ i, IsLieComb (M i) x.v (v' i) := by
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hb⟩ := LieComb.lieComb_algebra K x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (M i)).exists
  refine ⟨KeyNormalExists.constMul x.P.A.hom a x.th, fun s => ?_, v, (hb M v x.basis hv).2 hM.isUnit, fun _ => rfl, hv⟩
  obtain ⟨z, hz, hz'⟩ := x.th_ne s
  exact ⟨z, hz, KeyNormalExists.mem_nonzeroLocus_constMul _ ha.isUnit _ hz'⟩

theorem normalAt_scale {P : Out.PolAV (Sp ℂ)} {hg rig hr th hth v hv th' hth' v' hv'} {a : ℂ}
    {M : Matrix (Fin P.g) (Fin P.g) ℂ} (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i)
    (h₂ : ∀ i, IsLieComb (M i) v (v' i)) {τ N : Matrix (Fin P.g) (Fin P.g) ℂ} {p q : Fin P.g → ℂ} {c : ℂ}
    (h : NormalAt ⟨P, hg, rig, hr, th, hth, v, hv⟩ τ N p q c) :
    NormalAt ⟨P, hg, rig, hr, th', hth', v', hv'⟩ τ (M * N) p q (a * c) := by
  obtain ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩ := h
  have := P.isAb.comm
  refine ⟨u, k₁, k₂, k₃, k₄, fun i z hz => ?_, fun i => ?_⟩
  · refine ((congrArg (valAt' _ _) (h₁ i)).trans (valAt'_mul _ _ _ _)).trans ?_
    rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
    refine (congrArg (a * ·) (k₅ i z hz)).trans ?_
    simp only [_root_.mul_assoc]
  · have k := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 k₆ (h₂ i)
    have e : ∑ j, M i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • N j) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (M * N) i := by
      simp only [smul_comm (M i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
      rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
      rfl
    rwa [e] at k

theorem det_cast {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') {m n : ℕ} (e : m = n)
    (M : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun i j : Fin m => f (M (i.cast e) (j.cast e))).det = f M.det := by
  subst e
  exact (f.map_det M).symm

def FromNormal (t : KeyIn ℂ → ℂ) : Prop :=
  (∀ x : KeyIn ℂ, ∃ τ M a b c, charHalf x.P.g a b ∧ c ≠ 0 ∧ M.det ≠ 0 ∧ NormalAt x τ M a b c) ∧
    ∀ (x : KeyIn ℂ) τ M a b c, charHalf x.P.g a b → c ≠ 0 → NormalAt x τ M a b c → t x = M.det ^ 4 / c ^ 8

theorem IsValAt.scale (ht : InFamilies t) (hN : FromNormal t) {k : Type} [Field k] {P : Out.PolAV (Sp k)}
    {hg rig hr th hth v hv th' hth' v' hv'} {a : k} (ha : a ≠ 0)
    {M : Matrix (Fin P.g) (Fin P.g) k} (hM : M.det ≠ 0)
    (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i)
    (h₂ : ∀ i, IsLieComb (M i) v (v' i)) {u : k} (h : IsValAt t ⟨P, hg, rig, hr, th, hth, v, hv⟩ u) :
    IsValAt t ⟨P, hg, rig, hr, th', hth', v', hv'⟩ (M.det ^ 4 / a ^ 8 * u) := by
  intro f x' hx'
  obtain ⟨c, hc⟩ := exists_keyPB_ring (⟨P, hg, rig, hr, th, hth, v, hv⟩ : KeyIn k) f
  have e : c.P.g = P.g := g_eq hc
  have hd := det_cast f e M
  have ha' : f a ≠ 0 := (map_ne_zero f).2 ha
  obtain ⟨s', hs', w', hw', k₁, k₂⟩ := exists_scale c ha' (hd ▸ (map_ne_zero f).2 hM)
  have hc' := KeyPBScale.keyPB_scale k ℂ f P hg rig hr th hth v hv th' hth' v' hv' a M c.P e c.g_pos c.rig c.rig_gen c.th c.th_ne
    c.v c.basis s' hs' w' hw' h₁ h₂ k₁ k₂ hc
  obtain ⟨τ, N, p, q, d, hpq, hd0, -, hn⟩ := hN.1 c
  have e₁ := hN.2 ⟨c.P, c.g_pos, c.rig, c.rig_gen, s', hs', w', hw'⟩ _ _ _ _ _ hpq (mul_ne_zero ha' hd0)
    (normalAt_scale (hg := c.g_pos) (hr := c.rig_gen) (hth := c.th_ne) (hv := c.basis) (hth' := hs') (hv' := hw')
      k₁ k₂ hn)
  have e₂ := (h f c hc).symm.trans (hN.2 _ _ _ _ _ _ hpq hd0 hn)
  rw [ht ℂ _ (RingHom.id ℂ) (RingHom.id ℂ) _ _ x' Function.injective_id (keyPB_id _ _) (cancel' hc' hx' rfl) rfl,
    RingHom.id_apply, e₁, map_mul, e₂, Matrix.det_mul, hd, map_div₀, map_pow, map_pow]
  field_simp

theorem scale_ne_zero {K : Type} [Field K] {P : Out.PolAV (Sp K)} {th th' : P.L.Sec} {a : K}
    (hth' : ∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th')
    (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) : a ≠ 0 := by
  rintro rfl
  obtain ⟨z, -, hz⟩ := hth' (default : PrimeSpectrum K)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  rw [h₁, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
  exact hi

theorem IsVal.scale (hD : Descent) (ht : InFamilies t) (hN : FromNormal t) {K : Type} [Field K] [CharZero K]
    {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'} {a : K} {M : Matrix (Fin P.g) (Fin P.g) K}
    (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) (h₂ : ∀ i, IsLieComb (M i) v (v' i)) {u u' : K}
    (h : IsVal t ⟨P, hg, rig, hr, th, hth, v, hv⟩ u) (h' : IsVal t ⟨P, hg, rig, hr, th', hth', v', hv'⟩ u') :
    a ^ 8 * u' = M.det ^ 4 * u := by
  have ha := scale_ne_zero hth' h₁
  have := P.isAb.comm
  have hM : M.det ≠ 0 := (((LieComb.lieComb_algebra K P.A P.g v hv.1).2.2.2.2 M v' hv h₂).1 hv').ne_zero
  obtain ⟨k, y, _, hs, hy⟩ := hD.field (⟨P, hg, rig, hr, th, hth, v, hv⟩ : KeyIn K)
    (insert a (Set.range fun p : Fin P.g × Fin P.g => M p.1 p.2)) ((Set.countable_range _).insert a)
  have e : P.g = y.P.g := g_eq hy
  let a₀ : k := ⟨a, hs (Set.mem_insert _ _)⟩
  let M₀ : Matrix (Fin y.P.g) (Fin y.P.g) k := fun i j =>
    ⟨M (i.cast e.symm) (j.cast e.symm), hs (Set.mem_insert_of_mem _ ⟨(_, _), rfl⟩)⟩
  have hd : M.det = k.subtype M₀.det := det_cast k.subtype e M₀
  have ha₀ : a₀ ≠ 0 := fun h => ha (congrArg Subtype.val h)
  have hM₀ : M₀.det ≠ 0 := fun h => hM (by rw [hd, h, map_zero])
  obtain ⟨s', hs', w', hw', k₁, k₂⟩ := exists_scale y ha₀ hM₀
  obtain ⟨u₀, hu₀⟩ := exists_isValAt ht k y
  have hy' := KeyPBScale.keyPB_scale k K k.subtype y.P y.g_pos y.rig y.rig_gen y.th y.th_ne y.v y.basis s' hs' w' hw' a₀ M₀ P e hg rig
    hr th hth v hv th' hth' v' hv' k₁ k₂ h₁ h₂ hy
  rw [h.unique ⟨k, _, ‹_›, k.subtype, y, u₀, hy, hu₀, rfl⟩, h'.unique ⟨k, _, ‹_›, k.subtype, _, _, hy',
    IsValAt.scale ht hN (hg := y.g_pos) (hr := y.rig_gen) (hth := y.th_ne) (hv := y.basis) ha₀ hM₀ k₁ k₂ hu₀, rfl⟩,
    hd, map_mul, map_div₀, map_pow, map_pow]
  change a ^ 8 * (_ / a ^ 8 * _) = _
  field_simp

theorem keyFormula_of_families : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] [CharZero R] (x : KeyIn R) (s : Set R), s.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (x₀ : KeyIn R₀), Countable R₀ ∧ s ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ KeyPB x x₀ R₀.subtype) → (∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf) → (∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsPrincipalIdealRing S] (x₀ : KeyIn S) (f f' : S →+* ℂ) (u : S) (x x' : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ) (τ' M' : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a' b' : Fin x'.P.g → ℂ) (c' : ℂ), Function.Injective f → KeyPB x x₀ f → KeyPB x' x₀ f' → charHalf _ a b → charHalf _ a' b' → c ≠ 0 → c' ≠ 0 → NormalAt x τ M a b c → NormalAt x' τ' M' a' b' c' → M.det ^ 4 / c ^ 8 = f u → M'.det ^ 4 / c' ^ 8 = f' u) → KeyFormula := by
  intro hU _ hD ⟨N, hN1, ρ, ρH, ρF, ρU, ρN⟩ hC
  have hE := fun x => (KeyNormalExists.exists_normalAt hU x).1
  choose τ M a b c hab hc hM hn using id hE
  let t : KeyIn ℂ → ℂ := fun x => (M x).det ^ 4 / c x ^ 8
  have ht : InFamilies t := fun S _ _ _ _ x₀ f f' u x x' hf h h' e =>
    hC S x₀ f f' u x x' _ _ _ _ _ _ _ _ _ _ hf h h' (hab x) (hab x') (hc x) (hc x') (hn x) (hn x') e
  have hN : FromNormal t := ⟨hE, fun x τ' M' a' b' c' hab' hc' hn' =>
    hC ℂ x (RingHom.id ℂ) (RingHom.id ℂ) _ x x _ _ _ _ _ _ _ _ _ _ Function.injective_id (keyPB_id _ x) (keyPB_id _ x)
      hab' (hab x) hc' (hc x) hn' (hn x) rfl⟩
  have h0 : ∀ x, t x ≠ 0 := fun x => div_ne_zero (pow_ne_zero _ (hM x)) (pow_ne_zero _ (hc x))
  have hρ : ∀ x : KeyIn ℂ, (ρ ℂ x : ℂ) = t x ^ N x.P.g := fun x =>
    value_at_normalForm N 1 (ρ ℂ) x.P.g (a x) (b x) x.g_pos (ρH ℂ)
      (fun y h σ hy => ρN y σ _ _ y.g_pos ⟨fun i => (hab x).1 _, fun i => (hab x).2 _⟩ hy) x rfl _ _ _ (hc x) (hM x)
      (hn x)
  choose κ hκ using exists_isVal hD ht h0
  refine ⟨κ, fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂ =>
      IsVal.scale hD ht hN h₁ h₂ (hκ K _) (hκ K _),
    fun K K' _ _ _ _ f x x' h => (hκ K' x').unique ((hκ K x).map h), fun R K _ _ _ _ _ _ _ x xK h => ?_,
    fun x u σ p q h₁ h₂ hp hq h₃ h₄ h₅ h₆ => Units.ext ?_, fun x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_⟩
  · obtain ⟨u', hu', -⟩ := ρU R K x xK x.g_pos h
    have hp := ((hκ K xK).pow hD ht ρ ρF hρ).trans hu'
    have hpos : 0 < N xK.P.g := hN1 _
    obtain ⟨u, hu⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) hpos
      (hp ▸ isIntegral_algebraMap)
    have inj := IsFractionRing.injective R K
    have hunit : IsUnit u := by
      rw [← hu, ← map_pow] at hp
      exact (isUnit_pow_iff hpos.ne').1 (inj hp ▸ u'.isUnit)
    have hv : IsVal t x u := IsVal.special hD ht inj h (hu ▸ hκ K xK)
    exact ⟨hunit.unit, hu.symm, fun k _ _ r xk _ hk => (hκ k xk).unique (hv.map hk)⟩
  · rw [(hκ ℂ x).complex, hN.2 x σ 1 p q 1 ⟨hp, hq⟩ one_ne_zero
      ((normalAt_one_iff x σ p q).2 ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩)]
    simp
  · obtain ⟨u', σ, M', p, q, d, k₁, k₂, hp, hq, k₃, k₄, hd, k₅, -, k₆, k₇⟩ :=
      keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [(hκ ℂ x).complex, hN.2 x σ M' p q d ⟨hp, hq⟩ hd ⟨u', k₁, k₂, k₃, k₄, k₅, k₆⟩]
    exact k₇

end GlobalTheory.KeyRoot
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem keyFormula_of_connFam : GlobalTheory.KeyKa.ConnFam → KeyFormula := fun hF =>
  have hL := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hR := GlobalTheory.KeyTop.exists_keyRule_charHalf hL GlobalTheory.T.theta_uniformisation_complex_abelian_varieties GlobalTheory.ThetaInversion.inversion (GlobalTheory.phHolo_of_phKoecher GlobalTheory.phKoecher) GlobalTheory.torusAlgebraic_holds
  GlobalTheory.KeyRoot.keyFormula_of_families GlobalTheory.T.theta_uniformisation_complex_abelian_varieties hL.polBaseChange (GlobalTheory.T.keyData_descend_countable_subrings hL).1 hR
    (GlobalTheory.ThetaFrameSpec.value_specialises hL GlobalTheory.T.theta_uniformisation_complex_abelian_varieties GlobalTheory.ThetaInversion.inversion hR (GlobalTheory.ThetaEquiv.val_equivariant hL GlobalTheory.T.theta_uniformisation_complex_abelian_varieties GlobalTheory.ThetaInversion.inversion hR hF))

end GlobalTheory
