module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLevelOverIntegers
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianSche
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilySRep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelLargeLevel

theorem isAlgebraic_of_mem_ZP {p M : ℕ} (hM : M ≠ 0) {x : ℂ} (hx : x ∈ ZP p M) : IsAlgebraic ℤ x := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ, ← mem_algebraicClosure_iff]
  have hle : ZP p M ≤ (algebraicClosure ℚ ℂ).toSubalgebra.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (rfl | ⟨n, -, rfl⟩)
    · have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
      exact mem_algebraicClosure_iff.2
        (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hM) (h1 ▸ isAlgebraic_one))
    · exact (algebraicClosure ℚ ℂ).inv_mem (natCast_mem _ n)
  exact hle hx

theorem exists_siegelFamily_sRep : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h n : ℕ), 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → n ≠ p → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SRep Ag := by
  intro L L2 hθ hU h n hh hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.nonempty_siegelFamily_over_arithmetic_base L L2 hθ hU h n hh hn hodd
  refine ⟨max j₀ 1, fun j hj p hp hnp => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨o, _, b, em, i, hem, hζ, hi, hconst⟩ :=
    GlobalTheory.ZM.CycBase.exists_base n (j * 2) p ((n ^ j) ^ 2) hn hp hnp (by omega) (pow_mul n j 2).symm
  obtain ⟨F⟩ := hj₀ j (le_trans (le_max_left _ _) hj) o b em hem
  have h3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨m, rfl⟩
    omega
  have hk : 3 ≤ (n ^ j) ^ 2 := by
    rw [← pow_mul]
    exact h3.trans (Nat.le_self_pow (by omega) n)
  have hinj : Function.Injective i := fun x y hxy => hem.2.2 (by rw [← hi, ← hi, hxy])
  have halg : Algebra.IsAlgebraic ℤ o := ⟨fun x => by
    have hx : IsAlgebraic ℤ (em.toIntAlgHom x) := by
      change IsAlgebraic ℤ (em x)
      rw [← hi]
      exact isAlgebraic_of_mem_ZP (by omega) (i x).2
    exact (isAlgebraic_algHom_iff em.toIntAlgHom hem.2.2).1 hx⟩
  exact GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers L L2 h _ p o _ i (hodd.pow.pow) hk hp hinj hζ hconst halg F

end GlobalTheory.ZM.SiegelLargeLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPrincipalLift
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LiftZPMapAeval
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Polynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem isUnit_of_isUnit_map_of_ker_sq_eq_bot {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥) (x : R') (hx : IsUnit (π x)) :
    IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y', rfl⟩ := hs y
  have h1 : x * y' - 1 ∈ RingHom.ker π := by simp [RingHom.mem_ker, hy]
  have h2 : (x * y' - 1) ^ 2 = 0 := by
    have := Ideal.pow_mem_pow h1 2
    rwa [hk, Ideal.mem_bot] at this
  have h3 : IsUnit (x * y' - 1 + 1) := IsNilpotent.isUnit_add_one ⟨2, h2⟩
  rw [sub_add_cancel] at h3
  exact isUnit_of_mul_isUnit_left h3

private theorem ringHom_aeval_eq_aeval_apply {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (f : ℤ[X]) (x : R') : π (Polynomial.aeval x f) = Polynomial.aeval (π x) f :=
  (Polynomial.aeval_algHom_apply π.toIntAlgHom x f).symm

private theorem exists_root_lift_of_ker_sq_eq_bot {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥) (f : ℤ[X]) (z : R)
    (hz : Polynomial.aeval z f = 0) (hd : IsUnit (Polynomial.aeval z (derivative f))) :
    ∃ z' : R', π z' = z ∧ Polynomial.aeval z' f = 0 := by
  obtain ⟨z₀, rfl⟩ := hs z
  have hu : IsUnit (Polynomial.aeval z₀ (derivative f)) :=
    isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ (by rwa [ringHom_aeval_eq_aeval_apply])
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h0 : π (Polynomial.aeval z₀ f) = 0 := by rwa [ringHom_aeval_eq_aeval_apply]
  have h1 : -(v * Polynomial.aeval z₀ f) ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_neg, map_mul, h0, mul_zero, neg_zero]
  have h2 : (-(v * Polynomial.aeval z₀ f)) ^ 2 = 0 := by
    have := Ideal.pow_mem_pow h1 2
    rwa [hk, Ideal.mem_bot] at this
  refine ⟨z₀ + -(v * Polynomial.aeval z₀ f), ?_, ?_⟩
  · rw [map_add (f := _), RingHom.mem_ker.mp h1, add_zero]
  · rw [Polynomial.aeval_add_of_sq_eq_zero _ _ _ h2, mul_neg, ← _root_.mul_assoc, hv, _root_.one_mul,
      add_neg_cancel]

private theorem isUnit_aeval_derivative_cyclotomic {R : Type} [CommRing R] (M : ℕ) (hM : M ≠ 0) (hu : IsUnit (M : R))
    (z : R) (hz : Polynomial.aeval z (cyclotomic M ℤ) = 0) :
    IsUnit (Polynomial.aeval z (derivative (cyclotomic M ℤ))) := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one M ℤ
  have h1 : z ^ M = 1 := by
    have := congrArg (Polynomial.aeval z) hg
    rw [map_mul, hz, zero_mul] at this
    simpa [sub_eq_zero] using this
  have hzu : IsUnit z := IsUnit.of_pow_eq_one h1 hM
  have h2 := congrArg (fun q => Polynomial.aeval z (derivative q)) hg
  simp only [derivative_mul, map_add (f := _), map_mul, hz, zero_mul, add_zero, derivative_sub,
    derivative_one, sub_zero, derivative_X_pow, map_natCast, map_pow, aeval_X] at h2
  have h3 : IsUnit ((M : R) * z ^ (M - 1)) := hu.mul (hzu.pow _)
  rw [h2] at h3
  exact isUnit_of_mul_isUnit_left h3

private theorem lift_squareZero_general {B R' R : Type} [CommRing B] [CommRing R'] [CommRing R]
    (π : R' →+* R) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (f : ℤ[X]) (ζ : B) (S : Submonoid ℕ) (h0 : Polynomial.aeval ζ f = 0)
    (hinj : ∀ g : ℤ[X], Polynomial.aeval ζ g = 0 → f ∣ g)
    (hS : ∀ n ∈ S, IsUnit (n : B))
    (hsurj : ∀ b : B, ∃ n ∈ S, ∃ g : ℤ[X], b * (n : B) = Polynomial.aeval ζ g)
    (β : B →+* R) (z' : R') (hz : π z' = β ζ) (hz' : Polynomial.aeval z' f = 0) :
    ∃ β' : B →+* R', π.comp β' = β := by
  let φ : AdjoinRoot f →+* B := AdjoinRoot.lift (algebraMap ℤ B) ζ h0
  let α : AdjoinRoot f →+* R' := AdjoinRoot.lift (algebraMap ℤ R') z' hz'
  have hφ : ∀ g : ℤ[X], φ (AdjoinRoot.mk f g) = Polynomial.aeval ζ g := fun g =>
    AdjoinRoot.lift_mk _ _
  have hα : ∀ g : ℤ[X], α (AdjoinRoot.mk f g) = Polynomial.aeval z' g := fun g =>
    AdjoinRoot.lift_mk _ _
  letI : Algebra (AdjoinRoot f) B := φ.toAlgebra
  have halg : algebraMap (AdjoinRoot f) B = φ := rfl
  let S' : Submonoid (AdjoinRoot f) := S.map (Nat.castRingHom (AdjoinRoot f))
  haveI : IsLocalization S' B := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun b => ?_, fun {a c} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, n, hn, rfl⟩
      simpa using hS n hn
    · obtain ⟨n, hn, g, hg⟩ := hsurj b
      refine ⟨(AdjoinRoot.mk f g, ⟨_, n, hn, rfl⟩), ?_⟩
      simp only [halg, hφ]
      simpa using hg
    · obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨c, rfl⟩ := AdjoinRoot.mk_surjective c
      rw [halg, hφ, hφ, ← sub_eq_zero, ← map_sub] at h
      rw [AdjoinRoot.mk_eq_mk.mpr (hinj _ h)]
  have hu : ∀ y : S', IsUnit (α y) := by
    rintro ⟨_, n, hn, rfl⟩
    refine isUnit_of_isUnit_map_of_ker_sq_eq_bot π hs hk _ ?_
    simpa using (hS n hn).map β
  refine ⟨IsLocalization.lift hu, IsLocalization.ringHom_ext S' ?_⟩
  refine RingHom.ext fun a => ?_
  obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
  simp only [RingHom.comp_apply, IsLocalization.lift_eq]
  rw [halg, hφ, hα, ringHom_aeval_eq_aeval_apply, ringHom_aeval_eq_aeval_apply, hz]

private def liftZP_S (p : ℕ) : Submonoid ℕ where
  carrier := {n | n ≠ 0 ∧ n.Coprime p}
  mul_mem' := fun ha hb => ⟨mul_ne_zero ha.1 hb.1, Nat.Coprime.mul_left ha.2 hb.2⟩
  one_mem' := ⟨one_ne_zero, Nat.coprime_one_left p⟩

private theorem isUnit_natCast_of_mem_denominators (p M n : ℕ) (hn : n ∈ liftZP_S p) : IsUnit (n : ZP p M) := by
  have hmem : (n : ℂ)⁻¹ ∈ ZP p M := Subring.subset_closure (Or.inr ⟨n, hn.2, rfl⟩)
  refine IsUnit.of_mul_eq_one (⟨_, hmem⟩ : ZP p M) (Subtype.ext ?_)
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.1
  simp [this]

private theorem exists_mul_eq_aeval_zeta_of_mem (p M : ℕ) (x : ℂ) (hx : x ∈ ZP p M) :
    ∃ n ∈ liftZP_S p, ∃ g : ℤ[X], x * (n : ℂ) = Polynomial.aeval (zeta M) g := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨n, hn, rfl⟩
    · exact ⟨1, one_mem _, Polynomial.X, by simpa using hx⟩
    · by_cases h : n = 0
      · exact ⟨1, one_mem _, 0, by simp [h]⟩
      · have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
        exact ⟨n, ⟨h, hn⟩, 1, by simp [this]⟩
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | one => exact ⟨1, one_mem _, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * (m : ℤ[X]) + k * (n : ℤ[X]), ?_⟩
    simp only [map_add (f := _), map_mul, map_natCast, Nat.cast_mul, ← hg, ← hk]
    ring
  | neg x _ hx =>
    obtain ⟨n, hn, g, hg⟩ := hx
    exact ⟨n, hn, -g, by rw [map_neg, ← hg, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * k, ?_⟩
    simp only [map_mul, Nat.cast_mul, ← hg, ← hk]
    ring

theorem zp_lift_sqZero :
  (∀ (p M : ℕ) (R' R : Type) [CommRing R'] [CommRing R] (π : R' →+* R), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → M.Coprime p → M ≠ 0 →
    ∀ β : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M →+* R, ∃ β' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ZP p M →+* R', π.comp β' = β) := by
  intro p M R' R _ _ π hs hk hMp hM β
  have hprim : IsPrimitiveRoot (zeta M) M := Complex.isPrimitiveRoot_exp M hM
  have hmin : cyclotomic M ℤ = minpoly ℤ (zeta M) :=
    cyclotomic_eq_minpoly hprim (Nat.pos_of_ne_zero hM)
  have hcoe : ∀ g : ℤ[X], ((Polynomial.aeval (zetaZP p M) g : ZP p M) : ℂ)
      = Polynomial.aeval (zeta M) g := fun g => ringHom_aeval_eq_aeval_apply (ZP p M).subtype g _
  have h0 : Polynomial.aeval (zetaZP p M) (cyclotomic M ℤ) = 0 := by
    apply Subtype.ext
    rw [hcoe, hmin]
    exact minpoly.aeval _ _
  have hβ0 : Polynomial.aeval (β (zetaZP p M)) (cyclotomic M ℤ) = 0 := by
    rw [← ringHom_aeval_eq_aeval_apply, h0, map_zero]
  have hMu : IsUnit (M : R) := by simpa using (isUnit_natCast_of_mem_denominators p M M ⟨hM, hMp⟩).map β
  obtain ⟨z', hz, hz'⟩ := exists_root_lift_of_ker_sq_eq_bot π hs hk _ _ hβ0 (isUnit_aeval_derivative_cyclotomic M hM hMu _ hβ0)
  refine lift_squareZero_general π hs hk (cyclotomic M ℤ) (zetaZP p M) (liftZP_S p) h0 ?_
    (isUnit_natCast_of_mem_denominators p M) ?_ β z' hz hz'
  · intro g hg
    rw [hmin]
    refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral (Nat.pos_of_ne_zero hM)) ?_
    rw [← hcoe, hg]
    rfl
  · intro b
    obtain ⟨n, hn, g, hg⟩ := exists_mul_eq_aeval_zeta_of_mem p M b b.2
    exact ⟨n, hn, g, Subtype.ext (by rw [hcoe, ← hg]; simp)⟩

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelLift

private theorem formallySmooth_stalk {B : CommRingCat.{0}} {X : Scheme.{0}} (s : X ⟶ Spec B) [Smooth s] (y : X) :
    ∃ α : B ⟶ X.presheaf.stalk y, α.hom.FormallySmooth ∧ Spec.map α = X.fromSpecStalk y ≫ s := by
  let τ : B ⟶ (Spec B).presheaf.stalk (s y) := StructureSheaf.toStalk B (s y)
  refine ⟨τ ≫ s.stalkMap y, ?_, ?_⟩
  · have hs : (s.stalkMap y).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp (s.smoothLocus_eq_top.ge (Set.mem_univ y))
    letI : Algebra B ((Spec B).presheaf.stalk (s y)) := StructureSheaf.stalkAlgebra B (s y)
    have := (s y).isPrime
    have : IsLocalization.AtPrime ((Spec B).presheaf.stalk (s y)) (s y).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk B (s y)
    have h₀ : Algebra.FormallySmooth B ((Spec B).presheaf.stalk (s y)) :=
      Algebra.FormallySmooth.of_isLocalization (s y).asIdeal.primeCompl
    exact RingHom.FormallySmooth.comp (RingHom.formallySmooth_algebraMap.2 h₀) hs
  · have e : (Spec B).fromSpecStalk (s y) = Spec.map τ := Spec.fromSpecStalk_eq' _ _
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk, e]

private theorem ring_lift {B A O R' : Type} [CommRing B] [CommRing A] [CommRing O] [CommRing R'] (α : B →+* A)
    (hα : α.FormallySmooth) (π : R' →+* O) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (β' : B →+* R') (χ : A →+* O) (hc : χ.comp α = π.comp β') :
    ∃ χ' : A →+* R', π.comp χ' = χ ∧ χ'.comp α = β' := by
  letI := α.toAlgebra
  letI := β'.toAlgebra
  letI := (π.comp β').toAlgebra
  haveI : Algebra.FormallySmooth B A := hα
  let π₁ : R' →ₐ[B] O := { π with commutes' := fun _ => rfl }
  let χ₁ : A →ₐ[B] O := { χ with commutes' := fun b => RingHom.congr_fun hc b }
  have hn : IsNilpotent (RingHom.ker (π₁ : R' →+* O)) := ⟨2, hk⟩
  refine ⟨(Algebra.FormallySmooth.liftOfSurjective χ₁ π₁ hs hn : A →+* R'), RingHom.ext fun a => ?_,
    RingHom.ext fun b => (Algebra.FormallySmooth.liftOfSurjective χ₁ π₁ hs hn).commutes b⟩
  exact Algebra.FormallySmooth.liftOfSurjective_apply χ₁ π₁ hs hn a

private theorem point_lift {B O R' : Type} [CommRing B] [CommRing O] [IsLocalRing O] [CommRing R'] {X : Scheme.{0}}
    (s : X ⟶ Geo.Tor.Sp B) [Smooth s] (π : R' →+* O) (hs : Function.Surjective π) (hk : RingHom.ker π ^ 2 = ⊥)
    (β' : B →+* R') (f : Geo.Tor.Sp O ⟶ X) (hf : f ≫ s = Geo.Tor.spMap (π.comp β')) :
    ∃ f' : Geo.Tor.Sp R' ⟶ X, f' ≫ s = Geo.Tor.spMap β' ∧ Geo.Tor.spMap π ≫ f' = f := by
  obtain ⟨α, hα, e⟩ := formallySmooth_stalk s (f (IsLocalRing.closedPoint O))
  have hχ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of O) f
  have hc : α ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of O) f = CommRingCat.ofHom (π.comp β') := by
    apply Spec.map_injective
    rw [Spec.map_comp, e, ← Category.assoc, hχ, hf]
  obtain ⟨χ', h₁, h₂⟩ := ring_lift α.hom hα π hs hk β' (Scheme.stalkClosedPointTo (R := CommRingCat.of O) f).hom
    (congrArg (fun g => g.hom) hc)
  refine ⟨Spec.map (CommRingCat.ofHom χ') ≫ X.fromSpecStalk _, ?_, ?_⟩
  · rw [Category.assoc, ← e, ← Spec.map_comp, ← h₂]
    rfl
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h₁]
    exact hχ

theorem exists_principal_lift : ∀ (h p M : ℕ) (Ag : Geo.Tor.SiegelFamily h p M), GlobalTheory.ZM.SRep Ag → M.Coprime p → M ≠ 0 → ∀ (O R' : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CommRing R'] (π : R' →+* O), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ β : Geo.Tor.ZP p M →+* O, Function.Injective β → ∀ c : Geo.Tor.SiegPre h M (Geo.Tor.zetaZP p M) (Geo.Tor.spMap β), c.Principal → ∃ (β' : Geo.Tor.ZP p M →+* R') (c' : Geo.Tor.SiegPre h M (Geo.Tor.zetaZP p M) (Geo.Tor.spMap β')), c'.Principal ∧ Geo.Tor.SiegPB c c' (Geo.Tor.spMap π) := by
  intro h p M Ag hA hMp hM O R' _ _ _ _ π hs hk β hβ c hc
  have hd : Dense {x : Geo.Tor.Sp O | (Geo.Tor.spMap β x).asIdeal = ⊥} := by
    have h0 : Dense ({(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)} : Set (PrimeSpectrum O)) := by
      rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
      exact PrimeSpectrum.zeroLocus_bot
    refine h0.mono ?_
    rintro _ rfl
    exact (RingHom.injective_iff_ker_eq_bot β).1 hβ
  obtain ⟨f, hf, hcf⟩ := hA.2 _ _ c inferInstance hd hc
  obtain ⟨β', rfl⟩ := GlobalTheory.zp_lift_sqZero p M R' O π hs hk hMp hM β
  have : Smooth Ag.s := have := Ag.smooth; SmoothOfRelativeDimension.smooth (h * (h + 1) / 2) _
  obtain ⟨f', hf', e⟩ := point_lift Ag.s π hs hk β' f hf
  obtain ⟨⟨c', hc'⟩, hp⟩ := GlobalTheory.siegPre_pullback h M _ _ _ _ _ _ f' Ag.univ hf'
  exact ⟨β', c', hp c' hc' Ag.princ, GlobalTheory.SiegelPullComp.pb_cancel hc' (by rw [e]; exact hcf)⟩

end GlobalTheory.SiegelLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsZpRingHomIntegers
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
open Polynomial

private theorem zpMap_map_aeval {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (f : ℤ[X]) (x : R') : π (Polynomial.aeval x f) = Polynomial.aeval (π x) f :=
  (Polynomial.aeval_algHom_apply π.toIntAlgHom x f).symm

private theorem zpMap_general {B R : Type} [CommRing B] [CommRing R]
    (f : ℤ[X]) (ζ : B) (S : Submonoid ℕ) (h0 : Polynomial.aeval ζ f = 0)
    (hinj : ∀ g : ℤ[X], Polynomial.aeval ζ g = 0 → f ∣ g)
    (hS : ∀ n ∈ S, IsUnit (n : B))
    (hsurj : ∀ b : B, ∃ n ∈ S, ∃ g : ℤ[X], b * (n : B) = Polynomial.aeval ζ g)
    (hS' : ∀ n ∈ S, IsUnit (n : R)) (z : R) (hz : Polynomial.aeval z f = 0) :
    ∃ β : B →+* R, β ζ = z := by
  let φ : AdjoinRoot f →+* B := AdjoinRoot.lift (algebraMap ℤ B) ζ h0
  let α : AdjoinRoot f →+* R := AdjoinRoot.lift (algebraMap ℤ R) z hz
  have hφ : ∀ g : ℤ[X], φ (AdjoinRoot.mk f g) = Polynomial.aeval ζ g := fun g =>
    AdjoinRoot.lift_mk _ _
  have hα : ∀ g : ℤ[X], α (AdjoinRoot.mk f g) = Polynomial.aeval z g := fun g =>
    AdjoinRoot.lift_mk _ _
  letI : Algebra (AdjoinRoot f) B := φ.toAlgebra
  have halg : algebraMap (AdjoinRoot f) B = φ := rfl
  let S' : Submonoid (AdjoinRoot f) := S.map (Nat.castRingHom (AdjoinRoot f))
  haveI : IsLocalization S' B := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun b => ?_, fun {a c} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, n, hn, rfl⟩
      simpa using hS n hn
    · obtain ⟨n, hn, g, hg⟩ := hsurj b
      refine ⟨(AdjoinRoot.mk f g, ⟨_, n, hn, rfl⟩), ?_⟩
      simp only [halg, hφ]
      simpa using hg
    · obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨c, rfl⟩ := AdjoinRoot.mk_surjective c
      rw [halg, hφ, hφ, ← sub_eq_zero, ← map_sub] at h
      rw [AdjoinRoot.mk_eq_mk.mpr (hinj _ h)]
  have hu : ∀ y : S', IsUnit (α y) := by
    rintro ⟨_, n, hn, rfl⟩
    simpa using hS' n hn
  refine ⟨IsLocalization.lift hu, ?_⟩
  have h1 : ζ = algebraMap (AdjoinRoot f) B (AdjoinRoot.mk f Polynomial.X) := by
    rw [halg, hφ, Polynomial.aeval_X]
  rw [h1, IsLocalization.lift_eq, hα, Polynomial.aeval_X]

private def zpMap_S (p : ℕ) : Submonoid ℕ where
  carrier := {n | n ≠ 0 ∧ n.Coprime p}
  mul_mem' := fun ha hb => ⟨mul_ne_zero ha.1 hb.1, Nat.Coprime.mul_left ha.2 hb.2⟩
  one_mem' := ⟨one_ne_zero, Nat.coprime_one_left p⟩

private theorem zpMap_isUnit (p M n : ℕ) (hn : n ∈ zpMap_S p) : IsUnit (n : Geo.Tor.ZP p M) := by
  have hmem : (n : ℂ)⁻¹ ∈ Geo.Tor.ZP p M := Subring.subset_closure (Or.inr ⟨n, hn.2, rfl⟩)
  refine IsUnit.of_mul_eq_one (⟨_, hmem⟩ : Geo.Tor.ZP p M) (Subtype.ext ?_)
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.1
  simp [this]

private theorem zpMap_surj (p M : ℕ) (x : ℂ) (hx : x ∈ Geo.Tor.ZP p M) :
    ∃ n ∈ zpMap_S p, ∃ g : ℤ[X],
      x * (n : ℂ) = Polynomial.aeval ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) g := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨n, hn, rfl⟩
    · exact ⟨1, one_mem _, Polynomial.X, by simpa [Geo.Tor.zetaZP] using hx⟩
    · by_cases h : n = 0
      · exact ⟨1, one_mem _, 0, by simp [h]⟩
      · have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
        exact ⟨n, ⟨h, hn⟩, 1, by simp [this]⟩
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | one => exact ⟨1, one_mem _, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * (m : ℤ[X]) + k * (n : ℤ[X]), ?_⟩
    simp only [map_add (f := _), map_mul, map_natCast, Nat.cast_mul, ← hg, ← hk]
    ring
  | neg x _ hx =>
    obtain ⟨n, hn, g, hg⟩ := hx
    exact ⟨n, hn, -g, by rw [map_neg, ← hg, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * k, ?_⟩
    simp only [map_mul, Nat.cast_mul, ← hg, ← hk]
    ring

private theorem zpMap_unit (p : ℕ) (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ) (hn : n.Coprime p) : IsUnit (n : O) := by
  have hp : (p : O) ∈ Ideal.jacobson (⊥ : Ideal O) :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(p : O)}) (Ideal.subset_span rfl)
  have hc : IsCoprime (n : O) (p : O) := Nat.Coprime.cast hn
  obtain ⟨a, b, hab⟩ := hc
  have hu := Ideal.mem_jacobson_bot.mp hp (-b)
  have : (p : O) * -b + 1 = a * n := by rw [← hab]; ring
  rw [this] at hu
  exact isUnit_of_mul_isUnit_right hu

private theorem zpMap_main (p : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    [IsAdicComplete (Ideal.span {(p : O)}) O] (M : ℕ) (hM : M ≠ 0) (hMp : M.Coprime p) :
    ∃ β : Geo.Tor.ZP p M →+* O, Function.Injective β ∧ IsUnit (M : O) ∧
      ∀ (k : Type) [Field k] (gk : O →+* k), IsPrimitiveRoot (gk (β (Geo.Tor.zetaZP p M))) M := by
  have hpos : 0 < M := Nat.pos_of_ne_zero hM
  haveI : NeZero M := ⟨hM⟩
  have hprim : IsPrimitiveRoot ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) M :=
    Complex.isPrimitiveRoot_exp M hM
  have hmin := cyclotomic_eq_minpoly hprim hpos
  have hcoe : ∀ g : ℤ[X], ((Polynomial.aeval (Geo.Tor.zetaZP p M) g : Geo.Tor.ZP p M) : ℂ)
      = Polynomial.aeval ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) g :=
    fun g => zpMap_map_aeval (Geo.Tor.ZP p M).subtype g _
  have h0 : Polynomial.aeval (Geo.Tor.zetaZP p M) (cyclotomic M ℤ) = 0 := by
    apply Subtype.ext
    rw [hcoe, hmin]
    exact minpoly.aeval _ _
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C M
  have hvw : v w ≤ 1 := by
    have h1 : v w ^ M = 1 := by rw [← map_pow, hw.pow_eq_one, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le hM).mp h1).le
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvw
  have hminw := cyclotomic_eq_minpoly hw hpos
  have hz : Polynomial.aeval z (cyclotomic M ℤ) = 0 := by
    apply hv.hom_inj
    rw [zpMap_map_aeval, map_zero, hminw]
    exact minpoly.aeval _ _
  have hsurj : ∀ b : Geo.Tor.ZP p M, ∃ n ∈ zpMap_S p, ∃ g : ℤ[X],
      b * (n : Geo.Tor.ZP p M) = Polynomial.aeval (Geo.Tor.zetaZP p M) g := by
    intro b
    obtain ⟨n, hn, g, hg⟩ := zpMap_surj p M b b.2
    exact ⟨n, hn, g, Subtype.ext (by rw [hcoe, ← hg]; simp)⟩
  obtain ⟨β, hβ⟩ := zpMap_general (cyclotomic M ℤ) (Geo.Tor.zetaZP p M) (zpMap_S p) h0
    (fun g hg => by
      rw [hmin]
      refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hpos) ?_
      rw [← hcoe, hg]
      rfl)
    (zpMap_isUnit p M) hsurj (fun n hn => zpMap_unit p O n hn.2) z hz
  have hMu : IsUnit (M : O) := zpMap_unit p O M hMp
  refine ⟨β, ?_, hMu, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨n, hn, g, hg⟩ := hsurj b
    have h1 : Polynomial.aeval (algebraMap O C z) g = 0 := by
      rw [← zpMap_map_aeval, ← hβ, ← zpMap_map_aeval, ← hg, map_mul, hb, zero_mul, map_zero]
    have h2 : cyclotomic M ℤ ∣ g := by
      rw [hminw]
      exact minpoly.isIntegrallyClosed_dvd (hw.isIntegral hpos) h1
    obtain ⟨q, rfl⟩ := h2
    rw [map_mul, h0, zero_mul] at hg
    exact ((zpMap_isUnit p M n hn).mul_left_eq_zero).mp hg
  · intro k _ gk
    haveI : NeZero (M : k) := ⟨by simpa using (hMu.map gk).ne_zero⟩
    rw [← isRoot_cyclotomic_iff, hβ, IsRoot.def, ← map_cyclotomic_int, ← algebraMap_int_eq,
      eval_map_algebraMap, ← zpMap_map_aeval, hz, map_zero]

end

theorem exists_zp_ringHom_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (M : ℕ), M ≠ 0 → M.Coprime p → ∃ β : Geo.Tor.ZP p M →+* O, Function.Injective β ∧ IsUnit (M : O) ∧ ∀ (k : Type) [Field k] (gk : O →+* k), IsPrimitiveRoot (gk (β (Geo.Tor.zetaZP p M))) M := by
  intro p _ C _ _ _ v O _ _ hv _ _ M hM hMp
  exact zpMap_main p C v O hv M hM hMp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianLift

private theorem exists_odd_prime_ne (p : ℕ) : ∃ n : ℕ, n.Prime ∧ Odd n ∧ n ≠ p := by
  by_cases h : p = 3
  · exact ⟨5, by norm_num, by decide, by omega⟩
  · exact ⟨3, by norm_num, by decide, fun e => h e.symm⟩

theorem exists_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → 1 ≤ P.g → ∀ (R' : Type) [CommRing R'] (π : R' →+* O), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∃ (G : Over (Spec (CommRingCat.of R'))) (_ : GrpObj G) (_ : IsCommMonObj G) (Q : LB (G ⊗ G).left) (ψ : P.A.left ⟶ G.left) (ψ₂ : (P.A ⊗ P.A).left ⟶ (G ⊗ G).left), IsAbelianScheme G ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (Q.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) ∧ Geo.Tor.LBIso Q (Q.pull (lift (snd G G) (fst G G)).left) ∧ Out.RelAmple G (Q.pull (lift (𝟙 G) (𝟙 G)).left) ∧ (∀ (Z : Over (Spec (CommRingCat.of R'))) (x : Z ⟶ G), (∃ t : (Q.pull (lift (snd G Z ≫ x) (fst G Z)).left).Gen, t.IsGen) → x = 1) ∧ Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom π)) ψ ∧ Geo.Tor.IsSquare ψ ψ₂ ∧ Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) := by
  intro p _ C _ _ _ v O _ _ hv _ _ T _ _ P₀ io P φ hφ hL hg h1 R' _ π hπ hker
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have : IsDomain O := hinj.isDomain _
  have : IsLocalRing O := by
    have : ValuationRing O := ValuationRing.of_integers v hv
    infer_instance
  obtain ⟨n, hn, hodd, hnp⟩ := exists_odd_prime_ne p
  obtain ⟨j, hj⟩ := GlobalTheory.ZM.SiegelLargeLevel.exists_siegelFamily_sRep GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1
    GlobalTheory.AbLaw.CubeAssembly.cube_gen GlobalTheory.thetaUnifAV_all P.g n h1 hn hodd
  obtain ⟨Ag, hAg⟩ := hj j le_rfl p hp hnp
  have hM0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  have hcop : ((n ^ j) ^ 2).Coprime p :=
    Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _ ((Nat.coprime_primes hn hp).2 hnp))
  generalize (n ^ j) ^ 2 = M at Ag hAg hM0 hcop
  obtain ⟨β, hβ, hMu, hprim⟩ := GlobalTheory.exists_zp_ringHom_integers p C v O hv M hM0 hcop
  have hζ : β (Geo.Tor.zetaZP p M) ^ M = 1 := hinj (by
    rw [map_pow, map_one]; exact (hprim C (algebraMap O C)).pow_eq_one)
  let ze : Oˣ := (IsUnit.of_pow_eq_one hζ hM0).unit
  have hze : (ze : O) = β (Geo.Tor.zetaZP p M) := rfl
  obtain ⟨lev, hl₁, hl₂, hl₃⟩ := GlobalTheory.exists_level_over_integers p C v O hv T P₀ io P φ hφ hL hg P.g M ze rfl hMu
    (hprim C (algebraMap O C))
  obtain ⟨c, e, he, hc, hcP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre O T P₀ io P φ hφ hL hg _ β P.g M (Geo.Tor.zetaZP p M) ze lev rfl hMu hze
    hprim hl₁ hl₂ hl₃
  obtain ⟨β', c', hc', φ₁, φ₂, hpb, hsq, hiso, -⟩ :=
    GlobalTheory.SiegelLift.exists_principal_lift P.g p M Ag hAg hcop hM0 O R' π hπ hker β hβ c hc
  let k : P.A ⊗ P.A ⟶ c.A ⊗ c.A := lift (fst P.A P.A ≫ e.inv) (snd P.A P.A ≫ e.inv)
  have hk : k.left ≫ (lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [k]
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  refine ⟨c'.A, c'.grp, c'.comm, c'.P, e.inv.left ≫ φ₁, k.left ≫ φ₂, c'.ab, c'.isLB, c'.rig₁, c'.rig₂, c'.symm,
    hc'.1, hc'.2, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact ((Geo.Tor.isGrpPullback_of_iso e.symm).comp hpb).congr (Category.id_comp _) rfl
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd]
  · have hA : Geo.Tor.LBIso (abelian₂ P.A P.L) (c.P.pull k.left) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullSec _ _ k.left hk) (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        hcP.symm
    have hB : Geo.Tor.LBIso (c.P.pull k.left) (c'.P.pull (k.left ≫ φ₂)) :=
      Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull c.P k.left k.left rfl)
        (Geo.Tor.chartPullSame c'.P _ (fun _ => φ₂) _ k.left fun _ => rfl) hiso
    exact Geo.Tor.LBIso.trans (DVR.linComb_isLB _ P.isLB _ _) (DVR.linComb_isLB _ c.isLB _ _)
      (DVR.linComb_isLB _ c'.isLB _ _) hA hB

end GlobalTheory.AbelianLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_principally_polarised_abelian_square_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* O) (P : Out.PolAV (Geo.Tor.Sp O)) (φ : P.A.left ⟶ P₀.A.left), Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ → Geo.Tor.LBIso P.L (P₀.L.pull φ) → P.g = P₀.g → 1 ≤ P.g → ∀ (R' : Type) [CommRing R'] (π : R' →+* O), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∃ (G : Over (Spec (CommRingCat.of R'))) (_ : GrpObj G) (_ : IsCommMonObj G) (Q : LB (G ⊗ G).left) (ψ : P.A.left ⟶ G.left) (ψ₂ : (P.A ⊗ P.A).left ⟶ (G ⊗ G).left), IsAbelianScheme G ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (Q.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) ∧ Geo.Tor.LBIso Q (Q.pull (lift (snd G G) (fst G G)).left) ∧ Out.RelAmple G (Q.pull (lift (𝟙 G) (𝟙 G)).left) ∧ (∀ (Z : Over (Spec (CommRingCat.of R'))) (x : Z ⟶ G), (∃ t : (Q.pull (lift (snd G Z ≫ x) (fst G Z)).left).Gen, t.IsGen) → x = 1) ∧ Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom π)) ψ ∧ Geo.Tor.IsSquare ψ ψ₂ ∧ Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) := by
  first | exact @GlobalTheory.AbelianLift.exists_lift | exact GlobalTheory.AbelianLift.exists_lift | (intros; apply GlobalTheory.AbelianLift.exists_lift <;> assumption)
end
