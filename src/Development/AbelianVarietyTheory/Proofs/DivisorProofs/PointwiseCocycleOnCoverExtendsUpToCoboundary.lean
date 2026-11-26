module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleLocalSectionsGlueBasicOpenCoverStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPointwiseOneCocycleOpenCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyAwayNatural
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulEqZero
namespace GlobalTheory.CocycleCoboundaryNumerator

theorem exists_numerator (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (u v : D)
    (f : (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E)
    (hf : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ u) → IsUnit (ψ v) →
        f E' (θ.comp ψ) = θ (f E ψ)) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ u) → IsUnit (ψ v) → f E ψ * (ψ u * ψ v) ^ N = ψ c := by
  classical
  let L := Localization.Away (u * v)
  let ψ₀ : D →ₐ[R] L := IsScalarTower.toAlgHom R D L
  have hψ₀ : IsUnit (ψ₀ u * ψ₀ v) := by
    rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (u * v)
  obtain ⟨⟨a, _, k, rfl⟩, hk⟩ := IsLocalization.surj (Submonoid.powers (u * v)) (f L ψ₀)
  refine ⟨k, fun N hN => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨a * (u * v) ^ j, fun E _ _ ψ hu hv => ?_⟩
  have huv : IsUnit (ψ (u * v)) := by rw [map_mul]; exact hu.mul hv
  let θ : L →ₐ[R] E := IsLocalization.Away.liftAlgHom (u * v) huv
  have hθ : ∀ x : D, θ (algebraMap D L x) = ψ x := fun x =>
    IsLocalization.Away.lift_eq (u * v) huv x
  have hcomp : θ.comp ψ₀ = ψ := AlgHom.ext fun x => hθ x
  have key := hf L E ψ₀ θ (isUnit_of_mul_isUnit_left hψ₀) (isUnit_of_mul_isUnit_right hψ₀)
  rw [hcomp] at key
  have hk' := congrArg θ hk
  simp only [map_mul, hθ] at hk'
  rw [key, map_mul, ← hk']
  simp only [map_pow, map_mul]
  ring

theorem exists_pow_mul_eq_zero (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D]
    (u x : D)
    (h : ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ u) → ψ x = 0) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → u ^ M * x = 0 := by
  let L := Localization.Away u
  have h0 : algebraMap D L x = 0 :=
    h L (IsScalarTower.toAlgHom R D L) (IsLocalization.Away.algebraMap_isUnit u)
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers u) L x).mp h0
  refine ⟨m, fun M hM => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hm' : u ^ m * x = 0 := hm
  rw [pow_add, mul_comm (u ^ m), mul_assoc, hm', mul_zero]

theorem map_inverse_of_isUnit {E E' : Type} [CommRing E] [CommRing E'] (θ : E →+* E') {x : E}
    (hx : IsUnit x) : Ring.inverse (θ x) = θ (Ring.inverse x) := by
  obtain ⟨w, rfl⟩ := hx
  have hw : θ (w : E) = ((Units.map θ.toMonoidHom w : E'ˣ) : E') := rfl
  rw [Ring.inverse_unit, hw, Ring.inverse_unit]
  rfl

theorem cocycle_is_coboundary (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D]
    (n : ℕ) (s : Fin n → D) (hs : Ideal.span (Set.range s) = ⊤)
    (d : Fin n → Fin n → (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E)
    (hnat : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
      [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) →
        d a b E' (AlgHom.comp θ ψ) = θ (d a b E ψ))
    (hcoc : ∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) →
        d a b E ψ + d b c E ψ = d a c E ψ) :
    ∃ (e : Fin n → (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E),
      (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
        [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
          e a E' (AlgHom.comp θ ψ) = θ (e a E ψ)) ∧
      ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  classical

  have h1 : ∀ a b : Fin n, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : D, ∀ (E : Type) [CommRing E]
      [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) →
        d a b E ψ * (ψ (s a) * ψ (s b)) ^ N = ψ c := fun a b =>
    exists_numerator R D (s a) (s b) (d a b) (fun E _ _ E' _ _ ψ θ ha hb => hnat a b E E' ψ θ ha hb)
  choose N₀ hN₀ using h1
  obtain ⟨N, hN⟩ : ∃ N, ∀ a b, N₀ a b ≤ N :=
    ⟨Finset.univ.sup (fun p : Fin n × Fin n => N₀ p.1 p.2), fun a b =>
      Finset.le_sup (f := fun p : Fin n × Fin n => N₀ p.1 p.2) (Finset.mem_univ (a, b))⟩
  choose c hc using fun a b => hN₀ a b N (hN a b)

  have h2 : ∀ a b k : Fin n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → (s a * s b * s k) ^ M *
      (s k ^ N * c a b - s a ^ N * c k b + s b ^ N * c k a) = 0 := by
    intro a b k
    apply exists_pow_mul_eq_zero R D
    intro E _ _ ψ hu
    rw [map_mul, map_mul] at hu
    have ha := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)
    have hb := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)
    have hk := isUnit_of_mul_isUnit_right hu
    have e4 := hcoc k a b E ψ hk ha hb
    simp only [map_add (f := _), map_sub, map_mul, map_pow]
    rw [← hc a b E ψ ha hb, ← hc k b E ψ hk hb, ← hc k a E ψ hk ha]
    linear_combination (ψ (s a) * ψ (s b) * ψ (s k)) ^ N * e4
  choose M₀ hM₀ using h2
  obtain ⟨M, hM⟩ : ∃ M, ∀ a b k, M₀ a b k ≤ M :=
    ⟨Finset.univ.sup (fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2), fun a b k =>
      Finset.le_sup (f := fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2)
        (Finset.mem_univ (a, b, k))⟩

  obtain ⟨K, c', hc', hy⟩ : ∃ (K : ℕ) (c' : Fin n → Fin n → D),
      (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ * (ψ (s a) * ψ (s b)) ^ K = ψ (c' a b)) ∧
      ∀ a b k, s k ^ K * c' a b = s a ^ K * c' k b - s b ^ K * c' k a := by
    refine ⟨N + M, fun a b => c a b * (s a * s b) ^ M, fun a b E _ _ ψ ha hb => ?_,
      fun a b k => ?_⟩
    · rw [map_mul, ← hc a b E ψ ha hb, map_pow, map_mul, pow_add]
      ring
    · linear_combination hM₀ a b k M (hM a b k)

  have hsK : Ideal.span (Set.range fun i => s i ^ K) = ⊤ := by
    have h := Ideal.span_pow_eq_top _ hs K
    rw [← Set.range_comp] at h
    exact h
  have h1mem : (1 : D) ∈ Ideal.span (Set.range fun i => s i ^ K) := by
    rw [hsK]; exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun D).mp h1mem
  refine ⟨fun a E _ _ ψ => ∑ k, ψ (g k * c' k a) * Ring.inverse (ψ (s a)) ^ K, ?_, ?_⟩
  · intro a E _ _ E' _ _ ψ θ ha
    have hinv : Ring.inverse (θ (ψ (s a))) = θ (Ring.inverse (ψ (s a))) :=
      map_inverse_of_isUnit (θ : E →+* E') ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hinv]
    simp only [map_mul, map_pow]
  · intro a b E _ _ ψ ha hb
    have hAK : ψ (s a) ^ K * Ring.inverse (ψ (s a)) ^ K = 1 := by
      rw [← mul_pow, Ring.mul_inverse_cancel _ ha, one_pow]
    have hBK : ψ (s b) ^ K * Ring.inverse (ψ (s b)) ^ K = 1 := by
      rw [← mul_pow, Ring.mul_inverse_cancel _ hb, one_pow]
    have hab := hc' a b E ψ ha hb
    have hsum : ∑ k, ψ (g k) * ψ (s k) ^ K = 1 := by
      have h := congrArg ψ hg
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, smul_eq_mul, map_mul, map_pow, map_one] using h
    have hd : d a b E ψ = ∑ k, ψ (g k) * ψ (s k) ^ K * d a b E ψ := by
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [hd, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hyk := congrArg ψ (hy a b k)
    simp only [map_mul, map_pow, map_sub] at hyk
    simp only [map_mul]
    linear_combination (ψ (g k)) * ((Ring.inverse (ψ (s a)) ^ K * Ring.inverse (ψ (s b)) ^ K) * hyk
      + (ψ (s k) ^ K * Ring.inverse (ψ (s a)) ^ K * Ring.inverse (ψ (s b)) ^ K) * hab
      + (Ring.inverse (ψ (s b)) ^ K * ψ (c' k b)
          - ψ (s k) ^ K * d a b E ψ * ψ (s b) ^ K * Ring.inverse (ψ (s b)) ^ K) * hAK
      - (Ring.inverse (ψ (s a)) ^ K * ψ (c' k a) + ψ (s k) ^ K * d a b E ψ) * hBK)

end GlobalTheory.CocycleCoboundaryNumerator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyAwayNatural
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechAway

theorem cech_one_away_natural : ∀ (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ → ∀ d : Fin n → Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E' (θ.comp ψ) = θ (d a b E ψ)) → (∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) → d a b E ψ + d b c E ψ = d a c E ψ) → ∃ e : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → e a E' (θ.comp ψ) = θ (e a E ψ)) ∧ ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  first
  | exact @_root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary
  | exact _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary
  | (apply _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> assumption)
  | (intros; apply _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary ..)

end GlobalTheory.CechAway
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyAwayNaturalStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_first_cohomology_away_natural : ∀ (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ → ∀ d : Fin n → Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E' (θ.comp ψ) = θ (d a b E ψ)) → (∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) → d a b E ψ + d b c E ψ = d a c E ψ) → ∃ e : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → e a E' (θ.comp ψ) = θ (e a E ψ)) ∧ ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  first | exact @GlobalTheory.CechAway.cech_one_away_natural | exact GlobalTheory.CechAway.cech_one_away_natural | (intros; apply GlobalTheory.CechAway.cech_one_away_natural <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAlgebraPointLiesInCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAlgebraPointLiesInCover
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_away_cover_sm :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ ∧ ∀ a,
          Sm (X := X) W (D := Localization.Away (s a))
            (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x) := by
  intro R _ X K W hW D _ _ x
  let f : Sp D ⟶ X.left := x.left
  let S : Set D := {s | ∃ i, ∀ q : PrimeSpectrum D, q ∈ PrimeSpectrum.basicOpen s → f q ∈ W i}
  have hS : Ideal.span S = ⊤ := by
    by_contra h'
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h'
    let p : PrimeSpectrum D := ⟨m, hm.isPrime⟩
    have hp : f p ∈ (⨆ i, W i) := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨s, rfl⟩, hs, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := f ⁻¹' (W i : Set X.left)) hi ((W i).isOpen.preimage f.continuous)
    have hsS : s ∈ S := ⟨i, fun q hq ↦ hsub hq⟩
    exact hs (hle (Ideal.subset_span hsS))
  have h1 : (1 : D) ∈ Submodule.span D S := by
    change (1 : D) ∈ Ideal.span S; rw [hS]; trivial
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span h1
  refine ⟨T.card, fun a ↦ (T.equivFin.symm a : D), ?_, ?_⟩
  · have hr : Set.range (fun a ↦ (T.equivFin.symm a : D)) = (T : Set D) := by
      ext y; constructor
      · rintro ⟨a, rfl⟩; exact (T.equivFin.symm a).2
      · intro hy; exact ⟨T.equivFin ⟨y, hy⟩, by simp⟩
    rw [hr, Ideal.eq_top_iff_one]; exact hT
  · intro a
    obtain ⟨i, hi⟩ := hTS (T.equivFin.symm a).2
    refine ⟨i, fun q _ ↦ ?_⟩
    have hq : (spMap (algebraMap D (Localization.Away ((T.equivFin.symm a : D)))) q : PrimeSpectrum D) ∈
        PrimeSpectrum.basicOpen ((T.equivFin.symm a : D)) :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away ((T.equivFin.symm a : D))) _).le ⟨q, rfl⟩
    exact hi _ hq

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAlgebraPointLiesInCoverStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_cover_algebraPoint_liesInCover :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ ∧ ∀ a,
          Sm (X := X) W (D := Localization.Away (s a))
            (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x) :=
  GlobalTheory.PtExt.exists_away_cover_sm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPointwiseOneCocycleOpenCover
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PtExt.CocSec

variable {R : Type} [CommRing R]

def liftU {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (t : D) (ψ : D →ₐ[R] E)
    (h : IsUnit (ψ t)) : Localization.Away t →ₐ[R] E :=
  IsLocalization.liftAlgHom (M := Submonoid.powers t) (f := ψ) (by
    rintro ⟨_, m, rfl⟩
    simpa using h.pow m)

theorem liftU_comp {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (t : D)
    (ψ : D →ₐ[R] E) (h : IsUnit (ψ t)) :
    (liftU t ψ h).comp (IsScalarTower.toAlgHom R D (Localization.Away t)) = ψ := by
  ext r
  simp [liftU]

theorem comp_liftU {D E E' : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [CommRing E']
    [Algebra R E'] (t : D) (ψ : D →ₐ[R] E) (h : IsUnit (ψ t)) (θ : E →ₐ[R] E') :
    θ.comp (liftU t ψ h) = liftU t (θ.comp ψ) (h.map θ) := by
  apply IsLocalization.algHom_ext (Submonoid.powers t)
  ext r
  have h1 := DFunLike.congr_fun (liftU_comp t ψ h) r
  have h2 := DFunLike.congr_fun (liftU_comp t (θ.comp ψ) (h.map θ)) r
  simp only [AlgHom.comp_apply] at h1 h2 ⊢
  exact (congrArg θ h1).trans h2.symm

end GlobalTheory.PtExt.CocSec

end


open GlobalTheory.PtExt.CocSec in
theorem GlobalTheory.PtExt.CocSec.exists_section :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u →
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
      ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
        ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
          (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'),
          Sm W (D := E) (spOver ψ ≫ x) →
            σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) := by
  intro R _ X K W hW u hu D _ _ x
  obtain ⟨n, s, hs, hsm⟩ := GlobalTheory.T.exists_basicOpen_cover_algebraPoint_liesInCover R X K W hW D x
  classical
  let k : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E := fun a E _ _ ψ ↦
    if h : IsUnit (ψ (s a)) then
      u (Localization.Away (s a)) E (liftU (s a) ψ h)
        (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x)
    else 0
  have hk : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      k a E' (θ.comp ψ) - θ (k a E ψ) = u E E' θ (spOver ψ ≫ x) := by
    intro a E _ _ E' _ _ ψ θ h
    have h' : IsUnit ((θ.comp ψ) (s a)) := h.map θ
    simp only [k, dif_pos h, dif_pos h']
    rw [← comp_liftU (s a) ψ h θ, hu _ _ _ (liftU (s a) ψ h) θ _ (hsm a), ← Category.assoc,
      spOver_comp, liftU_comp]
    ring
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.cech_first_cohomology_away_natural R D n s hs (fun a b E _ _ ψ ↦ k a E ψ - k b E ψ)
    (fun a b E _ _ E' _ _ ψ θ ha hb ↦ by
      have h1 := hk a E E' ψ θ ha
      have h2 := hk b E E' ψ θ hb
      simp only [map_sub]
      linear_combination h1 - h2)
    (fun a b c E _ _ ψ _ _ _ ↦ by ring)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.pointwiseCocycle_local_sections_glue_basicOpen_cover R X K W u hu D x n s hs (fun a E _ _ ψ ↦ k a E ψ + e a E ψ)
    (fun a E _ _ E' _ _ ψ θ ha ↦ by
      have h1 := hk a E E' ψ θ ha
      have h2 := he1 a E E' ψ θ ha
      simp only [map_add (f := _)]
      linear_combination h1 + h2)
    (fun a b E _ _ ψ ha hb ↦ by
      have h := he2 a b E ψ ha hb
      linear_combination h)
  exact ⟨σ, hσ⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPointwiseOneCocycleOpenCoverStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pointwiseOneCocycle_openCover :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u →
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
          ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
            (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'),
            Sm (D := E) W (spOver ψ ≫ x) →
              σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) :=
  @GlobalTheory.PtExt.CocSec.exists_section
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueElemOfNaturalFamilyOpenCoverPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueElemOfNaturalFamilyOpenCoverPoints
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.NatGlue

variable (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D]

def locMap (s : D) : D →ₐ[R] Localization.Away s := IsScalarTower.toAlgHom R D _

theorem locMap_apply (s x : D) : locMap R s x = algebraMap D (Localization.Away s) x := rfl

def locR (a b : D) : Localization.Away a →ₐ[R] Localization.Away (a * b) :=
  ⟨IsLocalization.Away.awayToAwayRight a b, fun r ↦ by
    have := IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away a) (P := Localization.Away (a * b))
      a b (algebraMap R D r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this⟩

def locL (a b : D) : Localization.Away b →ₐ[R] Localization.Away (a * b) :=
  ⟨IsLocalization.Away.awayToAwayLeft b a, fun r ↦ by
    have := IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away b) (P := Localization.Away (a * b))
      b a (algebraMap R D r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this⟩

theorem locR_apply (a b : D) (x : Localization.Away a) :
    locR R a b x = IsLocalization.Away.awayToAwayRight a b x := rfl

theorem locL_apply (a b : D) (x : Localization.Away b) :
    locL R a b x = IsLocalization.Away.awayToAwayLeft b a x := rfl

theorem locR_comp (a b : D) : (locR R a b).comp (locMap R a) = locMap R (a * b) := by
  ext x
  rw [AlgHom.comp_apply, locR_apply, locMap_apply, locMap_apply]
  exact IsLocalization.Away.awayToAwayRight_eq a b x

theorem locL_comp (a b : D) : (locL R a b).comp (locMap R b) = locMap R (a * b) := by
  ext x
  rw [AlgHom.comp_apply, locL_apply, locMap_apply, locMap_apply]
  exact IsLocalization.Away.awayToAwayLeft_eq b a x

theorem awayMap_comp {E : Type} [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (s : D) :
    (IsScalarTower.toAlgHom R E (Localization.Away (φ s))).comp φ = (Localization.awayMapₐ φ s).comp (locMap R s) := by
  ext x
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, locMap_apply]
  first
    | exact (IsLocalization.Away.map_eq (S := Localization.Away s) (P := Localization.Away (φ s)) s x).symm
    | simp [Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
    | (show _ = IsLocalization.map _ (φ : D →+* E) _ _; exact (IsLocalization.map_eq _ _).symm)

theorem existsUnique_of_natural : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
    ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D)
    (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E),
    (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E)
      (θ : E →ₐ[R] E'), Sm W (D := E) (spOver ψ ≫ y) → τ E' (θ.comp ψ) = θ (τ E ψ)) →
    ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      Sm W (D := E) (spOver ψ ≫ y) → τ E ψ = ψ d := by
  intro R _ X K W hW D _ _ y τ hτ

  let S : Set D := {s | ∃ i, ∀ p : PrimeSpectrum D, p ∈ PrimeSpectrum.basicOpen s → y.left.base p ∈ W i}
  have hS : Ideal.span S = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff', eq_top_iff]
    intro p _
    have hp : y.left.base p ∈ ⨆ i, W i := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    obtain ⟨_, ⟨s, rfl⟩, hps, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := p) (u := (y.left ⁻¹ᵁ W i).carrier) hi (y.left ⁻¹ᵁ W i).isOpen
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨s, ⟨i, fun q hq ↦ hsub hq⟩, hps⟩
  have hψ : ∀ s ∈ S, Sm W (D := Localization.Away s) (spOver (locMap R s) ≫ y) := by
    rintro s ⟨i, hi⟩
    refine ⟨i, fun q _ ↦ hi _ ?_⟩
    show PrimeSpectrum.comap (algebraMap D (Localization.Away s)) q ∈ PrimeSpectrum.basicOpen s
    rw [PrimeSpectrum.mem_basicOpen]
    intro h
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
  have hcomp : ∀ a b : S,
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (a.1 * b.1)) a.1 b.1 (τ (Localization.Away a.1) (locMap R a.1)) =
      IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a.1 * b.1)) b.1 a.1 (τ (Localization.Away b.1) (locMap R b.1)) := by
    intro a b
    have h1 := hτ _ _ (locMap R a.1) (locR R a.1 b.1) (hψ a.1 a.2)
    have h2 := hτ _ _ (locMap R b.1) (locL R a.1 b.1) (hψ b.1 b.2)
    rw [locR_comp] at h1
    rw [locL_comp] at h2
    rw [← locR_apply R, ← locL_apply R, ← h1, ← h2]
  obtain ⟨d, hd, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top S hS
    (fun a ↦ τ (Localization.Away a.1) (locMap R a.1)) hcomp
  refine ⟨d, ?_, fun d' hd' ↦ hu d' fun a ↦ (hd' _ (locMap R a.1) (hψ a.1 a.2)).symm⟩
  intro E _ _ φ hφ
  have hS' : Ideal.span ((φ : D →+* E) '' S) = ⊤ := by
    rw [← Ideal.map_span, hS, Ideal.map_top]
  apply Localization.algebraMap_injective_of_span_eq_top _ hS'
  funext b
  obtain ⟨b, s, hs, rfl⟩ := b
  have h1 := hτ _ _ φ (IsScalarTower.toAlgHom R E (Localization.Away (φ s))) hφ
  have h2 := hτ _ _ (locMap R s) (Localization.awayMapₐ φ s) (hψ s hs)
  rw [awayMap_comp, h2, ← hd ⟨s, hs⟩, ← locMap_apply R, ← AlgHom.comp_apply, ← awayMap_comp] at h1
  exact h1.symm

end GlobalTheory.PtExt.NatGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueElemOfNaturalFamilyOpenCoverPointsStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
    ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D)
    (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E),
    (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (D := E) (spOver ψ ≫ y) →
      τ E' (θ.comp ψ) = θ (τ E ψ)) →
    ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      Sm W (D := E) (spOver ψ ≫ y) → τ E ψ = ψ d := by
  first | exact @GlobalTheory.PtExt.NatGlue.existsUnique_of_natural | exact GlobalTheory.PtExt.NatGlue.existsUnique_of_natural | (intros; apply GlobalTheory.PtExt.NatGlue.existsUnique_of_natural <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleOnCoverExtendsUpToCoboundary
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt.CocExt

theorem sm_comp {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens}
    {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (x : Pt X D)
    (h : Sm W x) : Sm W (D := E) (spOver ψ ≫ x) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun z _ ↦ ?_⟩
  have := hi (Set.mem_univ ((spOver ψ).left.base z))
  simpa [Over.comp_left, Scheme.Hom.comp_base, Scheme.Hom.comp_apply] using this

theorem cocycle_extends : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u → ∃ u' : Fn1 X, IsCoc (whole X) u' ∧ Cohom W u u' := by
  intro R _ X K W hW u hu
  choose σ hσ using GlobalTheory.T.exists_section_pointwiseOneCocycle_openCover R X K W hW u hu
  have uniq : ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D) (d d' : D),
      (∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        Sm W (D := E) (spOver ψ ≫ y) → ψ d = ψ d') → d = d' := by
    intro D _ _ y d d' h
    obtain ⟨e, -, he⟩ := GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints R X K W hW D y (fun E _ _ ψ ↦ ψ d) (fun _ _ _ _ _ _ _ _ _ ↦ rfl)
    exact (he d (fun _ _ _ _ _ ↦ rfl)).trans (he d' (fun E _ _ ψ hψ ↦ h E ψ hψ)).symm
  have hA : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D),
      ∃ d : D', ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E),
        Sm W (D := E) (spOver ψ ≫ spOver φ ≫ x) →
          σ D x E (ψ.comp φ) - σ D' (spOver φ ≫ x) E ψ = ψ d := by
    intro D _ _ D' _ _ φ x
    refine (GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints R X K W hW D' (spOver φ ≫ x)
      (fun E _ _ ψ ↦ σ D x E (ψ.comp φ) - σ D' (spOver φ ≫ x) E ψ) ?_).exists
    intro E _ _ E' _ _ ψ θ hψ
    have e : spOver ψ ≫ spOver φ ≫ x = spOver (ψ.comp φ) ≫ x := by rw [← Category.assoc, spOver_comp]
    have h1 := hσ D x E E' (ψ.comp φ) θ (by rw [← e]; exact hψ)
    have h2 := hσ D' (spOver φ ≫ x) E E' ψ θ hψ
    rw [← e] at h1
    simp only [map_sub]
    rw [show (θ.comp ψ).comp φ = θ.comp (ψ.comp φ) from rfl]
    linear_combination h1 - h2
  choose u' hu' using hA
  refine ⟨u', ?_, ?_⟩
  · intro D _ _ D' _ _ D'' _ _ φ ψ x _
    have e : spOver ψ ≫ spOver φ ≫ x = spOver (ψ.comp φ) ≫ x := by rw [← Category.assoc, spOver_comp]
    apply uniq D'' (spOver (ψ.comp φ) ≫ x)
    intro E _ _ ρ hρ
    have h2 : Sm W (D := E) (spOver (ρ.comp ψ) ≫ spOver φ ≫ x) := by
      rw [← spOver_comp, Category.assoc, e]; exact hρ
    have h3 : Sm W (D := E) (spOver ρ ≫ spOver ψ ≫ spOver φ ≫ x) := by rw [e]; exact hρ
    rw [map_add (f := _), ← AlgHom.comp_apply, ← hu' D D'' (ψ.comp φ) x E ρ hρ, ← hu' D D' φ x E (ρ.comp ψ) h2,
      ← hu' D' D'' ψ (spOver φ ≫ x) E ρ h3, e]
    rw [show (ρ.comp ψ).comp φ = ρ.comp (ψ.comp φ) from rfl]
    ring
  · refine ⟨fun D _ _ x ↦ σ D x D (AlgHom.id R D), ?_⟩
    intro D _ _ D' _ _ φ x hx
    have hx' : Sm W (D := D) (spOver (AlgHom.id R D) ≫ x) := by
      simpa only [spOver_id, Category.id_comp] using hx
    have h1 := hσ D x D D' (AlgHom.id R D) φ hx'
    rw [spOver_id, Category.id_comp, AlgHom.comp_id] at h1
    have hφx : Sm W (D := D') (spOver (AlgHom.id R D') ≫ spOver φ ≫ x) := by
      simpa only [spOver_id, Category.id_comp] using sm_comp φ x hx
    have h2 := hu' D D' φ x D' (AlgHom.id R D') hφx
    rw [AlgHom.id_comp, AlgHom.id_apply] at h2
    show u D D' φ x + -u' D D' φ x = _
    linear_combination h2 - h1

end GlobalTheory.PtExt.CocExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleOnCoverExtendsUpToCoboundaryStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwise_cocycle_on_cover_extends_up_to_coboundary : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u → ∃ u' : Fn1 X, IsCoc (whole X) u' ∧ Cohom W u u' := by
  first | exact @GlobalTheory.PtExt.CocExt.cocycle_extends | exact GlobalTheory.PtExt.CocExt.cocycle_extends | (intros; apply GlobalTheory.PtExt.CocExt.cocycle_extends <;> assumption)
end
