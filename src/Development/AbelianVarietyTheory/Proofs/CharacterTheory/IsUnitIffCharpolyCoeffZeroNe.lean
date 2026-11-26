module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsUnitIffCharpolyCoeffZeroNe
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem _root_.GlobalTheory.CuspGL.ipGL_charpoly_eq_finsum_mass (F : Type) [Field F] [Finite F]
    (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ) (s : F[X] → ℂ) :
    _root_.GlobalTheory.CuspGL.ipGL φ (fun g => s (LinearMap.charpoly g)) =
      ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0},
        _root_.GlobalTheory.CuspGL.mass φ P * star (s P) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) :=
    Finite.of_injective (fun g : Module.End F V => (g : V → V)) DFunLike.coe_injective
  set S := {P : F[X] | P.Monic ∧ P.natDegree = Module.finrank F V ∧ P.coeff 0 ≠ 0} with hS
  set I := S ∩ Set.range (fun g : Module.End F V => LinearMap.charpoly g) with hI
  have hunit : ∀ g : Module.End F V, IsUnit g ↔ LinearMap.charpoly g ∈ S := by
    intro g
    simp only [hS, Set.mem_setOf_eq, LinearMap.charpoly_monic, LinearMap.charpoly_natDegree,
      true_and]
    rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_eq_sign_charpoly_coeff, isUnit_iff_ne_zero]
    simp
  have hset : {g : Module.End F V | IsUnit g} =
      ⋃ P ∈ I, {g : Module.End F V | LinearMap.charpoly g = P} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hI, Set.mem_inter_iff, Set.mem_range,
      exists_prop]
    rw [hunit]
    constructor
    · intro h
      exact ⟨_, ⟨h, g, rfl⟩, rfl⟩
    · rintro ⟨P, ⟨hP, _⟩, rfl⟩
      exact hP
  have hsupp : S ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) =
      I ∩ Function.support (fun P => _root_.GlobalTheory.CuspGL.mass φ P * star (s P)) := by
    ext P
    simp only [hI, Set.mem_inter_iff, Function.mem_support]
    constructor
    · rintro ⟨hPS, hne⟩
      refine ⟨⟨hPS, ?_⟩, hne⟩
      by_contra hr
      apply hne
      have hempty : {g : Module.End F V | LinearMap.charpoly g = P} = ∅ := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hr ⟨g, h⟩
      unfold _root_.GlobalTheory.CuspGL.mass
      simp [hempty]
    · rintro ⟨⟨hPS, _⟩, hne⟩
      exact ⟨hPS, hne⟩
  rw [finsum_mem_inter_support_eq _ S I hsupp]
  unfold _root_.GlobalTheory.CuspGL.ipGL _root_.GlobalTheory.CuspGL.mass
  rw [hset, finsum_mem_biUnion ?_ ((Set.finite_range _).subset Set.inter_subset_right)
    (fun _ _ => Set.toFinite _)]
  · refine finsum_mem_congr rfl fun P _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
      finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [Set.Finite.mem_toFinset] at hg
    show φ g * star (s (LinearMap.charpoly g)) = _
    rw [show LinearMap.charpoly g = P from hg]
  · intro P _ Q _ hPQ
    exact Set.disjoint_left.2 fun g hP hQ => hPQ (hP.symm.trans hQ)

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusCharacterOrthogonality
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusCharacterOrthogonality
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem finsum_rootsOfUnity_pow_mul_star {K : Type} [Field K] (θ : K →* ℂ) {N : ℕ} (hN : 0 < N)
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) (hω : IsPrimitiveRoot (θ ζ) N) (k l : ℕ) :
    ∑ᶠ α ∈ {α : K | α ^ N = 1}, θ α ^ k * star (θ α ^ l) =
      if k ≡ l [MOD N] then ((N : ℕ) : ℂ) else 0 := by
  classical
  set ω := θ ζ with hωdef
  have hNe : N ≠ 0 := hN.ne'
  have : NeZero N := ⟨hNe⟩

  have hset : {α : K | α ^ N = 1} = (fun i : ℕ => ζ ^ i) '' (↑(Finset.range N) : Set ℕ) := by
    ext α
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one h
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hinj : Set.InjOn (fun i : ℕ => ζ ^ i) (↑(Finset.range N) : Set ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hζ.pow_inj hi hj h
  rw [hset, finsum_mem_image hinj, finsum_mem_coe_finset]
  have hnorm : ‖ω‖ = 1 := hω.norm'_eq_one hNe
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hstar : star ω = ω⁻¹ := by
    rw [Complex.inv_eq_conj hnorm]
    rfl

  set u := ω ^ k * (ω ^ l)⁻¹ with hu
  have hterm : ∀ i, θ (ζ ^ i) ^ k * star (θ (ζ ^ i) ^ l) = u ^ i := by
    intro i
    rw [map_pow, star_pow, star_pow, hstar, hu]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hm : ∀ a, ω ^ a = ω ^ (a % N) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
  have huN : u ^ N = 1 := by
    rw [hu, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k N, mul_comm l N, pow_mul, pow_mul,
      hω.pow_eq_one, one_pow, one_pow, inv_one, mul_one]
  split_ifs with hkl
  · have hu1 : u = 1 := by
      rw [hu, hm k, hm l, show k % N = l % N from hkl]
      exact mul_inv_cancel₀ (pow_ne_zero _ hω0)
    simp [hu1]
  · have hu1 : u ≠ 1 := by
      intro h
      have hkl' : ω ^ k = ω ^ l := (mul_inv_eq_one₀ (pow_ne_zero _ hω0)).mp (hu ▸ h)
      apply hkl
      exact hω.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) (by rw [← hm, ← hm]; exact hkl')
    rw [geom_sum_eq hu1, huN, sub_self, zero_div]

theorem torus_orthogonality : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → (∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (Nat.card F ^ n - 1) ∧ IsPrimitiveRoot (θ ζ) (Nat.card F ^ n - 1)) ∧ ∀ k l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, θ α ^ k * star (θ α ^ l) = if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  intro F _ _ θ hθ n hn
  classical
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hqF : ((Nat.card F : ℕ) : F) = 0 := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero F
  set q := Nat.card F with hqdef
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq
  set N := q ^ n - 1 with hNdef
  have hN : 0 < N := by omega

  have hNF : (N : F) ≠ 0 := by
    intro h
    have h1 : ((N + 1 : ℕ) : F) = 0 := by
      rw [show N + 1 = q ^ n by omega, Nat.cast_pow, hqF, zero_pow hn.ne']
    rw [Nat.cast_add, h, zero_add, Nat.cast_one] at h1
    exact one_ne_zero h1
  have : NeZero (N : F) := ⟨hNF⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) N
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'

  have hω : IsPrimitiveRoot (θ ζ) N :=
    ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl =>
      hζ.dvd_of_pow_eq_one l (hθ _ _ (pow_ne_zero _ hζ0) one_ne_zero (by rw [map_pow, hl, map_one]))⟩
  exact ⟨⟨ζ, hζ, hω⟩, fun k l => finsum_rootsOfUnity_pow_mul_star θ hN hζ hω k l⟩

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusCharacterOrthogonalityStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusTorus_character_orthogonality : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n : ℕ, 0 < n → (∃ ζ : AlgebraicClosure F, IsPrimitiveRoot ζ (Nat.card F ^ n - 1) ∧ IsPrimitiveRoot (θ ζ) (Nat.card F ^ n - 1)) ∧ ∀ k l : ℕ, ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, θ α ^ k * star (θ α ^ l) = if k ≡ l [MOD Nat.card F ^ n - 1] then ((Nat.card F ^ n - 1 : ℕ) : ℂ) else 0 := by
  first | exact @GlobalTheory.CuspGL.torus_orthogonality | exact GlobalTheory.CuspGL.torus_orthogonality | (intros; apply GlobalTheory.CuspGL.torus_orthogonality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOne
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOne
open Polynomial

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F]

theorem mangoldtConv_eq_of_dvd_pow {f g : F[X]} (hf : f.Monic) (hf' : Irreducible f) (hg : g.Monic)
    (hg' : Irreducible g) {n : ℕ} (h : g ∣ f ^ n) : g = f :=
  eq_of_monic_of_associated hg hf (hg'.associated_of_dvd hf' (hg'.prime.dvd_of_dvd_pow h))

theorem mangoldt_pow (s : F[X] → ℂ) (f : F[X]) (m : ℕ) (hf : f.Monic) (hf' : Irreducible f) (hm : 0 < m) :
    mangoldt s (f ^ m) = s f := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ f ^ m = g ^ k} = {f} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hg, hg', k, hk, h⟩
      exact mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := m) (h ▸ dvd_pow_self g hk.ne')
    · rintro rfl
      exact ⟨hf, hf', m, hm, rfl⟩
  rw [mangoldt, this, finsum_mem_singleton]

theorem mangoldt_eq_zero (s : F[X] → ℂ) (P : F[X])
    (h : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) : mangoldt s P = 0 := by
  have : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ k : ℕ, 0 < k ∧ P = g ^ k} = ∅ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hg, hg', k, hk, h'⟩
    exact h ⟨g, k, hg, hg', hk, h'⟩
  rw [mangoldt, this, finsum_mem_empty]

theorem conv_const_one_eq_divisorSum (a : F[X] → ℂ) (P : F[X]) (hP : P.Monic) :
    conv a (fun _ => 1) P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, a D := by
  unfold conv
  refine finsum_mem_eq_of_bijOn (fun x => x.1) ⟨?_, ?_, ?_⟩ ?_
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩
    exact ⟨hD, E, h.symm⟩
  · rintro ⟨D, E⟩ ⟨hD, _, h⟩ ⟨D', E'⟩ ⟨_, _, h'⟩ h''
    simp only at h h' h'' hD
    subst h''
    rw [mul_left_cancel₀ hD.ne_zero (h.trans h'.symm)]
  · rintro D ⟨hD, E, h⟩
    exact ⟨(D, E), ⟨hD, hD.of_mul_monic_left (h ▸ hP), h.symm⟩, rfl⟩
  · intro x _
    simp

theorem mangoldtConv_finite_monicDivisors (P : F[X]) (hP : P.Monic) :
    {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by
  have := Polynomial.fintypeSubtypeMonicDvd P hP.ne_zero
  exact Set.finite_coe_iff.mp (Finite.of_fintype {g : F[X] // g.Monic ∧ g ∣ P})

theorem mangoldt_divisorSum_mul (s : F[X] → ℂ) (f Q : F[X]) (hf : f.Monic) (hf' : Irreducible f)
    (hQ : Q.Monic) :
    ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ f * Q}, mangoldt s D =
      s f + ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ Q}, mangoldt s D := by
  obtain ⟨n, R, hR, hQR⟩ := WfDvdMonoid.max_power_factor hQ.ne_zero hf'
  have hnot : f ^ (n + 1) ∉ {D : F[X] | D.Monic ∧ D ∣ Q} := by
    rintro ⟨_, h⟩
    rw [hQR, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n hf.ne_zero)] at h
    exact hR h
  rw [← mangoldt_pow s f (n + 1) hf hf' n.succ_pos,
    ← finsum_mem_insert _ hnot (mangoldtConv_finite_monicDivisors Q hQ)]
  refine finsum_mem_inter_support_eq _ _ _ ?_
  ext D
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Function.mem_support]
  refine and_congr_left fun hD => ?_
  constructor
  · rintro ⟨hDm, hd⟩
    obtain ⟨g, m, hg, hg', hm, rfl⟩ := not_not.mp (mt (mangoldt_eq_zero s D) hD)
    by_cases hgf : g = f
    · subst hgf
      rcases lt_trichotomy m (n + 1) with h | h | h
      · exact Or.inr ⟨hDm, hQR ▸ (pow_dvd_pow g (by omega)).mul_right R⟩
      · exact Or.inl (by rw [h])
      · exfalso
        have h2 : g ^ (n + 1) * g ∣ g ^ (n + 1) * R := by
          have h3 : g ^ (n + 1 + 1) ∣ g * Q := (pow_dvd_pow g (by omega)).trans hd
          rw [hQR, ← mul_assoc, ← pow_succ', pow_succ g (n + 1)] at h3
          exact h3
        exact hR ((mul_dvd_mul_iff_left (pow_ne_zero _ hf.ne_zero)).mp h2)
    · refine Or.inr ⟨hDm, ?_⟩
      have hc : IsCoprime g f := by
        rw [hg'.coprime_iff_not_dvd]
        intro h
        exact hgf (mangoldtConv_eq_of_dvd_pow hf hf' hg hg' (n := 1) (by simpa using h))
      exact (hc.pow_left (m := m)).dvd_of_dvd_mul_left hd
  · rintro (rfl | ⟨hDm, hd⟩)
    · refine ⟨hf.pow _, ?_⟩
      rw [hQR, ← mul_assoc, ← pow_succ']
      exact dvd_mul_right _ _
    · exact ⟨hDm, hd.mul_left f⟩

theorem IsAdditive.eq_divisorSum_mangoldt {s : F[X] → ℂ} (hs : IsAdditive s) (P : F[X]) (hP : P.Monic) :
    s P = ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ P}, mangoldt s D := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases hu : IsUnit P
    · have h1 : P = 1 := hP.isUnit_iff.mp hu
      subst h1
      have h0 : s 1 = 0 := by
        have := hs 1 1 monic_one monic_one
        rw [mul_one] at this
        exact left_eq_add.mp this
      rw [h0]
      symm
      refine finsum_mem_of_eqOn_zero fun D hD => ?_
      refine mangoldt_eq_zero s D ?_
      rintro ⟨g, m, _, hg', hm, rfl⟩
      exact hg'.not_isUnit (isUnit_of_dvd_one ((dvd_pow_self g hm.ne').trans hD.2))
    · obtain ⟨f, hf, hf', Q, rfl⟩ := Polynomial.exists_monic_irreducible_factor P hu
      have hQ : Q.Monic := hf.of_mul_monic_left hP
      have hlt : Q.natDegree < n := by
        rw [← hn, hf.natDegree_mul hQ]
        have := hf'.natDegree_pos
        omega
      rw [mangoldt_divisorSum_mul s f Q hf hf' hQ, hs f Q hf hQ, ih _ hlt Q hQ rfl]

theorem mangoldt_conv_spec : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s →
    (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧
    (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧
    ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) →
      mangoldt s P = 0 := by
  intro F _ s hs
  refine ⟨fun P hP => ?_, mangoldt_pow s, mangoldt_eq_zero s⟩
  rw [conv_const_one_eq_divisorSum _ P hP]
  exact hs.eq_divisorSum_mangoldt P hP

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s → (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧ (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧ ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) → mangoldt s P = 0 := by
  first | exact @GlobalTheory.CuspGL.mangoldt_conv_spec | exact GlobalTheory.CuspGL.mangoldt_conv_spec | (intros; apply GlobalTheory.CuspGL.mangoldt_conv_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndomorphismInnerProductPrimitiveMobiu
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndomorphismInnerProductPrimitiveMobiu
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL.PrimOrth

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem neg_mem_nilRad {A : Submodule F V} {h : Module.End F V} (hh : h ∈ nilRad A) : -h ∈ nilRad A :=
  ⟨fun x => by simpa using hh.1 x, fun x hx => by simpa using hh.2 x hx⟩

theorem add_preserves {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) : ∀ x ∈ A, (g + h) x ∈ A :=
  fun x hx => A.add_mem (hg x hx) (hh.1 x)

theorem add_preserves_iff {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A) :
    (∀ x ∈ A, (g + h) x ∈ A) ↔ ∀ x ∈ A, g x ∈ A := by
  refine ⟨fun H => ?_, add_preserves hh⟩
  have := add_preserves (neg_mem_nilRad hh) H
  simpa using this

theorem isUnit_add [FiniteDimensional F V] {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) (hu : IsUnit g) : IsUnit (g + h) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot] at hu
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hinj : Function.Injective (g.restrict hg) := by
    intro a b hab
    exact Subtype.ext (hu (congrArg Subtype.val hab))
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  have hx' : g x + h x = 0 := hx
  have hgx : g x ∈ A := by
    rw [eq_neg_of_add_eq_zero_left hx']
    exact A.neg_mem (hh.1 x)
  obtain ⟨w, hw⟩ := hsurj ⟨g x, hgx⟩
  have hwx : (w : V) = x := hu (congrArg Subtype.val hw)
  have hxA : x ∈ A := hwx ▸ w.2
  rw [hh.2 x hxA, add_zero] at hx'
  exact hu (by rw [hx', map_zero])

theorem isUnit_add_iff [FiniteDimensional F V] {A : Submodule F V} {g h : Module.End F V} (hh : h ∈ nilRad A)
    (hg : ∀ x ∈ A, g x ∈ A) : IsUnit (g + h) ↔ IsUnit g := by
  refine ⟨fun H => ?_, isUnit_add hh hg⟩
  have := isUnit_add (neg_mem_nilRad hh) (add_preserves hh hg) H
  simpa using this

theorem sum_mul_eq_zero [Fintype (Module.End F V)] {φ : Module.End F V → ℂ} (hφ : IsPrimitive φ)
    {A : Submodule F V} (h0 : A ≠ ⊥) (h1 : A ≠ ⊤) (f : Module.End F V → ℂ)
    (hf : ∀ g, ∀ h ∈ nilRad A, f (g + h) = f g) (hf0 : ∀ g, ¬ (∀ x ∈ A, g x ∈ A) → f g = 0) :
    ∑ g, φ g * f g = 0 := by
  classical
  have hfin : (nilRad A).Finite := Set.toFinite _
  have hne : (hfin.toFinset.card : ℂ) ≠ 0 := by
    have : hfin.toFinset.Nonempty := ⟨0, by
      rw [Set.Finite.mem_toFinset]
      exact ⟨fun x => by simp, fun x _ => by simp⟩⟩
    exact_mod_cast this.card_pos.ne'
  have key : ∑ h ∈ hfin.toFinset, ∑ g, φ g * f g = 0 := by
    have : ∀ h ∈ hfin.toFinset, ∑ g, φ g * f g = ∑ g, φ (g + h) * f g := by
      intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      rw [← Equiv.sum_comp (Equiv.addRight h)]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Equiv.coe_addRight, hf g h hh]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [← Finset.sum_mul]
    by_cases hg : ∀ x ∈ A, g x ∈ A
    · have := hφ A h0 h1 g hg
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at this
      rw [this, zero_mul]
    · rw [hf0 g hg, mul_zero]
  rw [Finset.sum_const, nsmul_eq_mul] at key
  exact (mul_eq_zero.mp key).resolve_left hne

theorem psi_bot {s : F[X] → ℂ} (hs : IsAdditive s) (U : Type) [AddCommGroup U] [Module F U]
    [FiniteDimensional F U] [Subsingleton U] (g : Module.End F U) : psi s U g = 0 := by
  have h1 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    simpa using this
  have hc : LinearMap.charpoly g = 1 := by
    have hm := LinearMap.charpoly_monic g
    rw [← hm.natDegree_eq_zero, LinearMap.charpoly_natDegree]
    exact Module.finrank_zero_of_subsingleton
  haveI : IsEmpty {W : Submodule F U // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} :=
    ⟨fun W => W.2.1 (Subsingleton.elim _ _)⟩
  rw [psi_eq, hc, h1, finsum_of_isEmpty, sub_zero]

open Classical in
theorem ipGL_psi_eq (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (hs : IsAdditive s) (φ : Module.End F V → ℂ)
    (hφ : IsPrimitive φ) : ipGL φ (psi s V) = ipGL φ (fun g => s (LinearMap.charpoly g)) := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective _ (DFunLike.coe_injective (F := V →ₗ[F] V))
  haveI : Finite (Submodule F V) := Finite.of_injective _ (SetLike.coe_injective (A := Submodule F V))
  letI := Fintype.ofFinite (Module.End F V)
  letI := Fintype.ofFinite (Submodule F V)
  let R : Submodule F V → Module.End F V → ℂ := fun W g =>
    if h : W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W then psi s W (g.restrict h.2) else 0
  have hR : ∀ g, psi s V g = s (LinearMap.charpoly g) - ∑ W, R W g := by
    intro g
    rw [psi_eq, finsum_eq_sum_of_fintype]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun W : Submodule F V => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun W : Submodule F V => ¬ (W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W)), add_zero,
      Finset.sum_subtype (p := fun W : Submodule F V => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) _ (by simp)]
    · refine Finset.sum_congr rfl fun W _ => ?_
      simp only [R, dif_pos W.2]
    · intro W hW
      simp only [R, dif_neg (Finset.mem_filter.mp hW).2]
  have hW : ∀ W, ∑ g, φ g * (if IsUnit g then star (R W g) else 0) = 0 := by
    intro W
    by_cases h1 : W = ⊤
    · refine Finset.sum_eq_zero fun g _ => ?_
      have : R W g = 0 := dif_neg (fun h => h.1 h1)
      simp [this]
    by_cases h0 : W = ⊥
    · refine Finset.sum_eq_zero fun g _ => ?_
      have : R W g = 0 := by
        subst h0
        simp only [R]
        split_ifs
        · exact psi_bot hs _ _
        · rfl
      simp [this]
    refine sum_mul_eq_zero hφ h0 h1 _ ?_ ?_
    · intro g h hh
      by_cases hg : ∀ x ∈ W, g x ∈ W
      · have e : R W (g + h) = R W g := by
          simp only [R]
          rw [dif_pos ⟨h1, add_preserves hh hg⟩, dif_pos ⟨h1, hg⟩]
          congr 1
          ext x
          simp [LinearMap.restrict_apply, hh.2 x x.2]
        simp only [e, isUnit_add_iff hh hg]
      · have e1 : R W g = 0 := dif_neg (fun H => hg H.2)
        have e2 : R W (g + h) = 0 := dif_neg (fun H => hg ((add_preserves_iff hh).mp H.2))
        simp [e1, e2]
    · intro g hg
      have e1 : R W g = 0 := dif_neg (fun H => hg H.2)
      simp [e1]
  have hsum : ∀ ψ : Module.End F V → ℂ,
      ipGL φ ψ = ∑ g, φ g * (if IsUnit g then star (ψ g) else 0) := by
    intro ψ
    rw [ipGL, finsum_mem_def, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : IsUnit g
    · simp [Set.indicator, hg]
    · simp [Set.indicator, hg]
  rw [hsum, hsum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have h2 : ∑ W, ∑ g, φ g * (if IsUnit g then star (R W g) else 0) = 0 :=
    Finset.sum_eq_zero fun W _ => hW W
  rw [Finset.sum_comm, ← neg_eq_zero, ← Finset.sum_neg_distrib] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hg : IsUnit g
  · simp only [if_pos hg, hR g, star_sub, star_sum, ← Finset.mul_sum]
    ring
  · simp [hg]

end GlobalTheory.CuspGL.PrimOrth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndomorphismInnerProductPrimitiveMobiuStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ φ : Module.End F V → ℂ, IsPrimitive φ → ipGL φ (psi s V) = ipGL φ (fun g => s (LinearMap.charpoly g)) := by
  first | exact @GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq | exact GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq | (intros; apply GlobalTheory.CuspGL.PrimOrth.ipGL_psi_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroup
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.AbByP.subgroup :
    ∀ (G : Type) [Group G] (T : Subgroup G),
      _root_.GlobalTheory.BI.AbByP G → _root_.GlobalTheory.BI.AbByP T := by
  intro G _ T h
  unfold _root_.GlobalTheory.BI.AbByP at h ⊢
  obtain ⟨p, hp, A, hA, hcomm, hpow⟩ := h
  haveI := hA
  refine ⟨p, hp, A.subgroupOf T, Subgroup.normal_subgroupOf, ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hcomm _ ha _ hb)
  · intro g
    obtain ⟨n, hn⟩ := hpow g
    exact ⟨n, by simpa [Subgroup.mem_subgroupOf] using hn⟩

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroupStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup : ∀ (G : Type) [Group G] (T : Subgroup G), AbByP G → AbByP T := by
  first | exact @GlobalTheory.BI.AbByP.subgroup | exact GlobalTheory.BI.AbByP.subgroup | (intros; apply GlobalTheory.BI.AbByP.subgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExponentRegularOfNatDegreeMinpolyGeneratorPow
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExponentRegularOfNatDegreeMinpolyGeneratorPow
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exponent_regular_of_natDegree_minpoly_pow : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by
  intro F _ _ d k ζ _ hord hdeg i hi hid hmod
  have h1 : ζ ^ (Nat.card F ^ d - 1) = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one ζ
  have h2 : (ζ ^ k) ^ (Nat.card F ^ i) = ζ ^ k := by
    rw [← pow_mul]; exact pow_eq_pow_of_modEq hmod h1
  have hint : IsIntegral F (ζ ^ k) := Algebra.IsIntegral.isIntegral _
  have hdvd : minpoly F (ζ ^ k) ∣ (X ^ (Nat.card F ^ i) - X : F[X]) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, h2, sub_self]
  have h3 := (minpoly.irreducible hint).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  rw [hdeg] at h3
  exact absurd (Nat.le_of_dvd hi h3) (not_le.mpr hid)

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by
  first | exact @GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow | exact GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow | (intros; apply GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassEqOfLinearEquivInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassEqOfLinearEquivInvariant
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem mass_eq_mass_pi_of_invariant : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.natDegree = Module.finrank F V → mass (Φ V) P = mass (Φ (Fin P.natDegree → F)) P := by
  intro F _ _ V _ _ _ Φ hΦ P hP
  let e : V ≃ₗ[F] (Fin P.natDegree → F) := LinearEquiv.ofFinrankEq _ _ (by simp [hP])
  unfold mass
  refine finsum_mem_eq_of_bijOn (fun g => e.conj g) ⟨?_, ?_, ?_⟩ ?_
  · intro g hg
    simpa using hg
  · intro g _ h _ hgh
    simpa using congrArg e.symm.conj hgh
  · intro h hh
    refine ⟨e.symm.conj h, ?_, by simp⟩
    simpa using hh
  · intro g _
    exact (hΦ V _ e g).symm

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassEqOfLinearEquivInvariantStatement
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.natDegree = Module.finrank F V → mass (Φ V) P = mass (Φ (Fin P.natDegree → F)) P := by
  first | exact @GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant | exact GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant | (intros; apply GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MultisetPowerSumNewtonIdentity
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

private theorem sum_antidiagonal_filter_ioo_eq_sum_ioo (k : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k, g a.1 a.2
      = ∑ i ∈ Finset.Ioo 0 k, g i (k - i) := by
  rw [Finset.sum_filter,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if i ∈ Set.Ioo 0 k then g i j else 0),
    ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo, Finset.mem_Ioo]
  omega

private theorem aeval_psum_eq_sum_map_pow (s : Multiset ℂ) (n : ℕ) :
    MvPolynomial.aeval (fun x : s => (x : ℂ)) (MvPolynomial.psum s ℂ n) = (s.map (· ^ n)).sum := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.psum, map_sum]
  simp only [map_pow, MvPolynomial.aeval_X]
  conv_rhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl

theorem multiset_newton_psum (s : Multiset ℂ) (r : ℕ) (hr : 0 < r) :
    (s.map (· ^ r)).sum = (-1) ^ (r + 1) * (r : ℂ) * s.esymm r
      - ∑ i ∈ Finset.Ioo 0 r, (-1) ^ i * s.esymm i * (s.map (· ^ (r - i))).sum := by
  classical
  have key := congrArg (MvPolynomial.aeval (fun x : s => (x : ℂ)))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ r hr)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe,
    aeval_psum_eq_sum_map_pow] at key
  rw [key, sum_antidiagonal_filter_ioo_eq_sum_ioo r (fun i j => (-1) ^ i * s.esymm i * (s.map (· ^ j)).sum)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedClassFunctionFromSubgroupEqFinsumCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedClassFunctionFromSubgroupEqFinsumCosets
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem subgroupFunctionExtendByZero_conj_of_mem {L G : Type} [Field L] [Group G] (H : Subgroup G) (ψ : H → L)
    (hψ : ∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) (a : G) (y : H) :
    ext0 H ψ ((y : G)⁻¹ * a * y) = ext0 H ψ a := by
  unfold ext0
  by_cases ha : a ∈ H
  · have h1 : (y : G)⁻¹ * a * y ∈ H := H.mul_mem (H.mul_mem (H.inv_mem y.2) ha) y.2
    rw [dite_eq_left ha, dite_eq_left h1]
    exact hψ ⟨a, ha⟩ y
  · have h1 : ¬ (y : G)⁻¹ * a * y ∈ H := by
      intro h
      apply ha
      have h2 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem y.2 h) (H.inv_mem y.2)
      have h3 : (y : G) * ((y : G)⁻¹ * a * y) * (y : G)⁻¹ = a := by group
      rwa [h3] at h2
    rw [dite_eq_right ha, dite_eq_right h1]

theorem out_mul_bijective {G : Type} [Group G] (H : Subgroup G) :
    Function.Bijective (fun p : (G ⧸ H) × H => p.1.out * (p.2 : G)) := by
  constructor
  · rintro ⟨q, y⟩ ⟨q', y'⟩ h
    simp only at h
    have hq : q = q' := by
      have h1 : ((q.out * (y : G) : G) : G ⧸ H) = ((q'.out * (y' : G) : G) : G ⧸ H) := by rw [h]
      rw [QuotientGroup.mk_mul_of_mem _ y.2, QuotientGroup.mk_mul_of_mem _ y'.2,
        QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
      exact h1
    subst hq
    have : y = y' := Subtype.ext (mul_left_cancel h)
    rw [this]
  · intro x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul H x
    refine ⟨((x : G ⧸ H), y⁻¹), ?_⟩
    simp [hy]

theorem ind_eq_finsum_cosets : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), (∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) → ∀ g : G, ind H ψ g = ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) := by
  intro L _ _ G _ _ H ψ hψ g
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (G ⧸ H)
  have := Fintype.ofFinite H
  have hc : (Nat.card H : L) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold ind
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← (out_mul_bijective H).sum_comp (fun x : G => ext0 H ψ (x⁻¹ * g * x)), Fintype.sum_prod_type]
  have h1 : ∀ q : G ⧸ H, ∑ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
      = (Nat.card H : L) * ext0 H ψ (q.out⁻¹ * g * q.out) := by
    intro q
    have h2 : ∀ y : H, ext0 H ψ ((q.out * (y : G))⁻¹ * g * (q.out * (y : G)))
        = ext0 H ψ (q.out⁻¹ * g * q.out) := by
      intro y
      rw [← subgroupFunctionExtendByZero_conj_of_mem H ψ hψ (q.out⁻¹ * g * q.out) y]
      congr 1
      group
    simp only [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  simp only [h1]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.BI
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedClassFunctionFromSubgroupEqFinsumCosetsStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedClassFunctionFromSubgroup_eq_finsum_cosets : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), (∀ h x : H, ψ (x⁻¹ * h * x) = ψ h) → ∀ g : G, ind H ψ g = ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out) := by
  first | exact @GlobalTheory.BI.ind_eq_finsum_cosets | exact GlobalTheory.BI.ind_eq_finsum_cosets | (intros; apply GlobalTheory.BI.ind_eq_finsum_cosets <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CommuteImageAbelianByPrimePowerOfNormalCentral
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CommuteImageAbelianByPrimePowerOfNormalCentral
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.commute_all : ∀ (G : Type) [Group G] [Finite G] (M : Type) [Monoid M] (φ : G →* M), _root_.GlobalTheory.BI.AbByP G → (∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, φ a * φ b = φ b * φ a) → ∀ b ∈ B, ∀ g : G, φ b * φ g = φ g * φ b) → ∀ a b : G, φ a * φ b = φ b * φ a := by
  intro G _ _ M _ φ hG hyp
  obtain ⟨p, hp, A, hAn, hAc, hpow⟩ := hG
  let Z : Subgroup G :=
    { carrier := {b | ∀ g, φ b * φ g = φ g * φ b}
      mul_mem' := fun {x y} hx hy g => by
        rw [map_mul, mul_assoc, hy g, ← mul_assoc, hx g, mul_assoc]
      one_mem' := fun g => by simp
      inv_mem' := fun {x} hx g => by
        have h1 : φ x⁻¹ * φ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h2 : φ x * φ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        calc φ x⁻¹ * φ g = φ x⁻¹ * φ g * (φ x * φ x⁻¹) := by rw [h2, mul_one]
          _ = φ x⁻¹ * (φ x * φ g) * φ x⁻¹ := by rw [hx g]; simp only [mul_assoc]
          _ = φ g * φ x⁻¹ := by rw [← mul_assoc, h1, one_mul] }
  have hZ : ∀ b, b ∈ Z ↔ ∀ g, φ b * φ g = φ g * φ b := fun b => Iff.rfl
  have hZn : Z.Normal := ⟨fun b hb g => by
    rw [hZ] at hb ⊢
    intro h
    have e : φ (g * b * g⁻¹) = φ b := by
      rw [map_mul, map_mul, ← hb g, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [e]
    exact hb h⟩
  have hAZ : A ≤ Z := fun a ha => (hZ a).2 (hyp A hAn (fun x hx y hy => by
    rw [← map_mul, ← map_mul, hAc x hx y hy]) a ha)
  suffices hZtop : Z = ⊤ by
    intro a b
    exact (hZ a).1 (hZtop ▸ Subgroup.mem_top a) b
  by_contra hne
  have hP : IsPGroup p (G ⧸ Z) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := hpow g
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hAZ hk⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (G ⧸ Z) := QuotientGroup.nontrivial_iff.mpr hne
  haveI := hP.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (G ⧸ Z))
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (z : G ⧸ Z)
  have hzc : ∀ q : G ⧸ Z, ∀ i : ℤ, q * (z : G ⧸ Z) ^ i = (z : G ⧸ Z) ^ i * q := fun q i =>
    ((Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ z.2 i)) q)
  let C : Subgroup G := (Subgroup.zpowers (z : G ⧸ Z)).comap (QuotientGroup.mk' Z)
  have hmemC : ∀ c ∈ C, ∃ i : ℤ, ∃ b ∈ Z, c = g ^ i * b := by
    intro c hc
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine ⟨i, (g ^ i)⁻¹ * c, ?_, by group⟩
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hg]
    exact hi
  have hCn : C.Normal := ⟨fun c hc h => by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hi ⊢
    rw [← hi, hzc, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hCc : ∀ x ∈ C, ∀ y ∈ C, φ x * φ y = φ y * φ x := by
    intro x hx y hy
    obtain ⟨i, b1, hb1, rfl⟩ := hmemC x hx
    obtain ⟨j, b2, hb2, rfl⟩ := hmemC y hy
    rw [hZ] at hb1 hb2
    have key : ∀ (i j : ℤ) (b1 b2 : G), (∀ g, φ b1 * φ g = φ g * φ b1) →
        φ (g ^ i * b1) * φ (g ^ j * b2) = φ (g ^ (i + j)) * (φ b1 * φ b2) := by
      intro i j b1 b2 hb1
      rw [map_mul, map_mul, mul_assoc, ← mul_assoc (φ b1), hb1, mul_assoc, ← mul_assoc,
        ← map_mul, ← zpow_add]
    rw [key i j b1 b2 hb1, key j i b2 b1 hb2, add_comm, hb1 b2]
  have hgC : g ∈ C := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp [hg]⟩
  have hgZ : g ∈ Z := (hZ g).2 (hyp C hCn hCc g hgC)
  apply hz1
  apply Subtype.ext
  rw [← hg]
  exact (QuotientGroup.eq_one_iff g).mpr hgZ

end GlobalTheory.BI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CommuteImageAbelianByPrimePowerOfNormalCentralStatement
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_image_abelianByPrimePower_of_normal_central : ∀ (G : Type) [Group G] [Finite G] (M : Type) [Monoid M] (φ : G →* M), AbByP G → (∀ B : Subgroup G, B.Normal → (∀ a ∈ B, ∀ b ∈ B, φ a * φ b = φ b * φ a) → ∀ b ∈ B, ∀ g : G, φ b * φ g = φ g * φ b) → ∀ a b : G, φ a * φ b = φ b * φ a := by
  first | exact @GlobalTheory.BI.commute_all | exact GlobalTheory.BI.commute_all | (intros; apply GlobalTheory.BI.commute_all <;> assumption)
end
end
