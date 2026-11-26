module

public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
public import Formalism.GaloisIrreducibility.NoSolvableTransitive
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Window
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt

@[expose] public section

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.ZReuse
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem twist_invertible_holds : TwistInvertible := by
  intro k V _ _ _ _ γ₀ c hc hne
  let L : Module.End k V := c⁻¹ • γ₀ - 1
  have hL : ∀ v, L v = c⁻¹ • γ₀ v - v := fun v => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hL, sub_eq_zero] at hv
    have h2 : γ₀ v = c • v := by
      calc γ₀ v = c • (c⁻¹ • γ₀ v) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        _ = c • v := by rw [hv]
    by_contra hv0
    exact hne (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr h2, hv0⟩)
  have hbij : Function.Bijective L := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  exact hbij

theorem phi15_is_unit_holds : PrimitiveRootFifteenSubOneUnit := by
  intro R _ _ ζ hζ
  have hnp : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ 15 := by
    intro p hp k h
    have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (show 3 ∣ p ^ k by rw [h]; norm_num)
    have h5 : 5 ∣ p := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow (show 5 ∣ p ^ k by rw [h]; norm_num)
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
    have e5 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) hp).mp h5
    omega
  have hev : (Polynomial.cyclotomic 15 R).eval 1 = 1 := Polynomial.eval_one_cyclotomic_not_prime_pow hnp
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  have hmem : ζ ∈ primitiveRoots 15 R := (mem_primitiveRoots (by norm_num)).mpr hζ
  have hdvd : (1 - ζ) ∣ 1 := (Finset.dvd_prod_of_mem (fun μ => (1 : R) - μ) hmem).trans hev.dvd
  have hu : IsUnit (1 - ζ) := isUnit_of_dvd_one hdvd
  rw [show ζ - 1 = -(1 - ζ) by ring]
  exact hu.neg

theorem g5b_multiplicity_holds : UnitEvalOfMultiplicity := by
  intro O _ _ t c s' hs hmult
  have hmap : (s' * (X - C c) ^ t).map (IsLocalRing.residue O) =
      s'.map (IsLocalRing.residue O) * (X - C (IsLocalRing.residue O c)) ^ t := by
    simp
  have hs0 : s'.map (IsLocalRing.residue O) ≠ 0 := (hs.map _).ne_zero
  rw [hmap, Polynomial.rootMultiplicity_mul
    (mul_ne_zero hs0 (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))),
    Polynomial.rootMultiplicity_X_sub_C_pow] at hmult
  have h0 : (s'.map (IsLocalRing.residue O)).rootMultiplicity (IsLocalRing.residue O c) = 0 := by
    omega
  rw [Polynomial.rootMultiplicity_eq_zero_iff] at h0
  have hne : (s'.map (IsLocalRing.residue O)).eval (IsLocalRing.residue O c) ≠ 0 :=
    fun e => hs0 (h0 e)
  rw [Polynomial.eval_map, Polynomial.eval₂_hom] at hne
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne

theorem same_residue_holds : SameResidue := by
  intro O _ _ X _ T hT a ha x y
  let ev : X → (T →+* IsLocalRing.ResidueField O) := fun z =>
    (IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) z).comp T.val.toRingHom)
  have hev : ∀ z (b : T), ev z b = IsLocalRing.residue O ((b : X → O) z) := fun z b => rfl
  have hsurj : ∀ z, Function.Surjective (ev z) := by
    intro z k
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective k
    exact ⟨algebraMap O T r, by rw [hev]; simp⟩
  have hmax : ∀ z, RingHom.ker (ev z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hmem : ((⟨a, ha⟩ : T) - algebraMap O T (a x)) ∈ RingHom.ker (ev x) := by
    rw [RingHom.mem_ker, map_sub, hev, hev]
    simp
  rw [hmax x, ← hmax y, RingHom.mem_ker, map_sub, hev, hev, sub_eq_zero] at hmem
  simpa using hmem.symm

end Formalism.IrreducibleCountingLemmas.Z
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.CharpolyFactorAnnihilator
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem charpolyFactorAnnihilator : CharpolyFactorAnnihilator := by
  intro K V _ _ _ _ A B γ₀ γ c cγ t P hAB hA₀ hA hB₀ hB ht hchar
  classical
  let gA : Module.End K A := γ₀.restrict hA₀
  let gB : Module.End K B := c • LinearMap.id
  let e : (A × B) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl A B hAB

  have hconj : e.conj (gA.prodMap gB) = γ₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    simp [e, gA, gB, Submodule.coe_prodEquivOfIsCompl', hB₀ b b.2]

  have hcB : gB.charpoly = (X - C c) ^ t := by
    rw [← LinearMap.charpoly_toMatrix gB (Module.finBasis K B)]
    have hm : LinearMap.toMatrix (Module.finBasis K B) (Module.finBasis K B) gB =
        Matrix.diagonal (fun _ => c) := by
      simp only [gB, map_smul, LinearMap.toMatrix_id]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [hm, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ht]
  have hPA : P = gA.charpoly := by
    have h1 : γ₀.charpoly = gA.charpoly * gB.charpoly := by
      rw [← hconj, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap]
    rw [hchar, hcB] at h1
    exact mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero c)) h1

  have hrestr : ∀ (p : K[X]) (a : A), (aeval γ₀ p) (a : V) = ((aeval gA p) a : V) := by
    intro p
    induction p using Polynomial.induction_on with
    | C r => intro a; simp [Module.algebraMap_end_apply]
    | add p q hp hq => intro a; simp [hp, hq]
    | monomial n r ih =>
      intro a
      rw [pow_succ, ← mul_assoc, map_mul (aeval γ₀), map_mul (aeval gA), aeval_X, aeval_X,
        Module.End.mul_apply, Module.End.mul_apply]
      rw [show γ₀ (a : V) = ((gA a : A) : V) from rfl, ih]
  have h0 : aeval gA P = 0 := by
    rw [hPA]
    exact LinearMap.aeval_self_charpoly gA
  have hkill : ∀ w ∈ A, (aeval γ₀ P) w = 0 := by
    intro w hw
    have h2 := hrestr P ⟨w, hw⟩
    rw [h0] at h2
    simpa using h2
  apply LinearMap.ext
  intro v
  have hv : v ∈ A ⊔ B := by rw [hAB.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Module.End.mul_apply, LinearMap.zero_apply, LinearMap.sub_apply,
    Module.algebraMap_end_apply]
  have h3 : γ (a + b) - cγ • (a + b) = γ a - cγ • a := by
    rw [map_add (f := _), hB b hb, smul_add]
    abel
  rw [h3]
  exact hkill _ (A.sub_mem (hA a ha) (A.smul_mem cγ ha))

end Formalism.IrreducibleCountingLemmas.Z
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.ZGoodCuspidal
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem goodCuspidal_holds : GoodCuspidal := by
  intro k _ P _ r f I _ n d h hdeg hsq hprod hhdeg hn hd hno
  obtain ⟨v0⟩ := ‹Nonempty P›

  have hdvd : ∀ v i, h v i ∣ f v := by
    intro v i
    rw [hprod v]
    exact (dvd_pow_self (h v i) (by have := hd i; omega)).trans
      (Finset.dvd_prod_of_mem (fun j => h v j ^ d j) (Finset.mem_univ i))

  have hd1 : ∀ i, d i = 1 := by
    intro i
    by_contra hne
    have h2 : 2 ≤ d i := by have := hd i; omega
    have hsq' : h v0 i * h v0 i ∣ f v0 := by
      rw [hprod v0]
      refine (?_ : h v0 i * h v0 i ∣ h v0 i ^ d i).trans
        (Finset.dvd_prod_of_mem (fun j => h v0 j ^ d j) (Finset.mem_univ i))
      rw [← pow_two]
      exact pow_dvd_pow _ h2
    have hu := hsq v0 _ hsq'
    have e1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have e2 := hhdeg v0 i
    have e3 := hn i
    omega
  refine ⟨hd1, ?_⟩
  by_contra hcard
  push_neg at hcard
  haveI : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨i, j, hij⟩ := exists_pair_ne I
  have hf0 : f v0 ≠ 0 := (hsq v0).ne_zero
  have hne : ∀ l, h v0 l ≠ 0 := by
    intro l hl
    have := hdvd v0 l
    rw [hl, zero_dvd_iff] at this
    exact hf0 this

  have hr : r = ∑ l, n l := by
    rw [← hdeg v0, hprod v0, Polynomial.natDegree_prod _ _ (fun l _ => pow_ne_zero _ (hne l))]
    simp [Polynomial.natDegree_pow, hd1, hhdeg]
  have hle : n i + n j ≤ ∑ l, n l := by
    classical
    rw [← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rcases le_total (n i) (n j) with hij' | hji'
  · exact hno ⟨n i, hn i, by omega, fun v => ⟨h v i, hdvd v i, hhdeg v i⟩⟩
  · exact hno ⟨n j, hn j, by omega, fun v => ⟨h v j, hdvd v j, hhdeg v j⟩⟩

end Formalism.IrreducibleCountingLemmas.Z
end

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.FactorOverLocalSubalgebra
open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

theorem factorOverLocalSubalgebra : FactorOverLocalSubalgebra := by
  intro O _ _ X' _ T hT t c F s hF hs
  have := hT
  let c' : T := algebraMap O T c
  have hev_c : ∀ x, ev T x c' = c := fun x => by simp [ev, c']
  have hq : ((X - C c') ^ t : T[X]).Monic := (monic_X_sub_C c').pow t
  have hqO : ((X - C c) ^ t : O[X]).Monic := (monic_X_sub_C c).pow t
  have hqmap : ∀ x, ((X - C c') ^ t : T[X]).map (ev T x) = (X - C c) ^ t := by
    intro x
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hev_c]
  have hR : F %ₘ (X - C c') ^ t = 0 := by
    ext n x
    have h1 : (F %ₘ (X - C c') ^ t).map (ev T x) = 0 := by
      rw [map_modByMonic _ hq, hqmap, hF, (modByMonic_eq_zero_iff_dvd hqO).mpr (dvd_mul_left _ _)]
    have h2 := congrArg (fun p => p.coeff n) h1
    simpa [Polynomial.coeff_map, ev] using h2
  have hmapP : ∀ x, (F /ₘ (X - C c') ^ t).map (ev T x) = s x := by
    intro x
    rw [map_divByMonic _ hq, hqmap, hF, mul_comm, mul_divByMonic_cancel_left _ hqO]
  refine ⟨F /ₘ (X - C c') ^ t, ?_, ?_, hmapP⟩
  · have h := modByMonic_add_div F ((X - C c') ^ t)
    rw [hR, zero_add] at h
    rw [mul_comm]
    exact h.symm
  · obtain ⟨x⟩ : Nonempty X' := by
      by_contra h
      rw [not_nonempty_iff] at h
      have hsub : Subsingleton T := ⟨fun a b => Subtype.ext (funext fun x => (IsEmpty.false x).elim)⟩
      exact not_subsingleton T hsub
    have := IsLocalHom.of_surjective (ev T x) (fun o => ⟨algebraMap O T o, by simp [ev]⟩)
    apply isUnit_of_map_unit (ev T x)
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, hmapP, hev_c]
    exact hs x

end Formalism.IrreducibleCountingLemmas.Z
end

open Polynomial Filter Topology

namespace Formalism.IrreducibleCountingLemmas.Z

theorem charpolyRev_map_alt {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) :
    Matrix.charpolyRev (M.map f) = (Matrix.charpolyRev M).map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [h]

theorem third_reduction_holds : ResidueCharpolyEq := by
  intro O _ _ X' _ T hT G n r hr x y g
  have h1 : Matrix.charpolyRev ((r x g).map (IsLocalRing.residue O)) =
      Matrix.charpolyRev ((r y g).map (IsLocalRing.residue O)) := by
    rw [charpolyRev_map_alt, charpolyRev_map_alt]
    ext j
    rw [coeff_map, coeff_map]
    exact same_residue_holds O X' T hT _ (hr g j) x y
  refine ⟨h1, ?_⟩
  have key : ∀ M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O),
      M.charpoly = (Matrix.charpolyRev M).reflect n := by
    intro M
    rw [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, reflect_reflect]
  rw [key, key, h1]

theorem nonempty_of_local_subalgebra {O X' : Type} [CommRing O] (T : Subalgebra O (X' → O)) [IsLocalRing T] :
    Nonempty X' := by
  by_contra h
  have : IsEmpty X' := not_nonempty_iff.1 h
  exact zero_ne_one (α := T) (Subtype.ext (funext fun x => isEmptyElim x))

theorem monic_of_eval_monic {O X' : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X' → O))
    [IsLocalRing T] (p : T[X]) (h : ∀ x, (p.map (ev T x)).Monic) : p.Monic := by
  obtain ⟨x₀⟩ := nonempty_of_local_subalgebra T
  have hp0 : p ≠ 0 := by
    intro h0
    have := h x₀
    rw [h0, Polynomial.map_zero] at this
    exact this.ne_zero rfl
  have ha0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  have hval : ∀ x, ev T x p.leadingCoeff = 1 ∨ ev T x p.leadingCoeff = 0 := by
    intro x
    have hle : (p.map (ev T x)).natDegree ≤ p.natDegree := natDegree_map_le
    have hc : ev T x p.leadingCoeff = (p.map (ev T x)).coeff p.natDegree := by
      rw [coeff_map]; rfl
    rcases hle.eq_or_lt with he | hl
    · left
      rw [hc, ← he]; exact h x
    · right
      rw [hc]; exact coeff_eq_zero_of_natDegree_lt hl
  have hidem : p.leadingCoeff * (1 - p.leadingCoeff) = 0 := by
    apply Subtype.ext
    funext x
    have : ev T x (p.leadingCoeff * (1 - p.leadingCoeff)) = 0 := by
      rw [map_mul, map_sub, map_one]
      rcases hval x with h1 | h1 <;> rw [h1] <;> simp
    exact this
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self p.leadingCoeff with hu | hu
  · have := (hu.mul_right_eq_zero).1 hidem
    exact (sub_eq_zero.1 this).symm
  · exact absurd ((hu.mul_left_eq_zero).1 hidem) ha0

theorem fifth_factor_monic : FactorOverLocalSubalgebraMonic := by
  intro O _ _ X' _ T hT t c F s hF h1 h2
  obtain ⟨P, hP1, hP2, hP3⟩ := factorOverLocalSubalgebra O X' T hT t c F s h1 h2
  refine ⟨P, ?_, hP1, hP2, hP3⟩
  rw [hP1] at hF
  exact Monic.of_mul_monic_right ((monic_X_sub_C _).pow t) hF

theorem charpoly_smul_id {K B : Type} [Field K] [AddCommGroup B] [Module K B]
    [FiniteDimensional K B] (c : K) :
    (c • (LinearMap.id : B →ₗ[K] B)).charpoly = (X - C c) ^ Module.finrank K B := by
  rw [LinearMap.charpoly_def, map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal,
    Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ,
    Module.finrank_eq_card_chooseBasisIndex]

theorem charpoly_eq_restrict_mul_scalar {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K V) (γ₀ : Module.End K V) (c : K) (hAB : IsCompl A B)
    (hA0 : ∀ v ∈ A, γ₀ v ∈ A) (hB0 : ∀ v ∈ B, γ₀ v = c • v) :
    γ₀.charpoly = (γ₀.restrict hA0).charpoly * (X - C c) ^ Module.finrank K B := by
  have hconj : (Submodule.prodEquivOfIsCompl A B hAB).conj
      ((γ₀.restrict hA0).prodMap (c • (LinearMap.id : B →ₗ[K] B))) = γ₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A B hAB).surjective v
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    simp [Submodule.coe_prodEquivOfIsCompl', hB0 b b.2]
  rw [← charpoly_smul_id, ← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj
    (Submodule.prodEquivOfIsCompl A B hAB), hconj]

theorem fifth_assembly_second : FactorAnnihilatorFamily := by
  intro O K _ _ _ _ hinj X' _ T hT V _ _ _ A B γ₀ γ c cγ t F hF hAB hA0 hA hB0 hB hfr hmult
  have := hT
  have hDm : ((X - C c : O[X]) ^ t).Monic := (monic_X_sub_C _).pow t
  have hDK : ((X - C c : O[X]) ^ t).map (algebraMap O K) = (X - C (algebraMap O K c)) ^ t := by
    rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  have hsplit : ∀ x, (γ₀ x).charpoly =
      ((γ₀ x).restrict (hA0 x)).charpoly * (X - C (algebraMap O K c)) ^ t := by
    intro x
    have := charpoly_eq_restrict_mul_scalar (A x) (B x) (γ₀ x) (algebraMap O K c) (hAB x) (hA0 x) (hB0 x)
    rwa [hfr x] at this
  have hFx : ∀ x, F.map (ev T x) = (F.map (ev T x) /ₘ (X - C c) ^ t) * (X - C c) ^ t := by
    intro x
    have hrem : F.map (ev T x) %ₘ (X - C c) ^ t = 0 := by
      apply Polynomial.map_injective _ hinj
      rw [map_modByMonic _ hDm, hDK, hF x, hsplit x, Polynomial.map_zero]
      exact (modByMonic_eq_zero_iff_dvd ((monic_X_sub_C _).pow t)).2 (dvd_mul_left _ _)
    have := modByMonic_add_div (F.map (ev T x)) ((X - C c) ^ t)
    rw [hrem, zero_add] at this
    rw [mul_comm]; exact this.symm
  have hFm : ∀ x, (F.map (ev T x)).Monic := by
    intro x
    apply monic_of_injective hinj
    rw [hF x]; exact LinearMap.charpoly_monic _
  have hsm : ∀ x, (F.map (ev T x) /ₘ (X - C c) ^ t).Monic := by
    intro x
    have := hFm x
    rw [hFx x] at this
    exact Monic.of_mul_monic_right hDm this
  have hunit : ∀ x, IsUnit ((F.map (ev T x) /ₘ (X - C c) ^ t).eval c) := by
    intro x
    apply g5b_multiplicity_holds O t c _ (hsm x)
    rw [← hFx x]; exact hmult x
  obtain ⟨P, hPm, hP1, hP2, hP3⟩ := fifth_factor_monic O X' T hT t c F
    (fun x => F.map (ev T x) /ₘ (X - C c) ^ t) (monic_of_eval_monic T F hFm) hFx hunit
  refine ⟨P, hPm, hP1, hP2, fun x => ?_⟩
  apply charpolyFactorAnnihilator K (V x) (A x) (B x) (γ₀ x) (γ x) (algebraMap O K c) (algebraMap O K cγ) t _
    (hAB x) (hA0 x) (hA x) (hB0 x) (hB x) (hfr x)
  rw [hP3 x, ← hF x, ← hDK, ← Polynomial.map_mul, ← hFx x]

theorem good_cuspidal_multiplicity_one : GoodCuspidalOne := by
  intro k _ P _ r f I _ n d h hr hdeg hsq hprod hn hn1 hd1 hno
  obtain ⟨hd, hcard⟩ := goodCuspidal_holds k P r f I n d h hdeg hsq hprod hn hn1 hd1 hno
  obtain ⟨v₀⟩ := ‹Nonempty P›
  have hne : Nonempty I := by
    by_contra hemp
    have : IsEmpty I := not_nonempty_iff.1 hemp
    have := hdeg v₀
    rw [hprod v₀, Finset.univ_eq_empty, Finset.prod_empty, natDegree_one] at this
    omega
  have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.1 hcard
  refine ⟨le_antisymm hcard (Fintype.card_pos_iff.2 hne), fun i => ⟨hd i, ?_⟩⟩
  have := hdeg v₀
  rw [hprod v₀, Fintype.prod_subsingleton _ i, hd i, pow_one, hn] at this
  exact this

theorem first_charpoly_in_T : CharpolyOverSubalgebra := by
  intro O _ _ X' _ T n M h
  have hdeg : ∀ x, (M x).charpoly.natDegree = n := fun x => by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hco : ∀ (x : X') (j : ℕ), j ≤ n →
      (M x).charpoly.coeff j = (Matrix.charpolyRev (M x)).coeff (n - j) := by
    intro x j hj
    rw [← Matrix.reverse_charpoly, coeff_reverse, hdeg, revAt_le (Nat.sub_le n j),
      Nat.sub_sub_self hj]
  have hmem : ∀ j : ℕ, (fun x => (M x).charpoly.coeff j) ∈ T := by
    intro j
    by_cases hj : j ≤ n
    · have : (fun x => (M x).charpoly.coeff j) =
          fun x => (Matrix.charpolyRev (M x)).coeff (n - j) := funext fun x => hco x j hj
      rw [this]; exact h _
    · have : (fun x => (M x).charpoly.coeff j) = 0 := funext fun x =>
        coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
      rw [this]; exact T.zero_mem
  let F : T[X] := ∑ j ∈ Finset.range (n + 1), C (⟨_, hmem j⟩ : T) * X ^ j
  have hFc : ∀ j, F.coeff j = if j ≤ n then (⟨_, hmem j⟩ : T) else 0 := by
    intro j
    simp only [F, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp
  refine ⟨F, ?_, fun x => ?_⟩
  · apply monic_of_natDegree_le_of_coeff_eq_one n
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hFc, if_neg (by omega)]
    · rw [hFc, if_pos le_rfl]
      apply Subtype.ext
      funext x
      have := (Matrix.charpoly_monic (M x)).coeff_natDegree
      rw [hdeg] at this
      exact this
  · ext j
    rw [coeff_map, hFc]
    by_cases hj : j ≤ n
    · rw [if_pos hj]; rfl
    · rw [if_neg hj, map_zero]
      exact (coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)).symm

end Formalism.IrreducibleCountingLemmas.Z
