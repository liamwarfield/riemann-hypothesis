module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletionStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalLocalIsLocalisationOfFiniteOverPolynomialA
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsQuasiFinitePolynomialMap
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsQuasiFinitePolynomialMap
namespace GlobalTheory.NoetherInt

open Polynomial

theorem quasiFinite_quotient_of_isUnit_coeff {R : Type*} [CommRing R] (G : R[X]) (k : ℕ)
    (hc : IsUnit (G.coeff k)) : Algebra.QuasiFinite R (R[X] ⧸ Ideal.span {G}) := by
  refine ⟨fun P _ => ?_⟩
  let f : R[X] →ₐ[R] (R[X] ⧸ Ideal.span {G}) := Ideal.Quotient.mkₐ R _
  have hf : Function.Surjective f := Ideal.Quotient.mkₐ_surjective R _
  let e := Polynomial.fiberEquivQuotient f hf P
  let I : Ideal (P.ResidueField[X]) :=
    (RingHom.ker (f : R[X] →+* (R[X] ⧸ Ideal.span {G}))).map (mapRingHom (algebraMap R P.ResidueField))
  let Gb : P.ResidueField[X] := G.map (algebraMap R P.ResidueField)
  have hG : Gb ≠ 0 := by
    intro h
    have h2 : (Gb).coeff k = 0 := by rw [h]; simp
    rw [coeff_map] at h2
    exact (hc.map (algebraMap R P.ResidueField)).ne_zero h2
  have hmem : Gb ∈ I := by
    refine Ideal.mem_map_of_mem (mapRingHom (algebraMap R P.ResidueField)) (x := G) ?_
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self G)
  have hM : (Gb * C Gb.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hG
  have hMI : Gb * C Gb.leadingCoeff⁻¹ ∈ I := I.mul_mem_right _ hmem
  have h1 : Module.Finite P.ResidueField
      (P.ResidueField[X] ⧸ Ideal.span {Gb * C Gb.leadingCoeff⁻¹}) := hM.finite_quotient
  have hle : Ideal.span {Gb * C Gb.leadingCoeff⁻¹} ≤ I := by
    rw [Ideal.span_singleton_le_iff_mem]; exact hMI
  have h2 : Module.Finite P.ResidueField (P.ResidueField[X] ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ P.ResidueField hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

theorem quasiFinite_of_eval₂_eq_zero {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (t : T)
    (h : (eval₂RingHom φ t).QuasiFinite) (G : R[X]) (hG : eval₂ φ t G = 0) (k : ℕ)
    (hc : IsUnit (G.coeff k)) : φ.QuasiFinite := by
  have hker : ∀ a ∈ Ideal.span {G}, eval₂RingHom φ t a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hG]
  let ψ : (R[X] ⧸ Ideal.span {G}) →+* T := Ideal.Quotient.lift _ (eval₂RingHom φ t) hker
  have h1 : ψ.comp (Ideal.Quotient.mk (Ideal.span {G})) = eval₂RingHom φ t := by
    ext <;> simp [ψ]
  have h2 : ψ.QuasiFinite := RingHom.QuasiFinite.of_comp (g := Ideal.Quotient.mk (Ideal.span {G}))
    (h1 ▸ h)
  have h3 : (algebraMap R (R[X] ⧸ Ideal.span {G})).QuasiFinite :=
    RingHom.quasiFinite_algebraMap.2 (quasiFinite_quotient_of_isUnit_coeff G k hc)
  have h4 : ψ.comp (algebraMap R (R[X] ⧸ Ideal.span {G})) = φ := by
    ext a
    simp [ψ, IsScalarTower.algebraMap_apply R R[X] (R[X] ⧸ Ideal.span {G})]
  exact h4 ▸ h2.comp h3

theorem quasiFinite_of_isUnit_coeff {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (t : T)
    (h : (eval₂RingHom φ t).QuasiFinite) (G : R[X]) (hG : eval₂ φ t G = 0) (k : ℕ)
    (hc : IsUnit (φ (G.coeff k))) : φ.QuasiFinite := by
  let c := G.coeff k
  let φ' : Localization.Away c →+* T := IsLocalization.Away.lift c hc
  have hφ : φ'.comp (algebraMap R (Localization.Away c)) = φ := IsLocalization.Away.lift_comp c hc
  have hφx : ∀ a, φ' (algebraMap R (Localization.Away c) a) = φ a := fun a => by
    rw [← RingHom.comp_apply, hφ]
  have hι : (eval₂RingHom φ' t).comp (mapRingHom (algebraMap R (Localization.Away c)))
      = eval₂RingHom φ t := by
    ext <;> simp [hφx]
  have h1 : (eval₂RingHom φ' t).QuasiFinite := RingHom.QuasiFinite.of_comp
    (g := mapRingHom (algebraMap R (Localization.Away c))) (hι ▸ h)
  have hG' : eval₂ φ' t (G.map (algebraMap R (Localization.Away c))) = 0 := by
    have h5 := DFunLike.congr_fun hι G
    simpa [hG] using h5
  have h2 : φ'.QuasiFinite := quasiFinite_of_eval₂_eq_zero φ' t h1 _ hG' k (by
    rw [coeff_map]; exact IsLocalization.Away.algebraMap_isUnit c)
  have h3 : (algebraMap R (Localization.Away c)).QuasiFinite :=
    RingHom.quasiFinite_algebraMap.2 (.of_isLocalization (.powers c))
  exact hφ ▸ h2.comp h3

end GlobalTheory.NoetherInt

namespace GlobalTheory.NoetherInt

open MvPolynomial

section shear

variable {A : Type*} [CommRing A] {n : ℕ}

noncomputable def shearHom (A : Type*) [CommRing A] (n u : ℕ) (c : A) :
    MvPolynomial (Fin (n + 1)) A →ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ (u ^ i.1)

lemma shearHom_comp_neg (u : ℕ) (c : A) :
    (shearHom A n u c).comp (shearHom A n u (-c)) = AlgHom.id _ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp [shearHom]

noncomputable def shear (A : Type*) [CommRing A] (n u : ℕ) :
    MvPolynomial (Fin (n + 1)) A ≃ₐ[A] MvPolynomial (Fin (n + 1)) A :=
  AlgEquiv.ofAlgHom (shearHom A n u 1) (shearHom A n u (-1))
    (shearHom_comp_neg u 1)
    (by have := shearHom_comp_neg (A := A) (n := n) u (-1); rwa [neg_neg] at this)

lemma map_shear {B : Type*} [CommRing B] (φ : A →+* B) (u : ℕ)
    (g : MvPolynomial (Fin (n + 1)) A) :
    MvPolynomial.map φ (shear A n u g) = shear B n u (MvPolynomial.map φ g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [shear, shearHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    cases i using Fin.cases <;> simp [shear, shearHom]

lemma map_finSuccEquiv {B : Type*} [CommRing B] (φ : A →+* B)
    (h : MvPolynomial (Fin (n + 1)) A) :
    Polynomial.map (MvPolynomial.map φ) (finSuccEquiv A n h) =
      finSuccEquiv B n (MvPolynomial.map φ h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq, Polynomial.map_add (f := _)]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, hp]
    congr 1
    cases i using Fin.cases <;> simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]

end shear

section lead

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

private lemma sum_r_mul_ne {u : ℕ} (hu : 1 < u) (vlt : ∀ i, v i < u)
    (wlt : ∀ i, w i < u) (ne : v ≠ w) :
    ∑ i : Fin (n + 1), u ^ i.1 * v i ≠ ∑ i : Fin (n + 1), u ^ i.1 * w i := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| List.ofFn_inj.mp ?_
  apply Nat.ofDigits_inj_of_len_eq hu (by simp)
    (List.forall_mem_ofFn_iff.mpr vlt) (List.forall_mem_ofFn_iff.mpr wlt)
  simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, mul_comm, List.sum_ofFn] using! h

private lemma shear_X_zero (u : ℕ) : shear k n u (X 0) = X 0 := by simp [shear, shearHom]

private lemma shear_X_succ (u : ℕ) (i : Fin n) :
    shear k n u (X i.succ) = X i.succ + X 0 ^ (u ^ i.succ.1) := by simp [shear, shearHom]

private lemma degreeOf_zero_t {u : ℕ} (hu : 0 < u) {a : k} (ha : a ≠ 0) :
    (shear k n u (monomial v a)).degreeOf 0 = ∑ i : Fin (n + 1), u ^ i.1 * v i := by
  have hT : shear k n u (MvPolynomial.C a) = MvPolynomial.C a := (shear k n u).commutes a
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [hT, Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    shear_X_zero, shear_X_succ, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ (u ^ i.succ.1)) ^ v i.succ ≠ 0 := by
    rw [add_comm (Polynomial.C _)]
    exact pow_ne_zero _ (Polynomial.X_pow_add_C_ne_zero (pow_pos hu _) _)
  rw [Polynomial.natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), Polynomial.natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    Polynomial.natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [Polynomial.natDegree_pow, zero_add, Polynomial.natDegree_X, mul_one, Fin.val_zero,
    pow_zero, one_mul, add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), Polynomial.natDegree_X_pow_add_C, mul_comm])

private lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (shear k n (2 + f.totalDegree) (monomial v (f.coeff v))).degreeOf 0 ≠
    (shear k n (2 + f.totalDegree) (monomial w (f.coeff w))).degreeOf 0 := by
  have hu : 0 < 2 + f.totalDegree := by omega
  rw [degreeOf_zero_t v hu (mem_support_iff.mp hv), degreeOf_zero_t w hu (mem_support_iff.mp hw)]
  refine sum_r_mul_ne v w (by omega) (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

private lemma leadingCoeff_finSuccEquiv_t {u : ℕ} (hu : 0 < u) (a : k) :
    (finSuccEquiv k n (shear k n u (monomial v a))).leadingCoeff = algebraMap k _ a := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_prod]
    have h0 : (finSuccEquiv k n (shear k n u (MvPolynomial.C a))).leadingCoeff = algebraMap k _ a := by
      have : shear k n u (MvPolynomial.C a) = MvPolynomial.C a := (shear k n u).commutes a
      rw [this]; simp [finSuccEquiv_apply]
    have : ∀ j, (finSuccEquiv k n (shear k n u (X j))).leadingCoeff = 1 := fun j ↦ by
      cases j using Fin.cases with
      | zero => simp [shear_X_zero, finSuccEquiv_X_zero]
      | succ i =>
        simp only [shear_X_succ, map_add (f := _), map_pow, finSuccEquiv_X_succ, finSuccEquiv_X_zero]
        rw [add_comm (Polynomial.C _), Polynomial.leadingCoeff_X_pow_add_C (pow_pos hu _)]
    simp only [h0, map_pow, Polynomial.leadingCoeff_pow, this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

theorem shear_leadingCoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (shear k n (2 + f.totalDegree) f)).leadingCoeff := by
  let T := shear k n (2 + f.totalDegree)
  change IsUnit (finSuccEquiv k n (T f)).leadingCoeff
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T (monomial v (f.coeff v))).degreeOf 0) (support_nonempty.mpr fne)
  let h := fun w ↦ monomial w (f.coeff w)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n (T (h x))).degree <
      (finSuccEquiv k n (T (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply Polynomial.degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne f _ _ h1 vin (fun heq ↦ h2 (Finset.mem_singleton.mpr heq))
  have hcoeff : (finSuccEquiv k n (T (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n (T (h v))).leadingCoeff := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum]
    rw [add_comm]
    apply Polynomial.leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| Polynomial.degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n (T (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| Polynomial.degree_eq_bot.mp x)).mpr vs
  have hf : f = h v + ∑ x ∈ f.support \ {v}, h x := calc
    f = ∑ x ∈ f.support, h x := f.support_sum_monomial_coeff.symm
    _ = _ := Finset.sum_eq_add_sum_sdiff_singleton_of_mem vin h
  rw [← hf] at hcoeff
  have hlead : (finSuccEquiv k n (T (h v))).leadingCoeff = algebraMap k _ (f.coeff v) :=
    leadingCoeff_finSuccEquiv_t v (by omega) (f.coeff v)
  rw [hcoeff, hlead, algebraMap_eq]
  exact (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

end lead

end GlobalTheory.NoetherInt

namespace GlobalTheory.NoetherInt

open MvPolynomial

theorem exists_coeff_map_eq_C {K : Type*} [Field K] {n : ℕ} (φ : ℤ →+* K)
    (g : MvPolynomial (Fin (n + 1)) ℤ) (hg : MvPolynomial.map φ g ≠ 0) :
    ∃ (u k : ℕ) (a : K), a ≠ 0 ∧
      MvPolynomial.map φ ((finSuccEquiv ℤ n (shear ℤ n u g)).coeff k) = MvPolynomial.C a := by
  set f := MvPolynomial.map φ g with hf
  have hU := shear_leadingCoeff_isUnit f hg
  obtain ⟨a, ha, hE⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hU
  refine ⟨2 + f.totalDegree, (finSuccEquiv K n (shear K n (2 + f.totalDegree) f)).natDegree, a,
    ha.ne_zero, ?_⟩
  rw [← Polynomial.coeff_map, map_finSuccEquiv, map_shear, ← hf]
  exact hE

theorem exists_primitive_of_aeval_eq_zero {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    {n : ℕ} (y : Fin n → S) (g : MvPolynomial (Fin n) ℤ) (hg0 : g ≠ 0)
    (hg : aeval y g = 0) (I : Ideal ℤ) (hI : I ≠ ⊤) :
    ∃ g₀ : MvPolynomial (Fin n) ℤ, aeval y g₀ = 0 ∧ ∃ v, g₀.coeff v ∉ I := by
  classical
  have hs : g.support.Nonempty := support_nonempty.mpr hg0
  obtain ⟨b, hb, hgcd⟩ := Finset.extract_gcd (fun v => g.coeff v) hs
  set d := g.support.gcd (fun v => g.coeff v) with hd
  have hd0 : d ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := hs
    have := (Finset.gcd_eq_zero_iff.mp h) v hv
    exact (mem_support_iff.mp hv) this
  let g₀ : MvPolynomial (Fin n) ℤ := ∑ v ∈ g.support, monomial v (b v)
  have hc : ∀ v, v ∈ g.support → g₀.coeff v = b v := by
    intro v hv
    simp [g₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hv]
  have hc' : ∀ v, v ∉ g.support → g₀.coeff v = 0 := by
    intro v hv
    simp only [g₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    exact Finset.sum_eq_zero fun w hw => if_neg (fun h : w = v => hv (h ▸ hw))
  have hgd : g = MvPolynomial.C d * g₀ := by
    ext v
    rw [MvPolynomial.coeff_C_mul]
    by_cases hv : v ∈ g.support
    · rw [hc v hv]; exact hb v hv
    · rw [hc' v hv, mul_zero]; exact notMem_support_iff.mp hv
  refine ⟨g₀, ?_, ?_⟩
  · have h1 : ((d : ℤ) : S) * aeval y g₀ = 0 := by
      rw [hgd, map_mul] at hg
      simpa using hg
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hd0)
  · by_contra hall
    push_neg at hall
    obtain ⟨l, hl⟩ := (IsPrincipalIdealRing.principal I).principal
    have hdvd : l ∣ g.support.gcd b := Finset.dvd_gcd fun v hv => by
      have := hall v
      rw [hc v hv, hl] at this
      exact Ideal.mem_span_singleton.mp this
    rw [hgcd] at hdvd
    exact hI (by rw [hl]; exact Ideal.span_singleton_eq_top.mpr (isUnit_of_dvd_one hdvd))

theorem quasiFiniteAt_iff {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : Ideal S)
    [q.IsPrime] :
    f.QuasiFiniteAt q ↔ ((algebraMap S (Localization.AtPrime q)).comp f).QuasiFinite := by
  letI := f.toAlgebra
  have : f = algebraMap R S := rfl
  rw [this, ← IsScalarTower.algebraMap_eq R S (Localization.AtPrime q),
    RingHom.quasiFinite_algebraMap]

end GlobalTheory.NoetherInt

namespace GlobalTheory.NoetherInt

open MvPolynomial

theorem exists_quasiFiniteAt_of_not_injective {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    (q : Ideal S) [q.IsPrime] {n : ℕ} (y : Fin (n + 1) → S)
    (h : (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q)
    (hy : ¬ Function.Injective (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S)) :
    ∃ y' : Fin n → S, (aeval y' : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q := by

  obtain ⟨g, hg0, hg⟩ : ∃ g : MvPolynomial (Fin (n + 1)) ℤ, g ≠ 0 ∧ aeval y g = 0 := by
    rw [injective_iff_map_eq_zero] at hy
    push_neg at hy
    obtain ⟨g, h1, h2⟩ := hy
    exact ⟨g, h2, h1⟩
  let L := algebraMap S (Localization.AtPrime q)
  let K := IsLocalRing.ResidueField (Localization.AtPrime q)
  let res : Localization.AtPrime q →+* K := IsLocalRing.residue _
  let ι : ℤ →+* K := Int.castRingHom K
  obtain ⟨g₁, hg₁, v, hv⟩ := exists_primitive_of_aeval_eq_zero y g hg0 hg (RingHom.ker ι)
    (RingHom.ker_ne_top ι)
  have hne : MvPolynomial.map ι g₁ ≠ 0 := by
    intro h0
    apply hv
    have := congrArg (AddMonoidAlgebra.coeff · v) h0
    rw [MvPolynomial.coeff_map] at this
    simpa [RingHom.mem_ker] using this
  obtain ⟨u, k, a, ha, hc⟩ := exists_coeff_map_eq_C ι g₁ hne

  let σ := shear ℤ n u
  let e := finSuccEquiv ℤ n
  let y₁ : Fin (n + 1) → S := fun i => aeval y (σ.symm (X i))
  have h1 : ∀ p, aeval y₁ p = aeval y (σ.symm p) := by
    intro p
    have : (aeval y₁ : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S) =
        (aeval y).comp (σ.symm : _ →ₐ[ℤ] _) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [y₁]
    exact DFunLike.congr_fun this p
  let y' : Fin n → S := fun i => y₁ i.succ
  let t := L (y₁ 0)
  let φ : MvPolynomial (Fin n) ℤ →+* Localization.AtPrime q :=
    L.comp (aeval y' : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom
  have key : ∀ p, Polynomial.eval₂ φ t (e p) = L (aeval y₁ p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [← Polynomial.coe_eval₂RingHom]
      simp only [eq_intCast, map_intCast]
    | add p r hp hr => simp [hp, hr, Polynomial.eval₂_add]
    | mul_X p i hp =>
      simp only [map_mul, Polynomial.eval₂_mul, hp]
      congr 1
      cases i using Fin.cases with
      | zero => simp [e, t, finSuccEquiv_X_zero]
      | succ i => simp [e, φ, y', finSuccEquiv_X_succ]
  let E : Polynomial (MvPolynomial (Fin n) ℤ) ≃+* MvPolynomial (Fin (n + 1)) ℤ :=
    (e.symm.trans σ.symm).toRingEquiv
  have hE : Polynomial.eval₂RingHom φ t =
      (L.comp (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S).toRingHom).comp E.toRingHom := by
    refine RingHom.ext fun p => ?_
    obtain ⟨p, rfl⟩ := e.surjective p
    rw [Polynomial.coe_eval₂RingHom, key, h1]
    simp [E]
  have hq : (Polynomial.eval₂RingHom φ t).QuasiFinite := by
    rw [hE]
    exact ((quasiFiniteAt_iff _ q).mp h).comp (RingHom.QuasiFinite.of_finite E.finite)
  have hG : Polynomial.eval₂ φ t (e (σ g₁)) = 0 := by
    rw [key, h1]; simp [hg₁]
  have hunit : IsUnit (φ ((e (σ g₁)).coeff k)) := by
    have hΦ : res.comp φ =
        (MvPolynomial.eval fun i => res (φ (X i))).comp (MvPolynomial.map ι) := by
      apply MvPolynomial.ringHom_ext
      · intro m; simp [ι]
      · intro i; simp
    have h2 : res (φ ((e (σ g₁)).coeff k)) = a := by
      have : res (φ ((e (σ g₁)).coeff k)) = MvPolynomial.eval (fun i => res (φ (X i)))
          (MvPolynomial.map ι ((e (σ g₁)).coeff k)) := DFunLike.congr_fun hΦ ((e (σ g₁)).coeff k)
      rw [this]
      simp only [e, σ]
      rw [hc]; simp
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (h2 ▸ ha)
  exact ⟨y', (quasiFiniteAt_iff _ q).mpr (quasiFinite_of_isUnit_coeff φ t hq _ hG k hunit)⟩

theorem exists_algebraicIndependent_of_quasiFiniteAt {S : Type*} [CommRing S] [IsDomain S]
    [CharZero S] (q : Ideal S) [q.IsPrime] (n : ℕ) :
    ∀ y : Fin n → S, (aeval y : MvPolynomial (Fin n) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q →
    ∃ (r : ℕ) (y' : Fin r → S), AlgebraicIndependent ℤ y' ∧
      (aeval y' : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.QuasiFiniteAt q := by
  induction n with
  | zero =>
    intro y h
    refine ⟨0, y, ?_, h⟩
    rw [algebraicIndependent_empty_type_iff]
    exact Int.cast_injective
  | succ n ih =>
    intro y h
    by_cases hy : Function.Injective (aeval y : MvPolynomial (Fin (n + 1)) ℤ →ₐ[ℤ] S)
    · exact ⟨n + 1, y, hy, h⟩
    · obtain ⟨y', hy'⟩ := exists_quasiFiniteAt_of_not_injective q y h hy
      exact ih y' hy'

end GlobalTheory.NoetherInt

namespace GlobalTheory

open IsLocalRing

theorem exists_algebraicIndependent_int_quasiFiniteAt :
    ∀ (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra.FiniteType ℤ S] (𝔮 : Ideal S) [𝔮.IsPrime], ∃ (r : ℕ) (y : Fin r → S), AlgebraicIndependent ℤ y ∧ @Algebra.QuasiFiniteAt (MvPolynomial (Fin r) ℤ) S _ _ (MvPolynomial.aeval y : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.toAlgebra 𝔮 _ := by
  intro S _ _ _ hS 𝔮 _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hS
  have hfe : (MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) :
      MvPolynomial (Fin n) ℤ →ₐ[ℤ] S) = f := by
    apply MvPolynomial.algHom_ext
    intro i; simp
  refine NoetherInt.exists_algebraicIndependent_of_quasiFiniteAt 𝔮 n
    (fun i => f (MvPolynomial.X i)) ?_
  rw [NoetherInt.quasiFiniteAt_iff, hfe]
  refine RingHom.QuasiFinite.comp ?_ (RingHom.QuasiFinite.of_finite
    (RingHom.Finite.of_surjective _ hf))
  exact RingHom.quasiFinite_algebraMap.2 (.of_isLocalization 𝔮.primeCompl)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsQuasiFinitePolynomialMapStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasi_finite_polynomial_map : ∀ (S : Type) [CommRing S] [IsDomain S] [CharZero S] [Algebra.FiniteType ℤ S] (𝔮 : Ideal S) [𝔮.IsPrime], ∃ (r : ℕ) (y : Fin r → S), AlgebraicIndependent ℤ y ∧ @Algebra.QuasiFiniteAt (MvPolynomial (Fin r) ℤ) S _ _ (MvPolynomial.aeval y : MvPolynomial (Fin r) ℤ →ₐ[ℤ] S).toRingHom.toAlgebra 𝔮 _ := by
  first | exact @GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt | exact GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt | (intros; apply GlobalTheory.exists_algebraicIndependent_int_quasiFiniteAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalLocalIsLocalisationOfFiniteOverPolynomialA
open IsLocalRing

namespace GlobalTheory.QFNN

theorem integralClosure_of_fractions (P A : Type) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CharZero P] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Algebra P A] [Algebra.EssFiniteType P A]
    (hinj : Function.Injective (algebraMap P A))
    (hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b) :
    Module.Finite P (integralClosure P A) ∧ IsIntegrallyClosed (integralClosure P A) ∧
      Function.Injective (algebraMap P (integralClosure P A)) ∧
      IsLocalization.AtPrime A
        ((maximalIdeal A).comap (algebraMap (integralClosure P A) A)) := by
  let K := FractionRing A
  let F := FractionRing P
  let B := integralClosure P A
  have hιinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hPK : Function.Injective (algebraMap P K) := by
    rw [IsScalarTower.algebraMap_eq P A K]
    exact hιinj.comp hinj
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr hPK
  letI : Algebra F K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P F K := FractionRing.isScalarTower_liftAlgebra P K

  have halgA : ∀ a : A, IsAlgebraic P (algebraMap A K a) := by
    intro a
    obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
    have ht0 : algebraMap A K t ≠ 0 := by
      simpa using (map_ne_zero_iff _ hιinj).mpr hu.ne_zero
    have : algebraMap A K a = algebraMap A K b * (algebraMap A K t)⁻¹ := by
      rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    rw [this]
    exact (hb.algebraMap (B := K)).isAlgebraic.mul (ht.algebraMap (B := K)).isAlgebraic.inv
  haveI hPKalg : Algebra.IsAlgebraic P K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, s, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [div_eq_mul_inv]
    exact (halgA a).mul (halgA s).inv
  haveI : Algebra.IsAlgebraic F K := (IsFractionRing.comap_isAlgebraic_iff (A := P) (K := F)).mp hPKalg
  haveI : Algebra.EssFiniteType A K := .of_isLocalization K (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType P K := .comp P A K
  haveI : Algebra.EssFiniteType F K := .of_comp P F K
  haveI : FiniteDimensional F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective P F)
  haveI hic : IsIntegralClosure B P K :=
    { algebraMap_injective := hιinj.comp Subtype.val_injective
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := A))
          have ha : IsIntegral P a := (isIntegral_algebraMap_iff (A := A) (B := K)).mp hx
          exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact (y.2.algebraMap (B := K)) }
  haveI hfrac : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension P F K B
  refine ⟨IsIntegralClosure.finite P F K B, ?_, ?_, ?_⟩
  · refine (isIntegrallyClosed_iff K).mpr ?_
    intro x hx
    have hxP : IsIntegral P x := isIntegral_trans x hx
    exact (IsIntegralClosure.isIntegral_iff (A := B)).mp hxP
  · intro x y h
    exact hinj (congrArg Subtype.val h)
  · have hne : ∀ b : B, b ∈ ((maximalIdeal A).comap (algebraMap B A)).primeCompl →
        IsUnit (algebraMap B A b) := by
      intro b hb
      by_contra hu
      exact hb ((mem_maximalIdeal _).mpr hu)
    refine ⟨fun y => hne y.1 y.2, fun a => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
      refine ⟨(⟨b, hb⟩, ⟨⟨t, ht⟩, ?_⟩), hab⟩
      intro hmem
      exact (mem_maximalIdeal _).mp hmem hu
    · have : x = y := Subtype.val_injective h
      rw [this]

end GlobalTheory.QFNN

theorem GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B)
      (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B)
      (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime),
      Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  intro A _ _ _ _ _ hess
  obtain ⟨S₀, M, hft, hlocM⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ A).mp hess
  let 𝔮 : Ideal S₀ := (maximalIdeal A).comap (algebraMap S₀ A)
  haveI h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  have hunit : ∀ s : S₀, s ∉ 𝔮 → IsUnit (algebraMap S₀ A s) := by
    intro s hs
    by_contra hu
    exact hs ((mem_maximalIdeal _).mpr hu)
  have hM : M ≤ 𝔮.primeCompl := by
    intro m hm hmem
    exact (mem_maximalIdeal _).mp hmem (IsLocalization.map_units A ⟨m, hm⟩)
  haveI hat : IsLocalization 𝔮.primeCompl A :=
    IsLocalization.of_le M _ hM (fun s hs => hunit s hs)
  haveI : CharZero S₀ := (algebraMap S₀ A).charZero
  obtain ⟨r, y, hy, hqf⟩ := GlobalTheory.T.exists_quasi_finite_polynomial_map S₀ 𝔮
  let P := MvPolynomial (Fin r) ℤ
  letI algPS : Algebra P S₀ := (MvPolynomial.aeval y : P →ₐ[ℤ] S₀).toRingHom.toAlgebra
  letI algPA : Algebra P A := ((algebraMap S₀ A).comp (algebraMap P S₀)).toAlgebra
  haveI : IsScalarTower P S₀ A := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ P S₀ := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsScalarTower ℤ P A := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType P S₀ := .of_restrictScalars_finiteType ℤ P S₀
  haveI : Algebra.EssFiniteType P A := .of_comp ℤ P A
  have hinj : Function.Injective (algebraMap P A) :=
    (Subtype.val_injective : Function.Injective (algebraMap S₀ A)).comp
      ((algebraicIndependent_iff_injective_aeval).mp hy)
  have hzmp : Algebra.ZariskisMainProperty P 𝔮 := Algebra.ZariskisMainProperty.of_finiteType 𝔮
  obtain ⟨ρ, hρq, hρ, H⟩ := Algebra.zariskisMainProperty_iff.mp hzmp
  have hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b := by
    intro a
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj 𝔮.primeCompl a
    obtain ⟨m₁, h₁⟩ := H x
    obtain ⟨m₂, h₂⟩ := H s
    have hb : IsIntegral P (ρ ^ (m₁ + m₂) * x) := by
      have : ρ ^ (m₁ + m₂) * x = ρ ^ m₂ * (ρ ^ m₁ * x) := by ring
      rw [this]
      exact (hρ.pow _).mul h₁
    have ht : IsIntegral P (ρ ^ (m₁ + m₂) * (s : S₀)) := by
      have : ρ ^ (m₁ + m₂) * (s : S₀) = ρ ^ m₁ * (ρ ^ m₂ * (s : S₀)) := by ring
      rw [this]
      exact (hρ.pow _).mul h₂
    refine ⟨_, _, hb.algebraMap (B := A), ht.algebraMap (B := A), hunit _ ?_, ?_⟩
    · exact h𝔮.mul_notMem (fun h => hρq (h𝔮.mem_of_pow_mem _ h)) s.2
    · simp only [map_mul, map_pow]
      rw [← hxs]
      ring
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.QFNN.integralClosure_of_fractions P A hinj hloc
  exact ⟨r, integralClosure P A, inferInstance, inferInstance, h2, inferInstance, h1, inferInstance,
    _, Ideal.comap_isPrime _ _, h3, h4⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalLocalIsLocalisationOfFiniteOverPolynomialAStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B) (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime), Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  first | exact @GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | exact GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial | (intros; apply GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorProdFst
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorProdFst
open IsLocalRing Polynomial

namespace GlobalTheory

theorem conductor_prod_fst (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S]
    (e : S ≃+* R × S') (d : S)
    (hd : ∀ c : FractionRing S, IsIntegral S c →
      ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) :
    ∀ c : FractionRing R, IsIntegral R c →
      ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  intro c hc
  let g : S →+* FractionRing R × FractionRing S' :=
    (RingHom.prodMap (algebraMap R (FractionRing R)) (algebraMap S' (FractionRing S'))).comp
      e.toRingHom
  have hgx : ∀ x : S, g x = (algebraMap R (FractionRing R) (e x).1,
      algebraMap S' (FractionRing S') (e x).2) := fun x => rfl
  have hg : ∀ y : nonZeroDivisors S, IsUnit (g y) := by
    intro y
    rw [hgx, Prod.isUnit_iff]
    have h1 : (e y).1 ∈ nonZeroDivisors R := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (z, 0) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).1) this
      simpa using this
    have h2 : (e y).2 ∈ nonZeroDivisors S' := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      have h0 : e.symm (0, z) * (y : S) = 0 := by
        apply e.injective
        rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
        ext <;> simp [hz]
      have := (mul_right_mem_nonZeroDivisors_eq_zero_iff y.2).mp h0
      have := congrArg (fun w => (e w).2) this
      simpa using this
    exact ⟨IsLocalization.map_units (FractionRing R) (⟨_, h1⟩ : nonZeroDivisors R),
      IsLocalization.map_units (FractionRing S') (⟨_, h2⟩ : nonZeroDivisors S')⟩
  let Θ : FractionRing S →+* FractionRing R × FractionRing S' := IsLocalization.lift hg
  have hΘ : ∀ x : S, Θ (algebraMap S (FractionRing S) x) = g x := fun x =>
    IsLocalization.lift_eq hg x
  have hΘinj : Function.Injective Θ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h; rw [(IsFractionRing.injective S (FractionRing S)) h]
    · intro h
      have h' : e x = e y := by
        rw [hgx, hgx] at h
        ext
        · exact IsFractionRing.injective R (FractionRing R) (congrArg Prod.fst h)
        · exact IsFractionRing.injective S' (FractionRing S') (congrArg Prod.snd h)
      rw [e.injective h']

  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
  have hb' : e.symm ((b : R), (1 : S')) ∈ nonZeroDivisors S := by
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    have hz' := congrArg e hz
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero] at hz'
    have h1 : (e z).1 * b = 0 := congrArg Prod.fst hz'
    have h2 : (e z).2 * 1 = 0 := congrArg Prod.snd hz'
    rw [mul_right_mem_nonZeroDivisors_eq_zero_iff b.2] at h1
    rw [mul_one] at h2
    apply e.injective
    rw [map_zero]
    ext <;> simp [h1, h2]
  set c := IsLocalization.mk' (FractionRing R) a b with hcdef
  let b' : nonZeroDivisors S := ⟨_, hb'⟩
  let c' : FractionRing S := IsLocalization.mk' (FractionRing S) (e.symm (a, 0)) b'
  have hΘc : Θ c' = (c, 0) := by
    have hs := IsLocalization.mk'_spec (FractionRing S) (e.symm (a, 0)) b'
    have hs2 := congrArg Θ hs
    rw [map_mul, hΘ, hΘ] at hs2
    have hu := hg b'
    have hcs := IsLocalization.mk'_spec (FractionRing R) a b
    rw [← hu.mul_left_inj, hs2]
    rw [hgx, hgx]
    simp only [b', RingEquiv.apply_symm_apply, Prod.mk_mul_mk, map_zero, map_one, mul_one,
      zero_mul]
    rw [hcs]
  have hf : Function.Surjective ((RingHom.fst R S').comp e.toRingHom) := by
    intro r
    exact ⟨e.symm (r, 0), by simp⟩
  have hc' : IsIntegral S c' := by
    obtain ⟨p, hpm, hp⟩ := hc
    obtain ⟨q, hqmap, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
      (f := (RingHom.fst R S').comp e.toRingHom) (p := p)
      ((lifts_iff_coeff_lifts p).mpr (fun n => hf _)) hpm
    refine ⟨X * q, monic_X.mul hqm, ?_⟩
    apply hΘinj
    rw [Polynomial.hom_eval₂, map_zero, hΘc, eval₂_mul, eval₂_X]
    have hfst : (RingHom.fst (FractionRing R) (FractionRing S')).comp
        (Θ.comp (algebraMap S (FractionRing S))) =
        (algebraMap R (FractionRing R)).comp ((RingHom.fst R S').comp e.toRingHom) := by
      ext x
      simp [hΘ, hgx]
    have h1 : (eval₂ (Θ.comp (algebraMap S (FractionRing S))) (c, 0) q).1 = 0 := by
      have := Polynomial.hom_eval₂ q (Θ.comp (algebraMap S (FractionRing S)))
        (RingHom.fst (FractionRing R) (FractionRing S')) (c, 0)
      simp only [RingHom.coe_fst] at this
      rw [this, hfst, ← eval₂_map, hqmap]
      exact hp
    ext
    · simp [h1]
    · simp
  obtain ⟨s, hs⟩ := hd c' hc'
  refine ⟨(e s).1, ?_⟩
  have h := congrArg (fun z => (Θ z).1) hs
  simp only [map_mul, hΘ, hΘc, hgx, Prod.fst_mul] at h
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorProdFstStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor : ∀ (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S] (e : S ≃+* R × S') (d : S), (∀ c : FractionRing S, IsIntegral S c → ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) → ∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  first | exact @GlobalTheory.conductor_prod_fst | exact GlobalTheory.conductor_prod_fst | (intros; apply GlobalTheory.conductor_prod_fst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConductorAdicCompletionEssFiniteType
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_finite_over_localization_atPrime_below (P B A : Type) [CommRing P] [CommRing B]
    [IsDomain B] [Algebra P B] [Module.Finite P B] [CommRing A] [IsLocalRing A] [Algebra B A]
    (𝔫 : Ideal B) [𝔫.IsPrime] [IsLocalization.AtPrime A 𝔫]
    (hinj : Function.Injective (algebraMap P B)) :
    ∃ (p : Ideal P) (_ : p.IsPrime) (C : Type) (_ : CommRing C) (_ : IsDomain C)
      (_ : Algebra (Localization.AtPrime p) C) (_ : Module.Finite (Localization.AtPrime p) C)
      (_ : Algebra C A) (𝔪 : Ideal C) (_ : 𝔪.IsPrime),
      Function.Injective (algebraMap (Localization.AtPrime p) C) ∧ IsLocalization.AtPrime A 𝔪 ∧
        𝔪.comap (algebraMap (Localization.AtPrime p) C) = maximalIdeal (Localization.AtPrime p) := by
  classical
  let p : Ideal P := 𝔫.comap (algebraMap P B)
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  let M : Submonoid B := Algebra.algebraMapSubmonoid B p.primeCompl
  have hMle : M ≤ 𝔫.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩ h
    exact hs (Ideal.mem_comap.mpr h)
  have hM0 : M ≤ nonZeroDivisors B := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hs ?_
    show algebraMap P B s ∈ 𝔫
    rw [h0]
    exact 𝔫.zero_mem
  have : IsDomain (Localization M) := IsLocalization.isDomain_localization hM0
  let algCA : Algebra (Localization M) A :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) A M 𝔫.primeCompl hMle
  have : IsScalarTower B (Localization M) A :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  let 𝔪 : Ideal (Localization M) := (maximalIdeal A).comap (algebraMap (Localization M) A)
  have h𝔪 : 𝔪.IsPrime := Ideal.comap_isPrime _ _
  have hNA : IsLocalization (𝔫.primeCompl.map (algebraMap B (Localization M))) A :=
    IsLocalization.isLocalization_of_submonoid_le (Localization M) A M 𝔫.primeCompl hMle
  have hunitB : ∀ b : B, IsUnit (algebraMap B A b) ↔ b ∈ 𝔫.primeCompl := fun b =>
    IsLocalization.AtPrime.isUnit_to_map_iff A 𝔫 b
  have hA : IsLocalization.AtPrime A 𝔪 := by
    refine IsLocalization.isLocalization_of_is_exists_mul_mem (S := A)
      (M := 𝔫.primeCompl.map (algebraMap B (Localization M))) (N := 𝔪.primeCompl) ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩ h
      have hu : IsUnit (algebraMap B A b) := (hunitB b).mpr hb
      rw [IsScalarTower.algebraMap_apply B (Localization M) A] at hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h) hu
    · rintro ⟨x, hx⟩
      obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
      have key : algebraMap B A b =
          algebraMap B A s * algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s) := by
        rw [IsScalarTower.algebraMap_apply B (Localization M) A b,
          IsScalarTower.algebraMap_apply B (Localization M) A s, ← map_mul, IsLocalization.mk'_spec']
      refine ⟨algebraMap B (Localization M) s, b, ?_, (IsLocalization.mk'_spec' _ _ _).symm⟩
      have hs : IsUnit (algebraMap B A s) := (hunitB s).mpr (hMle s.2)
      have hx' : IsUnit (algebraMap (Localization M) A (IsLocalization.mk' (Localization M) b s)) := by
        by_contra hn
        exact hx (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn))
      refine (hunitB b).mp ?_
      rw [key]
      exact hs.mul hx'
  have hcomapB : 𝔪.comap (algebraMap B (Localization M)) = 𝔫 := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact IsLocalization.AtPrime.under_maximalIdeal A 𝔫
  refine ⟨p, hp, Localization M, inferInstance, inferInstance, inferInstance, inferInstance, algCA,
    𝔪, h𝔪, ?_, hA, ?_⟩
  · exact localizationAlgebra_injective (S := B) (M := p.primeCompl) (Localization.AtPrime p)
      (Localization M) hinj
  · let Q : Ideal (Localization.AtPrime p) :=
      𝔪.comap (algebraMap (Localization.AtPrime p) (Localization M))
    have hQ : Q.comap (algebraMap P (Localization.AtPrime p)) = p := by
      show (𝔪.comap _).comap _ = p
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq P B (Localization M), ← Ideal.comap_comap, hcomapB]
    have h1 : Q = p.map (algebraMap P (Localization.AtPrime p)) := by
      have h2 := IsLocalization.map_under p.primeCompl (Localization.AtPrime p) Q
      rw [Ideal.under_def, hQ] at h2
      exact h2.symm
    show Q = _
    rw [h1]
    exact Localization.AtPrime.map_eq_maximalIdeal

theorem exists_conductor_adicCompletion_of_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ x : A, x ≠ 0 ∧ ∀ c : FractionRing (AdicCompletion (maximalIdeal A) A), IsIntegral (AdicCompletion (maximalIdeal A) A) c → ∃ s : AdicCompletion (maximalIdeal A) A, algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) s = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) (algebraMap A (AdicCompletion (maximalIdeal A) A) x) * c := by
  intro A _ _ _ _ _ _
  obtain ⟨r, B, _, _, _, _, _, _, 𝔫, _, hinj, hloc⟩ := GlobalTheory.T.injective_and_isLocalization_of_finite_over_mvPolynomial A
  obtain ⟨p, _, C, _, _, _, _, _, 𝔪, _, hinjC, hlocC, hcomap⟩ :=
    exists_finite_over_localization_atPrime_below (MvPolynomial (Fin r) ℤ) B A 𝔫 hinj
  have hTreg : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  obtain ⟨_, _⟩ := GlobalTheory.T.regular_local_ring_normal_domain (Localization.AtPrime p)
  have := GlobalTheory.T.isRegularLocalRing_adicCompletion' (Localization.AtPrime p)
  obtain ⟨_, _⟩ := GlobalTheory.T.regular_local_ring_normal_domain
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))
  have : CharZero (Localization.AtPrime p) :=
    charZero_of_injective_algebraMap (R := MvPolynomial (Fin r) ℤ)
      (IsLocalization.injective (M := p.primeCompl) (S := Localization.AtPrime p)
        p.primeCompl_le_nonZeroDivisors)
  have hTU : Function.Injective (algebraMap (Localization.AtPrime p)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))) := by
    intro x y h
    exact AdicCompletion.of_injective (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) h
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_ne_zero_mul_integral_eq_tensor (Localization.AtPrime p)
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) C hTU hinjC
  obtain ⟨S', _, e, he⟩ := GlobalTheory.T.exists_ringEquiv_adicCompletion_localization_prod (Localization.AtPrime p) C A 𝔪 hcomap
  have key := GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor (AdicCompletion (maximalIdeal A) A) S' _ e _ hd
  have hed : (e (algebraMap (Localization.AtPrime p) _ d)).1 =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (algebraMap C A (algebraMap _ C d)) := by
    rw [Algebra.TensorProduct.algebraMap_apply', he]
  refine ⟨algebraMap C A (algebraMap _ C d), ?_, fun c hc => ?_⟩
  · intro h0
    apply hd0
    apply hinjC
    apply IsLocalization.injective (M := 𝔪.primeCompl) (S := A) 𝔪.primeCompl_le_nonZeroDivisors
    rw [h0, map_zero, map_zero]
  · obtain ⟨s, hs⟩ := key c hc
    exact ⟨s, by rw [hs, hed]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConductorAdicCompletionEssFiniteTypeStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conductor_adicCompletion_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ x : A, x ≠ 0 ∧ ∀ c : FractionRing (AdicCompletion (maximalIdeal A) A), IsIntegral (AdicCompletion (maximalIdeal A) A) c → ∃ s : AdicCompletion (maximalIdeal A) A, algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) s = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) (algebraMap A (AdicCompletion (maximalIdeal A) A) x) * c := by
  first | exact @GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType | exact GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType | (intros; apply GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType <;> assumption)
end
