module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
open Matrix

namespace GlobalTheory.RegSS

private theorem aeval_mul_mulVec {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f g : Polynomial K) (v : n → K) :
    Polynomial.aeval M (f * g) *ᵥ v = Polynomial.aeval M f *ᵥ (Polynomial.aeval M g *ᵥ v) := by
  rw [map_mul, Matrix.mulVec_mulVec]

private theorem det_aeval_eq_zero_of_irreducible_dvd_charpoly {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) {q : Polynomial K} (hq : Irreducible q)
    (hd : q ∣ M.charpoly) : (Polynomial.aeval M q).det = 0 := by
  have : Fact (Irreducible q) := ⟨hq⟩
  obtain ⟨s, hs⟩ := hd
  have hα : Polynomial.aeval (AdjoinRoot.root q) q = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hroot : (q.map (algebraMap K (AdjoinRoot q))).IsRoot (AdjoinRoot.root q) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, hα]
  obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hN : (Matrix.scalar n (AdjoinRoot.root q) - M.map (algebraMap K (AdjoinRoot q))).det = 0 := by
    rw [← Matrix.eval_charpoly, Matrix.charpoly_map, hs, Polynomial.map_mul, Polynomial.eval_mul,
      Polynomial.eval_map_algebraMap, hα, zero_mul]
  have hmap : Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q =
      (Polynomial.aeval M q).map (algebraMap K (AdjoinRoot q)) := by
    exact Polynomial.aeval_algHom_apply ((Algebra.ofId K (AdjoinRoot q)).mapMatrix (m := n)) M q
  have hfac : Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q =
      (M.map (algebraMap K (AdjoinRoot q)) - Matrix.scalar n (AdjoinRoot.root q)) *
        Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) g := by
    rw [← Polynomial.aeval_map_algebraMap (AdjoinRoot q), hg, map_mul, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C]
    congr 2
  have h2 : (Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q).det = 0 := by
    rw [hfac, Matrix.det_mul, ← neg_sub, Matrix.det_neg, hN, mul_zero, zero_mul]
  have h3 : algebraMap K (AdjoinRoot q) (Polynomial.aeval M q).det = 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hmap, h2]
  exact (map_eq_zero_iff _ (algebraMap K (AdjoinRoot q)).injective).mp h3

private theorem exists_vec_annihilator_eq_of_dvd_charpoly {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hsq : Squarefree M.charpoly) (q : Polynomial K) :
    q ∣ M.charpoly → ∃ w : n → K, Polynomial.aeval M q *ᵥ w = 0 ∧
      ∀ f : Polynomial K, Polynomial.aeval M f *ᵥ w = 0 → q ∣ f := by
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro h
    exact absurd (zero_dvd_iff.mp h) M.charpoly_monic.ne_zero
  · intro x hx _
    exact ⟨0, Matrix.mulVec_zero _, fun _ _ => hx.dvd⟩
  · intro r π _ hπ ih hd
    obtain ⟨wr, hwr0, hwr⟩ := ih (dvd_trans (dvd_mul_left r π) hd)
    obtain ⟨wp, hwpne, hwp0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      (det_aeval_eq_zero_of_irreducible_dvd_charpoly M hπ.irreducible (dvd_trans (dvd_mul_right π r) hd))
    have hcop : IsCoprime π r := by
      rw [hπ.coprime_iff_not_dvd]
      rintro ⟨t, rfl⟩
      exact hπ.not_isUnit (hsq π (dvd_trans ⟨t, by ring⟩ hd))
    have hwp : ∀ f : Polynomial K, Polynomial.aeval M f *ᵥ wp = 0 → π ∣ f := by
      intro f hf
      by_contra hn
      obtain ⟨a, b, hab⟩ := hπ.coprime_iff_not_dvd.mpr hn
      apply hwpne
      have h0 : Polynomial.aeval M (a * π + b * f) *ᵥ wp = 0 := by
        rw [map_add (f := _), Matrix.add_mulVec, aeval_mul_mulVec, aeval_mul_mulVec, hwp0, hf,
          Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
      rwa [hab, map_one, Matrix.one_mulVec] at h0
    refine ⟨wr + wp, ?_, ?_⟩
    · have e1 : Polynomial.aeval M (π * r) *ᵥ wr = 0 := by
        rw [aeval_mul_mulVec, hwr0, Matrix.mulVec_zero]
      have e2 : Polynomial.aeval M (π * r) *ᵥ wp = 0 := by
        rw [mul_comm π r, aeval_mul_mulVec, hwp0, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, e1, e2, add_zero]
    · intro f hf
      have hfp : Polynomial.aeval M (f * π) *ᵥ wp = 0 := by
        rw [aeval_mul_mulVec, hwp0, Matrix.mulVec_zero]
      have hfw : Polynomial.aeval M (f * π) *ᵥ (wr + wp) = 0 := by
        rw [mul_comm f π, aeval_mul_mulVec, hf, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, hfp, add_zero] at hfw
      have hrw : Polynomial.aeval M (f * r) *ᵥ wr = 0 := by
        rw [aeval_mul_mulVec, hwr0, Matrix.mulVec_zero]
      have hgw : Polynomial.aeval M (f * r) *ᵥ (wr + wp) = 0 := by
        rw [mul_comm f r, aeval_mul_mulVec, hf, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, hrw, zero_add] at hgw
      exact hcop.mul_dvd (hcop.dvd_of_dvd_mul_right (hwp _ hgw))
        (hcop.symm.dvd_of_dvd_mul_right (hwr _ hfw))

theorem cyclicField : GlobalTheory.RegSS.CyclicField := by
  intro K _ n _ _ M hsep
  obtain ⟨v, -, hv⟩ := exists_vec_annihilator_eq_of_dvd_charpoly M hsep.squarefree M.charpoly dvd_rfl
  refine ⟨v, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hc0
  set e := Fintype.equivFin n
  set f : Polynomial K := ∑ i : Fin (Fintype.card n),
    Polynomial.C (c (e.symm i)) * Polynomial.X ^ (i : ℕ) with hfdef
  have haeval : Polynomial.aeval M f = ∑ j : n, c j • M ^ ((e j : ℕ)) := by
    rw [hfdef, ← Equiv.sum_comp e]
    simp [Algebra.smul_def]
  have hf : Polynomial.aeval M f *ᵥ v = 0 := by
    rw [← hc, haeval]
    ext k
    simp only [krylov, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hf0 : f = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt (hv f hf) ?_
    rw [Matrix.charpoly_degree_eq_dim]
    exact Polynomial.degree_sum_fin_lt _
  funext j
  have hcoef := congrArg (fun g : Polynomial K => g.coeff (e j : ℕ)) hf0
  simpa [hfdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using hcoef

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyFieldStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicVector_of_separable_charpoly_field : GlobalTheory.RegSS.CyclicField := by
  first | exact @GlobalTheory.RegSS.cyclicField | exact GlobalTheory.RegSS.cyclicField | (intros; apply GlobalTheory.RegSS.cyclicField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorField
open GlobalTheory.RegSS Matrix

namespace GlobalTheory.RegSS.Semilocal

theorem _root_.GlobalTheory.RegSS.Semilocal.krylov_map_ringHom {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n A) (v : n → A) :
    (_root_.GlobalTheory.RegSS.krylov M v).map f = _root_.GlobalTheory.RegSS.krylov (M.map f) (f ∘ v) := by
  ext i j
  simp only [_root_.GlobalTheory.RegSS.krylov, Matrix.map_apply, Matrix.of_apply, RingHom.map_mulVec]
  congr 2
  exact RingHom.map_pow f.mapMatrix M _

theorem _root_.GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField :
    _root_.GlobalTheory.RegSS.CyclicField → _root_.GlobalTheory.RegSS.CyclicSemilocal := by
  intro hF A _ _ n _ _ M hM
  have hw : ∀ p : MaximalSpectrum A, ∃ w : n → A ⧸ p.asIdeal,
      IsUnit (_root_.GlobalTheory.RegSS.krylov (M.map (Ideal.Quotient.mk p.asIdeal)) w).det := by
    intro p
    haveI := p.isMaximal
    letI := Ideal.Quotient.field p.asIdeal
    exact hF _ n _ (by rw [Matrix.charpoly_map]; exact hM.map)
  choose w hw using hw
  have hcop : Pairwise (Function.onFun IsCoprime fun p : MaximalSpectrum A => p.asIdeal) :=
    fun p q hpq => Ideal.isCoprime_iff_sup_eq.mpr
      (p.isMaximal.coprime_of_ne q.isMaximal (mt MaximalSpectrum.ext hpq))
  have hs : ∀ y : ∀ p : MaximalSpectrum A, A ⧸ p.asIdeal,
      ∃ a : A, ∀ p, Ideal.Quotient.mk p.asIdeal a = y p := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.quotientInfToPiQuotient_surj hcop y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, fun p => by rw [← hx]; rfl⟩
  choose v hv using fun j => hs fun p => w p j
  refine ⟨v, ?_⟩
  by_contra h
  obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr h)
  let p : MaximalSpectrum A := ⟨I, hI⟩
  have hvp : (Ideal.Quotient.mk p.asIdeal) ∘ v = w p := funext fun j => hv j p
  have hzero : Ideal.Quotient.mk p.asIdeal (_root_.GlobalTheory.RegSS.krylov M v).det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [RingHom.map_det, RingHom.mapMatrix_apply, _root_.GlobalTheory.RegSS.Semilocal.krylov_map_ringHom, hvp] at hzero
  haveI := p.isMaximal
  exact (hw p).ne_zero hzero

end GlobalTheory.RegSS.Semilocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorFieldStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicVector_semilocal_of_cyclicVector_field : GlobalTheory.RegSS.CyclicField → GlobalTheory.RegSS.CyclicSemilocal := by
  first | exact @GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | exact GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField | (intros; apply GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndIntegral
set_option autoImplicit false

noncomputable section

open IsDedekindDomain IsLocalRing Formalism.L2.Pj

namespace GlobalTheory.CompleteValExt

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem exists_algebraMap_eq_iff (x : K) : (∃ a : V, algebraMap V K a = x) ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩
  have h1 := WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero
  rw [WithZero.log_one] at h1
  have h2 : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
    rw [← h1]
    unfold vV
    omega
  rw [h2]
  refine ⟨?_, fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) h⟩
  rintro ⟨a, rfl⟩
  exact HeightOneSpectrum.valuation_le_one _ a

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

theorem finite_and_integral_of_scale [IsAdicComplete (maximalIdeal V) V] (i : K →+* L) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (i z) = (r : ℤ) * vV V z) (h' : Finite (ResidueField W)) :
    i.Finite ∧ ∀ b : W, (i.comp (algebraMap V K)).IsIntegralElem (algebraMap W L b) := by
  have hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a) := fun a =>
    (exists_algebraMap_eq_iff _).2 (by
      rw [hi]; exact mul_nonneg (by positivity) ((exists_algebraMap_eq_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a) := hg0
  letI : Algebra V W := g.toAlgebra
  letI : Algebra K L := i.toAlgebra
  letI : Algebra V L := (i.comp (algebraMap V K)).toAlgebra
  have : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hgi : Function.Injective (algebraMap V W) := fun a b hab => by
    apply IsFractionRing.injective V K
    apply i.injective
    rw [← hg, ← hg]
    exact congrArg _ hab
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hgi
  have hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : i (algebraMap V K a) * algebraMap W L b = 1 := by
      rw [← hg, ← map_mul, ← map_one (algebraMap W L)]
      exact congrArg _ hb
    have h0 : algebraMap V K a ≠ 0 := fun h => by
      rw [h, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    have h1 : algebraMap W L b = i (algebraMap V K a)⁻¹ := by
      rw [map_inv₀]
      exact eq_inv_of_mul_eq_one_right hb'
    have h2 := (exists_algebraMap_eq_iff (V := W) _).1 ⟨b, h1⟩
    rw [hi] at h2
    obtain ⟨c, hc⟩ := (exists_algebraMap_eq_iff (V := V) _).2
      (nonneg_of_mul_nonneg_right h2 (by exact_mod_cast hr))
    refine (mem_maximalIdeal a).1 ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective V K ?_))
    rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]
  have hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hgi]
    exact IsDiscreteValuationRing.not_a_field V
  have htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have : Finite (W ⧸ maximalIdeal W) := h'
  have : Module.Finite V W := GlobalTheory.finite_of_forall_prime_mem hϖ.ne_zero (fun P hP h0 => by
    rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hϖ.not_isUnit) hne htop
  refine ⟨Module.Finite.of_isLocalization V W (nonZeroDivisors V), fun b => ?_⟩
  exact (Algebra.IsIntegral.isIntegral (R := V) b).algebraMap (B := L)

theorem finite_and_integral : ∀ (T T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r →
    (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → T'.FinRes →
    i.Finite ∧ ∀ b : T'.V, (i.comp (algebraMap T.V T.Fr)).IsIntegralElem (algebraMap T'.V T'.Fr b) :=
  fun T T' i _ hr hi h' => finite_and_integral_of_scale (V := T.V) (W := T'.V) i hr hi h'

end GlobalTheory.CompleteValExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructure
noncomputable section

open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

namespace GlobalTheory.RegSS.CycAlg

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def lowPoly (c : n → A) : A[X] :=
  ∑ j, c j • (X : A[X]) ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)

theorem aeval_lowPoly_mulVec (M : Matrix n n A) (v c : n → A) :
    aeval M (lowPoly c) *ᵥ v = krylov M v *ᵥ c := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lowPoly, map_sum, map_smul, map_pow, aeval_X, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [krylov, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_lowPoly (M : Matrix n n A) (p : A[X]) :
    ∃ c : n → A, p %ₘ M.charpoly = lowPoly c := by
  nontriviality A
  have h : (p %ₘ M.charpoly).degree < Fintype.card n := by
    rw [← Matrix.charpoly_degree_eq_dim M]
    exact degree_modByMonic_lt p M.charpoly_monic
  refine ⟨fun j => (p %ₘ M.charpoly).coeff (Fintype.equivFin n j), ?_⟩
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq (p %ₘ M.charpoly),
    Polynomial.sum_fin _ (by simp) h |>.symm]
  rw [lowPoly, ← Equiv.sum_comp (Fintype.equivFin n)]
  simp [Polynomial.smul_eq_C_mul]

theorem charpoly_dvd {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) {p : A[X]}
    (hp : aeval M p *ᵥ v = 0) : M.charpoly ∣ p := by
  obtain ⟨c, hc⟩ := exists_lowPoly M p
  rw [Matrix.aeval_eq_aeval_mod_charpoly, hc, aeval_lowPoly_mulVec] at hp
  have h0 : c = 0 := by
    have := congrArg (fun w => (krylov M v)⁻¹ *ᵥ w) hp
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h] using this
  rw [← modByMonic_eq_zero_iff_dvd M.charpoly_monic, hc, h0]
  simp [lowPoly]

theorem exists_aeval {M : Matrix n n A} (l : genAlg M) :
    ∃ p : A[X], aeval M p = (l : Matrix n n A) := by
  exact (Algebra.adjoin_singleton_eq_range_aeval A M).le l.2

theorem coe_aeval_gen (M : Matrix n n A) (p : A[X]) :
    ((aeval (gen M) p : genAlg M) : Matrix n n A) = aeval M p :=
  (Polynomial.aeval_algHom_apply (genAlg M).val (gen M) p).symm

def actOn (M : Matrix n n A) (v : n → A) : genAlg M →ₗ[A] (n → A) where
  toFun l := (l : Matrix n n A) *ᵥ v
  map_add' a b := Matrix.add_mulVec _ _ _
  map_smul' c a := Matrix.smul_mulVec c (a : Matrix n n A) v

theorem actOn_bijective {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) :
    Function.Bijective (actOn M v) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun l hl => ?_, fun w => ?_⟩
  · obtain ⟨p, hp⟩ := exists_aeval l
    have hl' : aeval M p *ᵥ v = 0 := by rw [hp]; exact hl
    obtain ⟨q, rfl⟩ := charpoly_dvd h hl'
    refine Subtype.ext ?_
    rw [← hp, map_mul, Matrix.aeval_self_charpoly, zero_mul]; rfl
  · refine ⟨aeval (gen M) (lowPoly ((krylov M v)⁻¹ *ᵥ w)), ?_⟩
    change ((aeval (gen M) _ : genAlg M) : Matrix n n A) *ᵥ v = w
    rw [coe_aeval_gen, aeval_lowPoly_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h,
      Matrix.one_mulVec]

theorem aeval_gen_charpoly (M : Matrix n n A) : aeval (gen M) M.charpoly = 0 :=
  Subtype.ext (by rw [coe_aeval_gen, Matrix.aeval_self_charpoly]; rfl)

def toGen (M : Matrix n n A) : AdjoinRoot M.charpoly →ₐ[A] genAlg M :=
  AdjoinRoot.liftAlgHom M.charpoly (Algebra.ofId A _) (gen M) (aeval_gen_charpoly M)

theorem toGen_mk (M : Matrix n n A) (p : A[X]) :
    toGen M (AdjoinRoot.mk _ p) = aeval (gen M) p :=
  AdjoinRoot.liftAlgHom_mk _ _ _ _ p

theorem toGen_bijective {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) :
    Function.Bijective (toGen M) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun l => ?_⟩
  · obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [toGen_mk] at hx
    rw [AdjoinRoot.mk_eq_zero]
    refine charpoly_dvd h ?_
    rw [← coe_aeval_gen, hx]
    exact Matrix.zero_mulVec v
  · obtain ⟨p, hp⟩ := exists_aeval l
    exact ⟨AdjoinRoot.mk _ p, Subtype.ext (by rw [toGen_mk, coe_aeval_gen, hp])⟩

theorem cyclicAlgebra : GlobalTheory.RegSS.CyclicAlgebra := by
  intro A _ n _ _ M v h
  refine ⟨⟨AlgEquiv.ofBijective (toGen M) (toGen_bijective h), ?_⟩,
    ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective (actOn M v) (actOn_bijective h))⟩,
    actOn_bijective h⟩
  change toGen M (AdjoinRoot.mk _ X) = _
  rw [toGen_mk, aeval_X]

end GlobalTheory.RegSS.CycAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructureStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicVector_generatedAlgebra_structure : GlobalTheory.RegSS.CyclicAlgebra := by
  first | exact @GlobalTheory.RegSS.CycAlg.cyclicAlgebra | exact GlobalTheory.RegSS.CycAlg.cyclicAlgebra | (intros; apply GlobalTheory.RegSS.CycAlg.cyclicAlgebra <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfect
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfect
open GlobalTheory.RegSS

namespace GlobalTheory.RegSS

theorem eq_zero_of_trace_mul_eq_zero {F L : Type} [Field F] [CharZero F] [CommRing L]
    [Algebra F L] [Module.Finite F L] [IsReduced L] (x : L)
    (hx : ∀ y : L, Algebra.trace F L (x * y) = 0) : x = 0 := by
  have : IsArtinianRing L := IsArtinianRing.of_finite F L
  have : IsSemisimpleRing L := IsArtinianRing.isSemisimpleRing_of_isReduced L

  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})
  have hem : e ∈ Ideal.span {x} := hI ▸ Ideal.mem_span_singleton_self e
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hem

  have htr : LinearMap.trace F L (Algebra.lmul F L e) = 0 := by
    rw [← Algebra.trace_apply, ← ha, mul_comm]
    exact hx a
  have hidem : IsIdempotentElem (Algebra.lmul F L e) := he.map (Algebra.lmul F L)
  have h0 : Algebra.lmul F L e = 0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem htr
  have he0 : e = 0 := by
    have := congrArg (fun f => f 1) h0
    simpa using this
  rw [he0] at hI
  exact Ideal.span_singleton_eq_bot.1 (hI.trans (Ideal.span_singleton_eq_bot.2 rfl))

end GlobalTheory.RegSS

namespace GlobalTheory.RegSS

theorem tracePerfect : TracePerfect := by
  unfold TracePerfect
  intro F E L _ _ _ _ _ _ _ _ _ _ _ _
  have : Module.Finite F L := Module.Finite.trans E L
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have inj : Function.Injective (Algebra.traceForm E L) := by
    intro x y hxy

    have h : ∀ z : L, Algebra.trace F L ((x - y) * z) = 0 := by
      intro z
      have hz := LinearMap.congr_fun hxy z
      rw [Algebra.traceForm_apply, Algebra.traceForm_apply] at hz
      rw [← Algebra.trace_trace (S := E), sub_mul, map_sub, hz, sub_self, map_zero]
    exact sub_eq_zero.1 (eq_zero_of_trace_mul_eq_zero (F := F) _ h)
  let b := Module.Free.chooseBasis E L
  let g : L →ₗ[E] L := b.toDualEquiv.symm.toLinearMap ∘ₗ Algebra.traceForm E L
  have ginj : Function.Injective g := b.toDualEquiv.symm.injective.comp inj
  refine ⟨inj, fun f => ?_⟩
  obtain ⟨x, hx⟩ := (IsArtinian.bijective_of_injective_endomorphism g ginj).2
    (b.toDualEquiv.symm f)
  exact ⟨x, b.toDualEquiv.symm.injective hx⟩

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReducedFreeAlgebraTraceFormPerfectStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_free_algebra_traceForm_perfect : GlobalTheory.RegSS.TracePerfect := by
  first | exact @GlobalTheory.RegSS.tracePerfect | exact GlobalTheory.RegSS.tracePerfect | (intros; apply GlobalTheory.RegSS.tracePerfect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiples
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiples
open Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem fieldUnitBounded_of_packing (hP : NormOnePacking) (hT : TensorLattice) :
    FieldUnitBounded := by
  unfold FieldUnitBounded
  intro F B _ _ _ _ _ τ hB hτ

  obtain ⟨hTop, hLC, hT2, hSC, _hinj, hdisc, C, hC, hcov⟩ := hT F B
  let : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  have := hTop
  have := hLC
  have := hT2
  have := hSC

  have : Nontrivial B := ⟨hB.exists_pair_ne⟩
  have : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have : Infinite B := Infinite.of_injective (algebraMap F B) (algebraMap F B).injective
  have : NoncompactSpace (B ⊗[F] AdeleRing (𝓞 F) F) := by
    refine ⟨fun hU => ?_⟩
    have hfin := hdisc Set.univ hU
    simp only [Set.mem_univ, Set.ofPred_true] at hfin
    exact Set.infinite_univ hfin

  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable B := (Module.finBasis F B).equivFun.injective.countable

  let ι := inclE (F := F) (E := B) (AdeleRing (𝓞 F) F)
  let Λ : AddSubgroup (B ⊗[F] AdeleRing (𝓞 F) F) := ι.toAddMonoidHom.range
  have hΛ : Countable Λ := by
    refine Function.Surjective.countable (f := fun b : B => (⟨ι b, b, rfl⟩ : Λ)) ?_
    rintro ⟨y, b, rfl⟩
    exact ⟨b, rfl⟩
  have hcoc : ∃ C' : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact C' ∧
      ∀ x, ∃ l ∈ Λ, x - l ∈ C' := by
    refine ⟨C, hC, fun x => ?_⟩
    obtain ⟨β, hβ⟩ := hcov x
    exact ⟨ι β, ⟨β, rfl⟩, hβ⟩

  obtain ⟨D, hD, hDu⟩ := hP (B ⊗[F] AdeleRing (𝓞 F) F) (sigR τ (AdeleRing (𝓞 F) F))
    (continuous_sigR τ (AdeleRing (𝓞 F) F)) (sigR_sigR hτ (AdeleRing (𝓞 F) F)) Λ hΛ hcoc
  refine ⟨D, hD, fun u hu => ?_⟩
  obtain ⟨β, ⟨b, rfl⟩, hβ0, huβ⟩ := hDu u hu

  have hb : b ≠ 0 := by
    rintro rfl
    exact hβ0 (map_zero ι)
  obtain ⟨c, hc⟩ := hB.mul_inv_cancel hb
  exact ⟨b, ⟨⟨b, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩, huβ⟩

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FieldAdelicUnitTranslateBoundedOfSmallMultiplesStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldAdelicUnitTranslateBounded_of_smallMultiples : GlobalTheory.RegSS.NormOnePacking → GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.FieldUnitBounded := by
  first | exact @GlobalTheory.RegSS.fieldUnitBounded_of_packing | exact GlobalTheory.RegSS.fieldUnitBounded_of_packing | (intros; apply GlobalTheory.RegSS.fieldUnitBounded_of_packing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLattice
open GlobalTheory.RegSS Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem normOne_bounded_of_unit_bounded {B X : Type} [CommRing B] [CommRing X]
    [TopologicalSpace X] [IsTopologicalRing X] (i : B →+* X) (τ : B →+* B) (s : X →+* X)
    (hs : Continuous s) (hi : ∀ b, i (τ b) = s (i b))
    (hfin : ∀ D : Set X, IsCompact D → {β : B | i β ∈ D}.Finite)
    (D : Set X) (hD : IsCompact D)
    (h : ∀ u : X, u * s u = 1 → ∃ β : B, IsUnit β ∧ u * i β ∈ D) :
    ∃ D' : Set X, IsCompact D' ∧
      ∀ u : X, u * s u = 1 → ∃ β : B, β * τ β = 1 ∧ u * i β ∈ D' := by
  classical

  set K : Set X := (fun x => x * s x) '' D with hK
  have hKc : IsCompact K := hD.image (continuous_id.mul hs : Continuous fun x : X => x * s x)

  set T : Set B := {γ : B | i γ ∈ K} with hT
  have hTf : T.Finite := hfin K hKc

  let c : B → B := fun γ =>
    if h : ∃ p : B × B, p.1 * p.2 = 1 ∧ p.1 * τ p.1 = γ then (Classical.choose h).2 else 0
  refine ⟨⋃ γ ∈ T, (fun x => x * i (c γ)) '' D,
    hTf.isCompact_biUnion fun γ _ => hD.image (continuous_mul_const _), ?_⟩
  intro u hu
  obtain ⟨β, hβ, hβD⟩ := h u hu
  obtain ⟨β', hβ'⟩ := hβ.exists_right_inv
  have hex : ∃ p : B × B, p.1 * p.2 = 1 ∧ p.1 * τ p.1 = β * τ β := ⟨(β, β'), hβ', rfl⟩
  set p := Classical.choose hex with hpdef
  have hp : p.1 * p.2 = 1 ∧ p.1 * τ p.1 = β * τ β := Classical.choose_spec hex
  have hc : c (β * τ β) = p.2 := by
    show (if h : ∃ q : B × B, q.1 * q.2 = 1 ∧ q.1 * τ q.1 = β * τ β
      then (Classical.choose h).2 else 0) = p.2
    rw [dite_eq_left hex]

  refine ⟨β * p.2, ?_, ?_⟩
  · calc β * p.2 * τ (β * p.2) = (β * τ β) * (p.2 * τ p.2) := by rw [map_mul]; ring
      _ = (p.1 * τ p.1) * (p.2 * τ p.2) := by rw [hp.2]
      _ = (p.1 * p.2) * τ (p.1 * p.2) := by rw [map_mul τ p.1 p.2]; ring
      _ = 1 := by rw [hp.1, map_one, one_mul]
  · have hmem : β * τ β ∈ T := by
      show i (β * τ β) ∈ K
      refine ⟨u * i β, hβD, ?_⟩
      show u * i β * s (u * i β) = i (β * τ β)
      rw [map_mul s, map_mul i, hi]
      calc u * i β * (s u * s (i β)) = (u * s u) * (i β * s (i β)) := by ring
        _ = i β * s (i β) := by rw [hu, one_mul]
    refine Set.mem_biUnion hmem ⟨u * i β, hβD, ?_⟩
    show u * i β * i (c (β * τ β)) = u * i (β * p.2)
    rw [hc, map_mul i, mul_assoc]

theorem normOfUnitBounded_of_tensorLattice :
    GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.NormOfUnitBounded := by
  intro hL F B _ _ _ _ _ τ hU
  let _ : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  obtain ⟨hTR, -, -, -, -, hfin, -⟩ := hL F B
  have := hTR
  obtain ⟨D, hD, hDu⟩ := hU
  exact normOne_bounded_of_unit_bounded (inclE (F := F) (AdeleRing (𝓞 F) F)) (τ : B →+* B)
    (sigR τ (AdeleRing (𝓞 F) F)) (continuous_sigR τ _) (fun b => inclE_conj τ _ b) hfin D hD hDu

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroup
open MeasureTheory MeasureTheory.Measure GlobalTheory.RegSS
open scoped NNReal ENNReal

namespace GlobalTheory.RegSS

theorem measure_le_of_sub_mem_imp_eq {X : Type} [AddCommGroup X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (Λ : AddSubgroup X) [Countable Λ]
    (C S : Set X) (hCm : MeasurableSet C) (hC : ∀ x, ∃ l ∈ Λ, x - l ∈ C) (hS : MeasurableSet S)
    (h : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ → x = y) : μ S ≤ μ C := by
  let A : Λ → Set X := fun l => (fun x => (l : X) + x) ⁻¹' S ∩ C
  have hAm : ∀ l, MeasurableSet (A l) := fun l =>
    ((measurable_const_add (l : X)) hS).inter hCm
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro l m hlm
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hx, -⟩ ⟨hx', -⟩
    apply hlm
    have := h _ hx _ hx' (by simpa using Λ.sub_mem l.2 m.2)
    exact Subtype.ext (add_right_cancel this)
  have hcov : S ⊆ ⋃ l : Λ, (fun x => -(l : X) + x) ⁻¹' A l := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := hC x
    refine Set.mem_iUnion.2 ⟨⟨l, hl⟩, ?_, ?_⟩
    · simpa using hx
    · simpa [neg_add_eq_sub] using hxl
  calc μ S ≤ μ (⋃ l : Λ, (fun x => -(l : X) + x) ⁻¹' A l) := measure_mono hcov
    _ ≤ ∑' l : Λ, μ ((fun x => -(l : X) + x) ⁻¹' A l) := measure_iUnion_le _
    _ = ∑' l : Λ, μ (A l) := by simp_rw [measure_preimage_add]
    _ = μ (⋃ l, A l) := (measure_iUnion hdisj hAm).symm
    _ ≤ μ C := measure_mono (Set.iUnion_subset fun l => Set.inter_subset_right)

theorem measure_preimage_mul_of_norm_one {X : Type} [CommRing X] [TopologicalSpace X]
    [IsTopologicalRing X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsAddHaarMeasure] [μ.Regular] (τ : X →+* X) (hτ : Continuous τ)
    (hττ : ∀ x, τ (τ x) = x) (u : X) (hu : u * τ u = 1) (S : Set X) :
    μ ((fun x => u * x) ⁻¹' S) = μ S := by
  let T : X ≃ₜ+ X :=
    { toFun := τ, invFun := τ, left_inv := hττ, right_inv := hττ, map_add' := map_add τ,
      continuous_toFun := hτ, continuous_invFun := hτ }
  let M : X ≃ₜ+ X :=
    { toFun := fun x => u * x, invFun := fun x => τ u * x,
      left_inv := fun x => by simp only [← mul_assoc, mul_comm (τ u) u, hu, one_mul],
      right_inv := fun x => by simp only [← mul_assoc, hu, one_mul],
      map_add' := mul_add u,
      continuous_toFun := continuous_const_mul u, continuous_invFun := continuous_const_mul _ }
  have h1 : T.trans T = ContinuousAddEquiv.refl X := by
    ext x; exact hττ x
  have h2 : (T.trans M).trans (T.trans M) = ContinuousAddEquiv.refl X := by
    ext x
    change u * τ (u * τ x) = x
    rw [map_mul, hττ, ← mul_assoc, hu, one_mul]
  have e1 := congrArg addEquivAddHaarChar h1
  have e2 := congrArg addEquivAddHaarChar h2
  simp only [addEquivAddHaarChar_trans, addEquivAddHaarChar_refl] at e1 e2
  have e3 : addEquivAddHaarChar M * addEquivAddHaarChar M = 1 := by
    rw [← e2, mul_mul_mul_comm, e1, one_mul]
  have e4 : addEquivAddHaarChar M = 1 := by
    have := (pow_eq_one_iff_of_nonneg (a := addEquivAddHaarChar M) zero_le two_ne_zero).1
      (by rw [sq, e3])
    exact this
  have := addEquivAddHaarChar_smul_preimage μ (X := S) M
  rw [e4, one_smul] at this
  exact this

theorem normOnePacking : NormOnePacking := by
  intro X _ _ _ _ _ _ _ τ hτ hττ Λ hΛ ⟨C, hCc, hC⟩
  borelize X
  let μ : Measure X := addHaar
  have huniv : μ Set.univ = ∞ := measure_univ_of_isAddLeftInvariant μ
  obtain ⟨K, -, hKc, hK⟩ := isOpen_univ.exists_lt_isCompact (μ := μ) (r := μ C)
    (by rw [huniv]; exact hCc.measure_lt_top)
  refine ⟨(fun p : X × X => p.1 - p.2) '' (K ×ˢ K), (hKc.prod hKc).image (by fun_prop), ?_⟩
  intro u hu
  by_contra hcon
  have hle := measure_le_of_sub_mem_imp_eq μ Λ C ((fun x => u * x) ⁻¹' K) hCc.measurableSet hC
    ((continuous_const_mul u).measurable hKc.measurableSet) (by
      intro x hx y hy hxy
      by_contra hne
      exact hcon ⟨x - y, hxy, sub_ne_zero.2 hne, (u * x, u * y), ⟨hx, hy⟩, (mul_sub u x y).symm⟩)
  rw [measure_preimage_mul_of_norm_one μ τ hτ hττ u hu] at hle
  exact absurd hK (not_lt.2 hle)

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroupStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOne_small_multiples_by_cocompact_subgroup : GlobalTheory.RegSS.NormOnePacking := by
  first | exact @GlobalTheory.RegSS.normOnePacking | exact GlobalTheory.RegSS.normOnePacking | (intros; apply GlobalTheory.RegSS.normOnePacking <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorInvolutionAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorInvolutionAdjoint
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem pointsAdjoint_toMat_tmul {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type}
    [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (l : plusAlg σ J γ) (c : E ⊗[F] R) :
    toMat σ J γ R (l ⊗ₜ c) = c • ((l : genAlg γ) : Matrix n n E).map (inclE (F := F) R) := by
  rw [Algebra.smul_def, Algebra.commutes]
  exact Algebra.TensorProduct.lift_tmul _ _ _ l c

theorem pointsAdjoint : PointsAdjoint := by
  intro F E _ _ _ _ n _ _ σ J γ h R _ _ u
  induction u using TensorProduct.induction_on with
  | zero => simp [adj_zero]
  | tmul a b =>
    have ha := (adj_eq_iff _ h.nondeg _ _).2 a.2
    have hc : lConj σ J (γ : Matrix n n E) R (a ⊗ₜ b) = a ⊗ₜ sigR σ R b := rfl
    rw [hc, pointsAdjoint_toMat_tmul,
      pointsAdjoint_toMat_tmul, adj_smul,
      adj_map (σ : E →+* E) (sigR σ R) (inclE (F := F) R) (inclE_conj σ R) h.nondeg, ha]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), adj_add, ha, hb]

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTensorInvolutionAdjointStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_tensor_involution_adjoint : GlobalTheory.RegSS.PointsAdjoint := by
  first | exact @GlobalTheory.RegSS.pointsAdjoint | exact GlobalTheory.RegSS.pointsAdjoint | (intros; apply GlobalTheory.RegSS.pointsAdjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartEtale
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem plusEtale : PlusEtale := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hA hbij
  have : Nontrivial E := quad_nontrivial hreg.quad
  have : Module.Finite F E := quad_finite hreg.quad
  obtain ⟨b⟩ := hA.2.2.1
  have : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b
  have : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b
  have : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _
  have : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) :=
    Module.Finite.of_injective (plusAlg σ J (γ : Matrix n n E)).val.toLinearMap
      Subtype.val_injective
  have : IsReduced (genAlg (γ : Matrix n n E)) := genAlg_isReduced hreg hA
  have : IsReduced (plusAlg σ J (γ : Matrix n n E)) :=
    isReduced_of_injective (plusAlg σ J (γ : Matrix n n E)).val Subtype.val_injective
  refine ⟨etale_of_isReduced _, ?_, hbij⟩
  have hdim := (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct, hreg.quad.finrank_eq,
    ← Module.finrank_mul_finrank F E (genAlg (γ : Matrix n n E)), hreg.quad.finrank_eq, Module.finrank_eq_card_basis b] at hdim
  have hr : Module.finrank F (plusAlg σ J (γ : Matrix n n E)) = Fintype.card n := by omega
  exact ⟨(Module.finBasisOfFinrankEq F _ hr).reindex (Fintype.equivFin n).symm⟩

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartEtaleStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_selfAdjointPart_etale : GlobalTheory.RegSS.PlusEtale := by
  first | exact @GlobalTheory.RegSS.plusEtale | exact GlobalTheory.RegSS.plusEtale | (intros; apply GlobalTheory.RegSS.plusEtale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NontrivialSplitSubtorusNotCentral
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NontrivialSplitSubtorusNotCentral
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem subtorusNotCentral_of (hU : UnitaryCommutant) (hL : SubtorusLaurent)
    (hC : CharacterMonomial) : SubtorusNotCentral := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hE s hs A
  by_contra hcon
  push Not at hcon
  have hfield : IsField (E ⊗[F] F) :=
    MulEquiv.isField hE (Algebra.TensorProduct.rid F F E).toMulEquiv
  haveI : Nontrivial (E ⊗[F] F) := hfield.nontrivial
  haveI : CharZero (E ⊗[F] F) := charZero_of_injective_algebraMap (algebraMap F (E ⊗[F] F)).injective
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let t₀ : Fin s → Fˣ := fun _ => Units.mk0 2 h2
  have hsq : A.hom F (t₀ * t₀) = 1 := by
    refine Units.ext ?_
    ext i j
    have hH : IsHerm (sigR σ F) (J.map (inclE (F := F) F)) := by
      have h : cT (σ : E →+* E) J = J := hreg.herm
      change cT _ _ = _
      conv_rhs => rw [← h]
      ext a b
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      exact (inclE_conj σ F _).symm
    have hdet : IsUnit (J.map (inclE (F := F) F)).det := isUnit_det_map _ hreg.nondeg
    have hsc : ∀ t, (A.hom F t : Matrix n n (E ⊗[F] F)) =
        ((A.hom F t : Matrix n n (E ⊗[F] F)) i i) • (1 : Matrix n n (E ⊗[F] F)) := by
      intro t
      obtain ⟨c, hc⟩ := hU (E ⊗[F] F) hfield (sigR σ F) (sigR_sigR hreg.quad.invol F) n _ hH hdet
        (A.hom F t : Matrix n n (E ⊗[F] F)) (fun g hg => congrArg Units.val (hcon g hg t))
      rw [hc]; simp
    letI := hfield.toField
    let f : (Fin s → Fˣ) →* E ⊗[F] F :=
      { toFun := fun t => (A.hom F t : Matrix n n (E ⊗[F] F)) i i
        map_one' := by simp
        map_mul' := fun a b => by
          rw [map_mul, Units.val_mul, hsc a, smul_mul_assoc, one_mul]
          simp }
    obtain ⟨S, C, hSC⟩ := hL F E n σ J γ s A
    obtain ⟨a, ha⟩ := hC F (E ⊗[F] F) s f S (fun a => C a i i) (fun t => by
      change (A.hom F t : Matrix n n (E ⊗[F] F)) i i = _
      rw [hSC t, Matrix.sum_apply]
      rfl)
    have hfix : sigR σ F (f t₀) = f t₀ := by
      rw [ha]; simp [sigR]
    have hmem := (mem_UJ_iff_mul_adj (sigR σ F) hdet (A.hom F t₀)).1 (A.mem F t₀).1
    have hadj : adj (sigR σ F) (J.map (inclE (F := F) F)) (A.hom F t₀ : Matrix n n (E ⊗[F] F)) =
        (A.hom F t₀ : Matrix n n (E ⊗[F] F)) := by
      rw [hsc t₀, adj_smul, adj_one _ hdet]
      exact congrArg (· • (1 : Matrix n n (E ⊗[F] F))) hfix
    rw [hadj] at hmem
    rw [map_mul, Units.val_mul, hmem, Units.val_one]
  have h1 : t₀ * t₀ = 1 := A.inj F (by rw [hsq, map_one])
  have h4 := congrArg Units.val (congrFun h1 ⟨0, hs⟩)
  simp only [t₀, Pi.mul_apply, Units.val_mul, Units.val_mk0, Pi.one_apply, Units.val_one] at h4
  norm_num at h4

end GlobalTheory.RegSS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NontrivialSplitSubtorusNotCentralStatement
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_split_subtorus_not_central : GlobalTheory.RegSS.UnitaryCommutant → GlobalTheory.RegSS.SubtorusLaurent → GlobalTheory.RegSS.CharacterMonomial → GlobalTheory.RegSS.SubtorusNotCentral := by
  first | exact @GlobalTheory.RegSS.subtorusNotCentral_of | exact GlobalTheory.RegSS.subtorusNotCentral_of | (intros; apply GlobalTheory.RegSS.subtorusNotCentral_of <;> assumption)
end
end
