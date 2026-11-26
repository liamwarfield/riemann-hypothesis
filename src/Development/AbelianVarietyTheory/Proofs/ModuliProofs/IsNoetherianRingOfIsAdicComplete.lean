module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DvdTraceOfBalancedTensor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete
open Polynomial

namespace GlobalTheory.AdicNoeth

theorem isNoetherianRing_graded {R : Type} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing (reesAlgebra I ⧸ reesShiftIdeal I) := by
  have hker : ∀ a ∈ I, algebraMap R (reesAlgebra I ⧸ reesShiftIdeal I) a = 0 := by
    intro a ha
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem, mem_reesShiftIdeal]
    intro n
    rw [Subalgebra.coe_algebraMap, Polynomial.algebraMap_eq, Polynomial.coeff_C]
    rcases n with _ | n
    · simpa using ha
    · simp
  letI : Algebra (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) :=
    (Ideal.Quotient.lift I (algebraMap R _) hker).toAlgebra
  have : IsScalarTower R (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R (reesAlgebra I) := ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  have : Algebra.FiniteType R (reesAlgebra I ⧸ reesShiftIdeal I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R (reesShiftIdeal I))
      (Ideal.Quotient.mkₐ_surjective R _)
  have : Algebra.FiniteType (R ⧸ I) (reesAlgebra I ⧸ reesShiftIdeal I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ I) _
  exact Algebra.FiniteType.isNoetherianRing (R ⧸ I) _

private lemma coeff_mul_monomial_eq_ite {R : Type} [CommRing R] (p : R[X]) (d n : ℕ) (r : R) :
    (p * monomial d r).coeff n = if d ≤ n then p.coeff (n - d) * r else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

theorem exists_leading_generators {R : Type} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] (J : Ideal R) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → R) (d : ι → ℕ), (∀ i, f i ∈ J) ∧
      ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1) := by
  classical
  have := isNoetherianRing_graded I hI
  let lf : {p : ℕ × R // p.2 ∈ J ∧ p.2 ∈ I ^ p.1} → reesAlgebra I ⧸ reesShiftIdeal I := fun x =>
    Ideal.Quotient.mk (reesShiftIdeal I) ⟨monomial x.1.1 x.1.2, reesAlgebra.monomial_mem.mpr x.2.2⟩
  obtain ⟨s, hsS, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Set.range lf)).mp
    (IsNoetherian.noetherian (Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I) (Set.range lf)))
  have hpre : ∀ q : s, ∃ x, lf x = q := fun q => hsS q.2
  choose pre hpre using hpre
  refine ⟨s, inferInstance, fun q => (pre q).1.2, fun q => (pre q).1.1, fun q => (pre q).2.1, ?_⟩
  intro n g hgJ hgn
  have hs : (↑s : Set (reesAlgebra I ⧸ reesShiftIdeal I)) = Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I) := by
    ext x; simp
  have hmem : lf ⟨(n, g), hgJ, hgn⟩ ∈ Submodule.span (reesAlgebra I ⧸ reesShiftIdeal I)
      (Set.range fun q : s => (q : reesAlgebra I ⧸ reesShiftIdeal I)) := by
    rw [← hs, ← hspan]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
  choose p hp using fun q => Ideal.Quotient.mk_surjective (I := reesShiftIdeal I) (c q)
  have hz : (⟨monomial n g, reesAlgebra.monomial_mem.mpr hgn⟩ : reesAlgebra I) -
      ∑ q : s, p q * ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩
      ∈ reesShiftIdeal I := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
    have hq : ∀ q : s, Ideal.Quotient.mk (reesShiftIdeal I) (p q *
        ⟨monomial (pre q).1.1 (pre q).1.2, reesAlgebra.monomial_mem.mpr (pre q).2.2⟩) =
        c q • (q : reesAlgebra I ⧸ reesShiftIdeal I) := by
      intro q
      rw [map_mul, hp q, smul_eq_mul]
      exact congrArg _ (hpre q)
    simp only [hq, hc]
    exact sub_self _
  rw [mem_reesShiftIdeal] at hz
  refine ⟨fun q => if (pre q).1.1 ≤ n then ((p q : reesAlgebra I) : R[X]).coeff (n - (pre q).1.1)
    else 0, ?_, ?_⟩
  · intro q
    dsimp only
    split_ifs
    · exact (mem_reesAlgebra_iff I _).mp (p q).2 _
    · exact zero_mem _
  · convert hz n using 1
    simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      coeff_sub, finsetSum_coeff, coeff_mul_monomial_eq_ite, ite_mul, zero_mul]
    rw [coeff_monomial_same]

theorem mem_span_of_leading {R : Type} [CommRing R] (I : Ideal R) [hc : IsAdicComplete I R]
    (J : Ideal R) {ι : Type} [Fintype ι] (f : ι → R) (d : ι → ℕ) (hf : ∀ i, f i ∈ J)
    (h : ∀ (n : ℕ) (g : R), g ∈ J → g ∈ I ^ n →
        ∃ c : ι → R, (∀ i, c i ∈ I ^ (n - d i)) ∧ g - ∑ i, c i * f i ∈ I ^ (n + 1))
    (g : R) (hg : g ∈ J) : g ∈ Ideal.span (Set.range f) := by
  classical
  have step : ∀ (n : ℕ) (r : {r : R // r ∈ J ∧ r ∈ I ^ n}), ∃ c : ι → R,
      (∀ i, c i ∈ I ^ (n - d i)) ∧ r.1 - ∑ i, c i * f i ∈ I ^ (n + 1) :=
    fun n r => h n r.1 r.2.1 r.2.2
  choose c hc1 hc2 using step
  let res : (n : ℕ) → {r : R // r ∈ J ∧ r ∈ I ^ n} := fun n =>
    Nat.rec (motive := fun n => {r : R // r ∈ J ∧ r ∈ I ^ n})
      ⟨g, hg, by simp⟩
      (fun n r => ⟨r.1 - ∑ i, c n r i * f i,
        J.sub_mem r.2.1 (J.sum_mem fun i _ => J.mul_mem_left _ (hf i)), hc2 n r⟩) n
  let a : ℕ → ι → R := fun n i => c n (res n) i
  have ha : ∀ n i, a n i ∈ I ^ (n - d i) := fun n i => hc1 n (res n) i
  have hres_succ : ∀ n, (res (n + 1)).1 = (res n).1 - ∑ i, a n i * f i := fun n => rfl
  have hdecomp : ∀ N, g = ∑ i, (∑ m ∈ Finset.range N, a m i) * f i + (res N).1 := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_mul, Finset.sum_const_zero, zero_add]
      rfl
    | succ N ih =>
      rw [hres_succ]
      simp only [Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
      conv_lhs => rw [ih]
      ring
  have hpow : ∀ {m n : ℕ} {x : R}, m ≤ n → x ∈ I ^ n → x ∈ I ^ m :=
    fun hmn hx => Ideal.pow_le_pow_right hmn hx
  have htop : ∀ m : ℕ, (I ^ m • ⊤ : Submodule R R) = I ^ m := fun m => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let T : ι → ℕ → R := fun i k => ∑ m ∈ Finset.range (k + d i), a m i
  have hT : ∀ i {m n : ℕ}, m ≤ n → T i m ≡ T i n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro i m n hmn
    rw [SModEq.sub_mem, htop]
    have hd : T i n - T i m = ∑ k ∈ Finset.Ico (m + d i) (n + d i), a k i := by
      simp only [T]
      rw [Finset.sum_Ico_eq_sub _ (by omega)]
    rw [← neg_sub, hd]
    refine neg_mem (Ideal.sum_mem _ fun k hk => hpow ?_ (ha k i))
    rw [Finset.mem_Ico] at hk
    omega
  choose L hL using fun i => IsPrecomplete.prec' (I := I) (T i) (hT i)
  have hzero : g - ∑ i, L i * f i = 0 := by
    refine IsHausdorff.haus' (I := I) _ fun N => ?_
    rw [SModEq.sub_mem, sub_zero, htop]
    have hdD : ∀ i, d i ≤ ∑ j, d j := fun i =>
      Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    rw [hdecomp (N + ∑ j, d j)]
    have hS : ∀ i, ∑ m ∈ Finset.range (N + ∑ j, d j), a m i = T i (N + ∑ j, d j - d i) := by
      intro i
      simp only [T]
      rw [Nat.sub_add_cancel (by have := hdD i; omega)]
    have hrw : ∑ i, (∑ m ∈ Finset.range (N + ∑ j, d j), a m i) * f i + (res (N + ∑ j, d j)).1 -
        ∑ i, L i * f i =
        ∑ i, (T i (N + ∑ j, d j - d i) - L i) * f i + (res (N + ∑ j, d j)).1 := by
      simp only [hS, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hrw]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_)
      (hpow (by omega) (res (N + ∑ j, d j)).2.2)
    have hLi := hL i (N + ∑ j, d j - d i)
    rw [SModEq.sub_mem, htop] at hLi
    exact hpow (by have := hdD i; omega) hLi
  rw [sub_eq_zero] at hzero
  rw [hzero]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem isNoetherianRing_of_isAdicComplete : ∀ (R : Type) [CommRing R] (I : Ideal R), I.FG →
    IsAdicComplete I R → IsNoetherianRing (R ⧸ I) → IsNoetherianRing R := by
  intro R _ I hI hc hq
  refine isNoetherianRing_iff.mpr ⟨fun J => ?_⟩
  obtain ⟨ι, _, f, d, hf, hlead⟩ := exists_leading_generators I hI J
  have hJ : J = Ideal.span (Set.range f) := le_antisymm
    (fun g hg => mem_span_of_leading I J f d hf hlead g hg)
    (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hf i))
  rw [hJ]
  exact Submodule.fg_span (Set.finite_range f)

end GlobalTheory.AdicNoeth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplex
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

private lemma pi_single_eq_re_smul_add_im_smul {g : ℕ} (a : Fin g) (w : ℂ) :
    (Pi.single a w : Fin g → ℂ) =
      (w.re : ℝ) • (Pi.single a 1 : Fin g → ℂ) + (w.im : ℝ) • (I • (Pi.single a 1 : Fin g → ℂ)) := by
  ext j
  by_cases hj : j = a
  · subst hj
    apply Complex.ext <;> simp
  · simp [hj]

theorem map_I_smul_of_cauchyRiemann {g : ℕ} (L : (Fin g → ℂ) →L[ℝ] ℂ)
    (h : ∀ a, L (Pi.single a 1 : Fin g → ℂ) + I * L (I • (Pi.single a 1 : Fin g → ℂ)) = 0)
    (c : ℂ) (v : Fin g → ℂ) : L (c • v) = c • L v := by

  have hI : ∀ a, L (I • (Pi.single a 1 : Fin g → ℂ)) = I * L (Pi.single a 1) := by
    intro a
    linear_combination (-I) * h a + L (I • (Pi.single a 1 : Fin g → ℂ)) * I_sq
  have hline : ∀ a (w : ℂ), L (Pi.single a w : Fin g → ℂ) = w * L (Pi.single a 1) := by
    intro a w
    rw [pi_single_eq_re_smul_add_im_smul a w, map_add (f := _), map_smul, map_smul, hI a]
    conv_rhs => rw [← Complex.re_add_im w]
    simp only [Complex.real_smul]
    ring
  have hsum : ∀ u : Fin g → ℂ, L u = ∑ a, u a * L (Pi.single a 1) := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl (fun a _ => hline a (u a))
  rw [hsum, hsum v, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem cauchyRiemann_iff_differentiableOn_complex :
    ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by
  intro g U f hU
  refine ⟨fun hR => ⟨fun hCR => ?_, fun hC => ?_⟩, fun hC => ?_⟩
  ·
    intro z hz
    have hzR : DifferentiableAt ℝ f z := hR.differentiableAt (hU.mem_nhds hz)
    set L := fderiv ℝ f z with hL
    have hlin : ∀ (c : ℂ) (v : Fin g → ℂ), L (c • v) = c • L v :=
      map_I_smul_of_cauchyRiemann L (fun a => hCR a z hz)
    let L' : (Fin g → ℂ) →L[ℂ] ℂ :=
      { toFun := L
        map_add' := L.map_add
        map_smul' := hlin
        cont := L.continuous }
    have hres : L'.restrictScalars ℝ = L := by
      ext v; rfl
    exact (hasFDerivAt_of_restrictScalars ℝ hzR.hasFDerivAt hres).differentiableAt.differentiableWithinAt
  · intro a z hz
    have hzC : DifferentiableAt ℂ f z := hC.differentiableAt (hU.mem_nhds hz)
    rw [hzC.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
    rw [← mul_assoc, I_mul_I]
    ring
  · refine ⟨?_, fun v => SCV.differentiableOn_fderiv_apply hU hC v⟩
    exact (SCV.contDiffOn_of_differentiableOn hU hC ∞).restrict_scalars ℝ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CauchyRiemannIffDifferentiableOnComplexStatement
open Complex Matrix
open scoped ContDiff BigOperators Real
theorem _root_.GlobalTheory.T.cauchyRiemann_iff_differentiableOn : ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by
  first | exact @GlobalTheory.cauchyRiemann_iff_differentiableOn_complex | exact GlobalTheory.cauchyRiemann_iff_differentiableOn_complex | (intros; apply GlobalTheory.cauchyRiemann_iff_differentiableOn_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatMapMaximalIdealIsSeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalUnramifiedOfIsIndEtale
open CategoryTheory IsLocalRing

namespace GlobalTheory.LocalIndEtaleUnramified

theorem exists_local_of_algHom {A S B : Type} [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)] [CommRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] (g : B →ₐ[A] S) (b : B) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = g b := by
  let P : Ideal B := (maximalIdeal S).comap (g : B →+* S)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hu : ∀ y : P.primeCompl, IsUnit (g y) := by
    intro y
    by_contra h
    exact y.2 (show (g : B →+* S) y ∈ maximalIdeal S from h)
  let φ : Localization.AtPrime P →ₐ[A] S := IsLocalization.liftAlgHom (M := P.primeCompl) hu
  have hφ : ∀ y : B, φ (algebraMap B (Localization.AtPrime P) y) = g y := fun y =>
    IsLocalization.lift_eq (M := P.primeCompl) (g := (g : B →+* S)) hu y
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
    refine (IsLocalization.AtPrime.isUnit_mk'_iff _ P y s).2 ?_
    have h1 : φ (IsLocalization.mk' (Localization.AtPrime P) y s) * g s = g y := by
      rw [← hφ, ← map_mul, IsLocalization.mk'_spec, hφ]
    have h2 : IsUnit (g y) := h1 ▸ ha.mul (hu s)
    intro hy
    exact (show (g : B →+* S) y ∈ maximalIdeal S from hy) h2
  have hA : IsLocalHom (algebraMap A (Localization.AtPrime P)) := by
    refine ⟨fun a ha => ?_⟩
    have := ha.map φ
    rw [AlgHom.commutes] at this
    exact IsLocalHom.map_nonunit a this
  haveI : Algebra.FormallyUnramified B (Localization.AtPrime P) :=
    Algebra.FormallyUnramified.of_isLocalization P.primeCompl
  haveI : Algebra.EssFiniteType B (Localization.AtPrime P) :=
    Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
  exact ⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance, hA,
    Algebra.FormallyUnramified.comp A B _, Algebra.EssFiniteType.comp A B _, φ, hloc,
    algebraMap B _ b, hφ b⟩

theorem exists_local_unramified_of_isIndEtale {A S : Type} [CommRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (s : S) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = s := by
  obtain ⟨J, _, _, D, t, c, hc, H⟩ := h
  obtain ⟨j, b, hb⟩ := Limits.Concrete.isColimit_exists_rep D hc s
  obtain ⟨hE, hcomp⟩ := H j
  let f : A →+* D.obj j := (t.app j).hom
  let g₀ : D.obj j →+* S := (c.app j).hom
  letI : Algebra A (D.obj j) := f.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := hE
  have hg : ∀ a : A, g₀ (f a) = algebraMap A S a := fun a =>
    congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of S => k.hom a) hcomp
  let g : D.obj j →ₐ[A] S := { g₀ with commutes' := hg }
  have hb' : g b = s := hb
  rw [← hb']
  exact exists_local_of_algHom g b

end GlobalTheory.LocalIndEtaleUnramified
end

open CategoryTheory Limits IsLocalRing

namespace GlobalTheory.IndEtaleLocal

theorem exists_etale_factor {A S Z : Type} [CommRing A] [CommRing S] [Algebra A S]
    [CommRing Z] [Algebra A Z] [Algebra.FinitePresentation A Z]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (g : Z →ₐ[A] S) :
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W)
      (u : Z →ₐ[A] W) (v : W →ₐ[A] S), v.comp u = g := by
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  obtain ⟨i, g', h1, h2⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of A) D t (S := CommRingCat.of Z) (CommRingCat.ofHom (algebraMap A Z))
    (Cocone.mk _ s) hs
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    (CommRingCat.ofHom g.toRingHom) (fun i => by
      rw [(hst i).2]
      ext a
      simp)
  let : Algebra A (D.obj i) := (t.app i).hom.toAlgebra
  have het : Algebra.Etale A (D.obj i) := (hst i).1
  refine ⟨D.obj i, inferInstance, inferInstance, het,
    { toRingHom := g'.hom, commutes' := fun a => congr($(h1).hom a) },
    { toRingHom := (s.app i).hom, commutes' := fun a => congr($((hst i).2).hom a) }, ?_⟩
  ext z
  exact (congr($(h2).hom z)).symm

theorem flat_of_isIndEtale {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) : Module.Flat A S := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx => ?_
  let p : MvPolynomial (Fin l) A := ∑ i, f i • MvPolynomial.X i
  let I : Ideal (MvPolynomial (Fin l) A) := Ideal.span {p}
  have : Algebra.FinitePresentation A (MvPolynomial (Fin l) A ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton p)
  let g : (MvPolynomial (Fin l) A ⧸ I) →ₐ[A] S :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have : MvPolynomial.aeval x p = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [p, map_sum, map_smul, MvPolynomial.aeval_X, hfx]
      rw [map_mul, this, mul_zero])
  obtain ⟨W, _, _, _, u, v, huv⟩ := exists_etale_factor h g
  let w : Fin l → W := fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
  have hw : ∀ i, v (w i) = x i := fun i => by
    have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
    exact this.trans (MvPolynomial.aeval_X x i)
  have hrel : ∑ i, f i • w i = 0 := by
    have h0 : Ideal.Quotient.mkₐ A I p = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)
    have : u (Ideal.Quotient.mkₐ A I p) = 0 := by rw [h0, map_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [p, map_sum, map_smul] using this
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := W) hrel
  refine ⟨k, a, fun j => v (y j), fun i => ?_, ha⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hw, hy, map_sum]
  simp only [map_smul]

theorem exists_local_unramified {A S : Type} [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (s : S) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L), φ x = s := by
  first
  | exact @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale
  | exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale
  | (apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale ..)

theorem flat_map_maximalIdeal_isSeparable (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) :
    Module.Flat A S ∧ (maximalIdeal A).map (algebraMap A S) = maximalIdeal S ∧
      Algebra.IsSeparable (ResidueField A) (ResidueField S) := by
  refine ⟨flat_of_isIndEtale h, le_antisymm ?_ fun s hs => ?_, ⟨fun r => ?_⟩⟩
  · exact ((local_hom_tfae (algebraMap A S)).out 1 3 rfl rfl).mp inferInstance
  · obtain ⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩ := exists_local_unramified h s
    have hx : x ∈ maximalIdeal L := fun hx => hs (hx.map φ)
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A)] at hx
    have := Ideal.mem_map_of_mem (φ : L →+* S) hx
    rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this
  · obtain ⟨s, rfl⟩ := residue_surjective r
    obtain ⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩ := exists_local_unramified h s
    have : IsLocalHom (φ : L →+* S) := ⟨hφ.1⟩
    let ψ : ResidueField L →ₐ[ResidueField A] ResidueField S :=
      { toRingHom := ResidueField.map (φ : L →+* S)
        commutes' := fun a => by
          obtain ⟨a, rfl⟩ := residue_surjective a
          simp [ResidueField.algebraMap_residue] }
    have := (Algebra.IsSeparable.isSeparable (ResidueField A) (residue L x)).map ψ ψ.injective
    exact this

end GlobalTheory.IndEtaleLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfApplyEqGenericPoint
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenericFlat

theorem _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint {O K : Type} [CommRing O] [IsDomain O] [Field K]
    (δ : O →+* K) (pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)) :
    Function.Injective δ := by
  change (Spec.map (CommRingCat.ofHom δ)) pt = genericPoint (Spec (CommRingCat.of O)) at h
  rw [genericPoint_eq_bot_of_affine] at h
  have hpt : pt.asIdeal = ⊥ := Ideal.eq_bot_of_prime (h := pt.isPrime) _
  have h2 := congrArg PrimeSpectrum.asIdeal h
  change Ideal.comap δ pt.asIdeal = ⊥ at h2
  rw [hpt, ← RingHom.ker_eq_comap_bot] at h2
  exact (RingHom.injective_iff_ker_eq_bot δ).mpr h2

theorem _root_.GlobalTheory.GenericFlat.apply_eq_genericPoint {O : Type} [CommRing O] [IsDomain O]
    {T : Scheme.{0}} (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) [Flat s]
    {t : T} (ht : t ∈ genericPoints T) : s t = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
  obtain ⟨t', hspec, heq⟩ := Flat.generalizingMap s
    ((genericPoint_spec (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O)).specializes (Set.mem_univ (s t)))
  have hsub : closure {t} ⊆ closure {t'} := specializes_iff_closure_subset.mp hspec
  have hcl : closure {t} = closure {t'} :=
    (show closure {t} ∈ irreducibleComponents T from ht).eq_of_le
      isIrreducible_singleton.closure hsub
  have hback : t ⤳ t' := specializes_iff_closure_subset.mpr hcl.ge
  rw [← heq, (hspec.antisymm hback).eq]

theorem _root_.GlobalTheory.GenericFlat.generic_charZero_and_flat : (∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Flat s → ∀ x : T, ∃ ξ : T, ξ ⤳ x ∧ CharZero (T.residueField ξ)) ∧ ∀ (R O : Type) [CommRing R] [IsDedekindDomain R] [CommRing O] [IsDomain O] (b : R →+* O) (T : Scheme.{0}) (s : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ T) (v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O), Function.Injective b → Flat s → Set.range x ⊆ genericPoints T → x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap V K) ≫ v → Flat (v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b) := by
  refine ⟨fun O _ _ _ T s hs x => ?_,
    fun R O _ _ _ _ b T s V K _ _ _ _ _ x v hb hs hx hxs => ?_⟩
  · obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x))
      (isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x))
    refine ⟨ξ, hξ.specializes mem_irreducibleComponent, ?_⟩
    have hgen : ξ ∈ genericPoints T := by
      change closure {ξ} ∈ irreducibleComponents T
      rw [hξ.def]
      exact irreducibleComponent_mem_irreducibleComponents x
    let δ : O →+* T.residueField ξ := (Spec.preimage (T.fromSpecResidueField ξ ≫ s)).hom
    have hδ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap δ = T.fromSpecResidueField ξ ≫ s := Spec.map_preimage _
    have hinj : Function.Injective δ := by
      refine _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint δ
        (IsLocalRing.closedPoint (T.residueField ξ)) ?_
      rw [hδ]
      exact (congrArg s (Scheme.fromSpecResidueField_apply ξ _)).trans
        (_root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s hgen)
    exact charZero_of_injective_ringHom hinj
  · let φ : O →+* V := (Spec.preimage v).hom
    have hv : v = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ := (Spec.map_preimage v).symm
    have hcomp : x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) := by
      rw [hxs, hv]; exact (Spec.map_comp _ _).symm
    let pt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K := IsLocalRing.closedPoint K
    have hpt : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ((algebraMap V K).comp φ) pt = genericPoint (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp O) := by
      rw [← hcomp, Scheme.Hom.comp_apply]
      exact _root_.GlobalTheory.GenericFlat.apply_eq_genericPoint s (hx ⟨pt, rfl⟩)
    have hφ : Function.Injective φ := by
      have h := _root_.GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ pt hpt
      rw [RingHom.coe_comp] at h
      exact h.of_comp
    have hψ : Function.Injective (φ.comp b) := hφ.comp hb
    have hmap : v ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap b = Spec.map (CommRingCat.ofHom (φ.comp b)) := by
      rw [hv]; exact (Spec.map_comp _ _).symm
    rw [hmap, HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := (φ.comp b).toAlgebra
    change Module.Flat R V
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule.eq_bot_iff]
    intro m hm
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff m).mp hm
    rw [Submonoid.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra] at ha
    have h0 : (φ.comp b) a ≠ 0 := fun h =>
      nonZeroDivisors.coe_ne_zero a (hψ (h.trans (map_zero _).symm))
    exact (mul_eq_zero.mp ha).resolve_left h0

end GlobalTheory.GenericFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirational
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory.FiniteBirationalNear

theorem exists_common_smul_mem {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (S : Submonoid A) {N : Submodule A M} (hN : N.FG) (N' : Submodule A M)
    (h : ∀ m ∈ N, ∃ s ∈ S, s • m ∈ N') : ∃ s ∈ S, ∀ m ∈ N, s • m ∈ N' := by
  classical
  obtain ⟨T, rfl⟩ := hN
  choose! s hs hs' using h
  refine ⟨∏ t ∈ T, s t, prod_mem fun t ht => hs t (Submodule.subset_span ht), ?_⟩
  have : Submodule.span A (T : Set M) ≤ N'.comap ((∏ t ∈ T, s t) • LinearMap.id) := by
    refine Submodule.span_le.2 fun t ht => ?_
    change (∏ t ∈ T, s t) • t ∈ N'
    rw [← Finset.prod_erase_mul T s ht, mul_smul]
    exact N'.smul_mem _ (hs' t (Submodule.subset_span ht))
  exact fun m hm => this hm

theorem exists_away_isDomain {A O : Type*} [CommRing A] [IsNoetherianRing A] [CommRing O]
    [Algebra A O] (S : Submonoid A) [IsLocalization S O] [IsDomain O] :
    ∃ s ∈ S, ∀ (P : Type) [CommRing P] [Algebra A P] [IsLocalization.Away s P], IsDomain P := by
  obtain ⟨s, hs, h⟩ := exists_common_smul_mem S
    (IsNoetherian.noetherian (RingHom.ker (algebraMap A O))) ⊥ fun m hm => by
      obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff S O m).1 hm
      exact ⟨c, c.2, hc⟩
  refine ⟨s, hs, fun P _ _ _ => ?_⟩
  have hu : IsUnit (algebraMap A O s) := IsLocalization.map_units O ⟨s, hs⟩
  refine Function.Injective.isDomain (IsLocalization.Away.lift (S := P) s hu) ?_
  rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro e
    have := congrArg (IsLocalization.Away.lift (S := P) s hu) e
    simpa using this
  · intro e
    have h1 : x - y ∈ RingHom.ker (algebraMap A O) := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    have h2 : s * (x - y) = 0 := h _ h1
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalization.map_eq_zero_iff (.powers s) P _).2 ⟨⟨s, Submonoid.mem_powers s⟩, h2⟩

theorem exists_mul_mem_range {A O K B : Type*} [CommRing A] [IsDomain A] [CommRing O]
    [Algebra A O] (S : Submonoid A) [IsLocalization S O] [IsDomain O] [IsIntegrallyClosed O]
    [Field K] [Algebra A K] [IsFractionRing A K] [CommRing B] [Algebra A B] [Module.Finite A B]
    (ψ : B →ₐ[A] K) (hψ : Function.Injective ψ) :
    ∃ r ∈ S, ∀ b : B, ∃ a : A, algebraMap A B a = algebraMap A B r * b := by
  have hu (s : S) : IsUnit (algebraMap A K s) := by
    refine IsUnit.mk0 _ fun h0 => ?_
    have h1 : (s : A) = 0 := IsFractionRing.injective A K (by rw [h0, map_zero])
    have h2 := IsLocalization.map_units O s
    rw [h1, map_zero] at h2
    exact not_isUnit_zero h2
  let : Algebra O K := (IsLocalization.lift (S := O) hu).toAlgebra
  have : IsScalarTower A O K := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.lift_eq hu a).symm
  have : IsFractionRing O K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S O K
  obtain ⟨r, hr, h⟩ := exists_common_smul_mem S (Module.Finite.fg_top (R := A) (M := B))
    (LinearMap.range (Algebra.linearMap A B)) fun b _ => by
      have hb : IsIntegral O (ψ b) := ((Algebra.IsIntegral.isIntegral (R := A) b).map ψ).tower_top
      obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.mp hb
      obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj S o
      refine ⟨s, s.2, a, hψ ?_⟩
      have e' := congrArg (algebraMap O K) e
      rw [map_mul, ho, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
      rw [Algebra.linearMap_apply, ψ.commutes, map_smul, Algebra.smul_def, mul_comm, e']
  refine ⟨r, hr, fun b => ?_⟩
  obtain ⟨a, ha⟩ := h b trivial
  exact ⟨a, by rw [← Algebra.smul_def]; exact ha⟩

theorem exists_isIntegral_nhds {M : Scheme.{0}} [IsLocallyNoetherian M] (x : M)
    [IsDomain (M.presheaf.stalk x)] : ∃ V : M.Opens, x ∈ V ∧ IsIntegral V := by
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    M.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(M, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := M.presheaf.algebra_section_stalk (U := U) ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨s, hs, h⟩ := exists_away_isDomain (O := M.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have := hU.isLocalization_basicOpen s
  have : IsDomain Γ(M, M.basicOpen s) := h _
  refine ⟨M.basicOpen s, (M.mem_basicOpen s x hxU).2
    (IsLocalization.map_units (M.presheaf.stalk x) ⟨s, hs⟩), ?_⟩
  exact IsIntegral.of_isIso (hU.basicOpen s).isoSpec.inv

theorem exists_isIso_of_isIntegral {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [IsIntegral X]
    [IsIntegral Y] [IsDominant f] [IsIso (f.stalkMap (genericPoint X))] (y : Y)
    [IsIntegrallyClosed (Y.presheaf.stalk y)] : ∃ V : Y.Opens, y ∈ V ∧ IsIso (f ∣_ V) := by
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : Nonempty U := ⟨⟨y, hxU⟩⟩
  letI := (f.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  have hη := apply_genericPoint_of_isDominant f
  have hyU : f (genericPoint X) ∈ U := by
    rw [hη]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨_, hyU⟩
  have hfr_local (z : Y) (hzU : z ∈ U) (hz : z = genericPoint Y) :
      letI := Y.presheaf.algebra_section_stalk (U := U) ⟨z, hzU⟩
      IsFractionRing Γ(Y, U) (Y.presheaf.stalk z) := by
    haveI : Nonempty U := ⟨⟨z, hzU⟩⟩
    subst hz
    exact functionField_isFractionRing_of_isAffineOpen Y U hU
  haveI : IsFractionRing Γ(Y, U) (Y.presheaf.stalk (f (genericPoint X))) :=
    hfr_local _ hyU hη
  have hgerm (a : Γ(Y, U)) : f.stalkMap (genericPoint X) (Y.presheaf.germ U _ hyU a) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hyU (f.app U a) :=
    f.germ_stalkMap_apply U _ hyU a
  have hbij : Function.Bijective (f.stalkMap (genericPoint X)) :=
    ConcreteCategory.bijective_of_isIso _
  have hinj : Function.Injective (f.app U) := by
    intro a a' h'
    apply germ_injective_of_isIntegral Y _ hyU
    apply hbij.1
    rw [hgerm, hgerm, h']
  let φ : Γ(X, f ⁻¹ᵁ U) ⟶ Y.presheaf.stalk (f (genericPoint X)) :=
    X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hyU ≫ inv (f.stalkMap (genericPoint X))
  have hφ (c : Γ(X, f ⁻¹ᵁ U)) : f.stalkMap (genericPoint X) (φ c) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) hyU c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Y.presheaf.stalk (f (genericPoint X)) :=
    { φ.hom with
      commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  have hψ : Function.Injective ψ := fun b b' e => by
    apply germ_injective_of_isIntegral X (genericPoint X) hyU
    rw [← hφ b, ← hφ b']
    exact congr(f.stalkMap (genericPoint X) $e)
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := IsFractionRing.toField Γ(Y, U)
  letI := Y.presheaf.algebra_section_stalk (U := U) ⟨y, hxU⟩
  have := hU.isLocalization_stalk ⟨y, hxU⟩
  obtain ⟨r, hr, h⟩ := exists_mul_mem_range (O := Y.presheaf.stalk y)
    (hU.primeIdealOf ⟨y, hxU⟩).asIdeal.primeCompl ψ hψ
  refine ⟨Y.basicOpen r, (Y.mem_basicOpen r y hxU).2
    (IsLocalization.map_units (Y.presheaf.stalk y) ⟨r, hr⟩), ?_⟩
  rw [isIso_morphismRestrict_iff_isIso_app _ (hU.basicOpen r),
    hU.app_basicOpen_eq_away_map f (hU.preimage f) r]
  refine IsIso.comp_isIso' ?_ inferInstance
  rw [ConcreteCategory.isIso_iff_bijective]
  have := hU.isLocalization_basicOpen r
  have := (hU.preimage f).isLocalization_basicOpen (f.app U r)
  constructor
  · exact (IsLocalization.Away.map_injective_iff _ _ _).2 fun a ha =>
      ⟨0, by rw [hinj (ha.trans (map_zero _).symm), mul_zero]⟩
  · refine (IsLocalization.Away.map_surjective_iff _ _ _ _).2 fun b => ?_
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, 1, by rw [pow_one]; exact ha⟩

theorem main : ∀ (U M : Scheme.{0}) [IsLocallyNoetherian M] (u : U ⟶ M) (W : M.Opens), IsFinite u → IsReduced U → IsIso (u ∣_ W) → Dense (W : Set M) → Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) → ∀ x : M, IsDomain (M.presheaf.stalk x) → IsIntegrallyClosed (M.presheaf.stalk x) → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V) := by
  intro U M _ u W _ _ hW hd hd' x _ _
  obtain ⟨V, hxV, hV⟩ := exists_isIntegral_nhds x
  let f := u ∣_ V
  let W' : V.toScheme.Opens := V.ι ⁻¹ᵁ W
  have : IsFinite f := MorphismProperty.of_isPullback (P := @IsFinite)
    (isPullback_morphismRestrict u V).flip ‹_›
  have hW' : IsIso (f ∣_ W') := by
    have h1 : IsIso (u ∣_ W ∣_ (W.ι ⁻¹ᵁ V)) := inferInstance
    have h2 := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u W (W.ι ⁻¹ᵁ V))).1 h1
    have e : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V.ι ''ᵁ W' := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, inf_comm]
    exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u V W')).2
      (((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictEq u e)).1 h2)
  have hne : Nonempty W' := by
    obtain ⟨z, hz, hz'⟩ := hd.inter_open_nonempty V V.isOpen ⟨x, hxV⟩
    exact ⟨⟨⟨z, hz⟩, hz'⟩⟩
  have : IsIntegral W' := isIntegral_of_isOpenImmersion W'.ι
  have : IsIntegral (f ⁻¹ᵁ W') := IsIntegral.of_isIso (inv (f ∣_ W'))
  have hd₂ : Dense ((f ⁻¹ᵁ W' : (u ⁻¹ᵁ V).toScheme.Opens) : Set (u ⁻¹ᵁ V).toScheme) := by
    have e : f ⁻¹ᵁ W' = (u ⁻¹ᵁ V).ι ⁻¹ᵁ u ⁻¹ᵁ W := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
    rw [e]
    exact hd'.preimage (u ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap
  have : IrreducibleSpace (u ⁻¹ᵁ V).toScheme := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hd₂.closure_eq]
    refine IsIrreducible.closure ?_
    exact isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace (f ⁻¹ᵁ W').toScheme))
  have : IsIntegral (u ⁻¹ᵁ V).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict f W' hne
  have : IsIntegrallyClosed (V.toScheme.presheaf.stalk (⟨x, hxV⟩ : V)) :=
    IsIntegrallyClosed.of_equiv (R := M.presheaf.stalk x)
      (V.stalkIso ⟨x, hxV⟩).symm.commRingCatIsoToRingEquiv
  obtain ⟨V', hx', hV'⟩ := exists_isIso_of_isIntegral f ⟨x, hxV⟩
  refine ⟨V.ι ''ᵁ V', ⟨⟨x, hxV⟩, hx', rfl⟩, ?_⟩
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict u V V')).1 hV'

end GlobalTheory.FiniteBirationalNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolynomialFinrankHomogeneousSubmodule
namespace GlobalTheory

private lemma finite_setOf_finsupp_degree_eq (σ : Type) [Finite σ] [Nonempty σ] (e : ℕ) :
    Finite ↑{d : σ →₀ ℕ | d.degree = e} := by
  have := Fintype.ofFinite σ
  have h : Nat.card {d : σ →₀ ℕ // d.degree = e} ≠ 0 := by
    rw [_root_.GlobalTheory.natCard_degree_eq]
    have := Fintype.card_pos (α := σ)
    exact (Nat.choose_pos (by omega)).ne'
  exact Nat.finite_of_card_ne_zero h

private lemma finrank_homogeneousSubmodule_eq_choose (σ : Type) [Fintype σ] [Nonempty σ] (K : Type)
    [Field K] (e : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K e) =
      (e + Fintype.card σ - 1).choose e := by
  have := finite_setOf_finsupp_degree_eq σ e
  have := Fintype.ofFinite ↑{d : σ →₀ ℕ | d.degree = e}
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
      {d : σ →₀ ℕ | d.degree = e}).finrank_eq,
    ← _root_.GlobalTheory.natCard_degree_eq σ e, Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
  rfl

private lemma cast_choose_eq_eval_descPochhammer (m e : ℕ) (hm : 1 ≤ m) :
    (((e + m - 1).choose e : ℕ) : ℚ) = (Polynomial.C (1 / ((m - 1).factorial : ℚ)) *
      (descPochhammer ℚ (m - 1)).comp (Polynomial.X + Polynomial.C ((m - 1 : ℕ) : ℚ))).eval
        (e : ℚ) := by
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  have h1 : (e : ℚ) + ((m - 1 : ℕ) : ℚ) = ((e + (m - 1) : ℕ) : ℚ) := by push_cast; ring
  rw [h1, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    show e + m - 1 = e + (m - 1) by omega, Nat.choose_symm_add]
  have : ((m - 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem _root_.GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule :
    ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ),
      ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) =
        Q.eval (e : ℚ) := by
  intro σ _ _
  have := Fintype.ofFinite σ
  refine ⟨Polynomial.C (1 / ((Fintype.card σ - 1).factorial : ℚ)) *
    (descPochhammer ℚ (Fintype.card σ - 1)).comp
      (Polynomial.X + Polynomial.C ((Fintype.card σ - 1 : ℕ) : ℚ)), fun K _ e => ?_⟩
  rw [finrank_homogeneousSubmodule_eq_choose σ K e]
  exact cast_choose_eq_eval_descPochhammer _ e Fintype.card_pos

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodicCechCocycleSmoothCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodicCechCocycleSmoothCoboundary
open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

theorem periodic_cech_cocycle_smooth_coboundary : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i j, ContDiffOn ℝ ∞ (c i j) (U i ∩ U j)) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, c i j (z + l) = c i j z) → (∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z = c i k z) → ∃ b : ι → (Fin g → ℂ) → ℂ, (∀ i, ContDiffOn ℝ ∞ (b i) (U i) ∧ ∀ (l : Λ), ∀ z ∈ U i, b i (z + l) = b i z) ∧ ∀ i j, ∀ z ∈ U i ∩ U j, c i j z = b j z - b i z := by
  intro g Λ hΛ hspan ι U c hU hper hcov hc hcper hcoc
  obtain ⟨s, ρ, hρ, hsum⟩ :=
    exists_smooth_periodic_partition_of_unity g Λ hΛ hspan ι U hU hper hcov
  have hzero : ∀ k z, z ∉ U k → ρ k z = 0 := by
    intro k z hz
    by_contra h
    exact hz ((hρ k).2.2 (subset_tsupport _ (Function.mem_support.mpr h)))
  refine ⟨fun i z => ∑ k ∈ s, (ρ k z : ℂ) * c k i z, fun i => ⟨?_, ?_⟩, ?_⟩
  · refine ContDiffOn.sum (fun k _ => ?_)
    have hρc : ContDiff ℝ ∞ (fun z => (ρ k z : ℂ)) := ofRealCLM.contDiff.comp (hρ k).1
    apply contDiffOn_of_locally_contDiffOn
    intro x _
    by_cases hxk : x ∈ U k
    · refine ⟨U k, hU k, hxk, ?_⟩
      exact hρc.contDiffOn.mul ((hc k i).mono fun z hz => ⟨hz.2, hz.1⟩)
    · refine ⟨(tsupport (ρ k))ᶜ, (isClosed_tsupport _).isOpen_compl,
        fun h => hxk ((hρ k).2.2 h), ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun z hz => ?_
      simp [image_eq_zero_of_notMem_tsupport hz.2]
  · intro l z hz
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hρ k).2.1 l z]
    by_cases hzk : z ∈ U k
    · rw [hcper k i l z ⟨hzk, hz⟩]
    · simp [hzero k z hzk]
  · intro i j z hz
    have hone : c i j z = ∑ k ∈ s, (ρ k z : ℂ) * c i j z := by
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum z]
      simp
    rw [hone, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hzk : z ∈ U k
    · rw [← hcoc k i j z ⟨⟨hzk, hz.1⟩, hz.2⟩]
      ring
    · simp [hzero k z hzk]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodicCechCocycleSmoothCoboundaryStatement
open Complex Matrix
open scoped ContDiff BigOperators Real
theorem _root_.GlobalTheory.T.exists_periodic_smooth_coboundary_of_cech_cocycle : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i j, ContDiffOn ℝ ∞ (c i j) (U i ∩ U j)) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, c i j (z + l) = c i j z) → (∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z = c i k z) → ∃ b : ι → (Fin g → ℂ) → ℂ, (∀ i, ContDiffOn ℝ ∞ (b i) (U i) ∧ ∀ (l : Λ), ∀ z ∈ U i, b i (z + l) = b i z) ∧ ∀ i j, ∀ z ∈ U i ∩ U j, c i j z = b j z - b i z := by
  first | exact @GlobalTheory.periodic_cech_cocycle_smooth_coboundary | exact GlobalTheory.periodic_cech_cocycle_smooth_coboundary | (intros; apply GlobalTheory.periodic_cech_cocycle_smooth_coboundary <;> assumption)
end
end
