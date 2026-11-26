module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfAssembleMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocalLatticeRepresentationSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicative

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentWittTiltEqZeroOfResidueZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentWittTiltEqZeroOfResidueZero
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.IdemVanish

theorem dvd_of_one_tmul_eq_zero {O k R : Type} [CommRing O] [CommRing k] [CommRing R]
    [Algebra O k] [Algebra O R] (lam : O) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) (x : R)
    (hx : ((1 : k) ⊗ₜ[O] x : k ⊗[O] R) = 0) : algebraMap O R lam ∣ x := by

  let f : O →ₐ[O] k := Algebra.ofId O k
  have hf : Function.Surjective f := hs
  have hker : RingHom.ker f = Ideal.span {lam} := by
    ext a
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    exact hk a
  let e : (O ⧸ RingHom.ker f) ≃ₐ[O] k := Ideal.quotientKerAlgEquivOfSurjective hf
  let φ : k ⊗[O] R ≃ₗ[O] R ⧸ (RingHom.ker f • (⊤ : Submodule O R)) :=
    (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl O R)).trans
      (TensorProduct.quotTensorEquivQuotSMul R (RingHom.ker f))
  have he : e.symm (1 : k) = Ideal.Quotient.mk (RingHom.ker f) 1 := by simp
  have h1 : φ ((1 : k) ⊗ₜ[O] x) = Submodule.Quotient.mk x := by
    simp only [φ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply,
      LinearEquiv.refl_apply, he, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have h2 : x ∈ RingHom.ker f • (⊤ : Submodule O R) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← h1, hx, map_zero]
  rw [hker, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨y, -, hy⟩ := h2
  exact ⟨y, by rw [← hy, Algebra.smul_def]⟩

theorem idem_eq_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] (lam : ↥(OL LL)), Function.Surjective (algebraMap ↥(OL LL) k) → (∀ x, algebraMap ↥(OL LL) k x = 0 ↔ lam ∣ x) → ∀ x : RW LL, IsIdempotentElem x → ((1 : k) ⊗ₜ[↥(OL LL)] x : k ⊗[↥(OL LL)] RW LL) = 0 → x = 0 := by
  intro l _ P LL k _ _ lam hs hk x hx h1

  have hd : algebraMap (↥(OL LL)) (RW LL) lam ∣ x := dvd_of_one_tmul_eq_zero lam hs hk x h1
  have hnu : ¬ IsUnit lam := by
    intro hu
    have h0 : algebraMap (↥(OL LL)) k 1 = 0 := (hk 1).2 hu.dvd
    simp at h0
  obtain ⟨m, hm⟩ := (GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL lam).resolve_left hnu
  apply GlobalTheory.EtaleExact.sep_RW LL x
  intro n
  calc (l : RW LL) ^ n = algebraMap (↥(OL LL)) (RW LL) (((l : ℕ) : ↥(OL LL)) ^ n) := by
        rw [map_pow, map_natCast]
    _ ∣ algebraMap (↥(OL LL)) (RW LL) (lam ^ (m * n)) :=
        map_dvd _ (by rw [pow_mul]; exact pow_dvd_pow_of_dvd hm n)
    _ ∣ algebraMap (↥(OL LL)) (RW LL) lam ^ (m * n + 1) := by
        rw [map_pow]; exact pow_dvd_pow _ (Nat.le_succ _)
    _ ∣ x ^ (m * n + 1) := pow_dvd_pow_of_dvd hd _
    _ = x := hx.pow_succ_eq _

end GlobalTheory.IdemVanish
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentWittTiltEqZeroOfResidueZeroStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_witt_tilt_eq_zero_of_residue_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] (lam : ↥(OL LL)), Function.Surjective (algebraMap ↥(OL LL) k) → (∀ x, algebraMap ↥(OL LL) k x = 0 ↔ lam ∣ x) → ∀ x : RW LL, IsIdempotentElem x → ((1 : k) ⊗ₜ[↥(OL LL)] x : k ⊗[↥(OL LL)] RW LL) = 0 → x = 0 := by
  first | exact @GlobalTheory.IdemVanish.idem_eq_zero | exact GlobalTheory.IdemVanish.idem_eq_zero | (intros; apply GlobalTheory.IdemVanish.idem_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionCyclotomicEndoEqFrobeniusLaurent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionCyclotomicEndoEqFrobeniusLaurent
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
namespace GlobalTheory.RedPhiProof

theorem ringHom_eq_of_agree {O k : Type} [CommRing O] [CommRing k] (f g : O⟦X⟧ →+* k⟦X⟧)
    (hC : ∀ c : O, f (PowerSeries.C c) = g (PowerSeries.C c))
    (hX : f PowerSeries.X = g PowerSeries.X) (hd : PowerSeries.X ∣ f PowerSeries.X) (a : O⟦X⟧) :
    f a = g a := by

  have hpoly : ∀ p : Polynomial O, f (p : O⟦X⟧) = g (p : O⟦X⟧) := by
    intro p
    have hfg : f.comp (Polynomial.coeToPowerSeries.ringHom) = g.comp (Polynomial.coeToPowerSeries.ringHom) :=
      Polynomial.ringHom_ext (fun c => by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hC c)
        (by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hX)
    simpa [Polynomial.coeToPowerSeries.ringHom_apply] using RingHom.congr_fun hfg p
  refine PowerSeries.ext fun n => ?_
  rw [← sub_eq_zero, ← map_sub]

  have htail : PowerSeries.X ^ (n + 1) ∣ a - (PowerSeries.trunc (n + 1) a : O⟦X⟧) := by
    refine PowerSeries.X_pow_dvd_iff.mpr fun m hm => ?_
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨b, hb⟩ := htail
  have ha : a = (PowerSeries.trunc (n + 1) a : O⟦X⟧) + PowerSeries.X ^ (n + 1) * b := by
    rw [← hb]; ring

  have hdiv : PowerSeries.X ^ (n + 1) ∣ f a - g a := by
    have e : f a - g a = f PowerSeries.X ^ (n + 1) * (f b - g b) := by
      conv_lhs => rw [ha]
      rw [map_add (f := _), map_add (f := _), hpoly, map_mul, map_mul, map_pow, map_pow, ← hX]
      ring
    rw [e]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd _) _
  exact PowerSeries.X_pow_dvd_iff.mp hdiv n (Nat.lt_succ_self n)

theorem red_phi (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [Field k] [Algebra O k] [CharP k l]
    (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (h : φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1) (a : O⟦X⟧) :
    ((PowerSeries.map (algebraMap O k) (φ₀ a) : k⟦X⟧) : k⸨X⸩) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩) := by
  have hc : PowerSeries.constantCoeff ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) = 0 := by simp
  have hs : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hc

  have key : PowerSeries.map (algebraMap O k) (φ₀ a) =
      (PowerSeries.map (algebraMap O k) a).subst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) := by
    have e := ringHom_eq_of_agree ((PowerSeries.map (algebraMap O k)).comp φ₀.toRingHom)
      ((PowerSeries.substAlgHom hs).toRingHom.comp (PowerSeries.map (algebraMap O k)))
      (fun c => by
        have h1 : φ₀ (PowerSeries.C c) = PowerSeries.C c := by simpa using φ₀.commutes c
        have h2 := (PowerSeries.substAlgHom hs).commutes (algebraMap O k c)
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, PowerSeries.map_C]
        simpa using h2.symm)
      (by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h, PowerSeries.map_X,
          PowerSeries.substAlgHom_X]
        simp)
      (by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h]
        exact PowerSeries.X_dvd_iff.mpr (by simp))
      a
    simpa [PowerSeries.coe_substAlgHom] using e
  rw [key, GlobalTheory.PsiShiftProof.phi_eq_subst, GlobalTheory.PsiLemmaCompare.substHom_coe]

end GlobalTheory.RedPhiProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionCyclotomicEndoEqFrobeniusLaurentStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_cyclotomic_endo_eq_frobenius_laurent : ∀ (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [Field k] [Algebra O k] [CharP k l] (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧), φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 → ∀ a : O⟦X⟧, ((PowerSeries.map (algebraMap O k) (φ₀ a) : k⟦X⟧) : k⸨X⸩) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩) := by
  first | exact @GlobalTheory.RedPhiProof.red_phi | exact GlobalTheory.RedPhiProof.red_phi | (intros; apply GlobalTheory.RedPhiProof.red_phi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiagonalRingHomOfLetterwiseReductions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiagonalRingHomOfLetterwiseReductions
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory

theorem exists_diagonal_ringHom_of_letterwise_reductions :
    ∀ (I E F R : Type) [Fintype I] [CommRing E] [CommRing F] [CommRing R] (e : I → E), (∀ i, e i * e i = e i) → (∀ i j, i ≠ j → e i * e j = 0) → ∑ i, e i = 1 → ∀ (p : I → (E →+* F)) (r : E →+* R), (∀ i, Function.Surjective (p i)) → (∀ i x, p i x = 0 → r (e i) * r x = 0) → ∃ κ : F →+* R, ∀ i x, r (e i) * κ (p i x) = r (e i) * r x := by
  intro I E F R _ _ _ _ e hid hort hsum p r hsurj hker
  classical
  choose s hs using hsurj
  have key : ∀ i x y, p i x = p i y → r (e i) * r x = r (e i) * r y := by
    intro i x y h
    have := hker i (x - y) (by rw [map_sub, h, sub_self])
    rw [map_sub, mul_sub] at this
    exact sub_eq_zero.mp this
  have hext : ∀ a b : R, (∀ i, r (e i) * a = r (e i) * b) → a = b := by
    intro a b h
    have h1 : ∑ i, r (e i) = 1 := by rw [← map_sum, hsum, map_one]
    calc a = (∑ i, r (e i)) * a := by rw [h1, one_mul]
      _ = (∑ i, r (e i)) * b := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => h i
      _ = b := by rw [h1, one_mul]
  have hidR : ∀ i, r (e i) * r (e i) = r (e i) := fun i => by rw [← map_mul, hid]
  let k : F → R := fun c => ∑ i, r (e i) * r (s i c)
  have hk0 : ∀ i c, r (e i) * k c = r (e i) * r (s i c) := by
    intro i c
    show r (e i) * ∑ j, r (e j) * r (s j c) = _
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [← mul_assoc, hidR]
    · intro j _ hj
      rw [← mul_assoc, ← map_mul, hort i j (Ne.symm hj), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hk : ∀ i x, r (e i) * k (p i x) = r (e i) * r x := by
    intro i x
    rw [hk0]
    exact key i _ _ (hs i _)
  refine ⟨{ toFun := k, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hk⟩
  · apply hext
    intro i
    have := hk i 1
    rwa [map_one, map_one] at this
  · intro a b
    apply hext
    intro i
    have h := hk i (s i a * s i b)
    rw [map_mul, hs, hs, map_mul] at h
    have ha := hk0 i a
    have hb := hk0 i b
    have hi := hidR i
    rw [h]
    linear_combination (-(k b)) * ha - (r (s i a)) * hb
  · apply hext
    intro i
    have := hk i 0
    rwa [map_zero, map_zero] at this
  · intro a b
    apply hext
    intro i
    have h := hk i (s i a + s i b)
    rw [map_add (f := _), hs, hs, map_add (f := _)] at h
    rw [h, mul_add, mul_add, hk0, hk0]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiagonalRingHomOfLetterwiseReductionsStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_of_idempotent_surjective_family : ∀ (I E F R : Type) [Fintype I] [CommRing E] [CommRing F] [CommRing R] (e : I → E), (∀ i, e i * e i = e i) → (∀ i j, i ≠ j → e i * e j = 0) → ∑ i, e i = 1 → ∀ (p : I → (E →+* F)) (r : E →+* R), (∀ i, Function.Surjective (p i)) → (∀ i x, p i x = 0 → r (e i) * r x = 0) → ∃ κ : F →+* R, ∀ i x, r (e i) * κ (p i x) = r (e i) * r x := by
  first | exact @GlobalTheory.exists_diagonal_ringHom_of_letterwise_reductions | exact GlobalTheory.exists_diagonal_ringHom_of_letterwise_reductions | (intros; apply GlobalTheory.exists_diagonal_ringHom_of_letterwise_reductions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceFormIntegralIffGoodCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceFormIntegralIffGoodCoeff
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

theorem exists_trace_form_integral_iff : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ lam : LL →ₗ[ℚ_[l]] ℚ_[l], ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a := by
  intro l _ LL _ _ _ O _ _ hG
  have hint := (good_coeff_integers l LL O hG).1
  obtain ⟨⟨hD, hDVR, hFr⟩, hfin, hmod, htop, hopen⟩ := hG
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI : FiniteDimensional ℚ_[l] LL := hfin
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let A : Subring LL := (algebraMap O LL).range
  have hZ : ∀ u : ℤ_[l], algebraMap ℤ_[l] LL u ∈ A := fun u =>
    padicInt_mem A (by rw [RingHom.coe_range]; exact hopen) u
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  let ψ : O ≃+* A := RingEquiv.ofBijective (algebraMap O LL).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap O LL).rangeRestrict_surjective⟩
  have hψ : ∀ a : A, algebraMap O LL (ψ.symm a) = a := fun a =>
    congrArg Subtype.val (ψ.apply_symm_apply a)
  let f : ℤ_[l] →+* O := ψ.symm.toRingHom.comp ((algebraMap ℤ_[l] LL).codRestrict A hZ)
  letI : Algebra ℤ_[l] O := f.toAlgebra
  haveI : IsScalarTower ℤ_[l] O LL := IsScalarTower.of_algebraMap_eq
    (fun u => (hψ ((algebraMap ℤ_[l] LL).codRestrict A hZ u)).symm)
  haveI : IsIntegralClosure O ℤ_[l] LL :=
    { algebraMap_injective := hinj
      isIntegral_iff := fun {x} => by
        rw [← Set.mem_range]
        exact (hint x).symm }
  let D : FractionalIdeal (nonZeroDivisors O) LL := FractionalIdeal.dual ℤ_[l] ℚ_[l] 1
  have hD0 : D ≠ 0 := FractionalIdeal.dual_ne_zero ℤ_[l] ℚ_[l] one_ne_zero
  haveI hP : (D : Submodule O LL).IsPrincipal := FractionalIdeal.isPrincipal D
  set c : LL := Submodule.IsPrincipal.generator (D : Submodule O LL) with hc
  have hDc : (D : Submodule O LL) = Submodule.span O {c} :=
    (Submodule.IsPrincipal.span_singleton_generator _).symm
  have hc0 : c ≠ 0 := by
    intro h
    apply hD0
    apply FractionalIdeal.coeToSubmodule_injective
    show (D : Submodule O LL) = ((0 : FractionalIdeal (nonZeroDivisors O) LL) : Submodule O LL)
    rw [hDc, h, FractionalIdeal.coe_zero]
    exact Submodule.span_singleton_eq_bot.2 rfl
  refine ⟨(Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c), fun a => ?_⟩
  have key : (∀ b : O, ∃ u : ℤ_[l], (Algebra.trace ℚ_[l] LL) (c * (a * algebraMap O LL b)) = (u : ℚ_[l]))
      ↔ c * a ∈ D := by
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors O) LL) ≠ 0)]
    constructor
    · intro h y hy
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      obtain ⟨u, hu⟩ := h b
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc, hu]
      rfl
    · intro h b
      obtain ⟨u, hu⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩)
      refine ⟨u, ?_⟩
      rw [Algebra.traceForm_apply, mul_assoc] at hu
      rw [← hu]
      rfl
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [key, ← FractionalIdeal.mem_coe, hDc, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [Algebra.smul_def, mul_comm] at hz
    exact mul_left_cancel₀ hc0 hz
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, mul_comm]⟩

end GlobalTheory.GoodCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceFormIntegralIffGoodCoeffStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_form_integral_iff_goodCoeff : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ lam : LL →ₗ[ℚ_[l]] ℚ_[l], ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a := by
  first | exact @GlobalTheory.GoodCoeff.exists_trace_form_integral_iff | exact GlobalTheory.GoodCoeff.exists_trace_form_integral_iff | (intros; apply GlobalTheory.GoodCoeff.exists_trace_form_integral_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfFixedByDeltaGammaLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfFixedByDeltaGammaLifts
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.HerrClass

namespace GlobalTheory.RedDense

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_pred_sub_one_le {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l]) ^ (l - 1) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
  let u : ℤ_[l] := ⟨(χ g : ℚ_[l]), hχ.norm_le_one g⟩
  have hu : IsUnit u := PadicInt.isUnit_iff.2 (hχ.norm_eq_one g)
  have h3 : PadicInt.toZMod (u ^ (l - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one (hu.map _).ne_zero, sub_self]
  have h4 : u ^ (l - 1) - 1 ∈ Ideal.span {(l : ℤ_[l]) ^ 1} := by
    rw [pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
    exact h3
  have h5 := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).2 h4
  rw [PadicInt.norm_def] at h5
  exact h5

theorem card_and_dense {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} {s : ℕ} (h2 : l ≠ 2)
    (hK : K.1 ≤ Ks K s)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    ¬ l ∣ W.DelF.card ∧ ∀ γ : W.Gam, (W.χΓ γ : ↥(OL LL)) = 1 + (l : ↥(OL LL)) →
      ∀ U : Subgroup ↥(GK K), IsClosed (U : Set ↥(GK K)) →
        (∀ g, (W.resΓ g ∈ W.DelF ∨ W.resΓ g = γ) → g ∈ U) → ∀ g, g ∈ U := by
  have hl : l.Prime := Fact.out
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨-, -, hG⟩ := cyc_basic l P.χQ hχ
  have hH0 : ∀ x ∈ Hinf K, x ∈ (K0 K).fixingSubgroup := fun x hx y =>
    hx ⟨y.1, (le_sup_left : K0 K ≤ Kinf K) y.2⟩
  have hH : Hinf K ≤ GK K := by
    intro x hx
    have h1 : x ∈ Gj K s := ((hG K x (hH0 x hx)).1 s).2 (by
      rw [(hG K x (hH0 x hx)).2.1 hx, Units.val_one, sub_self, norm_zero]
      positivity)
    exact fun y => h1 ⟨y.1, hK y.2⟩
  have hj : Lev l 1 := ⟨le_rfl, fun e => absurd e h2⟩
  have hN : ¬ l ∣ l - 1 := by
    have := hl.two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpow := norm_pow_pred_sub_one_le hχ
  have hN0 : l - 1 ≠ 0 := by have := hl.two_le; omega
  refine ⟨?_, fun γ hγ U hU hp g => ?_⟩
  · have htor : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := by
      intro δ hδ
      obtain ⟨g, rfl⟩ := W.resΓ_onto δ
      obtain ⟨k, hk, hk'⟩ := (W.DelF_def _).1 hδ
      rw [res_pow_eq_one_iff] at hk' ⊢
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      refine eq_one_of_pow hj (hpow g) hk.ne' ?_
      rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hk', Units.val_one, one_pow]
    have h1Δ : (1 : W.Gam) ∈ W.DelF := (mem_DelF_iff W _).2 (one_mem _)
    intro hdv
    haveI : Finite ↥(CommGroup.torsion W.Gam) := Nat.finite_of_card_ne_zero (by
      rw [card_torsion]; exact Finset.card_ne_zero.2 ⟨1, h1Δ⟩)
    rw [← card_torsion] at hdv
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hdv
    apply hN
    have h3 : orderOf x ∣ l - 1 :=
      orderOf_dvd_iff_pow_eq_one.2 (Subtype.ext (htor x ((mem_DelF_iff W _).2 x.2)))
    rwa [hx] at h3
  · have hmemΔ : ∀ g : ↥(GK K), P.χQ g ^ (l - 1) = 1 → W.resΓ g ∈ W.DelF := fun g hg =>
      (W.DelF_def _).2 ⟨l - 1, Nat.pos_of_ne_zero hN0, (res_pow_eq_one_iff W g _).2 hg⟩
    obtain ⟨γ', hγ'⟩ := W.resΓ_onto γ
    have hv : (P.χQ γ' : ℚ_[l]) = 1 + l := by
      apply (algebraMap ℚ_[l] ↥LL.1).injective
      rw [← chi_res W γ', hγ', hγ]
      simp
    have hn : ‖(P.χQ γ' : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
      rw [hv, add_sub_cancel_left, Padic.norm_p]
      simp
    refine mem_of_tors_gen ha hχ K hH hj hN hN (fun x _ => hpow x) (fun x _ hx => hx) U hU
      (fun x hx => hp x (Or.inl (hmemΔ x hx))) γ' (hp γ' (Or.inr hγ')) (fun x => ?_) g
    rw [norm_pow_sub_one hj hn.le hN, hn]
    exact hpow x

theorem exists_closed_stab {G Qp LL O k : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL] [Field k]
    [Algebra O k] (hO : IsOpen (Set.range (algebraMap O LL))) {c : O} (hc : algebraMap O LL c ≠ 0)
    (hk : algebraMap O k c = 0) (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k))
    (hq : Onto T A q) (t : Fin A.m → k) :
    ∃ U : Subgroup G, IsClosed (U : Set G) ∧ ∀ g, g ∈ U ↔ A.ρ g t = t := by
  obtain ⟨x, rfl⟩ := hq.1 t
  have hlc : IsLocallyConstant fun g => q (latRep T.L g x) :=
    GlobalTheory.FiniteAdm.isLocallyConstant_comp hO T.L.T T.L.fg T.L.span hc q
      (fun y => by rw [← algebraMap_smul k, hk, zero_smul]) _ (T.cont x)
  let U : Subgroup G :=
    { carrier := {g | A.ρ g (q x) = q x}
      mul_mem' := fun {a b} ha hb => by
        change A.ρ a (q x) = q x at ha
        change A.ρ b (q x) = q x at hb
        change A.ρ (a * b) (q x) = q x
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        change A.ρ a (q x) = q x at ha
        change A.ρ a⁻¹ (q x) = q x
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  refine ⟨U, ?_, fun g => Iff.rfl⟩
  have := hlc.isClosed_fiber (q x)
  simp only [hq.2] at this
  exact this

theorem fixed_of_fixed_lifts : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → (((S.W H).DelF.card : ℕ) : k) ≠ 0 ∧ ∀ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)), Onto T A q → ∀ t : Fin A.m → k, (∀ g, ((S.W H).resΓ g ∈ (S.W H).DelF ∨ (S.W H).resΓ g = γ) → A.ρ g t = t) → ∀ g, A.ρ g t = t := by
  intro l _ P AI H S k _ _ _ _
  have hl : l.Prime := Fact.out
  obtain ⟨h1, h2⟩ := card_and_dense AI S.hyp.1.2.1.2.1 S.hyp.1.2.1.2.2.2.2.1 (S.W H)
  refine ⟨fun h => h1 ((CharP.cast_eq_zero_iff k l _).1 h), fun γ hγ T A q hq t ht => ?_⟩
  haveI : IsTopologicalRing ↥S.LL.1 :=
    inferInstanceAs (IsTopologicalRing ↥S.LL.1.toSubalgebra.toSubring)
  obtain ⟨U, hU, hm⟩ := exists_closed_stab (c := (l : S.O)) (GlobalTheory.LocalIntegers.isOpen_integers l S.LL)
    (by rw [map_natCast]; exact Nat.cast_ne_zero.2 hl.ne_zero)
    (by rw [map_natCast, CharP.cast_eq_zero]) T A q hq t
  exact fun g => (hm g).1 (h2 γ hγ U hU (fun g hg => (hm g).2 (ht g hg)) g)

end GlobalTheory.RedDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfFixedByDeltaGammaLiftsStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_of_fixed_by_delta_gamma_lifts : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → (((S.W H).DelF.card : ℕ) : k) ≠ 0 ∧ ∀ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) (q : ↥T.L.T →ₗ[S.O] (Fin A.m → k)), Onto T A q → ∀ t : Fin A.m → k, (∀ g, ((S.W H).resΓ g ∈ (S.W H).DelF ∨ (S.W H).resΓ g = γ) → A.ρ g t = t) → ∀ g, A.ρ g t = t := by
  first | exact @GlobalTheory.RedDense.fixed_of_fixed_lifts | exact GlobalTheory.RedDense.fixed_of_fixed_lifts | (intros; apply GlobalTheory.RedDense.fixed_of_fixed_lifts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModuleGeneratorReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelMap
namespace GlobalTheory.RelationExtension

section
variable {A E F : Type} [CommRing A] [CommRing E] [CommRing F]

def Rel (ι : A →+* E) (f : A →+* F) (π P : A) (e : E) (x : F) : Prop :=
  ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y ∧ x * f π ^ m = f a

theorem rel_unique (ι : A →+* E) (f : A →+* F) (π P : A) (hu : IsUnit (f π)) (hP : f P = 0)
    (hk : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b : A, a = P * b) {e : E} {x x' : F}
    (h : Rel ι f π P e x) (h' : Rel ι f π P e x') : x = x' := by
  obtain ⟨a, m, y, h1, h2⟩ := h
  obtain ⟨a', m', y', h1', h2'⟩ := h'
  obtain ⟨b, hb⟩ := hk (a * π ^ m' - a' * π ^ m) (y' * ι π ^ m - y * ι π ^ m') (by
    simp only [map_sub, map_mul, map_pow]
    linear_combination (-(ι π ^ m')) * h1 + (ι π ^ m) * h1')
  have hf := congrArg f hb
  rw [map_mul, hP, zero_mul, map_sub, map_mul, map_mul, map_pow, map_pow] at hf
  have hu' : IsUnit (f π ^ (m + m')) := hu.pow _
  have h3 : x * f π ^ (m + m') = x' * f π ^ (m + m') := by
    rw [pow_add]
    linear_combination (f π ^ m') * h2 - (f π ^ m) * h2' + hf
  exact hu'.mul_right_cancel h3

theorem rel_map (ι : A →+* E) (f : A →+* F) (π P : A) (a : A) : Rel ι f π P (ι a) (f a) := ⟨a, 0, 0, by simp, by simp⟩

theorem rel_add (ι : A →+* E) (f : A →+* F) (π P : A) {e e' : E} {x x' : F}
    (h : Rel ι f π P e x) (h' : Rel ι f π P e' x') : Rel ι f π P (e + e') (x + x') := by
  obtain ⟨a, m, y, h1, h2⟩ := h
  obtain ⟨a', m', y', h1', h2'⟩ := h'
  refine ⟨a * π ^ m' + a' * π ^ m, m + m', y * ι π ^ m' + y' * ι π ^ m, ?_, ?_⟩
  · rw [pow_add, map_add (f := _), map_mul, map_mul, map_pow, map_pow]
    linear_combination (ι π ^ m') * h1 + (ι π ^ m) * h1'
  · rw [pow_add, map_add (f := _), map_mul, map_mul, map_pow, map_pow]
    linear_combination (f π ^ m') * h2 + (f π ^ m) * h2'

theorem rel_mul (ι : A →+* E) (f : A →+* F) (π P : A) {e e' : E} {x x' : F}
    (h : Rel ι f π P e x) (h' : Rel ι f π P e' x') : Rel ι f π P (e * e') (x * x') := by
  obtain ⟨a, m, y, h1, h2⟩ := h
  obtain ⟨a', m', y', h1', h2'⟩ := h'
  refine ⟨a * a', m + m', y * ι a' + ι a * y' + ι P * y * y', ?_, ?_⟩
  · rw [pow_add, map_mul]
    linear_combination (e' * ι π ^ m') * h1 + (ι a + ι P * y) * h1'
  · rw [pow_add, map_mul]
    linear_combination (x' * f π ^ m') * h2 + f a * h2'

end

theorem exists_extension {A E F : Type} [CommRing A] [CommRing E] [CommRing F]
    (ι : A →+* E) (f : A →+* F) (π P : A) (hu : IsUnit (f π)) (hP : f P = 0)
    (hs : ∀ e : E, ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y)
    (hk : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b : A, a = P * b) :
    ∃ g : E →+* F, ∀ a : A, g (ι a) = f a := by
  have hex : ∀ e, ∃ x, Rel ι f π P e x := fun e => by
    obtain ⟨a, m, y, h⟩ := hs e
    exact ⟨f a * Ring.inverse (f π ^ m), a, m, y, h, by rw [mul_assoc, Ring.inverse_mul_cancel _ (hu.pow m), mul_one]⟩
  choose g hg using hex
  have hgu : ∀ e x, Rel ι f π P e x → g e = x := fun e x h => rel_unique ι f π P hu hP hk (hg e) h
  have h1 := rel_map ι f π P 1
  rw [map_one, map_one] at h1
  have h0 := rel_map ι f π P 0
  rw [map_zero, map_zero] at h0
  exact ⟨{ toFun := g
           map_one' := hgu _ _ h1
           map_mul' := fun e e' => hgu _ _ (rel_mul ι f π P (hg e) (hg e'))
           map_zero' := hgu _ _ h0
           map_add' := fun e e' => hgu _ _ (rel_add ι f π P (hg e) (hg e')) },
    fun a => hgu _ _ (rel_map ι f π P a)⟩

end GlobalTheory.RelationExtension
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModuleGeneratorReduction
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_extend_of_dense {A E F : Type} [CommRing A] [CommRing E] [CommRing F] (ι : A →+* E) (f : A →+* F)
    (π P : A) (hf : IsUnit (f π)) (hP : f P = 0)
    (hd : ∀ e : E, ∃ (a : A) (m : ℕ) (y : E), e * ι π ^ m = ι a + ι P * y)
    (hs : ∀ (a : A) (y : E), ι a = ι P * y → ∃ b, a = P * b) :
    ∃ g : E →+* F, (∀ a, g (ι a) = f a) := by
  first
  | exact @_root_.GlobalTheory.RelationExtension.exists_extension
  | exact _root_.GlobalTheory.RelationExtension.exists_extension
  | (apply _root_.GlobalTheory.RelationExtension.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelationExtension.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelationExtension.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelationExtension.exists_extension ..)

theorem exists_letter_reduction : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {k : Type} [Field k] [Algebra O k] (lam : O), Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 ↔ lam ∣ x) → ((PD.p : ℕ) : k) = 0 → ∃ p : ZMod n → (W.EE →+* k⸨X⸩), (∀ i (a : LetA O n), p i (algebraMap (LetA O n) W.EE a) = ((PowerSeries.map (algebraMap O k) (a i) : k⟦X⟧) : k⸨X⸩)) ∧ (∀ i, Function.Surjective (p i)) ∧ ∀ i e, p i e = 0 → ∃ e', algebraMap (LetA O n) W.EE (letE i) * e = algebraMap O W.EE lam * e' := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W k _ _ lam hsurj hker hp
  let f : ZMod n → (LetA O n →+* k⸨X⸩) := fun i =>
    (algebraMap k⟦X⟧ k⸨X⸩).comp ((PowerSeries.map (algebraMap O k)).comp (Pi.evalRingHom (fun _ => O⟦X⟧) i))
  have hf : ∀ i (a : LetA O n), f i a = algebraMap k⟦X⟧ k⸨X⸩ (PowerSeries.map (algebraMap O k) (a i)) :=
    fun _ _ => rfl
  have hX : ∀ i, f i letπ = algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X := fun i => by
    rw [hf, letπ, PowerSeries.map_X]
  have hu : IsUnit (algebraMap k⟦X⟧ k⸨X⸩ PowerSeries.X) :=
    IsLocalization.map_units k⸨X⸩ (⟨PowerSeries.X, Submonoid.mem_powers _⟩ : Submonoid.powers (PowerSeries.X : k⟦X⟧))
  have hP : ∀ i, f i (PD.p : LetA O n) = 0 := fun i => by
    rw [map_natCast, ← map_natCast (algebraMap k k⸨X⸩), hp, map_zero]
  have hd : ∀ e : W.EE, ∃ (a : LetA O n) (m : ℕ) (y : W.EE), e * algebraMap (LetA O n) W.EE letπ ^ m =
      algebraMap (LetA O n) W.EE a + algebraMap (LetA O n) W.EE (PD.p : LetA O n) * y := by
    intro e
    obtain ⟨a, m, h⟩ := W.EE_dense e 1
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
    refine ⟨a, m, y, ?_⟩
    rw [map_pow, pow_one] at hy
    rw [map_natCast]
    linear_combination -hy
  have hs : ∀ (a : LetA O n) (y : W.EE), algebraMap (LetA O n) W.EE a =
      algebraMap (LetA O n) W.EE (PD.p : LetA O n) * y → ∃ b, a = (PD.p : LetA O n) * b := by
    intro a y h
    have := W.EE_sat a 1 (Ideal.mem_span_singleton'.2 ⟨y, by rw [h, map_natCast, pow_one, mul_comm]⟩)
    simpa using this
  choose p hpa using fun i => exists_extend_of_dense (algebraMap (LetA O n) W.EE) (f i) letπ (PD.p : LetA O n)
    (by rw [hX]; exact hu) (hP i) hd hs
  obtain ⟨u, hπ⟩ := W.EE_π.exists_right_inv
  refine ⟨p, fun i a => hpa i a, fun i c => ?_, fun i e he => ?_⟩
  · obtain ⟨⟨s, ⟨_, m, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (PowerSeries.X : k⟦X⟧)) c
    obtain ⟨t, rfl⟩ := PowerSeries.map_surjective _ hsurj s
    refine ⟨algebraMap (LetA O n) W.EE (fun _ => t) * u ^ m, ?_⟩
    have h1 := congrArg (p i) hπ
    rw [map_mul, hpa, hX, map_one] at h1
    simp only [map_pow] at h
    rw [map_mul, hpa, hf, map_pow, ← h, mul_assoc, ← mul_pow, h1, one_pow, mul_one]
  · obtain ⟨a, m, y, h⟩ := hd e
    have h1 := congrArg (p i) h
    rw [map_mul, he, zero_mul, map_add (f := _), map_mul, hpa, hpa, hP, zero_mul, add_zero, hf] at h1
    have h2 : PowerSeries.map (algebraMap O k) (a i) = 0 :=
      (IsFractionRing.injective k⟦X⟧ k⸨X⸩) (by rw [map_zero]; exact h1.symm)
    have h3 : ∀ j, ∃ d, PowerSeries.coeff j (a i) = lam * d := fun j => (hker _).1 (by
      have := congrArg (PowerSeries.coeff j) h2
      simpa using this)
    choose d hd' using h3
    obtain ⟨c, hc⟩ := (hker (PD.p : O)).1 (by rw [map_natCast, hp])
    have h4 : letE i * a = algebraMap O (LetA O n) lam * (letE i * fun _ => PowerSeries.mk d) := by
      funext j
      by_cases hj : j = i
      · subst hj
        ext l
        simp [letE, hd']
      · simp [letE, hj]
    have h5 : (PD.p : LetA O n) = algebraMap O (LetA O n) lam * algebraMap O (LetA O n) c := by
      rw [← map_mul, ← hc, map_natCast]
    have h6 := congrArg (algebraMap (LetA O n) W.EE) h4
    rw [h5] at h
    simp only [map_mul] at h h6
    rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
    have h7 : algebraMap (LetA O n) W.EE letπ ^ m * u ^ m = 1 := by rw [← mul_pow, hπ, one_pow]
    refine ⟨(algebraMap (LetA O n) W.EE (letE i) * algebraMap (LetA O n) W.EE (fun _ => PowerSeries.mk d) +
      algebraMap (LetA O n) W.EE (letE i) * algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) c) * y) * u ^ m, ?_⟩
    linear_combination (algebraMap (LetA O n) W.EE (letE i) * u ^ m) * h + u ^ m * h6 -
      (algebraMap (LetA O n) W.EE (letE i) * e) * h7

end GlobalTheory.RedFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModuleGeneratorReductionStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachModule_generator_reduction : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {k : Type} [Field k] [Algebra O k] (lam : O), Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 ↔ lam ∣ x) → ((PD.p : ℕ) : k) = 0 → ∃ p : ZMod n → (W.EE →+* k⸨X⸩), (∀ i (a : LetA O n), p i (algebraMap (LetA O n) W.EE a) = ((PowerSeries.map (algebraMap O k) (a i) : k⟦X⟧) : k⸨X⸩)) ∧ (∀ i, Function.Surjective (p i)) ∧ ∀ i e, p i e = 0 → ∃ e', algebraMap (LetA O n) W.EE (letE i) * e = algebraMap O W.EE lam * e' := by
  first | exact @GlobalTheory.RedFun.exists_letter_reduction | exact GlobalTheory.RedFun.exists_letter_reduction | (intros; apply GlobalTheory.RedFun.exists_letter_reduction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisation
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem specPhi_coord {Z N C : Type} [CommRing Z] [AddCommGroup N] [Module Z N] [CommRing C]
    (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N) (u : N →ₗ[Z] N)
    (U : Matrix (Fin d) (Fin d) C) (hU : ∀ i j, U i j = φ (b.repr (u (b j)) i)) (t : N) :
    (fun i => φ (b.repr (u t) i)) = U.mulVec (fun i => φ (b.repr t i)) := by
  funext i
  conv_lhs => rw [← b.sum_repr t]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, map_mul, Matrix.mulVec, dotProduct, hU]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem specPhi_coord_smul {Z O N C : Type} [CommRing Z] [CommRing O] [Algebra Z O] [AddCommGroup N]
    [Module O N] [Module Z N] (hs : ∀ (x : Z) (t : N), x • t = algebraMap Z O x • t) [CommRing C]
    (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N) (a : O)
    (U : Matrix (Fin d) (Fin d) C) (hU : ∀ i j, U i j = φ (b.repr (a • b j) i)) (t : N) :
    (fun i => φ (b.repr (a • t) i)) = U.mulVec (fun i => φ (b.repr t i)) := by
  have hlin : ∀ (x : Z) (s : N), a • (x • s) = x • (a • s) := by
    intro x s
    rw [hs, hs, smul_smul, smul_smul, mul_comm]
  let u : N →ₗ[Z] N :=
    { toFun := fun s => a • s
      map_add' := fun x y => smul_add a x y
      map_smul' := fun x s => hlin x s }
  exact specPhi_coord φ b u U hU t

theorem specPhi_generic {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (L : R → Matrix (Fin d) (Fin d) C) (hL0 : L 0 = 0) (hLa : ∀ x y, L (x + y) = L x + L y)
    (hLm : ∀ x y, L (x * y) = L x * L y) (co : ↥T.L.T →+ (Fin d → C))
    (hco : ∀ (a : O) t, co (a • t) = (L (algebraMap O R a)).mulVec (co t)) :
    ∃ Φ : TW R T →+ (Fin d → C), (∀ (r : R) (t : ↥T.L.T), Φ (r ⊗ₜ[O] t) = (L r).mulVec (co t)) ∧
      ∀ (r : R) (z : TW R T), Φ (r • z) = (L r).mulVec (Φ z) := by
  let f : R →+ ↥T.L.T →+ (Fin d → C) :=
    { toFun := fun r =>
        { toFun := fun t => (L r).mulVec (co t)
          map_zero' := by simp
          map_add' := fun x y => by simp [Matrix.mulVec_add] }
      map_zero' := by ext t : 1; simp [hL0]
      map_add' := fun x y => by ext t : 1; simp [hLa, Matrix.add_mulVec] }
  have hf : ∀ (a : O) (r : R) (t : ↥T.L.T), f (a • r) t = f r (a • t) := by
    intro a r t
    show (L (a • r)).mulVec (co t) = (L r).mulVec (co (a • t))
    rw [Algebra.smul_def, mul_comm, hLm, hco, Matrix.mulVec_mulVec]
  refine ⟨TensorProduct.liftAddHom f hf, fun r t => rfl, fun r z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    show (L (r * x)).mulVec (co t) = (L r).mulVec ((L x).mulVec (co t))
    rw [hLm, Matrix.mulVec_mulVec]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, Matrix.mulVec_add]

theorem specPhi_equiv {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (Φ : TW R T →+ (Fin d → C)) (u : R →ₐ[O] R) (g : G) (U : Matrix (Fin d) (Fin d) C)
    (σ : C ≃+* C)
    (h : ∀ (r : R) (t : ↥T.L.T), Φ (u r ⊗ₜ[O] T.actT g t) =
      U.mulVec (fun i => σ (Φ (r ⊗ₜ[O] t) i))) (z : TW R T) :
    Φ (TWact u T g z) = U.mulVec (fun i => σ (Φ z i)) := by
  unfold TWact
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply]
    exact (Matrix.mulVec_zero U).symm
  | tmul r t => exact h r t
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, ← Matrix.mulVec_add]
    congr 1
    funext i
    simp [map_add (f := _)]

theorem specPhi_norm {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d : ℕ}
    (Φ : TW R T →+ (Fin d → C)) (S : AddSubmonoid C)
    (h : ∀ (r : R) (t : ↥T.L.T) i, Φ (r ⊗ₜ[O] t) i ∈ S) (z : TW R T) (i : Fin d) :
    Φ z i ∈ S := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => exact h r t i
  | add x y hx hy => simpa using S.add_mem hx hy

variable {l : ℕ} [Fact l.Prime]


set_option synthInstance.maxHeartbeats 400000 in
theorem specPhi_co (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (h : IsMat K LL T M A)
    {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (hact : IsActC act) :
    ∃ co : ↥T.L.T →+ (Fin d → PadicComplex l), (∀ t i, co t i ∈ (PadicComplexInt l).toSubring) ∧
      (∀ (g : ↥(GK K)) t i, act (g : GQ l) (co t i) = co t i) ∧
      (∀ (a : ↥(OL LL)) (t : ↥T.L.T), co (a • t) = (A a).mulVec (co t)) ∧
      (∀ (g : ↥(GK K)) (t : ↥T.L.T), co (T.actT g t) = (M (g : GQ l)).mulVec (co t)) ∧
      ∀ j, ∃ t, co t = Pi.single j 1 := by
  obtain ⟨b, hM, hA⟩ := h
  letI := zlMod LL T
  let φ : ℤ_[l] →+* PadicComplex l :=
    (algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom
  let co : ↥T.L.T →+ (Fin d → PadicComplex l) :=
    { toFun := fun t i => zC (b.repr t i)
      map_zero' := by funext i; simp [zC]
      map_add' := fun x y => by funext i; simp [zC] }
  refine ⟨co, fun t i => ?_, fun g t i => act_zC hact _ _, fun a t => ?_, fun g t => ?_,
    fun j => ⟨b j, ?_⟩⟩
  · exact (mem_OC _).2 ((norm_zC _).le.trans (PadicInt.norm_le_one _))
  · have hs : ∀ (x : ℤ_[l]) (s : ↥T.L.T), x • s = algebraMap ℤ_[l] ↥(OL LL) x • s :=
      fun x s => rfl
    exact specPhi_coord_smul hs φ b a (A a) (fun i j => hA a i j) t
  · exact specPhi_coord φ b (actTZ LL T g) (M g) (fun i j => hM g i j) t
  · funext i
    show zC (b.repr (b j) i) = (Pi.single j (1 : PadicComplex l) : Fin d → PadicComplex l) i
    rw [b.repr_self]
    by_cases hij : i = j
    · subst hij
      simp [zC]
    · simp [zC, hij]

theorem specPhi_abstract {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) {C : Type} [CommRing C] {d f : ℕ}
    (S : Subring C) (A : O → Matrix (Fin d) (Fin d) C) (M : G → Matrix (Fin d) (Fin d) C)
    (σ : G → C ≃+* C) (u : G → R →ₐ[O] R) (o : Fin f → O) (κ : R → Fin f → C)
    (L : R → Matrix (Fin d) (Fin d) C) (hL : ∀ r, L r = ∑ k, κ r k • A (o k))
    (hL0 : L 0 = 0) (hLa : ∀ x y, L (x + y) = L x + L y)
    (hLm : ∀ x y, L (x * y) = L x * L y) (hal : ∀ a, L (algebraMap O R a) = A a) (hone : A 1 = 1)
    (hκS : ∀ r k, κ r k ∈ S) (hκ : ∀ g r k, κ (u g r) k = σ g (κ r k))
    (co : ↥T.L.T →+ (Fin d → C)) (hS : ∀ t i, co t i ∈ S) (hσ : ∀ g t i, σ g (co t i) = co t i)
    (hcoA : ∀ (a : O) t, co (a • t) = (A a).mulVec (co t))
    (hcoM : ∀ g t, co (T.actT g t) = (M g).mulVec (co t)) :
    ∃ Φ : TW R T →+ (Fin d → C), (∀ (r : R) (z : TW R T), Φ (r • z) = (L r).mulVec (Φ z)) ∧
      (∀ z i, Φ z i ∈ S) ∧
      (∀ g z, Φ (TWact (u g) T g z) = (M g).mulVec (fun i => σ g (Φ z i))) ∧
      ∀ t : ↥T.L.T, Φ ((1 : R) ⊗ₜ[O] t) = co t := by
  obtain ⟨Φ, hΦt, hΦs⟩ := specPhi_generic T L hL0 hLa hLm co (fun a t => by rw [hcoA, hal])
  have hLco : ∀ r t, (L r).mulVec (co t) = ∑ k, κ r k • co (o k • t) := by
    intro r t
    rw [hL, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, hcoA]
  refine ⟨Φ, hΦs, fun z i => specPhi_norm T Φ S.toAddSubmonoid (fun r t i => ?_) z i,
    fun g z => specPhi_equiv T Φ (u g) g (M g) (σ g) (fun r t => ?_) z, fun t => ?_⟩
  · show _ ∈ S
    rw [hΦt, hLco, Finset.sum_apply]
    refine S.sum_mem fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact S.mul_mem (hκS r k) (hS _ i)
  · rw [hΦt, hΦt, hLco, hLco]
    have h1 : ∀ k, co (o k • T.actT g t) = (M g).mulVec (co (o k • t)) := fun k => by
      rw [← map_smul (T.actT g) (o k) t, hcoM]
    have h2 : (fun i => σ g ((∑ k, κ r k • co (o k • t)) i)) =
        ∑ k, κ (u g r) k • co (o k • t) := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hσ, ← hκ]
    rw [h2, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h1, Matrix.mulVec_smul]
  · have h1 : L 1 = 1 := by rw [← map_one (algebraMap O R), hal, hone]
    rw [hΦt, h1, Matrix.one_mulVec]

set_option synthInstance.maxHeartbeats 400000 in
theorem specPhi_thR_alg (LL : FinExt l) (θ : Ainf l →ₐ[ℤ_[l]] OC l) (a : ↥(OL LL)) :
    thR LL θ (algebraMap ↥(OL LL) (RA LL) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a := by
  rw [Algebra.TensorProduct.algebraMap_apply, thR_tmul, map_one]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem exists_specPhi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f n : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (θ : Ainf l →ₐ[ℤ_[l]] OC l), IsMat K LL T M A → IsThetaShift AI n θ → ∃ Φ : TW (RA LL) T →+ (Fin d → PadicComplex l), (∀ (r : RA LL) (z : TW (RA LL) T), Φ (r • z) = (lam o A (thR LL θ r)).mulVec (Φ z)) ∧ (∀ z i, ‖Φ z i‖ ≤ 1) ∧ (∀ (g : ↥(GK K)) (z : TW (RA LL) T), Φ (TWact (gRA AI LL (g : GQ l)) T g z) = (M (g : GQ l)).mulVec (fun i => AI.actC (g : GQ l) (Φ z i))) ∧ ∀ j, ∃ t : ↥T.L.T, Φ ((1 : RA LL) ⊗ₜ[↥(OL LL)] t) = Pi.single j 1 := by
  intro l _ P AI K LL T d f n M A o θ hM hθ
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨co, hS, hσ, hcoA, hcoM, hsingle⟩ := specPhi_co K LL T M A hM hact
  have hmul := lam_mul_of_isMat l K LL T d f M A o hM
  have hL : ∀ r : RA LL, lam o A (thR LL θ r) = ∑ k, kap o (thR LL θ r) k • A (o k) :=
    fun r => rfl
  have hL0 : lam o A (thR LL θ 0) = 0 := by rw [map_zero, lamMul_lam_zero]
  have hLa : ∀ x y : RA LL, lam o A (thR LL θ (x + y)) =
      lam o A (thR LL θ x) + lam o A (thR LL θ y) := fun x y => by
    rw [map_add (f := _), lamMul_lam_add]
  have hLm : ∀ x y : RA LL, lam o A (thR LL θ (x * y)) =
      lam o A (thR LL θ x) * lam o A (thR LL θ y) := fun x y => by
    rw [map_mul, hmul.2.2.2]
  have hal : ∀ a : ↥(OL LL), lam o A (thR LL θ (algebraMap ↥(OL LL) (RA LL) a)) = A a :=
    fun a => by rw [specPhi_thR_alg, hmul.1]; simp
  have hκS : ∀ (r : RA LL) (k : Fin f), kap o (thR LL θ r) k ∈ (PadicComplexInt l).toSubring :=
    fun r k => (mem_OC _).2 (norm_kap_le o _ k)
  have hκ : ∀ (g : ↥(GK K)) (r : RA LL) (k : Fin f),
      kap o (thR LL θ (gRA AI LL (g : GQ l) r)) k = AI.actC (g : GQ l) (kap o (thR LL θ r) k) :=
    fun g r k => kap_thR_gRA AI o hθ _ r k
  have keyA := specPhi_abstract (R := RA LL) T (PadicComplexInt l).toSubring
    A (fun g => M (g : GQ l)) (fun g => AI.actC (g : GQ l)) (fun g => gRA AI LL (g : GQ l)) o
    (fun r k => kap o (thR LL θ r) k) (fun r => lam o A (thR LL θ r)) hL hL0 hLa hLm hal
    hmul.2.1 hκS hκ co hS hσ hcoA hcoM
  obtain ⟨Φ, hΦs, hΦS, hΦg, hΦ1⟩ := keyA
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · exact hΦs
  · intro z i
    exact (mem_OC _).1 (hΦS z i)
  · intro g z
    convert hΦg g z using 3
  · intro j
    obtain ⟨t, ht⟩ := hsingle j
    exact ⟨t, (hΦ1 t).trans ht⟩

end GlobalTheory.Cyc.Decomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfTensorLatticeSpecialisationStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_tensor_lattice_specialisation : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f n : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (θ : Ainf l →ₐ[ℤ_[l]] OC l), IsMat K LL T M A → IsThetaShift AI n θ → ∃ Φ : TW (RA LL) T →+ (Fin d → PadicComplex l), (∀ (r : RA LL) (z : TW (RA LL) T), Φ (r • z) = (lam o A (thR LL θ r)).mulVec (Φ z)) ∧ (∀ z i, ‖Φ z i‖ ≤ 1) ∧ (∀ (g : ↥(GK K)) (z : TW (RA LL) T), Φ (TWact (gRA AI LL (g : GQ l)) T g z) = (M (g : GQ l)).mulVec (fun i => AI.actC (g : GQ l) (Φ z i))) ∧ ∀ j, ∃ t : ↥T.L.T, Φ ((1 : RA LL) ⊗ₜ[↥(OL LL)] t) = Pi.single j 1 := by
  exact @GlobalTheory.Cyc.Decomp.exists_specPhi
end
end
