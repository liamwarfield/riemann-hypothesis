module

public import Formalism.QuotientMetricDivisors.ProdFormula
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SelectionLemmas
public import Formalism.LogFactorialBounds.LogFactorialProofs.PrimeSum
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.LogProductFormula

@[expose] public section

section -- merged from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ValuationRepresentative

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cO_apply (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem cO_cO (x : 𝓞 K) : cO K (cO K x) = x := by
  apply RingOfIntegers.ext
  rw [cO_apply, cO_apply, star_star]

theorem map_cO_map_cO (I : Ideal (𝓞 K)) : (I.map (cO K)).map (cO K) = I := by
  ext y
  simp only [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    rwa [cO_cO]
  · intro hy
    exact ⟨cO K y, ⟨y, hy, rfl⟩, cO_cO y⟩

theorem conjPl_conjPl (w : HeightOneSpectrum (𝓞 K)) : conjPl (conjPl w) = w := HeightOneSpectrum.ext (map_cO_map_cO w.asIdeal)

theorem map_cO_le_iff (I J : Ideal (𝓞 K)) : I.map (cO K) ≤ J.map (cO K) ↔ I ≤ J := by
  constructor
  · intro h
    have h2 := Ideal.map_mono (f := cO K) h
    rwa [map_cO_map_cO, map_cO_map_cO] at h2
  · intro h
    exact Ideal.map_mono (f := cO K) h

theorem dvd_map_iff (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (n : ℕ) :
    (v.asIdeal.map (cO K)) ^ n ∣ J.map (cO K) ↔ v.asIdeal ^ n ∣ J := by
  rw [← Ideal.map_pow, Ideal.dvd_iff_le, Ideal.dvd_iff_le, map_cO_le_iff]

theorem count_map (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (hJ : J ≠ 0) :
    FractionalIdeal.count K (conjPl v) ((J.map (cO K) : Ideal (𝓞 K)) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
    FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  have hJ' : J.map (cO K) ≠ 0 := fun h =>
    hJ ((Ideal.map_eq_bot_iff_of_injective (cO K).injective).mp h)
  rw [FractionalIdeal.count_coe K (conjPl v) hJ', FractionalIdeal.count_coe K v hJ]
  congr 1
  apply eq_of_forall_le_iff
  intro n
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ')
      (Associates.irreducible_mk.mpr (conjPl v).irreducible),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
      (Associates.irreducible_mk.mpr v.irreducible),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Associates.mk_le_mk_iff_dvd]
  exact dvd_map_iff v J n

theorem vw_zero (w : HeightOneSpectrum (𝓞 K)) : vw w (0 : K) = 0 := by
  simp only [vw, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]

theorem vw_mul (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) b ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul K w h1 h2

theorem vw_inv (w : HeightOneSpectrum (𝓞 K)) (a : K) : vw w a⁻¹ = - vw w a := by
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

theorem vw_one (w : HeightOneSpectrum (𝓞 K)) : vw w (1 : K) = 0 := by
  simp only [vw]
  rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem vw_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (x : K) = FractionalIdeal.count K w
      ((Ideal.span {x} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  rw [FractionalIdeal.coeIdeal_span_singleton]
  rfl

theorem vw_int_nonneg (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) : 0 ≤ vw w (x : K) := by
  rw [vw_int]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_star_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (star (x : K)) = vw (conjPl w) (x : K) := by
  by_cases hx : x = 0
  · subst hx
    simp [vw_zero]
  · have hJ : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by
      rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have key := count_map (conjPl w) (Ideal.span {x}) hJ
    rw [conjPl_conjPl] at key
    rw [← cO_apply, vw_int, vw_int, ← key, Ideal.map_span, Set.image_singleton]

private theorem vw_div (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a / b) = vw w a - vw w b := by
  rw [div_eq_mul_inv, vw_mul w a b⁻¹ ha (inv_ne_zero hb), vw_inv, sub_eq_add_neg]

theorem vw_star (w : HeightOneSpectrum (𝓞 K)) (a : K) :
    vw w (star a) = vw (conjPl w) a := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have e : ∀ z : 𝓞 K, algebraMap (𝓞 K) K z = (z : K) := fun _ => rfl
  have hy0 : (y : K) ≠ 0 := by
    rw [Ne, ← e, ← map_zero (algebraMap (𝓞 K) K)]
    exact (IsFractionRing.injective (𝓞 K) K).ne (nonZeroDivisors.ne_zero hy)
  rw [e, e]
  by_cases hx0 : (x : K) = 0
  · rw [hx0, zero_div, star_zero, vw_zero, vw_zero]
  · rw [star_div₀, vw_div w _ _ (star_ne_zero.mpr hx0) (star_ne_zero.mpr hy0),
      vw_div _ _ _ hx0 hy0, vw_star_int, vw_star_int]

theorem absNorm_map_ringEquiv {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S] (g : S ≃+* S) (I : Ideal S) :
    Ideal.absNorm (I.map g) = Ideal.absNorm I := by
  by_cases hI : I = ⊥
  · simp [hI]
  have hI' : I.map g ≠ ⊥ := fun h =>
    hI ((Ideal.map_eq_bot_iff_of_injective g.injective).mp h)
  rw [Ideal.absNorm_of_ne_bot hI', Ideal.absNorm_of_ne_bot hI, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map g) g rfl).toEquiv).symm

theorem lw_conjPl (w : HeightOneSpectrum (𝓞 K)) : lw (conjPl w) = lw w := by
  unfold lw
  rw [show (conjPl w).asIdeal = w.asIdeal.map (cO K) from rfl, absNorm_map_ringEquiv]

theorem gramR_eq {K : Type} [Field K] [StarRing K] {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) :
    gramR Γ e = ((Matrix.of e).map star * Γ * (Matrix.of e).transpose).det := by
  unfold gramR
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end ValuationRepresentative

open ValuationRepresentative

theorem valuation_basic_properties : ValBasic := by
  intro K _ _ _ w
  exact ⟨fun a b ha hb => vw_mul w a b ha hb, vw_star w, lw_conjPl w, conjPl_conjPl w,
    vw_one w, vw_inv w, vw_int_nonneg w⟩

theorem gram_matrix_change : GramChange := by
  intro K _ _ D m Γ e γ
  have h : Matrix.of (fun i => ∑ k, γ k i • e k) = γᵀ * Matrix.of e := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  have hm : (γᵀ * Matrix.of e).map star = γᵀ.map star * (Matrix.of e).map star := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      star_sum, star_mul']
  have hd : (γᵀ.map star).det = star γ.det := Matrix.det_conjTranspose γ
  have hr : γᵀ.map star * (Matrix.of e).map star * Γ * ((Matrix.of e)ᵀ * γ) =
      γᵀ.map star * ((Matrix.of e).map star * Γ * (Matrix.of e)ᵀ) * γ := by
    simp only [Matrix.mul_assoc]
  rw [gramR_eq, gramR_eq, h, hm, Matrix.transpose_mul, Matrix.transpose_transpose, hr,
    Matrix.det_mul, Matrix.det_mul, hd]
  ring

theorem finite_sum_conjugation : FinsumConj := by
  intro K _ _ _ f
  exact finsum_comp_equiv (Function.Involutive.toPerm _ (fun w => conjPl_conjPl w))

end Formalism.DivisionValues
end
end

section -- merged from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ReductionFirst

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def Tw (w : HeightOneSpectrum (𝓞 K)) : Submonoid (𝓞 K) where
  carrier := {s | s ∉ w.asIdeal ∧ cO K s ∉ w.asIdeal}
  one_mem' := by
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    exact ⟨h1, by simpa using h1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha h, hb h]
    · rw [map_mul] at h
      rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha' h, hb' h]

theorem cO_coe (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem cO_cO (x : 𝓞 K) : cO K (cO K x) = x := by
  apply RingOfIntegers.ext
  rw [cO_coe, cO_coe, star_star]

theorem cO_mem_Tw {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : cO K s ∈ Tw w :=
  ⟨hs.2, by rw [cO_cO]; exact hs.1⟩

theorem hcompl_le_Tw (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ Tw w := by
  refine Submonoid.closure_le.2 ?_
  rintro s ⟨hs, hs'⟩
  exact ⟨hs, hs' (cO K s) rfl⟩

theorem smul_coe {m : Type*} (r : 𝓞 K) (v : m → K) : r • v = (r : K) • v :=
  (algebraMap_smul K r v).symm

theorem vw_mul (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 ha)
      (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hb)]

theorem vw_pow (w : HeightOneSpectrum (𝓞 K)) (a : K) (m : ℕ) :
    vw w (a ^ m) = (m : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

theorem vw_int_nonneg (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) : 0 ≤ vw w (r : K) := by
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_unit (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (hr : r ∉ w.asIdeal) :
    vw w (r : K) = 0 := by
  classical
  have hr0 : r ≠ 0 := fun h => hr (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {r} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr0
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w hJ]
  have h2 : ¬ w.asIdeal ∣ Ideal.span {r} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hr
  have h3 := mt (Associates.count_ne_zero_iff_dvd hJ w.irreducible).1 h2
  rw [not_not] at h3
  simp [h3]

theorem Tw_ne_zero {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : (s : K) ≠ 0 := by
  intro h
  apply hs.1
  have : s = 0 := RingOfIntegers.ext (by simpa using h)
  rw [this]; exact w.asIdeal.zero_mem

theorem main {n D : ℕ} (H : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin D) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : M.FG) (l g : ℕ) (hl : 0 < l)
    (hdual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H) M, ((l : 𝓞 K) ^ g) • x ∈ M)
    (w : HeightOneSpectrum (𝓞 K)) (e : Fin D → Fin D → K) (he : IsLocBasis (matLat P M) w e) :
    vw w (gramR (quotGram P H) e) ≤ (g : ℤ) * (D : ℤ) * vw w (l : K) :=
  _root_.UpperTheory.Reformulated.B.SelectionLemmas.main H P M hM l g hl hdual w e he

end ReductionFirst

theorem reduction_lemma_first : LemmaRa := by
  intro K _ _ _ _ K0 _ v0 _ n D H _ _ P _ M hM l g hl hdual w e he
  exact ReductionFirst.main H P M hM.fg l g hl hdual w e he

end Formalism.DivisionValues
end
end

section -- merged from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

namespace SemilocalBasisHermitianTwistDivisors

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma mem_loc_iff' (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔
      ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal, s • x ∈ M :=
  Iff.rfl

lemma mem_hcompl (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (h1 : x ∉ w.asIdeal)
    (h2 : x ∉ (conjPl w).asIdeal) : x ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal := by
  apply Submonoid.subset_closure
  refine ⟨h1, fun t ht htw => h2 ?_⟩
  have hct : cO K t = x := by
    apply RingOfIntegers.ext
    change star (t : K) = (x : K)
    have ht' : (t : K) = star (x : K) := ht
    rw [ht', star_star]
  rw [← hct]
  exact Ideal.mem_map_of_mem _ htw

lemma hcompl_le (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ nonZeroDivisors (𝓞 K) := by
  apply Submonoid.closure_le.mpr
  intro s hs
  apply mem_nonZeroDivisors_of_ne_zero
  rintro rfl
  exact hs.1 w.asIdeal.zero_mem

abbrev A (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (hcompl_le w)

lemma mem_A (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ A w ↔ ∃ (a s : 𝓞 K) (_ : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

lemma algebraMap_ne_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hcompl_le w hs)

lemma primes_finite (w : HeightOneSpectrum (𝓞 K)) :
    {P : Ideal (A w) | P.IsPrime}.Finite := by
  apply ((({⊥, w.asIdeal, (conjPl w).asIdeal} : Set (Ideal (𝓞 K))).toFinite.image
    (Ideal.map (algebraMap (𝓞 K) (A w))))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (A w) P).mp hP'
  refine ⟨P.comap (algebraMap (𝓞 K) (A w)), ?_,
    IsLocalization.map_under (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal) (A w) P⟩
  set Q := P.comap (algebraMap (𝓞 K) (A w))
  have hsub : (Q : Set (𝓞 K)) ⊆ (w.asIdeal : Set (𝓞 K)) ∪ ((conjPl w).asIdeal : Set (𝓞 K)) := by
    intro x hx
    by_contra hn
    simp only [Set.mem_union, SetLike.mem_coe, not_or] at hn
    exact Set.disjoint_left.mp hdisj (mem_hcompl w x hn.1 hn.2) hx
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  rcases Ideal.subset_union.mp hsub with h | h
  · exact Or.inr (Or.inl (hmax.eq_of_le w.isPrime.ne_top h))
  · exact Or.inr (Or.inr (hmax.eq_of_le (conjPl w).isPrime.ne_top h))

lemma mem_loc_iff_span (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal M ↔ x ∈ Submodule.span (A w) (M : Set (Fin d → K)) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 := algebraMap_ne_zero w hs
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ A w := (mem_A w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : A w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact (mem_loc_iff' w M y).mpr ⟨1, one_mem _, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := (mem_loc_iff' w M y).mp hy
      obtain ⟨r, t, ht, hat⟩ := (mem_A w a).mp a.2
      refine (mem_loc_iff' w M _).mpr ⟨t * s, mul_mem ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero w ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

end SemilocalBasisHermitianTwistDivisors


open SemilocalBasisHermitianTwistDivisors in
theorem semilocal_basis_exists :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
      (L : Submodule (𝓞 K) (Fin d → K)), Submodule.IsFullLattice K L →
      ∀ w : HeightOneSpectrum (𝓞 K), ∃ f : Fin d → Fin d → K, IsLocBasis L w f := by
  intro K _ _ _ d L hL w
  have : IsDedekindDomain (A w) :=
    IsLocalization.isDedekindDomain (𝓞 K) (hcompl_le w) (A w)
  have : IsPrincipalIdealRing (A w) := IsPrincipalIdealRing.of_finite_primes (primes_finite w)
  set N : Submodule (A w) (Fin d → K) := Submodule.span (A w) (L : Set (Fin d → K)) with hN
  have : Module.Finite (A w) N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    refine ⟨s, ?_⟩
    rw [hN, ← hs, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (A w) N := inferInstance
  let b := Module.Free.chooseBasis (A w) N
  let v : Module.Free.ChooseBasisIndex (A w) N → Fin d → K := fun i => (b i : Fin d → K)
  have hliA : LinearIndependent (A w) v := b.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing (A w) K).mp hliA
  have hspanA : Submodule.span (A w) (Set.range v) = N := by
    have : Set.range v = N.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span (A w) (Set.range v) := by
      rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars (A w) K _ hxN
  let bK : Basis _ K (Fin d → K) := Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (A w) N) = d := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨v ∘ e.symm, hli.comp _ e.symm.injective, ?_⟩
  ext x
  rw [mem_loc_iff_span, mem_loc_iff_span, Submodule.span_span_of_tower, EquivLike.range_comp,
    hspanA]

end Formalism.DivisionValues
end
end

section -- merged from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsSum
open Finset

noncomputable section

namespace Formalism.DivisionValues

theorem divisor_bounds_sum : BoundsSum := by
  intro Pl J _ S D hD lcvR logκ LG E3 lcvM L E1 E2 l ell vG g I Ic jT F err Jx η hl h0 hvG hLG hL
    hI hjT hE1 hE2 hE3
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : ∑ j, lcvM j ≤ (D : ℝ) * ∑ j, L j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have := (div_le_iff₀ hDr).1 (hL j)
      linarith
  have h2 : ∑ w ∈ S, l w * vG w ≤ (D : ℝ) * LG := by
    calc ∑ w ∈ S, l w * vG w ≤ ∑ w ∈ S, (D : ℝ) * (l w * g w) :=
          Finset.sum_le_sum fun w hw => by
            have := mul_le_mul_of_nonneg_left (hvG w hw) (hl w)
            linarith
      _ = (D : ℝ) * ∑ w ∈ S, l w * g w := by rw [Finset.mul_sum]
      _ ≤ (D : ℝ) * LG := mul_le_mul_of_nonneg_left hLG hDr.le
  have f1 : ∑ w ∈ S, l w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) =
      ∑ w ∈ S, l w * vG w + ∑ w ∈ S, l w * ∑ j, (I w j + Ic w j) +
        ∑ w ∈ S, l w * ∑ j, jT w j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_add_distrib]
    ring
  have f4 : ∑ w ∈ S, l w * ∑ j, (I w j + Ic w j) ≤
      (D : ℝ) * 2 * ∑ w ∈ S, l w * ∑ j, F w j + (D : ℝ) * ∑ w ∈ S, l w * ∑ j, err w j +
        (D : ℝ) * ∑ w ∈ S, l w * (2 / ell w ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have h := mul_le_mul_of_nonneg_left (hI w hw) (hl w)
    have e : ∑ j, (2 * F w j + err w j) = 2 * ∑ j, F w j + ∑ j, err w j := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [e] at h
    linarith
  have f6 : ∑ w ∈ S, l w * ∑ j, jT w j ≤
      (D : ℝ) * ∑ w ∈ S, l w * ∑ j, Jx w j + ∑ w ∈ S, l w * ∑ j, η w j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have h : ∑ j, jT w j ≤ (D : ℝ) * ∑ j, Jx w j + ∑ j, η w j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by have := hjT w hw j; linarith
    have := mul_le_mul_of_nonneg_left h (hl w)
    linarith
  have eswap : ∀ f : Pl → J → ℝ, ∑ j, ∑ w ∈ S, l w * f w j = ∑ w ∈ S, l w * ∑ j, f w j := by
    intro f
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have f8 : ∑ w ∈ S, l w * ∑ j, err w j + ∑ w ∈ S, l w * ∑ j, Jx w j ≤ ∑ j, E1 j := by
    rw [← eswap, ← eswap, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by
      refine le_trans (le_of_eq ?_) (hE1 j)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
  have f9 : ∑ w ∈ S, l w * ∑ j, η w j ≤ (D : ℝ) * ∑ j, E2 j := by
    rw [← eswap, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have h := hE2 j
      rw [← Finset.sum_div] at h
      have := (div_le_iff₀ hDr).1 h
      linarith
  have f10 : (D : ℝ) * ∑ w ∈ S, l w * (2 / ell w ^ 2) ≤ (D : ℝ) * E3 :=
    mul_le_mul_of_nonneg_left hE3 hDr.le
  have f11 : ∑ j, (E1 j + E2 j) = ∑ j, E1 j + ∑ j, E2 j := Finset.sum_add_distrib
  have eF := eswap F
  rw [div_le_iff₀ hDr]
  have hD0 : (0 : ℝ) ≤ D := hDr.le
  nlinarith [h0, h1, h2, f1, f4, f6, f8, f9, f10, f11, eF, mul_le_mul_of_nonneg_left f8 hD0]

end Formalism.DivisionValues
end
end

section -- merged from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.WeightedPlaceLogSum
open Finset NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

namespace place_log_sum

end place_log_sum

theorem prime_log_sum_bound : PrimeLogSum := by
  intro Y hY s hs
  have hn : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hnR : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn
  have hfl : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  calc ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log (p : ℝ) / (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
        · intro p _ _
          exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ ≤ Real.log (⌊Y⌋₊ : ℝ) + Real.log 4 := Formalism.LogFactorialBounds.sum_primesLE_log_div_le _ hn
    _ ≤ Real.log Y + Real.log 4 := by
        have := Real.log_le_log hnR hfl
        linarith

namespace place_log_sum

end place_log_sum

namespace place_log_sum

end place_log_sum

end Formalism.DivisionValues
end
end

section -- merged from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjTransposeEqOfPosDef
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace R0

variable {K : Type} [Field K] [StarRing K]

theorem map_inv_field {F : Type} [Field F] (f : K →+* F) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : A⁻¹.map f = (A.map f)⁻¹ := by
  have hdet : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ f.map_zero f.map_one]
  · have h' : ¬ IsUnit (A.map f).det := by
      rw [hdet, isUnit_iff_ne_zero, map_ne_zero f]
      rw [isUnit_iff_ne_zero] at h
      exact h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      Matrix.map_zero _ f.map_zero]

theorem conjTranspose_map (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a))
    {m n : Type} (A : Matrix m n K) : Aᴴ.map σ = (A.map σ)ᴴ := by
  ext i j
  rw [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, Matrix.map_apply, hσ]
  rfl

theorem conjTranspose_eq_of_posDef [NumberField K] (v0 : InfinitePlace K) (hv0 : IsConjAt v0)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : (H.map v0.embedding).PosDef) : Hᴴ = H := by
  have h1 := conjTranspose_map v0.embedding hv0 H
  have h2 : (H.map v0.embedding)ᴴ = H.map v0.embedding := hH.isHermitian
  ext i j
  have h3 := congrFun (congrFun (h1.trans h2) i) j
  simp only [Matrix.map_apply] at h3
  exact v0.embedding.injective h3

theorem gramMat_conjTranspose {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K) (hΓ : Γᴴ = Γ)
    (e : Fin m → Fin D → K) :
    (Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b))ᴴ =
      Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  have h1 : star (star (e j) ⬝ᵥ Γ.mulVec (e i)) = star (e i) ⬝ᵥ Γᴴ.mulVec (e j) := by
    simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Matrix.conjTranspose_apply,
      Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  rw [h1, hΓ]

end R0

open R0 in
theorem gram_determinant_quotient_metric : GramDeterminantQuotientMetric := by
  intro K _ _ _ _ K0 hCM v0 hv0 n D H hK0 hpos P hsurj XQ hQ e
  have hH : Hᴴ = H := conjTranspose_eq_of_posDef v0 hv0 H (hpos v0)
  have hΓ : (quotGram P H)ᴴ = quotGram P H := by
    unfold quotGram
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, hH, Matrix.mul_assoc]
  have hΓmap : (quotGram P H).map v0.embedding = ((XQ v0)⁻¹)ᴴ * (XQ v0)⁻¹ := by
    rw [(hQ v0).2]
    unfold quotGram
    rw [map_inv_field, Matrix.map_mul, Matrix.map_mul, map_inv_field, conjTranspose_map v0.embedding hv0]
  refine ⟨?_, ?_⟩
  · unfold gramR
    rw [← Matrix.det_conjTranspose, gramMat_conjTranspose _ hΓ e]
  · unfold gramR gram Formalism.HN.gramPl
    rw [RingHom.map_det]
    congr 1
    ext a c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Formalism.HermitianLatticesTheory.majAt,
      Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
    have hY : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (x y : Fin D → ℂ),
        ∑ i, star ((Y *ᵥ x) i) * (Y *ᵥ y) i = ∑ i, star (x i) * ((Yᴴ * Y) *ᵥ y) i := by
      intro Y x y
      have e1 : ∑ i, star ((Y *ᵥ x) i) * (Y *ᵥ y) i = star (Y *ᵥ x) ⬝ᵥ (Y *ᵥ y) := rfl
      have e2 : ∑ i, star (x i) * ((Yᴴ * Y) *ᵥ y) i = star x ⬝ᵥ ((Yᴴ * Y) *ᵥ y) := rfl
      rw [e1, e2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    rw [hY, ← hΓmap]
    have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Matrix.map_apply, hv0']
    rfl

end Formalism.DivisionValues
end
end

section -- merged from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DeterminantCauchySchwarz
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Formalism.DivisionValues

lemma one_le_det_one_add {m : Type*} [Fintype m] [DecidableEq m] {Z : Matrix m m ℂ}
    (hZ : Z.PosSemidef) : (1 : ℂ) ≤ (1 + Z).det := by
  have hspec := hZ.1.spectral_theorem
  have hUU : (hZ.1.eigenvectorUnitary : Matrix m m ℂ) * star (hZ.1.eigenvectorUnitary : Matrix m m ℂ) = 1 := by
    simp
  have hdet : ∀ x : Matrix m m ℂ, ((hZ.1.eigenvectorUnitary : Matrix m m ℂ) * x *
      star (hZ.1.eigenvectorUnitary : Matrix m m ℂ)).det = x.det := by
    intro x
    rw [det_mul, det_mul, mul_comm (det (hZ.1.eigenvectorUnitary : Matrix m m ℂ)), mul_assoc, ← det_mul, hUU,
      det_one, mul_one]
  have key : 1 + Z = (Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) hZ.1.eigenvectorUnitary)
      (1 + diagonal (RCLike.ofReal ∘ hZ.1.eigenvalues)) := by
    rw [map_add (f := _), map_one, ← hspec]
  rw [key, Unitary.conjStarAlgAut_apply, hdet, ← diagonal_one, diagonal_add, det_diagonal]
  have hev := hZ.eigenvalues_nonneg
  have hprod : ∏ i, ((1 : ℂ) + (RCLike.ofReal ∘ hZ.1.eigenvalues) i) =
      ((∏ i, (1 + hZ.1.eigenvalues i) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, ← Complex.ofReal_one, Complex.real_le_real]
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => by linarith [hev i])

lemma det_le_det_add {m : Type*} [Fintype m] [DecidableEq m] {X Y : Matrix m m ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : X.det ≤ (X + Y).det := by
  by_cases hXu : IsUnit X
  · have hX0 : (0 : Matrix m m ℂ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
    have hSS : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X hX0
    have hS0 : (0 : Matrix m m ℂ) ≤ CFC.sqrt X := CFC.sqrt_nonneg X
    set S := CFC.sqrt X with hSdef
    have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hS0
    have hSh : Sᴴ = S := hSpsd.1
    have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hSS ▸ hXu)
    have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
    have h1 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
    have h2 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
    have hTh : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSh]
    have hZ : ((S⁻¹)ᴴ * Y * S⁻¹).PosSemidef := hY.conjTranspose_mul_mul_same _
    have hmid : S * (S⁻¹ * Y * S⁻¹) * S = Y := by
      rw [← mul_assoc, ← mul_assoc, h1, one_mul, mul_assoc, h2, mul_one]
    have hsum : X + Y = S * (1 + (S⁻¹)ᴴ * Y * S⁻¹) * S := by
      rw [hTh, mul_add, add_mul, mul_one, hSS, hmid]
    have hdX : X.det = S.det * S.det := by rw [← hSS, det_mul]
    rw [hsum, det_mul, det_mul]
    have e : S.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det * S.det = X.det * (1 + (S⁻¹)ᴴ * Y * S⁻¹).det := by
      rw [hdX]; ring
    rw [e]
    have hone := one_le_det_one_add hZ
    have hXd : 0 ≤ X.det := hX.det_nonneg
    have := mul_le_mul_of_nonneg_left hone hXd
    simpa using this
  · have hd : X.det = 0 := by
      by_contra h
      exact hXu ((Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr h))
    rw [hd]
    exact (hX.add hY).det_nonneg

theorem determinant_cauchy_schwarz : DetCS := by
  intro n D Hc hHc A B
  have hHh : Hcᴴ = Hc := hHc.1
  have hPpsd : (A * Hc * Aᴴ).PosSemidef := hHc.posSemidef.mul_mul_conjTranspose_same A
  set P := A * Hc * Aᴴ with hP
  set Q := A * Hc * Bᴴ with hQ
  set R := B * Hc * Bᴴ with hR
  by_cases hPu : IsUnit P
  · have hPpd : P.PosDef := (hPpsd.posDef_iff_isUnit).mpr hPu
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
    have hPinv : (P⁻¹).PosSemidef := hPpd.inv.posSemidef
    have hPih : (P⁻¹)ᴴ = P⁻¹ := hPinv.1
    have hQh : Qᴴ = B * Hc * Aᴴ := by
      rw [hQ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hHh, Matrix.mul_assoc]
    set K := B - Qᴴ * P⁻¹ * A with hK
    have hKpsd : (K * Hc * Kᴴ).PosSemidef := hHc.posSemidef.mul_mul_conjTranspose_same K
    have hXpsd : (Qᴴ * P⁻¹ * Q).PosSemidef := hPinv.conjTranspose_mul_mul_same Q
    have hKh : Kᴴ = Bᴴ - Aᴴ * P⁻¹ * Q := by
      rw [hK, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPih]
      simp only [Matrix.mul_assoc]
    have r1 : B * (Hc * Bᴴ) = R := by rw [hR, Matrix.mul_assoc]
    have r2 : ∀ X : Matrix (Fin D) (Fin D) ℂ, B * (Hc * (Aᴴ * X)) = Qᴴ * X := by
      intro X; rw [hQh]; simp only [Matrix.mul_assoc]
    have r3 : A * (Hc * Bᴴ) = Q := by rw [hQ, Matrix.mul_assoc]
    have r4 : ∀ X : Matrix (Fin D) (Fin D) ℂ, A * (Hc * (Aᴴ * X)) = P * X := by
      intro X; rw [hP]; simp only [Matrix.mul_assoc]
    have r5 : ∀ X : Matrix (Fin D) (Fin D) ℂ, P⁻¹ * (P * X) = X := by
      intro X; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet, one_mul]
    have hKK : K * Hc * Kᴴ = R - Qᴴ * P⁻¹ * Q := by
      rw [hKh, hK]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      rw [r2, r3, r4, r5, r1]
      abel
    have hsplit : R = Qᴴ * P⁻¹ * Q + K * Hc * Kᴴ := by rw [hKK]; abel
    have hle := det_le_det_add hXpsd hKpsd
    rw [← hsplit, det_mul, det_mul, det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hle
    obtain ⟨hpre, hpim⟩ := Complex.lt_def.mp hPpd.det_pos
    have key : ∀ pr : ℝ, star Q.det * (pr : ℂ)⁻¹ * Q.det = ((‖Q.det‖ ^ 2 / pr : ℝ) : ℂ) := by
      intro pr
      rw [mul_right_comm, Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    have hpeq : P.det = ((P.det.re : ℝ) : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; simpa using hpim.symm)
    rw [hpeq, key] at hle
    have h2 := (Complex.le_def.mp hle).1
    rw [Complex.ofReal_re] at h2
    have hpre' : 0 < P.det.re := by simpa using hpre
    rw [div_le_iff₀ hpre'] at h2
    rw [mul_comm]
    exact h2
  · have hd : P.det = 0 := by
      by_contra h
      exact hPu ((Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr h))
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    have hw : v ᵥ* A = 0 := by
      by_contra hw
      have hsw : star (v ᵥ* A) ≠ 0 := star_ne_zero.mpr hw
      have hpos := hHc.dotProduct_mulVec_pos hsw
      have h0 : star (star (v ᵥ* A)) ⬝ᵥ (Hc *ᵥ star (v ᵥ* A)) = 0 := by
        rw [star_star]
        have h00 : (v ᵥ* P) ⬝ᵥ star v = 0 := by rw [hv, zero_dotProduct]
        rw [hP, ← vecMul_vecMul, ← vecMul_vecMul, ← dotProduct_mulVec, mulVec_conjTranspose, star_star,
          ← dotProduct_mulVec] at h00
        exact h00
      rw [h0] at hpos
      exact lt_irrefl _ hpos
    have hq : Q.det = 0 := by
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨v, hv0, ?_⟩
      rw [hQ, ← vecMul_vecMul, ← vecMul_vecMul, hw, zero_vecMul, zero_vecMul]
    rw [hq, hd]
    simp

end Formalism.DivisionValues
end
end
