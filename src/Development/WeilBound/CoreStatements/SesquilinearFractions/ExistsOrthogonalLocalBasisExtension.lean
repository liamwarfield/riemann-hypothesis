module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.DBlock
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DOkBasis
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsLocalBasisStatement

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.AlgebraMapIntegralCoeffsRaw
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsCommonDenominatorCoeffs
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.DCompl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def orthogonalFamilyAlt (D : Datum H) {p : ℕ} (x' : Fin p → D.La) : Submodule (𝓞 E) D.La where
  carrier := {y | ∀ a, sesq D (x' a) y = 0}
  add_mem' := by
    intro y y' hy hy' a
    rw [(sesq_sesquilinear_properties D).2.2.1, hy a, hy' a, add_zero]
  zero_mem' := by
    intro a
    have := (sesq_sesquilinear_properties D).2.2.2.2.1 0 (x' a) 0
    simpa using this
  smul_mem' := by
    intro c y hy a
    rw [(sesq_sesquilinear_properties D).2.2.2.2.1, hy a, mul_zero]

theorem nsmul_injective_lattice (D : Datum H) {m : ℕ} (hm : m ≠ 0) {y y' : D.La} (h : m • y = m • y') : y = y' := by
  haveI := D.fin
  haveI := D.proj
  have hm' : (m : 𝓞 E) ≠ 0 := by exact_mod_cast hm
  have h' : (m : 𝓞 E) • y = (m : 𝓞 E) • y' := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact h
  exact smul_right_injective _ hm' h'

theorem padic_norm_sesq_le (D : Datum H) (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]) (y y' : D.La) :
    ‖j (sesq D y y')‖ ≤ Real.exp (-logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) := by
  have hinj : Function.Injective (j.comp (algebraMap (𝓞 E) E)) :=
    j.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 E) E)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨a, ha, ha0, -, hL⟩ := GlobalTheory.T.padic_logIdeal_max_element E ℓ (j.comp (algebraMap (𝓞 E) E)) _ hinj hne
  have hca : (j.comp (algebraMap (𝓞 E) E)) a = j (a : E) := rfl
  have hja : 0 < ‖j (a : E)‖ := by
    rw [← hca]
    exact norm_pos_iff.mpr ((map_ne_zero_iff _ hinj).mpr ha0)
  rw [hL, hca, Real.exp_neg, Real.exp_log hja]
  obtain ⟨b, hb⟩ := (sesq_sesquilinear_properties D).2.2.2.2.2.2 a ha y y'
  have hb1 : ‖j (b : E)‖ ≤ 1 :=
    (GlobalTheory.T.padic_integral_iff_denominator E ℓ (b : E)).mpr ⟨1, b, Nat.Prime.not_dvd_one ℓ.prop, by simp⟩ j
  have hm : ‖j (a : E)‖ * ‖j (sesq D y y')‖ ≤ 1 := by
    rw [← norm_mul, ← map_mul, hb]
    exact hb1
  calc ‖j (sesq D y y')‖ = ‖j (a : E)‖⁻¹ * (‖j (a : E)‖ * ‖j (sesq D y y')‖) := by
        field_simp
    _ ≤ ‖j (a : E)‖⁻¹ * 1 := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hja.le)
    _ = ‖j (a : E)‖⁻¹ := mul_one _

def pairingVector (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (y : D.La) : Fin p → E := fun b => sesq D (x' b) y

def projectionCoeffs (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (y : D.La) : Fin p → E :=
  (gramE D x')⁻¹ *ᵥ pairingVector D x' y

theorem padic_norm_projectionCoeffs_le (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (ℓ : Nat.Primes) (hdet : (gramE D x').det ≠ 0)
    (hlog : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) (y : D.La) (a : Fin p)
    (j : E →+* ℂ_[ℓ]) : ‖j (projectionCoeffs D x' y a)‖ ≤ 1 := by
  classical
  set R := Real.exp (-logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hdetn : ‖j (gramE D x').det‖ = R ^ p := by
    have h0 : 0 < ‖j (gramE D x').det‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr hdet)
    rw [← Real.exp_log h0, hlog j, hR, ← Real.exp_nat_mul]
    congr 1
    ring
  have he : projectionCoeffs D x' y a =
      (gramE D x').det⁻¹ * ((gramE D x').updateCol a (pairingVector D x' y)).det := by
    rw [projectionCoeffs, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec,
      ← Matrix.cramer_eq_adjugate_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply]
  have hb : ‖j ((gramE D x').updateCol a (pairingVector D x' y)).det‖ ≤ R ^ p := by
    rw [RingHom.map_det]
    have := GlobalTheory.T.ultrametric_det_norm_le ℂ_[ℓ] (Fin p) (j.mapMatrix ((gramE D x').updateCol a (pairingVector D x' y)))
      R hR0.le (fun b c => by
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply]
        split_ifs
        · exact padic_norm_sesq_le D ℓ j _ _
        · simpa [gramE] using padic_norm_sesq_le D ℓ j (x' b) (x' c))
    simpa using this
  rw [he, map_mul, norm_mul, map_inv₀, norm_inv, hdetn]
  calc (R ^ p)⁻¹ * ‖j ((gramE D x').updateCol a (pairingVector D x' y)).det‖ ≤ (R ^ p)⁻¹ * R ^ p :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 := inv_mul_cancel₀ (pow_pos hR0 p).ne'

theorem projectionCoeffs_add (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (y y' : D.La) :
    projectionCoeffs D x' (y + y') = projectionCoeffs D x' y + projectionCoeffs D x' y' := by
  have : pairingVector D x' (y + y') = pairingVector D x' y + pairingVector D x' y' := by
    funext b; simp [pairingVector, (sesq_sesquilinear_properties D).2.2.1]
  simp [projectionCoeffs, this, Matrix.mulVec_add]

theorem projectionCoeffs_smul (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (c : 𝓞 E) (y : D.La) :
    projectionCoeffs D x' (c • y) = IsCMField.complexConj E (c : E) • projectionCoeffs D x' y := by
  have : pairingVector D x' (c • y) = IsCMField.complexConj E (c : E) • pairingVector D x' y := by
    funext b; simp [pairingVector, (sesq_sesquilinear_properties D).2.2.2.2.1]
  simp [projectionCoeffs, this, Matrix.mulVec_smul]

theorem gram_mulVec_projection_coeffs (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (hdet : (gramE D x').det ≠ 0) (y : D.La) :
    gramE D x' *ᵥ projectionCoeffs D x' y = pairingVector D x' y := by
  rw [projectionCoeffs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]

theorem sesq_integral_combination (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (d : Fin p → 𝓞 E) (b : Fin p) :
    sesq D (x' b) (∑ a, d a • x' a) = ∑ a, gramE D x' b a * IsCMField.complexConj E (d a : E) := by
  let f : D.La →+ E := AddMonoidHom.mk' (sesq D (x' b)) (fun y y' => (sesq_sesquilinear_properties D).2.2.1 _ _ _)
  have hf : sesq D (x' b) (∑ a, d a • x' a) = f (∑ a, d a • x' a) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  show sesq D (x' b) (d a • x' a) = _
  rw [(sesq_sesquilinear_properties D).2.2.2.2.1, mul_comm]
  simp [gramE]

end GlobalTheory.CompanionTheory.Ar.Fl

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def projectionCoeffsAddHom (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (a : Fin p) : D.La →+ E :=
  AddMonoidHom.mk' (fun y => projectionCoeffs D x' y a) (fun y y' => by rw [projectionCoeffs_add]; rfl)

theorem exists_common_denominator_coeffs (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (ℓ : Nat.Primes) (hdet : (gramE D x').det ≠ 0)
    (hlog : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) :
    ∃ m : ℕ, ¬ (ℓ : ℕ) ∣ m ∧ ∀ y a, ∃ g : 𝓞 E, (g : E) = m * projectionCoeffs D x' y a := by
  classical
  have := D.fin
  obtain ⟨k, t, ht⟩ := Module.Finite.exists_fin (R := 𝓞 E) (M := D.La)
  have hpt : ∀ i a, ∃ n : ℕ, ¬ (ℓ : ℕ) ∣ n ∧ ∃ b : 𝓞 E, (n : E) * projectionCoeffs D x' (t i) a = b := fun i a => by
    obtain ⟨n, b, hn, hb⟩ := (GlobalTheory.T.padic_integral_iff_denominator E ℓ _).1 (fun j => padic_norm_projectionCoeffs_le D x' ℓ hdet hlog (t i) a j)
    exact ⟨n, hn, b, hb⟩
  choose n hn b hb using hpt
  refine ⟨∏ i, ∏ a, n i a, ?_, fun y a => ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.1 ℓ.2) _).1 h
    obtain ⟨a, -, ha⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.1 ℓ.2) _).1 hi
    exact hn i a ha
  · have hy : y ∈ Submodule.span (𝓞 E) (Set.range t) := ht ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hy
    have hdv : ∀ i, ∃ w : ℕ, ∏ i, ∏ a, n i a = n i a * w := fun i =>
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ a)).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    choose w hw using hdv
    have he : projectionCoeffs D x' (∑ i, c i • t i) a = ∑ i, IsCMField.complexConj E (c i : E) * projectionCoeffs D x' (t i) a := by
      show projectionCoeffsAddHom D x' a (∑ i, c i • t i) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show projectionCoeffs D x' (c i • t i) a = _
      rw [projectionCoeffs_smul, Pi.smul_apply, smul_eq_mul]
    have hmem : ((∏ i, ∏ a, n i a : ℕ) : E) * projectionCoeffs D x' (∑ i, c i • t i) a ∈ (algebraMap (𝓞 E) E).range := by
      rw [he, Finset.mul_sum]
      refine Subring.sum_mem _ fun i _ => ?_
      rw [mul_left_comm, hw i, Nat.cast_mul, mul_comm ((n i a : ℕ) : E), _root_.mul_assoc, hb i a]
      exact Subring.mul_mem _ ⟨H.bar (c i), H.bar_eq (c i)⟩ (Subring.mul_mem _ ⟨(w i : 𝓞 E), by simp⟩ ⟨b i a, rfl⟩)
    obtain ⟨g, hg⟩ := hmem
    exact ⟨g, hg⟩

end GlobalTheory.CompanionTheory.Ar.Fl

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem algebraMap_bar_eq_conj (a : 𝓞 E) :
    algebraMap (𝓞 E) E (H.bar a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) := H.bar_eq a

def familyCombination (D : Datum H) {p : ℕ} (x' : Fin p → D.La) : (Fin p → 𝓞 E) →ₗ[𝓞 E] D.La where
  toFun c := ∑ a, c a • x' a
  map_add' c c' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_smul]

section Maps

variable (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (m : ℕ)
  (hm : ∀ y a, ∃ g : 𝓞 E, (g : E) = m * projectionCoeffs D x' y a)

def integralCoeffsRaw (y : D.La) (a : Fin p) : 𝓞 E := Classical.choose (hm y a)

theorem algebraMap_integralCoeffsRaw (y : D.La) (a : Fin p) :
    algebraMap (𝓞 E) E (integralCoeffsRaw D x' m hm y a) = m * projectionCoeffs D x' y a := Classical.choose_spec (hm y a)

def integralCoeffs : D.La →ₗ[𝓞 E] (Fin p → 𝓞 E) where
  toFun y a := H.bar (integralCoeffsRaw D x' m hm y a)
  map_add' y y' := by
    funext a
    apply IsFractionRing.injective (𝓞 E) E
    simp only [Pi.add_apply]
    rw [map_add (f := _), algebraMap_bar_eq_conj, algebraMap_bar_eq_conj, algebraMap_bar_eq_conj, algebraMap_integralCoeffsRaw, algebraMap_integralCoeffsRaw, algebraMap_integralCoeffsRaw, projectionCoeffs_add,
      Pi.add_apply, mul_add, map_add]
  map_smul' c y := by
    funext a
    apply IsFractionRing.injective (𝓞 E) E
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [map_mul, algebraMap_bar_eq_conj, algebraMap_bar_eq_conj, algebraMap_integralCoeffsRaw, algebraMap_integralCoeffsRaw, projectionCoeffs_smul, Pi.smul_apply, smul_eq_mul,
      map_mul, map_mul, map_mul, IsCMField.complexConj_apply_apply, map_natCast]
    show _ = ((c : 𝓞 E) : E) * _
    ring

theorem conj_integralCoeffs (y : D.La) (a : Fin p) :
    IsCMField.complexConj E (algebraMap (𝓞 E) E (integralCoeffs D x' m hm y a)) = m * projectionCoeffs D x' y a := by
  show IsCMField.complexConj E (algebraMap (𝓞 E) E (H.bar (integralCoeffsRaw D x' m hm y a))) = _
  rw [algebraMap_bar_eq_conj, IsCMField.complexConj_apply_apply, algebraMap_integralCoeffsRaw]

def orthogonalComponent : D.La →ₗ[𝓞 E] D.La := (m : 𝓞 E) • LinearMap.id - familyCombination D x' ∘ₗ integralCoeffs D x' m hm

theorem orthogonalComponent_mem (hdet : (gramE D x').det ≠ 0) (y : D.La) : orthogonalComponent D x' m hm y ∈ orthogonalFamilyAlt D x' := by
  show ∀ a, sesq D (x' a) (orthogonalComponent D x' m hm y) = 0
  intro b
  have hsub : ∀ u v w : D.La, sesq D u (v - w) = sesq D u v - sesq D u w := by
    intro u v w
    simp only [sesq, map_sub, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  have hsm : ∀ u v : D.La, sesq D u ((m : 𝓞 E) • v) = m * sesq D u v := by
    intro u v
    rw [Nat.cast_smul_eq_nsmul]
    simp only [sesq, map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Finset.mul_sum,
      _root_.mul_assoc]
  have hcomb : familyCombination D x' (integralCoeffs D x' m hm y) =
      ∑ a, integralCoeffs D x' m hm y a • x' a := rfl
  have hG := congrFun (gram_mulVec_projection_coeffs D x' hdet y) b
  simp only [Matrix.mulVec, dotProduct, pairingVector] at hG
  have hd : ∀ a, IsCMField.complexConj E ((integralCoeffs D x' m hm y a : 𝓞 E) : E) =
      m * projectionCoeffs D x' y a := fun a => conj_integralCoeffs D x' m hm y a
  simp only [orthogonalComponent, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.comp_apply]
  rw [hsub, hsm, hcomb, sesq_integral_combination]
  simp only [hd]
  rw [← hG, Finset.mul_sum]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro a _
  ring

end Maps

end GlobalTheory.CompanionTheory.Ar.Fl

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem rank_free_prod (L : Type) [AddCommGroup L] [Module (𝓞 E) L] (p : ℕ) :
    Module.rank (𝓞 E) ((Fin p → 𝓞 E) × L) = p + Module.rank (𝓞 E) L := by
  have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst (𝓞 E) (Fin p → 𝓞 E) L)
  rw [LinearMap.range_eq_top_of_surjective _ LinearMap.fst_surjective, rank_top, rank_fin_fun,
    LinearMap.ker_fst] at h
  rw [← h, ← (LinearEquiv.ofInjective (LinearMap.inr (𝓞 E) (Fin p → 𝓞 E) L)
    LinearMap.inr_injective).rank_eq]

theorem family_orthogonal_sum_injective (D : Datum H) {p : ℕ} (x' : Fin p → D.La) (hdet : (gramE D x').det ≠ 0)
    (c : Fin p → 𝓞 E) (z : orthogonalFamilyAlt D x') (h : familyCombination D x' c + (z : D.La) = 0) : c = 0 ∧ z = 0 := by
  have hadd : ∀ u v w : D.La, sesq D u (v + w) = sesq D u v + sesq D u w := by
    intro u v w
    simp only [sesq, map_add (f := _), Int.cast_add, add_mul, Finset.sum_add_distrib]
  have hcomb : familyCombination D x' c = ∑ a, c a • x' a := rfl
  have hv : (gramE D x') *ᵥ (fun a => IsCMField.complexConj E ((c a : 𝓞 E) : E)) = 0 := by
    funext b
    have hb := congrArg (sesq D (x' b)) h
    have h0 : sesq D (x' b) 0 = 0 := by simp [sesq]
    have hz : sesq D (x' b) (z : D.La) = 0 := z.2 b
    rw [hadd, hcomb, sesq_integral_combination, hz, h0, _root_.add_zero] at hb
    simpa [Matrix.mulVec, dotProduct] using hb
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
  have hc : c = 0 := by
    funext a
    have ha := congrFun hc0 a
    simp only [Pi.zero_apply, map_eq_zero] at ha
    first
      | simpa using ha
      | exact RingOfIntegers.coe_eq_zero_iff.mp ha
      | exact_mod_cast ha
  refine ⟨hc, ?_⟩
  subst hc
  have h1 : familyCombination D x' 0 = 0 := map_zero _
  rw [h1, _root_.zero_add] at h
  exact Submodule.coe_eq_zero.mp h

theorem finrank_orthogonal_family (D : Datum H) {p q : ℕ} (x' : Fin p → D.La) (ℓ : Nat.Primes) (hpq : p + q = D.p + D.q)
    (hdet : (gramE D x').det ≠ 0) (m : ℕ) (hm0 : m ≠ 0) (hm : ∀ y a, ∃ g : 𝓞 E, (g : E) = m * projectionCoeffs D x' y a) :
    Module.finrank (𝓞 E) (orthogonalFamilyAlt D x') = q := by
  classical
  haveI := D.fin
  set L2 := orthogonalFamilyAlt D x' with hL2
  let ψ : ((Fin p → 𝓞 E) × L2) →ₗ[𝓞 E] D.La := (familyCombination D x').coprod L2.subtype
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨c, z⟩ h
    obtain ⟨hc, hz⟩ := family_orthogonal_sum_injective D x' hdet c z h
    rw [hc, hz]
    rfl
  have hyp : ∀ y, orthogonalComponent D x' m hm y = m • y - familyCombination D x' (integralCoeffs D x' m hm y) := by
    intro y
    simp only [orthogonalComponent, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Nat.cast_smul_eq_nsmul]
  let φ : D.La →ₗ[𝓞 E] (Fin p → 𝓞 E) × L2 :=
    (integralCoeffs D x' m hm).prod
      ((orthogonalComponent D x' m hm).codRestrict L2 (fun y => orthogonalComponent_mem D x' m hm hdet y))
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : integralCoeffs D x' m hm y = 0 := congrArg Prod.fst hy
    have h2 : orthogonalComponent D x' m hm y = 0 := by
      have h3 := congrArg (fun w => (w.2 : D.La)) hy
      simpa [φ] using h3
    rw [hyp, h1, map_zero, sub_zero] at h2
    exact nsmul_injective_lattice D hm0 (by rw [h2, smul_zero])
  have hr : Module.rank (𝓞 E) ((Fin p → 𝓞 E) × L2) = Module.rank (𝓞 E) D.La :=
    le_antisymm (LinearMap.rank_le_of_injective ψ hψ) (LinearMap.rank_le_of_injective φ hφ)
  rw [rank_free_prod, ← Module.finrank_eq_rank (𝓞 E) D.La, D.rank, ← hpq,
    ← Module.finrank_eq_rank (𝓞 E) L2] at hr
  norm_cast at hr
  omega

theorem exists_orthogonal_local_basis_extension (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La) (hpq : p + q = D.p + D.q)
    (hdet : (gramE D x').det ≠ 0) (hlog : ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ =
      -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) :
    ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧
      ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  classical
  obtain ⟨m, hmℓ, hm⟩ := exists_common_denominator_coeffs D x' ℓ hdet hlog
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmℓ (dvd_zero _)
  haveI := D.fin
  haveI := D.proj
  set L2 := orthogonalFamilyAlt D x' with hL2
  have hfr : Module.finrank (𝓞 E) L2 = q := finrank_orthogonal_family D x' ℓ hpq hdet m hm0 hm
  obtain ⟨b0, hb0⟩ := exists_local_basis_cm_order.locBasis' (𝓞 E) (ℓ : ℕ) ℓ.prop (M := L2)
  let b : Fin q → L2 := b0 ∘ Fin.cast hfr.symm
  have hbli : LinearIndependent (𝓞 E) b := hb0.1.comp _ (Fin.cast_injective _)
  obtain ⟨n, hnℓ, hn⟩ := hb0.2
  have hrange : Set.range b = Set.range b0 := Function.Surjective.range_comp (fun i => ⟨Fin.cast hfr i, by ext; simp⟩) _
  have hyp : ∀ y, orthogonalComponent D x' m hm y = m • y - familyCombination D x' (integralCoeffs D x' m hm y) := by
    intro y
    simp only [orthogonalComponent, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Nat.cast_smul_eq_nsmul]
  refine ⟨Sum.elim x' (fun j => (b j : D.La)), rfl, ⟨?_, ?_⟩, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    set z : L2 := ∑ j, g (Sum.inr j) • b j with hz
    have hzc : (z : D.La) = ∑ j, g (Sum.inr j) • (b j : D.La) := by simp [hz]
    have hpsi := family_orthogonal_sum_injective D x' hdet (fun a => g (Sum.inl a)) z (by rw [hzc]; exact hg)
    have hg2 : ∀ j, g (Sum.inr j) = 0 := Fintype.linearIndependent_iff.mp hbli _ hpsi.2
    rintro (a | j)
    · exact congrFun hpsi.1 a
    · exact hg2 j
  · refine ⟨m * n, ?_, ?_⟩
    · rw [ℓ.prop.dvd_mul]
      push_neg
      exact ⟨hmℓ, hnℓ⟩
    · intro y
      have hdec : m • y = familyCombination D x' (integralCoeffs D x' m hm y) + orthogonalComponent D x' m hm y := by
        rw [hyp]
        abel
      rw [_root_.mul_comm m n, mul_smul, hdec, smul_add]
      apply Submodule.add_mem
      · apply nsmul_mem
        show ∑ a, integralCoeffs D x' m hm y a • x' a ∈ _
        refine Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl a, rfl⟩))
      · have h1 := hn ⟨_, orthogonalComponent_mem D x' m hm hdet y⟩
        rw [← hrange] at h1
        have h2 := Submodule.mem_map_of_mem (f := L2.subtype) h1
        rw [Submodule.map_span] at h2
        have h3 := Submodule.span_mono (R := 𝓞 E) (s := L2.subtype '' Set.range b)
          (t := Set.range (Sum.elim x' (fun j => (b j : D.La)))) (by
            rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
            exact ⟨Sum.inr j, rfl⟩) h2
        simpa using h3
  · intro a j
    exact (b j).2 a

end GlobalTheory.CompanionTheory.Ar.Fl

end

namespace PositivityTheory.Xgf

theorem exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 :=
  fun _ _ _ _ _ D p q ℓ x' hpq hdet hlog => GlobalTheory.CompanionTheory.Ar.Fl.exists_orthogonal_local_basis_extension D p q ℓ x' hpq hdet hlog

end PositivityTheory.Xgf
