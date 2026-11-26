module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem exists_eq_mul_mult_of_units (F : Type) [Field F] [NumberField F]
    (D : InfinitePlace F → ℝ)
    (h : ∀ u : (𝓞 F)ˣ, ∑ w : InfinitePlace F, Real.log (w ((u : 𝓞 F) : F)) * D w = 0) :
    ∃ c : ℝ, ∀ w, D w = c * (mult w : ℝ) := by
  classical
  have hsplit : ∀ f : InfinitePlace F → ℝ,
      ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)}, f v.1 = ∑ w, f w - f (w₀ : InfinitePlace F) := by
    intro f
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (w₀ : InfinitePlace F)), add_sub_cancel_right]
    exact (Finset.sum_subtype _ (fun w => by simp) f).symm
  let a : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ :=
    fun v => D v.1 / (mult v.1 : ℝ) - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ)
  let φ : ({w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ v, x v * a v
      map_add' := fun x y => by simp [Finset.sum_add_distrib, add_mul]
      map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u : (𝓞 F)ˣ, φ (logEmbedding F (Additive.ofMul u)) = 0 := by
    intro u
    have e1 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
          = 0 - Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) * D (w₀ : InfinitePlace F) := by
      rw [← h u]
      exact hsplit (fun w => Real.log (w (algebraMap (𝓞 F) F u)) * D w)
    have e2 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u))
          = 0 - (mult (w₀ : InfinitePlace F) : ℝ) * Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) := by
      rw [← sum_mult_mul_log u]
      exact hsplit (fun w => (mult w : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)))
    have hm0 : (mult (w₀ : InfinitePlace F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
    show ∑ v, logEmbedding F (Additive.ofMul u) v * a v = 0
    simp only [logEmbedding_component]
    calc ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)) * a v
        = ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
            - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ) * ((mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)))) := by
          apply Finset.sum_congr rfl
          intro v _
          have hm : (mult v.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
          simp only [a]
          field_simp
          try ring
      _ = 0 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
          field_simp
          try ring
  have hle : Submodule.span ℝ (unitLattice F : Set (logSpace F)) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hφ (Additive.toMul y)
  rw [unitLattice_span_eq_top F] at hle
  have ha : ∀ v, a v = 0 := by
    intro v
    have hv : (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) ∈ LinearMap.ker φ :=
      hle Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    have hφv : φ (Pi.single v (1 : ℝ)) = a v := by
      show ∑ v', (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) v' * a v' = a v
      simp [Pi.single_apply]
    rw [← hφv]
    exact hv
  refine ⟨D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ), fun w => ?_⟩
  have hm : (mult w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
  by_cases hw : w = (w₀ : InfinitePlace F)
  · subst hw
    field_simp
  · have hv := ha ⟨w, hw⟩
    simp only [a, sub_eq_zero] at hv
    rw [← hv]
    field_simp

theorem sum_eq_mean_of_units :
    ∀ (F : Type) [Field F] [NumberField F] (d t : (F →+* ℂ) → ℝ),
      (∀ u : (𝓞 F)ˣ, ∑ σ : F →+* ℂ, Real.log ‖σ ((u : 𝓞 F) : F)‖ * d σ = 0) →
      (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) →
      ∑ σ : F →+* ℂ, t σ * d σ =
        (∑ σ : F →+* ℂ, t σ) / (Module.finrank ℚ F : ℝ) * ∑ σ : F →+* ℂ, d σ := by
  intro F _ _ d t hd ht
  classical
  have hfib : ∀ f : (F →+* ℂ) → ℝ, ∑ σ, f σ
      = ∑ w : InfinitePlace F, ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ :=
    fun f => (Finset.sum_fiberwise Finset.univ InfinitePlace.mk f).symm
  obtain ⟨c, hc⟩ := exists_eq_mul_mult_of_units F
    (fun w => ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), d σ) (by
      intro u
      have h1 := hd u
      rw [hfib] at h1
      refine Eq.trans ?_ h1
      apply Finset.sum_congr rfl
      intro w _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
      rw [InfinitePlace.apply])
  have ht' : ∀ σ : F →+* ℂ, t σ = t (InfinitePlace.mk σ).embedding := by
    intro σ
    have h2 : InfinitePlace.mk (InfinitePlace.mk σ).embedding = InfinitePlace.mk σ :=
      InfinitePlace.mk_embedding _
    rcases InfinitePlace.mk_eq_iff.mp h2 with h3 | h3
    · rw [h3]
    · have h4 := ht (InfinitePlace.mk σ).embedding
      rw [h3] at h4
      exact h4
  have hTfib : ∀ (w : InfinitePlace F) (f : (F →+* ℂ) → ℝ),
      ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), t σ * f σ
        = t w.embedding * ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ := by
    intro w f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
    rw [← ht' σ]
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hsum_d : ∑ σ, d σ = c * (Module.finrank ℚ F : ℝ) := by
    rw [hfib, ← InfinitePlace.sum_mult_eq, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact hc w
  have hsum_t : ∑ σ, t σ = ∑ w : InfinitePlace F, t w.embedding * (w.mult : ℝ) := by
    rw [hfib]
    apply Finset.sum_congr rfl
    intro w _
    have h5 := hTfib w (fun _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h5
    rw [h5, InfinitePlace.card_filter_mk_eq]
  have hsum_td : ∑ σ, t σ * d σ = c * ∑ σ, t σ := by
    conv_lhs => rw [hfib]
    rw [hsum_t, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [hTfib w d]
    have h6 := hc w
    rw [h6]
    ring
  rw [hsum_td, hsum_d, div_mul_eq_mul_div, eq_div_iff hn]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

def SncChart {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (e : ℕ) (h : Ω) : Prop :=
  ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ A) ∧ (∀ l, a l ∈ A) ∧ ∑ l, a l * f l = 1 ∧
    ∀ l, f l ≠ 0 → ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (f l)⁻¹ (A : Set Ω)) →
      Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
        LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
        Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
        ∀ q : Ideal S, q.IsPrime →
          ((∀ s : S, (s : Ω) = h → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

abbrev addJ {K : Type} (J : K → Type) (N : ℕ) : Unit ⊕ K → Type := Sum.elim (fun _ => Fin (N + 1)) J

instance addJ_fintype {K : Type} (J : K → Type) [∀ k, Fintype (J k)] (N : ℕ) : ∀ k, Fintype (addJ J N k)
  | .inl _ => inferInstanceAs (Fintype (Fin (N + 1)))
  | .inr k => inferInstanceAs (Fintype (J k))

def addY {K : Type} {J : K → Type} {N : ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (y : (Σ k, J k) → Ω₀) (x' : Fin (N + 1) → Ω) : (Σ k, addJ J N k) → Ω
  | ⟨.inl _, a⟩ => x' a
  | ⟨.inr k, a⟩ => algebraMap Ω₀ Ω (y ⟨k, a⟩)

def addV {K : Type} (J : K → Type) (N : ℕ) : (Σ k, J k) → Σ k, addJ J N k := fun p => ⟨.inr p.1, p.2⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueValuationRingLift
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem existsUnique_valuationRing_lift : ∀ (O V C : Type) [CommRing O] [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C] [IsFractionRing V C] (b : O →+* V) (Z : Scheme.{0}) (s : Z ⟶ Spec (CommRingCat.of O)) [IsProper s] (y : Spec (CommRingCat.of C) ⟶ Z), y ≫ s = Spec.map (CommRingCat.ofHom ((algebraMap V C).comp b)) → ∃! y' : Spec (CommRingCat.of V) ⟶ Z, Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ y' = y ∧ y' ≫ s = Spec.map (CommRingCat.ofHom b) := by
  intro O V C _ _ _ _ _ _ _ b Z s hs y hy
  have hv : ValuativeCriterion s := by
    have h : (@IsProper : MorphismProperty Scheme.{0}) s := hs
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hc : CommSq y (Spec.map (CommRingCat.ofHom (algebraMap V C))) s
      (Spec.map (CommRingCat.ofHom b)) := ⟨by
    rw [hy, ← Spec.map_comp]; rfl⟩
  let S : ValuativeCommSq s :=
    { R := V, K := C, i₁ := y, i₂ := Spec.map (CommRingCat.ofHom b), commSq := hc }
  obtain ⟨u⟩ := hv S
  refine ⟨u.default.l, ⟨u.default.fac_left, u.default.fac_right⟩, ?_⟩
  rintro y' ⟨h1, h2⟩
  have := u.uniq ⟨y', h1, h2⟩
  exact congrArg CommSq.LiftStruct.l this

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiChangeOfBasisDet
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiChangeOfBasisDet
namespace GlobalTheory.CompanionTheory.Ar.Lat

theorem wedge_matrix_mul_family (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (e : Fin n → V) (P : Matrix (Fin n) (Fin n) Ω) :
    exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e := by
  let L : (Fin n → Ω) →ₗ[Ω] V := (Pi.basisFun Ω (Fin n)).constr Ω e
  have hL : ∀ c : Fin n → Ω, L c = ∑ j, c j • e j := fun c => by
    simp [L, Module.Basis.constr_apply_fintype]
  have hLe : (fun i => L (Pi.basisFun Ω (Fin n) i)) = e := funext fun i => by simp [L]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff Ω _).1 fun f => ?_
  let A : (Fin n → Ω) [⋀^Fin n]→ₗ[Ω] Ω :=
    (f.compAlternatingMap (exteriorPower.ιMulti Ω n (M := V))).compLinearMap L
  have h := congrArg (fun g => g (fun i => P i))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun Ω (Fin n)) A)
  simp only [AlternatingMap.smul_apply, Pi.basisFun_det_apply, smul_eq_mul] at h
  have h1 : A (fun i => P i) = f (exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j)) := by
    simp only [A, AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply]
    congr 2
    funext i
    exact hL _
  have h2 : A (Pi.basisFun Ω (Fin n)) = f (exteriorPower.ιMulti Ω n e) := by
    simp only [A, AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply]
    congr 2
  have h3 : (Matrix.of fun i => P i) = P := rfl
  rw [h1, h2, h3] at h
  rw [map_sub, map_smul, h, smul_eq_mul, mul_comm, sub_self]

end GlobalTheory.CompanionTheory.Ar.Lat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiChangeOfBasisDetStatement
alias GlobalTheory.T.iota_multi_change_of_basis_det := GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaled
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaled
namespace GlobalTheory.CompanionTheory.Ggeo.ClearDenominators

open Polynomial

theorem exists_common_denominator {o K : Type} [CommRing o] [Field K] [Algebra o K]
    (A : Subalgebra o K) (R : Subring K)
    (hfrac : ∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v)
    (s : Finset K) (hs : ∀ x ∈ s, x ∈ R) :
    ∃ w ∈ A, w ≠ 0 ∧ w⁻¹ ∈ R ∧ ∀ x ∈ s, w * x ∈ A := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    refine ⟨1, one_mem A, one_ne_zero, ?_, ?_⟩
    · rw [inv_one]
      exact one_mem R
    · intro x hx
      simp at hx
  · intro a t _ ih hs
    obtain ⟨w, hwA, hw0, hwR, hw⟩ :=
      ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨u, huA, v, hvA, hv0, hvR, hav⟩ := hfrac a (hs a (Finset.mem_insert_self a t))
    refine ⟨w * v, mul_mem hwA hvA, mul_ne_zero hw0 hv0, ?_, ?_⟩
    · rw [mul_inv]
      exact mul_mem hwR hvR
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxt
      · have key : w * v * x = w * u := by
          rw [hxa, hav, div_eq_mul_inv]
          calc w * v * (u * v⁻¹) = w * u * (v * v⁻¹) := by ring
            _ = w * u := by rw [mul_inv_cancel₀ hv0, mul_one]
        rw [key]
        exact mul_mem hwA huA
      · have key : w * v * x = v * (w * x) := by ring
        rw [key]
        exact mul_mem hvA (hw x hxt)

theorem exists_mul_isIntegral :
    ∀ {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K),
      (∀ a ∈ A, a ∈ R) → (∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v) →
      ∀ (t : K), IsIntegral R t → ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ IsIntegral A (v * t) := by
  intro o K _ _ _ A R _ hfrac t ht
  classical
  obtain ⟨p, hpm, hp⟩ := ht
  have hPm : (p.map (algebraMap R K)).Monic := hpm.map (algebraMap R K)
  have hP : (p.map (algebraMap R K)).eval₂ (RingHom.id K) t = 0 := by
    rw [Polynomial.eval₂_map, RingHom.id_comp]
    exact hp
  have hPR : ∀ i, (p.map (algebraMap R K)).coeff i ∈ R := by
    intro i
    rw [Polynomial.coeff_map]
    exact (p.coeff i).2
  generalize p.map (algebraMap R K) = P at hPm hP hPR
  obtain ⟨w, hwA, hw0, hwR, hw⟩ := exists_common_denominator A R hfrac
    ((Finset.range (P.natDegree + 1)).image P.coeff) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hPR i)
  refine ⟨w, hwA, hw0, hwR, ?_⟩
  have hcoef : ∀ i, P.coeff i * w ^ (P.natDegree - i) ∈ A := by
    intro i
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      have h1 : P.coeff i * w ^ (P.natDegree - i) = w ^ k * (w * P.coeff i) := by
        rw [hk]
        ring
      rw [h1]
      exact mul_mem (pow_mem hwA k)
        (hw _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))))
    · rw [hi, Nat.sub_self, pow_zero, mul_one, hPm.coeff_natDegree]
      exact one_mem A
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact zero_mem A
  have hQm : (P.scaleRoots w).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_scaleRoots,
      Polynomial.coeff_scaleRoots_natDegree]
    exact hPm
  have hlift : P.scaleRoots w ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    exact ⟨⟨_, hcoef i⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hQm
  refine ⟨q, hqm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hqmap]
  exact Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id K) hP

end GlobalTheory.CompanionTheory.Ggeo.ClearDenominators
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaledStatement
alias GlobalTheory.T.integral_over_localization_scaled := GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullback
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullback
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ggeo.LocalLift

theorem exists_mul_eq_of_isPushout {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (po : IsPushout f g h k) (M : Submonoid A)
    (hg : ∀ c : C, ∃ a, ∃ m ∈ M, c * g.hom m = g.hom a) (d : D) :
    ∃ m ∈ M, ∃ b, d * h.hom (f.hom m) = h.hom b := by
  have GlobalTheory.CompanionTheory.Ar.Conj.hw : ∀ a, h.hom (f.hom a) = k.hom (g.hom a) := fun a => by
    have := congrArg (fun φ : A ⟶ D => φ.hom a) po.w
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have GlobalTheory.CompanionTheory.RedCov.Levi.hd : d ∈ Subring.closure
      (Set.range (ConcreteCategory.hom h) ∪ Set.range (ConcreteCategory.hom k)) := by
    rw [CommRingCat.closure_range_union_range_eq_top_of_isPushout po]
    exact Subring.mem_top d
  refine Subring.closure_induction
    (p := fun x _ => ∃ m ∈ M, ∃ b, x * h.hom (f.hom m) = h.hom b) ?_ ?_ ?_ ?_ ?_ ?_ GlobalTheory.CompanionTheory.RedCov.Levi.hd
  · rintro x (⟨b, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1, M.one_mem, b, ?_⟩
      show h.hom b * h.hom (f.hom 1) = h.hom b
      simp
    · show ∃ m ∈ M, ∃ b, k.hom c * h.hom (f.hom m) = h.hom b
      obtain ⟨a, m, hm, hca⟩ := hg c
      refine ⟨m, hm, f.hom a, ?_⟩
      rw [GlobalTheory.CompanionTheory.Ar.Conj.hw, GlobalTheory.CompanionTheory.Ar.Conj.hw, ← map_mul, hca]
  · exact ⟨1, M.one_mem, 0, by simp⟩
  · exact ⟨1, M.one_mem, 1, by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨m₁, hm₁, b₁, e₁⟩ := hx
    obtain ⟨m₂, hm₂, b₂, e₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, b₁ * f.hom m₂ + b₂ * f.hom m₁, ?_⟩
    simp only [map_mul, map_add (f := _)]
    linear_combination h.hom (f.hom m₂) * e₁ + h.hom (f.hom m₁) * e₂
  · intro x _ hx
    obtain ⟨m, hm, b, e⟩ := hx
    exact ⟨m, hm, -b, by rw [neg_mul, e, map_neg]⟩
  · intro x y _ _ hx hy
    obtain ⟨m₁, hm₁, b₁, e₁⟩ := hx
    obtain ⟨m₂, hm₂, b₂, e₂⟩ := hy
    refine ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, b₁ * b₂, ?_⟩
    simp only [map_mul]
    linear_combination (y * h.hom (f.hom m₂)) * e₁ + h.hom b₁ * e₂

theorem stalk_exists_mul_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {p : X} (hp : p ∈ U)
    (c : X.presheaf.stalk p) :
    ∃ a m : Γ(X, U), IsUnit ((X.presheaf.germ U p hp).hom m) ∧
      c * (X.presheaf.germ U p hp).hom m = (X.presheaf.germ U p hp).hom a := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hp⟩
  have hloc := hU.isLocalization_stalk ⟨p, hp⟩
  obtain ⟨⟨a, m⟩, hm⟩ := @IsLocalization.surj _ _ _ _ _ _ hloc c
  exact ⟨a, m, @IsLocalization.map_units _ _ _ _ _ _ hloc m, hm⟩

theorem fromSpecStalk_appLE {X : Scheme.{0}} {U : X.Opens} {p : X} (hp : p ∈ U)
    (h : (⊤ : (Spec (X.presheaf.stalk p)).Opens) ≤ X.fromSpecStalk p ⁻¹ᵁ U) :
    (X.fromSpecStalk p).appLE U ⊤ h =
      X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso (X.presheaf.stalk p)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hp, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  have e : (homOfLE (le_top : X.fromSpecStalk p ⁻¹ᵁ U ≤ ⊤)).op ≫ (homOfLE h).op =
      𝟙 (Opposite.op (⊤ : (Spec (X.presheaf.stalk p)).Opens)) := by
    exact Subsingleton.elim _ _
  rw [e]
  exact (congrArg (fun t => X.presheaf.germ U p hp ≫ (Scheme.ΓSpecIso (X.presheaf.stalk p)).inv ≫ t)
    ((Spec (X.presheaf.stalk p)).presheaf.map_id _)).trans (by simp only [Category.comp_id])

theorem exists_extension {X Y Z P : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y) (hy : π y₀ = p)
    (fst : P ⟶ Y) (snd : P ⟶ Spec (X.presheaf.stalk p))
    (H : IsPullback fst snd π (X.fromSpecStalk p)) (c : Z ⟶ P) [IsClosedImmersion c]
    (s : Γ(Z, ⊤)) :
    ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧ ((c ≫ fst).app W).hom f =
      Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ W ≤ ⊤)).op s := by
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := p) (by simp)
  have hy₀ : y₀ ∈ π ⁻¹ᵁ V := (Scheme.Hom.mem_preimage π).2 (by rw [hy]; exact hpV)
  obtain ⟨W₀, hW₀, hy₀W₀, hW₀V⟩ := exists_isAffineOpen_mem_and_subset hy₀
  have hUSX : W₀ ≤ π ⁻¹ᵁ V := fun x hx => hW₀V hx
  have hUST : (⊤ : (Spec (X.presheaf.stalk p)).Opens) ≤ X.fromSpecStalk p ⁻¹ᵁ V := by
    intro x _
    have hx : X.fromSpecStalk p x ∈ Set.range (X.fromSpecStalk p) := ⟨x, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hx
    have hx' : X.fromSpecStalk p x ⤳ p := hx
    exact (Scheme.Hom.mem_preimage _).2 (Specializes.mem_open hx' V.isOpen hpV)
  obtain ⟨UY, hUY⟩ : ∃ UY, UY = fst ⁻¹ᵁ W₀ ⊓ snd ⁻¹ᵁ ⊤ := ⟨_, rfl⟩
  have hUYle : UY ≤ fst ⁻¹ᵁ W₀ := by
    rw [hUY]
    exact inf_le_left
  have hpo := (isIso_pushoutSection_iff H hUST hUSX hUY).1
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hV (isAffineOpen_top _) hW₀)
  have hUYaff : IsAffineOpen UY := by
    have hpb := Scheme.Hom.isPullback_resLE H hUST hUSX hUY
    haveI : IsAffine (W₀ : Scheme.{0}) := hW₀
    haveI : IsAffine (V : Scheme.{0}) := hV
    haveI : IsAffine ((⊤ : (Spec (X.presheaf.stalk p)).Opens) : Scheme.{0}) :=
      isAffineOpen_top _
    haveI := Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
      (π.resLE V W₀ hUSX) ((X.fromSpecStalk p).resLE V ⊤ hUST)
    exact IsAffine.of_isIso hpb.isoPullback.hom
  obtain ⟨d, GlobalTheory.CompanionTheory.RedCov.Levi.hd⟩ := Scheme.Hom.app_surjective c UY hUYaff
    ((Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op).hom s)
  have hd' : (c.app UY).hom d = (Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op).hom s :=
    GlobalTheory.CompanionTheory.RedCov.Levi.hd
  have hg : ∀ c' : Γ(Spec (X.presheaf.stalk p), ⊤), ∃ a, ∃ m ∈
      (IsUnit.submonoid (X.presheaf.stalk p)).comap (X.presheaf.germ V p hpV).hom,
      c' * ((X.fromSpecStalk p).appLE V ⊤ hUST).hom m =
        ((X.fromSpecStalk p).appLE V ⊤ hUST).hom a := by
    intro c'
    obtain ⟨a, m, hmu, hm⟩ := GlobalTheory.CompanionTheory.Ggeo.LocalLift.stalk_exists_mul_eq hV hpV
      ((Scheme.ΓSpecIso (X.presheaf.stalk p)).hom.hom c')
    refine ⟨a, m, Submonoid.mem_comap.2 ((IsUnit.mem_submonoid_iff _).2 hmu), ?_⟩
    rw [GlobalTheory.CompanionTheory.Ggeo.LocalLift.fromSpecStalk_appLE hpV, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
      ← hm, map_mul]
    exact congrArg (fun t => t * _) (CommRingCat.inv_hom_apply _ c').symm
  obtain ⟨m, hmM, b, hb⟩ := GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_mul_eq_of_isPushout hpo _ hg d
  have hmu : IsUnit ((X.presheaf.germ V p hpV).hom m) :=
    (IsUnit.mem_submonoid_iff _).1 (Submonoid.mem_comap.1 hmM)
  have hy₀W : y₀ ∈ Y.basicOpen ((π.appLE V W₀ hUSX).hom m) := by
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.basicOpen_res]
    refine TopologicalSpace.Opens.mem_inf.2 ⟨hy₀W₀, ?_⟩
    rw [← Scheme.preimage_basicOpen, Scheme.Hom.mem_preimage, hy]
    exact (X.mem_basicOpen m p hpV).2 hmu
  obtain ⟨fm, hfm⟩ : ∃ fm, (π.appLE V W₀ hUSX).hom m = fm := ⟨_, rfl⟩
  rw [hfm] at hb hy₀W
  have hWW₀ : Y.basicOpen fm ≤ W₀ := Y.basicOpen_le fm
  have hu : IsUnit ((Y.presheaf.map (homOfLE hWW₀).op).hom fm) :=
    RingedSpace.isUnit_res_basicOpen _ fm
  refine ⟨Y.basicOpen fm, (Y.presheaf.map (homOfLE hWW₀).op).hom b * ↑hu.unit⁻¹, hy₀W, ?_⟩
  have hQ : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ c ⁻¹ᵁ UY := by
    rw [hUY]
    intro z hz
    exact (Scheme.Hom.mem_preimage c).2 (TopologicalSpace.Opens.mem_inf.2
      ⟨(Scheme.Hom.mem_preimage fst).2 (hWW₀ ((Scheme.Hom.mem_preimage (c ≫ fst)).1 hz)),
        (Scheme.Hom.mem_preimage snd).2 (by simp)⟩)
  have E₁ : Y.presheaf.map (homOfLE hWW₀).op ≫ (c ≫ fst).app (Y.basicOpen fm) =
      fst.appLE W₀ UY hUYle ≫ c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
  have e₁ : ∀ x, ((c ≫ fst).app (Y.basicOpen fm)).hom
      ((Y.presheaf.map (homOfLE hWW₀).op).hom x) =
      (c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ).hom ((fst.appLE W₀ UY hUYle).hom x) := by
    intro x
    have := congrArg (fun φ => CommRingCat.Hom.hom φ x) E₁
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have E₂ : Z.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ UY ≤ ⊤)).op ≫
      Z.presheaf.map (homOfLE hQ).op =
      Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ ⊤)).op := by
    (rw [← Functor.map_comp]) <;> rfl
  have e₂ : (c.appLE UY ((c ≫ fst) ⁻¹ᵁ Y.basicOpen fm) hQ).hom d =
      (Z.presheaf.map (homOfLE (le_top : (c ≫ fst) ⁻¹ᵁ Y.basicOpen fm ≤ ⊤)).op).hom s := by
    have h₂ := congrArg (fun φ => CommRingCat.Hom.hom φ s) E₂
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h₂
    rw [← h₂, ← hd', Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [map_mul, e₁ b, ← hb, map_mul, e₂, ← e₁ fm, mul_assoc, ← map_mul, hu.mul_val_inv,
    map_one, mul_one]

theorem exists_open_extension : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y), π y₀ = p →
    ∀ (c : Z ⟶ pullback π (X.fromSpecStalk p)) [IsClosedImmersion c] (s : Γ(Z, ⊤)),
    ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧
      ((c ≫ pullback.fst π (X.fromSpecStalk p)).app W).hom f =
        Z.presheaf.map (homOfLE (le_top : (c ≫ pullback.fst π (X.fromSpecStalk p)) ⁻¹ᵁ W ≤ ⊤)).op s := by
  intro X Y Z π p y₀ hy c _ s
  exact exists_extension π p y₀ hy _ _ (IsPullback.of_hasPullback π (X.fromSpecStalk p)) c s

end GlobalTheory.CompanionTheory.Ggeo.LocalLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullbackStatement
open AlgebraicGeometry CategoryTheory Limits
alias GlobalTheory.T.section_extends_from_stalk_pullback := GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GapN
namespace GlobalTheory.CompanionTheory.Ar.ExRefEff

def gapN {Ψ : Type} {N : ℕ} (ν : Ψ × Fin N → ℤ) : Option (Ψ × Fin N) → ℤ
  | none => 0
  | some p => ν p - if h : (p.2 : ℕ) + 1 < N then ν (p.1, ⟨p.2 + 1, h⟩) else 0

end GlobalTheory.CompanionTheory.Ar.ExRefEff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HBBound
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hB_bound : ∀ (N j B : ℕ) (S : Finset ℕ) (d v : ℕ → ℝ) (lrd Lv hrec hB : ℝ), j ≤ N → 3 ≤ B → 0 ≤ lrd → |hrec| ≤ N * (3 / 2 * lrd + |Lv| / 2) → hB = hrec + ∑ p ∈ S, d p → (∀ p ∈ S, p.Prime) → (∀ p ∈ S, 0 ≤ v p) → (∀ p ∈ S, |d p| ≤ (N / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p) → ∑ p ∈ S, v p * Real.log p ≤ lrd → ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 → |hB| ≤ 4 * N * (Real.log B + lrd + |Lv|) := by
  intro N j B S d v lrd Lv hrec hB hj hB3 hl hrecb hBeq hprime hv hd hsv hsl
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlogB : 1 ≤ Real.log B := by
    have h3 : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    have hexp : Real.exp 1 ≤ B := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hsum : |∑ p ∈ S, d p| ≤ N * (3 * Real.log B + 1) + N * lrd := by
    calc |∑ p ∈ S, d p| ≤ ∑ p ∈ S, |d p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S, ((N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hdp := hd p hp
        have e : ((N : ℝ) / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p =
            (N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p) := by ring
        linarith
      _ = (N : ℝ) * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) + N * ∑ p ∈ S, v p * Real.log p := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ N * (3 * Real.log B + 1) + N * lrd := by gcongr
  have htot : |hB| ≤ |hrec| + |∑ p ∈ S, d p| := by
    rw [hBeq]; exact abs_add_le _ _
  nlinarith [mul_nonneg hN (sub_nonneg.mpr hlogB), mul_nonneg hN hl, mul_nonneg hN (abs_nonneg Lv)]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndep
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndep
namespace GlobalTheory.CompanionTheory.Exterior

theorem ιMulti_ne_zero_of_linearIndependent :
    ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V),
      LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  intro Ω V _ _ _ n e he h
  let f : (Fin n → Ω) →ₗ[Ω] V := Fintype.linearCombination Ω e
  have hf : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective
  obtain ⟨π, hπ⟩ := f.exists_leftInverse_of_injective hf
  have hπe : ∀ j, π (e j) = Pi.single j 1 := by
    intro j
    have h2 := LinearMap.congr_fun hπ (Pi.single j 1)
    simpa [f, Fintype.linearCombination_apply_single] using h2
  let D : V [⋀^Fin n]→ₗ[Ω] Ω :=
    (Matrix.detRowAlternating (n := Fin n) (R := Ω)).compLinearMap π
  have h1 := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti D e
  rw [h, map_zero] at h1
  have h3 : D e = 1 := by
    have h4 : (fun i => π (e i)) = (1 : Matrix (Fin n) (Fin n) Ω) := by
      ext i j
      simp [hπe, Matrix.one_apply, Pi.single_apply, eq_comm]
    change Matrix.det (fun i => π (e i)) = 1
    rw [h4, Matrix.det_one]
  rw [h3] at h1
  exact zero_ne_one h1

end GlobalTheory.CompanionTheory.Exterior
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndepStatement
alias GlobalTheory.T.iota_multi_ne_zero_of_lin_indep := GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalization
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalization
namespace GlobalTheory.CompanionTheory.LocalSubringUnits

theorem mem_prime_iff_not_inv_mem :
    ∀ {K : Type} [Field K] (T : Subring K) (P : Ideal T) (_ : P.IsPrime) (t : T),
      t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ (LocalSubring.ofPrime T P).toSubring) := by
  intro K _ T P hP t
  have key : IsUnit (algebraMap T (LocalSubring.ofPrime T P).toSubring t) ↔ t ∉ P :=
    IsLocalization.AtPrime.isUnit_to_map_iff (LocalSubring.ofPrime T P).toSubring P t
  have hcoe : ((algebraMap T (LocalSubring.ofPrime T P).toSubring t :
      (LocalSubring.ofPrime T P).toSubring) : K) = (t : K) := rfl
  constructor
  · rintro ht ⟨h0, hinv⟩
    refine key.1 (IsUnit.of_mul_eq_one ⟨(t : K)⁻¹, hinv⟩ ?_) ht
    apply Subtype.ext
    rw [Subring.coe_mul, hcoe]
    exact mul_inv_cancel₀ h0
  · intro h
    by_contra ht
    obtain ⟨u, hu⟩ := (key.2 ht).exists_right_inv
    have hu' : (t : K) * (u : K) = 1 := by
      have := congrArg (fun x : (LocalSubring.ofPrime T P).toSubring => (x : K)) hu
      simpa only [Subring.coe_mul, hcoe, Subring.coe_one] using this
    have h0 : (t : K) ≠ 0 := left_ne_zero_of_mul_eq_one hu'
    refine h ⟨h0, ?_⟩
    rw [inv_eq_of_mul_eq_one_right hu']
    exact u.2

end GlobalTheory.CompanionTheory.LocalSubringUnits
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeMemIffNotUnitLocalizationStatement
alias GlobalTheory.T.prime_mem_iff_not_unit_localization := GlobalTheory.CompanionTheory.LocalSubringUnits.mem_prime_iff_not_inv_mem
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemSpanOfIotaMultiProportional
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemSpanOfIotaMultiProportional
namespace GlobalTheory.CompanionTheory.WedgeSpan

theorem span_of_wedge_proportional (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (b e : Fin n → V) (t : Ω) (he : LinearIndependent Ω e) (ht : t ≠ 0)
    (hbe : exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e) (i : Fin n) :
    b i ∈ Submodule.span Ω (Set.range e) := by
  classical
  by_contra hx
  have hv : LinearIndependent Ω (Fin.cons (b i) e : Fin (n + 1) → V) :=
    linearIndependent_finCons.2 ⟨he, hx⟩
  have hbe' : ExteriorAlgebra.ιMulti Ω n b = t • ExteriorAlgebra.ιMulti Ω n e := by
    have := congrArg Subtype.val hbe
    simpa using this
  have htb : Matrix.vecTail (Fin.cons (b i) b : Fin (n + 1) → V) = b :=
    by funext k; simp [Matrix.vecTail]
  have hte : Matrix.vecTail (Fin.cons (b i) e : Fin (n + 1) → V) = e :=
    by funext k; simp [Matrix.vecTail]
  have h0 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) b : Fin (n + 1) → V) = 0 :=
    (ExteriorAlgebra.ιMulti Ω (n + 1)).map_eq_zero_of_eq _ (i := 0) (j := i.succ)
      (by simp) (Fin.succ_ne_zero i).symm
  rw [ExteriorAlgebra.ιMulti_succ_apply, htb, hbe', mul_smul_comm, smul_eq_zero] at h0
  have h1 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) e : Fin (n + 1) → V) = 0 := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, hte]
    rcases h0 with h | h
    · exact absurd h ht
    · simpa using h
  have hfam := exteriorPower.ιMulti_family_linearIndependent_field (n := n + 1) hv
  apply hfam.ne_zero (Set.powersetCard.ofFinEmbEquiv (RelEmbedding.refl _))
  rw [exteriorPower.ιMulti_family, Equiv.symm_apply_apply]
  exact Subtype.ext h1

end GlobalTheory.CompanionTheory.WedgeSpan
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemSpanOfIotaMultiProportionalStatement
alias GlobalTheory.T.mem_span_of_iota_multi_proportional := GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerFinrankFractionField
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerFinrankFractionField
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ggeo

theorem finrank_kaehler_fractionRing_eq_of_basis
    (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] (m : ℕ) (w : Fin m → T)
    (hli : LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)))
    (hspan : Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = m := by
  haveI : Algebra.FormallyEtale T L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors T)
  haveI : Algebra.FormallyUnramified S K :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors S)
  haveI : Subsingleton (KaehlerDifferential S K) :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have hinj : Function.Injective (KaehlerDifferential.map S K L L) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map S K L x).1 hx
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  let e : KaehlerDifferential S L ≃ₗ[L] KaehlerDifferential K L :=
    LinearEquiv.ofBijective (KaehlerDifferential.map S K L L)
      ⟨hinj, KaehlerDifferential.map_surjective S K L⟩
  let b : Module.Basis (Fin m) T (KaehlerDifferential S T) := Module.Basis.mk hli hspan.ge
  let b' : Module.Basis (Fin m) L (KaehlerDifferential K L) :=
    ((Algebra.TensorProduct.basis L b).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale S T L)).map e
  simpa using Module.finrank_eq_card_basis b'

end GlobalTheory.CompanionTheory.Ggeo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerFinrankFractionFieldStatement
alias GlobalTheory.T.kaehler_finrank_fraction_field := GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocal
namespace GlobalTheory.CompanionTheory.IntegralClosureLocal

theorem mem_maximal_iff_not_inv_mem {K : Type} [Field K] (R : Subring K) [IsLocalRing R]
    (P : Ideal (integralClosure R K).toSubring) (hP : P.IsMaximal)
    (t : (integralClosure R K).toSubring) (htR : (t : K) ∈ R) :
    t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ R) := by
  let f : R →+* (integralClosure R K).toSubring :=
    (algebraMap R K).codRestrict (integralClosure R K).toSubring
      (fun r => (integralClosure R K).algebraMap_mem r)
  letI : Algebra R (integralClosure R K).toSubring := f.toAlgebra
  haveI : Algebra.IsIntegral R (integralClosure R K).toSubring := by
    refine ⟨fun x => ?_⟩
    obtain ⟨p, hp, h⟩ : IsIntegral R (x : K) := x.2
    refine ⟨p, hp, ?_⟩
    apply Subtype.ext
    have key := Polynomial.hom_eval₂ p f (integralClosure R K).toSubring.subtype x
    exact key.trans h
  have hm : (P.comap (algebraMap R (integralClosure R K).toSubring)).IsMaximal :=
    letI := hP
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  have hmax : P.comap (algebraMap R (integralClosure R K).toSubring)
      = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hm
  have hrt : algebraMap R (integralClosure R K).toSubring ⟨t, htR⟩ = t := Subtype.ext rfl
  have h1 : t ∈ P ↔ (⟨t, htR⟩ : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hmax, Ideal.mem_comap, hrt]
  rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have hne : (t : K) ≠ 0 := by
      intro h0
      have : (u : R) = 0 := by rw [hu]; exact Subtype.ext h0
      exact u.ne_zero this
    refine ⟨hne, ?_⟩
    have hmul : ((u : R) : K) * (((u⁻¹ : Rˣ) : R) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    have hut : ((u : R) : K) = (t : K) := by rw [hu]
    rw [hut] at hmul
    have : (t : K)⁻¹ = (((u⁻¹ : Rˣ) : R) : K) := inv_eq_of_mul_eq_one_right hmul
    rw [this]
    exact Subtype.coe_prop _
  · rintro ⟨hne, hinv⟩
    refine IsUnit.of_mul_eq_one (⟨(t : K)⁻¹, hinv⟩ : R) ?_
    exact Subtype.ext (mul_inv_cancel₀ hne)

end GlobalTheory.CompanionTheory.IntegralClosureLocal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocalStatement
alias GlobalTheory.T.maximal_ideal_membership_of_local := GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem
end
end
