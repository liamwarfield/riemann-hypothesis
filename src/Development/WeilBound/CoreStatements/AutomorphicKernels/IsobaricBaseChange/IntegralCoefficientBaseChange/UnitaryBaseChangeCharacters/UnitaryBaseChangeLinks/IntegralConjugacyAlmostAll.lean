module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralUnitaryConjugacyLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingExistsAevalOfCommuteSeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingExistsAevalOfCommuteSeparable
open Polynomial Matrix

namespace GlobalTheory.LocalCommutant

open GlobalTheory.ClassParam

variable {S : Type} [CommRing S] {n : ℕ}

theorem krylov_mulVec (Y : Matrix (Fin n) (Fin n) S) (v c : Fin n → S) :
    krylov Y v *ᵥ c = ∑ j, c j • (Y ^ (j : ℕ) *ᵥ v) := by
  ext i
  simp [krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem aeval_sum_monomial (Y : Matrix (Fin n) (Fin n) S) (c : Fin n → S) :
    aeval Y (∑ j : Fin n, monomial (j : ℕ) (c j)) = ∑ j : Fin n, c j • Y ^ (j : ℕ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, aeval_monomial, Algebra.smul_def]

theorem exists_isUnit_krylov (R : Type) [CommRing R] [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R)
    (hs : Y.charpoly.Separable) : ∃ v, IsUnit (krylov Y v) := by
  obtain ⟨w, hw⟩ := exists_cyclic_field (Y.map (IsLocalRing.residue R)) (by rw [charpoly_map]; exact hs.map)
  choose e he using fun i => IsLocalRing.residue_surjective (w i)
  refine ⟨e, (Matrix.isUnit_iff_isUnit_det _).2 ?_⟩
  have h1 : w = (IsLocalRing.residue R) ∘ e := funext fun i => (he i).symm
  rw [h1, ← krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hw
  exact (isUnit_map_iff (IsLocalRing.residue R) _).1 (isUnit_iff_ne_zero.2 hw)

theorem exists_aeval_of_comm (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ)
    (Y T : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) (hc : T * Y = Y * T) :
    ∃ p : R[X], T = aeval Y p := by
  obtain ⟨e, hK⟩ := exists_isUnit_krylov R Y hs
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hK
  set K := krylov Y e
  set c := K⁻¹ *ᵥ (T *ᵥ e)
  refine ⟨∑ j : Fin n, monomial (j : ℕ) (c j), ?_⟩
  set p : R[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  set D := T - aeval Y p
  have hKc : K *ᵥ c = T *ᵥ e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hDe : D *ᵥ e = 0 := by
    have h2 : aeval Y p *ᵥ e = K *ᵥ c := by
      rw [aeval_sum_monomial, Matrix.sum_mulVec, krylov_mulVec]
      simp [Matrix.smul_mulVec]
    rw [Matrix.sub_mulVec, h2, hKc, sub_self]
  have hpY : aeval Y p * Y = Y * aeval Y p := by
    calc aeval Y p * Y = aeval Y (p * X) := by simp
      _ = aeval Y (X * p) := by rw [mul_comm]
      _ = Y * aeval Y p := by simp
  have hDY : Commute D Y := Commute.sub_left hc hpY
  have hDK : D * K = 0 := by
    ext i j
    have h2 : D *ᵥ (Y ^ (j : ℕ) *ᵥ e) = 0 := by
      rw [Matrix.mulVec_mulVec, (hDY.pow_right _).eq, ← Matrix.mulVec_mulVec, hDe, Matrix.mulVec_zero]
    have := congrFun h2 i
    simpa [K, krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hD : D = 0 := by
    calc D = D * K * K⁻¹ := by rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
      _ = 0 := by rw [hDK, zero_mul]
  exact sub_eq_zero.1 hD

end GlobalTheory.LocalCommutant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingExistsAevalOfCommuteSeparableStatement
open Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRing_exists_aeval_of_commute_separable : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y T : Matrix (Fin n) (Fin n) R), Y.charpoly.Separable → T * Y = Y * T → ∃ p : R[X], T = aeval Y p := by
  first | exact @GlobalTheory.LocalCommutant.exists_aeval_of_comm | exact GlobalTheory.LocalCommutant.exists_aeval_of_comm | (intros; apply GlobalTheory.LocalCommutant.exists_aeval_of_comm <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.SeparableIntegralModelAlmostAll
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.SeparableIntegralModelAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodPlaces

theorem eventually_valued_le_one {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w in Filter.cofinite (α := HeightOneSpectrum (𝓞 E)),
      Valued.v (algebraMap E (w.adicCompletion E) x) ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 E) x
  rw [Filter.eventually_cofinite]
  refine h.subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, not_le] at hw ⊢
  have e : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w x
  rwa [e] at hw

theorem eventually_coeffs_integral {E : Type} [Field E] [NumberField E] (P : E[X]) :
    ∀ᶠ w in Filter.cofinite (α := HeightOneSpectrum (𝓞 E)),
      ((P.map (algebraMap E (w.adicCompletion E))).coeffs : Set (w.adicCompletion E)) ⊆
        intL (w.adicCompletion E) := by
  have hall : ∀ᶠ w in Filter.cofinite (α := HeightOneSpectrum (𝓞 E)),
      ∀ n ∈ P.support, Valued.v (algebraMap E (w.adicCompletion E) (P.coeff n)) ≤ 1 :=
    (Filter.eventually_all_finset P.support).2 fun n _ => eventually_valued_le_one (P.coeff n)
  filter_upwards [hall] with w hw
  intro c hc
  rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
  obtain ⟨n, -, rfl⟩ := hc
  rw [Polynomial.coeff_map]
  change Valued.v (algebraMap E (w.adicCompletion E) (P.coeff n)) ≤ 1
  by_cases h0 : P.coeff n = 0
  · rw [h0, map_zero, map_zero]
    exact zero_le'
  · exact hw n (Polynomial.mem_support_iff.2 h0)

theorem goodPlaces (E : Type) [Field E] [NumberField E] (P : E[X]) (hP : P.Separable) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), ∃ Q₀ : (intL (w.adicCompletion E))[X], Q₀.Separable ∧
      Q₀.map (intL (w.adicCompletion E)).subtype = P.map (algebraMap E (w.adicCompletion E)) := by
  obtain ⟨a, b, hab⟩ := hP
  filter_upwards [eventually_coeffs_integral P, eventually_coeffs_integral a,
    eventually_coeffs_integral b] with w hPw haw hbw
  have lift : ∀ p : E[X],
      ((p.map (algebraMap E (w.adicCompletion E))).coeffs : Set (w.adicCompletion E)) ⊆
        intL (w.adicCompletion E) →
      ∃ q : (intL (w.adicCompletion E))[X],
        q.map (intL (w.adicCompletion E)).subtype = p.map (algebraMap E (w.adicCompletion E)) := by
    intro p hp
    have hl : p.map (algebraMap E (w.adicCompletion E)) ∈
        Polynomial.lifts (intL (w.adicCompletion E)).subtype := by
      rw [Polynomial.lifts_iff_coeffs_subset_range]
      intro c hc
      exact ⟨⟨c, hp hc⟩, rfl⟩
    exact (Polynomial.mem_lifts _).1 hl
  obtain ⟨Q, hQ⟩ := lift P hPw
  obtain ⟨A, hA⟩ := lift a haw
  obtain ⟨B, hB⟩ := lift b hbw
  refine ⟨Q, ⟨A, B, ?_⟩, hQ⟩
  apply Polynomial.map_injective (intL (w.adicCompletion E)).subtype Subtype.val_injective
  have h2 := congrArg (Polynomial.map (algebraMap E (w.adicCompletion E))) hab
  simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_one] at h2 ⊢
  rw [← Polynomial.derivative_map] at h2 ⊢
  rw [hQ, hA, hB]
  exact h2

end GlobalTheory.GoodPlaces
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.SeparableIntegralModelAlmostAllStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_integral_model_almost_all : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable → ∀ᶠ w in (cofinite : Filter (Pl E)), ∃ Q₀ : (intL (w.adicCompletion E))[X], Q₀.Separable ∧ Q₀.map (intL (w.adicCompletion E)).subtype = P.map (algebraMap E (w.adicCompletion E)) := by
  first | exact @GlobalTheory.GoodPlaces.goodPlaces | exact GlobalTheory.GoodPlaces.goodPlaces | (intros; apply GlobalTheory.GoodPlaces.goodPlaces <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralConjugacyAlmostAll
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntUniq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

instance instLocalIntL : IsLocalRing (intL L) :=
  inferInstanceAs (IsLocalRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)

theorem mul_int {n : ℕ} {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L)
    (hB : ∀ i j, B i j ∈ intL L) : ∀ i j, (A * B) i j ∈ intL L := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem cT_int {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ intL L) : ∀ i j, cT σ A i j ∈ intL L := fun i j => by
  have h := hA j i
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [intL, Valuation.mem_integer_iff] at h ⊢
  rw [hv]; exact h

theorem cT_cT {σ : L →+* L} (hs : ∀ x, σ (σ x) = x) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) : cT σ (cT σ A) = A := by
  ext i j; simp [cT, hs]

theorem locConj [CompleteSpace L] {σ : L →+* L} {ϖ : L} {q : ℕ} (hσ : IsUnramInv ϖ σ q) {n : ℕ}
    (Y Y' : GL (Fin n) (intL L)) (hu : bc (intL L).subtype Y ∈ UJ σ 1) (hu' : bc (intL L).subtype Y' ∈ UJ σ 1)
    (hc : Y.val.charpoly = Y'.val.charpoly) (hs : Y.val.charpoly.Separable) :
    ∃ g ∈ UJ σ 1, bc (intL L).subtype Y' = g⁻¹ * bc (intL L).subtype Y * g := by
  set φ := (intL L).subtype with hφ
  have hv := hσ.2.1
  have hinv := hσ.1
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_conj_of_charpoly_eq_of_separable_local (intL L) n Y.val Y'.val hc hs
  have hk' : Y' = k⁻¹ * Y * k := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hk)
  set g : GL (Fin n) L := bc φ k with hg
  set y := bc φ Y with hydef
  set y' := bc φ Y' with hy'def
  have hyy : y' = g⁻¹ * y * g := by rw [hy'def, hk', map_mul, map_mul, map_inv]
  set G := g.val with hG
  set Gi := (g⁻¹ : GL (Fin n) L).val with hGi
  set ym := y.val with hym
  set ym' := y'.val with hym'
  have hGGi : G * Gi = 1 := g.mul_inv
  have hGiG : Gi * G = 1 := g.inv_mul
  have hGI : ∀ i j, G i j ∈ intL L := fun i j => (k.val i j).2
  have hGiI : ∀ i j, Gi i j ∈ intL L := fun i j => by
    have : Gi = (bc φ k⁻¹).val := by rw [map_inv]
    rw [this]; exact ((k⁻¹ : GL (Fin n) (intL L)).val i j).2
  have hyI : ∀ i j, ym i j ∈ intL L := fun i j => (Y.val i j).2
  have hyU : cT σ ym * ym = 1 := by
    have h1 : cT σ ym * 1 * ym = 1 := hu
    rwa [Matrix.mul_one] at h1
  have hyU' : cT σ ym' * ym' = 1 := by
    have h1 : cT σ ym' * 1 * ym' = 1 := hu'
    rwa [Matrix.mul_one] at h1
  have hyU'2 : ym' * cT σ ym' = 1 := mul_eq_one_comm.1 hyU'
  have hy'm : ym' = Gi * ym * G := by rw [hym', hyy, Units.val_mul, Units.val_mul]
  have hGy : G * ym' = ym * G := by
    rw [hy'm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGGi, Matrix.one_mul]
  have hGs : cT σ G * ym = ym' * cT σ G := by
    have h1 : cT σ ym' * cT σ G = cT σ G * cT σ ym := by rw [← cT_mul, ← cT_mul, hGy]
    calc cT σ G * ym = (ym' * cT σ ym') * cT σ G * ym := by rw [hyU'2, Matrix.one_mul]
      _ = ym' * (cT σ ym' * cT σ G) * ym := by simp only [Matrix.mul_assoc]
      _ = ym' * cT σ G * (cT σ ym * ym) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = ym' * cT σ G := by rw [hyU, Matrix.mul_one]
  set T := G * cT σ G with hT
  have hT1 : T * (cT σ Gi * Gi) = 1 := by
    calc T * (cT σ Gi * Gi) = G * (cT σ G * cT σ Gi) * Gi := by simp only [hT, Matrix.mul_assoc]
      _ = 1 := by rw [← cT_mul, hGiG, cT_one, Matrix.mul_one, hGGi]
  let tU : GL (Fin n) L := ⟨T, cT σ Gi * Gi, hT1, mul_eq_one_comm.1 hT1⟩
  have hTI : ∀ i j, T i j ∈ intL L := mul_int hGI (cT_int hv hGI)
  have htiI : ∀ i j, (tU⁻¹ : GL (Fin n) L).val i j ∈ intL L := mul_int (cT_int hv hGiI) hGiI
  have hTfix : cT σ T = T := by rw [hT, cT_mul, cT_cT hinv]
  have hTy : T * ym = ym * T := by
    rw [hT, Matrix.mul_assoc, hGs, ← Matrix.mul_assoc, hGy, Matrix.mul_assoc]
  let T₀ : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨T i j, hTI i j⟩
  have hT₀ : T₀.map φ = T := by ext i j; rfl
  have hYm : Y.val.map φ = ym := rfl
  have hT₀c : T₀ * Y.val = Y.val * T₀ := by
    apply Matrix.map_injective (f := φ) Subtype.val_injective
    show (T₀ * Y.val).map φ = (Y.val * T₀).map φ
    rw [Matrix.map_mul, Matrix.map_mul, hT₀, hYm, hTy]
  obtain ⟨p, hp⟩ := GlobalTheory.T.localRing_exists_aeval_of_commute_separable (intL L) n Y.val T₀ hs hT₀c
  have hTp : tU.val = aeval ym (p.map φ) := by
    change T = _
    rw [← hT₀, hp, ← hYm, GlobalTheory.UTr.aeval_map_map]
  have hch : ym.charpoly = Y.val.charpoly.map φ := by rw [← hYm, Matrix.charpoly_map]
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.exists_commute_mul_cT_eq_of_integral_hermitian_polynomial L σ ϖ q hσ n ym Y.val.charpoly hyI hyU hch hs tU hTI htiI hTfix ⟨p, hTp⟩
  refine ⟨s⁻¹ * g, ?_, ?_⟩
  · set S := s.val
    set Si := (s⁻¹ : GL (Fin n) L).val
    have hSiS : Si * S = 1 := s.inv_mul
    have hh : (Si * G) * cT σ (Si * G) = 1 := by
      calc (Si * G) * cT σ (Si * G) = Si * T * cT σ Si := by rw [cT_mul]; simp only [hT, Matrix.mul_assoc]
        _ = Si * (S * cT σ S) * cT σ Si := by rw [← show S * cT σ S = T from hs2]
        _ = cT σ (Si * S) := by rw [cT_mul, ← Matrix.mul_assoc Si S, hSiS, Matrix.one_mul]
        _ = 1 := by rw [hSiS, cT_one]
    show cT σ (s⁻¹ * g).val * 1 * (s⁻¹ * g).val = 1
    rw [Matrix.mul_one, Units.val_mul]
    exact mul_eq_one_comm.1 hh
  · have hsy : s * y = y * s := Units.ext hs1
    calc y' = g⁻¹ * (s * y * s⁻¹) * g := by rw [hsy, mul_inv_cancel_right, hyy]
      _ = (s⁻¹ * g)⁻¹ * y * (s⁻¹ * g) := by group

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n → ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ y y' : UL n w, y ∈ KL n w → y' ∈ KL n w → y.1.val.charpoly = atPl w P → y'.1.val.charpoly = atPl w P → ∃ g : UL n w, y' = g⁻¹ * y * g := by
  intro E _ _ _ hU n P hP
  have hPs : P.Separable := hP.2.2.1
  filter_upwards [GlobalTheory.T.separable_integral_model_almost_all E P hPs] with w ⟨Q₀, hQs, hQ⟩
  intro y y' hy hy' hc hc'
  by_cases hsp : IsSplitAt w
  · have hsep : y.1.val.charpoly.Separable := by rw [hc]; exact hPs.map
    obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.conj_of_charpoly y.1 y'.1 hsep (hc.trans hc'.symm)
    refine ⟨⟨g, by simp [UL, hsp]⟩, Subtype.ext ?_⟩
    rw [hg]; rfl
  · obtain ⟨ϖ, q, hq, -⟩ := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hsp).2.1
    rw [KL, Subgroup.mem_subgroupOf] at hy hy'
    obtain ⟨Y, hY⟩ := hy
    obtain ⟨Y', hY'⟩ := hy'
    have hcp : ∀ (Z : GL (Fin n) (intL (w.adicCompletion E))) (z : UL n w), bc (intL _).subtype Z = z.1 →
        z.1.val.charpoly = atPl w P → Z.val.charpoly = Q₀ := by
      intro Z z hZ hz
      apply Polynomial.map_injective _ (intL (w.adicCompletion E)).subtype_injective
      rw [← Matrix.charpoly_map, hQ]
      change (bc (intL _).subtype Z).val.charpoly = _
      rw [hZ, hz]
    have hYc := hcp Y y hY hc
    have hY'c := hcp Y' y' hY' hc'
    have hmemU : ∀ z : UL n w, z.1 ∈ UJ (cj w) 1 := fun z => by
      have := z.2
      simpa [UL, hsp] using this
    obtain ⟨g, hgU, hgeq⟩ := locConj hq Y Y' (hY ▸ hmemU y) (hY' ▸ hmemU y') (hYc.trans hY'c.symm)
      (hYc ▸ hQs)
    refine ⟨⟨g, by simpa [UL, hsp] using hgU⟩, Subtype.ext ?_⟩
    show y'.1 = g⁻¹ * y.1 * g
    rw [← hY, ← hY']
    exact hgeq

end GlobalTheory.IntUniq
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralConjugacyAlmostAllStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.integral_conjugacy_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n → ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ y y' : UL n w, y ∈ KL n w → y' ∈ KL n w → y.1.val.charpoly = atPl w P → y'.1.val.charpoly = atPl w P → ∃ g : UL n w, y' = g⁻¹ * y * g := by
  first | exact @GlobalTheory.IntUniq.main | (intros; apply GlobalTheory.IntUniq.main <;> assumption)
end
