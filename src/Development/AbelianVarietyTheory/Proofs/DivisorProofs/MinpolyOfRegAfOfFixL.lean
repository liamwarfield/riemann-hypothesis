module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentralise
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenspacesOfSeparableMinpoly
open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.EigSum

theorem finrank_eigenspaces_of_separable_minpoly
    (Ω V : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] (T : Module.End Ω V) (f : Polynomial Ω) (hm : f.Monic)
    (hs : f.Separable) (h0 : Polynomial.aeval T f = 0)
    (hmin : ∀ g : Polynomial Ω, Polynomial.aeval T g = 0 → f ∣ g) :
    ∑ z ∈ f.roots.toFinset, Module.finrank Ω (T.eigenspace z) = Module.finrank Ω V ∧
      ∀ z ∈ f.roots, T.eigenspace z ≠ ⊥ := by
  have hf : f = minpoly Ω T := by
    apply Polynomial.eq_of_monic_of_associated hm (minpoly.monic (Algebra.IsIntegral.isIntegral T))
    exact associated_of_dvd_dvd (hmin _ (minpoly.aeval Ω T)) (minpoly.dvd Ω T h0)
  have hroot : ∀ z, T.HasEigenvalue z ↔ z ∈ f.roots := by
    intro z
    rw [Module.End.hasEigenvalue_iff_isRoot, ← hf, Polynomial.mem_roots hm.ne_zero]
  have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0
  refine ⟨?_, fun z hz => (hroot z).2 hz⟩
  set s := f.roots.toFinset
  let N : s → Submodule Ω V := fun z => T.eigenspace z
  have hind : iSupIndep N :=
    iSupIndep.comp (Module.End.eigenspaces_iSupIndep T) Subtype.val_injective
  have htop : ⨆ z, N z = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top T
    simp only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
    rw [eq_top_iff, ← h1]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ s
    · exact le_iSup N ⟨μ, hμ⟩
    · have : ¬ T.HasEigenvalue μ := by
        rw [hroot]; simpa [s] using hμ
      rw [Module.End.hasEigenvalue_iff, not_not] at this
      simp [this]
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hint).finrank_eq,
    Module.finrank_directSum]
  exact (Finset.sum_coe_sort s (fun z => Module.finrank Ω (T.eigenspace z))).symm

end GlobalTheory.EigSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantComm
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.RegCommutant

theorem exists_not_commute_of_two_le_finrank {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (h : 2 ≤ Module.finrank K E) :
    ∃ S₁ S₂ : Module.End K E, S₁ * S₂ ≠ S₂ * S₁ := by
  let b := Module.finBasis K E
  let e := LinearMap.toMatrixAlgEquiv b
  let i0 : Fin (Module.finrank K E) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank K E) := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨e.symm (Matrix.single i0 i1 1), e.symm (Matrix.single i1 i0 1), ?_⟩
  intro hc
  have h2 := congrArg e hc
  simp only [map_mul, AlgEquiv.apply_symm_apply] at h2
  have h3 := congrFun (congrFun h2 i0) i0
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h3
  simp [Matrix.single_apply, hne.symm] at h3

theorem finrank_le_natDegree_minpoly (K V : Type) [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : Module.End K V) (hs : (minpoly K T).Separable)
    (hc : ∀ a b : Module.End K V, Commute a T → Commute b T → Commute a b) :
    Module.finrank K V ≤ (minpoly K T).natDegree := by
  classical
  set f := minpoly K T with hf
  have hmon : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  obtain ⟨hsum, -⟩ := GlobalTheory.EigSum.finrank_eigenspaces_of_separable_minpoly K V T f hmon hs
    (minpoly.aeval K T) (fun g hg => minpoly.dvd K T hg)
  have hcard : f.roots.toFinset.card = f.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)]
    exact ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
  by_contra hlt
  push_neg at hlt
  obtain ⟨μ, hμ, h2⟩ : ∃ μ ∈ f.roots.toFinset, 2 ≤ Module.finrank K (T.eigenspace μ) := by
    by_contra hno
    push_neg at hno
    have : ∑ z ∈ f.roots.toFinset, Module.finrank K (T.eigenspace z) ≤
        ∑ z ∈ f.roots.toFinset, 1 :=
      Finset.sum_le_sum fun z hz => Nat.lt_succ_iff.mp (hno z hz)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  have hroot : f.IsRoot μ := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmon.ne_zero] at hμ; exact hμ
  set q := f /ₘ (Polynomial.X - Polynomial.C μ) with hq
  have hfq : (Polynomial.X - Polynomial.C μ) * q = f :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqμ : q.eval μ ≠ 0 := by
    intro h0
    have hq' : (Polynomial.X - Polynomial.C μ) * (q /ₘ (Polynomial.X - Polynomial.C μ)) = q :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h0
    obtain ⟨q2, hq2⟩ : ∃ q2, (Polynomial.X - Polynomial.C μ) * q2 = q := ⟨_, hq'⟩
    have hu : IsUnit (Polynomial.X - Polynomial.C μ) :=
      hs.squarefree _ ⟨q2, by rw [← hfq, ← hq2]; ring⟩
    exact Polynomial.not_isUnit_X_sub_C μ hu
  set c := q.eval μ with hc_def
  set Q := Polynomial.aeval T q with hQ
  set E := T.eigenspace μ with hE
  have hTQ : ∀ v, T (Q v) = μ • Q v := by
    intro v
    have h0 : Polynomial.aeval T ((Polynomial.X - Polynomial.C μ) * q) = 0 := by
      rw [hfq]; exact minpoly.aeval K T
    have h1 := congrArg (fun g : Module.End K V => g v) h0
    simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
      LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.zero_apply] at h1
    exact sub_eq_zero.mp h1
  have hQT : ∀ v, Q (T v) = T (Q v) := by
    intro v
    have h := congrArg (Polynomial.aeval T) (mul_comm q Polynomial.X)
    simp only [map_mul, Polynomial.aeval_X] at h
    exact congrArg (fun g : Module.End K V => g v) h
  have hQE : ∀ v, Q v ∈ E := by
    intro v
    rw [hE, Module.End.mem_eigenspace_iff]
    exact hTQ v
  have hQid : ∀ u ∈ E, Q u = c • u := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [hu0]
    · exact Module.End.aeval_apply_of_hasEigenvector ⟨hu, hu0⟩
  let π : V →ₗ[K] E := Q.codRestrict E hQE
  let ι : E →ₗ[K] V := E.subtype
  have hπι : ∀ x : E, π (ι x) = c • x := by
    intro x; apply Subtype.ext; simp [π, ι, hQid x.1 x.2]
  have hπT : ∀ v, π (T v) = μ • π v := by
    intro v; apply Subtype.ext; simp [π, hQT v, hTQ v]
  have hcomm : ∀ S : Module.End K E, Commute (ι ∘ₗ S ∘ₗ π) T := by
    intro S
    apply LinearMap.ext
    intro v
    have hm : T (S (π v) : V) = μ • (S (π v) : V) := Module.End.mem_eigenspace_iff.mp (S (π v)).2
    simp only [Module.End.mul_apply, LinearMap.comp_apply, hπT v, map_smul]
    simp [ι, hm]
  obtain ⟨S₁, S₂, hS⟩ := exists_not_commute_of_two_le_finrank h2
  have hab := hc _ _ (hcomm S₁) (hcomm S₂)
  apply hS
  apply LinearMap.ext
  intro w
  have h1 := congrArg (fun g : Module.End K V => g (ι (c⁻¹ • c⁻¹ • w))) hab.eq
  simp only [Module.End.mul_apply, LinearMap.comp_apply, map_smul, hπι, smul_smul] at h1
  apply Subtype.ext
  simpa [ι, mul_inv_cancel₀ hqμ, inv_mul_cancel₀ hqμ, mul_assoc, mul_left_comm] using h1

theorem natDegree_minpoly_eq_of_commutant_comm : ∀ (K : Type) [Field K] [IsAlgClosed K] (k : ℕ)
    (N : Matrix (Fin k) (Fin k) K), (minpoly K N).Separable →
    (∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B) →
    (minpoly K N).natDegree = k := by
  intro K _ _ k N hs hc
  have hmin : minpoly K (Matrix.toLin' N) = minpoly K N := Matrix.minpoly_toLin' N
  apply le_antisymm
  · calc (minpoly K N).natDegree ≤ N.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N) (Matrix.charpoly_monic N).ne_zero
      _ = k := by rw [Matrix.charpoly_natDegree_eq_dim]; simp
  · have h := finrank_le_natDegree_minpoly K (Fin k → K) (Matrix.toLin' N) (hmin ▸ hs) ?_
    · simpa [hmin] using h
    · intro a b ha hb
      let e : Matrix (Fin k) (Fin k) K ≃ₐ[K] Module.End K (Fin k → K) := Matrix.toLinAlgEquiv'
      have hN : e.symm (Matrix.toLin' N) = N := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      have hA := ha.map e.symm
      have hB := hb.map e.symm
      rw [hN] at hA hB
      simpa only [AlgEquiv.apply_symm_apply] using (hc _ _ hA hB).map e

end GlobalTheory.RegCommutant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqOfSeparableCommutantCommStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_of_separable_commutant_comm : ∀ (K : Type) [Field K] [IsAlgClosed K] (k : ℕ) (N : Matrix (Fin k) (Fin k) K), (minpoly K N).Separable → (∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B) → (minpoly K N).natDegree = k := by
  first | (exact @GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm) | (exact GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm) | (intros; apply GlobalTheory.RegCommutant.natDegree_minpoly_eq_of_commutant_comm  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentralise
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.RegDeg

open Polynomial

theorem natDegree_minpoly_eq : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C]
    [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C,
    (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) →
    (minpoly F c).natDegree = n := by
  intro F C _ _ _ _ _ _ n hC c hsep hcomm
  obtain ⟨k, hk0, hkC, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F C
  have hkn : k = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hkC.symm.trans hC)
  subst hkn
  set K := AlgebraicClosure F
  set x : K ⊗[F] C := (1 : K) ⊗ₜ[F] c with hx
  have hxi : IsIntegral K x := IsIntegral.of_finite K x
  have hxr : x = Algebra.TensorProduct.includeRight c := rfl
  have hdvd : minpoly K x ∣ (minpoly F c).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hxr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K c hxi
  have hmap : (minpoly F c).map (algebraMap F K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr
      (minpoly.ne_zero (IsIntegral.of_finite F c))
  have hle : (minpoly K x).natDegree ≤ (minpoly F c).natDegree := by
    calc (minpoly K x).natDegree ≤ ((minpoly F c).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap
      _ = (minpoly F c).natDegree := natDegree_map _
  have hxsep : (minpoly K x).Separable := (hsep.map).of_dvd hdvd

  let S := Subalgebra.centralizer F ({c} : Set C)
  letI : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b => Subtype.ext (by
        have ha : Commute (a : C) c := ((Subalgebra.mem_centralizer_iff F).mp a.2 c rfl).symm
        have hb : Commute (b : C) c := ((Subalgebra.mem_centralizer_iff F).mp b.2 c rfl).symm
        exact (hcomm _ _ ha hb).eq) }
  have hcent : ∀ y : C, y * c = c * y ↔ y ∈ Set.range (S.val) := by
    intro y
    constructor
    · intro h
      refine ⟨⟨y, ?_⟩, rfl⟩
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact h.symm
    · rintro ⟨w, rfl⟩
      exact ((Subalgebra.mem_centralizer_iff F).mp w.2 c rfl).symm
  set N := e x with hN
  have hmN : minpoly K N = minpoly K x := minpoly.algEquiv_eq e x
  have hNcomm : ∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B := by
    intro A B hA hB
    have hA' : e.symm A * x = x * e.symm A := by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hA.eq
    have hB' : e.symm B * x = x * e.symm B := by
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hB.eq
    have h := GlobalTheory.LKCentAf.commute_of_centralizer F K C S c S.val hcent _ _ hA' hB'
    have h2 := congrArg e h
    rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at h2
    exact h2
  have hdegN := GlobalTheory.T.natDegree_minpoly_eq_of_separable_commutant_comm K k N (by rw [hmN]; exact hxsep) hNcomm
  have hxk : (minpoly K x).natDegree = k := by rw [← hmN]; exact hdegN
  rw [← hxk]
  exact le_antisymm hge hle

end GlobalTheory.RegDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentraliseStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C, (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) → (minpoly F c).natDegree = n := by
  first | (exact @GlobalTheory.RegDeg.natDegree_minpoly_eq) | (exact GlobalTheory.RegDeg.natDegree_minpoly_eq) | (intros; apply GlobalTheory.RegDeg.natDegree_minpoly_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeSignatureOnePreservesPosDefForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeSignatureOnePreservesPosDefForm
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.PositiveDefiniteFormIdentities

theorem form_pull {n : ℕ} (h Z : Matrix (Fin n) (Fin n) ℂ) (v v' : Fin n → ℂ) :
    star (Z *ᵥ v) ⬝ᵥ h *ᵥ (Z *ᵥ v') = star v ⬝ᵥ (Zᴴ * h * Z) *ᵥ v' := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem form_swap {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ Q *ᵥ x = star (star x ⬝ᵥ Q *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hQ.eq, ← dotProduct_mulVec]

theorem form_expand {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (w z : Fin n → ℂ) (a : ℂ)
    (hwz : star z ⬝ᵥ Q *ᵥ w = 0) :
    star (w + a • z) ⬝ᵥ Q *ᵥ (w + a • z) =
      star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * (star z ⬝ᵥ Q *ᵥ z) := by
  have hzw : star w ⬝ᵥ Q *ᵥ z = 0 := by rw [form_swap hQ, hwz, star_zero]
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hwz, hzw, smul_eq_mul, Complex.normSq_eq_conj_mul_self, RCLike.star_def]
  ring

theorem form_self_ofReal {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q.IsHermitian) (x : Fin n → ℂ) :
    ((star x ⬝ᵥ Q *ᵥ x).re : ℂ) = star x ⬝ᵥ Q *ᵥ x := by
  have h := form_swap hQ x x
  exact Complex.conj_eq_iff_re.mp h.symm

end GlobalTheory.PositiveDefiniteFormIdentities

namespace GlobalTheory


open GlobalTheory.PositiveDefiniteFormIdentities in
theorem similitude_preserves_posDef : ∀ (n : ℕ) (h Q M : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (s : ℝ), h.det ≠ 0 → sigPosH hh = 1 → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) → 0 < s → Mᴴ * Q * M = (s : ℂ) • Q → ∀ (z : Fin n → ℂ) (c : ℂ), 0 < (star z ⬝ᵥ Q *ᵥ z).re → M *ᵥ z = c • z → ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ Mᴴ * H * M = (s : ℂ) • H := by
  intro n h Q M hh Z s hdet hsig hQZ hs hsim z c hz hMz
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hZm
  have hQ : Q.IsHermitian := by
    rw [hQZ]
    simp [IsHermitian, conjTranspose_mul, hh.eq, Matrix.mul_assoc]
  set q0 : ℝ := (star z ⬝ᵥ Q *ᵥ z).re with hq0
  have hq : star z ⬝ᵥ Q *ᵥ z = (q0 : ℂ) := (form_self_ofReal hQ z).symm
  have hq0ne : (q0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  set u : Fin n → ℂ := Q *ᵥ z with hu
  set H : Matrix (Fin n) (Fin n) ℂ := ((2 / q0 : ℝ) : ℂ) • vecMulVec u (star u) - Q with hH
  have hsu : ∀ x : Fin n → ℂ, star u ⬝ᵥ x = star z ⬝ᵥ Q *ᵥ x := by
    intro x
    rw [hu, star_mulVec, ← dotProduct_mulVec, hQ.eq]
  have hus : ∀ x : Fin n → ℂ, star x ⬝ᵥ u = star (star z ⬝ᵥ Q *ᵥ x) := by
    intro x
    rw [hu, ← form_swap hQ]

  have hval : ∀ x : Fin n → ℂ, star x ⬝ᵥ H *ᵥ x =
      ((2 / q0 * Complex.normSq (star z ⬝ᵥ Q *ᵥ x) - (star x ⬝ᵥ Q *ᵥ x).re : ℝ) : ℂ) := by
    intro x
    rw [hH, sub_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, hsu, hus, smul_eq_mul, smul_eq_mul]
    have e := form_self_ofReal hQ x
    push_cast
    rw [e, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hHh : H.IsHermitian := by
    rw [hH]
    refine IsHermitian.sub ?_ hQ
    ext i j
    simp [vecMulVec_apply, mul_comm]
  have hpos : H.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos hHh fun x hx => ?_
    rw [hval x]
    refine Complex.zero_lt_real.mpr ?_
    set p := star z ⬝ᵥ Q *ᵥ x with hp
    set a : ℂ := p / (q0 : ℂ) with ha
    have hpa : p = a * q0 := by rw [ha]; field_simp
    set w := x - a • z with hw
    have hxw : x = w + a • z := by rw [hw]; abel
    have hwz : star z ⬝ᵥ Q *ᵥ w = 0 := by
      rw [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hq, ← hp, hpa, sub_self]
    have hexp : star x ⬝ᵥ Q *ᵥ x = star w ⬝ᵥ Q *ᵥ w + (Complex.normSq a : ℂ) * q0 := by
      conv_lhs => rw [hxw]
      rw [form_expand hQ w z a hwz, hq]
    have hre : (star x ⬝ᵥ Q *ᵥ x).re = (star w ⬝ᵥ Q *ᵥ w).re + Complex.normSq a * q0 := by
      rw [hexp, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hnp : Complex.normSq p = Complex.normSq a * q0 ^ 2 := by
      rw [hpa, Complex.normSq_mul, Complex.normSq_ofReal]; ring
    have h2 : 2 / q0 * (Complex.normSq a * q0 ^ 2) = 2 * Complex.normSq a * q0 := by
      field_simp
    rw [hre, hnp, h2]
    by_cases hw0 : w = 0
    · have ha0 : a ≠ 0 := by
        intro ha0
        apply hx
        rw [hxw, hw0, ha0, zero_smul, add_zero]
      have e : (star w ⬝ᵥ Q *ᵥ w).re = 0 := by simp [hw0]
      rw [e]
      nlinarith [Complex.normSq_pos.mpr ha0]
    · have hZw : Zm *ᵥ w ≠ 0 := by
        intro h0
        apply hw0
        have hinv : ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm = 1 := Units.inv_mul Z
        calc w = (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * Zm) *ᵥ w := by rw [hinv, one_mulVec]
          _ = 0 := by rw [← mulVec_mulVec, h0, mulVec_zero]
      have hneg := re_form_neg_of_orth_of_sigPosH_eq_one h hh hdet hsig (Zm *ᵥ z) (Zm *ᵥ w)
        (by rw [form_pull, ← hQZ]; exact hz) (by rw [form_pull, ← hQZ]; exact hwz) hZw
      rw [form_pull, ← hQZ] at hneg
      nlinarith [Complex.normSq_nonneg a]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hc : star c * c = (s : ℂ) := by
    have e1 := congrArg (fun A => star z ⬝ᵥ A *ᵥ z) hsim
    rw [← form_pull Q M z z, hMz] at e1
    simp only [star_smul, mulVec_smul, smul_mulVec, smul_dotProduct, dotProduct_smul, smul_eq_mul] at e1
    rw [← hu, hq] at e1
    have e3 : (star c * c - s) * (q0 : ℂ) = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_right hq0ne)
  have hMu : Mᴴ *ᵥ u = star c • u := by
    have e2 := congrArg (fun A => A *ᵥ z) hsim
    rw [← mulVec_mulVec, ← mulVec_mulVec, hMz, mulVec_smul, mulVec_smul, smul_mulVec, ← hu] at e2
    apply smul_right_injective _ hs0
    change (s : ℂ) • (Mᴴ *ᵥ u) = (s : ℂ) • (star c • u)
    calc (s : ℂ) • (Mᴴ *ᵥ u) = star c • (c • Mᴴ *ᵥ u) := by rw [smul_smul, hc]
      _ = star c • ((s : ℂ) • u) := by rw [e2]
      _ = (s : ℂ) • (star c • u) := smul_comm _ _ _
  have hstar : star u ᵥ* M = c • star u := by
    have e : star (Mᴴ *ᵥ u) = star u ᵥ* M := by rw [star_mulVec, conjTranspose_conjTranspose]
    rw [← e, hMu, star_smul, star_star]
  have hM1 : Mᴴ * vecMulVec u (star u) * M = (s : ℂ) • vecMulVec u (star u) := by
    rw [mul_vecMulVec, vecMulVec_mul, hMu, hstar, ← hc]
    ext i j
    simp [vecMulVec_apply]
    ring
  refine ⟨H, hpos, ?_⟩
  rw [hH, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hM1, hsim, smul_sub,
    smul_comm ((2 / q0 : ℝ) : ℂ) (s : ℂ)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeSignatureOnePreservesPosDefFormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_signature_one_preserves_posDef_form : ∀ (n : ℕ) (h Q M : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (s : ℝ), h.det ≠ 0 → sigPosH hh = 1 → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) → 0 < s → Mᴴ * Q * M = (s : ℂ) • Q → ∀ (z : Fin n → ℂ) (c : ℂ), 0 < (star z ⬝ᵥ Q *ᵥ z).re → M *ᵥ z = c • z → ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ Mᴴ * H * M = (s : ℂ) • H := by
  first | (exact @GlobalTheory.similitude_preserves_posDef) | (exact GlobalTheory.similitude_preserves_posDef) | (intros; apply GlobalTheory.similitude_preserves_posDef  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitude
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitude
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.SimNormSq

open Polynomial

theorem commute_aeval_of_commute {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {x y : A} (h : Commute y x) (p : R[X]) : Commute y (aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial n a =>
    rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right a y).mul_right (h.pow_right n)

theorem eq_zero_of_conjTranspose_mul_mul_eq_zero {n : ℕ} {H A : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (h : Aᴴ * H * A = 0) : A = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.zero_mulVec]
  by_contra hne
  have hpos := hH.dotProduct_mulVec_pos hne
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h,
    Matrix.zero_mulVec, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.SimNormSq

namespace GlobalTheory

open Polynomial

theorem aeval_eq_zero_of_mul_self_eq_zero_of_similitude :
    ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s →
      Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ,
        Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  intro n H M s hH hs hM P hP
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hHinv : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHinv' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHh : Hᴴ = H := hH.1
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [conjTranspose_nonsing_inv, hHh]
  have hc : ∀ A : Matrix (Fin n) (Fin n) ℂ, H⁻¹ * (H * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv, Matrix.one_mul]
  have hc' : ∀ A : Matrix (Fin n) (Fin n) ℂ, H * (H⁻¹ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hHinv', Matrix.one_mul]
  have hM' : Mᴴ * (H * M) = (s : ℂ) • H := by rw [← Matrix.mul_assoc]; exact hM
  set D := H⁻¹ * Mᴴ * H with hD
  have hDM : D * M = (s : ℂ) • 1 := by
    rw [hD]; simp only [Matrix.mul_assoc]; rw [hM', Matrix.mul_smul, hHinv]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hMD : M * D = (s : ℂ) • 1 := by
    have h1 : ((s : ℂ)⁻¹ • D) * M = 1 := by
      rw [Matrix.smul_mul, hDM, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.mul_smul] at h2
    calc M * D = (s : ℂ) • ((s : ℂ)⁻¹ • (M * D)) := by
          rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
      _ = (s : ℂ) • 1 := by rw [h2]
  have hcomm : Commute D M := by
    show D * M = M * D
    rw [hDM, hMD]
  have hall : ∀ Y, Commute Y M → Commute Y (aeval M P) := fun Y hY =>
    SimNormSq.commute_aeval_of_commute hY P
  have hDW := hall D hcomm
  generalize hW : aeval M P = W at hP hDW ⊢
  have key : Commute (H⁻¹ * Wᴴ * H) M := by
    have h1 : Wᴴ * (H * (M * H⁻¹)) = H * (M * (H⁻¹ * Wᴴ)) := by
      have h0 := congrArg conjTranspose hDW.eq
      simp only [hD, conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
        Matrix.mul_assoc] at h0
      exact h0
    show H⁻¹ * Wᴴ * H * M = M * (H⁻¹ * Wᴴ * H)
    calc H⁻¹ * Wᴴ * H * M = H⁻¹ * (Wᴴ * (H * (M * H⁻¹))) * H := by
          simp only [Matrix.mul_assoc, hHinv, Matrix.mul_one]
      _ = H⁻¹ * (H * (M * (H⁻¹ * Wᴴ))) * H := by rw [h1]
      _ = M * (H⁻¹ * Wᴴ * H) := by
          simp only [Matrix.mul_assoc, hc]
  have hXW : Commute (H⁻¹ * Wᴴ * H) W := by
    have h4 := hall _ key
    rwa [hW] at h4
  have hX : (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W) = 0 := by
    calc (H⁻¹ * Wᴴ * H * W)ᴴ * H * (H⁻¹ * Wᴴ * H * W)
        = Wᴴ * H * (W * (H⁻¹ * Wᴴ * H)) * W := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, hHh, hHih,
            Matrix.mul_assoc, hc]
      _ = Wᴴ * H * ((H⁻¹ * Wᴴ * H) * W) * W := by rw [← hXW.eq]
      _ = 0 := by simp only [Matrix.mul_assoc, hP, Matrix.mul_zero]
  have hX0 := SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hX
  have hW2 : Wᴴ * H * W = 0 := by
    have h3 : H * (H⁻¹ * Wᴴ * H * W) = Wᴴ * H * W := by simp only [Matrix.mul_assoc, hc']
    rw [← h3, hX0, Matrix.mul_zero]
  exact SimNormSq.eq_zero_of_conjTranspose_mul_mul_eq_zero hH hW2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitudeStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude : ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s → Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ, Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  first | (exact @GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (exact GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (intros; apply GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolySeparableOfNoSqZeroPolynomialImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolySeparableOfNoSqZeroPolynomialImage
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.LKCx

theorem minpoly_separable_of_sq_zero_free
    (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C]
    (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hψ : ∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) (c : C)
    (hc : ∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 →
      Polynomial.aeval (ψ c) P = 0) :
    (minpoly F c).Separable := by
  haveI : CharZero F := (RingHom.charZero_iff σ.injective).2 inferInstance
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective ψ := ψ.injective
  have hcomp : ψ.comp (algebraMap F C) = (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).comp σ := by
    ext x
    simp only [RingHom.comp_apply, hψ, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  have hev : ∀ Q : Polynomial F, ψ (Polynomial.aeval c Q) = Polynomial.aeval (ψ c) (Q.map σ) := by
    intro Q
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.aeval_def,
      Polynomial.eval₂_map]
  have hint : IsIntegral F c := IsIntegral.of_finite F c
  have hm0 : minpoly F c ≠ 0 := minpoly.ne_zero hint
  rw [PerfectField.separable_iff_squarefree]
  intro g hg
  obtain ⟨h, hh⟩ := hg
  have hQ : Polynomial.aeval c (g * h) = 0 := by
    apply hinj
    rw [map_zero, hev]
    apply hc
    rw [← hev, ← map_mul, ← map_mul]
    have : g * h * (g * h) = minpoly F c * h := by rw [hh]; ring
    rw [this, map_mul, minpoly.aeval, zero_mul, map_zero]
  have hdvd : minpoly F c ∣ g * h := minpoly.dvd F c hQ
  have hgh0 : g * h ≠ 0 := by
    intro h0
    apply hm0
    rw [hh, mul_assoc, h0, mul_zero]
  rw [hh, mul_assoc] at hdvd
  have : g * (g * h) ∣ 1 * (g * h) := by rwa [one_mul]
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hgh0).1 this)

end GlobalTheory.LKCx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolySeparableOfNoSqZeroPolynomialImageStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_separable_of_no_sq_zero_polynomial_image : ∀ (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C] (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ), 0 < n → (∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) → ∀ c : C, (∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 → Polynomial.aeval (ψ c) P = 0) → (minpoly F c).Separable := by
  first | (exact @GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free) | (exact GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free) | (intros; apply GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free  <;> assumption)
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem GlobalTheory.LKCx.minpoly_of_regAf_of_fixL : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : grp G β) (h : G.GAf) (z : PosV G v β), FixL G v β y z.1 → RegAf G (h⁻¹ * toAfF G β x t hx y * h) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
  intro p _ G v hv β hβ hR x t hx y h z hfix hreg
  have hcomm : ∀ a b : G.C, Commute a (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) →
      Commute b (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) → Commute a b := by
    obtain ⟨w, hw⟩ := hreg
    obtain ⟨U, hU⟩ := ubc_val_eq G β x t hx y h w
    rw [hU] at hw
    intro a b ha hb
    let ι : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C := Algebra.TensorProduct.includeRight
    have hinj : Function.Injective ι :=
      Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (w.1.adicCompletion ℚ)).injective
    have e : ι (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
        (1 : w.1.adicCompletion ℚ) ⊗ₜ (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
    have ha' := ha.map ι
    have hb' := hb.map ι
    rw [e] at ha' hb'
    have hab := comm_of_conj U _ hw (ι a) (ι b) ha' hb'
    exact hinj (by rw [map_mul, map_mul]; exact hab.eq)
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have hs : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast y.2.2
  obtain ⟨c0, hc0⟩ := hfix
  obtain ⟨H, hH, hHM⟩ := GlobalTheory.T.similitude_signature_one_preserves_posDef_form G.n (G.gram v) (herm G v β) (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm v) Z _ (G.gram_det v) hv hZ hs (by rw [Complex.ofReal_ratCast]; exact hsim) z.1 c0 z.2 hc0
  have hsq := GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude G.n H _ _ hH hs hHM
  have hsep := GlobalTheory.T.minpoly_separable_of_no_sq_zero_polynomial_image G.F G.C G.n v.embedding (G.psi v) G.n_pos (G.psi_F v) _ hsq
  exact ⟨GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser G.F G.C G.n G.rankC _ hsep hcomm, hsep⟩
