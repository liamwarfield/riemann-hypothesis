module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsRangeOfMonicRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbit
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FinOrbit

theorem exists_algEquiv_shift (E : Subfield ℂ) (z : ℂ) (hz : Transcendental E z) (k : ℕ) :
    ∃ g : ℂ ≃ₐ[E] ℂ, g z = z + k := by
  classical
  have hind : AlgebraicIndepOn E id ({z} : Set ℂ) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using hz
  obtain ⟨B, hzB, hB⟩ := exists_isTranscendenceBasis_superset hind
  have hzB' : z ∈ B := hzB rfl
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hB
  let b0 : B := ⟨z, hzB'⟩
  let f : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i + (k : MvPolynomial B E)
    else MvPolynomial.X i
  let f' : B → MvPolynomial B E := fun i => if i = b0 then MvPolynomial.X i - (k : MvPolynomial B E)
    else MvPolynomial.X i
  let n : MvPolynomial B E ≃ₐ[E] MvPolynomial B E :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f')
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
      (by ext i; by_cases h : i = b0 <;> simp [f, f', h])
  let e := (hB.1.aevalEquiv.symm.trans (n.trans hB.1.aevalEquiv))
  let g0 := IsAlgClosure.equivOfEquiv ℂ ℂ e.toRingEquiv
  have hcomm : ∀ c : E, g0 (algebraMap E ℂ c) = algebraMap E ℂ c := by
    intro c
    rw [IsScalarTower.algebraMap_apply E (Algebra.adjoin E (Set.range ((↑) : B → ℂ))) ℂ,
      IsAlgClosure.equivOfEquiv_algebraMap]
    simp
  refine ⟨AlgEquiv.ofRingEquiv (f := g0) hcomm, ?_⟩
  have h1 : algebraMap _ ℂ (hB.1.aevalEquiv (MvPolynomial.X b0)) = z := by
    rw [hB.1.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  show g0 z = z + k
  conv_lhs => rw [← h1]
  rw [IsAlgClosure.equivOfEquiv_algebraMap]
  have : e.toRingEquiv (hB.1.aevalEquiv (MvPolynomial.X b0))
      = hB.1.aevalEquiv (MvPolynomial.X b0 + (k : MvPolynomial B E)) := by
    simp [e, n, f]
  rw [this, map_add (f := _), map_natCast, map_add (f := _), map_natCast, h1]

theorem isAlgebraic_of_finite_orbit :
    ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  intro E x hfin
  by_contra hx
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => x + (k : ℂ)) _ _ hfin
  · intro a b hab
    simpa using hab
  · intro k
    obtain ⟨g, hg⟩ := exists_algEquiv_shift E x hx k
    exact ⟨g, hg⟩

end GlobalTheory.FinOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfFiniteComplexAutomorphismOrbitStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit : ∀ (E : Subfield ℂ) (x : ℂ), (Set.range fun g : ℂ ≃ₐ[E] ℂ => g x).Finite → IsAlgebraic E x := by
  first | exact @GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit | exact GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit | (intros; apply GlobalTheory.FinOrbit.isAlgebraic_of_finite_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRoot
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.PsRoot

theorem mem_of_isAlgebraic_of_isAlgClosed (E : Subfield ℂ) [IsAlgClosed E] {x : ℂ}
    (hx : IsAlgebraic E x) : x ∈ E := by
  have hi : IsIntegral E x := hx.isIntegral
  have h1 : (minpoly E x).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible E (minpoly.irreducible hi)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨y, hy⟩ := (minpoly.natDegree_eq_one_iff).1 h1
  rw [← hy]
  exact y.2

theorem coeff_mem_range_of_isRoot : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)
    (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 →
    (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 →
    ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  intro Ω _ _ ε b Q hQ hcoef hb k
  let E : Subfield ℂ := ε.fieldRange
  haveI : IsAlgClosed E := IsAlgClosed.of_ringEquiv Ω E ε.rangeRestrictFieldEquiv
  have hE : ∀ z : ℂ, z ∈ ε.range → z ∈ E := fun z hz => by
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, rfl⟩

  have hroot : ∀ g : ℂ ≃ₐ[E] ℂ, Q.IsRoot (PowerSeries.map (g : ℂ →+* ℂ) b) := by
    intro g
    have hfix : Q.map (PowerSeries.map (g : ℂ →+* ℂ)) = Q := by
      ext i j
      rw [Polynomial.coeff_map, PowerSeries.coeff_map]
      obtain ⟨y, hy⟩ := hE _ (hcoef i j)
      rw [← hy]
      exact g.commutes ⟨_, ⟨y, rfl⟩⟩
    have h2 := Polynomial.eval_map_apply (PowerSeries.map (g : ℂ →+* ℂ)) (p := Q) b
    show Q.eval _ = 0
    rw [hfix, hb, map_zero] at h2
    exact h2
  have hfin : (Set.range fun g : ℂ ≃ₐ[E] ℂ => g (PowerSeries.coeff k b)).Finite := by
    refine ((Polynomial.finite_setOf_isRoot hQ).image (PowerSeries.coeff k)).subset ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨PowerSeries.map (g : ℂ →+* ℂ) b, hroot g, ?_⟩
    simp [PowerSeries.coeff_map]
  obtain ⟨y, hy⟩ := mem_of_isAlgebraic_of_isAlgClosed E (GlobalTheory.T.isAlgebraic_of_finite_complex_automorphism_orbit E _ hfin)
  exact ⟨y, hy⟩

end GlobalTheory.PsRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffMemRangeOfIsRootStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_range_of_isRoot_of_coeff_mem_range : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (b : PowerSeries ℂ) (Q : Polynomial (PowerSeries ℂ)), Q ≠ 0 → (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range) → Q.eval b = 0 → ∀ k, PowerSeries.coeff k b ∈ ε.range := by
  first | exact @GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | exact GlobalTheory.PsRoot.coeff_mem_range_of_isRoot | (intros; apply GlobalTheory.PsRoot.coeff_mem_range_of_isRoot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsRangeOfMonicRoot
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem qAll_isBoundedAtImInfty {p : ℂ → Prop} {N : ℕ} {f : ℍ → ℂ} (hN : 0 < N) (h : QAll p N f) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  obtain ⟨a, ha, -⟩ := h
  exact (GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN ha).2

theorem isBoundedAtImInfty_of_monic_root {n : ℕ} {h : ℍ → ℂ} {s : Fin n → ℍ → ℂ}
    (hs : ∀ j, UpperHalfPlane.IsBoundedAtImInfty (s j))
    (hrel : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) : UpperHalfPlane.IsBoundedAtImInfty h := by
  have hb : ∀ τ, ‖h τ‖ ≤ 1 + ∑ j, ‖s j τ‖ := fun τ => GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff n (fun j => s j τ) (h τ) (hrel τ)
  have hsum : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
    refine Asymptotics.IsBigO.add (Asymptotics.isBigO_refl _ _) ?_
    convert Asymptotics.IsBigO.sum (A := fun j τ => ‖s j τ‖) (s := Finset.univ) (fun j _ => (hs j).norm_left) using 1
    ext τ; simp [Finset.sum_apply]
  refine Asymptotics.IsBigO.trans (Asymptotics.isBigO_of_le _ fun τ => ?_) hsum
  refine (hb τ).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

end GlobalTheory.FN

namespace GlobalTheory.FN

theorem qAll_range_of_monic_root : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (N n : ℕ) (h : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ) → (∀ j, QAll (· ∈ ε.range) N (s j)) → (∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) → QAll (· ∈ ε.range) N h := by
  intro Ω _ _ ε N n h s hN hh hper hs hrel
  obtain ⟨b, hb⟩ := GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic N h hN hh hper
    (isBoundedAtImInfty_of_monic_root (fun j => qAll_isBoundedAtImInfty hN (hs j)) hrel)
  choose a ha hain using hs
  let p : ℕ → ℍ → ℂ := fun i => if hi : i < n then s ⟨i, hi⟩ else fun _ => 1
  let c : ℕ → ℕ → ℂ := fun i => if hi : i < n then a ⟨i, hi⟩ else fun k => if k = 0 then 1 else 0
  have hp : ∀ i, HasQ N (p i) (c i) := by
    intro i
    by_cases hi : i < n
    · simpa [p, c, hi] using ha ⟨i, hi⟩
    · simpa [p, c, hi] using HasQ.const N 1
  have hrel' : ∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * h τ ^ i = 0 := by
    intro τ
    rw [Finset.sum_range_succ, Finset.sum_range, add_comm, ← hrel τ]
    simp [p]
  have hQ := GlobalTheory.T.polynomial_relation_passes_to_qExpansions N n h b p c hN hb hp hrel'
  set Q := ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i)) with hQdef
  have hcoeff : ∀ i, Q.coeff i = if i < n + 1 then PowerSeries.mk (c i) else 0 := by
    intro i
    rw [hQdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial, Finsupp.single_apply]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) i (fun j => PowerSeries.mk (c j))]
    simp
  have hcn : PowerSeries.mk (c n) = 1 := by
    ext k
    simp [c, PowerSeries.coeff_one]
  have hQ0 : Q ≠ 0 := by
    intro h0
    have := hcoeff n
    rw [h0, if_pos (Nat.lt_succ_self n), hcn] at this
    simp at this
  have hcr : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range := by
    intro i k
    rw [hcoeff i]
    split_ifs with hi
    · rw [PowerSeries.coeff_mk]
      by_cases hin : i < n
      · simpa [c, hin] using hain ⟨i, hin⟩ k
      · simp only [c, hin, dite_false]
        split_ifs
        · exact ⟨1, map_one ε⟩
        · exact ⟨0, map_zero ε⟩
    · simp only [map_zero]
      exact ⟨0, map_zero ε⟩
  have key := GlobalTheory.T.coeff_mem_range_of_isRoot_of_coeff_mem_range Ω ε (PowerSeries.mk b) Q hQ0 hcr hQ
  exact ⟨b, hb, fun k => by simpa using key k⟩

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsRangeOfMonicRootStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_range_of_monic_root : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (N n : ℕ) (h : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ) → (∀ j, QAll (· ∈ ε.range) N (s j)) → (∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) → QAll (· ∈ ε.range) N h := by
  first | exact @GlobalTheory.FN.qAll_range_of_monic_root | exact GlobalTheory.FN.qAll_range_of_monic_root | (intros; apply GlobalTheory.FN.qAll_range_of_monic_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverOfIntegralInvariant
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

private theorem gamma_le_of_dvd' {N N' : ℕ} (hd : N ∣ N') :
    CongruenceSubgroup.Gamma N' ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ x : ℤ, (x : ZMod N) = ZMod.castHom hd (ZMod N) (x : ZMod N') := fun x => by
    rw [map_intCast]
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, h1, map_one]
  · rw [key, h2, map_zero]
  · rw [key, h3, map_zero]
  · rw [key, h4, map_one]

theorem exists_common_lv {E : Subring ℂ} {n : ℕ} (M : ℕ) (hM : 0 < M) (r : Fin n → ℍ → ℂ)
    (hr : ∀ j, InR E (r j)) : ∃ N w : ℕ, 0 < N ∧ M ∣ N ∧ ∀ j, Lv E N w (r j) := by
  choose Nj wj hNj hLv using hr
  have hpos : 0 < M * ∏ j, Nj j := Nat.mul_pos hM (Finset.prod_pos fun j _ => hNj j)
  refine ⟨M * ∏ j, Nj j, ∑ j, wj j, hpos, dvd_mul_right _ _, fun j => ?_⟩
  exact GlobalTheory.T.lv_mono_of_dvd_of_le E (Nj j) _ (wj j) _ (r j) hpos
    (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) M)
    (Finset.single_le_sum (fun i _ => Nat.zero_le (wj i)) (Finset.mem_univ j)) (hLv j)

theorem mdifferentiable_DD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) DD := CuspForm.discriminant.holo'

theorem mdifferentiable_comp_smul {h : ℍ → ℂ} (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun τ => h (γ • τ) := by
  have e : (fun τ => h (γ • τ)) = h ∣[(0 : ℤ)] γ := by
    funext τ
    rw [ModularForm.SL_slash_apply]
    simp
  rw [e]
  exact hh.slash 0 _

theorem DD_vadd (N : ℕ) (τ : ℍ) : DD ((N : ℝ) +ᵥ τ) = DD τ := by
  have hT : (ModularGroup.T ^ (N : ℤ)) • τ = (N : ℝ) +ᵥ τ := by
    rw [UpperHalfPlane.modular_T_zpow_smul]; simp
  have hden : UpperHalfPlane.denom (ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) τ = 1 := by
    rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
  rw [← hT, ReciprocityTheory.ChartRestriction.L1.DD_smul, hden, one_pow, one_mul]

theorem comp_smul_vadd {N : ℕ} {h : ℍ → ℂ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, h (γ • τ) = h τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    h (γ • ((N : ℝ) +ᵥ τ)) = h (γ • τ) := by
  have hT : (ModularGroup.T ^ (N : ℤ)) • τ = (N : ℝ) +ᵥ τ := by
    rw [UpperHalfPlane.modular_T_zpow_smul]; simp
  have h1 : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
  have h2 := (CongruenceSubgroup.Gamma_normal N).conj_mem _ h1 γ
  rw [← hT, ← mul_smul,
    show γ * ModularGroup.T ^ (N : ℤ) = (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) * γ by group, mul_smul]
  exact hinv _ h2 _

theorem inR_of_integral : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (h : ℍ → ℂ)
    (r : Fin n → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, h (γ • τ) = h τ) → (∀ j, InR ε.range (r j)) →
    (∀ τ, h τ ^ n + ∑ j, r j τ * h τ ^ (j : ℕ) = 0) → InR ε.range h := by
  intro Ω _ _ ε M n h r hM hh hinv hr heq
  obtain ⟨N, w, hN, hMN, hlv⟩ := exists_common_lv M hM r hr
  have hinvN : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, h (γ • τ) = h τ :=
    fun γ hγ τ => hinv γ (gamma_le_of_dvd' hMN hγ) τ
  refine ⟨N, w, hN, hinvN, fun γ => ?_⟩
  have hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => DD τ ^ w * h (γ • τ)) :=
    (mdifferentiable_DD.pow w).mul (mdifferentiable_comp_smul hh γ)
  have hper : ∀ τ : ℍ, DD ((N : ℝ) +ᵥ τ) ^ w * h (γ • ((N : ℝ) +ᵥ τ)) = DD τ ^ w * h (γ • τ) := by
    intro τ; rw [DD_vadd, comp_smul_vadd hinvN γ τ]
  let s : Fin n → ℍ → ℂ := fun j τ => DD τ ^ (w * (n - (j : ℕ))) * r j (γ • τ)
  have hs : ∀ j, QAll (· ∈ ε.range) N (s j) := by
    intro j
    have h1 := (hlv j).2 γ
    have h2 : QAll (· ∈ ε.range) N fun τ => DD τ ^ (w * (n - 1 - (j : ℕ))) :=
      QAllSubring.pow _ (eis_qAll N hN DD (Or.inr (Or.inr rfl)) ε.range)
    refine (congrArg (QAll (· ∈ ε.range) N) (funext fun τ => ?_)).mp (QAllSubring.mul h2 h1)
    have hj := j.isLt
    have e : w * (n - 1 - (j : ℕ)) + w = w * (n - (j : ℕ)) := by
      rw [← Nat.mul_succ]; congr 1; omega
    simp only [s]
    rw [← mul_assoc, ← pow_add, e]
  have heqH : ∀ τ, (DD τ ^ w * h (γ • τ)) ^ n +
      ∑ j, s j τ * (DD τ ^ w * h (γ • τ)) ^ (j : ℕ) = 0 := by
    intro τ
    have e := heq (γ • τ)
    calc _ = DD τ ^ (w * n) * (h (γ • τ) ^ n + ∑ j, r j (γ • τ) * h (γ • τ) ^ (j : ℕ)) := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          · rw [mul_pow, pow_mul]
          · refine Finset.sum_congr rfl fun j _ => ?_
            have hj := j.isLt
            have e2 : w * n = w * (n - (j : ℕ)) + w * (j : ℕ) := by
              rw [← Nat.mul_add]; congr 1; omega
            simp only [s]
            rw [e2, pow_add, mul_pow, ← pow_mul]; ring
      _ = 0 := by rw [e, mul_zero]
  exact GlobalTheory.T.qExpansionAllCoeffs_range_of_monic_root Ω ε N n _ s hN hH hper hs heqH

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverOfIntegralInvariantStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSomeLevelOver_of_integral_invariant : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (h : ℍ → ℂ) (r : Fin n → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, h (γ • τ) = h τ) → (∀ j, InR ε.range (r j)) → (∀ τ, h τ ^ n + ∑ j, r j τ * h τ ^ (j : ℕ) = 0) → InR ε.range h := by
  first | exact @GlobalTheory.FN.inR_of_integral | exact GlobalTheory.FN.inR_of_integral | (intros; apply GlobalTheory.FN.inR_of_integral <;> assumption)
end
