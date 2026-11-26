module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthComposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTestDivisorsKltLcPencilBoundaries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeight
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GdegMetric

theorem coeff_eq_zero_of_const (N : ℕ) (γ : ℕ → ℝ) (K : ℝ)
    (h : ∀ c : ℕ, ∑ m ∈ Finset.range (N + 1), (c : ℝ) ^ m * γ m = K) {m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    γ m = 0 := by
  let P : Polynomial ℝ := ∑ j ∈ Finset.range (N + 1), Polynomial.C (γ j) * Polynomial.X ^ j
  have hP : P = Polynomial.C K := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.infinite_of_injective_forall_mem (f := fun c : ℕ => (c : ℝ)) Nat.cast_injective fun c => ?_
    simp only [Set.mem_ofPred_eq, P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h c]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e := congrArg (fun Q : Polynomial ℝ => Q.coeff m) hP
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C] at e
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) m, if_pos (Finset.mem_range.2 (by omega)),
    if_neg (by omega)] at e
  exact e

theorem map_mul_add_pow {ι : Type} (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (A x y : MvPolynomial ι ℝ) (c : ℝ) (n : ℕ) :
    Φ (A * (MvPolynomial.C c * x + y) ^ n) =
      ∑ m ∈ Finset.range (n + 1), c ^ m * ((n.choose m : ℝ) * Φ (A * x ^ m * y ^ (n - m))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : A * ((MvPolynomial.C c * x) ^ m * y ^ (n - m) * (n.choose m : MvPolynomial ι ℝ)) =
      (c ^ m * (n.choose m : ℝ)) • (A * x ^ m * y ^ (n - m)) := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, map_natCast, mul_pow, ← map_pow]
    ring
  rw [e, map_smul, smul_eq_mul]
  ring

end GlobalTheory.GdegMetric

namespace GlobalTheory.GdegMetric

open MvPolynomial HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem lin_single' {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) :
    (lin fun j => (((Pi.single i 1 : ι → ℤ) j : ℤ) : ℝ)) = MvPolynomial.X i := by
  simp [lin, Pi.single_apply, apply_ite, ite_mul]

theorem isConj_const_mul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ}
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (c : ℝ) (σ σ' : k →+* ℂ) :
    (Weight.ofFun fun y => c * u σ y).IsConj (Weight.ofFun fun y => c * u σ' y) :=
  fun i y y' h hy => congrArg (c * ·) (hc σ σ' i y y' h hy)

theorem icls_fnB_sum {u v w : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu hc hv hd hw he) (e : ∀ σ y, w σ y = u σ y + v σ y) :
    (fnB w hw he).icls = (fnB u hu hc).icls + (fnB v hv hd).icls := by
  rw [← icls_tens, icls_eq_iff.2 (isometric_tens_fnB _ v hv hd)]
  exact icls_eq_iff.2 (isometric_of_eqOn fun σ _ y _ => (e σ y).symm)

theorem icls_fnB_zsmul {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (n : ℤ) :
    (fnB (fun σ y => (n : ℝ) * u σ y) (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _)).icls =
      n • (fnB u hu hc).icls := by
  have key (m : ℤ) := icls_fnB_sum (p := p) (w := fun σ y => ((m + 1 : ℤ) : ℝ) * u σ y)
    (u := fun σ y => (m : ℝ) * u σ y)
    (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc (fun σ y => (hu σ y).const_mul _)
    (isConj_const_mul hc _) fun σ y => by push_cast; ring
  induction n using Int.induction_on with
  | zero =>
    have := icls_fnB_sum (p := p) (w := u) (u := fun σ y => ((0 : ℤ) : ℝ) * u σ y)
      (fun σ y => (hu σ y).const_mul _) (isConj_const_mul hc _) hu hc hu hc fun σ y => by push_cast; ring
    rw [zero_smul]
    exact right_eq_add.1 this
  | succ n ih => rw [key, ih, add_smul, one_smul]
  | pred n ih =>
    have := key (-(n : ℤ) - 1)
    simp only [sub_add_cancel] at this
    rw [sub_smul, one_smul, ← ih, this, add_sub_cancel_right]

theorem chInt_raise_const (N : HermLB p) (t : ℝ) (hu : ∀ σ (y : CxPts p σ), CInfAt (fun _ => t) y) (hc) (D : ℕ)
    (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) :
    chInt (N.raise (fun _ _ => t) hu hc) D f = chInt N D f := by
  simp only [chInt, HermLB.raise, Weight.chernInt, Weight.chernPart_addFn_const]

end GlobalTheory.GdegMetric

namespace GlobalTheory.GdegMetric

open MvPolynomial HermLB

theorem gdeg_up : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p), gdeg (up L u) D = gdeg L D := by
  intro HC k _ S _ p D hX L u
  classical
  let one : ∀ σ : k →+* ℂ, CxPts p σ → ℝ := fun _ _ => 1
  have h1 : ∀ σ (y : CxPts p σ), CInfAt (one σ) y := fun σ y => cInfAt_const 1 y
  have hc1 : ∀ σ σ', (Weight.ofFun (one σ)).IsConj (Weight.ofFun (one σ')) := fun _ _ _ _ _ _ _ => rfl
  let T : HermLB p := fnB one h1 hc1
  let U : HermLB p := fnB u.u u.cInf u.conj
  let G : Fin 3 → HermLB p := ![T, L, U]
  obtain ⟨Φ, hΦ⟩ := ((HC.arExists k S p D hX).2 _ G).1
  let eA : Option (Fin 3) → Fin 3 := fun o => o.elim 2 id
  have hA : IsArFun (fun o : Option (Fin 3) => o.elim U G) D
      (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eA o) : MvPolynomial (Fin 3) ℝ)).toLinearMap) := by
    have := ((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 3)) (fun o => o.elim U G)
      (fun o => Pi.single (eA o) 1) fun o => by
        rcases o with _ | j
        · exact isometric_comb_single G 2
        · exact isometric_comb_single G j
    simpa only [lin_single'] using this
  let eB : Option (Fin 2) → Fin 3 := fun o => o.elim 0 Fin.succ
  have hB : IsArFun (fun o : Option (Fin 2) => o.elim T ![L, U]) D
      (Φ ∘ₗ (MvPolynomial.aeval fun o => (MvPolynomial.X (eB o) : MvPolynomial (Fin 3) ℝ)).toLinearMap) := by
    have := ((HC.arIso k S p D hX).2 _ G Φ hΦ).2.2 (Option (Fin 2)) (fun o => o.elim T ![L, U])
      (fun o => Pi.single (eB o) 1) fun o => by
        rcases o with _ | j
        · exact isometric_comb_single G 0
        · fin_cases j
          · exact isometric_comb_single G 1
          · exact isometric_comb_single G 2
    simpa only [lin_single'] using this
  have chA : ∀ c b : ℤ, Φ (X 2 * (C (c : ℝ) * X 0 + (X 1 + C (b : ℝ) * X 2)) ^ D) =
      1 / 2 * chInt (comb G ![c, 1, b]) D u.u := by
    intro c b
    have := HC.arChange k S p D hX (Fin 3) G u.u u.cInf u.conj _ hA ![c, 1, b]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [← this]
    congr 1
    simp [lin, Fin.sum_univ_three, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eA]
    ring
  have chB : ∀ b : ℤ, Φ (X 0 * (X 1 + C (b : ℝ) * X 2) ^ D) = 1 / 2 * gdeg (comb ![L, U] ![1, b]) D := by
    intro b
    have := HC.arChange k S p D hX (Fin 2) ![L, U] one h1 hc1 _ hB ![1, b]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at this
    rw [gdeg, ← this]
    congr 1
    simp [lin, Fin.sum_univ_two, MvPolynomial.aeval_rename, MvPolynomial.algebraMap_eq, eB]

  have iso : ∀ c b : ℤ, (comb G ![c, 1, b]).Isometric ((comb ![L, U] ![1, b]).raise (fun _ _ => (c : ℝ) * 1)
      (fun σ y => cInfAt_const _ y) (fun _ _ _ _ _ _ _ => rfl)) := by
    intro c b
    refine Isometric.trans (icls_eq_iff.1 ?_) (isometric_tens_fnB _ _ _ _)
    rw [icls_tens]
    have e : (fnB (p := p) (fun _ _ => (c : ℝ) * 1) (fun σ y => cInfAt_const _ y)
        (fun _ _ _ _ _ _ _ => rfl)).icls = c • T.icls := icls_fnB_zsmul h1 hc1 c
    rw [e, icls_comb, icls_comb, Fin.sum_univ_three, Fin.sum_univ_two]
    simp [G]
    abel
  have hind : ∀ c b : ℤ, chInt (comb G ![c, 1, b]) D u.u = chInt (comb G ![0, 1, b]) D u.u := by
    intro c b
    rw [(iso c b).chInt_eq, (iso 0 b).chInt_eq]
    exact (chInt_raise_const _ _ _ _ _ _).trans (chInt_raise_const _ _ _ _ _ _).symm
  have i1 : (comb ![L, U] ![1, 1]).Isometric (up L u) := icls_eq_iff.1 (by
    rw [← icls_eq_iff.2 (isometric_tens_fnB L u.u u.cInf u.conj), icls_tens, icls_comb, Fin.sum_univ_two]
    simp [U])
  have i0 : (comb ![L, U] ![1, 0]).Isometric L := icls_eq_iff.1 (by
    rw [icls_comb, Fin.sum_univ_two]
    simp)
  rw [← i1.gdeg_eq, ← i0.gdeg_eq]
  have e1 := chB 1
  have e0 := chB 0
  cases D with
  | zero =>
    simp only [pow_zero, mul_one] at e1 e0
    linarith
  | succ d =>
    have s1 : ∀ b : ℤ, Φ (X 2 * X 0 * (X 1 + C (b : ℝ) * X 2) ^ d) = 0 := by
      intro b
      have h := coeff_eq_zero_of_const (d + 1)
        (fun m => ((d + 1).choose m : ℝ) * Φ (X 2 * X 0 ^ m * (X 1 + C (b : ℝ) * X 2) ^ (d + 1 - m)))
        (1 / 2 * chInt (comb G ![0, 1, b]) (d + 1) u.u) (fun c => by
          beta_reduce
          rw [← map_mul_add_pow, ← hind c b, ← chA c b]
          push_cast
          rfl) (le_refl 1) (by omega)
      simp only [Nat.choose_one_right, pow_one, Nat.add_sub_cancel] at h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h (by positivity)
      · exact h
    have s2 : ∀ m ≤ d, Φ (X 2 * X 0 * X 2 ^ m * X 1 ^ (d - m)) = 0 := by
      intro m hm
      have hs : ∀ c : ℕ, ∑ j ∈ Finset.range (d + 1),
          (c : ℝ) ^ j * ((d.choose j : ℝ) * Φ (X 2 * X 0 * X 2 ^ j * X 1 ^ (d - j))) = 0 := by
        intro c
        rw [← map_mul_add_pow]
        have := s1 c
        rw [add_comm] at this
        push_cast at this
        exact this
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · have := hs 0
        rw [Finset.sum_range_succ'] at this
        simpa using this
      · have h := coeff_eq_zero_of_const d _ 0 hs hm0 hm
        rcases mul_eq_zero.1 h with h | h
        · exact absurd h (by exact_mod_cast (Nat.choose_pos hm).ne')
        · exact h
    have ex := map_mul_add_pow Φ (X 0) (X 2) (X 1) 1 (d + 1)
    rw [Finset.sum_range_succ'] at ex
    have hz : ∀ i ∈ Finset.range (d + 1), (1 : ℝ) ^ (i + 1) * (((d + 1).choose (i + 1) : ℝ) *
        Φ (X 0 * X 2 ^ (i + 1) * X 1 ^ (d + 1 - (i + 1)))) = 0 := by
      intro i hi
      have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [Nat.add_sub_add_right, show (X 0 * X 2 ^ (i + 1) * X 1 ^ (d - i) : MvPolynomial (Fin 3) ℝ) =
        X 2 * X 0 * X 2 ^ i * X 1 ^ (d - i) by ring, s2 i hi', mul_zero, mul_zero]
    rw [Finset.sum_eq_zero hz, zero_add] at ex
    have e1' : Φ (X 0 * (C 1 * X 2 + X 1) ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 1]) (d + 1) := by
      rw [← e1, add_comm]
      push_cast
      rfl
    have e0' : Φ (X 0 * X 1 ^ (d + 1)) = 1 / 2 * gdeg (comb ![L, U] ![1, 0]) (d + 1) := by
      rw [← e0]
      simp
    simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero] at ex
    linarith

end GlobalTheory.GdegMetric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeRaiseWeightStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundleGeometricDegree_raiseWeight : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (u : SmFn p), gdeg (up L u) D = gdeg L D := by
  first | exact @GlobalTheory.GdegMetric.gdeg_up | exact GlobalTheory.GdegMetric.gdeg_up | (intros; apply GlobalTheory.GdegMetric.gdeg_up <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixFin

theorem finite_and_intg : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ), (∀ ε : ℤˣ, IsFiniteMeasure (part L ε)) ∧ ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
  intro hP F _ X _ _ p σ D hX hdim L
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hproj, -, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p D hX hdim ⊥ (fun h => by rwa [← SetLike.mem_coe, Closeds.coe_bot] at h)
  haveI := hY
  haveI : SmoothOfRelativeDimension D (π ≫ p) := hsm
  haveI := CxPts.compactSpace (p := π ≫ p) σ hproj
  haveI := CxPts.t2Space_cxPts_of_isProjOver (p := π ≫ p) σ hproj
  haveI := CxPts.secondCountableTopology_of_isProjOver (p := π ≫ p) σ hproj
  let R := AnRead.all (π ≫ p) σ D
  have key : ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
    intro f hf
    have hf' : Continuous (fun y => f (ptMap π rfl σ y)) := hf.comp (PtsOver.continuous_map _ _ _)
    have h1 := (GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ D R.finAtlas R.isAlgAtlas_finAtlas
      (fun i => (L i).pull π rfl) _ hf'.measurable).1
    have hI := h1.2 (mIntegrableCont _ _ (fun i => Weight.isPotential_locPot
      ((Weight.isCInf_iff_isSmooth R).1 ((L i).pull π rfl).cInf)) _ hf')
    exact ((GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ D hX hdim hproj π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) L f hf.measurable).1).1 hI
  refine ⟨fun ε => ?_, key⟩
  have h := key (fun _ => (1 : ℝ)) continuous_const
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact (integrable_const_iff.1 h.1).resolve_left one_ne_zero
  · exact (integrable_const_iff.1 h.2).resolve_left one_ne_zero

end GlobalTheory.MixFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernMeasure_finite_integrable_projective : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ), (∀ ε : ℤˣ, IsFiniteMeasure (part L ε)) ∧ ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
  first | exact @GlobalTheory.MixFin.finite_and_intg | exact GlobalTheory.MixFin.finite_and_intg | (intros; apply GlobalTheory.MixFin.finite_and_intg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveSectionValueUnitFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveSectionValueUnitFrame
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.ValAdd

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem ratVal_add' {σ : k →+* ℂ} {y : CxPts p σ} {f g : X.functionField} (hf : RegAt (under y) f)
    (hg : RegAt (under y) g) : ratVal (f + g) y = ratVal f y + ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn p σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_add,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_add]

theorem val_add (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) {f g : X.functionField}
    (hf : f ∈ P.H a b) (hg : g ∈ P.H a b) : val P a b σ y (f + g) = val P a b σ y f + val P a b σ y g := by
  have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
  have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
  have e : P.loc a b (f + g) (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) =
      P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) +
        P.loc a b g (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]; ring
  rw [val, val, val, e, ratVal_add' (hf _ _ _ hi hj) (hg _ _ _ hi hj), add_mul]

end GlobalTheory.HSAmp.ValAdd


open GlobalTheory.HSAmp.ValAdd in
theorem GlobalTheory.HSAmp.val_additive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ ℓ : P.H a b →+ ℂ, ∀ f : P.H a b, ℓ f = val P a b σ y f := by
  intro k _ X _ p P a b σ y
  refine ⟨{ toFun := fun f => val P a b σ y f, map_zero' := ?_, map_add' := fun f g => val_add P a b σ y f.2 g.2 }, fun _ => rfl⟩
  have := val_add P a b σ y (zero_mem (P.H a b)) (zero_mem (P.H a b))
  simp only [add_zero] at this
  simpa using this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveSectionValueUnitFrameStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additive_sectionValueUnitFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ ℓ : P.H a b →+ ℂ, ∀ f : P.H a b, ℓ f = val P a b σ y f := by
  first | exact @GlobalTheory.HSAmp.val_additive | exact GlobalTheory.HSAmp.val_additive | (intros; apply GlobalTheory.HSAmp.val_additive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointGenericFibreOfActsStar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjGenericOfCube
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosGeneric

theorem linEnd_of_actsAs {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b : D.toPre.P.A ⟶ D.toPre.P.A} {h : D.toPre.X →+ D.toPre.X} {g : G ⟶ G} [IsMonHom g]
    (hg : ActsAs U b h g) : LinEnd U b h g :=
  ⟨inferInstance, fun _ => inferInstance, fun e => GlobalTheory.Mum.EndModel.thickMap_map g e, fun e => (hg e).1,
    fun e => (hg e).2⟩

theorem rosatiAdj_generic_of_cube (hcube : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ g g' : G ⟶ G, LinEnd U.toUnifPre a h' g → LinEnd U.toUnifPre a' h g' → LBIso (cubeLB G ![fst G G ≫ g, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ g'] U.LG.L)) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g → ActsAs U.toUnifPre (o.onB.act (star a)) (fun χ => star (star a) • χ) g' → RosatiAdj A.A A.L (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom) (U.gen.inv ≫ (Over.pullback (jK R)).map g' ≫ U.gen.hom) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o a g g' hg hg' ag ag'
  have hE := GlobalTheory.Mum.EndModel.endData_of_oAct O D.toPre o a
  have l1 : LinEnd U.toUnifPre (o.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) g :=
    linEnd_of_actsAs U.toUnifPre ag
  have l2 : LinEnd U.toUnifPre (o.onB.act (star a)) (DistribSMul.toAddMonoidHom D.toPre.X a) g' := by
    have := linEnd_of_actsAs (h := DistribSMul.toAddMonoidHom D.toPre.X (star (star a))) U.toUnifPre ag'
    simpa only [star_star] using this
  have H := hcube R hR D A G hG U _ _ _ _ hE g g' l1 l2
  obtain ⟨u, hu⟩ := (GlobalTheory.NormRos.normRos_of_lbIso _ G U.LG.L U.LG.isLB g g' H).1
  have := U.gen_hom
  exact GlobalTheory.EndRosati.rosatiAdj_generic U.toUnifPre (by simp) (by simp) u hu.1

end GlobalTheory.Mum.RosGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointGenericFibreOfActsStar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RosGeneric

theorem rosatiAdj_generic_of_actsAs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g → ActsAs U.toUnifPre (o.onB.act (star a)) (fun χ => star (star a) • χ) g' → RosatiAdj A.A A.L (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom) (U.gen.inv ≫ (Over.pullback (jK R)).map g' ≫ U.gen.hom) :=
  rosatiAdj_generic_of_cube GlobalTheory.T.uniformisedGroup_endomorphisms_adjoint_pair

end GlobalTheory.Mum.RosGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointGenericFibreOfActsStarStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiAdjoint_genericFibre_of_acts_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (a : O) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre (o.onB.act a) (fun χ => star a • χ) g → ActsAs U.toUnifPre (o.onB.act (star a)) (fun χ => star (star a) • χ) g' → RosatiAdj A.A A.L (U.gen.inv ≫ (Over.pullback (jK R)).map g ≫ U.gen.hom) (U.gen.inv ≫ (Over.pullback (jK R)).map g' ≫ U.gen.hom) := by
  first | exact @GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs | exact GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs | (intros; apply GlobalTheory.Mum.RosGeneric.rosatiAdj_generic_of_actsAs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadratic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadratic
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pull_zsmul_of_symm : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (f : B ⟶ A) (n : ℤ), AbVar.lam c f.hom f.hom = 2 • CechPic.pull f.hom.left c ∧ CechPic.pull (Hom.hom (n • f)).left c = (n ^ 2) • CechPic.pull f.hom.left c := by
  intro K _ B A c hc f n
  have bil := GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c B.X

  have h1 : CechPic.pull (1 : B.X ⟶ A.X).left c = 0 := by
    have e := (bil 1 1 1 0).2.1
    simp only [AbVar.lam, _root_.mul_one, sub_self, zero_sub, neg_eq_zero] at e
    exact e

  have hinv : ∀ y : B.X ⟶ A.X, CechPic.pull (y⁻¹).left c = CechPic.pull y.left c := by
    intro y
    have hc' : CechPic.pull ((𝟙 A.X)⁻¹).left c = c := hc
    rw [show y⁻¹ = y ≫ (𝟙 A.X)⁻¹ by rw [GrpObj.comp_inv, Category.comp_id], Over.comp_left, pull_comp, hc']

  have hmul : ∀ y z : B.X ⟶ A.X, CechPic.pull (y * z).left c =
      AbVar.lam c y z + CechPic.pull y.left c + CechPic.pull z.left c := by
    intro y z
    simp only [AbVar.lam]
    abel
  set x := f.hom with hx
  have key : AbVar.lam c x x = 2 • CechPic.pull x.left c := by
    have e := (bil x x 1 (-1)).2.2.2.2
    rw [zpow_neg_one] at e
    have e2 := hmul x x⁻¹
    rw [_root_.mul_inv_cancel, h1, hinv, e] at e2
    have e3 : AbVar.lam c x x - 2 • CechPic.pull x.left c =
        -((-1 : ℤ) • AbVar.lam c x x + CechPic.pull x.left c + CechPic.pull x.left c) := by module
    rw [← sub_eq_zero, e3, ← e2, neg_zero]
  refine ⟨key, ?_⟩
  have step : ∀ m : ℤ, CechPic.pull (x ^ (m + 1)).left c =
      CechPic.pull (x ^ m).left c + (2 * m + 1) • CechPic.pull x.left c := by
    intro m
    rw [zpow_add_one, hmul, (bil x x 1 m).2.2.2.1, key]
    module
  change CechPic.pull (x ^ n).left c = (n ^ 2) • CechPic.pull x.left c
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, h1]; simp
  | succ m ih =>
    rw [step, ih]
    module
  | pred m ih =>
    have e := step (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih] at e
    rw [eq_sub_of_add_eq e.symm]
    module

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadraticStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (f : B ⟶ A) (n : ℤ), AbVar.lam c f.hom f.hom = 2 • CechPic.pull f.hom.left c ∧ CechPic.pull (Hom.hom (n • f)).left c = (n ^ 2) • CechPic.pull f.hom.left c := by
  first | (exact @GlobalTheory.AV.AbVar.pull_zsmul_of_symm) | (exact GlobalTheory.AV.AbVar.pull_zsmul_of_symm) | (intros; apply GlobalTheory.AV.AbVar.pull_zsmul_of_symm  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralQuotientRingSectionTupleLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralQuotientRingSectionTupleLocus
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.FnInt

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (l : Fin (D + 1)) (w : X.functionField), x l ≠ 0 → (∀ z ∈ NV P e 0 (x l), RegAt z w) → IsIntegral (ratR x l) w := by
  intro k _ X _ p D hA P e x hG l w hl hw
  have : IsProper p := by
    obtain ⟨m, i, hi, rfl⟩ := hA.isProjOver
    have := isProper_str k m
    infer_instance
  have hmem : w ∈ (integralClosure (Subring.closure (Set.range fun j => x j / x l)) X.functionField).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    rintro ⟨V, hV⟩
    change w ∈ V
    have hk : ∀ a : k, toFunctionField p a ∈ V := by
      intro a
      have := hA.finite
      have h1 : IsIntegral ℤ (toFunctionField p a) :=
        (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (toFunctionField p).toIntAlgHom
      have h2 : IsIntegral V (toFunctionField p a) := h1.tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
      rw [← hy]; exact y.2
    have hd := dominatesStalk_centre p V hk
    obtain ⟨j, hj⟩ := hG.cover (centre p V hk)
    have hz : centre p V hk ∈ NV P e 0 (x l) := by
      intro i i' hi hi'
      have hu := hj i i' hi hi'
      have hr := hG.mem l (centre p V hk) i i' hi hi'
      have hne := hu.ne_zero
      have hxj : x j ≠ 0 := fun h0 => hne (by simp [Pair.loc, h0])
      have hloc : P.loc (e : ℤ) 0 (x l) i i' = x l / x j * P.loc (e : ℤ) 0 (x j) i i' := by
        simp only [Pair.loc]; field_simp
      have hg : RegAt (centre p V hk) (x l / x j) := by
        have : x l / x j = P.loc (e : ℤ) 0 (x l) i i' * (P.loc (e : ℤ) 0 (x j) i i')⁻¹ := by
          rw [hloc, mul_assoc, mul_inv_cancel₀ hne, mul_one]
        rw [this]; exact hr.mul hu.inv.regAt
      have hgu : UnitAt (centre p V hk) (x l / x j) := by
        by_contra hn
        obtain ⟨a, ha, hag⟩ := zeroAt_iff.2 ⟨hg, hn⟩
        have h1 := hd.2 a ha
        rw [hag] at h1
        have hgV : x l / x j ∈ V := by rw [← hag]; exact hd.1 a
        have h2 : (x l / x j)⁻¹ ∈ V := by
          rw [inv_div]; exact hV ⟨j, rfl⟩
        have hgne : x l / x j ≠ 0 := div_ne_zero hl hxj
        have hu' : IsUnit (⟨x l / x j, hgV⟩ : V) := by
          refine ⟨⟨⟨_, hgV⟩, ⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ hgne), Subtype.ext (inv_mul_cancel₀ hgne)⟩, rfl⟩
        exact (V.coe_mem_nonunits_iff (a := ⟨_, hgV⟩)).mp h1 hu'
      rw [hloc]; exact hgu.mul hu
    obtain ⟨a, ha⟩ := hw _ hz
    rw [← ha]; exact hd.1 a
  exact hmem

end GlobalTheory.FnInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralQuotientRingSectionTupleLocusStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_quotientRing_sectionTuple_locus : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (l : Fin (D + 1)) (w : X.functionField), x l ≠ 0 → (∀ z ∈ NV P e 0 (x l), RegAt z w) → IsIntegral (ratR x l) w := by
  first | exact @GlobalTheory.FnInt.main | exact GlobalTheory.FnInt.main | (intros; apply GlobalTheory.FnInt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitian
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem exists_unitary_conj_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    ∃ U : Matrix ι ι ℂ, Uᴴ * U = 1 ∧
      Uᴴ * A * U = Matrix.diagonal fun i => (hA.eigenvalues i : ℂ) := by
  have h1 : (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    have := hA.eigenvectorUnitary.2.1
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨hA.eigenvectorUnitary, h1, ?_⟩
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have h2 : Uᴴ * A * U = D := by
    rw [h, Matrix.star_eq_conjTranspose]
    calc Uᴴ * (U * D * Uᴴ) * U = (Uᴴ * U) * D * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = D := by rw [h1]; simp
  rw [h2, hD]; rfl

theorem simultaneous_diagonalisation :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G G' : Matrix ι ι ℂ), G.PosDef → G'.IsHermitian →
      ∃ (T : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit T.det ∧ Tᴴ * G * T = 1 ∧
        Tᴴ * G' * T = Matrix.diagonal fun i => (d i : ℂ) := by
  intro ι _ _ G G' hG hG'
  obtain ⟨U, hU, hUG⟩ := exists_unitary_conj_diagonal G hG.1
  have hpos : ∀ i, 0 < hG.1.eigenvalues i := hG.eigenvalues_pos
  set S : Matrix ι ι ℂ := Matrix.diagonal fun i => (((Real.sqrt (hG.1.eigenvalues i))⁻¹ : ℝ) : ℂ)
    with hS
  have hSH : Sᴴ = S := by
    rw [hS, Matrix.diagonal_conjTranspose]
    congr 1
    ext i
    simp
  have h0 : (U * S)ᴴ * G * (U * S) = 1 := by
    have : (U * S)ᴴ * G * (U * S) = S * (Uᴴ * G * U) * S := by
      rw [Matrix.conjTranspose_mul, hSH]; simp only [Matrix.mul_assoc]
    rw [this, hUG, hS, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    have hs : 0 < Real.sqrt (hG.1.eigenvalues i) := Real.sqrt_pos.2 (hpos i)
    have hs2 := Real.mul_self_sqrt (hpos i).le
    have : (Real.sqrt (hG.1.eigenvalues i))⁻¹ * hG.1.eigenvalues i *
        (Real.sqrt (hG.1.eigenvalues i))⁻¹ = 1 := by
      field_simp
      nlinarith
    exact_mod_cast this
  have hH : ((U * S)ᴴ * G' * (U * S)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul _ hG'
  obtain ⟨V, hV, hVG⟩ := exists_unitary_conj_diagonal _ hH
  have h1 : (U * S * V)ᴴ * G * (U * S * V) = 1 := by
    have : (U * S * V)ᴴ * G * (U * S * V) = Vᴴ * ((U * S)ᴴ * G * (U * S)) * V := by
      rw [Matrix.conjTranspose_mul (U * S) V]; simp only [Matrix.mul_assoc]
    rw [this, h0, Matrix.mul_one, hV]
  refine ⟨U * S * V, hH.eigenvalues, ?_, h1, ?_⟩
  · exact Matrix.isUnit_det_of_left_inverse h1
  · rw [← hVG, Matrix.conjTranspose_mul (U * S) V]; simp only [Matrix.mul_assoc]

end GlobalTheory.HSAmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimultaneousDiagonalisationPosDefHermitianStatement
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_simultaneous_diagonalisation_posDef_hermitian : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G G' : Matrix ι ι ℂ), G.PosDef → G'.IsHermitian → ∃ (T : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit T.det ∧ Tᴴ * G * T = 1 ∧ Tᴴ * G' * T = Matrix.diagonal fun i => (d i : ℂ) := by
  first | exact @GlobalTheory.HSAmp.simultaneous_diagonalisation | exact GlobalTheory.HSAmp.simultaneous_diagonalisation | (intros; apply GlobalTheory.HSAmp.simultaneous_diagonalisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosKltAddSmulEffectiveDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosKltAddSmulEffectiveDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_pos_mul_lt_of_finite {ι : Type*} {T : Set ι} (hT : T.Finite) (A O : ι → ℚ)
    (hA : ∀ t ∈ T, 0 < A t) : ∃ c : ℚ, 0 < c ∧ ∀ t ∈ T, c * O t < A t := by
  have h : ∀ᶠ c in nhdsWithin (0 : ℚ) (Set.Ioi 0), ∀ t ∈ T, c * O t < A t :=
    (Filter.eventually_all_finite hT).2 fun t ht => by
      have h1 : Filter.Tendsto (fun c : ℚ => c * O t) (nhds 0) (nhds (0 * O t)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h1
      exact nhdsWithin_le_nhds (h1.eventually (gt_mem_nhds (hA t ht)))
  obtain ⟨c, hc, hc'⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨c, hc', hc⟩

theorem exists_pos_kltAt_add_smul : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (B : X → ℚ), 0 < m → IsLogCanonicalMultiple p n Δ m G → (∀ y, KltAt p n Δ y) → IsQCart B → ∃ c : ℚ, 0 < c ∧ ∀ y, KltAt p n (Δ + c • B) y := by
  intro hP X _ _ _ p n hproj hn Δ m G B hm hG hklt hB
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj).1
  obtain ⟨η, hη, hGη⟩ := hG
  obtain ⟨m', D₀, hm', -, rfl⟩ := hB
  obtain ⟨S, hS, hSt⟩ := GlobalTheory.T.finite_test_divisors_klt_lc_pencil_boundaries hP X p n hproj hn η m G D₀ hη hm
  have hloc : ∀ x : X, ∃ (U : X.Opens) (g f : X.functionFieldˣ), x ∈ U ∧
      ∀ y ∈ U, G.IsEqn y g ∧ D₀.IsEqn y f := by
    intro x
    obtain ⟨g, hg⟩ := G.exists_isEqn x
    obtain ⟨f, hf⟩ := D₀.exists_isEqn x
    obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
    obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
    exact ⟨U ⊓ V, g, f, ⟨hU, hV⟩, fun y hy => ⟨hgU y hy.1, hfV y hy.2⟩⟩
  choose U g f hxU hUeq using hloc
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => (U x : Set X))
    fun x => (U x).isOpen.mem_nhds (hxU x)
  let T : Set (DivOver p × X) := {q | q.1 ∈ S ∧ q.2 ∈ t ∧ ∃ y ∈ U q.2, q.1.Through y}
  have hT : T.Finite := (hS.prod t.finite_toSet).subset fun q hq => ⟨hq.1, hq.2.1⟩
  obtain ⟨c, hc, hcT⟩ := exists_pos_mul_lt_of_finite hT
    (fun q => discrep q.1 η m (g q.2) + 1) (fun q => (q.1.ord (f q.2) : ℚ)) (by
      rintro ⟨E, x₀⟩ ⟨-, -, y, hy, hEy⟩
      have := ((hGη y _ (hUeq x₀ y hy).1).kltAt_iff hn hη hm).1 (hklt y) E hEy
      simp only
      linarith)
  refine ⟨c * m', mul_pos hc (by exact_mod_cast hm'), fun y => ?_⟩
  obtain ⟨x₀, hx₀t, hy⟩ : ∃ x₀ ∈ t, y ∈ U x₀ := by
    have : y ∈ ⋃ x ∈ t, (U x : Set X) := ht.symm ▸ trivial
    simpa using this
  obtain ⟨hgy, hfy⟩ := hUeq x₀ y hy
  have hlog := hGη y _ hgy
  have hD : ∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z →
      qWeil D₀ m' z = (E.ord (f x₀) : ℚ) / m' := by
    intro z hz E hE
    rw [qWeil, (hUeq x₀ z (hz.mem_open (U x₀).isOpen hy)).2.mult_eq, hE.ord_eq]
  obtain ⟨m'', g'', hm'', hlog'', hdisc⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ (qWeil D₀ m') η y m m' (g x₀)
    (f x₀) (c * m') hm hm' hlog hD
  refine (hlog''.kltAt_iff hn hη hm'').2 fun E hE => ?_
  rw [hdisc]
  have key := (hSt y (g x₀) (f x₀) c hgy hfy).1 (fun E' hE'S hE'y => by
    have := hcT (E', x₀) ⟨hE'S, hx₀t, y, hy, hE'y⟩
    simp only at this
    linarith) E hE
  have hm0 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have : c * m' * ((E.ord (f x₀) : ℚ) / m') = c * E.ord (f x₀) := by field_simp
  linarith

end GlobalTheory.PairStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosKltAddSmulEffectiveDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (B : X → ℚ), 0 < m → IsLogCanonicalMultiple p n Δ m G → (∀ y, KltAt p n Δ y) → IsQCart B → ∃ c : ℚ, 0 < c ∧ ∀ y, KltAt p n (Δ + c • B) y := by
  first | exact @GlobalTheory.PairStep.exists_pos_kltAt_add_smul | exact GlobalTheory.PairStep.exists_pos_kltAt_add_smul | (intros; apply GlobalTheory.PairStep.exists_pos_kltAt_add_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePow
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp GlobalTheory.ChartGlue GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.ChPow

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X}

theorem cHess_zero' (v : ReciprocityTheory.L2DbarEstimates.V D) :
    ReciprocityTheory.L2DbarEstimates.cHess D (fun _ => ((0 : ℝ) : ℂ)) v = 0 := by
  have h := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul isOpen_univ (p := fun _ => (0 : ℝ)) (q := fun _ => (0 : ℝ))
    contDiffOn_const contDiffOn_const 1 (Set.mem_univ v)
  simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h
  simpa using h

theorem hess_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (n : ℕ) {j : PUnit → B.ι} (hj : y ∈ ptsIn p σ (B.U (j PUnit.unit))) :
    c.hess (φ.pow n) j y = (n : ℂ) • c.hess φ (j PUnit.unit) y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U (j PUnit.unit)))
  have hm := mem_over c.e hy hj
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho (p := fun _ => (0 : ℝ)) contDiffOn_const
    (contDiffOn_chart (hφ (j PUnit.unit)) c) (n : ℝ) hm
  rw [cHess_zero', zero_add] at e
  simp only [zero_add, Complex.ofReal_natCast] at e
  refine Eq.trans ?_ e
  show ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((φ.pow n).φ j (c.e.symm v) : ℝ) : ℂ)) (c.e y) = _
  congr 1
  funext v
  simp [Weight.pow, Weight.zpow_φ]

theorem chernDens_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (n : ℕ) : c.chernDens (φ.pow n) y = (n : ℝ) ^ D * c.chernDens φ y := by
  have hj := (mem_pow_iff (n := (n : ℤ))).1 (mem_pick (φ.pow n).isLB y)
  rw [c.chernDens_eq hφ hy hj, AlgChart.chernDens, hess_pow hφ c hy n hj, Matrix.det_smul, Fintype.card_fin,
    ← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

theorem chernPart_pow {φ : Weight p σ B} (hφ : φ.IsCInf) (n : ℕ) (ε : ℤˣ) :
    (φ.pow n).chernPart D ε = ENNReal.ofReal ((n : ℝ) ^ D) • φ.chernPart D ε := by
  have h := GlobalTheory.ChernScale.glueMeas_restrict_eq (fun c : AlgChart p σ D => c.e)
    (ρ := fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens (φ.pow n) y))
    (ρ' := fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) ENNReal.ofReal_ne_top MeasurableSet.univ
    fun c y hy _ => by
      rw [chernDens_pow hφ c hy n, mul_left_comm, ENNReal.ofReal_mul (by positivity)]
  rw [Weight.chernPart, Weight.chernPart]
  simpa only [Measure.restrict_univ] using h

end GlobalTheory.HSAmp.ChPow

namespace GlobalTheory.HSAmp


open ChPow in
theorem chInt_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (n : ℕ) (w : ∀ σ, CxPts p σ → ℝ), chInt (L.pow n) D w = (n : ℝ) ^ D * chInt L D w := by
  intro k _ X _ p D _ L n w
  rw [chInt, chInt, mul_finsum]
  refine finsum_congr fun σ => ?_
  show ((L.φ σ).pow n).chernInt D Set.univ (w σ) = _
  rw [Weight.chernInt, Weight.chernInt, chernPart_pow (L.cInf σ), chernPart_pow (L.cInf σ), Measure.restrict_smul,
    Measure.restrict_smul, integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul, smul_eq_mul, mul_sub]

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePowStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ) (w : ∀ σ, CxPts p σ → ℝ), chInt (L.pow n) D w = (n : ℝ) ^ D * chInt L D w := by
  first | exact @GlobalTheory.HSAmp.chInt_pow | exact GlobalTheory.HSAmp.chInt_pow | (intros; apply GlobalTheory.HSAmp.chInt_pow <;> assumption)
end
end
