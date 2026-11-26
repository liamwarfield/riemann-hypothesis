module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomPlace

theorem norm_le_one_of_isIntegral_int {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem exists_extension (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (σ : K →+* ℂ) (ι : K →+* ℂ_[p]) :
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k := by
  have hmem : ∀ k, σ k ∈ TaylorLogMetric.Qbar := fun k =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) k).algHom σ.toRatAlgHom)
  let σ' : K →+* TaylorLogMetric.Qbar := σ.codRestrict TaylorLogMetric.Qbar hmem
  let : Algebra K TaylorLogMetric.Qbar := σ'.toAlgebra
  let : Algebra K ℂ_[p] := ι.toAlgebra
  have : IsScalarTower ℚ K TaylorLogMetric.Qbar := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast, eq_ratCast, map_ratCast]
  have : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar := by
    convert algebraicClosure.isAlgebraic ℚ ℂ <;> first | rfl | exact Subsingleton.elim _ _
  have : Algebra.IsAlgebraic K TaylorLogMetric.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let f : TaylorLogMetric.Qbar →ₐ[K] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom, fun k => ⟨hmem k, ?_⟩⟩
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left (hmem k)]
  exact f.commutes k

theorem norm_le_one_of_valuation (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) (hx : w.valuation K x ≤ 1) :
    ‖ι x‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hint : ∀ y : 𝓞 K, ‖ι (y : K)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral_int (by
      convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y)
      exact Subsingleton.elim _ _)
  have hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have h2 : ‖ι x‖ * ‖ι ((d : 𝓞 K) : K)‖ = ‖ι (n : K)‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun z => ‖ι z‖) h
  have h3 := hint n
  nlinarith [norm_nonneg (ι x)]

theorem exp_rat_pow_den (r : ℚ) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ^ r.den = 1 := by
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-r.num, ?_⟩
  have h : ((r.den : ℂ)) * (r : ℂ) = (r.num : ℂ) := by
    exact_mod_cast Rat.den_mul_eq_num r
  push_cast
  rw [← h]; ring

theorem root_of_unity_norm {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) : z ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam z‖ = 1 := by
  have hmem : z ∈ TaylorLogMetric.Qbar := by
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) ?_)
    rw [hz]; exact isAlgebraic_one
  refine ⟨hmem, ?_⟩
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hmem]
  have h1 : (⟨z, hmem⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by simpa using hz)
  have h2 : ‖lam ⟨z, hmem⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

theorem places : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (σ : K →+* ℂ) (ι : K →+* ℂ_[p]), (∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k) ∧ (∀ w : HeightOneSpectrum (𝓞 K), (∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) → ∀ x : K, w.valuation K x ≤ 1 → ‖ι x‖ ≤ 1) ∧ ∀ (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (r : ℚ), Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)))‖ = 1 :=
  fun K _ _ p _ σ ι => ⟨exists_extension K p σ ι, norm_le_one_of_valuation K p ι,
    fun lam r => root_of_unity_norm lam r.den_ne_zero (exp_rat_pow_den r)⟩

end GlobalTheory.MomPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFactsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicNumbers_padicPlaces_facts : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (σ : K →+* ℂ) (ι : K →+* ℂ_[p]), (∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k) ∧ (∀ w : HeightOneSpectrum (𝓞 K), (∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) → ∀ x : K, w.valuation K x ≤ 1 → ‖ι x‖ ≤ 1) ∧ ∀ (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (r : ℚ), Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)))‖ = 1 := by
  first | exact @GlobalTheory.MomPlace.places | exact GlobalTheory.MomPlace.places | (intros; apply GlobalTheory.MomPlace.places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSdLatTwOExpS
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.TwistSd

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in
theorem mem_twO_iff (N : Submodule (𝓞 E) (Sp E n)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : Sp E n) :
    y ∈ twist₂ N c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ localization₂ Q.asIdeal N := by
  simp [twist₂, Submodule.mem_iInf]

omit [StarRing E] in
theorem zpow_smul_mem (M : Submodule (𝓞 E) (Sp E n)) (c : ℕ) {k : ℤ} (hk : 0 ≤ k) {y : Sp E n} (hy : y ∈ M) :
    ((c : E) ^ k) • y ∈ M := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  have : ((c : E) ^ (m : ℤ)) • y = ((c : 𝓞 E) ^ m) • y := by
    rw [← algebraMap_smul E ((c : 𝓞 E) ^ m) y, map_pow, map_natCast, zpow_natCast]
  rw [this]
  exact M.smul_mem _ hy


omit [StarRing E] in
theorem isLattice_twO {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) : Submodule.IsLattice E (twist₂ N c e) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have h1 : ∀ x ∈ twist₂ N c e, (c : E) • x ∈ N := fun x hx => mem_of_locP fun Q => by
    have := zpow_smul_mem _ c (k := 1 + e Q) (by have := he Q; omega) ((mem_twO_iff N c e x).1 hx Q)
    rwa [smul_smul, zpow_add₀ hcE, zpow_one, mul_inv_cancel_right₀ (zpow_ne_zero _ hcE)] at this
  have h2 : ∀ x ∈ N, (c : E) • x ∈ twist₂ N c e := fun x hx => (mem_twO_iff N c e _).2 fun Q => by
    have := zpow_smul_mem _ c (k := 1 - e Q) (by have := he Q; omega) (mem_localization_of_mem Q hx)
    rwa [zpow_sub₀ hcE, zpow_one, div_eq_mul_inv, mul_comm, ← smul_smul] at this
  refine ⟨?_, ?_⟩
  · let f : Sp E n →ₗ[𝓞 E] Sp E n := ((c : E) • (LinearMap.id : Sp E n →ₗ[E] Sp E n)).restrictScalars (𝓞 E)
    have hf : Function.Injective f := fun x y h => smul_right_injective _ hcE h
    refine Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hN.fg ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem hStd_zpow_left (c : ℕ) (k : ℤ) (y x : Sp E n) :
    hStd E n (((c : E) ^ k) • y) x = hStd E n y (((c : E) ^ k) • x) := by
  rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, map_zpow₀, map_natCast]

theorem isSdLat_twO {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) (hodd : ∀ Q, e (conjPrime₂ Q) = -e Q) :
    IsSdLat (twist₂ N c e) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨isLattice_twO hN.1 hc he, ?_⟩
  change dual (hStd E n) (twist₂ N c e) = twist₂ N c e
  apply le_antisymm
  · intro x hx
    rw [mem_dual] at hx
    refine (mem_twO_iff N c e x).2 fun Q' => ?_
    obtain ⟨Q, rfl⟩ : ∃ Q, Q' = conjPrime₂ Q := ⟨conjPrime₂ Q', (GlobalTheory.GO.UniExt.conjP_involutive Q').symm⟩
    rw [GlobalTheory.GO.UniExt.mem_localization_conj_iff hN.1.fg hN.2, hodd, zpow_neg, inv_inv]
    intro y hy
    have hy' : ((c : E) ^ e Q) • y ∈ localization₂ Q.asIdeal (twist₂ N c e) := by
      rwa [mem_localization_twist N hc he, smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hcE), one_smul]
    obtain ⟨t, ht, hty⟩ := hy'
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx _ hty)
    refine ⟨r, cO E t, fun h => ht (by rwa [mem_conjP, cO_cO] at h), ?_⟩
    rw [hr, ← hStd_zpow_left, hStd_osmul_left, ← algebraMap_smul E (cO E t) x, LinearMap.map_smul, smul_eq_mul]
  · intro x hx
    rw [mem_dual]
    intro y hy
    refine mem_of_locP fun Q' => ?_
    obtain ⟨Q, rfl⟩ : ∃ Q, Q' = conjPrime₂ Q := ⟨conjPrime₂ Q', (GlobalTheory.GO.UniExt.conjP_involutive Q').symm⟩
    have h1 := (mem_twO_iff N c e x).1 hx (conjPrime₂ Q)
    rw [GlobalTheory.GO.UniExt.mem_localization_conj_iff hN.1.fg hN.2, hodd, zpow_neg, inv_inv] at h1
    obtain ⟨r, s, hs, hrs⟩ := h1 _ ((mem_twO_iff N c e y).1 hy Q)
    rw [← hStd_zpow_left, smul_smul, mul_inv_cancel₀ (zpow_ne_zero _ hcE), one_smul] at hrs
    exact ⟨s, hs, Submodule.mem_one.2 ⟨r, by rw [← hrs, Algebra.smul_def]⟩⟩

theorem expS_conjP {S : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ P ∈ S, conjPrime₂ P ∉ S) (Q : HeightOneSpectrum (𝓞 E)) :
    expS S (conjPrime₂ Q) = -expS S Q := by
  unfold expS
  rw [GlobalTheory.GO.UniExt.conjP_involutive]
  by_cases h : Q ∈ S
  · simp [h, hS Q h]
  · by_cases h' : conjPrime₂ Q ∈ S <;> simp [h, h']

theorem isSdLat_twO_expS : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n)) (c : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ S, conjPrime₂ P ∉ S) → IsSdLat N → 0 < c →
    IsSdLat (twist₂ N c (expS S)) ∧ IsSdLat (twist₂ N c fun Q => -expS S Q) := by
  intro E _ _ _ n N c S hS hN hc
  refine ⟨isSdLat_twO hN hc (expS_bound S) (expS_conjP hS), isSdLat_twO hN hc (fun Q => ?_) fun Q => ?_⟩
  · have := expS_bound S Q
    omega
  · rw [expS_conjP hS]

end GlobalTheory.ThetaMove.TwistSd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.JetIdentity

open MvPolynomial

section Lin

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in
theorem jetLin_add (J J' : (DVar ι a b →₀ ℕ) → K) : jetLin (J + J') = jetLin J + jetLin J' := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add (f := _)]

omit [Fintype ι] in
theorem jetLin_smul (c : K) (J : (DVar ι a b →₀ ℕ) → K) : jetLin (c • J) = c • jetLin J := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, Pi.smul_apply, smul_monomial]

def jetOpL (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) :
    ((DVar ι a b →₀ ℕ) → K) →ₗ[K] (Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') where
  toFun J := jetOp lam lam' J n
  map_add' J J' := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_add, LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _)]
  map_smul' c J := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_smul, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

theorem jetOp_sum (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) {I : Type} [Fintype I] (ξ : I → K)
    (J : I → (DVar ι a b →₀ ℕ) → K) :
    ∑ i, ξ i • jetOp lam lam' (J i) n = jetOp lam lam' (∑ i, ξ i • J i) n := by
  have := map_sum (jetOpL (K := K) lam lam' n) (fun i => ξ i • J i) Finset.univ
  simp only [map_smul] at this
  exact this.symm

omit [Fintype ι] in
theorem jetLin_congr (J J' : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K)
    (h : ∀ μ ∈ Q.support, J (μ.comapDomain Sum.inr Sum.inr_injective.injOn) =
      J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) : jetLin J Q = jetLin J' Q := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have e : (monomial μ (AddMonoidAlgebra.coeff Q μ) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
      AddMonoidAlgebra.coeff Q μ • basisMonomials _ K μ := by
    simp [coe_basisMonomials, smul_monomial]
  rw [e, map_smul, map_smul]
  simp only [jetLin, Module.Basis.constr_basis, h μ hμ]

theorem jetOp_congr (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, ((∑ β : Fin b, ∑ α : Fin a, m (τ, β, α) : ℕ) : ℤ) =
      ∑ s : Fin a, ((lam τ).w s - (lam τ).detShift + (n τ : ℤ))) → J m = J' m) :
    jetOp lam lam' J n = jetOp lam lam' J' n := by
  classical
  ext1 F
  simp only [jetOp, jetMap, LinearMap.comp_apply]
  congr 1
  refine jetLin_congr J J' _ fun μ hμ => h _ fun τ => ?_
  have h1 := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ F.2)) (mem_support_iff.mp hμ)
  rw [GlobalTheory.JetDeg.weight_derW] at h1
  simp only [Finsupp.comapDomain_apply]
  rw [h1]
  push_cast
  simp [GlobalTheory.JetDeg.natW_cast, Finset.sum_add_distrib, mul_comm]

end Lin

section An

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetC_sum (cD : ι → ℂ) {I : Type} [Fintype I] (c : I → ℂ) (G : I → VCx ι a b → ℂ)
    (hG : ∀ i, AnalyticOnNhd ℂ (G i) Set.univ) (m : DVar ι a b →₀ ℕ) :
    jetC cD (fun z => ∑ i, c i * G i z) m = ∑ i, c i * jetC cD (G i) m := by
  have hc : ∀ i (k : ℕ), ContDiff ℂ k (G i) := fun i k => (hG i).contDiff
  have e : (fun z => ∑ i, c i * G i z) = fun z => ∑ i, (c i • G i) z := by
    funext z; simp
  unfold jetC derivAt0
  rw [e, iteratedFDeriv_sum (f := fun i => c i • G i) (fun i _ => (hc i _).const_smul (c i))]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_const_smul_apply (hc i _).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem map_desc {K : Type} [Field K] (σ : K →+* ℂ) {z : ℂ} (h : ∃ k : K, σ k = z) : σ (desc σ z) = z := by
  rw [desc, dite_eq_left h]
  exact h.choose_spec

end An

end GlobalTheory.JetIdentity


open GlobalTheory.JetIdentity in
theorem GlobalTheory.jetOp_identity_of_entire : ∀ (X : Fields) (a b : ℕ) (σ : X.K →+* ℂ) (cD : X.Tau → ℂ) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) (I₁ I₂ : Type) [Fintype I₁] [Fintype I₂] (ξ₁ : I₁ → X.K) (ξ₂ : I₂ → X.K) (G₁ : I₁ → VCx X.Tau a b → ℂ) (G₂ : I₂ → VCx X.Tau a b → ℂ) (u₁ u₂ : ℂ) (r : X.K), (∀ i, AnalyticOnNhd ℂ (G₁ i) Set.univ) → (∀ i, AnalyticOnNhd ℂ (G₂ i) Set.univ) → (∀ i (m : DVar X.Tau a b →₀ ℕ), (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) → ∃ k : X.K, σ k = u₁ * jetC cD (G₁ i) m) → (∀ i (m : DVar X.Tau a b →₀ ℕ), (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) → ∃ k : X.K, σ k = u₂ * jetC cD (G₂ i) m) → (∀ z, ∑ i, σ (ξ₁ i) * (u₁ * G₁ i z) = σ r * ∑ i, σ (ξ₂ i) * (u₂ * G₂ i z)) → ∑ i, ξ₁ i • jetOp lam lam' (fun m => desc σ (u₁ * jetC cD (G₁ i) m)) n = r • ∑ i, ξ₂ i • jetOp lam lam' (fun m => desc σ (u₂ * jetC cD (G₂ i) m)) n := by
  intro X a b σ cD lam lam' n I₁ I₂ _ _ ξ₁ ξ₂ G₁ G₂ u₁ u₂ r hG₁ hG₂ hr₁ hr₂ hz
  rw [jetOp_sum, jetOp_sum]
  refine Eq.trans ?_ ((jetOpL lam lam' n).map_smul r _)
  refine jetOp_congr lam lam' n _ _ fun m hm => ?_
  apply σ.injective
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_sum]
  have h1 := jetC_sum cD (fun i => σ (ξ₁ i) * u₁) G₁ hG₁ m
  have h2 := jetC_sum cD (fun i => σ r * (σ (ξ₂ i) * u₂)) G₂ hG₂ m
  have e : (fun z => ∑ i, σ (ξ₁ i) * u₁ * G₁ i z) = fun z => ∑ i, σ r * (σ (ξ₂ i) * u₂) * G₂ i z := by
    funext z
    have := hz z
    rw [Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  rw [e, h2] at h1
  rw [Finset.mul_sum]
  simp only [fun i => map_desc σ (hr₁ i m hm), fun i => map_desc σ (hr₂ i m hm)]
  simpa only [mul_assoc] using h1.symm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SpanImageLeOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.IdealTransport

section General

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
  (φ : R ≃+* R') (f : M ≃+ M') (h : ∀ r m, f (r • m) = φ r • f m)

include h

theorem span_image_le_of (N : Submodule R M) (N' : Submodule R' M') (S : Set M) (hS : N = Submodule.span R S)
    (hN : ∀ m ∈ S, f m ∈ N') : Submodule.span R' (f '' (N : Set M)) ≤ N' := by
  rw [Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  show f m ∈ N'
  have hm' : m ∈ Submodule.span R S := hS ▸ hm
  clear hm
  induction hm' using Submodule.span_induction with
  | mem x hx => exact hN x hx
  | zero => rw [map_zero]; exact N'.zero_mem
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact N'.add_mem hx hy
  | smul r x _ hx => rw [h]; exact N'.smul_mem _ hx

theorem span_image_span (S : Set M) :
    Submodule.span R' (f '' (Submodule.span R S : Set M)) = Submodule.span R' (f '' S) := by
  apply le_antisymm
  · exact span_image_le_of φ f h _ _ S rfl fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem mem_span_image (N : Submodule R M) (x : M') :
    x ∈ Submodule.span R' (f '' (N : Set M)) ↔ f.symm x ∈ N := by
  have hsm : ∀ (r : R') (y : M'), f.symm (r • y) = φ.symm r • f.symm y := by
    intro r y
    apply f.injective
    rw [h, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      simpa using hm
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact N.add_mem hy hz
    | smul r y _ hy => rw [hsm]; exact N.smul_mem _ hy
  · intro hx
    exact Submodule.subset_span ⟨f.symm x, hx, by simp⟩

end General

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E')

theorem map_smul_int (r : 𝓞 E) (x : E) : e (r • x) = RingOfIntegers.mapRingEquiv e r • e x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

abbrev trI (I : Submodule (𝓞 E) E) : Submodule (𝓞 E') E' := Submodule.span (𝓞 E') (e '' (I : Set E))

abbrev trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E') (Fin n → E') :=
  Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) => e (x i)) '' (N : Set (Fin n → E)))

theorem mem_trI (I : Submodule (𝓞 E) E) (x : E') : x ∈ trI e I ↔ e.symm x ∈ I := mem_span_image (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) I x

theorem trI_span (S : Set E) : trI e (Submodule.span (𝓞 E) S) = Submodule.span (𝓞 E') (e '' S) := span_image_span (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) S

theorem mem_trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E') :
    x ∈ trL e N ↔ (fun i => e.symm (x i)) ∈ N := mem_span_image (RingOfIntegers.mapRingEquiv e) (AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv)
    (fun r v => funext fun i => map_smul_int e r (v i)) N x

theorem trI_mul (I J : Submodule (𝓞 E) E) : trI e (I * J) = trI e I * trI e J := by
  rw [Submodule.mul_eq_span_mul_set I J, trI_span, Set.image_mul]
  exact (Submodule.span_mul_span _ _ _).symm

theorem trI_singleton (y : E) : trI e (Submodule.span (𝓞 E) {y}) = Submodule.span (𝓞 E') {e y} := by
  rw [trI_span, Set.image_singleton]

theorem trI_one : trI e 1 = 1 := by
  conv_lhs => rw [Submodule.one_eq_span]
  rw [trI_singleton, map_one, ← Submodule.one_eq_span]

theorem trI_surj (J : Submodule (𝓞 E') E') : ∃ I, trI e I = J := by
  refine ⟨Submodule.span (𝓞 E) (e.symm '' (J : Set E')), ?_⟩
  rw [trI_span, Set.image_image]
  simp only [RingEquiv.apply_symm_apply, Set.image_id']
  exact Submodule.span_eq J

theorem mem_one_iff (x : E') : x ∈ (1 : Submodule (𝓞 E') E') ↔ e.symm x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← trI_one e, mem_trI]

theorem map_mulVec' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (A.map e).mulVec (fun i => e (v i)) = fun i => e (A.mulVec v i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum]

theorem det_map' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : (A.map e).det = e A.det := (RingHom.map_det (e : E →+* E') A).symm

theorem carries_iff {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) :
    (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')), (A.map e).mulVec v ∈ trL e N) ↔
      ∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)), A.mulVec v ∈ N := by
  constructor
  · intro H v hv
    have hv' : (fun i => e (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [mem_one_iff e, RingEquiv.symm_apply_apply]
      exact hv i hi
    have hA := H _ hv'
    rw [map_mulVec' e A v, mem_trL] at hA
    simpa using hA
  · intro H v hv
    have hv' : (fun i => e.symm (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [← mem_one_iff e]
      exact hv i hi
    have hmv : (A.map e).mulVec v = fun i => e (A.mulVec (fun i => e.symm (v i)) i) := by
      have hk := map_mulVec' e A (fun i => e.symm (v i))
      simp only [RingEquiv.apply_symm_apply] at hk
      exact hk
    rw [hmv, mem_trL]
    simpa using H _ hv'

theorem det_set {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) :
    {x | ∃ A : Matrix (Fin n) (Fin n) E', (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')),
        A.mulVec v ∈ trL e N) ∧ x = A.det} =
      e '' {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)),
        A.mulVec v ∈ N) ∧ x = A.det} := by
  ext x
  constructor
  · rintro ⟨A', hA', rfl⟩
    have hmap : (A'.map e.symm).map e = A' := by
      ext i j
      simp
    refine ⟨(A'.map e.symm).det, ⟨A'.map e.symm, ?_, rfl⟩, ?_⟩
    · rw [← carries_iff e N, hmap]
      exact hA'
    · rw [← det_map', hmap]
  · rintro ⟨y, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map e, (carries_iff e N A).mpr hA, (det_map' e A).symm⟩

end Fields

theorem transport : ∀ (D : D7) (X : Fields) (s : Seam D X), (∀ (I : Submodule (𝓞 X.E) X.E) (x : D.host.E), x ∈ idTo s I ↔ s.iE.symm x ∈ I) ∧ (∀ I J : Submodule (𝓞 X.E) X.E, idTo s (I * J) = idTo s I * idTo s J) ∧ idTo s 1 = 1 ∧ (∀ y : X.E, idTo s (Submodule.span (𝓞 X.E) {y}) = Submodule.span (𝓞 D.host.E) {s.iE y}) ∧ (∀ 𝔞 : TaylorLogMetric.IdE D, ∃ I, idTo s I = 𝔞) ∧ ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = idTo s (detLat N) := by
  intro D X s
  refine ⟨fun I x => mem_trI s.iE I x, fun I J => trI_mul s.iE I J, trI_one s.iE,
    fun y => trI_singleton s.iE y, trI_surj s.iE, fun n N => ?_⟩
  calc TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)
      = Submodule.span (𝓞 D.host.E) (s.iE '' {x | ∃ A : Matrix (Fin n) (Fin n) X.E,
          (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 X.E) X.E)), A.mulVec v ∈ N) ∧
            x = A.det}) := by
        rw [← det_set s.iE N]
        rfl
    _ = idTo s (detLat N) := (trI_span s.iE _).symm

end GlobalTheory.IdealTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRational
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRational
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.Heis

theorem HV_conj {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) (x y : VV ι a b) :
    Formalism.L2.Ker.HV sc y x = (starRingEnd ℂ) (Formalism.L2.Ker.HV sc x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem alpha_opU_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) (c : ℝ) (x y : V) (F : V → ℂ) (z : V) :
    alphaQ (c / 2) H x * opU H x (fun w => alphaQ (c / 2) H y * opU H y F w) z =
      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((c * (H x y).re + (H x y).im) / 2 : ℝ) : ℂ)) *
        (alphaQ (c / 2) H (x + y) * opU H (x + y) F z) := by
  simp only [alphaQ, opU, Formalism.L2.Th1.H.qOf]
  rw [← add_assoc z x y]
  have key : ∀ a b c d e f g u : ℂ, a + b + c + d = e + f + g →
      Complex.exp a * (Complex.exp b * (u * Complex.exp c) * Complex.exp d) =
        Complex.exp e * (Complex.exp f * (u * Complex.exp g)) := by
    intro a b c d e f g u h
    have : Complex.exp a * Complex.exp b * Complex.exp c * Complex.exp d =
        Complex.exp e * Complex.exp f * Complex.exp g := by
      simp only [← Complex.exp_add, h]
    linear_combination u * this
  apply key
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [hH x y]
  have h1 : H x y = ((H x y).re : ℂ) + ((H x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : (starRingEnd ℂ) (H x y) = ((H x y).re : ℂ) - ((H x y).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Complex.add_re, Complex.conj_re]
  rw [h2]
  generalize (H x y).re = r at *
  generalize (H x y).im = s at *
  rw [h1]
  push_cast
  ring

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add _ x y

theorem Wx_Wx (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z := by
  funext z
  have := alpha_opU_mul (Formalism.L2.Ker.HV A.sc) (fun x y => HV_conj A.sc x y) (Real.sqrt A.d) (emb A x) (emb A y) F z
  rw [← emb_add] at this
  exact this

theorem imH_eq (x y : HomE X.E a b) : imH A x y = coc A x y - coc A y x := by
  simp only [coc, imH, altE]
  rw [HV_conj A.sc (emb A x) (emb A y)]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

theorem imH_add_left (x y z : HomE X.E a b) : imH A (x + y) z = imH A x z + imH A y z := by
  simp only [imH, altE, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_im]

theorem imH_add_right (x y z : HomE X.E a b) : imH A x (y + z) = imH A x y + imH A x z := by
  simp only [imH, altE, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_im]

theorem Wx_comm (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z := by
  rw [Wx_Wx, Wx_Wx, add_comm y x]
  funext z
  have : brkE A y x = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A x y : ℂ)) := rfl
  rw [this, ← mul_assoc, ← Complex.exp_add, imH_eq]
  congr 2
  push_cast
  ring

theorem contDiff_Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) (k : ℕ) (hF : ContDiff ℂ k F) :
    ContDiff ℂ k (Wx A x F) := by
  have h : ContDiff ℂ k (fun z : VCx X.Tau a b => Formalism.L2.Ker.HV A.sc z (emb A x)) := by
    simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply]
    fun_prop
  unfold Wx opU
  exact contDiff_const.mul ((hF.comp (contDiff_id.add contDiff_const)).mul
    (((contDiff_const.mul h).sub contDiff_const).cexp))

theorem jetC_sum (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ)
    (hF : ∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) (m : DVar X.Tau a b →₀ ℕ) :
    jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m := by
  classical
  have hd : ∀ n : ℕ, iteratedFDeriv ℂ n (fun z => ∑ i ∈ T, c i * F i z) 0 = ∑ i ∈ T, c i • iteratedFDeriv ℂ n (F i) 0 := by
    intro n
    have e : (fun z => ∑ i ∈ T, c i * F i z) = ∑ i ∈ T, c i • F i := by
      funext z; simp
    rw [e, iteratedFDeriv_sum_apply (f := fun i => c i • F i) (fun i hi => ((hF i hi n).const_smul (c i)).contDiffAt)]
    exact Finset.sum_congr rfl fun i hi => iteratedFDeriv_const_smul_apply (hF i hi n).contDiffAt
  simp only [jetC, derivAt0, hd, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem calculus : ∀ (X : Fields) (A : Amb X) (a b : ℕ), (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z) ∧ (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z) ∧ (∀ x y : HomE X.E a b, imH A x y = coc A x y - coc A y x) ∧ (∀ x y z : HomE X.E a b, coc A (x + y) z = coc A x z + coc A y z ∧ coc A x (y + z) = coc A x y + coc A x z ∧ imH A (x + y) z = imH A x z + imH A y z ∧ imH A x (y + z) = imH A x y + imH A x z) ∧ (∀ y t : HomE X.E a b, brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ))) ∧ (∀ y t : HomE X.E a b, brkE A y t = 1 ↔ ∃ n : ℤ, imH A t y = n) ∧ (∀ (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ), (∀ k : ℕ, ContDiff ℂ k F) → ∀ k : ℕ, ContDiff ℂ k (Wx A x F)) ∧ (∀ (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ), (∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) → ∀ m, jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m) := by
  intro X A a b
  refine ⟨Wx_Wx A, Wx_comm A, imH_eq A, fun x y z => ⟨?_, ?_, imH_add_left A x y z, imH_add_right A x y z⟩,
    fun _ _ => rfl, fun y t => ?_, fun x F hF k => contDiff_Wx A x F k (hF k), fun κ T c F hF m => jetC_sum A κ T c F hF m⟩
  · simp only [coc, imH_add_left, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_re]; ring
  · simp only [coc, imH_add_right, emb_add, map_add (f := _), LinearMap.add_apply, Complex.add_re]; ring
  · have : brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ)) := rfl
    rw [this, Complex.exp_eq_one_iff]
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      have : ((imH A t y : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination -hn
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [hn]
      push_cast
      ring

end GlobalTheory.MomT.Heis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRationalStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylHeisenbergOperator_calculus_rational : ∀ (X : Fields) (A : Amb X) (a b : ℕ), (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z) ∧ (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z) ∧ (∀ x y : HomE X.E a b, imH A x y = coc A x y - coc A y x) ∧ (∀ x y z : HomE X.E a b, coc A (x + y) z = coc A x z + coc A y z ∧ coc A x (y + z) = coc A x y + coc A x z ∧ imH A (x + y) z = imH A x z + imH A y z ∧ imH A x (y + z) = imH A x y + imH A x z) ∧ (∀ y t : HomE X.E a b, brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ))) ∧ (∀ y t : HomE X.E a b, brkE A y t = 1 ↔ ∃ n : ℤ, imH A t y = n) ∧ (∀ (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ), (∀ k : ℕ, ContDiff ℂ k F) → ∀ k : ℕ, ContDiff ℂ k (Wx A x F)) ∧ (∀ (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ), (∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) → ∀ m, jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m) := by
  first | exact @GlobalTheory.MomT.Heis.calculus | exact GlobalTheory.MomT.Heis.calculus | (intros; apply GlobalTheory.MomT.Heis.calculus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerOComponents
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.PeriodComp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem apply_smul (x : HomE E a b) (s : 𝓞 E) (y : Sp E a) : x (s • y) = s • x y := x.map_smul_of_tower s y

theorem exists_common (S : Submonoid (𝓞 E)) {N : Submodule (𝓞 E) (Sp E a)} (hN : N.FG) (N' : Submodule (𝓞 E) (Sp E b))
    (x : HomE E a b) (h : ∀ y ∈ N, ∃ s ∈ S, s • x y ∈ N') : ∃ s ∈ S, s • x ∈ homO N N' := by
  classical
  obtain ⟨T, hT⟩ := hN
  have hgen : ∀ y ∈ T, ∃ s ∈ S, s • x y ∈ N' := fun y hy =>
    h y (hT ▸ Submodule.subset_span (Finset.mem_coe.mpr hy))
  choose! f hfS hf using hgen
  refine ⟨∏ y ∈ T, f y, prod_mem fun y hy => hfS y hy, ?_⟩
  intro y hy
  rw [← hT] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [LinearMap.smul_apply, ← Finset.mul_prod_erase T f (Finset.mem_coe.mp hy), mul_comm, mul_smul]
    exact N'.smul_mem _ (hf y (Finset.mem_coe.mp hy))
  | zero => rw [map_zero]; exact N'.zero_mem
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact N'.add_mem hy hz
  | smul r y _ hy => rw [GlobalTheory.ThetaMove.PeriodComp.apply_smul]; exact N'.smul_mem r hy

theorem smul_mem_perO {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {r : E} (hr : r ∈ AA) {x : HomE E a b} (hx : x ∈ homO N N') : r • x ∈ perO AA N N' :=
  Submodule.subset_span ⟨r, hr, x, hx, rfl⟩

theorem mono (AA : Submodule (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a))
    (N₁' N₂' : Submodule (𝓞 E) (Sp E b)) (hN : N₂.FG) (h : localization₂ Q.asIdeal N₂ ≤ localization₂ Q.asIdeal N₁)
    (h' : localization₂ Q.asIdeal N₁' ≤ localization₂ Q.asIdeal N₂') :
    localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (perO AA N₂ N₂') := by
  have hgen : perO AA N₁ N₁' ≤ localization₂ Q.asIdeal (perO AA N₂ N₂') := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, x, hx, rfl⟩
    have hmult : ∀ y ∈ N₂, ∃ s ∈ Q.asIdeal.primeCompl, s • x y ∈ N₂' := by
      intro y hy
      obtain ⟨u, hu, huy⟩ := h (mem_localization_of_mem Q hy)
      have hxy : x (u • y) ∈ N₁' := hx _ huy
      rw [GlobalTheory.ThetaMove.PeriodComp.apply_smul] at hxy
      obtain ⟨v, hv, hvxy⟩ := h' (mem_localization_of_mem Q hxy)
      exact ⟨v * u, mul_mem hv hu, by rw [mul_smul]; exact hvxy⟩
    obtain ⟨t, ht, htx⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common Q.asIdeal.primeCompl hN N₂' x hmult
    exact ⟨t, ht, by rw [smul_comm]; exact GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hr htx⟩
  calc localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (localization₂ Q.asIdeal (perO AA N₂ N₂')) :=
        localization_mono Q hgen
    _ = localization₂ Q.asIdeal (perO AA N₂ N₂') := localization_localization₂ Q _

theorem eq_homAt (AA : Submodule (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) :
    localization₂ P.asIdeal (perO AA N N') = homAt {P} N N' := by
  apply le_antisymm
  · have hgen : perO AA N N' ≤ homAt {P} N N' := by
      apply Submodule.span_le.mpr
      rintro _ ⟨r, hr, x, hx, rfl⟩
      intro P' hP' y hy
      rw [Finset.mem_singleton] at hP'
      subst hP'
      obtain ⟨u, hu, huy⟩ := hy
      have hr1 : r ∈ localization₂ P'.asIdeal (1 : Submodule (𝓞 E) E) := by
        rw [← hA]; exact mem_localization_of_mem P' hr
      obtain ⟨v, hv, hvr⟩ := hr1
      obtain ⟨w, hw⟩ := Submodule.mem_one.mp hvr
      have hxy : u • x y ∈ N' := by
        rw [← GlobalTheory.ThetaMove.PeriodComp.apply_smul]; exact hx _ huy
      refine ⟨v * u, mul_mem hv hu, ?_⟩
      rw [LinearMap.smul_apply, mul_smul, smul_comm u r, ← smul_assoc v r, ← hw, algebraMap_smul]
      exact N'.smul_mem w hxy
    intro z hz
    obtain ⟨s, hs, hsz⟩ := hz
    have h1 := hgen hsz
    intro P' hP' y hy
    obtain ⟨t, ht, hty⟩ := h1 P' hP' y hy
    rw [Finset.mem_singleton] at hP'
    subst hP'
    refine ⟨t * s, mul_mem ht hs, ?_⟩
    rw [mul_smul, ← LinearMap.smul_apply]
    exact hty
  · intro x hx
    have h1 : (1 : E) ∈ localization₂ P.asIdeal AA := by
      rw [hA]; exact mem_localization_of_mem P (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    obtain ⟨v, hv, hv1⟩ := h1
    have hmult : ∀ y ∈ N, ∃ s ∈ P.asIdeal.primeCompl, s • x y ∈ N' := fun y hy =>
      hx P (Finset.mem_singleton_self P) y (mem_localization_of_mem P hy)
    obtain ⟨t, ht, htx⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common P.asIdeal.primeCompl hN N' x hmult
    refine ⟨v * t, mul_mem hv ht, ?_⟩
    have h2 := GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hv1 htx
    rwa [smul_one_smul, ← mul_smul] at h2

private theorem exists_nsmul_mem_of_isLattice (N' : Submodule (𝓞 E) (Sp E b)) (hN' : Submodule.IsFullLattice E N') (v : Sp E b) :
    ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ N' := by
  have hv : v ∈ Submodule.span E (N' : Set (Sp E b)) := by
    let _ : Submodule.IsFullLattice E N' := hN'
    rw [Submodule.IsFullLattice.span_eq_top (A := E) (M := N')]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem w hw => exact ⟨1, one_pos, by rw [Nat.cast_one, one_smul]; exact hw⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact N'.zero_mem⟩
  | add v w _ _ hv hw =>
    obtain ⟨m, hm, hmv⟩ := hv
    obtain ⟨k, hk, hkw⟩ := hw
    refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine N'.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N'.smul_mem _ hmv
    · rw [mul_smul]; exact N'.smul_mem _ hkw
  | smul c v _ hv =>
    obtain ⟨m, hm, hmv⟩ := hv
    obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
    have h1 : IsIntegral ℤ ((y : E) * c) := by
      simpa [zsmul_eq_mul] using hyint c (Finset.mem_singleton_self c)
    have hint : IsIntegral ℤ ((y.natAbs : E) * c) := by
      rcases Int.natAbs_eq y with h | h
      · rw [h] at h1; simpa using h1
      · rw [h] at h1; simpa using h1.neg
    refine ⟨y.natAbs * m, Nat.mul_pos (Int.natAbs_pos.mpr hy0) hm, ?_⟩
    have key : ((y.natAbs * m : ℕ) : 𝓞 E) • (c • v) =
        (⟨(y.natAbs : E) * c, hint⟩ : 𝓞 E) • ((m : 𝓞 E) • v) := by
      ext i
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply]
      simp only [smul_eq_mul, Algebra.smul_def, map_natCast]
      push_cast
      have hα : ∀ z : ↥(integralClosure ℤ E), algebraMap (↥(integralClosure ℤ E)) E z = (z : E) :=
        fun _ => rfl
      simp only [hα]
      ring
    rw [key]
    exact N'.smul_mem _ hmv

theorem full (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (hN' : Submodule.IsFullLattice E N') (hA : AA ≠ ⊥) : Full (perO AA N N') := by
  obtain ⟨r, hrA, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  intro x
  let S : Submonoid (𝓞 E) :=
    { carrier := {s | ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) = s}
      mul_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨k, hk, rfl⟩
        exact ⟨m * k, Nat.mul_pos hm hk, by push_cast; rfl⟩
      one_mem' := ⟨1, one_pos, Nat.cast_one⟩ }
  have hmult : ∀ y ∈ N, ∃ s ∈ S, s • (r⁻¹ • x) y ∈ N' := fun y _ => by
    obtain ⟨n, hn, h⟩ := exists_nsmul_mem_of_isLattice N' hN' ((r⁻¹ • x) y)
    exact ⟨n, ⟨n, hn, rfl⟩, h⟩
  obtain ⟨s, hsS, hs⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common S hN N' (r⁻¹ • x) hmult
  obtain ⟨n, hn, rfl⟩ := hsS
  refine ⟨n, hn, ?_⟩
  have h2 := GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hrA hs
  rwa [smul_comm r, smul_inv_smul₀ hr0] at h2

theorem perO_components : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA : Submodule (𝓞 E) E), (∀ (Q : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Sp E b)), N₂.FG → localization₂ Q.asIdeal N₂ ≤ localization₂ Q.asIdeal N₁ → localization₂ Q.asIdeal N₁' ≤ localization₂ Q.asIdeal N₂' → localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (perO AA N₂ N₂')) ∧ (∀ (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)), N.FG → localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) → localization₂ P.asIdeal (perO AA N N') = homAt {P} N N') ∧ ∀ (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)), N.FG → Submodule.IsFullLattice E N' → AA ≠ ⊥ → Full (perO AA N N') := by
  intro E _ _ _ a b AA
  exact ⟨fun Q N₁ N₂ N₁' N₂' hN h h' => GlobalTheory.ThetaMove.PeriodComp.mono AA Q N₁ N₂ N₁' N₂' hN h h',
    fun P N N' hN hA => GlobalTheory.ThetaMove.PeriodComp.eq_homAt AA P N N' hN hA,
    fun N N' hN hN' hA => GlobalTheory.ThetaMove.PeriodComp.full AA N N' hN hN' hA⟩

end GlobalTheory.ThetaMove.PeriodComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocCharEqZpowMul
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.LocCharVal

theorem isUnit_redP {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (hb : P.valuation E b = 1) : IsUnit (redP P b) := by
  have h1 : Formalism.L2.Col.IntAt P b := (GlobalTheory.CharVal.intAt_iff _).2 hb.le
  have h2 : Formalism.L2.Col.IntAt P b⁻¹ := (GlobalTheory.CharVal.intAt_iff _).2 (by rw [map_inv₀, hb]; simp)
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have h3 := reduction_mul h1 h2
  rw [mul_inv_cancel₀ hb0] at h3
  have h4 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [h4] at h3
  exact IsUnit.of_mul_eq_one _ h3.symm

theorem locChar_eq_zpow_mul : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), P.valuation E (q : E) = WithZero.exp (-1 : ℤ) → a ≠ 0 → ∃ (z : ℤ) (ζ : Kˣ), IsOfFinOrder ζ ∧ LocE.locChar q cq χ a = cq ^ z * (ζ : K) := by
  intro E K _ _ _ P q cq χ a hq ha
  have hv : P.valuation E a ≠ 0 := by simpa using ha
  have hex : ∃ z : ℤ, IsUnit (redP P (a / (q : E) ^ z)) := by
    refine ⟨-WithZero.log (P.valuation E a), isUnit_redP P _ ?_⟩
    rw [map_div₀, map_zpow₀, hq, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log hv, hv]
  have hu : IsUnit (redP P (a / (q : E) ^ LocE.vP P q a)) := Classical.epsilon_spec hex
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨LocE.vP P q a, χ hu.unit, MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite _), ?_⟩
  unfold LocE.locChar LocE.unitV
  rw [dite_eq_left hu]

end GlobalTheory.LocCharVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftsLatticeMapMemSetupGoodLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftsLatticeMapMemSetupGoodLifts
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomGood

theorem inOK_iff_mem_OK (d : ℕ) (z : ℂ) : GlobalTheory.MomOne.InOK d z ↔ z ∈ JMB.OK d := Iff.rfl

theorem lamA_eq_lamC {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) : JMB.lamA lam x = lamC lam x := rfl

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D (tor0 D cc δ) L L') → ∀ y ∈ GlobalTheory.MomT.goodLifts D (tor0 D cc δ) lam N₀ n L L', e y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x} := by
  intro D cc δ N N' L L' g S e p _ lam N₀ n hd hLa y hy
  obtain ⟨-, -, hOK, hconj, -⟩ := GlobalTheory.MomDict.main D
  unfold GlobalTheory.MomT.goodLifts at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, hκ, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.φ₀ ((κ : D.host.K) : D.host.E), ?_, ?_, e x, (hLa x).2 hx, ?_⟩
    · rw [hd]
      exact (inOK_iff_mem_OK _ _).1 ((hOK _).2 ⟨κ, rfl⟩)
    · rw [lamA_eq_lamC, ← hconj]
      exact hκ
    · exact map_smul e _ x
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end GlobalTheory.MomGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftsLatticeMapMemSetupGoodLiftsStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodLiftsLattice_map_mem_setup_goodLifts : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D (tor0 D cc δ) L L') → ∀ y ∈ GlobalTheory.MomT.goodLifts D (tor0 D cc δ) lam N₀ n L L', e y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x} := by
  first | exact @GlobalTheory.MomGood.main | exact GlobalTheory.MomGood.main | (intros; apply GlobalTheory.MomGood.main <;> assumption)
end
end
