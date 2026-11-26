module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterCuspidalRootSumRegular
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal_of_bialgHom (k A B : Type) [CommRing k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] (f : B →ₐc[k] A) : (kerIdeal f).IsHopfIdeal k := by
  refine Ideal.IsHopfIdeal.mk (toIsCoideal := ⟨?_, ?_⟩) ?_
  · intro x hx
    exact (kerIdeal_le_ker_iff f (counitAlgHom k A)).2 (fun c => by simp) hx
  · intro x hx
    have h0 := (kerIdeal_le_ker_iff f (Ideal.Quotient.mkₐ k (kerIdeal f))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    have h : kerIdeal f ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f))).comp (comulAlgHom k A)) := by
      refine (kerIdeal_le_ker_iff f _).2 fun c => ?_
      have key : ∀ t : B ⊗[k] B, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f)) (pullbackTwo f t) =
          algebraMap k _ (counit (R := k)
            (TensorProduct.lid k B (LinearMap.rTensor B (counit (R := k) (A := B)) t))) := by
        intro t
        induction t with
        | add x y hx hy => simp only [map_add (f := _), hx, hy]
        | tmul x y =>
          rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
            TensorProduct.lid_tmul, map_smul]
          erw [h0, h0]
          simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
            smul_smul, mul_comm]
      rw [AlgHom.comp_apply, comulAlgHom_apply, ← pullTwo_comul, key, rTensor_counit_comul,
        TensorProduct.lid_tmul, one_smul]
    exact h hx
  · intro x hx
    have h : kerIdeal f ≤ (kerIdeal f).comap (HopfAlgebra.antipodeAlgHom k A) := by
      refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      have ha' : counit (R := k) a = 0 := ha
      change HopfAlgebra.antipode k (f a) ∈ kerIdeal f
      rw [← bialgHom_map_antipode]
      exact Ideal.mem_map_of_mem (f : B →ₐ[k] A) (by simp [RingHom.mem_ker, ha'])
    exact h hx

end GlobalTheory.PDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOf
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam

theorem derivWeierstrassP_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.derivWeierstrassP = L'.derivWeierstrassP := by
  rw [← L.deriv_weierstrassP, ← L'.deriv_weierstrassP, Formalism.L2.Th1.F.LatOnly.wp_eq h]

theorem derivWeierstrassP_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (scalePair L c hc).derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z := by
  unfold PeriodPair.derivWeierstrassP
  have hs := Formalism.L2.Th1.F.Homog.tsum_scale L c hc (fun w => 2 / (c * z - w) ^ 3)
  rw [hs]
  have hterm : ∀ l : L.lattice, 2 / (c * z - c * (l : ℂ)) ^ 3 = (c ^ 3)⁻¹ * (2 / (z - l) ^ 3) := by
    intro l
    rw [← mul_sub, mul_pow, div_mul_eq_div_div, div_eq_inv_mul (2 / c ^ 3), div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  ring

theorem lattice_eq_scalePair_tauPair {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.lattice = (scalePair (tauPair τ) c h.1).lattice := by
  ext x
  rw [h.2 x, Formalism.L2.Th1.F.Homog.mem_scale, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨u, v, rfl⟩
    refine ⟨u, v, ?_⟩
    change (u : ℂ) * (τ : ℂ) + (v : ℂ) * 1 = c⁻¹ * (c * ((u : ℂ) * (τ : ℂ) + (v : ℂ)))
    rw [← mul_assoc, inv_mul_cancel₀ h.1, one_mul, mul_one]
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    change (m : ℂ) * (τ : ℂ) + (n : ℂ) * 1 = c⁻¹ * x at hmn
    rw [mul_one] at hmn
    rw [hmn, ← mul_assoc, mul_inv_cancel₀ h.1, one_mul]

theorem homogeneity_of_isTauOf : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf L c τ → (∀ z, c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice) ∧ (∀ z, L.weierstrassP (c * z) = (c ^ 2)⁻¹ * (tauPair τ).weierstrassP z) ∧ (∀ z, L.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * (tauPair τ).derivWeierstrassP z) ∧ s2 L = (c ^ 2)⁻¹ * s2 (tauPair τ) ∧ area L = ‖c‖ ^ 2 * area (tauPair τ) := by
  intro L c τ h
  have hl := lattice_eq_scalePair_tauPair h
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · rw [hl, Formalism.L2.Th1.F.Homog.mem_scale, ← mul_assoc, inv_mul_cancel₀ h.1, one_mul]
  · rw [Formalism.L2.Th1.F.LatOnly.wp_eq hl, Formalism.L2.Th1.F.Homog.wp_scale]
  · rw [derivWeierstrassP_eq_of_lattice_eq hl, derivWeierstrassP_scalePair]
  · rw [Formalism.L2.Th1.F.LatOnly.quasiPeriodConst_eq hl, Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale]
  · rw [Formalism.L2.Th1.F.LatOnly.area_eq hl, Formalism.L2.Th1.F.Homog.area_scale]

end GlobalTheory.WpFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOfStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf L c τ → (∀ z, c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice) ∧ (∀ z, L.weierstrassP (c * z) = (c ^ 2)⁻¹ * (tauPair τ).weierstrassP z) ∧ (∀ z, L.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * (tauPair τ).derivWeierstrassP z) ∧ s2 L = (c ^ 2)⁻¹ * s2 (tauPair τ) ∧ area L = ‖c‖ ^ 2 * area (tauPair τ) := by
  first | exact @GlobalTheory.WpFam.homogeneity_of_isTauOf | exact GlobalTheory.WpFam.homogeneity_of_isTauOf | (intros; apply GlobalTheory.WpFam.homogeneity_of_isTauOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.FischerParts

theorem exists_fockIP (σ : Type) [DecidableEq σ] :
    ∃ ι : MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2,
      IsFockIP ι ∧ Function.Injective ι := by
  classical
  let w : (σ →₀ ℕ) → ℕ := fun α => α.prod fun _ k => k.factorial
  have hw : ∀ α, w α ≠ 0 := fun α => Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  let v : (σ →₀ ℕ) → lp (fun _ : σ →₀ ℕ => ℂ) 2 := fun α => lp.single 2 α (√(w α) : ℝ)
  have hv : ∀ α β, inner ℂ (v α) (v β) = if α = β then (w α : ℂ) else 0 := by
    intro α β
    simp only [v, lp.inner_single_left, lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      simp only [RCLike.inner_apply, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    · simp
  refine ⟨(basisMonomials σ ℂ).constr ℂ v, fun α β => ?_, ?_⟩
  · have e : ∀ α, (basisMonomials σ ℂ).constr ℂ v (monomial α 1) = v α := fun α => by
      have := (basisMonomials σ ℂ).constr_basis ℂ v α
      rwa [coe_basisMonomials] at this
    rw [e, e, hv]
    simp [w, Finsupp.prod]
  · refine (basisMonomials σ ℂ).injective_constr_of_linearIndependent ?_
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun α h => hw α ?_) fun α β h => ?_
    · have := hv α α
      rw [h, inner_zero_left, if_pos rfl] at this
      exact_mod_cast this.symm
    · exact (hv α β).trans (if_neg h)

theorem fischer_parts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  intro p q r s d
  obtain ⟨ι, hι, hinj⟩ := exists_fockIP (Ln p q r s)
  refine ⟨fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron1 r s Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron2 p q Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | (∃ Z, IsPC Z ∧ M = kron1 r s Z) ∨ ∃ Z, IsPC Z ∧ M = kron2 p q Z}
      ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron1 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron2 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [odd_kron1 hZ, odd_kron2 hZ]
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [⟨_, .inl ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩,
      ⟨_, .inr ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩]
  · exact ⟨fun Z hZ => hP _ (.inl ⟨Z, hZ, rfl⟩), fun Z hZ => hP _ (.inr ⟨Z, hZ, rfl⟩)⟩
  · constructor
    · rintro ⟨Q, hQ, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩⟩
      exacts [⟨Q, hQ, _, .inl ⟨Z, hZ, rfl⟩, rfl⟩, ⟨Q, hQ, _, .inr ⟨Z, hZ, rfl⟩, rfl⟩]
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩, rfl⟩
      exacts [⟨Q, hQ, .inl ⟨Z, hZ, rfl⟩⟩, ⟨Q, hQ, .inr ⟨Z, hZ, rfl⟩⟩]

end GlobalTheory.FischerParts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactPartsStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fischerDecomposition_fockNoncompactParts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  first | exact @GlobalTheory.FischerParts.fischer_parts | exact GlobalTheory.FischerParts.fischer_parts | (intros; apply GlobalTheory.FischerParts.fischer_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.SubstCalc

variable {R : Type} [CommRing R]

theorem constantCoeff_subst_of_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem hasSubst_elim {d : ℕ} {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem subst_powerSeriesEvalTwoGroups {d : ℕ} {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {a : τ → MvPowerSeries τ' R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i)) := by
  unfold at2
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  funext s
  cases s <;> rfl

theorem powerSeriesEvalTwoGroups_rules_alt : ∀ (R : Type) [CommRing R] (d : ℕ) (τ τ' : Type) [Finite τ] (u v : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ f, at2 (inL f) u v = subst u f) ∧ (∀ f, at2 (inR f) u v = subst v f) ∧ (∀ c c', at2 (c + c') u v = at2 c u v + at2 c' u v ∧ at2 (c - c') u v = at2 c u v - at2 c' u v) ∧ (∀ c, constantCoeff (at2 c u v) = constantCoeff c) ∧ (∀ c, at2 (swap c) u v = at2 c v u) ∧ (∀ (e : ℕ) (μ : Fin e → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin e) R, at2 (subst μ f) u v = subst (fun i => at2 (μ i) u v) f) ∧ (∀ a : τ → MvPowerSeries τ' R, (∀ t, constantCoeff (a t) = 0) → ∀ c, subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, cob2 (addLaw R d) c = 0 → at2 c u v - at2 c (u + u) v + at2 c u (u + v) - at2 c u u = 0 := by
  intro R _ d τ τ' _ u v hu hv
  have hs := hasSubst_elim hu hv
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold at2 inL
    rw [subst_comp_subst_apply hX hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro f
    unfold at2 inR
    rw [subst_comp_subst_apply hY hs]
    congr 1
    funext i
    rw [subst_X hs]; rfl
  · intro c c'
    unfold at2
    exact ⟨subst_add hs _ _, subst_sub hs _ _⟩
  · intro c
    unfold at2
    exact constantCoeff_subst_of_zero (fun s => by cases s <;> simp [hu, hv]) c
  · intro c
    have hW : HasSubst (Sum.elim (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (fun i => X (Sum.inl i))) :=
      hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp
    unfold swap at2
    rw [subst_comp_subst_apply hW hs]
    congr 1
    funext s
    cases s <;> simp [subst_X hs]
  · intro e μ hμ f
    unfold at2
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hs]
  · intro a ha c
    exact subst_powerSeriesEvalTwoGroups hu hv ha c
  · intro c hc
    set w : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim u v) with hw
    have hw0 : ∀ t, constantCoeff (w t) = 0 := fun t => by
      rcases t with t | t | t <;> simp [hw, hu, hv]
    have hsw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
    have h1 : ∀ i, subst w (x1 (R := R) (d := d) i) = u i := fun i => by
      unfold x1; rw [subst_X hsw]; rfl
    have h2 : ∀ i, subst w (x2 (R := R) (d := d) i) = u i := fun i => by
      unfold x2; rw [subst_X hsw]; rfl
    have h3 : ∀ i, subst w (x3 (R := R) (d := d) i) = v i := fun i => by
      unfold x3; rw [subst_X hsw]; rfl
    have hx0 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx20 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx30 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        op (addLaw R d) a b = a + b := by
      intro a b ha hb
      funext i
      unfold op addLaw at2
      have := hasSubst_elim ha hb
      rw [subst_add this, subst_X this, subst_X this]
      rfl
    have hop0 : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
        ∀ i, constantCoeff ((a + b) i) = 0 := by
      intro a b ha hb i; simp [ha, hb]
    have key := congrArg (subst w) hc
    unfold cob2 at key
    rw [hop _ _ hx0 hx20, hop _ _ hx20 hx30] at key
    rw [subst_sub hsw, subst_add hsw, subst_sub hsw,
      subst_powerSeriesEvalTwoGroups hx20 hx30 hw0, subst_powerSeriesEvalTwoGroups (hop0 _ _ hx0 hx20) hx30 hw0,
      subst_powerSeriesEvalTwoGroups hx0 (hop0 _ _ hx20 hx30) hw0, subst_powerSeriesEvalTwoGroups hx0 hx20 hw0] at key
    have e : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
        (fun i => subst w ((a + b) i)) = (fun i => subst w (a i)) + (fun i => subst w (b i)) := by
      intro a b; funext i; simp only [Pi.add_apply]; exact subst_add hsw _ _
    rw [e, e] at key
    simp only [h1, h2, h3] at key
    have e0 : subst w (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := by
      simpa using (subst_sub hsw (0 : MvPowerSeries _ R) 0)
    rw [e0] at key
    convert key using 2

end GlobalTheory.Katz.SubstCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRulesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesEvalTwoGroups_rules : ∀ (R : Type) [CommRing R] (d : ℕ) (τ τ' : Type) [Finite τ] (u v : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ f, at2 (inL f) u v = subst u f) ∧ (∀ f, at2 (inR f) u v = subst v f) ∧ (∀ c c', at2 (c + c') u v = at2 c u v + at2 c' u v ∧ at2 (c - c') u v = at2 c u v - at2 c' u v) ∧ (∀ c, constantCoeff (at2 c u v) = constantCoeff c) ∧ (∀ c, at2 (swap c) u v = at2 c v u) ∧ (∀ (e : ℕ) (μ : Fin e → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin e) R, at2 (subst μ f) u v = subst (fun i => at2 (μ i) u v) f) ∧ (∀ a : τ → MvPowerSeries τ' R, (∀ t, constantCoeff (a t) = 0) → ∀ c, subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, cob2 (addLaw R d) c = 0 → at2 c u v - at2 c (u + u) v + at2 c u (u + v) - at2 c u u = 0 := by
  first | exact @GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt | exact GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt | (intros; apply GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin

def QHyp {S : Scheme.{0}} (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) : Prop :=
  IsAbelianScheme A ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left)

def formLB {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) {G : Over S} {r : ℕ} (pr : Fin r → (G ⟶ A))
    (W : Matrix (Fin r) (Fin r) ℤ) : LB G.left :=
  LB.LinComb Q (K := Fin r × Fin r) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)

def diagPow {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) (d : ℤ) : LB A.left :=
  LB.LinComb Q (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => d)

def sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : (G' ⊗ G').left ⟶ (G ⊗ G).left :=
  pullback.lift ((fst G' G').left ≫ φ) ((snd G' G').left ≫ φ) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, Over.w (fst G' G'), Over.w (snd G' G')])

theorem isSquare_sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : IsSquare φ (sqMap f φ w) :=
  ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {φ' : G''.left ⟶ G'.left} {φ₂' : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare φ' φ₂') (h : IsSquare φ φ₂) : IsSquare (φ' ≫ φ) (φ₂' ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
   by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isMonHom_prodPow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (c : Fin r → ℤ) : IsMonHom (∏ k, f k ^ c k) :=
  Finset.prod_induction _ (fun x => IsMonHom x) (fun a b ha hb => by
    haveI := ha; haveI := hb; exact GlobalTheory.Serre.isMonHom_mul a b) GlobalTheory.Serre.isMonHom_one fun k _ => by
    haveI := hf k; exact GlobalTheory.Serre.isMonHom_zpow _ _

theorem powext {S : Scheme.{0}} (A : Over S) (r : ℕ) {X : Scheme.{0}} (a b : X ⟶ (Out.powObj A r).left)
    (h0 : a ≫ (Out.powObj A r).hom = b ≫ (Out.powObj A r).hom)
    (h : ∀ k, a ≫ (Out.powPr A k).left = b ≫ (Out.powPr A k).left) : a = b := by
  have := (Out.powIsLimit A r).hom_ext (W := Over.mk (b ≫ (Out.powObj A r).hom)) (f := Over.homMk a h0)
    (f' := Over.homMk b rfl) (fun ⟨k⟩ => Over.OverMorphism.ext (by simpa using h k))
  exact congrArg (fun m => m.left) this

end GlobalTheory.ActFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommMonObjOfGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem isCommMonObj_of_grpPullback : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → IsCommMonObj G' := by
  intro S S' G _ _ G' _ f φ h
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
  rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
    ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFinite
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.exists_pow_char_eq_of_isReduced_finite : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A], ∀ a : A, ∃ b : A, a = b ^ p := by
  intro p _ k _ _ _ A _ _ _ _ a
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : PerfectField k := PerfectRing.toPerfectField k p
  let e := IsArtinianRing.equivPi A
  have key : ∀ I : MaximalSpectrum A, ∃ c : A ⧸ I.asIdeal, e a I = c ^ p := by
    intro I
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite k (A ⧸ I.asIdeal) := Module.Finite.trans A (A ⧸ I.asIdeal)
    haveI : Algebra.IsAlgebraic k (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite k _
    haveI : PerfectField (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.perfectField k
    haveI : CharP (A ⧸ I.asIdeal) p :=
      charP_of_injective_algebraMap (algebraMap k (A ⧸ I.asIdeal)).injective p
    haveI : PerfectRing (A ⧸ I.asIdeal) p := PerfectField.toPerfectRing p
    obtain ⟨c, hc⟩ := surjective_frobenius (A ⧸ I.asIdeal) p (e a I)
    exact ⟨c, by rw [← hc, frobenius_def]⟩
  choose c hc using key
  refine ⟨e.symm c, e.injective ?_⟩
  rw [map_pow, AlgEquiv.apply_symm_apply]
  funext I
  rw [hc I, Pi.pow_apply]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegular
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem isChar_cusp_and_norm_of_reg (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (m k : ℕ) (hm : 0 < m)
    (hk : Reg (Nat.card F) m k) :
    IsChar ℂ ℂ (cusp θ m k) ∧
      ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  obtain ⟨h1, h2⟩ := isChar_psi_rootSum_of_regular F θ hθ m k hm hk
  refine ⟨h1, ?_⟩
  have hip := ipGL_eq_finsum_GL (F := F) (d := m) (psi (rootSum θ k) (Fin m → F))
    (psi (rootSum θ k) (Fin m → F))
  rw [h2] at hip
  have hsq : ((-1 : ℂ) ^ (m - 1)) * star ((-1 : ℂ) ^ (m - 1)) = 1 := by
    rw [star_pow, star_neg, star_one, ← mul_pow]
    norm_num
  have hterm : ∀ x : GL (Fin m) F, cusp θ m k x * star (cusp θ m k x) =
      psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))) := by
    intro x
    simp only [cusp, psiG, star_mul']
    linear_combination (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) *
        star (psi (rootSum θ k) (Fin m → F) (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)))) * hsq
  rw [finsum_congr hterm, ← hip]
  rfl

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegularStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k : ℕ, 0 < m → Reg (Nat.card F) m k → IsChar ℂ ℂ (cusp θ m k) ∧ ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  first | (exact @GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (exact GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (intros; apply GlobalTheory.Shin.isChar_cusp_and_norm_of_reg  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompleteDvrPadicAlgCl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompleteDvrPadicAlgCl
open IsLocalRing

namespace GlobalTheory.DvrFinExt

theorem exists_finite_intermediateField (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F Ω]
    [Algebra.IsIntegral F Ω] [Algebra K Ω] (hQ : ∀ q : F, algebraMap F Ω q ∈ (algebraMap K Ω).range)
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* Ω) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ ∀ a, y₀ a ∈ L := by
  have hb : Function.Bijective (algebraMap K Ω).rangeRestrict :=
    ⟨(algebraMap K Ω).rangeRestrict.injective, (algebraMap K Ω).rangeRestrict_surjective⟩
  let e := RingEquiv.ofBijective _ hb
  let u : F →+* K := e.symm.toRingHom.comp ((algebraMap F Ω).codRestrict _ hQ)
  have hu : (algebraMap K Ω).comp u = (RingHom.id Ω).comp (algebraMap F Ω) := by
    ext q
    have h := e.apply_symm_apply ((algebraMap F Ω).codRestrict _ hQ q)
    exact congrArg Subtype.val h
  have hint : ∀ x : Ω, IsIntegral K x := fun x =>
    IsIntegral.map_of_comp_eq u (RingHom.id Ω) hu (Algebra.IsIntegral.isIntegral (R := F) x)
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  haveI : Finite (y₀ '' (s : Set R)) := (s.finite_toSet.image y₀).to_subtype
  refine ⟨IntermediateField.adjoin K (y₀ '' (s : Set R)),
    IntermediateField.finiteDimensional_adjoin (fun x _ => hint x), fun a => ?_⟩
  have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  | algebraMap n => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_finite_extension : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W) (fV : V →+* W) (fK : FractionRing V →+* FractionRing W) (κ' : FractionRing W →+* PadicAlgCl p), Function.Injective fV ∧ IsLocalHom fV ∧ fV.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (fV a)) ∧ κ'.comp fK = κ ∧ (∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ ∀ a, y₀ a ∈ κ'.range := by
  intro p _ V _ _ _ _ hc κ hκ hQ R _ _ y₀
  letI : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra
  obtain ⟨L, hL, hy⟩ := exists_finite_intermediateField ℚ_[p] (FractionRing V) (PadicAlgCl p) hQ R y₀
  obtain ⟨W, _, _, _, hcW, _, _, _, hcomp, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  let e := FractionRing.algEquiv W L
  let κ' : FractionRing W →+* PadicAlgCl p := L.val.toRingHom.comp e.toRingEquiv.toRingHom
  let fK : FractionRing V →+* FractionRing W :=
    e.symm.toRingEquiv.toRingHom.comp (algebraMap (FractionRing V) L)
  have hfK : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (algebraMap V W a) := by
    intro a
    apply e.injective
    rw [e.commutes]
    have h := congrArg (fun g : V →+* L => g a) hcomp
    exact (e.apply_symm_apply _).trans h.symm
  have hκ' : κ'.comp fK = κ := by
    refine RingHom.ext fun x => ?_
    show ((e (e.symm (algebraMap (FractionRing V) L x)) : L) : PadicAlgCl p) = κ x
    rw [e.apply_symm_apply]
    rfl
  haveI : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  refine ⟨W, inferInstance, inferInstance, inferInstance, hcW, inferInstance, algebraMap V W, fK, κ', hinj, hloc,
    RingHom.finite_algebraMap.2 hfin, hfK, hκ', GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ κ' (fun v => ?_) hκ,
    fun a => ⟨e.symm ⟨y₀ a, hy a⟩, ?_⟩⟩
  · rw [← hfK]
    exact congrArg (fun g : FractionRing V →+* PadicAlgCl p => g (algebraMap V (FractionRing V) v)) hκ'
  · show ((e (e.symm ⟨y₀ a, hy a⟩) : L) : PadicAlgCl p) = y₀ a
    rw [e.apply_symm_apply]

end GlobalTheory.DvrFinExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompleteDvrPadicAlgClStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_complete_dvr_padicAlgCl : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ q : ℚ_[p], algebraMap ℚ_[p] (PadicAlgCl p) q ∈ κ.range) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* PadicAlgCl p), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (maximalIdeal W) W) (_ : CharZero W) (fV : V →+* W) (fK : FractionRing V →+* FractionRing W) (κ' : FractionRing W →+* PadicAlgCl p), Function.Injective fV ∧ IsLocalHom fV ∧ fV.Finite ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (fV a)) ∧ κ'.comp fK = κ ∧ (∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧ ∀ a, y₀ a ∈ κ'.range := by
  first | exact @GlobalTheory.DvrFinExt.exists_finite_extension | exact GlobalTheory.DvrFinExt.exists_finite_extension | (intros; apply GlobalTheory.DvrFinExt.exists_finite_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplication
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplication
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.JInt

theorem not_four_sq {u Δ : ℤ} (hu : Δ ≤ u) (hΔ : 0 < Δ) (r : ℤ) : u ^ 2 + Δ ≠ 4 * (r * r) := by
  intro h
  have h2 : (2 * |r|) ^ 2 = u ^ 2 + Δ := by rw [mul_pow, sq_abs]; linarith
  have hr0 : 0 ≤ 2 * |r| := by positivity
  have hu0 : 0 ≤ u := by linarith
  have a1 : u < 2 * |r| := by nlinarith
  have a2 : 2 * |r| < u + 1 := by nlinarith
  omega

theorem disc_pos {A B C D : ℤ} {τ : ℍ} (hC : C ≠ 0)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : 0 < -((D - A) ^ 2 + 4 * B * C) := by
  set x := (τ : ℂ).re
  set y := (τ : ℂ).im
  have hy : 0 < y := τ.im_pos
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
    Complex.mul_im] at hre him
  have h1 : ((D : ℝ) - A + 2 * C * x) * y = 0 := by linear_combination -him
  have h1' : (D : ℝ) - A + 2 * C * x = 0 := (mul_eq_zero.mp h1).resolve_right hy.ne'
  have key : (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) = 4 * (C : ℝ) ^ 2 * y ^ 2 := by
    push_cast
    linear_combination (-(D : ℝ) + A - 2 * C * x) * h1' - 4 * (C : ℝ) * hre
  have hCr : (0 : ℝ) < (C : ℝ) ^ 2 := by positivity
  have : (0 : ℝ) < (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) := by rw [key]; positivity
  exact_mod_cast this

theorem main : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ) (α : ℂ), IsTauOf L c τ → MulStable L α → α.im ≠ 0 →
    IsIntegral ℤ (jT τ) := by
  intro L c τ α hτ hα him
  obtain ⟨hc, hlat⟩ := hτ
  have h1 : c * (τ : ℂ) ∈ L.lattice := (hlat _).2 ⟨1, 0, by simp⟩
  have h2 : c ∈ L.lattice := (hlat _).2 ⟨0, 1, by simp⟩
  obtain ⟨A, B, hAB⟩ := (hlat _).1 (hα _ h1)
  obtain ⟨C, D, hCD⟩ := (hlat _).1 (hα _ h2)
  have e1 : α * (τ : ℂ) = A * τ + B := by apply mul_left_cancel₀ hc; linear_combination hAB
  have e2 : α = C * τ + D := by apply mul_left_cancel₀ hc; linear_combination hCD
  have hfix : (A : ℂ) * τ + B = τ * (C * τ + D) := by rw [← e1, e2]; ring
  have hC : C ≠ 0 := by
    rintro rfl
    apply him; rw [e2]; simp
  have hΔ := disc_pos hC hfix
  set Δ := -((D - A) ^ 2 + 4 * B * C) with hΔdef
  set t := A + D
  set k := Δ + |t|
  set M := (A + k) * (D + k) - B * C with hM
  have h4M : 4 * M = (2 * k + t) ^ 2 + Δ := by rw [hM, hΔdef]; ring
  have hu : Δ ≤ 2 * k + t := by
    have := neg_abs_le t; have := abs_nonneg t; linarith
  have hMpos : 0 < M := by nlinarith
  have hm : 0 < M.toNat := by omega
  have hMc : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hMpos.le
  refine jT_isIntegral hm ?_ (Gm_vanish hm τ (A + k) B C (D + k) (by rw [hMc]) ?_)
  · rintro ⟨r, hr⟩
    have : M = (r : ℤ) * r := by rw [← hMc, hr]; push_cast; ring
    exact not_four_sq hu hΔ r (by rw [← h4M, this])
  · push_cast; linear_combination hfix

end GlobalTheory.JInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJInvariantOfComplexMultiplicationStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ) (α : ℂ), IsTauOf L c τ → MulStable L α → α.im ≠ 0 → IsIntegral ℤ (jT τ) := by
  first | exact @GlobalTheory.JInt.main | exact GlobalTheory.JInt.main | (intros; apply GlobalTheory.JInt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
noncomputable section

namespace GlobalTheory.HomFixMat

abbrev powPull {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (a : ℤ) : LB Y :=
  LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => a)

theorem wchart_comp_le {X Y Z : Scheme.{0}} (L : LB X) (f : Z ⟶ Y) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f ≫ φ) j ≤ f ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) j := by
  intro y hy
  exact Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    simpa using this

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev topS (Rg : Type) [CommRing Rg] : Over (Sp Rg) := overRes (T := baseOver (Sp Rg)) ⊤

def coord {X : Scheme.{0}} {N : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (n : Fin N) : Γ(X, ⊤) :=
  g.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.X n))

def matOf {X : Scheme.{0}} {mA mB : ℕ} (g : X ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) :
    Fin mA → Fin mB → Γ(X, ⊤) :=
  fun i j => coord g (finProdFinEquiv (i, j))

abbrev affπ (Rg : Type) [CommRing Rg] (N : ℕ) : Sp (MvPolynomial (Fin N) Rg) ⟶ Sp Rg :=
  Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))


variable (A B L M) in
def IsTest {T : Scheme.{0}} (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
    (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') : Prop :=
  IsGrpPullback A' A t φA' ∧ IsGrpPullback B' B t φB' ∧ IsMonHom Φ' ∧
    LBIso (L.pull φA') ((M.pull φB').pull Φ'.left)

def IsPullD {T₁ T₂ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left)
    (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left)
    (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (h : T₂ ⟶ T₁) : Prop :=
  ∃ (ψA : A₂.left ⟶ A₁.left) (ψB : B₂.left ⟶ B₁.left), IsGrpPullback A₂ A₁ h ψA ∧
    IsGrpPullback B₂ B₁ h ψB ∧ ψA ≫ φA₁ = φA₂ ∧ ψB ≫ φB₁ = φB₂ ∧ Φ₂.left ≫ ψB = ψA ≫ Φ₁.left


variable (A L) in
def IsBCBasis (k : ℕ) {m : ℕ} (b : Fin m → LB.Sec (LPow A L (k : ℤ) (topS Rg))) : Prop :=
  ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (topS Rg).left)
    (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))),
    (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) →
    LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧
    Submodule.span Γ((baseAt t).left, ⊤)
      (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}

abbrev isoLB (k : ℕ) {R : Type} [CommRing R] {A' B' : Over (Sp R)} (Φ' : A' ⟶ B')
    (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) : LB A'.left :=
  LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
    (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))

abbrev zeroPt {R : Type} [CommRing R] (A' : Over (Sp R)) [GrpObj A'] : Sp R ⟶ A'.left := η[A'].left


variable (L M) in
def IsMat (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) {R : Type} [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A']
    [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B')
    (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) : Prop :=
  ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left)
    (α : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)),
    ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ α.IsGen ∧
    (∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((zeroPt A').appLE ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_left)).hom (α.s p).val *
        ((t.appLE (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          (inf_le_left.trans inf_le_right)).hom (eA.s (fun _ => p.2 0)).val) ^ k =
      ((t.appLE (LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          ((zeroPt A') ⁻¹ᵁ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ⊓
            t ⁻¹ᵁ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => p.2 0) ⊓
            t ⁻¹ᵁ LB.wchart M (fun _ : PUnit => eSec B) (fun _ => p.1 0))
          inf_le_right).hom (eB.s (fun _ => p.1 0)).val) ^ k) ∧
    ∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}


variable (L M) in
def Hyps (k : ℕ) {mA mB : ℕ} (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg)))
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A)))
    (eB : LB.Gen (M.pull (eSec B))) : Prop :=
  IsAbelianScheme A ∧ IsAbelianScheme B ∧ L.IsLB ∧ M.IsLB ∧ eA.IsGen ∧ eB.IsGen ∧ RelAmple A L ∧ 1 ≤ k ∧
    VeryAmpleAt B M k ∧ IsBCBasis A L k bA ∧ IsBCBasis B M k bB

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat
variable {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B]

theorem IsPullD.comp {T₁ T₂ T₃ : Scheme.{0}} {A₁ B₁ : Over T₁} [GrpObj A₁] [GrpObj B₁] {φA₁ : A₁.left ⟶ A.left}
    {φB₁ : B₁.left ⟶ B.left} {Φ₁ : A₁ ⟶ B₁} {A₂ B₂ : Over T₂} [GrpObj A₂] [GrpObj B₂] {φA₂ : A₂.left ⟶ A.left}
    {φB₂ : B₂.left ⟶ B.left} {Φ₂ : A₂ ⟶ B₂} {A₃ B₃ : Over T₃} [GrpObj A₃] [GrpObj B₃] {φA₃ : A₃.left ⟶ A.left}
    {φB₃ : B₃.left ⟶ B.left} {Φ₃ : A₃ ⟶ B₃} {h₁ : T₂ ⟶ T₁} {h₂ : T₃ ⟶ T₂}
    (p₁ : IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h₁) (p₂ : IsPullD φA₂ φB₂ Φ₂ φA₃ φB₃ Φ₃ h₂) :
    IsPullD φA₁ φB₁ Φ₁ φA₃ φB₃ Φ₃ (h₂ ≫ h₁) := by
  obtain ⟨ψA, ψB, qA, qB, eA, eB, eΦ⟩ := p₁
  obtain ⟨ψA', ψB', qA', qB', eA', eB', eΦ'⟩ := p₂
  refine ⟨ψA' ≫ ψA, ψB' ≫ ψB, qA'.comp qA, qB'.comp qB, by rw [Category.assoc, eA, eA'],
    by rw [Category.assoc, eB, eB'], ?_⟩
  rw [← Category.assoc, eΦ', Category.assoc, eΦ, Category.assoc]

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem hom_ext_affine (Rg : Type) [CommRing Rg] (N : ℕ) (X : Scheme.{0}) (g g' : X ⟶ Sp (MvPolynomial (Fin N) Rg))
    (h0 : g ≫ affπ Rg N = g' ≫ affπ Rg N) (h1 : ∀ n, coord g n = coord g' n) : g = g' := by
  apply ext_of_isAffine
  refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))) _ _).1 ?_
  ext1
  apply MvPolynomial.ringHom_ext
  · intro r
    have e := congrArg (fun f => f.appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)) h0
    simp only [Scheme.Hom.comp_appTop] at e
    have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin N) Rg))).inv (MvPolynomial.C r) =
        (affπ Rg N).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp]
    rw [n2]
    simpa using e
  · intro n
    exact h1 n

end GlobalTheory.HomFixMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module

variable {F : Type} [Field F] {r : ℕ}

def colSet (F : Type) [Field F] (b : Fin r → ℕ) (k : ℕ) : Set (blockTri (κ := F) b) :=
  {p | (p : GL (Fin r) F) ∈ unip F r ∧ ∀ i j : Fin r, j.val < k →
    ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j}

def colChar (ψ : AddChar F ℂ) (b : Fin r → ℕ) (k : Fin r) (l : Fin r → F) (p : blockTri (κ := F) b) : ℂ :=
  ψ (∑ i, l i * ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k +
    edgeSum (fun i j => blkEdge b i j ∧ k < j) (p : GL (Fin r) F))

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ : G → ℂ) (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem eig_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ χ' : G → ℂ) (h : ∀ g ∈ S, χ g = χ' g) : eig τ S χ = eig τ S χ' := by
  ext v
  simp only [mem_eig]
  exact forall₂_congr fun g hg => by rw [h g hg]

end GlobalTheory.FinGL.LeviWh
end
end
