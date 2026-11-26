module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointThLeSpanGood

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorISignatureConjApplyOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorISignatureConjApplyOne
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section
namespace GlobalTheory.HeisTwist

theorem jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => (-1 : ℂ))) := by
  rw [Jm, Formalism.UG.Jpq, ← Matrix.fromBlocks_diagonal]
  simp [Matrix.diagonal_neg]
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]

theorem jm_mul_mul_jm_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (a : Ix P Q) (b : Ix R S) :
    (Jm P Q * c * Jm R S) a b = lineSign a b * c a b := by
  rw [jm_eq_diagonal, jm_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (l : Ln P Q R S) :
    (Complex.I * lineSign l.1 l.2 * c l.1 l.2) • raiB l (1 : Pol P Q R S)
      - (lineSign l.1 l.2 * star (Complex.I * lineSign l.1 l.2 * c l.1 l.2)) • lowB l 1
      = Complex.I • (c l.1 l.2 • raiB l (1 : Pol P Q R S) - (lineSign l.1 l.2 * star (c l.1 l.2)) • lowB l 1) := by
  rcases l with ⟨a | a, b | b⟩ <;>
    simp [raiB, lowB, linePos, lineSign, smul_sub, smul_smul] <;> ring_nf <;> simp [Complex.conj_I] <;> module

end GlobalTheory.HeisTwist

namespace GlobalTheory.RealLift

theorem heisOp_twist_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := by
  simp only [heisOp, LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_comm Complex.I]
  congr 1
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Matrix.smul_apply,
    GlobalTheory.HeisTwist.jm_mul_mul_jm_apply, smul_eq_mul]
  rw [← GlobalTheory.HeisTwist.term_one c l, mul_assoc]

end GlobalTheory.RealLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorISignatureConjApplyOneStatement
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHeisenbergOperator_I_signatureConj_apply_one : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ), heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := by
  first | exact @GlobalTheory.RealLift.heisOp_twist_one | exact GlobalTheory.RealLift.heisOp_twist_one | (intros; apply GlobalTheory.RealLift.heisOp_twist_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyPadicBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderEmbeddingOpenImmersion
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PadicPolys

theorem minpoly_coeff_bdd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1),
      f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ),
        ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  intro p _ G K' f' hf β
  obtain ⟨k0, hk0⟩ := GlobalTheory.AtPBd.main p G 1 K' f' one_pos hf
  set R : ℝ := (p : ℝ) ^ k0 with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  refine ⟨max (R * R) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y h hy φ k
  have hnrm : IsNrm G 1 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h := by
    show nrmG (sigG G 1) 1 _ = _
    simp [nrmG]
    rfl
  obtain ⟨hs, -, hrt, hrti⟩ := hk0 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h 1 hnrm (by simpa using hy)
  set yC : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyC
  have hint : IsIntegral G.F yC := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly G.F yC).Monic := minpoly.monic hint
  have hsn : ‖(((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)‖ ≤ R := by
    rw [← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
    exact hs
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hroot : ∀ μ ∈ ((minpoly G.F yC).map φ).roots, ‖μ‖ ≤ R * R := by
    intro μ hμ
    have hμ' : ((minpoly G.F yC).map φ).IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
    rcases GlobalTheory.GlobEig.liesOver_or_conj G φ with hφ | hφ
    · obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G φ hφ yC μ hμ'
      rw [← hν]
      exact (hrt i ν hνr).trans (le_mul_of_one_le_left (by linarith) hR1)
    · have h2 := GlobalTheory.GlobEig.isRoot_minpoly_sh G yC φ μ hμ'
      obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G _ hφ (sh G yC) μ h2
      have h3 := GlobalTheory.GlobEig.isRoot_inv G i β (y : G.Cˣ × ℚˣ).1 (y : G.Cˣ × ℚˣ).2 y.2.1 ν hνr
      have h4 := hrti i _ h3
      rw [← hν]
      have e : ν = ν * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)⁻¹ * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) := by
        field_simp
      rw [e, norm_mul]
      exact mul_le_mul h4 hsn (norm_nonneg _) (by linarith)
  have hdeg : (minpoly G.F yC).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le yC
  rw [← Polynomial.coeff_map]
  exact Polynomial.coeff_bdd_of_roots_le φ hmon (IsAlgClosed.splits _) hdeg hroot k

end GlobalTheory.LKCx.PadicPolys
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1), f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ), ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  first | (exact @GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd) | (exact GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd) | (intros; apply GlobalTheory.LKCx.PadicPolys.minpoly_coeff_bdd  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestriction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestriction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


open Classical in
theorem GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χ n → ResEta D χ n := by
  intro D χ n h
  refine ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η hη a => ?_⟩
  have hsq : ∀ x, η x * η x = 1 := GlobalTheory.VolHeckeCompare.IsEta_mul_self hη
  obtain ⟨-, h1, h2, h3⟩ := hη
  set S := (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range ⊔
    (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F)).range with hSdef
  have key : ∀ x, ((χ (idF D x) : Circle) : ℂ) = if x ∈ S then 1 else (-1) ^ n := fun x => h x
  have hS : ∀ x ∈ S, η x = 1 := by
    have : S ≤ η.ker := sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    exact fun x hx => this hx
  apply Circle.ext
  rw [key a, Circle.coe_pow]
  by_cases ha : a ∈ S
  · rw [if_pos ha, hS a ha]; simp
  rw [if_neg ha]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hn
  · rw [← two_mul, pow_mul, pow_mul, neg_one_sq, one_pow, ← Circle.coe_pow, sq, hsq a]; simp
  have hn1 : ((-1 : ℂ)) ^ n = -1 := hn.neg_one_pow
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push_neg at hh
    exact h3 (MonoidHom.ext hh)
  have hbS : b ∉ S := fun hm => hb (hS b hm)
  have hab : a * b ∈ S := by
    by_contra hn2
    have e := key (a * b)
    rw [map_mul, map_mul, Circle.coe_mul, key a, key b, if_neg ha, if_neg hbS, if_neg hn2, hn1] at e
    norm_num at e
  have hηb : (η b : ℂ) = -1 := GlobalTheory.VolHeckeCompare.circle_eq_neg_one (hsq b) hb
  have e2 : (η a : ℂ) * η b = 1 := by rw [← Circle.coe_mul, ← map_mul, hS _ hab]; simp
  rw [hηb] at e2
  have hηa : (η a : ℂ) = -1 := by linear_combination -e2
  rw [hηa]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowIdelicRestrictionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ),
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χ n → ResEta D χ n := by
  first | exact @GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow | exact GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow | (intros; apply GlobalTheory.ResEtaOfPow.resEta_of_resEtaPow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDifferentialMulLogCoordinateWedge
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDifferentialMulLogCoordinateWedge
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.WedgeMul

theorem prod_perm_sign {A : Type} [Ring A] {α : Type} (f : α → A)
    (hf : ∀ a b, f a * f b = -(f b * f a)) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (l₁.map f).prod = ε • (l₂.map f).prod := by
  induction h with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons x _ ih =>
    obtain ⟨ε, hε, e⟩ := ih
    exact ⟨ε, hε, by simp only [List.map_cons, List.prod_cons, e, mul_smul_comm]⟩
  | swap x y l =>
    refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [List.map_cons, List.prod_cons, ← mul_assoc, hf y x, neg_mul, neg_smul, one_smul]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨ε₁, h₁, e₁⟩ := ih₁
    obtain ⟨ε₂, h₂, e₂⟩ := ih₂
    refine ⟨ε₁ * ε₂, ?_, by rw [e₁, e₂, smul_smul]⟩
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

end GlobalTheory.LogDR.WedgeMul


open GlobalTheory.LogDR.WedgeMul in
theorem GlobalTheory.LogDR.dlog_mul_logWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n) (I : Finset (Fin n)), (i ∈ I → ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = 0) ∧ (i ∉ I → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = ε • logWedge x (insert i I)) := by
  intro K _ n x i I
  set f : Fin n → abelian₂ K := fun j => ExteriorAlgebra.ι K (dlog (x j)) with hfdef
  have hf : ∀ a b, f a * f b = -(f b * f a) := fun a b =>
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  constructor
  · intro hi
    have hp : (I.sort (· ≤ ·)).Perm (i :: (I.erase i).sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · refine List.nodup_cons.2 ⟨?_, Finset.sort_nodup _ _⟩
        simp
      · by_cases ha : a = i
        · subst ha; simp [hi]
        · simp [ha]
    obtain ⟨ε, -, e⟩ := prod_perm_sign f hf hp
    show f i * ((I.sort (· ≤ ·)).map f).prod = 0
    rw [e, mul_smul_comm, List.map_cons, List.prod_cons, ← mul_assoc]
    simp [hfdef, ExteriorAlgebra.ι_sq_zero]
  · intro hi
    have hp : ((insert i I).sort (· ≤ ·)).Perm (i :: I.sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · exact List.nodup_cons.2 ⟨by simpa using hi, Finset.sort_nodup _ _⟩
      · simp
    obtain ⟨ε, hε, e⟩ := prod_perm_sign f hf hp
    refine ⟨ε, hε, ?_⟩
    show f i * ((I.sort (· ≤ ·)).map f).prod = ε • (((insert i I).sort (· ≤ ·)).map f).prod
    rw [e, List.map_cons, List.prod_cons, smul_smul]
    rcases hε with rfl | rfl <;> simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDifferentialMulLogCoordinateWedgeStatement
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDifferential_mul_logCoordinateWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n) (I : Finset (Fin n)), (i ∈ I → ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = 0) ∧ (i ∉ I → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = ε • logWedge x (insert i I)) := by
  first | exact @GlobalTheory.LogDR.dlog_mul_logWedge | exact GlobalTheory.LogDR.dlog_mul_logWedge | (intros; apply GlobalTheory.LogDR.dlog_mul_logWedge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominators
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.BoundedDen

theorem den_factorization_le (p : ℕ) [Fact p.Prime] (q : ℚ) (M : ℕ) (hM : 0 < M) (k : ℤ) (e : ℕ)
    (h : q * ((M : ℚ) * (p : ℚ) ^ e) = k) (ℓ : ℕ) (hℓ : ℓ ≠ p) :
    q.den.factorization ℓ ≤ M.factorization ℓ := by
  have hp : p.Prime := Fact.out
  have hN : ((M * p ^ e : ℕ) : ℚ) ≠ 0 := by
    have : 0 < M * p ^ e := Nat.mul_pos hM (pow_pos hp.pos e)
    exact_mod_cast this.ne'
  have hq : q = Rat.divInt k ((M * p ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast at hN ⊢
    rw [eq_div_iff hN]; exact h
  have hd : q.den ∣ M * p ^ e := by
    have := Rat.den_dvd k ((M * p ^ e : ℕ) : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  have hle := (Nat.factorization_le_iff_dvd q.den_nz (Nat.mul_pos hM (pow_pos hp.pos e)).ne').2 hd ℓ
  rw [Nat.factorization_mul hM.ne' (pow_pos hp.pos e).ne', Nat.factorization_pow, hp.factorization] at hle
  simpa [Finsupp.single_apply, Ne.symm hℓ] using hle

end GlobalTheory.LKCx.BoundedDen

namespace GlobalTheory.LKCx.BoundedDen

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  intro p _ G β x t hx L f hf h₁
  obtain ⟨Ω, Ω', hΩ, hΩ', hmem⟩ := exists_compact_toAfF p G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  let b := Module.finBasis ℚ G.C
  let b' := b.baseChange (AfP p)
  have hcpt : ∀ i, IsCompact ((b'.coord i) '' Ω) := fun i =>
    hΩ.image (IsModuleTopology.continuous_of_linearMap (b'.coord i))
  choose m hm0 hm using fun i => GlobalTheory.DenAway.den_bounded_of_isCompact p _ (hcpt i)
  obtain ⟨M', hM'0, hM'⟩ := GlobalTheory.DenAway.den_bounded_of_isCompact p Ω' hΩ'
  refine ⟨(∏ i, m i) * M', Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0, fun y hy ℓ hℓ => ⟨fun i => ?_, ?_⟩⟩
  · have hval : b'.coord i (inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
        algebraMap ℚ (AfP p) (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) := by
      simp only [inC, b', RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Module.Basis.coord_apply,
        Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    obtain ⟨k, e, hk⟩ := hm i (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) (by rw [← hval]; exact ⟨_, (hmem y hy).1, rfl⟩)
    have h1 := den_factorization_le p _ (m i) (hm0 i) k e hk ℓ hℓ
    have hd : m i ∣ (∏ j, m j) * M' := (Finset.dvd_prod_of_mem m (Finset.mem_univ i)).mul_right _
    exact h1.trans ((Nat.factorization_le_iff_dvd (hm0 i).ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 hd ℓ)
  · have e0 : ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ := Units.val_inv_eq_inv_val _
    obtain ⟨k, e, hk⟩ := hM' _ (hmem y hy).2
    rw [e0]
    have h1 := den_factorization_le p _ M' hM'0 k e hk ℓ hℓ
    exact h1.trans ((Nat.factorization_le_iff_dvd hM'0.ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 (dvd_mul_left _ _) ℓ)

end GlobalTheory.LKCx.BoundedDen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominatorsStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formGroup_testFunction_support_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  first | (exact @GlobalTheory.LKCx.BoundedDen.main) | (exact GlobalTheory.LKCx.BoundedDen.main) | (intros; apply GlobalTheory.LKCx.BoundedDen.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsHilbertModuleExists
open Formalism.IndefR Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.AdFormsModel

section

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ι : Γ →* G} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {I : Type} {y : I → G}

theorem eq_zero_of_reps (hy : Bridge.IsReps ι J y) {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ)
    (h0 : ∀ i, F (y i) = 0) : F = 0 := by
  funext h
  obtain ⟨i, ⟨γ, k, rfl⟩, -⟩ := hy h
  have := hF γ (y i) k
  rw [this, h0 i]
  simp

theorem finiteDimensional_adForms [FiniteDimensional ℂ W] [Finite I] (hy : Bridge.IsReps ι J y) :
    FiniteDimensional ℂ (Bridge.AdForms ι ρ J χ) := by
  let ev : Bridge.AdForms ι ρ J χ →ₗ[ℂ] (I → W) :=
    (LinearMap.funLeft ℂ W y).comp (Bridge.AdForms ι ρ J χ).subtype
  refine FiniteDimensional.of_injective ev ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro F hF
  exact Subtype.ext (eq_zero_of_reps hy F.2 fun i => congrFun hF i)

theorem adInner_self_pos [Fintype I] (hy : Bridge.IsReps ι J y) (hs : ∀ i, Finite (Bridge.stab ι J (y i)))
    {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ) (hne : F ≠ 0) : 0 < (Bridge.adInner ι J y F F).re := by
  have hre : (Bridge.adInner ι J y F F).re =
      ∑ i, ((Nat.card (Bridge.stab ι J (y i)) : ℝ))⁻¹ * ‖F (y i)‖ ^ 2 := by
    unfold Bridge.adInner
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K]
    have : ((Nat.card (Bridge.stab ι J (y i)) : ℂ))⁻¹ * ((‖F (y i)‖ : ℝ) : ℂ) ^ 2 =
        ((((Nat.card (Bridge.stab ι J (y i)) : ℝ))⁻¹ * ‖F (y i)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; rfl
    exact (congrArg Complex.re this).trans (Complex.ofReal_re _)
  rw [hre]
  obtain ⟨i, hi⟩ : ∃ i, F (y i) ≠ 0 := by
    by_contra hcon
    exact hne (eq_zero_of_reps hy hF fun i => by
      by_contra h
      exact hcon ⟨i, h⟩)
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, ?_⟩
  haveI := hs i
  have h1 : (0 : ℝ) < (Nat.card (Bridge.stab ι J (y i)) : ℝ) := by exact_mod_cast Nat.card_pos
  have h2 : 0 < ‖F (y i)‖ := norm_pos_iff.2 hi
  positivity

end

theorem exists_hmod_adForms : ∀ (G Γ W : Type) [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (I : Type)
    [Fintype I] (y : I → G), Bridge.IsReps ι J y → (∀ i, Finite (Bridge.stab ι J (y i))) →
    ∃ M : HMod (G → W), M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y) := by
  intro G Γ W _ _ _ _ _ ι ρ J χ I _ y hy hs
  refine GlobalTheory.HilbertModel.exists_hmod (G → W) _ _ (finiteDimensional_adForms hy) ?_
    (fun F hF hne => adInner_self_pos hy hs hF hne)
  intro a _ b _ d _ c
  constructor
  · simp only [Bridge.adInner, Pi.add_apply, Pi.smul_apply, inner_add_right, inner_smul_right, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · simp only [Bridge.adInner, star_sum, star_mul', star_inv₀, star_natCast]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← inner_conj_symm (b (y i)) (a (y i))]
    rfl

end GlobalTheory.AdFormsModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDim
set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ChowHt

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_isChowFormInt_of_ringKrullDim_eq (K : Type) [Field K] (N D : ℕ)
    (P : Ideal (MvPolynomial (Fin N) K)) (hP : P.IsPrime)
    (hh : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ)) :
    ∃ (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f := by
  classical
  have hI : P.IsHomogeneous (homogeneousSubmodule (Fin N) K) := by
    intro n g hg
    have h1 : (DirectSum.decompose (homogeneousSubmodule (Fin N) K) g n : MvPolynomial (Fin N) K) =
        homogeneousComponent n g := MvPolynomial.decomposition.decompose'_apply g n
    rw [h1]
    exact hh g hg n
  have hX : ∃ j, X j ∉ P := by
    by_contra hc
    push Not at hc
    have h0 := GlobalTheory.ringKrullDim_quotient_le_zero_of_forall_X_mem hc
    rw [hdim] at h0
    have h1 : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by simpa using h0
    have h2 : D + 1 ≤ 0 := by exact_mod_cast h1
    omega
  have hdim' : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (Fintype.card (Fin (D + 1)) : ℕ) := by
    rw [Fintype.card_fin]; exact hdim
  have hprime : (GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P).IsPrime := GlobalTheory.Chow.isPrime_elimIdeal hX
  have hne : GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P ≠ ⊥ := GlobalTheory.Chow.elimIdeal_ne_bot hI hX hdim'.le
  obtain ⟨f, hf⟩ := (GlobalTheory.Chow.isPrincipal_elimIdeal hdim').principal
  have hf' : GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P = Ideal.span {f} := hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hne (by rw [hf', Ideal.span_singleton_eq_bot])
  have hfmem : f ∈ GlobalTheory.Chow.elimIdeal (β := Fin (D + 1)) P := hf' ▸ Ideal.subset_span rfl
  have hfp : Prime f := (Ideal.span_singleton_prime hf0).1 (hf' ▸ hprime)
  obtain ⟨a, ha⟩ := GlobalTheory.Chow.exists_isWeightedHomogeneous_of_dvd
    (GlobalTheory.Chow.blockWeight : Fin (D + 1) × Fin N → Fin (D + 1) → ℕ) (f := f) (fun a => by
      rw [← Ideal.mem_span_singleton, ← hf']
      exact GlobalTheory.Chow.weightedHomogeneousComponent_mem_elimIdeal hfmem a)
  have ha' : GlobalTheory.Chow.IsBlockHomogeneous f a := ha
  have hconst : ∀ i, a i = a 0 := by
    intro i
    have h1 := GlobalTheory.Chow.map_rename_elimIdeal (Equiv.swap i 0) P
    rw [hf', Ideal.map_span, Set.image_singleton] at h1
    obtain ⟨c, hc, hcf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_span_eq h1
    have h2 : GlobalTheory.Chow.IsBlockHomogeneous f (a ∘ (Equiv.swap i 0).symm) := by
      rw [hcf]
      exact IsWeightedHomogeneous.C_mul (ha'.rename (Equiv.swap i 0)) c
    have h3 := congrFun (GlobalTheory.Chow.IsBlockHomogeneous.unique hf0 ha' h2) i
    simpa using h3
  refine ⟨a 0, f, ?_, hfp.irreducible, fun u => ?_⟩
  · rw [isMultiHomogeneous_iff_block, ← (funext hconst : a = fun _ => a 0)]
    exact ha'
  · rw [← GlobalTheory.Chow.forall_aeval_eq_zero_iff hI u, hf']
    refine ⟨fun hu p hp => ?_, fun hu => hu f (Ideal.subset_span rfl)⟩
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    rw [map_mul, hu, mul_zero]

end GlobalTheory.ChowHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChowFormOfHomogeneousPrimeKrullDimStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chowForm_of_homogeneous_prime_krullDim : ∀ (K : Type) [Field K] (N D : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ) → ∃ (δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f := by
  first | exact @GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | exact GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq | (intros; apply GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCo
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

set_option autoImplicit false

namespace GlobalTheory.CoverDeg

theorem exists_goodCover_of_coords_of_cover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (x : X) (U₁ U₂ : X.Opens), IsAffineOpen U₁ → x ∈ U₁ → (∃ t : Fin D → Γ(X, U₁), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t).Etale) → IsAffineOpen U₂ → x ∈ U₂ → IsAffineOpen (π ⁻¹ᵁ U₂) → (π.app U₂).hom.Etale → (π.app U₂).hom.Finite → (letI := (π.app U₂).hom.toAlgebra; Module.Free Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) ∧ Module.finrank Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) = δ) → ∃ U : X.Opens, x ∈ U ∧ GlobalTheory.CoverDeg.GoodCover p π D δ U := by
  intro k _ X Y p π D δ x U₁ U₂ hU₁ hx₁ ⟨t, ht⟩ hU₂ hx₂ hV₂ he hf hfr
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU₁ hU₂ x ⟨hx₁, hx₂⟩
  have hxU : x ∈ X.basicOpen g := hfg ▸ hxf
  refine ⟨X.basicOpen g, hxU, ?_⟩
  have hUU₁ : X.basicOpen g ≤ U₁ := hfg ▸ X.basicOpen_le f
  have hUU₂ : X.basicOpen g ≤ U₂ := X.basicOpen_le g
  have hUa : IsAffineOpen (X.basicOpen g) := hU₂.basicOpen g
  have hpre : π ⁻¹ᵁ X.basicOpen g = Y.basicOpen (π.app U₂ g) := Scheme.preimage_basicOpen π g
  have hVa : IsAffineOpen (π ⁻¹ᵁ X.basicOpen g) := hpre ▸ hV₂.basicOpen _
  have hVV₂ : π ⁻¹ᵁ X.basicOpen g ≤ π ⁻¹ᵁ U₂ := fun _ h => hUU₂ h
  refine ⟨hUa, hVa, ?_, ?_⟩
  · refine ⟨fun i => resG X hUU₁ (t i), ?_⟩
    have e : MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen g)) (fun i => resG X hUU₁ (t i)) =
        (resG X hUU₁).comp (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG X hUU₁).Etale := by
      letI : Algebra Γ(X, U₁) Γ(X, X.basicOpen g) := (resG X hUU₁).toAlgebra
      haveI : IsLocalization.Away f Γ(X, X.basicOpen g) :=
        hU₁.isLocalization_of_eq_basicOpen f (homOfLE hUU₁) hfg.symm
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ ht hR
  · letI i1 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := (π.app U₂).hom.toAlgebra
    letI i2 : Algebra Γ(X, U₂) Γ(X, X.basicOpen g) := (resG X hUU₂).toAlgebra
    letI i3 : Algebra Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (resG Y hVV₂).toAlgebra
    letI i4 : Algebra Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) := (π.app (X.basicOpen g)).hom.toAlgebra
    letI i5 : Algebra Γ(X, U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      ((π.app (X.basicOpen g)).hom.comp (resG X hUU₂)).toAlgebra
    have hnat : (π.app (X.basicOpen g)).hom.comp (resG X hUU₂) = (resG Y hVV₂).comp (π.app U₂).hom := by
      ext a
      exact congr($(π.naturality (homOfLE hUU₂).op) a)
    haveI : IsScalarTower Γ(X, U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      IsScalarTower.of_algebraMap_eq' hnat
    haveI : IsLocalization.Away g Γ(X, X.basicOpen g) :=
      hU₂.isLocalization_of_eq_basicOpen g (homOfLE hUU₂) rfl
    haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g))
        Γ(Y, π ⁻¹ᵁ X.basicOpen g) := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      exact hV₂.isLocalization_of_eq_basicOpen (π.app U₂ g) (homOfLE hVV₂) hpre
    haveI hpo : Algebra.IsPushout Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Algebra.isPushout_of_isLocalization (Submonoid.powers g) Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ U₂)
        Γ(Y, π ⁻¹ᵁ X.basicOpen g)
    have het : (algebraMap Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g)).Etale :=
      RingHom.Etale.isStableUnderBaseChange _ _ _ _ he
    haveI : Module.Finite Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) := hf
    haveI hfin : Module.Finite Γ(X, X.basicOpen g) Γ(Y, π ⁻¹ᵁ X.basicOpen g) :=
      Module.Finite.of_isLocalization Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) (Submonoid.powers g)
    refine ⟨het, hfin, ?_⟩
    obtain ⟨hfree, hrk⟩ := hfr
    haveI : Nontrivial Γ(X, X.basicOpen g) := (X.presheaf.germ _ x hxU).hom.domain_nontrivial
    haveI : Nontrivial Γ(X, U₂) := (X.presheaf.germ _ x hx₂).hom.domain_nontrivial
    let b := Module.Free.chooseBasis Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂)
    let b' := hpo.symm.out.basis b
    refine ⟨Module.Free.of_basis b', ?_⟩
    rw [Module.finrank_eq_card_basis b', ← hrk, Module.finrank_eq_card_basis b]

end GlobalTheory.CoverDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenEtaleCoordinatesFiniteFreeEtaleCoStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_etaleCoordinates_finiteFreeEtaleCover : ∀ {k : Type} [CommRing k] {X Y : Scheme.{0}} (p : X ⟶ Sp k) (π : Y ⟶ X) (D δ : ℕ) (x : X) (U₁ U₂ : X.Opens), IsAffineOpen U₁ → x ∈ U₁ → (∃ t : Fin D → Γ(X, U₁), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₁) t).Etale) → IsAffineOpen U₂ → x ∈ U₂ → IsAffineOpen (π ⁻¹ᵁ U₂) → (π.app U₂).hom.Etale → (π.app U₂).hom.Finite → (letI := (π.app U₂).hom.toAlgebra; Module.Free Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) ∧ Module.finrank Γ(X, U₂) Γ(Y, π ⁻¹ᵁ U₂) = δ) → ∃ U : X.Opens, x ∈ U ∧ GlobalTheory.CoverDeg.GoodCover p π D δ U := by
  first | exact @GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover | exact GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover | (intros; apply GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqHolomorphicLowestKTypeSubRootLt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqHolomorphicLowestKTypeSubRootLt
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.VoganRoot

open Finset Formalism.REAL

theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a = ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  have h1 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      = n - 1 - a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h2 : (univ.filter fun b => b < a ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have ha := a.2
  have h3 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      + a + 1 = n := by omega
  have h3' := congrArg (Nat.cast : ℕ → ℝ) h3
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  push_cast at h3' h2'
  unfold Formalism.REAL.rhoN Formalism.REAL.rhoC
  linarith

theorem nsq_sub_root {n : ℕ} (u : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    Formalism.REAL.nsq (u - Formalism.REAL.root a b) = Formalism.REAL.nsq u - 2 * (u a - u b) + 2 := by
  have : ∀ i, (u - Formalism.REAL.root a b) i * (u - Formalism.REAL.root a b) i =
      u i * u i - 2 * ((if i = a then u i else 0) - (if i = b then u i else 0)) +
        ((if i = a then 1 else 0) + (if i = b then 1 else 0)) := by
    intro i
    simp only [Formalism.REAL.root, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [h1, h2, hab, hab.symm]
    all_goals ring
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  norm_num

theorem vNormSq_lowK_sub_root_lt {n : ℕ} (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : StrictAnti μ)
    {a b : Fin n} (hab : a < b) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b) < Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ) := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [show Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b + (2 : ℝ) • Formalism.REAL.rhoC ε
      = (Formalism.QuantumDeterminants.lowK ε μ + (2 : ℝ) • Formalism.REAL.rhoC ε) - Formalism.REAL.root a b by abel,
    nsq_sub_root _ hab.ne]
  have h1 := hμ hab
  have h2 := rhoN_add_rhoC ε a
  have h3 := rhoN_add_rhoC ε b
  have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

end GlobalTheory.HolDict.VoganRoot

theorem GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → ∀ a c : Fin n, ε a = true → ε c = false → vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam - Formalism.REAL.root a c) < vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) := by
  intro n p ε lam hl hε a c ha hc
  rw [hε] at ha hc
  have hac : a < c := by
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ha hc
    exact Fin.lt_def.mpr (by omega)
  exact GlobalTheory.HolDict.VoganRoot.vNormSq_lowK_sub_root_lt ε hl.1 hac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqHolomorphicLowestKTypeSubRootLtStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.voganNormSq_holomorphicLowestKType_sub_root_lt : ∀ (n p : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → (∀ a, ε a = decide ((a : ℕ) < p)) → ∀ a c : Fin n, ε a = true → ε c = false → vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam - Formalism.REAL.root a c) < vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) := by
  first | exact @GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt | exact GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt | (intros; apply GlobalTheory.HolDict.vNormSq_lowK_sub_noncompact_root_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCentralizerTranslate
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.TorusNorm

theorem exists_compact_mod_sim (Z S : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z]
    [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z]
    [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [SigmaCompactSpace S]
    [T2Space S] (hZ : ∀ a b : Z, a * b = b * a) (hS : ∀ a b : S, a * b = b * a)
    (τ : Z →* Z) (hτc : Continuous τ) (hτi : ∀ z, τ (τ z) = z)
    (hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s)
    (ι : S →* Z) (hιc : Continuous ι) (hτι : ∀ a, τ (ι a) = ι a)
    (hU : ∃ U ∈ nhds (1 : S), ∀ a ∈ U, a * a = 1 → a = 1) (D : Set Z) (hD : IsCompact D) :
    ∃ B : Set Z, IsCompact B ∧ ∀ (z : Z) (a : S), τ z * z * (ι a)⁻¹ ∈ D →
      ∃ u : Z, ∃ l : S, τ u * u = ι l ∧ ∃ b ∈ B, z = u * b := by
  let T : Z × S →* Z × S :=
    { toFun := fun h => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
      map_one' := by simp
      map_mul' := fun h k => by
        ext
        · show τ (h.1 * k.1) * (ι (h.2 * k.2))⁻¹ = τ h.1 * (ι h.2)⁻¹ * (τ k.1 * (ι k.2)⁻¹)
          rw [map_mul, map_mul, _root_.mul_inv_rev, hZ (ι k.2)⁻¹ (ι h.2)⁻¹]
          simp only [mul_assoc]
          congr 1
          rw [← mul_assoc, ← mul_assoc, hZ (ι h.2)⁻¹ (τ k.1)]
        · show (h.2 * k.2)⁻¹ = h.2⁻¹ * k.2⁻¹
          rw [_root_.mul_inv_rev, hS] }
  have hT : ∀ h, T h = (τ h.1 * (ι h.2)⁻¹, h.2⁻¹) := fun h => rfl
  have hcomm : ∀ a b : Z × S, a * b = b * a := fun a b => Prod.ext (hZ _ _) (hS _ _)
  have hTc : Continuous T := by
    show Continuous fun h : Z × S => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
    exact ((hτc.comp continuous_fst).mul (hιc.comp continuous_snd).inv).prodMk continuous_snd.inv
  have hTi : ∀ h, T (T h) = h := by
    intro h
    rw [hT, hT]
    ext
    · simp only [map_mul, map_inv, hτi, hτι, inv_inv]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    · simp
  obtain ⟨W, hW, hWs⟩ := hsq
  obtain ⟨U, hU1, hUs⟩ := hU
  have hsqT : ∃ W' ∈ nhds (1 : Z × S), ∀ s ∈ W', T s = s → ∃ r : Z × S, T r = r ∧ r * r = s := by
    refine ⟨W ×ˢ U, prod_mem_nhds hW hU1, fun s hs hTs => ?_⟩
    have h2 : s.2⁻¹ = s.2 := congrArg Prod.snd hTs
    have ha : s.2 = 1 := hUs _ hs.2 (by
      calc s.2 * s.2 = s.2 * s.2⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _)
    have h1 : τ s.1 * (ι s.2)⁻¹ = s.1 := congrArg Prod.fst hTs
    rw [ha, map_one, inv_one, mul_one] at h1
    obtain ⟨r, hr, hrr⟩ := hWs _ hs.1 h1
    refine ⟨(r, 1), ?_, ?_⟩
    · rw [hT]; simp [hr]
    · ext
      · exact hrr
      · simp [ha]
  haveI : T2Space (Z × S) := inferInstance
  obtain ⟨B, hB, hBs⟩ := GlobalTheory.InvolutionNorm.exists_compact_mod_kernel (Z × S) hcomm T hTc hTi hsqT
    (D ×ˢ {1}) (hD.prod isCompact_singleton)
  refine ⟨Prod.fst '' B, hB.image continuous_fst, fun z a hz => ?_⟩
  have hmem : T (z, a) * (z, a) ∈ D ×ˢ ({1} : Set S) := by
    rw [hT]
    refine ⟨?_, ?_⟩
    · show τ z * (ι a)⁻¹ * z ∈ D
      rw [mul_assoc, hZ (ι a)⁻¹ z, ← mul_assoc]; exact hz
    · show a⁻¹ * a = 1
      exact inv_mul_cancel a
  obtain ⟨t, ht, b, hb, hzb⟩ := hBs _ hmem
  refine ⟨t.1, t.2, ?_, b.1, ⟨b, hb, rfl⟩, congrArg Prod.fst hzb⟩
  have h1 : τ t.1 * (ι t.2)⁻¹ * t.1 = 1 := congrArg Prod.fst ht
  rw [mul_assoc, hZ _ t.1, ← mul_assoc] at h1
  exact mul_inv_eq_one.1 h1

end GlobalTheory.OrbFinAf.TorusNorm

namespace GlobalTheory.OrbFinAf.TorusNorm

end GlobalTheory.OrbFinAf.TorusNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorMvPolynomialSubmoduleEqTopOfOneMulX
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorMvPolynomialSubmoduleEqTopOfOneMulX
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift

theorem atPl_tprod {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem mvPolynomial_submodule_eq_top {σ : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) (h1 : (1 : MvPolynomial σ ℂ) ∈ S)
    (hX : ∀ (l : σ), ∀ p ∈ S, MvPolynomial.X l * p ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : (MvPolynomial.C a : MvPolynomial σ ℂ) = a • (1 : MvPolynomial σ ℂ) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [this]; exact S.smul_mem a h1
  | add p q hp hq => exact S.add_mem (hp trivial) (hq trivial)
  | mul_X p n hp => rw [mul_comm]; exact hX n p (hp trivial)

theorem tensor_submodule_eq_top : ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)),
    PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N →
    (∀ (w : ι) (l : σ), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) → N = ⊤ := by
  intro ι σ _ _ N h1 hX
  have key : ∀ s : Finset ι, ∀ f : ι → MvPolynomial σ ℂ, (∀ i ∉ s, f i = 1) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = fun _ => 1 := funext fun i => hf i (Finset.notMem_empty i)
      rw [this]; exact h1
    | insert w₀ s hw₀ ih =>
      intro f hf
      let S : Submodule ℂ (MvPolynomial σ ℂ) :=
        N.comap ((PiTensorProduct.tprod ℂ : (∀ _ : ι, MvPolynomial σ ℂ) →ₘₗ[ℂ] (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)).toLinearMap f w₀)
      have hS1 : (1 : MvPolynomial σ ℂ) ∈ S := by
        show PiTensorProduct.tprod ℂ (Function.update f w₀ 1) ∈ N
        apply ih
        intro i hi
        by_cases h : i = w₀
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hf i (by simp [h, hi])
      have hSX : ∀ (l : σ), ∀ p ∈ S, MvPolynomial.X l * p ∈ S := by
        intro l p hp
        have hp' : PiTensorProduct.tprod ℂ (Function.update f w₀ p) ∈ N := hp
        show PiTensorProduct.tprod ℂ (Function.update f w₀ (MvPolynomial.X l * p)) ∈ N
        have := hX w₀ l _ hp'
        rw [atPl_tprod] at this
        simpa using this
      have htop := mvPolynomial_submodule_eq_top S hS1 hSX
      have hf0 : f w₀ ∈ S := by rw [htop]; trivial
      have : PiTensorProduct.tprod ℂ (Function.update f w₀ (f w₀)) ∈ N := hf0
      simpa using this
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory.RealLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiTensorMvPolynomialSubmoduleEqTopOfOneMulXStatement
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piTensorMvPolynomial_submodule_eq_top_of_one_mul_X : ∀ {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ)), PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N → (∀ (w : ι) (l : σ), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) → N = ⊤ := by
  first | exact @GlobalTheory.RealLift.tensor_submodule_eq_top | exact GlobalTheory.RealLift.tensor_submodule_eq_top | (intros; apply GlobalTheory.RealLift.tensor_submodule_eq_top <;> assumption)
end
end
