module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.MinorHarmonic

theorem pderiv_comm {σ R : Type*} [CommRing R] (i j : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) = MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.X k : MvPolynomial σ R)) = 0 := by
      intro a b
      rw [MvPolynomial.pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, hp, h]
    ring

def ker {σ : Type*} (v : σ) : Subring (MvPolynomial σ ℂ) where
  carrier := {f | MvPolynomial.pderiv v f = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Derivation.leibniz, ha, hb]
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [ha]

theorem det_mem {R : Type*} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

variable {D : D7} {m n : ℕ}

theorem varF_mem (τ τ' : D.what₂.Tau) (a : Fin m) (c : Fin n) (i j : ℕ)
    (h : τ' = τ → i = a → j = c → False) :
    (varF τ' i j : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  classical
  unfold varF
  split_ifs with h1
  · show MvPolynomial.pderiv _ _ = 0
    apply MvPolynomial.pderiv_X_of_ne
    intro he
    simp only [Prod.mk.injEq] at he
    exact h he.1 (congrArg Fin.val he.2.1) (congrArg Fin.val he.2.2)
  · exact Subring.zero_mem _

theorem delta_mem (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hpq : ∀ τ, p τ + q τ ≤ n)
    (τ : D.what₂.Tau) (a : Fin m) (c : Fin n)
    (h : ((a : ℕ) < p τ ∧ p τ ≤ c) ∨ (p τ ≤ (a : ℕ) ∧ (c : ℕ) < p τ)) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  unfold delta deltaAt
  refine Subring.prod_mem _ fun τ' _ => Subring.mul_mem _ ?_ ?_
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := α.2
    have := β.2
    omega
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := hpq τ'
    omega

theorem laplacian_delta : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ n) → ∀ τ (a b : Fin m), p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin n, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n)) = 0 := by
  intro D m n p q ap am hpq τ a b ha hb
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge (c : ℕ) (p τ) with hc | hc
  · rw [pderiv_comm]
    have : MvPolynomial.pderiv (τ, a, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ a c (Or.inr ⟨ha, hc⟩)
    rw [this, map_zero]
  · have : MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ b c (Or.inl ⟨hb, hc⟩)
    rw [this, map_zero]

end GlobalTheory.MinorHarmonic

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinorsStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_laplacian_kills_product_of_minors : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ n) → ∀ τ (a b : Fin m), p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin n, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n)) = 0 := by
  first | exact @GlobalTheory.MinorHarmonic.laplacian_delta | exact GlobalTheory.MinorHarmonic.laplacian_delta | (intros; apply GlobalTheory.MinorHarmonic.laplacian_delta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaCoefficient

open GlobalTheory.FinTranslate

theorem exists_unit_smul {X : Type} (f f' : X → ℂ) (h : ∀ x y, f' y * star (f' x) = f y * star (f x)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  have hn : ∀ x, ‖f' x‖ = ‖f x‖ := fun x => by
    have := congrArg norm (h x x)
    rw [norm_mul, norm_mul, norm_star, norm_star] at this
    exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 this
  by_cases h0 : ∀ x, f x = 0
  · refine ⟨1, norm_one, funext fun x => ?_⟩
    have := hn x
    rw [h0, norm_zero, norm_eq_zero] at this
    simp [this, h0]
  · obtain ⟨x, hx⟩ := not_forall.1 h0
    have hx' : f' x ≠ 0 := fun e => hx (by rw [← norm_eq_zero, ← hn, e, norm_zero])
    refine ⟨star (f x) / star (f' x), ?_, funext fun y => ?_⟩
    · rw [norm_div, norm_star, norm_star, hn, div_self (norm_ne_zero_iff.2 hx)]
    · have hs : star (f' x) ≠ 0 := star_ne_zero.2 hx'
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h x y, mul_comm]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_eq (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold symplOH
  linear_combination (-symplO S T x y) * h2

theorem char_mul_heisO {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) {γ : WO S T} (hγ : γ ∈ ratL T S) (w x : WO S T) :
    ψ (symplO S T x γ) * heisO ψ S T w g x = ψ (symplOH S T γ w) * heisO ψ S T (γ + w) g x := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hg.quasi γ (x + w)
  show ψ (symplO S T x (ratW T S γ)) * (ψ (symplOH S T x w) * g (x + w)) =
    ψ (symplOH S T (ratW T S γ) w) * (ψ (symplOH S T x (ratW T S γ + w)) * g (x + (ratW T S γ + w)))
  rw [add_left_comm, h]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [symplO_eq, symplOH_add_right, symplOH_add_right, symplOH_skew S T x (ratW T S γ)]
  congr 2
  ring

theorem exists_unit_smul_of_coefficient_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f f' : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ w, ∫ x in 𝓕, heisO ψ S T w f' x * star (f' x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 f f' hf hf' h
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have hT := @GlobalTheory.ThetaClosed.isThetaFunO_heisO_all D ψ hψ S T
  refine exists_unit_smul f f' fun x y => ?_
  obtain ⟨w, rfl⟩ : ∃ w, y = x + w := ⟨y - x, by abel⟩
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      simp only [symplO_eq]
      exact hψ.1.1.comp ((continuous_symplOH S T _).add (continuous_symplOH S T _)))
    (fun γ x y => by
      simp only [symplO_eq, symplOH_add_left, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun γ γ' x => by
      show ψ (symplO S T x (γ + γ')) = ψ (symplO S T x γ) * ψ (symplO S T x γ')
      simp only [symplO_eq, symplOH_add_right, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun x => by
      show ψ (symplO S T x 0) = 1
      rw [symplO_eq, symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by rw [← GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x]; exact Subtype.forall)
    μ 𝓕 hμ h𝓕 (fun x => heisO ψ S T w f' x * star (f' x) - heisO ψ S T w f x * star (f x))
    (by
      have a := (hT hf' w).cont
      have b := (hT hf w).cont
      have a' := hf'.cont
      have b' := hf.cont
      generalize heisO ψ S T w f' = u at a
      generalize heisO ψ S T w f = v at b
      exact (a.mul a'.star).sub (b.mul b'.star))
    (fun γ hγ x => by
      have a := GlobalTheory.Size.mul_conj_periodic hψ (hT hf' w) hf' γ hγ x
      have b := GlobalTheory.Size.mul_conj_periodic hψ (hT hf w) hf γ hγ x
      simp only [starRingEnd_apply] at a b
      simp only [a, b])
    (fun γ => by
      have e : ∀ x, ψ (symplO S T x γ) * (heisO ψ S T w f' x * star (f' x) - heisO ψ S T w f x * star (f x)) =
          ψ (symplOH S T γ w) * (heisO ψ S T (γ + w) f' x * star (f' x) - heisO ψ S T (γ + w) f x * star (f x)) :=
        fun x => by
          linear_combination star (f' x) * char_mul_heisO hf' γ.2 w x - star (f x) * char_mul_heisO hf γ.2 w x
      simp only [e]
      have a := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 (hT hf' (γ + w)) hf'
      have b := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 (hT hf (γ + w)) hf
      rw [integral_const_mul]
      refine mul_eq_zero_of_right _ ((integral_sub a b).trans (sub_eq_zero.2 (h _))))
  have e := congrFun key x
  have hne : ψ (symplOH S T x w) ≠ 0 := fun e => by simpa [e] using hψ.1.2.1 (symplOH S T x w)
  simp only [heisO, Pi.zero_apply] at e
  refine mul_left_cancel₀ hne ?_
  linear_combination e

end GlobalTheory.ThetaCoefficient
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_eq_unitSmul_of_diagonalCoefficient_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f f' : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ w, ∫ x in 𝓕, heisO ψ S T w f' x * star (f' x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  first | exact @GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq | exact GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq | (intros; apply GlobalTheory.ThetaCoefficient.exists_unit_smul_of_coefficient_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefLiftMult

open Matrix

theorem sig_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) := by
  obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
  have hq : q = 0 := by
    by_contra hq
    have j : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
    have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inr j)
    rw [hQ] at h1
    simp [Formalism.UG.Jpq] at h1
    exact absurd h1 (by norm_num)
  subst hq
  simp at hn
  rw [hn]

theorem exists_tauE (D : D7) (σ : D.host.E →+* ℂ) :
    ∃ τ, σ = tauE D τ ∨ σ = (starRingEnd ℂ).comp (tauE D τ) := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have key : ∀ (t : D.R.GG) (ht : t ∈ D.R.Psi),
      tauE D (D.eTau.symm ⟨t, ht⟩) = D.host.emb t := fun t ht => by
    unfold tauE
    rw [Equiv.apply_symm_apply]
  by_cases h : g ∈ D.R.Psi
  · exact ⟨D.eTau.symm ⟨_, h⟩, Or.inl (key g h).symm⟩
  · have h' : g * D.R.cc ∈ D.R.Psi := by
      by_contra h2
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h2)
    refine ⟨D.eTau.symm ⟨_, h'⟩, Or.inr ?_⟩
    rw [key, Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have := D.host.conjE_apply (D.host.emb g) x
    exact ((starRingEnd_self_apply _).symm.trans (congrArg (starRingEnd ℂ) this.symm))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem isDefinite (hs : V.SigOK) (h : AllPlus M) : V.IsDefinite := by
  intro σ
  refine Or.inl (sig_of_posDef ?_ (hs σ))
  obtain ⟨τ, rfl | rfl⟩ := exists_tauE D σ
  · exact h.posDef τ
  · have e : V.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D V τ)ᴴᵀ := by
      ext i j
      rfl
    rw [e]
    exact (h.posDef τ).conjTranspose.transpose

theorem rTr_mem {θ : InfFam D} (hθ : IsInfFam θ) (U : Set (GA D V → ℂ))
    (hU : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ U, rTr V (atTau θ V τ g) f ∈ U) {k : GA D V}
    (hk : k ∈ GinfC V) : ∀ f ∈ U, rTr V k f ∈ U := by
  classical
  obtain ⟨-, -, r3, -⟩ := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hu := GlobalTheory.RealLift.archM_mem hθ V k
  have e : GlobalTheory.RealLift.prodAt θ V Finset.univ.toList (fun τ => Formalism.L2.Pj.archM V (θ τ) k) = k :=
    r3 _ (GlobalTheory.RealLift.prodAt_mem θ V _ _) _ hk fun τ => by
      rw [GlobalTheory.RealLift.infMat_prodAt hθ V hu τ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
      rfl
  rw [← e]
  clear e
  generalize (Finset.univ.toList : List D.what₂.Tau) = l
  induction l with
  | nil =>
    intro f hf
    convert hf using 1
    funext g
    exact congrArg f (mul_one g)
  | cons τ l ih =>
    intro f hf
    convert hU τ _ (hu τ) _ (ih f hf) using 1
    funext g
    exact congrArg f (mul_assoc _ _ _).symm

open Classical in
theorem actT_tprod (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    inclT M (PiTensorProduct.tprod ℂ (Function.update v τ w)) = actT M τ g (inclT M (PiTensorProduct.tprod ℂ v)) := by
  unfold inclT actT
  simp only [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases c : ρ = τ
  · subst c
    simpa using hw
  · simp [Function.update_of_ne c]

theorem mem_multT_of_equivariant : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ) (L : SmT M →ₗ[ℂ] (GA D V → ℂ)), IsInfFam θ → V.SigOK → AllPlus M → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → FiniteDimensional ℂ (SmT M) → Function.Injective (inclT M) → IsTensAct M π → (∀ x, IsAutFun V (L x)) → (∀ x, ∀ k ∈ J, ∀ g, L x (g * k) = χ k * L x g) → (∀ τ u x, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x)) → L ∈ MultT θ M J χ := by
  intro D θ V S M π J χ L hθ hs hp hfd hT hinj hπ haut hlev heq
  have hd := isDefinite hs hp
  refine (mem_multT θ M J χ L).2 (Submodule.subset_span ?_)
  have e : ∀ v : M.Vec, PiTensorProduct.lift.symm L v = L (PiTensorProduct.tprod ℂ v) := fun v => rfl
  refine ⟨fun v => ?_, fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _, fun v k hk g => hlev _ k hk g,
    fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    refine (GlobalTheory.DefiniteForms.autFunDefIffSm D θ hθ V hs hd _).1 ⟨haut _, ?_⟩
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, hk, rfl⟩
    refine rTr_mem hθ _ (fun τ g hg => ?_) hk _ (LinearMap.mem_range_self L _)
    rintro _ ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    exact ⟨_, heq τ u x⟩
  · obtain ⟨u, rfl⟩ := hp.exists_unfr τ hg
    rw [e, e, ← heq]
    congr 1
    exact hinj ((actT_tprod τ _ v w hw).trans (hπ τ u _).symm)
  · haveI := (hfd τ).1
    exact GlobalTheory.DefiniteEnd.exists_sobCont M τ _ v x

end GlobalTheory.DefLiftMult

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_multT_of_equivariant' : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (π : D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ → Module.End ℂ (SmT M)) (J : Set (GA D V)) (χ : GA D V → ℂ) (L : SmT M →ₗ[ℂ] (GA D V → ℂ)), IsInfFam θ → V.SigOK → AllPlus M → (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤) → FiniteDimensional ℂ (SmT M) → Function.Injective (inclT M) → IsTensAct M π → (∀ x, IsAutFun V (L x)) → (∀ x, ∀ k ∈ J, ∀ g, L x (g * k) = χ k * L x g) → (∀ τ u x, L (π τ u x) = rTr V (atTau θ V τ (unfr M τ u)) (L x)) → L ∈ MultT θ M J χ := by
  first | exact @GlobalTheory.DefLiftMult.mem_multT_of_equivariant | exact GlobalTheory.DefLiftMult.mem_multT_of_equivariant | (intros; apply GlobalTheory.DefLiftMult.mem_multT_of_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

private theorem eq_spMap_of_specializes {X : Scheme.{0}} {K : Type} [Field K] (g : Sp K ⟶ X) {z : X}
    (h : g (IsLocalRing.closedPoint K) ⤳ z) :
    g = spMap (X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) g).hom ≫
      X.fromSpecStalk z := by
  conv_lhs => rw [← spMap_stalkClosedPointTo g]
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
  show Spec.map _ ≫ _ = Spec.map _ ≫ _
  simp only [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]

private theorem spMap_comp_spMap_divisor {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_isHom_of_generic (M : RatModel F Ω) (M' : RatModel F Ω') (f : M'.Z ⟶ M.Z) (hs : f ≫ M.s = M'.s)
    (hg : f (genericPoint M'.Z) = genericPoint M.Z) : ∃ φ : Ω →ₐ[F] Ω', M.IsHom M' φ f := by
  classical
  have hp0 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = genericPoint M.Z := by
    have h1 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = f (M'.pt (IsLocalRing.closedPoint Ω')) := rfl
    rw [h1]
    exact (congrArg f (M'.pt_apply (IsLocalRing.closedPoint Ω'))).trans hg
  have hp : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ⤳ genericPoint M.Z := by rw [hp0]
  have hq : M.pt = spMap (M.stalkHom (genericPoint M.Z)) ≫ M.Z.fromSpecStalk (genericPoint M.Z) :=
    eq_spMap_of_specializes M.pt (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z))
  have hsurj : Function.Surjective (M.stalkHom (genericPoint M.Z)) := by
    intro x
    have hx : x ∈ M.O (genericPoint M.Z) := by rw [M.O_genericPoint]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (M.stalkEquiv (genericPoint M.Z)).surjective ⟨x, hx⟩
    refine ⟨a, ?_⟩
    rw [← RatModel.coe_stalkEquiv, ha]
  let E := RingEquiv.ofBijective (M.stalkHom (genericPoint M.Z)) ⟨M.stalkHom_injective _, hsurj⟩
  let α := (M.Z.presheaf.stalkSpecializes hp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω') (M'.pt ≫ f)).hom
  let φ₀ : Ω →+* Ω' := α.comp E.symm.toRingHom
  have key : φ₀.comp (M.stalkHom (genericPoint M.Z)) = α := by
    ext a
    show α (E.symm (E a)) = α a
    rw [E.symm_apply_apply]
  have hpt : M'.pt ≫ f = spMap φ₀ ≫ M.pt := by
    rw [eq_spMap_of_specializes (M'.pt ≫ f) hp, hq, ← Category.assoc, ← spMap_comp_spMap_divisor, key]
  have hc : spMap (φ₀.comp (algebraMap F Ω)) = spMap (algebraMap F Ω') := by
    rw [spMap_comp_spMap_divisor, ← M.pt_s, ← Category.assoc, ← hpt, Category.assoc, hs, M'.pt_s]
  have hinj : φ₀.comp (algebraMap F Ω) = algebraMap F Ω' := by
    have h2 : CommRingCat.ofHom (φ₀.comp (algebraMap F Ω)) = CommRingCat.ofHom (algebraMap F Ω') :=
      Spec.map_injective hc
    ext a
    exact congrArg (fun g => g.hom a) h2
  exact ⟨⟨φ₀, fun a => RingHom.congr_fun hinj a⟩, hpt⟩

theorem apply_eq_of_isHom_id {M : RatModel F Ω} {χ : Ω →ₐ[F] Ω} (h : M.IsHom M χ (𝟙 M.Z)) (x : Ω) : χ x = x := by
  have hpt : (𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω)) = genericPoint M.Z := by
    exact M.pt_apply _
  have hx : x ∈ M.O ((𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω))) := by
    rw [hpt, M.O_genericPoint]; exact Algebra.mem_top
  have h2 := h.val_comp M.pt (IsLocalRing.closedPoint Ω) hx
  rw [Category.comp_id, RatModel.val_pt, RatModel.val_pt] at h2
  exact h2.symm

theorem iso_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y) :
    e.hom (genericPoint X) = genericPoint Y := by
  exact genericPoint_eq_of_isOpenImmersion e.hom

private theorem mat_map_mul_inv {ι : Type} {m : ι → ℕ} {K K' : Type} [Field K] [Field K'] (σ : K →+* K')
    (X Y : Mat m K) : (X * Y⁻¹).map σ = X.map σ * (Y.map σ)⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv]

theorem exists_refines_of_iso {ι : Type} {m k : ι → ℕ} (M : RatModel F Ω) (M' : RatModel F Ω') (e : M'.Z ≅ M.Z)
    (hs : e.hom ≫ M.s = M'.s) (S : Fr M m k) :
    ∃ (φ : Ω →ₐ[F] Ω') (S' : Fr M' m k), Refines S S' φ e.hom := by
  classical
  obtain ⟨φ, hφ⟩ := exists_isHom_of_generic M M' e.hom hs (iso_genericPoint e)
  have hs' : e.inv ≫ M'.s = M.s := by rw [← hs, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨ψ, hψ⟩ := exists_isHom_of_generic M' M e.inv hs' (iso_genericPoint e.symm)
  have hid : M.IsHom M (ψ.comp φ) (𝟙 M.Z) := by
    have h1 := hφ.comp hψ
    rwa [e.inv_hom_id] at h1
  have hid' : M'.IsHom M' (φ.comp ψ) (𝟙 M'.Z) := by
    have h1 := hψ.comp hφ
    rwa [e.hom_inv_id] at h1
  have hψφ : ∀ x, ψ (φ x) = x := fun x => apply_eq_of_isHom_id hid x
  have hφψ : ∀ x, φ (ψ x) = x := fun x => apply_eq_of_isHom_id hid' x
  have pt2 : ∀ z' : M'.Z, e.inv (e.hom z') = z' := fun z' => by simp
  have memφ : ∀ {z' : M'.Z} {x : Ω}, x ∈ M.O (e.hom z') → φ x ∈ M'.O z' := fun hx => hφ.map_mem_O hx
  have memψ : ∀ {z' : M'.Z} {x : Ω'}, x ∈ M'.O z' → ψ x ∈ M.O (e.hom z') := by
    intro z' x hx
    apply hψ.map_mem_O
    rwa [pt2]
  have mm1 : ∀ g : Mat m Ω, (g.map φ).map ψ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hψφ]
  have mm2 : ∀ g : Mat m Ω', (g.map ψ).map φ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hφψ]
  have I1 : ∀ (B : Mat m Ω') (A : Mat m Ω), B.map ψ * A⁻¹ = (B * (A.map φ)⁻¹).map ψ := by
    intro B A
    have h1 := mat_map_mul_inv ψ.toRingHom B (A.map φ)
    have h2 : (B * (A.map φ)⁻¹).map ψ = B.map ψ * ((A.map φ).map ψ)⁻¹ := h1
    rw [h2, mm1]
  have I2 : ∀ (B : Mat m Ω') (A : Mat m Ω), (B.map ψ * A⁻¹).map φ = B * (A.map φ)⁻¹ := by
    intro B A
    have h1 := mat_map_mul_inv φ.toRingHom (B.map ψ) A
    have h2 : (B.map ψ * A⁻¹).map φ = (B.map ψ).map φ * (A.map φ)⁻¹ := h1
    rw [h2, mm2]
  have hdet : ∀ {A : Mat m Ω}, (∀ τ, (A τ).det ≠ 0) → ∀ τ, ((A.map φ) τ).det ≠ 0 := by
    intro A hA τ
    have h1 : ((A.map φ) τ).det = φ (A τ).det := Mat.det_map A φ.toRingHom τ
    rw [h1]
    exact (map_ne_zero φ).2 (hA τ)
  let S' : Fr M' m k :=
    { S := fun z' => {A' | A'.map ψ ∈ S.S (e.hom z')}
      loc := by
        intro z'
        obtain ⟨U, A, hzU, hA, hU⟩ := S.loc (e.hom z')
        refine ⟨e.hom ⁻¹ᵁ U, A.map φ, hzU, hdet hA, fun z'' hz'' A'' => ?_⟩
        show A''.map ψ ∈ S.S (e.hom z'') ↔ _
        rw [hU (e.hom z'') hz'' (A''.map ψ), I1]
        constructor
        · intro h
          have h1 : Par k (M'.O z'').toSubring (((A'' * (A.map φ)⁻¹).map ψ).map φ) :=
            h.map φ.toRingHom (fun x hx => memφ hx)
          rwa [mm2] at h1
        · intro h
          exact h.map ψ.toRingHom (fun x hx => memψ hx) }
  refine ⟨φ, S', ⟨le_rfl, hφ, ?_, ?_, ?_⟩⟩
  · intro z' A' hA' A hA
    have h1 : Par k (M.O (e.hom z')).toSubring (A'.map ψ * A⁻¹) :=
      (Fr.mem_iff hA).1 (show A'.map ψ ∈ S.S (e.hom z') from hA')
    have h2 : Par k (M'.O z').toSubring ((A'.map ψ * A⁻¹).map φ) :=
      h1.map φ.toRingHom (fun x hx => memφ hx)
    rwa [I2] at h2
  · unfold KeepsRad Rad
    intro z' g hg
    obtain ⟨hg0, hgO, hgr⟩ := hg
    refine ⟨(map_ne_zero φ).2 hg0, memφ hgO, fun x n hx hxn => ?_⟩
    have hx' : ψ x ∈ M.O (e.hom z') := memψ hx
    have hxn' : ψ x ^ n / g ∈ M.O (e.hom z') := by
      have h1 := memψ hxn
      rw [map_div₀, map_pow, hψφ] at h1
      exact h1
    have h2 := memφ (hgr (ψ x) n hx' hxn')
    rw [map_div₀, hφψ] at h2
    exact h2
  · intro K _ x A hA h hh
    refine ⟨x ≫ e.inv, ⟨by simp, ?_⟩, fun p hp => ?_⟩
    · have hx1 : e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
        have h1 : (x ≫ e.inv) (IsLocalRing.closedPoint K) = e.inv (x (IsLocalRing.closedPoint K)) := rfl
        rw [h1]
        simp
      have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := hdet (Fr.det_ne hA)
      have hone : (1 : Mat m Ω').map (M'.val (x ≫ e.inv)) = 1 := by
        funext τ; ext i j
        simp only [Mat.map, Matrix.map_apply, Pi.one_apply, Matrix.one_apply]
        split_ifs
        · exact RatModel.val_one _
        · exact RatModel.val_zero _
      have hinv : (1 : Mat m K)⁻¹ = 1 := by
        have h1 := Mat.mul_inv (g := (1 : Mat m K)) (fun τ => by simp)
        rwa [one_mul] at h1
      unfold Bears
      refine ⟨A.map φ, ?_, ?_⟩
      · show (A.map φ).map ψ ∈ S.S (e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)))
        rw [mm1, hx1]
        exact hA
      · rw [Mat.mul_inv hd, hone, hinv, mul_one]
        exact hh
    · rw [← hp.1, Category.assoc, e.hom_inv_id, Category.comp_id]

theorem exists_var_refines (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (h : Good M d) :
    ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k),
      Y.dim = d ∧ Refines S S' φ f := by
  obtain ⟨hP, hSm, hGI⟩ := h
  haveI : SmoothOfRelativeDimension d M.s := hSm
  haveI : GeometricallyIntegral M.s := hGI
  haveI : GeometricallyConnected M.s := by
    constructor
    intro a b y c fst snd hpb
    have := GeometricallyIntegral.geometrically_isIntegral (f := M.s) y fst snd hpb
    infer_instance
  obtain ⟨Y, e, hd, he⟩ := GlobalTheory.ProjVar.Var.exists_iso M.s d hP
  have hs : e.inv ≫ M.s = (ratOf Y).s := by
    show e.inv ≫ M.s = Y.str
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨φ, S', hS'⟩ := exists_refines_of_iso M (ratOf Y) e.symm hs S
  exact ⟨Y, φ, e.inv, S', hd, hS'⟩

end GlobalTheory.FlagBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModelStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type) (m k : ι → ℕ) (S : Fr M m k), Good M d → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k), Y.dim = d ∧ Refines S S' φ f := by
  first | exact @GlobalTheory.FlagBundle.exists_var_refines | exact GlobalTheory.FlagBundle.exists_var_refines | (intros; apply GlobalTheory.FlagBundle.exists_var_refines <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicity
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicity
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU.admitted

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_fin_mul_inf (y : UA E n) : ∃ a ∈ finU (E := E) (n := n), ∃ b ∈ infU E n, y = a * b := by
  let yi := GeneralLinearGroup.map (pInf E) y.1
  have hyi : yi.valᴴ * yi.val = 1 := by
    have hy : cT (conjAd E) y.1.val * 1 * y.1.val = 1 := y.2
    have h3 : (cT (conjAd E) y.1.val).map (pInf E) = yi.valᴴ := by
      ext1 i j
      rw [Matrix.conjTranspose_apply]
      exact (infEq E).symm_apply_apply _
    have h := congrArg (pInf E).mapMatrix hy
    rw [map_mul, map_mul, map_one, mul_one, RingHom.mapMatrix_apply, h3] at h
    exact h
  let b : UA E n := ⟨infGL E n yi, infGL_mem_UA yi hyi⟩
  have hb : b ∈ infU E n := MonoidHom.mem_ker.2 (pFin_infGL yi)
  have ha : b⁻¹ * y ∈ finU (E := E) (n := n) := by
    refine MonoidHom.mem_ker.2 ?_
    rw [map_mul, map_inv]
    have : cInf b = cInf y := pInf_infGL yi
    rw [this, inv_mul_cancel]
  refine ⟨b⁻¹ * y, ha, b, hb, ?_⟩
  rw [fin_mul_inf ha hb, mul_inv_cancel_left]

def X (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) := Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_mem_X (φ : UA E n → ℂ) (x : infU E n) {ξ : UA E n → ℂ} (h : ξ ∈ X φ) : RU E n x ξ ∈ X φ := by
  have : X φ ≤ (X φ).comap (RU E n x) := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨x * k, (RU_RU _ _ _).symm⟩)
  exact this h

theorem self_mem_X (φ : UA E n → ℂ) : φ ∈ X φ :=
  Submodule.subset_span ⟨1, by show RU E n 1 φ = φ; rw [map_one]; rfl⟩

def rhoX (φ : UA E n → ℂ) (x : infU E n) : Module.End ℂ (X φ) :=
  (RU E n x).restrict fun _ h => RU_mem_X φ x h

theorem rhoX_mul (φ : UA E n → ℂ) (x y : infU E n) : rhoX φ (x * y) = rhoX φ x * rhoX φ y :=
  LinearMap.ext fun ξ => Subtype.ext (RU_RU (x : UA E n) y ξ.1).symm

def coef (φ : UA E n → ℂ) : Module.Dual ℂ (Module.End ℂ (X φ)) →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun x => LinearMap.applyₗ (rhoX φ x)

def C (φ : UA E n → ℂ) : Submodule ℂ (infU E n → ℂ) := LinearMap.range (coef φ)

theorem mem_C (φ : UA E n → ℂ) (f : X φ →ₗ[ℂ] ℂ) (ξ : X φ) : (fun x : infU E n => f (rhoX φ x ξ)) ∈ C φ :=
  ⟨f ∘ₗ LinearMap.applyₗ ξ, rfl⟩

theorem C_right (φ : UA E n → ℂ) {c : infU E n → ℂ} (hc : c ∈ C φ) (y : infU E n) :
    (fun x => c (x * y)) ∈ C φ := by
  obtain ⟨B, rfl⟩ := hc
  refine ⟨B ∘ₗ LinearMap.mulRight ℂ (rhoX φ y), funext fun x => ?_⟩
  change B (rhoX φ x * rhoX φ y) = B (rhoX φ (x * y))
  rw [rhoX_mul]

def Y (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  ⨅ g : UA E n, (C φ).comap (LinearMap.funLeft ℂ ℂ fun x : infU E n => g * (x : UA E n))

theorem mem_Y {φ ψ : UA E n → ℂ} : ψ ∈ Y φ ↔ ∀ g : UA E n, (fun x : infU E n => ψ (g * x)) ∈ C φ := by
  simp only [Y, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem le_Y (π : AutSub E n) {φ : UA E n → ℂ} (hφ : φ ∈ π.V) (h0 : φ ≠ 0) : π.V ≤ Y φ := by
  have hφY : φ ∈ Y φ := mem_Y.2 fun g =>
    mem_C φ ((LinearMap.proj g) ∘ₗ (X φ).subtype) ⟨φ, self_mem_X φ⟩
  have hst : ∀ x, ∀ ψ ∈ π.V ⊓ Y φ, RU E n x ψ ∈ π.V ⊓ Y φ := by
    intro x ψ hψ
    refine ⟨π.isAut.stable x ψ hψ.1, mem_Y.2 fun g => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_fin_mul_inf x
    have e : (fun z : infU E n => RU E n (a * b) ψ (g * z)) = fun z => ψ ((g * a) * ((z * ⟨b, hb⟩ : infU E n) : UA E n)) := by
      funext z
      rw [RU_apply, Subgroup.coe_mul, Subgroup.coe_mk, ← mul_assoc, mul_assoc g, ← fin_mul_inf ha z.2, ← mul_assoc, mul_assoc (g * a)]
    rw [e]
    exact C_right φ (mem_Y.1 hψ.2 (g * a)) ⟨b, hb⟩
  rcases π.isAut.irred (π.V ⊓ Y φ) inf_le_left hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hφ, hφY⟩ : φ ∈ π.V ⊓ Y φ))) h0
  · rw [← h]
    exact inf_le_right

theorem eq_zero_of_vanish {K : Subgroup (finU (E := E) (n := n))} {S : Finset (UA E n)}
    (hS : ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K, g = γ * s * x * (k : UA E n))
    {f : UA E n → ℂ} (hl : ∀ γ ∈ ratU E n, ∀ g, f (γ * g) = f g) (hK : ∀ k ∈ K, RU E n k f = f)
    (h0 : ∀ s ∈ S, ∀ x ∈ infU E n, f (s * x) = 0) : f = 0 := by
  funext g
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  rw [mul_assoc, mul_assoc, hl γ hγ, ← mul_assoc]
  have := congrFun (hK k hk) (s * x)
  rw [RU_apply] at this
  rw [this, h0 s hs x hx]
  rfl

theorem exists_ne_zero (π : AutSub E n) : ∃ φ ∈ π.V, φ ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot π.isAut.ne_bot

theorem finiteDimensional_fixed (π : AutSub E n) (K : Subgroup (finU (E := E) (n := n))) (hK : IsOpen (K : Set (finU (E := E) (n := n)))) :
    FiniteDimensional ℂ (fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hK
  let L : fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K →ₗ[ℂ] (S → C φ) :=
    LinearMap.pi fun s => LinearMap.codRestrict (C φ)
      ((LinearMap.funLeft ℂ ℂ fun x : infU E n => (s : UA E n) * x) ∘ₗ π.V.subtype ∘ₗ (fixed _ K).subtype)
      (fun ψ => mem_Y.1 (le_Y π hφ h0 ψ.1.2) s)
  refine Module.Finite.of_injective L (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun ψ hψ => ?_))
  have hK' : ∀ k ∈ K, RU E n k ψ.1.1 = ψ.1.1 := fun k hk => by
    have e : (π.rep.comp (finU (E := E) (n := n)).subtype) k ψ.1 = (((1 : K →* ℂˣ) ⟨k, hk⟩ : ℂˣ) : ℂ) • ψ.1 := ψ.2 ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at e
    exact congrArg Subtype.val e
  have hf := eq_zero_of_vanish hS (π.isAut.aut _ ψ.1.2).left hK' fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hψ ⟨s, hs⟩)) ⟨x, hx⟩
  exact Subtype.ext (Subtype.ext hf)

def stab (φ : UA E n → ℂ) : Subgroup (finU (E := E) (n := n)) where
  carrier := {k | RU E n k φ = φ}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Subgroup.coe_mul, ← RU_RU, hb, ha]
  one_mem' := by
    show RU E n 1 φ = φ
    rw [map_one]
    rfl
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [RU_RU, InvMemClass.coe_inv, inv_mul_cancel, map_one]
    rfl

theorem finiteDimensional_hom (π : AutSub E n) : FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) := by
  obtain ⟨φ, hφ, h0⟩ := exists_ne_zero π
  have : FiniteDimensional ℂ (X φ) := (π.isAut.aut φ hφ).kfin
  have : FiniteDimensional ℂ (C φ) := LinearMap.finiteDimensional_range _
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n (stab φ) (π.isAut.aut φ hφ).level
  let φV : π.V := ⟨φ, hφ⟩
  have hXV : X φ ≤ π.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact π.isAut.stable _ φ hφ)
  have hmem : ∀ (T : π.rep.IntertwiningMap (autRep E n)) (s : UA E n),
      (fun x : infU E n => (T φV).1 (s * x)) ∈ C φ := by
    intro T s
    have e : (fun x : infU E n => (T φV).1 (s * x)) = fun x => ((LinearMap.proj s) ∘ₗ (autU E n).subtype ∘ₗ
        T.toLinearMap ∘ₗ Submodule.inclusion hXV) (rhoX φ x ⟨φ, self_mem_X φ⟩) :=
      funext fun x => (congrFun (congrArg Subtype.val (LinearMap.congr_fun (T.isIntertwining' (x : UA E n)) φV)) s).symm
    rw [e]
    exact mem_C φ _ _
  let Φ : π.rep.IntertwiningMap (autRep E n) →ₗ[ℂ] (S → C φ) :=
    { toFun := fun T s => ⟨fun x : infU E n => (T φV).1 ((s : UA E n) * x), hmem T s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective Φ (LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun T hT => ?_))
  have hK : ∀ k ∈ stab φ, RU E n k (T φV).1 = (T φV).1 := fun k hk => by
    have e : T (π.rep k φV) = autRep E n k (T φV) := LinearMap.congr_fun (T.isIntertwining' (k : UA E n)) φV
    rw [show π.rep k φV = φV from Subtype.ext hk] at e
    exact (congrArg Subtype.val e).symm
  have hTφ : T φV = 0 := Subtype.ext (eq_zero_of_vanish hS (mem_autU.1 (T φV).2).left hK fun s hs x hx =>
    congrFun (congrArg Subtype.val (congrFun hT ⟨s, hs⟩)) ⟨x, hx⟩)
  let W : Submodule ℂ (UA E n → ℂ) := (LinearMap.ker T.toLinearMap).map π.V.subtype
  have hst : ∀ x, ∀ ψ ∈ W, RU E n x ψ ∈ W := by
    rintro x _ ⟨ψ', hψ', rfl⟩
    refine ⟨π.rep x ψ', ?_, rfl⟩
    have h1 : T ψ' = 0 := hψ'
    change T (π.rep x ψ') = 0
    have h2 : T (π.rep x ψ') = autRep E n x (T ψ') := LinearMap.congr_fun (T.isIntertwining' x) ψ'
    rw [h2, h1, map_zero]
  rcases π.isAut.irred W (Submodule.map_subtype_le _ _) hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨φV, hTφ, rfl⟩ : φ ∈ W))) h0
  · refine DFunLike.ext _ _ fun ψ => ?_
    obtain ⟨ψ', hψ', e⟩ : ψ.1 ∈ W := h.symm ▸ ψ.2
    rw [← Subtype.ext e]
    exact hψ'

theorem admissible_finiteMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n),
    (∀ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) →
      FiniteDimensional ℂ (fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K)) ∧
    FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) :=
  fun _ _ _ _ _ π => ⟨fun K hK => finiteDimensional_fixed π K hK, finiteDimensional_hom π⟩

end GlobalTheory.DefU.admitted
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicityStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_admissible_finiteMultiplicity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n), (∀ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) → FiniteDimensional ℂ (fixed (π.rep.comp (finU (E := E) (n := n)).subtype) K)) ∧ FiniteDimensional ℂ (π.rep.IntertwiningMap (autRep E n)) := by
  first | exact @GlobalTheory.DefU.admitted.admissible_finiteMult | exact GlobalTheory.DefU.admitted.admissible_finiteMult | (intros; apply GlobalTheory.DefU.admitted.admissible_finiteMult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RecordWeightVec

theorem aPl_eq_aPlusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) τ n : ℚ) = DV.aPlusQ D ((i : ℕ) + 1) τ n := by
  have hi := i.2
  have h1 : DV.sigPar D τ n = Formalism.L2.NTheta.lamAt (D.hc τ) n := by
    unfold DV.sigPar Formalism.L2.NTheta.lamAt
    rfl
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aPl_cast D i τ n hn, DV.aPlusQ_eq, h1, h2]
  push_cast
  ring

theorem aMi_eq_aMinusQ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (q n c : ℕ) (hq : i + 1 + q = D.R.m)
    (hn : n + c + 1 = q) : (aMi D i (D.R.k + i) q τ n : ℚ) = DV.aMinusQ D ((i : ℕ) + 1) τ c := by
  have hi := i.2
  have h2 : DV.eQ D ((i : ℕ) + 1) τ = (D.hc τ).e i := by
    unfold DV.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [GlobalTheory.CoefMapRecord.aMi_cast D i τ q n c hq hn, DV.aMinusQ, dite_eq_left (by omega), h2]
  ring

theorem wtOf_kapTop : ∀ D : D7, DV.KapDef D → ∀ i : Fin D.R.m,
    (kapTop D i).n = D.R.nV ∧ Formalism.L2.Geo.wtOf (kapTop D i) = DV.kapW D ((i : ℕ) + 1) := by
  intro D hK i
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hs : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ =>
    D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  refine ⟨rfl, Formalism.L2.Geo.wtOf_eq_kapW _ (fun τ a => ?_) (fun τ c => ?_) rfl⟩
  · have h := (hK _ (inR i).1 (inR i).2 τ).1 a
    have h' := aPl_eq_aPlusQ D i τ a (hp ▸ a.2)
    have he := (kapIs_kapTop D i τ).1 a
    rw [he, hs τ]
    rw [← h, ← hp] at h'
    exact_mod_cast h'
  · have h := (hK _ (inR i).1 (inR i).2 τ).2 (Fin.rev c)
    have hc := c.2
    have h' := aMi_eq_aMinusQ D i τ _ c (Fin.rev c) hq (by rw [Fin.val_rev]; omega)
    have he := (kapIs_kapTop D i τ).2.1 c
    rw [he, hs τ]
    rw [← hp, ← neg_neg (DV.aMinusQ _ _ _ _), ← h] at h'
    exact_mod_cast h'

end GlobalTheory.RecordWeightVec
end
