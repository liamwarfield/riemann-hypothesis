module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedPowOfUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDRAndDdRLeFilZeroOfTwist
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicative
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

theorem actMat_props {Z O N C : Type} [CommRing Z] [CommRing O] [Algebra Z O] [AddCommGroup N]
    [Module O N] [Module Z N] (hs : ∀ (x : Z) (t : N), x • t = algebraMap Z O x • t)
    [CommRing C] (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N)
    (A : O → Matrix (Fin d) (Fin d) C) (hA : ∀ a i j, A a i j = φ (b.repr (a • b j) i)) :
    (∀ a a', A (a + a') = A a + A a') ∧ (∀ (x : Z) a, A (x • a) = φ x • A a) ∧ A 1 = 1 ∧
      ∀ a a', A (a * a') = A a * A a' := by
  have hc : ∀ (a : O) (x : Z) (t : N), a • (x • t) = x • (a • t) := by
    intro a x t
    rw [hs, hs, smul_smul, smul_smul, mul_comm]
  refine ⟨fun a a' => ?_, fun x a => ?_, ?_, fun a a' => ?_⟩
  · ext i j
    simp only [hA, Matrix.add_apply, add_smul, map_add (f := _), Finsupp.add_apply]
  · ext i j
    have hx : (x • a) • b j = x • (a • b j) := by
      rw [Algebra.smul_def, mul_smul, ← hs]
    simp only [hA, Matrix.smul_apply, hx, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  · ext i j
    rw [hA, one_smul, Module.Basis.repr_self]
    by_cases h : i = j
    · subst h
      simp
    · simp [Finsupp.single_apply, Matrix.one_apply, h, Ne.symm h]
  · ext i j
    rw [Matrix.mul_apply, hA, mul_smul]
    conv_lhs => rw [← b.sum_repr (a' • b j)]
    rw [Finset.smul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply,
      smul_eq_mul, map_mul, hA]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable {l : ℕ} [Fact l.Prime]

theorem lamMul_lam_add {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (x y : OCO LL) :
    lam o A (x + y) = lam o A x + lam o A y := by
  simp only [lam, kap_add, add_smul, Finset.sum_add_distrib]

theorem lamMul_lam_zero {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) :
    lam o A 0 = 0 := by
  simp only [lam, kap_zero, zero_smul, Finset.sum_const_zero]

theorem lam_mul_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  intro l _ K LL T d f M A o h
  letI := zlMod LL T
  obtain ⟨b, -, hA⟩ := h
  let φ : ℤ_[l] →+* PadicComplex l := (algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom
  have hφ : ∀ x, φ x = zC x := fun _ => rfl
  obtain ⟨Pa, Ps, P1, Pm⟩ := actMat_props (Z := ℤ_[l]) (O := ↥(OL LL)) (N := ↥T.L.T)
    (fun _ _ => rfl) φ b A (fun a i j => hA a i j)
  have hsum : ∀ a, A a = ∑ k, zC (o.repr a k) • A (o k) := by
    intro a
    have e := map_sum (AddMonoidHom.mk' A Pa) (fun k => o.repr a k • o k) Finset.univ
    simp only [AddMonoidHom.mk'_apply, o.sum_repr] at e
    rw [e]
    simp only [Ps, hφ]
  have ht : ∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a := by
    intro c a
    rw [hsum a, Finset.smul_sum]
    simp only [lam, kap_tmul, mul_smul]
  refine ⟨ht, P1, Pm, fun x y => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp [lamMul_lam_zero]
  | tmul c a =>
    induction y using TensorProduct.induction_on with
    | zero => simp [lamMul_lam_zero]
    | tmul c' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, ht, ht, ht, Pm, smul_mul_smul_comm]
      rfl
    | add y₁ y₂ h₁ h₂ => rw [mul_add, lamMul_lam_add, lamMul_lam_add, h₁, h₂, mul_add]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, lamMul_lam_add, lamMul_lam_add, h₁, h₂, add_mul]

end GlobalTheory.Cyc.Decomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicativeStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ocTensorCoeffActionMatrix_multiplicative : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  first | exact @GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | exact GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | (intros; apply GlobalTheory.Cyc.Decomp.lam_mul_of_isMat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSymbolBasis
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbolBasis

open GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : ThetaL P AI)

theorem theta_zero : J.θ 0 = 0 := by
  have h := J.θ_add 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero] at h
  simpa using h

theorem theta_sum {ι : Type} (s : Finset ι) (f : ι → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) : J.θ (∑ i ∈ s, f i) = ∑ i ∈ s, J.θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero J
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      J.θ_add _ (hf a) _ (Submodule.sum_mem _ fun i _ => hf i), ih]

theorem om_mul_mem (c : Om l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    algebraMap (Om l) P.R.BdR c * x ∈ (P.PD (botExt l)).Fil 0 := by
  simpa using (P.PD (botExt l)).Fil_mul _ _ _ _ (om_mem c) hx

theorem theta_comb {n : ℕ} (c : Fin n → Om l) (f : Fin n → P.R.BdR)
    (hf : ∀ i, f i ∈ (P.PD (botExt l)).Fil 0) :
    J.θ (∑ i, algebraMap (Om l) P.R.BdR (c i) * f i) = ∑ i, (c i : PadicComplex l) * J.θ (f i) := by
  rw [theta_sum J _ _ fun i => om_mul_mem (c i) (hf i)]
  exact Finset.sum_congr rfl fun i _ => by rw [J.θ_mul _ (om_mem _) _ (hf i), J.θ_Om]

omit J in
theorem shift_act (a : ℤ) (g : GQ l) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) *
        P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
  rw [map_mul, DeRhamSymbol.act_zpow, ← mul_assoc, ← mul_assoc,
    ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
    map_one, one_mul]

omit J in
theorem exists_adapted {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V)
    (hL : FiniteDimensional Qp LL) (hV : FiniteDimensional LL V) (hDR : IsDR PD ρ) :
    ∃ (x : Fin d → Fin d → BdR) (u : Fin d → ℤ), (∀ k, (∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x k i)) = x k) ∧
      ∀ i, x k i ∈ PD.Fil (u k)) ∧ ∀ (a : ℤ) (c : Fin d → K), (∀ k, u k ≠ a → c k = 0) →
      (∀ i, ∑ k, algebraMap K BdR (c k) * x k i ∈ PD.Fil (a + 1)) → ∀ k, c k = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  haveI : Nontrivial V := ⟨⟨b ⟨0, hd⟩, 0, b.ne_zero _⟩⟩
  haveI := PD.finK
  have hfin : Module.Finite LL ↥(DdR PD ρ) := by
    apply Module.finite_of_finrank_pos
    rw [hDR]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  obtain ⟨Φ, -, hΦ⟩ := GlobalTheory.exists_coord_tensor_dR PD ρ b
  obtain ⟨D, hD, hDf, hDr⟩ := GlobalTheory.deRham_invariants_coord_finrank PD ρ b hL hfin hDR Φ hΦ
  obtain ⟨x, u, hx, hind⟩ := GlobalTheory.exists_family_adapted_filtration K (Fin d → BdR) D
    (fun a => Submodule.pi Set.univ fun _ => PD.Fil a) d hDf hDr
    (fun a z hz i hi => PD.Fil_anti a (hz i hi))
    (fun z => by
      have anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
      choose f hf using fun i => PD.Fil_exh (z i)
      obtain ⟨m, hm⟩ := (Set.finite_range f).bddBelow
      exact ⟨m, fun i _ => anti (hm ⟨i, rfl⟩) (hf i)⟩)
    (fun z hz => funext fun i => PD.Fil_sep _ fun a => hz a i trivial)
  refine ⟨x, u, fun k => ⟨(hD _).1 (hx k).1, fun i => (hx k).2 i trivial⟩, fun a c hc hs => ?_⟩
  refine hind a c hc fun i _ => ?_
  have := hs i
  simp only [← Algebra.smul_def] at this
  simpa only [Finset.sum_apply, Pi.smul_apply, SetLike.mem_coe] using this

omit J in
theorem sum_mem_DdR {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (b : Module.Basis (Fin d) Qp V) (x : Fin d → BdR)
    (hx : ∀ g : G, (Matrix.of fun i j =>
      algebraMap Qp BdR (b.repr (ρ g (b j)) i)).mulVec (fun i => PD.actdR g (x i)) = x) :
    ∑ i, b i ⊗ₜ[Qp] x i ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  intro g
  have hact : ∀ (v : V) (y : BdR),
      actVdR PD ρ g (v ⊗ₜ y) = ρ g v ⊗ₜ PD.actdR g y := by
    intro v y
    unfold actVdR
    rw [TensorProduct.AlgebraTensorModule.map_tmul]
    rfl
  obtain ⟨Φ, h, -⟩ := GlobalTheory.exists_tensor_coord_of_basis (M := BdR) b
  apply Φ.injective
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  simp only [hact, h, Module.Basis.repr_self]
  have h1 := congrFun (hx g) i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ← Algebra.smul_def] at h1
  rw [h1, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [Finsupp.single_apply, hij]
  · simp

omit J in
theorem exists_symbol_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (θ : ThetaL P AI) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsDR (P.PD K) T.ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)), (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) → ∀ t : (P.R.BdR)ˣ, (t : P.R.BdR) = P.ιB P.tB → ∃ (u : Fin d → ℤ) (y : Fin d → Fin d → P.R.BdR), (∀ k i, y k i ∈ (P.PD K).Fil 0) ∧ (∀ k, ∑ i, b i ⊗ₜ[ℚ_[l]] (y k i * ((t ^ u k : (P.R.BdR)ˣ) : P.R.BdR)) ∈ DdR (P.PD K) T.ρ) ∧ LinearIndependent (PadicComplex l) (fun k i => θ.θ (y k i)) ∧ ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ (fun i => θ.θ (y k i)) = fun i => θ.θ (y k i) := by
  intro l _ P AI J K LL T hDR d b M hM t ht
  obtain rfl : t = tU P := Units.ext ht
  obtain ⟨x, u, hx, hind⟩ := exists_adapted (P.PD K) T.ρ b LL.2 T.fdim hDR
  have key : ∀ k i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i ∈ (P.PD (botExt l)).Fil 0 :=
    fun k i => (shift_iff J (u k) 0 _).2 (by
      rw [add_zero]; exact (mem_iff K _ _).1 ((hx k).2 i))
  have heq : ∀ σ ∈ GK K, ∀ k, twAct AI.actC P.χQ (u k) M σ
      (fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i)) =
      fun i => J.θ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i) := by
    intro σ hσ k
    funext i
    generalize hN : (fun i j => b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i : Fin d → Fin d → ℚ_[l]) = N
    have hN' : ∀ i j, b.repr (T.ρ ⟨σ, hσ⟩ (b j)) i = N i j := fun i j => congrFun (congrFun hN i) j
    have h1 := congrFun ((hx k).1 ⟨σ, hσ⟩) i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, P.PD_actdR, hN'] at h1
    have h2 : ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i =
        ∑ j, algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l)
          (((P.χQ σ ^ u k : ℚ_[l]ˣ) : ℚ_[l]) * N i j)) *
          P.actQdR σ (((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k j) := by
      conv_lhs => rw [← h1]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, shift_act, ← IsScalarTower.algebraMap_apply,
        map_mul (algebraMap ℚ_[l] P.R.BdR), mul_left_comm, mul_assoc]
    conv_rhs => rw [h2, theta_comb J _ _ fun j => act_mem σ (key k j)]
    simp only [twAct, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [J.θ_act σ _ (key k j), hM ⟨σ, hσ⟩ i j, hN', ← mul_assoc, chiC, ← map_mul]
    rfl
  refine ⟨u, fun k i => ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i,
    fun k i => (mem_iff K _ _).2 (key k i), fun k => ?_, ?_, heq⟩
  · have : ∀ i, ((tU P ^ (-u k) : P.R.BdRˣ) : P.R.BdR) * x k i *
        ((tU P ^ u k : P.R.BdRˣ) : P.R.BdR) = x k i := fun i => by
      rw [mul_right_comm, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one,
        one_mul]
    simp only [this]
    exact sum_mem_DdR (P.PD K) T.ρ b _ (hx k).1
  · refine GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise l AI.actC P.χQ (GK K) K.1
      (tate_invariants_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K) d d M _ u heq ?_
    intro a c hc hs
    refine hind a c hc fun i => ?_
    have h1 := congrFun hs i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
    rw [← theta_comb J (fun k => ((c k : ↥K.1) : Om l)) _ (fun k => key k i),
      J.θ_ker _ (Submodule.sum_mem _ fun k _ => om_mul_mem _ (key k i))] at h1
    rw [mem_iff K, ← shift_iff J, Finset.mul_sum]
    convert h1 using 2 with k
    by_cases hk : u k = a
    · rw [hk, mul_left_comm]
      rfl
    · simp [hc k hk]

end GlobalTheory.DeRhamSymbolBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffTeichSub
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc.IoMap

section General

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem X_pow_dvd_sub_trunc (a : R⟦X⟧) (n : ℕ) :
    (X : R⟦X⟧) ^ n ∣ a - (trunc n a : Polynomial R) := by
  rw [X_pow_dvd_iff]
  intro m hm
  simp [coeff_trunc, hm]

theorem algHom_coe (f : R⟦X⟧ →ₐ[R] A) (p : Polynomial R) :
    f (p : R⟦X⟧) = Polynomial.aeval (f X) p := by
  have : f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f X) := by
    ext
    simp
  simpa using DFunLike.congr_fun this p

theorem algHom_unique (f g : R⟦X⟧ →ₐ[R] A) (h : f X = g X)
    (hs : ∀ x : A, (∀ n, f X ^ n ∣ x) → x = 0) : f = g := by
  ext a
  rw [← sub_eq_zero]
  refine hs _ fun n => ?_
  obtain ⟨b, hb⟩ := X_pow_dvd_sub_trunc a n
  have h1 := congrArg f hb
  have h2 := congrArg g hb
  rw [map_sub, map_mul, map_pow, algHom_coe] at h1 h2
  rw [← h] at h2
  exact ⟨f b - g b, by linear_combination h1 - h2⟩

theorem algHom_exists (y : A) (hc : GlobalTheory.Per.AinfComplete.Summ y)
    (hs : ∀ x : A, (∀ n, y ^ n ∣ x) → x = 0) : ∃ f : R⟦X⟧ →ₐ[R] A, f X = y := by
  have h1 : ∀ a : R⟦X⟧, ∃ L : A, ∀ n, y ^ n ∣ L - Polynomial.aeval y (trunc n a) := by
    intro a
    obtain ⟨L, hL⟩ := hc fun i => algebraMap R A (coeff i a)
    refine ⟨L, fun n => ?_⟩
    have e : Polynomial.aeval y (trunc n a) =
        ∑ i ∈ Finset.range n, y ^ i * algebraMap R A (coeff i a) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [trunc_succ, map_add (f := _), ih, Finset.sum_range_succ, Polynomial.aeval_monomial, mul_comm]
    rw [e]
    exact Ideal.mem_span_singleton.1 (hL n)
  choose L hL using h1
  have h2 : ∀ (a : R⟦X⟧) (p : Polynomial R) (n : ℕ), (X : R⟦X⟧) ^ n ∣ a - p →
      y ^ n ∣ L a - Polynomial.aeval y p := by
    intro a p n h
    have h3 : (Polynomial.X : Polynomial R) ^ n ∣ trunc n a - p := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      have := X_pow_dvd_iff.1 h d hd
      simpa [coeff_trunc, hd] using this
    have h4 := map_dvd (Polynomial.aeval y) h3
    rw [map_pow, Polynomial.aeval_X, map_sub] at h4
    convert dvd_add (hL a n) h4 using 1
    ring
  have h3 : ∀ p : Polynomial R, L p = Polynomial.aeval y p := fun p => by
    rw [← sub_eq_zero]
    exact hs _ fun n => h2 _ _ _ (by simp)
  have hadd : ∀ a b, L (a + b) = L a + L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := hL (a + b) n
    rw [map_add (f := _), map_add (f := _)] at this
    convert dvd_sub (dvd_sub this (hL a n)) (hL b n) using 1
    ring
  have hmul : ∀ a b, L (a * b) = L a * L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := h2 (a * b) (trunc n a * trunc n b) n (by
      rw [Polynomial.coe_mul]
      convert dvd_add ((X_pow_dvd_sub_trunc a n).mul_right b)
        ((X_pow_dvd_sub_trunc b n).mul_left (trunc n a : Polynomial R)) using 1
      ring)
    rw [map_mul] at this
    convert dvd_sub (dvd_sub this ((hL a n).mul_right (L b)))
      ((hL b n).mul_left (Polynomial.aeval y (trunc n a))) using 1
    ring
  refine ⟨{ toFun := L
            map_one' := by simpa using h3 1
            map_mul' := hmul
            map_zero' := by simpa using h3 0
            map_add' := hadd
            commutes' := fun r => by simpa using h3 (Polynomial.C r) }, ?_⟩
  simpa using h3 Polynomial.X

end General

variable (l : ℕ) [Fact l.Prime]

theorem ne_zero_of_coeff {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (m : ℕ) : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ coeff m a → ψ a ≠ 0 := by
  have h0 : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a → ψ a ≠ 0 := by
    intro a ha
    have : IsUnit (constantCoeff a) := by
      by_contra hn
      exact ha ((PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.not_isUnit_iff.1 hn))
    exact ((isUnit_iff_constantCoeff.2 this).map ψ).ne_zero
  induction m with
  | zero => intro a ha; exact h0 a (by simpa using ha)
  | succ m ih =>
    intro a ha
    by_cases h : ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a
    · obtain ⟨c, hc⟩ := h
      rw [eq_X_mul_shift_add_const a, hc, map_add (f := _), map_mul, map_mul, map_mul, map_natCast,
        map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
      exact mul_ne_zero hX (ih _ (by simpa using ha))
    · exact h0 a h

theorem ne_zero_of_not_dvd {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (a : ℤ_[l]⟦X⟧) (ha : ¬ ((l : ℕ) : ℤ_[l]⟦X⟧) ∣ a) : ψ a ≠ 0 := by
  by_contra h
  apply ha
  have : ∀ m, ((l : ℕ) : ℤ_[l]) ∣ coeff m a := fun m => by
    by_contra hm
    exact ne_zero_of_coeff l ψ hX m a hm h
  choose c hc using this
  refine ⟨PowerSeries.mk c, ?_⟩
  ext m
  rw [← map_natCast (C : ℤ_[l] →+* ℤ_[l]⟦X⟧), coeff_C_mul, coeff_mk, hc]

theorem phi_X : phi l ℤ_[l] X = (1 + X) ^ l - 1 := by
  rw [phi, act, substAlgHom_X, cyc, binomialSeries_nat]
  simp

theorem constantCoeff_teich_sub (e : OCb l) :
    WittVector.constantCoeff (WittVector.teichmuller l e - 1 : Ainf l) = e - 1 := by
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem complete_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    GlobalTheory.Per.AinfComplete.Summ (WittVector.teichmuller l e - 1 : Ainf l) ∧
      ∀ x : Ainf l, (∀ n, (WittVector.teichmuller l e - 1 : Ainf l) ^ n ∣ x) → x = 0 := by
  have hy : ¬ IsUnit (WittVector.teichmuller l e - 1 : Ainf l) := fun h =>
    he (constantCoeff_teich_sub l e ▸ h.map WittVector.constantCoeff)
  have := (GlobalTheory.Per.AinfComplete.main l _ hy).2
  exact ⟨GlobalTheory.Per.AinfComplete.summ_of_precomplete _, fun x hx =>
    GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (hx n)⟩

noncomputable def frobA : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem frobA_apply (x : Ainf l) : frobA l x = WittVector.frobenius x := by
  rw [WittVector.frobenius_eq_map_frobenius]
  rfl

theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ e : OCb l, ¬ IsUnit (e - 1) →
    (∃! io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io) ∧
    ∀ io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io →
      (∀ a, io (phi l ℤ_[l] a) = WittVector.frobenius (io a)) ∧
      (e ≠ 1 → ∀ a, ¬ ((l : ℕ) : PowerSeries ℤ_[l]) ∣ a → IsUnit (inclW l (io a))) := by
  intro l hl e he
  obtain ⟨hc, hs⟩ := complete_teich l e he
  refine ⟨?_, fun io hio => ⟨?_, fun he1 a ha => ?_⟩⟩
  · obtain ⟨f, hf⟩ := algHom_exists (R := ℤ_[l]) _ hc hs
    refine ⟨f, hf, fun g hg => algHom_unique g f (Eq.trans hg hf.symm) ?_⟩
    rw [show g X = _ from hg]
    exact hs
  · have he' : ¬ IsUnit (e ^ l - 1) := fun h => he (by
      rw [← geom_sum_mul] at h
      exact isUnit_of_mul_isUnit_right h)
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have e1 : (io.comp (phi l ℤ_[l])) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, phi_X, map_sub, map_pow, map_add (f := _), map_one, hio', map_pow]
      ring
    have e2 : ((frobA l).comp io) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, hio', map_sub, map_one]
      congr 1
      exact WittVector.map_teichmuller l (frobenius (OCb l) l) e
    have := algHom_unique _ _ (e1.trans e2.symm) (by rw [e1]; exact (complete_teich l _ he').2)
    intro a
    rw [← frobA_apply]
    exact DFunLike.congr_fun this a
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [inclW, WittVector.map_coeff]
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have := ne_zero_of_not_dvd l
      ((WittVector.constantCoeff : Ainf l →+* OCb l).comp io.toRingHom) (by
        change WittVector.constantCoeff (io X) ≠ 0
        rw [hio', constantCoeff_teich_sub]
        exact sub_ne_zero.2 he1) a ha
    intro hz
    exact this ((IsFractionRing.injective (OCb l) (Cb l)) (hz.trans (map_zero _).symm))

end GlobalTheory.Cyc.IoMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowNorm
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.GaussCore

theorem le_of_homog {A : Type} [CommRing A] (N : A → ℝ) (h01 : ∀ x, 0 ≤ N x ∧ N x ≤ 1)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) (hneg : ∀ x, N (-x) = N x)
    (hmul : ∀ x y, N (x * y) = N x * N y) (a b : A) (d : ℕ) (c : ℕ → A)
    (h : a ^ d + ∑ i ∈ Finset.range d, c i * a ^ i * b ^ (d - i) = 0) (hA : N 1 = 1) :
    N a ≤ N b := by
  by_contra hlt
  push_neg at hlt
  have ha : 0 < N a := lt_of_le_of_lt (h01 b).1 hlt
  have hb1 : N b < 1 := lt_of_lt_of_le hlt (h01 a).2
  have h0 : N 0 = 0 := by
    have := hmul 0 b
    rw [zero_mul] at this
    have h2 := (h01 0).1
    nlinarith
  have hpow : ∀ (x : A) (n : ℕ), N (x ^ n) = N x ^ n := by
    intro x n
    induction n with
    | zero => simpa using hA
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → A) (M : ℝ), 0 < M → (∀ i ∈ s, N (f i) < M) →
      N (∑ i ∈ s, f i) < M := by
    intro s f M hM
    induction s using Finset.induction_on with
    | empty => intro _; simpa [h0] using hM
    | insert i s hi ih =>
      intro hs
      rw [Finset.sum_insert hi]
      exact lt_of_le_of_lt (hadd _ _) (max_lt (hs i (Finset.mem_insert_self _ _))
        (ih fun j hj => hs j (Finset.mem_insert_of_mem hj)))
  have key := hsum (Finset.range d) (fun i => c i * a ^ i * b ^ (d - i)) (N a ^ d) (pow_pos ha d) (by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [hmul, hmul, hpow, hpow]
    have e : N a ^ d = N a ^ i * N a ^ (d - i) := by
      rw [← pow_add]; congr 1; omega
    have h1 : N b ^ (d - i) < N a ^ (d - i) := pow_lt_pow_left₀ hlt (h01 b).1 (by omega)
    have h2 : 0 < N a ^ i := pow_pos ha i
    have h3 : 0 ≤ N b ^ (d - i) := pow_nonneg (h01 b).1 _
    calc N (c i) * N a ^ i * N b ^ (d - i) ≤ 1 * N a ^ i * N b ^ (d - i) := by
          gcongr; exact (h01 _).2
      _ < N a ^ d := by rw [one_mul, e]; gcongr)
  rw [eq_neg_of_add_eq_zero_right h, hneg, hpow] at key
  exact lt_irrefl _ key

variable {l : ℕ} [Fact l.Prime]

theorem exists_monic (x : Om l) (h : ‖x‖ ≤ 1) : ∃ q : Polynomial ℤ_[l], q.Monic ∧
    Polynomial.eval₂ ((algebraMap ℚ_[l] (Om l)).comp (algebraMap ℤ_[l] ℚ_[l])) x q = 0 := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval₂_map, hq, ← Polynomial.aeval_def, minpoly.aeval]

theorem exists_pow_norm (x : Om l) (hx : x ≠ 0) :
    ∃ (t : ℕ) (s : ℤ), 0 < t ∧ ‖x‖ ^ t = (l : ℝ) ^ s := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[l] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have hd := minpoly.natDegree_pos hi
  refine ⟨(minpoly ℚ_[l] x).natDegree, -((minpoly ℚ_[l] x).coeff 0).valuation, hd, ?_⟩
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    ← Padic.norm_eq_zpow_neg_valuation h0, one_div]
  exact Real.rpow_inv_natCast_pow (norm_nonneg _) hd.ne'

theorem j_alg (C : Core l) (a : Per.Ainf l) :
    C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.RingIface.tower, C.j_cris.on0]
  simp [aDp]

set_option allowUnsafeReducibility true
attribute [local irreducible] Per.Acris Per.Bcris

theorem homog_eq (C : Core l) (a b : Per.Acris l) (y : Om l) (hy : ‖y‖ ≤ 1)
    (h : C.j a = C.o y * C.j b) : ∃ (d : ℕ) (c : ℕ → Per.Acris l),
      a ^ d + ∑ i ∈ Finset.range d, c i * a ^ i * b ^ (d - i) = 0 := by
  obtain ⟨q, hq, h0⟩ := exists_monic y hy
  refine ⟨q.natDegree, fun i => algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (q.coeff i)), ?_⟩
  apply crisP_injective l C.j C.j_cris
  rw [hq.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at h0
  have h1 := congrArg (fun z => C.o z * C.j b ^ q.natDegree) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_pow, map_sum, map_zero, zero_mul, add_mul, Finset.sum_mul,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_mul] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_pow, map_sum, map_zero, map_mul, h, j_alg]
  rw [← h1, mul_pow]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [← C.o_sec.z]
  have e : C.j b ^ q.natDegree = C.j b ^ i * C.j b ^ (q.natDegree - i) := by
    rw [← pow_add]; congr 1; omega
  rw [e, mul_pow]
  simp only [RingHom.comp_apply, PadicInt.algebraMap_apply]
  ring

theorem untilt_zero : (0 : Per.Fl l).untilt = 0 := by
  rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

theorem gauss_l (r : ℝ) (hr : 0 ≤ r) :
    (⨆ n : ℕ, ‖(((((l : ℕ) : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^
      ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) = r := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hf : ∀ n : ℕ, ‖(((((l : ℕ) : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^
      ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n = if n = 1 then r else 0 := by
    intro n
    rw [WittVector.coeff_p]
    split_ifs with h
    · simp [h]
    · rw [untilt_zero]
      have : ((1 : ℝ) / (l : ℝ) ^ n) ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  simp only [hf]
  have hb : ∀ n : ℕ, (if n = 1 then r else 0) ≤ r := fun n => by split_ifs <;> simp [hr]
  refine le_antisymm (ciSup_le hb) ?_
  have := le_ciSup (f := fun n : ℕ => if n = 1 then r else 0) ⟨r, by rintro _ ⟨n, rfl⟩; exact hb n⟩ 1
  simpa using this

theorem exp_eq {u v c c' : ℝ} {k k' : ℤ} (hu : 0 < u) (huv : u < v) (hc : 0 < c)
    (h : ∀ r, u < r → r < v → c * r ^ k = c' * r ^ k') : k = k' := by
  obtain ⟨r, h1, h2⟩ := exists_between huv
  obtain ⟨s, h3, h4⟩ := exists_between h2
  have hr : 0 < r := hu.trans h1
  have hs : 0 < s := hr.trans h3
  have e1 := h r h1 h2
  have e2 := h s (h1.trans h3) h4
  have hq : 1 < s / r := (one_lt_div hr).2 h3
  have hc' : c' ≠ 0 := by
    rintro rfl
    have : 0 < c * r ^ k := mul_pos hc (zpow_pos hr _)
    rw [e1, zero_mul] at this
    exact lt_irrefl _ this
  apply zpow_right_injective₀ (one_pos.trans hq) hq.ne'
  have a1 : r ^ k ≠ 0 := (zpow_pos hr _).ne'
  have a2 : r ^ k' ≠ 0 := (zpow_pos hr _).ne'
  show (s / r) ^ k = (s / r) ^ k'
  rw [div_zpow, div_zpow, ← mul_div_mul_left _ _ hc.ne', e1, e2, mul_div_mul_left _ _ hc']

theorem norm_eq_zpow : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (a b : Per.Acris l) (x : Om l),
    b ≠ 0 → x ≠ 0 → C.j a = C.o x * C.j b → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  intro l _ C a b x hb hx h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl : (0 : ℝ) < l := one_pos.trans hl1
  have hli : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 hl
  have hex : ∀ r : ℝ, ∃ N : Per.Acris l → ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ (∀ x y, N (x * y) = N x * N y) ∧ ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := by
    intro r
    by_cases h1 : (l : ℝ)⁻¹ ≤ r ∧ r < 1
    · obtain ⟨N, hN⟩ := GlobalTheory.T.exists_gauss_norm_extension_acris l r h1.1 h1.2
      exact ⟨N, fun _ _ => hN⟩
    · exact ⟨fun _ => 0, fun h2 h3 => absurd ⟨h2, h3⟩ h1⟩
  choose N hN using hex
  have ha : a ≠ 0 := by
    rintro rfl
    apply hb
    apply crisP_injective l C.j C.j_cris
    have := congrArg (fun z => C.o x⁻¹ * z) h
    simp only [map_zero, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one,
      one_mul] at this
    rw [← this, map_zero]
  obtain ⟨r₁, c, k, hr₁, hr₁', hc, hNa⟩ := GlobalTheory.T.acris_gauss_norm_eventually_monomial l N hN a (GlobalTheory.T.acris_norm_of_nonzero l N hN a ha)
  obtain ⟨r₂, c', k', hr₂, hr₂', hc', hNb⟩ := GlobalTheory.T.acris_gauss_norm_eventually_monomial l N hN b (GlobalTheory.T.acris_norm_of_nonzero l N hN b hb)
  obtain ⟨t, s, ht, hts⟩ := exists_pow_norm x hx
  obtain ⟨m, n, rfl⟩ : ∃ m n : ℕ, s = (m : ℤ) - n := ⟨s.toNat, (-s).toNat, by omega⟩
  have hl0 : ((l : ℕ) : Om l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hnl : ‖((l : ℕ) : Om l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]
  set y : Om l := x ^ t * (l : Om l) ^ m / (l : Om l) ^ n with hy
  have hy1 : ‖y‖ = 1 := by
    rw [hy, norm_div, norm_mul, norm_pow, norm_pow, norm_pow, hts, hnl, zpow_sub₀ hl.ne']
    simp only [zpow_natCast, inv_pow]
    field_simp
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hy1; exact zero_ne_one hy1
  have e1 : C.j (a ^ t * (l : Per.Acris l) ^ m) = C.o y * C.j (b ^ t * (l : Per.Acris l) ^ n) := by
    have e : y * (l : Om l) ^ n = x ^ t * (l : Om l) ^ m := div_mul_cancel₀ _ (pow_ne_zero _ hl0)
    have e' := congrArg C.o e
    simp only [map_mul, map_pow, map_natCast] at e' ⊢
    rw [h, mul_pow]
    linear_combination (-(C.j b) ^ t) * e'
  have e2 : C.j (b ^ t * (l : Per.Acris l) ^ n) = C.o y⁻¹ * C.j (a ^ t * (l : Per.Acris l) ^ m) := by
    rw [e1, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hy0, map_one, one_mul]
  obtain ⟨d1, c1, q1⟩ := homog_eq C _ _ y hy1.le e1
  obtain ⟨d2, c2, q2⟩ := homog_eq C _ _ y⁻¹ (by rw [norm_inv, hy1, inv_one]) e2
  have hk : k * t + m = k' * t + n := by
    refine exp_eq (c := c ^ t) (c' := c' ^ t) hli (lt_min hr₁ hr₂) (pow_pos hc t) fun r h1 h2 => ?_
    have hr : 0 < r := hli.trans h1
    have h3 : r < r₁ := h2.trans_le (min_le_left _ _)
    have h4 : r < r₂ := h2.trans_le (min_le_right _ _)
    obtain ⟨n01, nadd, nneg, nmul, nalg⟩ := hN r h1.le (h3.trans hr₁')
    have hNl : N r (l : Per.Acris l) = r := by
      rw [← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)), nalg, gauss_l r hr.le]
    have hN1 : N r 1 = 1 := by
      have := nmul (l : Per.Acris l) 1
      rw [mul_one, hNl] at this
      exact (mul_eq_left₀ hr.ne').1 this.symm
    have hpow : ∀ (x : Per.Acris l) (n : ℕ), N r (x ^ n) = N r x ^ n := by
      intro x n
      induction n with
      | zero => simpa using hN1
      | succ n ih => rw [pow_succ, nmul, ih, pow_succ]
    have e := le_antisymm (le_of_homog (N r) n01 nadd nneg nmul _ _ d1 c1 q1 hN1)
      (le_of_homog (N r) n01 nadd nneg nmul _ _ d2 c2 q2 hN1)
    rw [nmul, nmul, hpow, hpow, hpow, hpow, hNl, hNa r h1 h3, hNb r h1 h4] at e
    rw [zpow_add₀ hr.ne', zpow_add₀ hr.ne', zpow_mul, zpow_mul]
    simp only [zpow_natCast]
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow, e]
  refine ⟨k' - k, ?_⟩
  apply (pow_left_inj₀ (norm_nonneg _) (zpow_pos hl _).le ht.ne').1
  rw [hts, ← zpow_natCast, ← zpow_mul]
  congr 1
  linear_combination hk

end GlobalTheory.MemLoc.GaussCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntPts
noncomputable section

open Classical

namespace GlobalTheory.PositionData

def intPts (A : Set ℚ) : Finset ℤ :=
  if h : ((fun z : ℤ => (z : ℚ)) ⁻¹' A).Finite then h.toFinset else ∅

theorem mem_intPts {A : Set ℚ} (hA : A.Finite) (z : ℤ) : z ∈ intPts A ↔ (z : ℚ) ∈ A := by
  have h : ((fun z : ℤ => (z : ℚ)) ⁻¹' A).Finite :=
    hA.preimage (Set.injOn_of_injective Int.cast_injective)
  unfold intPts
  rw [dite_eq_left h, Set.Finite.mem_toFinset]
  rfl

def mnLo (Fl : Finset ℤ) : ℤ := (insert 0 Fl).min' (Finset.insert_nonempty _ _)

def mxLo (t : ℕ) (Fl : Finset ℤ) : ℤ := (insert ((t : ℤ) - 1) Fl).max' (Finset.insert_nonempty _ _)

def mnAll (Fl Fc : Finset ℤ) : ℤ := (insert 0 (Fl ∪ Fc)).min' (Finset.insert_nonempty _ _)

def mxAll (t : ℕ) (Fl Fc : Finset ℤ) : ℤ :=
  (insert ((t : ℤ) - 1) (Fl ∪ Fc)).max' (Finset.insert_nonempty _ _)

def wS (up : Bool) (Fl Fc : Finset ℤ) : ℕ :=
  if up then (1 - mnLo Fl).toNat else (1 - mnAll Fl Fc).toNat

def etaS (t : ℕ) (Fl : Finset ℤ) : ℕ := (mxLo t Fl - mnLo Fl + 1).toNat

def hS (up : Bool) (t : ℕ) (Fl Fc : Finset ℤ) : ℕ :=
  if up then (mxAll t Fl Fc + wS up Fl Fc + 1).toNat else (mxLo t Fl + wS up Fl Fc + 1).toNat

def US (up : Bool) (Fl Fc : Finset ℤ) : Multiset ℤ :=
  (Fl ∪ Fc).val.map (fun z => z + (wS up Fl Fc : ℤ))

theorem count_US (up : Bool) (Fl Fc : Finset ℤ) (b : ℤ) :
    (US up Fl Fc).count (b + wS up Fl Fc) = if b ∈ Fl ∪ Fc then 1 else 0 := by
  unfold US
  rw [Multiset.count_map_eq_count' _ _ (add_left_injective _)]
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem (Fl ∪ Fc).nodup h
  · exact Multiset.count_eq_zero.mpr h

end GlobalTheory.PositionData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankCount
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankCount
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.Decomp

theorem card_eq_finrank_mul_card {Z O R T : Type} [CommRing Z] [Nontrivial Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing R] [Nontrivial R] [Algebra O R]
    [AddCommGroup T] [Module O T] [Module.Free O T] [Module Z T] [IsScalarTower Z O T]
    {d : ℕ} (b : Module.Basis (Fin d) Z T) {ι : Type} [Fintype ι] (v : ι → R ⊗[O] T)
    (h1 : LinearIndependent R v) (h2 : Submodule.span R (Set.range v) = ⊤) :
    d = Module.finrank Z O * Fintype.card ι := by
  have e1 : Module.finrank Z T = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have e2 : Module.finrank R (R ⊗[O] T) = Fintype.card ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk h1 h2.ge)
  rw [← e1, ← e2, Module.finrank_baseChange, Module.finrank_mul_finrank]

theorem nontrivial_tensor_of_free {Z O S : Type} [CommRing Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing S] [Nontrivial S] [Algebra Z S] :
    Nontrivial (O ⊗[Z] S) := by
  haveI : Module.FaithfullyFlat Z O := inferInstance
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
theorem rank_count : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (ι : Type) [Fintype ι] (v : ι → TW (RW LL) T), IsMat K LL T M A → LinearIndependent (RW LL) v → Submodule.span (RW LL) (Set.range v) = ⊤ → ∃ (f : ℕ) (_ : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), Nonempty (Fin d ≃ Fin f × ι) := by
  intro l _ K LL T d M A ι _ v hM h1 h2
  haveI := freeOL LL
  haveI := finiteOL LL
  letI := zlMod LL T
  obtain ⟨b, -, -⟩ := hM
  haveI : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  haveI : IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : Nontrivial (RW LL) := nontrivial_tensor_of_free
  have h := card_eq_finrank_mul_card (R := RW LL) b v h1 h2
  refine ⟨Module.finrank ℤ_[l] ↥(OL LL), Module.finBasis _ _, ⟨Fintype.equivOfCardEq ?_⟩⟩
  simpa using h

end GlobalTheory.Cyc.Decomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankCountStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_and_equiv_fin_prod_of_basis : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (ι : Type) [Fintype ι] (v : ι → TW (RW LL) T), IsMat K LL T M A → LinearIndependent (RW LL) v → Submodule.span (RW LL) (Set.range v) = ⊤ → ∃ (f : ℕ) (_ : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), Nonempty (Fin d ≃ Fin f × ι) := by
  first | exact @GlobalTheory.Cyc.Decomp.rank_count | exact GlobalTheory.Cyc.Decomp.rank_count | (intros; apply GlobalTheory.Cyc.Decomp.rank_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatLogFloorExpLe
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

private lemma natLog_mul_log_two_le_log_of_le {l m : ℕ} {C : ℝ} (hl : 2 ≤ l) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ C) : (Nat.log l m : ℝ) * Real.log 2 ≤ Real.log C := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using Real.log_nonneg hC
  have h1 : Nat.log l m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hl
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 : ℝ) ^ Nat.log l m ≤ C :=
    calc (2 : ℝ) ^ Nat.log l m ≤ 2 ^ Nat.log 2 m := pow_le_pow_right₀ (by norm_num) h1
      _ ≤ m := by exact_mod_cast h2
      _ ≤ C := hm
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

private lemma natLog_le_add_two_mul_of_le_two_pow_mul_exp {l m k : ℕ} {L : ℝ} (hl : 2 ≤ l) (hL : 0 ≤ L)
    (hm : (m : ℝ) ≤ 2 ^ k * Real.exp L) : (Nat.log l m : ℝ) ≤ k + 2 * L := by
  have hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)
  have h := natLog_mul_log_two_le_log_of_le hl hC hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_contra hcon
  push_neg at hcon
  have : ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L := by linarith
  nlinarith

theorem _root_.GlobalTheory.HubLoc.cBnum_le_thirty : ∀ (l t N : ℕ) (L : ℝ), 2 ≤ l → 1 ≤ t → 1 ≤ N →
    1 ≤ L → (_root_.GlobalTheory.HubLoc.cBnum l ⌊2 * Real.exp L⌋₊ t N : ℝ) ≤ 30 * t * N * L := by
  intro l t N L hl ht hN hL
  have hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L :=
    Nat.floor_le (by positivity)
  have hm : ((2 * ⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 ^ 2 * Real.exp L := by
    push_cast
    nlinarith
  have hK := natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm
  unfold _root_.GlobalTheory.HubLoc.cBnum
  push_cast at hK ⊢
  set K : ℝ := (Nat.log l (2 * ⌊2 * Real.exp L⌋₊) : ℝ)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have htN : (1 : ℝ) ≤ t * N := one_le_mul_of_one_le_of_one_le ht' hN'
  have htNL : (1 : ℝ) ≤ t * N * L := one_le_mul_of_one_le_of_one_le htN hL
  have hL1 : L ≤ t * N * L := by nlinarith
  have ht1 : (t : ℝ) ≤ t * N * L := by nlinarith
  have hA : (t : ℝ) * N * K ≤ t * N * (2 + 2 * L) := by
    apply mul_le_mul_of_nonneg_left hK; positivity
  nlinarith

end GlobalTheory.HubLoc
end
