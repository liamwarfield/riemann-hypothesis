module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem algHom_ext_of_constantCoeff_zero {O : Type} [CommRing O]
    (f g : PowerSeries O →ₐ[O] PowerSeries O) (h : f PowerSeries.X = g PowerSeries.X)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) : f = g := by
  have key : ∀ (n : ℕ) (a : PowerSeries O), PowerSeries.X ^ n ∣ f a - g a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      obtain ⟨b, hb⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
        rw [PowerSeries.X_dvd_iff]; simp
      have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
        rw [← hb, PowerSeries.algebraMap_eq]; ring
      have : f a - g a = f PowerSeries.X * (f b - g b) := by
        conv_lhs => rw [ha]
        rw [map_add (f := _), map_add (f := _), map_mul, map_mul, f.commutes, g.commutes, ← h]; ring
      rw [this, pow_succ']
      exact mul_dvd_mul (PowerSeries.X_dvd_iff.2 h0) (ih b)
  ext a n
  have := (PowerSeries.X_pow_dvd_iff.1 (key (n + 1) a)) n (Nat.lt_succ_self n)
  rw [map_sub] at this
  exact sub_eq_zero.1 this

theorem constantCoeff_algHom {O : Type} [CommRing O]
    (f : PowerSeries O →ₐ[O] PowerSeries O)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) (a : PowerSeries O) :
    PowerSeries.constantCoeff (f a) = PowerSeries.constantCoeff a := by
  obtain ⟨b, hb⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]; simp
  have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
    rw [← hb, PowerSeries.algebraMap_eq]; ring
  conv_lhs => rw [ha]
  rw [map_add (f := _), map_mul, f.commutes, map_add (f := _), map_mul, h0, PowerSeries.algebraMap_eq]
  simp

theorem eq_of_commute_pow {O : Type} [CommRing O] [IsDomain O] (l : ℕ) (hl0 : (l : O) ≠ 0)
    (hlu : ¬ IsUnit (l : O)) (φ f g : PowerSeries O →ₐ[O] PowerSeries O)
    (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1)
    (hf : φ (f PowerSeries.X) = f (φ PowerSeries.X))
    (hg : φ (g PowerSeries.X) = g (φ PowerSeries.X))
    (hf0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0)
    (hg0 : PowerSeries.constantCoeff (g PowerSeries.X) = 0)
    (h1 : PowerSeries.coeff 1 (f PowerSeries.X) = PowerSeries.coeff 1 (g PowerSeries.X)) :
    f PowerSeries.X = g PowerSeries.X := by
  set F := f PowerSeries.X with hF
  set G := g PowerSeries.X with hG
  have hφ0 : PowerSeries.constantCoeff (φ PowerSeries.X) = 0 := by rw [hφ]; simp
  have hp : φ PowerSeries.X = PowerSeries.X *
      ∑ i ∈ Finset.range l, (1 + PowerSeries.X : PowerSeries O) ^ i := by
    rw [hφ, ← geom_sum_mul]; ring
  have hd : φ (F - G) = (F - G) * ∑ i ∈ Finset.range l, (1 + F) ^ i * (1 + G) ^ (l - 1 - i) := by
    rw [map_sub, hf, hg, hφ]
    have := (Commute.all (1 + F) (1 + G)).mul_geom_sum₂ l
    simp only [map_sub, map_pow, map_add (f := _), map_one, ← hF, ← hG]
    rw [show (1 + F) - (1 + G) = F - G by ring] at this
    rw [this]; ring
  have key : ∀ n : ℕ, PowerSeries.X ^ (n + 2) ∣ F - G := by
    intro n
    induction n with
    | zero =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [hf0, hg0]
      · rw [map_sub, h1, sub_self]
    | succ n ih =>
      obtain ⟨e, he⟩ := ih
      rw [he, map_mul, map_pow, hp, mul_pow, mul_assoc, mul_assoc] at hd
      have hc := congrArg PowerSeries.constantCoeff
        (mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) hd)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_pow, map_sum, map_add (f := _), map_one, PowerSeries.constantCoeff_X, hf0, hg0,
        add_zero, one_pow, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        constantCoeff_algHom φ hφ0] at hc
      have he0 : PowerSeries.constantCoeff e = 0 := by
        by_contra hne
        have h2 : (l : O) * ((l : O) ^ (n + 1) - 1) * PowerSeries.constantCoeff e = 0 := by
          linear_combination hc
        rcases mul_eq_zero.1 h2 with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · exact hl0 h4
          · exact hlu (IsUnit.of_pow_eq_one (sub_eq_zero.1 h4) (Nat.succ_ne_zero n))
        · exact hne h3
      rw [he, show n + 1 + 2 = n + 2 + 1 from rfl, pow_succ]
      exact mul_dvd_mul_left _ (PowerSeries.X_dvd_iff.2 he0)
  ext n
  have := (PowerSeries.X_pow_dvd_iff.1 (key n)) n (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.1 this

theorem act_unique : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (f : PowerSeries O →ₐ[O] PowerSeries O) (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (c : ℤ_[l]), φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 → (∀ a, φ₀ (f a) = f (φ₀ a)) → PowerSeries.constantCoeff (f PowerSeries.X) = 0 → PowerSeries.coeff 1 (f PowerSeries.X) = algebraMap ℤ_[l] O c → φ₀ = phi l O ∧ f = act l O c := by
  intro l _ O _ _ _ _ _ hl0 hlu f φ₀ c hφ hcomm hf0 hf1
  obtain ⟨hX, hmul, -, hnat, hlin, -⟩ := GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws l O
  have hφe : φ₀ = phi l O := by
    refine algHom_ext_of_constantCoeff_zero _ _ ?_ (by rw [hφ]; simp)
    rw [hφ, phi, hX, hnat]
  refine ⟨hφe, algHom_ext_of_constantCoeff_zero _ _ ?_ hf0⟩
  refine eq_of_commute_pow l hl0 hlu φ₀ f (act l O c) hφ (hcomm _) ?_ hf0 ?_ ?_
  · rw [hφe, phi, hmul, hmul, mul_comm]
  · rw [hX, cyc_const]
  · rw [hX, hlin, hf1]

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriods
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriods
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.DeRhamSpan

open GlobalTheory.DeRhamCompare
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod)

theorem span_of_invariant {G E M : Type} [CommRing E] (hE : IsField E) [AddCommGroup M]
    [Module E M] [Module.Finite E M] {n : ℕ} (hn : n = finrank E M)
    (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : Fin n → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : Fin n → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0)
    (y : M) : ∃ c : Fin n → E, ∑ i, c i • v i = y := by
  letI := hE.toField
  have h := GlobalTheory.Per.linearIndependent_of_invariant G E M (Fin n) σ ρ hρ v hv hind
  have h2 := h.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin]; exact hn)
  exact (Submodule.mem_span_range_iff_exists_fun E).1 (h2 ▸ Submodule.mem_top)

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem finrank_DdRK [FiniteDimensional Qp LL] [FiniteDimensional LL V] (h : IsDR PD ρ) :
    FiniteDimensional K (DdRK PD ρ) ∧ finrank K (DdRK PD ρ) = finrank Qp V := by
  have := PD.finK
  have := finite_DdR PD ρ h
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have : FiniteDimensional Qp (DdR PD ρ) := Module.Finite.trans LL _
  let ε : DdR PD ρ ≃ₗ[Qp] DdRK PD ρ :=
    { toFun := fun x => DeRhamCompare.toK PD ρ x x.2
      invFun := fun y => ⟨(TensorProduct.comm Qp V BdR).symm y, y.2⟩
      map_add' := fun x y => Subtype.ext (by simp [DeRhamCompare.toK])
      map_smul' := fun a x => Subtype.ext (by simp [DeRhamCompare.toK])
      left_inv := fun x => Subtype.ext (by simp [DeRhamCompare.toK])
      right_inv := fun x => Subtype.ext (by simp [DeRhamCompare.toK]) }
  have : FiniteDimensional Qp (DdRK PD ρ) := ε.finiteDimensional
  refine ⟨Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K (DdRK PD ρ)
  have h2 := Module.finrank_mul_finrank Qp LL (DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  rw [← ε.finrank_eq, ← h2, h, mul_left_comm, h3] at h1
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

theorem span_of_isField [FiniteDimensional Qp LL] [FiniteDimensional LL V] (hF : IsField BdR)
    (h : IsDR PD ρ) (y : V ⊗[Qp] BdR) :
    ∃ (m : ℕ) (b : Fin m → BdR) (d : Fin m → V ⊗[Qp] BdR), (∀ i, d i ∈ DdR PD ρ) ∧
      y = ∑ i, mulPeriod (Qp := Qp) (LL := LL) (V := V) (b i) (d i) := by
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have := hF.nontrivial
  obtain ⟨_, hr⟩ := finrank_DdRK PD ρ h
  let e := Module.finBasisOfFinrankEq K _ hr
  let σ : G → BdR ⊗[Qp] V →ₗ[Qp] BdR ⊗[Qp] V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨b, hb⟩ := span_of_invariant (M := BdR ⊗[Qp] V) hF (n := finrank Qp V)
    Module.finrank_baseChange.symm
    (fun g => (PD.actdR g : BdR →+* BdR)) (fun g => (σ g).toAddMonoidHom) hσ
    (fun k => (e k : BdR ⊗[Qp] V))
    (fun g k => by
      have h1 := hc g ((TensorProduct.comm Qp V BdR).symm (e k))
      rw [(mem_DdR PD ρ _).1 (e k).2 g, LinearEquiv.apply_symm_apply] at h1
      exact h1)
    (fun c hcg hsum k => by
      choose a ha using fun p => PD.invdR (c p) fun g => hcg g p
      have h1 : ∑ i, a i • e i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_zero, ← hsum]
        simp only [Submodule.coe_sum, Submodule.coe_smul, ← ha, algebraMap_smul]
      rw [← ha, Fintype.linearIndependent_iff.1 e.linearIndependent a h1 k, map_zero])
    (TensorProduct.comm Qp V BdR y)
  refine ⟨_, b, fun k => (TensorProduct.comm Qp V BdR).symm (e k), fun k => (e k).2, ?_⟩
  apply (TensorProduct.comm Qp V BdR).injective
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, comm_mp, LinearEquiv.apply_symm_apply, hb]

end General

theorem tied_deRham_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.BdR, ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ h y
  haveI := LL.2
  exact span_of_isField (P.PD K) ρ (GlobalTheory.Per.TiedField.tied_field l P AI T).1 h y

end GlobalTheory.Per.DeRhamSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriodsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamDieudonne_spans_tensor_deRham_periods : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.BdR, ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  first | exact @GlobalTheory.Per.DeRhamSpan.tied_deRham_span | exact GlobalTheory.Per.DeRhamSpan.tied_deRham_span | (intros; apply GlobalTheory.Per.DeRhamSpan.tied_deRham_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrobIntegralCoeff

section Generic

variable {R O : Type} [CommRing R] [CommRing O] [Algebra R O] {I : Type} [Fintype I] [DecidableEq I]
  (b : Module.Basis I R O)

def regRep (W : Type) [CommRing W] [Algebra R W] : O ⊗[R] W →ₐ[R] Matrix I I W :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId R W)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom R W (Matrix I I W))
    (fun _ w => (Algebra.commutes w _).symm)

variable {W W' : Type} [CommRing W] [Algebra R W] [CommRing W'] [Algebra R W']

theorem regRep_tmul (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = Algebra.leftMulMatrix b o i j • w := by
  erw [Algebra.TensorProduct.lift_tmul]
  simp [Algebra.smul_def, Matrix.algebraMap_eq_diagonal, Matrix.mul_diagonal, mul_comm]

theorem regRep_map (f : W →ₐ[R] W') (z : O ⊗[R] W) (i j : I) :
    regRep b W' (Algebra.TensorProduct.map (AlgHom.id O O) f z) i j = f (regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, regRep_tmul, regRep_tmul, map_smul]
  | add x y hx hy => simp [map_add (f := _), Matrix.add_apply, hx, hy]

private theorem regRep_tmul' (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = b.repr (o * b j) i • w := by
  rw [regRep_tmul, Algebra.leftMulMatrix_eq_repr_mul]

theorem eq_sum_regRep (z : O ⊗[R] W) :
    z = ∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp_rw [regRep_tmul', ← TensorProduct.smul_tmul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, ← TensorProduct.sum_tmul, b.sum_repr, TensorProduct.smul_tmul',
      ← TensorProduct.sum_tmul]
    congr 1
    simp_rw [← mul_smul_comm, ← Finset.mul_sum, b.sum_repr, mul_one]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp [map_add (f := _), Matrix.add_apply, TensorProduct.tmul_add, smul_add, Finset.sum_add_distrib]

theorem mem_range_of_regRep (f : W →ₐ[R] W') (z : O ⊗[R] W')
    (h : ∀ i j, regRep b W' z i j ∈ Set.range f) :
    z ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  choose g hg using h
  refine ⟨∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] g i j), ?_⟩
  conv_rhs => rw [eq_sum_regRep b z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [TensorProduct.smul_tmul', map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hg]

def blow {p q : Type} (Z : Matrix p q (O ⊗[R] W)) : Matrix (p × I) (q × I) W :=
  Matrix.of fun x y => regRep b W (Z x.1 y.1) x.2 y.2

theorem blow_map {p q : Type} (f : W →ₐ[R] W') (Z : Matrix p q (O ⊗[R] W)) :
    blow b (Z.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) = (blow b Z).map f := by
  ext x y
  simp [blow, regRep_map]

theorem blow_add {p q : Type} (Z Z' : Matrix p q (O ⊗[R] W)) :
    blow b (Z + Z') = blow b Z + blow b Z' := by
  ext x y
  simp [blow, map_add (f := _)]

theorem blow_mul {p q r : Type} [Fintype q] (Z : Matrix p q (O ⊗[R] W))
    (Z' : Matrix q r (O ⊗[R] W)) : blow b (Z * Z') = blow b Z * blow b Z' := by
  ext x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [blow, Matrix.mul_apply, map_sum, Matrix.sum_apply, Fintype.sum_prod_type]


omit b [Fintype I] [DecidableEq I] in
theorem integrality_baseChange [Module.Free R O] [Module.Finite R O] (f : W →ₐ[R] W')
    (φ : W' →ₐ[R] W')
    (H : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q W') (S : Matrix p p W)
      (S' : Matrix q q W) (Y : Matrix p q W),
      Z.map φ = S.map f * Z * S'.map f + Y.map f → ∀ a b, Z a b ∈ Set.range f)
    (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (O ⊗[R] W')) (S : Matrix p p (O ⊗[R] W))
    (S' : Matrix q q (O ⊗[R] W)) (Y : Matrix p q (O ⊗[R] W))
    (h : Z.map (Algebra.TensorProduct.map (AlgHom.id O O) φ) =
      S.map (Algebra.TensorProduct.map (AlgHom.id O O) f) * Z *
        S'.map (Algebra.TensorProduct.map (AlgHom.id O O) f) +
      Y.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) (x : p) (y : q) :
    Z x y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R (O ⊗[R] W')
    exact ⟨0, Subsingleton.elim _ _⟩
  classical
  let c := Module.Free.chooseBasis R O
  have key := congrArg (blow c) h
  rw [blow_map, blow_add, blow_mul, blow_mul, blow_map, blow_map, blow_map] at key
  apply mem_range_of_regRep c f (Z x y)
  intro i j
  exact H _ _ (blow c Z) (blow c S) (blow c S') (blow c Y) key (x, i) (y, j)

private theorem module_free_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Free ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  have : Module.IsTorsionFree ℤ_[l] K := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  exact IsIntegralClosure.module_free ℤ_[l] ℚ_[l] K _

private theorem module_finite_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Finite ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] K _

end Generic

theorem frobenius_integrality_coeff : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (RW LL)) (S : Matrix p p (RA LL)) (S' : Matrix q q (RA LL)) (Y : Matrix p q (RA LL)), Z.map (φRW LL) = S.map (inclR LL) * Z * S'.map (inclR LL) + Y.map (inclR LL) → ∀ a b, Z a b ∈ Set.range (inclR LL) := by
  intro l _ LL p q _ _ Z S S' Y h a b
  unfold RW RA inclR φRW at *
  have := module_free_zpadic_OL l LL
  have := module_finite_zpadic_OL l LL
  exact integrality_baseChange (R := ℤ_[l]) (O := OL LL) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => GlobalTheory.T.frobeniusIntegrality_wittTilt_ainf l p q Z S S' Y h) p q Z S S' Y h a b

end GlobalTheory.FrobIntegralCoeff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficientsStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_integrality_tensor_ainf_coefficients : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (RW LL)) (S : Matrix p p (RA LL)) (S' : Matrix q q (RA LL)) (Y : Matrix p q (RA LL)), Z.map (φRW LL) = S.map (inclR LL) * Z * S'.map (inclR LL) + Y.map (inclR LL) → ∀ a b, Z a b ∈ Set.range (inclR LL) := by
  first | exact @GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff | exact GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff | (intros; apply GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc


open PowerSeries in
theorem algHom_sub_dvd {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧) (hf : (X : O⟦X⟧) ∣ f X)
    (a : O⟦X⟧) : f X - X ∣ f a - a := by
  set y := f X with hy
  let g : ℕ → O⟦X⟧ := fun n => ∑ i ∈ Finset.range n, y ^ i * X ^ (n - 1 - i)
  have hg : ∀ n, g n * (y - X) = y ^ n - X ^ n := fun n => geom_sum₂_mul y X n
  have hgd : ∀ n, (X : O⟦X⟧) ^ (n - 1) ∣ g n := by
    intro n
    refine Finset.dvd_sum fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have e : n - 1 = i + (n - 1 - i) := by omega
    conv_lhs => rw [e, pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd hf i) dvd_rfl
  let P : ℕ → O⟦X⟧ := fun N => ∑ n ∈ Finset.range N, C (coeff n a) * g n
  have hP : ∀ m k, (X : O⟦X⟧) ^ m ∣ P (m + 1 + k) - P (m + 1) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : P (m + 1 + (k + 1)) - P (m + 1)
          = (P (m + 1 + k) - P (m + 1)) + C (coeff (m + 1 + k) a) * g (m + 1 + k) := by
        simp only [P, ← add_assoc, Finset.sum_range_succ _ (m + 1 + k)]; ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_left ((pow_dvd_pow _ (by omega)).trans (hgd _)) _)
  let b : O⟦X⟧ := PowerSeries.mk fun m => coeff m (P (m + 2))
  have hb : ∀ N, (X : O⟦X⟧) ^ N ∣ P (N + 1) - b := by
    intro N
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
    have := X_pow_dvd_iff.mp (hP (m + 1) k) m (by omega)
    rw [map_sub] at this ⊢
    rw [coeff_mk, show m + k + 1 + 1 = m + 1 + 1 + k by omega]
    exact this
  have hr : ∀ N, ∃ r : O⟦X⟧, a = ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n + X ^ N * r := by
    intro N
    have : (X : O⟦X⟧) ^ N ∣ a - ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp [coeff_X_pow, hm]
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr]; ring⟩
  have hN : ∀ N, (X : O⟦X⟧) ^ N ∣ f a - a - (y - X) * P N := by
    intro N
    obtain ⟨r, hr⟩ := hr N
    have h1 : f a = ∑ n ∈ Finset.range N, C (coeff n a) * y ^ n + y ^ N * f r := by
      conv_lhs => rw [hr]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_mul, map_pow, ← hy]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      congr 1
      exact f.commutes _
    have h2 : (y - X) * P N = ∑ n ∈ Finset.range N, C (coeff n a) * y ^ n
        - ∑ n ∈ Finset.range N, C (coeff n a) * X ^ n := by
      simp only [P, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← mul_sub, ← hg]; ring
    have h3 : f a - a - (y - X) * P N = y ^ N * f r - X ^ N * r := by
      rw [h2, h1]; linear_combination -hr
    rw [h3]
    exact dvd_sub (Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hf N) _) (dvd_mul_right _ _)
  refine ⟨b, ?_⟩
  ext m
  have : (X : O⟦X⟧) ^ (m + 1) ∣ f a - a - (y - X) * b := by
    have e : f a - a - (y - X) * b
        = (f a - a - (y - X) * P (m + 1 + 1)) + (y - X) * (P (m + 1 + 1) - b) := by ring
    rw [e]
    exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hN _)) (Dvd.dvd.mul_left (hb _) _)
  have := X_pow_dvd_iff.mp this m (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.mp this

theorem geom_sum_one_add_prime {R : Type} [CommRing R] {p : ℕ} (hp : p.Prime) (x : R) :
    ∃ r, ∑ k ∈ Finset.range p, (1 + x) ^ k = x ^ (p - 1) + (p : R) * r := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (Polynomial.X : Polynomial ℤ) 1
  have h1 : (∑ k ∈ Finset.range p, (1 + Polynomial.X : Polynomial ℤ) ^ k)
      = Polynomial.X ^ (p - 1) + (p : Polynomial ℤ) * r := by
    apply mul_right_cancel₀ (Polynomial.X_ne_zero (R := ℤ))
    have h := geom_sum_mul (1 + Polynomial.X : Polynomial ℤ) p
    have e : (Polynomial.X : Polynomial ℤ) ^ p = Polynomial.X ^ (p - 1) * Polynomial.X := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
    rw [add_comm Polynomial.X, one_pow, e] at hr
    rw [hr] at h
    linear_combination h
  refine ⟨Polynomial.aeval x r, ?_⟩
  have := congrArg (Polynomial.aeval x) h1
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum] using this

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem act_X_eq (c : ℤ_[l]) : act l O c PowerSeries.X = cyc l O c := (GlobalTheory.Cyc.act_laws l O).1 c

theorem act_comm' (c c' : ℤ_[l]) (a) : act l O c (act l O c' a) = act l O c' (act l O c a) := by
  rw [(GlobalTheory.Cyc.act_laws l O).2.1, (GlobalTheory.Cyc.act_laws l O).2.1, mul_comm]

theorem act_nat_X (k : ℕ) : act l O (k : ℤ_[l]) PowerSeries.X = (1 + PowerSeries.X) ^ k - 1 := by
  rw [act_X_eq, (GlobalTheory.Cyc.act_laws l O).2.2.2.1]

theorem cyc_eq_X_mul (c : ℤ_[l]) :
    ∃ b, cyc l O c = PowerSeries.X * (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) := by
  have : (PowerSeries.X : PowerSeries O) ^ 2 ∣
      cyc l O c - PowerSeries.C (algebraMap ℤ_[l] O c) * PowerSeries.X := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [cyc_const]
    · simp [(GlobalTheory.Cyc.act_laws l O).2.2.2.2.1]
  obtain ⟨b, hb⟩ := this
  exact ⟨b, by linear_combination hb⟩

theorem XX_mul_QQ (s : ℕ) : XX l O s * QQ l O s = (1 + XX l O s) ^ l - 1 := by
  have h := geom_sum_mul (1 + XX l O s) l
  unfold QQ
  linear_combination h

theorem XX_mul_QQ' (s : ℕ) (hs : 1 ≤ s) :
    XX l O s * QQ l O s = (1 + PowerSeries.X) ^ l ^ s - 1 := by
  rw [XX_mul_QQ, XX, add_sub_cancel, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hs]

theorem phi_pow_X (n : ℕ) :
    (phi l O ^ n) PowerSeries.X = (1 + PowerSeries.X) ^ l ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgHom.mul_apply, ih]
    simp only [map_sub, map_pow, map_add (f := _), map_one, phi, act_nat_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ']

theorem act_C (c : ℤ_[l]) (x : O) : act l O c (PowerSeries.C x) = PowerSeries.C x :=
  (act l O c).commutes x

theorem act_QQ_one (c : ℤ_[l]ˣ) :
    ∃ b, act l O c (QQ l O 1) = QQ l O 1 * (1 + PowerSeries.X * b) := by
  obtain ⟨b, hb⟩ := cyc_eq_X_mul l O c
  have h1 : PowerSeries.X * QQ l O 1 = act l O (l : ℤ_[l]) PowerSeries.X := by
    have := XX_mul_QQ' l O 1 le_rfl
    rw [act_nat_X]
    simpa [XX] using this
  have h2 := act_comm' l O c l PowerSeries.X
  rw [← h1, map_mul, act_X_eq, hb] at h2
  simp only [map_mul, map_add (f := _), act_C, ← h1] at h2
  have hU : IsUnit (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using c.isUnit.map (algebraMap ℤ_[l] O)
  obtain ⟨v, hv⟩ := hU.exists_right_inv
  have h3 : (PowerSeries.C (algebraMap ℤ_[l] O c) + PowerSeries.X * b) * act l O c (QQ l O 1)
      = QQ l O 1 * (PowerSeries.C (algebraMap ℤ_[l] O c)
        + PowerSeries.X * QQ l O 1 * act l O (l : ℤ_[l]) b) := by
    apply PowerSeries.X_mul_cancel
    linear_combination h2
  refine ⟨v * (QQ l O 1 * act l O (l : ℤ_[l]) b - b), ?_⟩
  linear_combination v * h3 + (QQ l O 1 - act l O c (QQ l O 1)) * hv

theorem XX_QQ_properties : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O], ∀ s : ℕ, 1 ≤ s → phi l O (XX l O s) = XX l O s * QQ l O s ∧ (phi l O ^ (s - 1)) PowerSeries.X = XX l O s ∧ PowerSeries.constantCoeff (QQ l O s) = (l : O) ∧ (∃ b, QQ l O s = PowerSeries.X ^ (l ^ (s - 1) * (l - 1)) + (l : PowerSeries O) * b) ∧ (∃ b, QQ l O s = (l : PowerSeries O) + XX l O s * b) ∧ (∀ c : ℤ_[l]ˣ, (∃ b, act l O c (XX l O s) = XX l O s * (PowerSeries.C (algebraMap ℤ_[l] O c) + XX l O s * b)) ∧ ∃ b, act l O c (QQ l O s) = QQ l O s * (1 + XX l O s * b)) ∧ ∀ (u w : ℤ_[l]), u = 1 + (l : ℤ_[l]) ^ s * w → ∀ a, ∃ b, act l O u a - a = XX l O s * QQ l O s * b := by
  intro l _ O _ _ s hs
  have hp : l.Prime := Fact.out
  have hψ : act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) PowerSeries.X = XX l O s := act_nat_X l O _
  have hψQ : act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) (QQ l O 1) = QQ l O s := by
    have : XX l O 1 = PowerSeries.X := by simp [XX]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [QQ, this, map_sum, map_pow, map_add (f := _), map_one, hψ]
  have h0 : PowerSeries.constantCoeff (XX l O s) = 0 := by simp [XX]
  refine ⟨?_, phi_pow_X l O _, ?_, ?_, ?_, fun c => ⟨?_, ?_⟩, ?_⟩
  · rw [XX_mul_QQ' l O s hs, XX]
    simp only [map_sub, map_pow, map_add (f := _), map_one, phi, act_nat_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [QQ, map_sum, h0]
  · obtain ⟨r, hr⟩ := geom_sum_one_add_prime hp (XX l O s)
    obtain ⟨t, ht⟩ := exists_add_pow_prime_pow_eq hp (PowerSeries.X : PowerSeries O) 1 (s - 1)
    have h1 : (l : PowerSeries O) ∣ XX l O s - PowerSeries.X ^ l ^ (s - 1) :=
      ⟨PowerSeries.X * t, by rw [XX, add_comm, ht]; ring⟩
    obtain ⟨q, hq⟩ := h1.trans (sub_dvd_pow_sub_pow _ _ (l - 1))
    refine ⟨q + r, ?_⟩
    rw [QQ, hr, pow_mul]
    linear_combination hq
  · have : XX l O s ∣ QQ l O s - l := by
      have e : QQ l O s - l = ∑ k ∈ Finset.range l, ((1 + XX l O s) ^ k - 1) := by
        simp [QQ, Finset.sum_sub_distrib]
      rw [e]
      refine Finset.dvd_sum fun k _ => ?_
      simpa using sub_one_dvd_pow_sub_one (1 + XX l O s) k
    obtain ⟨b, hb⟩ := this
    exact ⟨b, by linear_combination hb⟩
  · obtain ⟨b, hb⟩ := cyc_eq_X_mul l O c
    refine ⟨act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) b, ?_⟩
    conv_lhs => rw [← hψ, act_comm', act_X_eq, hb]
    simp only [map_mul, map_add (f := _), act_C, hψ]
  · obtain ⟨b, hb⟩ := act_QQ_one l O c
    refine ⟨act l O ((l ^ (s - 1) : ℕ) : ℤ_[l]) b, ?_⟩
    conv_lhs => rw [← hψQ, act_comm', hb]
    simp only [map_mul, map_add (f := _), map_one, hψ, hψQ]
  · intro u w hu a
    have hX : PowerSeries.X ∣ act l O u PowerSeries.X := by
      rw [act_X_eq, PowerSeries.X_dvd_iff]; exact cyc_const l O u
    refine Dvd.dvd.trans ?_ (algHom_sub_dvd (act l O u) hX a)
    obtain ⟨b, hb⟩ := cyc_eq_X_mul l O w
    have h1 : cyc l O (((l ^ s : ℕ) : ℤ_[l]) * w) = XX l O s * QQ l O s *
        act l O ((l ^ s : ℕ) : ℤ_[l]) (PowerSeries.C (algebraMap ℤ_[l] O w) + PowerSeries.X * b) := by
      rw [← act_X_eq, ← (GlobalTheory.Cyc.act_laws l O).2.1, act_X_eq l O w, hb, map_mul, act_nat_X,
        XX_mul_QQ' l O s hs]
    have h2 : cyc l O u + 1 = (cyc l O ((1 : ℕ) : ℤ_[l]) + 1) * (cyc l O (((l ^ s : ℕ) : ℤ_[l]) * w) + 1) := by
      simp only [cyc, sub_add_cancel]
      rw [← map_mul, ← PowerSeries.binomialSeries_add, hu]
      push_cast
      rfl
    rw [(GlobalTheory.Cyc.act_laws l O).2.2.2.1, h1] at h2
    rw [act_X_eq]
    exact ⟨(1 + PowerSeries.X) * act l O ((l ^ s : ℕ) : ℤ_[l])
      (PowerSeries.C (algebraMap ℤ_[l] O w) + PowerSeries.X * b), by linear_combination h2⟩

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem exists_form_extending_coord {R F T V ι : Type} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup T] [Module R T] [AddCommGroup V] [Module R V]
    [Module F V] [IsScalarTower R F V] (b : Module.Basis ι R T) (f : T →ₗ[R] V)
    (hf : Function.Injective f) (i : ι) :
    ∃ φ : V →ₗ[F] F, ∀ x, φ (f x) = algebraMap R F (b.repr x i) := by
  classical
  set v : ι → V := fun j => f (b j) with hv
  have hR : LinearIndependent R v := b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hF : LinearIndependent F v := (LinearIndependent.iff_fractionRing R F).mp hR
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hF).coord i)
  refine ⟨g, fun x => ?_⟩
  have hx : f x = ∑ j ∈ (b.repr x).support, algebraMap R F (b.repr x j) • v j := by
    conv_lhs => rw [← b.linearCombination_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, algebraMap_smul]
  have hy : f x = ((∑ j ∈ (b.repr x).support,
      algebraMap R F (b.repr x j) • Module.Basis.span hF j : Submodule.span F (Set.range v)) : V) := by
    rw [hx, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Module.Basis.span_apply]
  have h2 := LinearMap.congr_fun hg
    (∑ j ∈ (b.repr x).support, algebraMap R F (b.repr x j) • Module.Basis.span hF j)
  rw [LinearMap.comp_apply, Submodule.subtype_apply] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, h2, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Finsupp.mem_support_iff, not_not] at h
    rw [h, map_zero]

theorem continuous_form_of_moduleTopology {F L V : Type} [NontriviallyNormedField F]
    [CompleteSpace F] [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] [ContinuousSMul F L] [AddCommGroup V] [Module L V]
    [Module F V] [IsScalarTower F L V] [TopologicalSpace V] [IsModuleTopology L V]
    [FiniteDimensional L V] (φ : V →ₗ[F] F) : Continuous φ := by
  let e := (Module.finBasis L V).equivFun
  have he : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  let ψ : (Fin (Module.finrank L V) → L) →ₗ[F] F := φ ∘ₗ (e.symm.toLinearMap.restrictScalars F)
  have hψ : Continuous ψ := LinearMap.continuous_of_finiteDimensional ψ
  have h : (φ : V → F) = ψ ∘ e.toLinearMap := by
    funext v
    simp [ψ]
  rw [h]
  exact hψ.comp he

variable {l : ℕ} [Fact l.Prime]

def zCHom (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* PadicComplex l :=
  (algebraMap ℚ_[l] (PadicComplex l)).comp (algebraMap ℤ_[l] ℚ_[l])

theorem zCHom_apply (x : ℤ_[l]) : zCHom l x = zC x := rfl

section Generic

variable {G R F L O : Type} [Group G] [TopologicalSpace G] [CommRing R] [Field F] [Field L]
  [Algebra F L] [CommRing O] [Algebra O L] [TopologicalSpace L] [Algebra R O]

def mulLat (R : Type) [CommRing R] [Algebra R O] (T : LocLat G F L O) (a : O) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ↥T.L.T →ₗ[R] ↥T.L.T :=
  letI := Module.compHom ↥T.L.T (algebraMap R O)
  { toFun := fun x => ⟨_, T.L.T.smul_mem a x.2⟩
    map_add' := fun x y => smul_add a x y
    map_smul' := fun c x => smul_comm a (algebraMap R O c) x }

theorem mulLat_apply (T : LocLat G F L O) (a : O) (x : ↥T.L.T) :
    mulLat R T a x = ⟨_, T.L.T.smul_mem a x.2⟩ := rfl

theorem coe_actT (T : LocLat G F L O) (g : G) (x : ↥T.L.T) :
    (actT T.L g x).1 = T.ρ g x.1 := rfl

theorem actT_mulLat (T : LocLat G F L O) (g : G) (a : O) (x : ↥T.L.T) :
    actT T.L g (mulLat R T a x) = mulLat R T a (actT T.L g x) := by
  rw [mulLat_apply, mulLat_apply]
  exact (actT T.L g).map_smul a x

theorem exists_basis_lat [Nontrivial R] [Module.Free R O] [Module.Finite R O]
    (T : LocLat G F L O) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) R ↥T.L.T) := by
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  have : IsScalarTower R O ↥T.L.T := ⟨fun r o x => by
    show (r • o) • x = algebraMap R O r • (o • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  have : Module.Free R ↥T.L.T :=
    Module.Free.of_basis ((Module.Free.chooseBasis R O).smulTower (Module.Free.chooseBasis O ↥T.L.T))
  have : Module.Finite R ↥T.L.T := Module.Finite.trans O ↥T.L.T
  exact ⟨_, ⟨Module.finBasis R ↥T.L.T⟩⟩

theorem exists_form_lat [IsDomain R] [Algebra R F] [IsFractionRing R F]
    (hc : ∀ c : R, algebraMap O L (algebraMap R O c) = algebraMap F L (algebraMap R F c))
    (T : LocLat G F L O) {ι : Type} :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ (b : Module.Basis ι R ↥T.L.T) (i : ι),
      ∃ φ : T.V →ₗ[F] F, ∀ x : ↥T.L.T, φ x.1 = algebraMap R F (b.repr x i) := by
  intro b i
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  let _ : Module R T.V := Module.compHom T.V (algebraMap R F)
  have : IsScalarTower R F T.V := ⟨fun r c v => by
    show (r • c) • v = algebraMap R F r • (c • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let f : ↥T.L.T →ₗ[R] T.V :=
    { toFun := fun x => x.1
      map_add' := fun x y => rfl
      map_smul' := fun r x => by
        show algebraMap R O r • x.1 = algebraMap R F r • x.1
        rw [← algebraMap_smul L (algebraMap R O r) x.1, hc, algebraMap_smul] }
  exact exists_form_extending_coord b f Subtype.val_injective i

def actLat (R : Type) [CommRing R] [Algebra R O] (T : LocLat G F L O) (g : G) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ↥T.L.T →ₗ[R] ↥T.L.T :=
  letI := Module.compHom ↥T.L.T (algebraMap R O)
  { toFun := actT T.L g
    map_add' := map_add _
    map_smul' := fun c x => (actT T.L g).map_smul (algebraMap R O c) x }

theorem matrices_lat {C : Type} [CommRing C] (z : R →+* C) (T : LocLat G F L O) {d : ℕ}
    (M : G → Matrix (Fin d) (Fin d) C) (A : O → Matrix (Fin d) (Fin d) C) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ b : Module.Basis (Fin d) R ↥T.L.T,
      (∀ g i j, M g i j = z (b.repr (actT T.L g (b j)) i)) →
      (∀ a i j, A a i j = z (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i)) →
      (∀ g h, M (g * h) = M g * M h) ∧ M 1 = 1 ∧ ∀ g a, M g * A a = A a * M g := by
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  intro b hM hA
  have kM : ∀ g, M g = (LinearMap.toMatrix b b (actLat R T g)).map z := by
    intro g; ext i j; rw [hM, Matrix.map_apply, LinearMap.toMatrix_apply]; rfl
  have kA : ∀ a, A a = (LinearMap.toMatrix b b (mulLat R T a)).map z := by
    intro a; ext i j; rw [hA, Matrix.map_apply, LinearMap.toMatrix_apply]; rfl
  have hmul : ∀ g h, actLat R T (g * h) = actLat R T g * actLat R T h := by
    intro g h
    refine LinearMap.ext fun x => Subtype.ext ?_
    show T.ρ (g * h) x.1 = T.ρ g (T.ρ h x.1)
    rw [map_mul]; rfl
  have hone : actLat R T 1 = 1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show T.ρ 1 x.1 = x.1
    rw [map_one]; rfl
  have hcomm : ∀ g a, actLat R T g * mulLat R T a = mulLat R T a * actLat R T g :=
    fun g a => LinearMap.ext fun x => actT_mulLat (R := R) T g a x
  refine ⟨fun g h => ?_, ?_, fun g a => ?_⟩
  · rw [kM, kM, kM, hmul, LinearMap.toMatrix_mul, Matrix.map_mul]
  · rw [kM, hone, LinearMap.toMatrix_one]
    exact Matrix.map_one _ z.map_zero z.map_one
  · rw [kM, kA, ← Matrix.map_mul, ← Matrix.map_mul, ← LinearMap.toMatrix_mul,
      ← LinearMap.toMatrix_mul, hcomm]

end Generic

theorem continuous_coord_lat {G R F L O : Type} [Group G] [TopologicalSpace G] [CommRing R]
    [NontriviallyNormedField F] [CompleteSpace F] [Field L] [Algebra F L] [CommRing O]
    [Algebra O L] [TopologicalSpace L] [Algebra R O] [FiniteDimensional F L]
    [IsTopologicalRing L] [T2Space L] [ContinuousSMul F L]
    [IsDomain R] [Algebra R F] [IsFractionRing R F]
    (hc : ∀ c : R, algebraMap O L (algebraMap R O c) = algebraMap F L (algebraMap R F c))
    (T : LocLat G F L O) {ι : Type} :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ (b : Module.Basis ι R ↥T.L.T) (x : ↥T.L.T) (i : ι),
      Continuous fun g : G => algebraMap R F (b.repr (actT T.L g x) i) := by
  intro b x i
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  obtain ⟨φ, hφ⟩ := exists_form_lat (R := R) hc T b i
  have hφc : Continuous φ := continuous_form_of_moduleTopology (L := L) φ
  have h : (fun g : G => algebraMap R F (b.repr (actT T.L g x) i)) = fun g => φ (T.ρ g x.1) := by
    funext g
    rw [← hφ, coe_actT]
  rw [h]
  exact hφc.comp (T.cont x.1)

theorem exists_basis_lattice {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlMod LL T
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) ℤ_[l] ↥T.L.T) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  have : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] (↥LL.1) (↥(OL LL))
  have : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] _
  have : Module.Free ℤ_[l] ↥(OL LL) :=
    IsIntegralClosure.module_free ℤ_[l] ℚ_[l] (↥LL.1) (↥(OL LL))
  exact exists_basis_lat (R := ℤ_[l]) T

theorem isMat_exists_and_props : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∃ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A) ∧ ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → (∀ i j, ContinuousOn (fun σ => M σ i j) (GK K)) ∧ (∀ σ ∈ GK K, ∀ τ ∈ GK K, M (σ * τ) = M σ * M τ) ∧ M 1 = 1 ∧ (∀ σ ∈ GK K, ∀ a, M σ * A a = A a * M σ) := by
  intro l _ K LL T
  classical
  let _ : Module ℤ_[l] ↥T.L.T := zlMod LL T
  have hc : ∀ c : ℤ_[l], algebraMap (↥(OL LL)) (↥LL.1) (algebraMap ℤ_[l] (↥(OL LL)) c) =
      algebraMap ℚ_[l] (↥LL.1) (algebraMap ℤ_[l] ℚ_[l] c) := fun c => rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨d, ⟨b⟩⟩ := exists_basis_lattice (G := ↥(GK K)) LL T
    refine ⟨d, fun σ => Matrix.of fun i j =>
        if h : σ ∈ GK K then zC (b.repr (actT T.L ⟨σ, h⟩ (b j)) i) else 0,
      fun a => Matrix.of fun i j => zC (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i),
      b, fun g i j => ?_, fun a i j => rfl⟩
    show (if h : (g : GQ l) ∈ GK K then zC (b.repr (actT T.L ⟨g, h⟩ (b j)) i) else 0) = _
    exact dif_pos g.2
  · intro d M A hMA
    obtain ⟨b, hM, hA⟩ := hMA
    have key := matrices_lat (R := ℤ_[l]) (F := ℚ_[l]) (L := ↥LL.1) (zCHom l) T
      (fun g : ↥(GK K) => M g) A b (fun g i j => (hM g i j).trans (zCHom_apply _).symm)
      (fun a i j => (hA a i j).trans (zCHom_apply _).symm)
    refine ⟨fun i j => ?_, fun σ hσ τ hτ => key.1 ⟨σ, hσ⟩ ⟨τ, hτ⟩, key.2.1,
      fun σ hσ a => key.2.2 ⟨σ, hσ⟩ a⟩
    rw [continuousOn_iff_continuous_domRestrict]
    have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have h1 := continuous_coord_lat (R := ℤ_[l]) (F := ℚ_[l]) (L := ↥LL.1) (O := ↥(OL LL)) hc T b
      (b j) i
    have h2 : Continuous (algebraMap ℚ_[l] (PadicComplex l)) := continuous_algebraMap _ _
    refine (h2.comp h1).congr fun g => ?_
    exact ((hM ⟨g.1, g.2⟩ i j).trans (zCHom_apply _).symm).symm

end GlobalTheory.Cyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegralStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∃ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A) ∧ ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → (∀ i j, ContinuousOn (fun σ => M σ i j) (GK K)) ∧ (∀ σ ∈ GK K, ∀ τ ∈ GK K, M (σ * τ) = M σ * M τ) ∧ M 1 = 1 ∧ (∀ σ ∈ GK K, ∀ a, M σ * A a = A a * M σ) := by
  first | exact @GlobalTheory.Cyc.isMat_exists_and_props | exact GlobalTheory.Cyc.isMat_exists_and_props | (intros; apply GlobalTheory.Cyc.isMat_exists_and_props <;> assumption)
end
end
