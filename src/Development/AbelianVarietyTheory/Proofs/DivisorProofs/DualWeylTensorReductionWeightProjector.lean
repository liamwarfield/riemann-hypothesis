module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjector
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem wComp_monomial_eq_ite {σ R M : Type} [CommSemiring R] [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (d : σ →₀ ℕ) (c : R) :
    weightedHomogeneousComponent w n (monomial d c) = if Finsupp.weight w d = n then monomial d c else 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_monomial]
  by_cases h : Finsupp.weight w d = n <;> by_cases hd : d = m
  · subst hd; simp [h]
  · simp [h, hd, coeff_monomial]
  · subst hd; simp [h]
  · simp [h, hd]

theorem wComp_mul_of_weight_zero {σ R M : Type} [CommSemiring R] [AddCommMonoid M] (w : σ → M) (n : M) (P Q : MvPolynomial σ R)
    (hQ : IsWeightedHomogeneous w Q 0) :
    weightedHomogeneousComponent w n (P * Q) = weightedHomogeneousComponent w n P * Q := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : AddMonoidAlgebra.coeff Q x.2 = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 = n := by rw [← h, ← hm, map_add (f := _), h2, add_zero]
      rw [if_pos e]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : AddMonoidAlgebra.coeff Q x.2 = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 ≠ n := by rw [← hm, map_add (f := _), h2, add_zero] at h; exact h
      rw [if_neg e, zero_mul]

theorem blockRed_eq_rename_map (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ f = rename (fun v => ((τ, v) : BVar N ι)) (map (Ideal.Quotient.mk (Ideal.span {ϖ})) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp => rw [map_mul, hp]; simp [blockRed]

theorem weight_blockW_mapDomain_self (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((τ, v) : BVar N ι)) d) = Finsupp.weight (rowW N N) d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, rowW]

theorem weight_blockW_mapDomain_of_ne (N : ℕ) {ι : Type} [DecidableEq ι] {τ σ : ι} (h : σ ≠ τ) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((σ, v) : BVar N ι)) d) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, h]

end GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_wComp_rowW (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) (τ : ι) (v : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v f) =
      weightedHomogeneousComponent (blockW N τ) v (blockRed O N ϖ τ f) := by
  classical
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [weightedHomogeneousComponent_apply, map_sum, map_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [blockRed_eq_rename_map, map_monomial, rename_monomial]
  rw [wComp_monomial_eq_ite, weight_blockW_mapDomain_self]

theorem blockRed_isWeightedHomogeneous_zero (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) {τ σ : ι} (h : σ ≠ τ)
    (f : MvPolynomial (Fin N × Fin N) O) : IsWeightedHomogeneous (blockW N τ) (blockRed O N ϖ σ f) 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [blockRed_eq_rename_map, f.as_sum, map_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [mem_weightedHomogeneousSubmodule, map_monomial, rename_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_blockW_mapDomain_of_ne N h d)

theorem redT_tprod_prod_blockRed (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O)
    (x : ∀ τ, dualWeyl O N N (res N (mu τ))) :
    redT O N mu ϖ (PiTensorProduct.tprod O x) = ∏ σ, blockRed O N ϖ σ (x σ) := by
  simp [redT]

theorem redT_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N mu)), IsProj O N mu τ v a → ∀ y : NablaT O N mu, redT O N mu ϖ (a y) = weightedHomogeneousComponent (blockW N τ) v (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ τ v a ha y
  have key : (redT O N mu ϖ).comp a =
      ((weightedHomogeneousComponent (blockW N τ) v).restrictScalars O).comp (redT O N mu ϖ) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    let yy : dualWeyl O N N (res N (mu τ)) := rowProj O N (res N (mu τ)) v (x τ)
    have hQ : IsWeightedHomogeneous (blockW N τ) (∏ σ ∈ ({τ}ᶜ : Finset ι), blockRed O N ϖ σ (x σ)) 0 := by
      have := IsWeightedHomogeneous.prod ({τ}ᶜ : Finset ι) (fun σ => blockRed O N ϖ σ (x σ)) (fun _ => (0 : Fin N → ℕ))
        (fun σ hσ => blockRed_isWeightedHomogeneous_zero O N ϖ (by simpa using hσ) (x σ))
      simpa using this
    rw [ha x yy rfl, redT_tprod_prod_blockRed, redT_tprod_prod_blockRed, Fintype.prod_eq_mul_prod_compl τ, Fintype.prod_eq_mul_prod_compl τ,
      Function.update_self, wComp_mul_of_weight_zero _ _ _ _ hQ]
    congr 1
    · show blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v (x τ : MvPolynomial (Fin N × Fin N) O)) = _
      exact blockRed_wComp_rowW O N ϖ τ v _
    · refine Finset.prod_congr rfl fun σ hσ => ?_
      rw [Function.update_of_ne (by simpa using hσ)]
  exact LinearMap.congr_fun key y

end GlobalTheory.HighWtEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjectorStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylTensorReduction_weightProjector : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N mu)), IsProj O N mu τ v a → ∀ y : NablaT O N mu, redT O N mu ϖ (a y) = weightedHomogeneousComponent (blockW N τ) v (redT O N mu ϖ y) := by
  first | exact @GlobalTheory.HighWtEmb.redT_isProj | exact GlobalTheory.HighWtEmb.redT_isProj | (intros; apply GlobalTheory.HighWtEmb.redT_isProj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorLiftEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorLiftEquivariant
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead.LiftEquiv

theorem map_rowAct_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R M f) = rowAct S (M.map φ) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, hp, map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [rowAct, map_sum, Matrix.map_apply]

theorem rowAct_detPol_eq {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    rowAct R M (detPol R n) = MvPolynomial.C M.det * detPol R n := by
  unfold detPol
  rw [AlgHom.map_det, RingHom.map_det (MvPolynomial.C : R →+* MvPolynomial (Fin n × Fin n) R), ← Matrix.det_mul]
  congr 1
  ext1 a s
  simp [rowAct, Matrix.mul_apply]

theorem rowAct_liftPol_eq {K C : Type} [CommRing K] [CommRing C] {n : ℕ} (e0 : K →+* C) (k : ℕ)
    (M : Matrix (Fin n) (Fin n) K) (f : MvPolynomial (Fin n × Fin n) K) :
    rowAct C (M.map e0) (liftPol e0 k f) = (e0 M.det) ^ k • liftPol e0 k (rowAct K M f) := by
  unfold liftPol
  have hd : (M.map e0).det = e0 M.det := (RingHom.map_det e0 M).symm
  rw [map_mul, map_pow, rowAct_detPol_eq, map_rowAct_eq, mul_pow, smul_eq_C_mul, map_pow, mul_assoc, hd]

theorem grp_tprod_eq (C : Type) [CommRing C] {ι : Type} (n : ℕ) (lamW : ι → ℕ → ℕ) (g : ι → GL (Fin n) C)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    grp C n lamW g (PiTensorProduct.tprod C y) =
      PiTensorProduct.tprod C (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (g τ) (y τ)) :=
  PiTensorProduct.map_tprod _ _

theorem scalar_eq {K C : Type} [Field K] [Field C] (e0 : K →+* C) {n : ℕ} (lam : DomWeight n) (k : ℕ) (c : ℤ)
    (h : ∀ hn : 0 < n, (k : ℤ) = lam.w ⟨n - 1, by omega⟩ + c) (g : GL (Fin n) K) :
    e0 (detPow K n (inside₂ K n g) lam.detShift) =
      ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map e0 g) ^ c : Cˣ) : C) *
        e0 ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ k := by
  have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have h2 : ((inside₂ K n g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = ((g : Matrix (Fin n) (Fin n) K).det)⁻¹ := by
    rw [← h1]; exact Matrix.det_transpose _
  have h3 : ((Matrix.GeneralLinearGroup.map e0 g : GL (Fin n) C) : Matrix (Fin n) (Fin n) C).det =
      e0 (g : Matrix (Fin n) (Fin n) K).det := (RingHom.map_det e0 _).symm
  have h0 : e0 (g : Matrix (Fin n) (Fin n) K).det ≠ 0 := by
    rw [map_ne_zero]; exact g.det_ne_zero
  simp only [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, h1, h2, h3, map_zpow₀, map_inv₀]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have he : lam.detShift = k - c := by
      rw [h hn]; simp [DomWeight.detShift, hn]
    rw [he, inv_zpow', inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ h0]
    congr 1
    ring

theorem phi_equivariant : ∀ (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW), Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ (g : ι → GL (Fin n) K) (v : VV K lam), Φ (rhoK lam (invTrK g) v) = lamG C n lamW c (fun τ => Matrix.GeneralLinearGroup.map e0 (g τ)) (Φ v) := by
  intro K C _ _ e0 ι _ _ n lam lamW c Φ hS hΦ g v
  obtain ⟨v, hv⟩ := v
  induction hv using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨x, hx, rfl⟩ := hP
    let M : ι → Matrix (Fin n) (Fin n) K := fun τ => ((g τ)⁻¹ : GL (Fin n) K)
    have hx' : ∀ τ, rowAct K (M τ) (x τ) ∈ nablaSq K n (lam τ) := fun τ =>
      Formalism.GradedWeylDivisibility.dualWeylRowStable K n n _ _ _ (hx τ)
    let w : VV K lam := ⟨Formalism.L2.DIV.ten fun τ => rowAct K (M τ) (x τ),
      Submodule.subset_span ⟨_, hx', rfl⟩⟩
    obtain ⟨y, hy, hyv⟩ := hΦ x ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ hx rfl
    obtain ⟨y', hy', hyw⟩ := hΦ _ w hx' rfl
    have hr : rhoK lam (invTrK g) ⟨_, Submodule.subset_span ⟨x, hx, rfl⟩⟩ = detTwK lam (invTrK g) • w := by
      apply Subtype.ext
      show detTwK lam (invTrK g) • trAct (invTrK g) (∏ τ, blockEmb K τ (x τ)) =
        detTwK lam (invTrK g) • ∏ τ, blockEmb K τ (rowAct K (M τ) (x τ))
      congr 1
      rw [map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1 τ (x τ)
    have hg : (fun τ => Formalism.UG.dualWeylRep C n n (res n (lamW τ)) (Matrix.GeneralLinearGroup.map e0 (g τ)) (y τ)) =
        fun τ => (e0 (M τ).det) ^ (lamW τ (n - 1)) • y' τ := by
      funext τ
      apply Subtype.ext
      show rowAct C (((Matrix.GeneralLinearGroup.map e0 (g τ))⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) (y τ) =
        (e0 (M τ).det) ^ (lamW τ (n - 1)) • (y' τ : MvPolynomial (Fin n × Fin n) C)
      rw [hy, hy', ← map_inv]
      exact rowAct_liftPol_eq e0 _ (M τ) (x τ)
    rw [hr, LinearMap.map_smulₛₗ, hyw, hyv, lamG_apply, grp_tprod_eq, hg, MultilinearMap.map_smul_univ, smul_smul]
    congr 1
    rw [detTwK, map_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact scalar_eq e0 (lam τ) _ (c τ) (fun hn => hS τ ⟨n - 1, by omega⟩) (g τ)
  | zero =>
    show Φ (rhoK lam (invTrK g) 0) = lamG C n lamW c _ (Φ 0)
    simp only [map_zero]
  | add a b ha hb iha ihb =>
    show Φ (rhoK lam (invTrK g) (⟨a, ha⟩ + ⟨b, hb⟩)) = lamG C n lamW c _ (Φ (⟨a, ha⟩ + ⟨b, hb⟩))
    simp only [map_add (f := _)]
    rw [iha, ihb]
  | smul r a ha iha =>
    show Φ (rhoK lam (invTrK g) (r • ⟨a, ha⟩)) = lamG C n lamW c _ (Φ (r • ⟨a, ha⟩))
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, iha]

end GlobalTheory.FrameRead.LiftEquiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorLiftEquivariantStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylTensorLift_equivariant : ∀ (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW), Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ (g : ι → GL (Fin n) K) (v : VV K lam), Φ (rhoK lam (invTrK g) v) = lamG C n lamW c (fun τ => Matrix.GeneralLinearGroup.map e0 (g τ)) (Φ v) := by
  first | exact @GlobalTheory.FrameRead.LiftEquiv.phi_equivariant | exact GlobalTheory.FrameRead.LiftEquiv.phi_equivariant | (intros; apply GlobalTheory.FrameRead.LiftEquiv.phi_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.GtVec

open ReciprocityTheory.ChartRestriction.G.DVR

section Local

variable {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} {M : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_cpt (hM : M.IsLB) {φ : K → (Sp S ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp S ⟶ X)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {t : LB.Gen (LB.LinComb M φ ε)} {t' : LB.Gen (LB.LinComb M φ' ε')} (ht : t.IsGen)
    (ht' : t'.IsGen) {J} (hJ : Good M (cpt S) J) (e : val t (𝟙 _) (cpt S) J = val t' (𝟙 _) (cpt S) J) :
    LB.Gen.Corr M _ _ _ _ t t' := by
  obtain ⟨u, hu, vu⟩ := exists_gen hM hF t' ht'
  obtain ⟨ρ, hρ⟩ := Geo.Tor.exists_ratio hM rfl t u ht hu
  have h1 : Geo.Tor.gm (𝟙 (Sp S)) (cpt S) ⊤ ρ = 1 :=
    mul_eq_right.1 ((hρ _ _ _ J hJ).symm.trans (e.trans (vu _ _ _ J hJ).symm))
  have h2 : ρ = 1 := by
    apply Units.ext
    obtain ⟨a, ha⟩ := (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.surjective ρ.val
    have h3 : toStkA (cpt S) a = toStkA (cpt S) 1 := by
      rw [map_one]
      refine Eq.trans ?_ (congrArg Units.val h1)
      rw [gm_val (𝟙 (Sp S)) (cpt S) ⊤ trivial, ← ha]
      rfl
    rw [← ha, toStkA_injective h3, map_one]; rfl
  refine corr_of_val hM fun y I hI => (hρ _ _ y I hI).trans ?_
  rw [h2, map_one, _root_.one_mul]
  exact vu _ _ y I hI

theorem exists_gen_cpt (hM : M.IsLB) (φ : K → (Sp S ⟶ X)) (ε : K → ℤ) {J} (hJ : Good M (cpt S) J)
    (u : ((Sp S).presheaf.stalk (cpt S))ˣ) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ val t (𝟙 _) (cpt S) J = u := by
  have all : ∀ w : Sp S, w ∈ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) := fun w =>
    (top_le_iff_cpt (𝟙 (Sp S)) _).2 (hJ.mem φ (𝟙 _)) trivial
  have le : ∀ j, LB.wchart M φ j ≤ LB.wchart M φ j ⊓ LB.wchart M φ fun k => J (𝟙 _ ≫ φ k) :=
    fun j w hw => ⟨hw, all w⟩
  obtain ⟨c, hc⟩ : ∃ c : Γ(Sp S, ⊤)ˣ, Geo.Tor.gm (𝟙 (Sp S)) (cpt S) ⊤ c = u := by
    obtain ⟨U, hU, a, ha⟩ := (Sp S).presheaf.exists_germ_eq u.val
    obtain rfl : U = ⊤ := top_le_iff.1 ((top_le_iff_cpt (𝟙 (Sp S)) U).2 hU)
    have hb : (Sp S).basicOpen a = ⊤ := top_le_iff.1 ((top_le_iff_cpt (𝟙 (Sp S)) _).2
      (((Sp S).mem_basicOpen a _ hU).2 (ha ▸ u.isUnit)))
    have ha' : IsUnit a := (Sp S).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
      ((Sp S).mem_basicOpen a y hy).1 (hb.ge trivial)
    exact ⟨ha'.unit, Units.ext ((gm_val (𝟙 _) _ ⊤ trivial _).trans ha)⟩
  let t : LB.Gen (LB.LinComb M φ ε) :=
    ⟨fun j => res (le j) ((LB.LinComb M φ ε).g j fun k => J (𝟙 _ ≫ φ k)) * res le_top c⟩
  have v : ∀ (w : Sp S) j, w ∈ LB.wchart M φ j → Geo.Tor.gm (𝟙 (Sp S)) w (LB.wchart M φ j) (t.s j) =
      trF φ ε (𝟙 _) w j (fun k => J (𝟙 _ ≫ φ k)) * Geo.Tor.gm (𝟙 (Sp S)) w ⊤ c := fun w j h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ w (le j) h _).trans (gm_linComb M _ ε (𝟙 _) w j _ h (all w)))
      (gm_res _ w le_top h c))
  refine ⟨t, isGen_of_gm _ fun w j j' h h' => ?_, (v _ _ (all _)).trans ?_⟩
  · refine (v w j h).trans (Eq.trans ?_ (congrArg _ (v w j' h')).symm)
    rw [← trF_trans hM _ ε (𝟙 _) w h h' (all w), _root_.mul_assoc]
  · rw [mul_eq_left.1 (trF_trans hM φ ε (𝟙 _) _ (all _) (all _) (all _)), _root_.one_mul, hc]

end Local

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

open GlobalTheory.TorusModel

theorem exists_over {S : Type} [CommRing S] [IsLocalRing S] (f : Sp S ⟶ Sp R) (b : Over.mk f ⟶ D.P.A) :
    ∃ g : GtPt D (Over.mk f), g.b = b := by
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB (cpt S)
  have C : IsCub (th D (T := Over.mk f) (cpt S) J) := isCub_cubV D.cub hJ
  obtain ⟨v, m₀, m⟩ := exists_mult C (c := cP D (Over.mk f)) (cPoint_add D _) b
  choose s hs hv using fun χ => exists_gen_cpt D.P.isLB (DegPre.gtφT D (Over.mk f) b χ) DegPre.gtε hJ (v χ)
  refine ⟨⟨b, s, hs, corr_cpt D.P.isLB (fun U _ h => Eq.symm ?_) (hs 0) (fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm) hJ
      ((hv 0).trans (m₀.trans (val_one _).symm)),
    fun χ χ' => corr_cpt D.P.isLB (fun U _ h => Eq.symm ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (pullGen_isGen _ _ _ _ D.cub.isGen _))
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) hJ
      (((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (val_cubAtT (T := Over.mk f) hJ _ _ _))).trans
        ((m χ χ').trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _) (hv _))).symm))⟩, rfl⟩
  · refine (prod_pt b 0 h).trans ?_
    rw [cPoint_zero, _root_.one_mul]; simp
  · refine (prod_sum₂ (K := Fin 4) (K' := thK.{0}) (U := U) _ (prod_pt b _ h)
      (prod_cub (cP D _ χ) (cP D _ χ') b h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_pt b χ h) (prod_pt b χ' h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem isZero_of_isAdd {T : Over (Sp R)} {g : GtPt D T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := mul_eq_left.1 hb.symm
  refine ⟨hb1, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e := hv χ y J hJ
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  rw [hb1, C.face₃, _root_.mul_one] at e
  exact (mul_eq_left.1 e.symm).trans (val_one _).symm

theorem isZero_unique {T : Over (Sp R)} {g g' : GtPt D T} (h : g.IsZero) (h' : g'.IsZero) : g = g' :=
  pt_ext (h.1.trans h'.1.symm) fun χ _ _ hJ => (val_corr hJ (h.2 χ) _).trans (val_corr hJ (h'.2 χ) _).symm

omit [IsDomain R] in
theorem red_comp : redE R ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), (∀ b : epsR R ⟶ D.P.A, IsTangent b → ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = b) ∧ (∀ gm gm' : GtPt D (epsR R), ∃ gm'', GtPt.IsAdd gm gm' gm'' ∧ (GtTan gm → GtTan gm' → GtTan gm'')) ∧ (∀ (T T' : Over (Sp R)) (h : T' ⟶ T) (gm : GtPt D T), ∃ gm' : GtPt D T', GtPt.IsPull h.left gm gm') ∧ ∀ gm gm' : GtPt D (epsR R), gm.b = gm'.b → (∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (gm.s χ) (gm'.s χ)) → gm = gm' := by
  intro R _ _ _ D
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  obtain ⟨G, _, _, hH⟩ := exists_isGt hG (splitExt D)
  obtain ⟨Φ, hp, ha⟩ := exists_points hG hH
  have hz : ∀ T, (Φ T 1).IsZero := fun T => isZero_of_isAdd (by simpa using ha T 1 1)
  let r : baseOver (Sp R) ⟶ epsR R := Over.homMk (redE R) red_comp
  let a : epsR R ⟶ baseOver (Sp R) := Over.homMk (spMap (algebraMap R (DualNumber R))) (Category.comp_id _)
  have hra : r ≫ a = 𝟙 _ := Over.OverMorphism.ext red_comp
  have tan : ∀ x : epsR R ⟶ G, GtTan (Φ _ x) ↔ r ≫ x = 1 := fun x =>
    ⟨fun ⟨o, ho, h⟩ => (Φ _).injective ((isPull_unique (hp _ _ r x) h).trans (isZero_unique ho (hz _))),
      fun h => ⟨Φ _ 1, hz _, h ▸ hp _ _ r x⟩⟩
  refine ⟨fun b hb => ?_, fun g g' => ?_, fun T T' h g => ?_, fun g g' hb hs =>
    pt_ext hb fun χ _ _ hJ => val_corr hJ (hs χ) _⟩
  · have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
      simpa only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one] using
        IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
    obtain ⟨g, hg⟩ := exists_over (D := D) _ b
    obtain ⟨x, rfl⟩ := (Φ (epsR R)).surjective g
    refine ⟨Φ _ (((a ≫ r) ≫ x)⁻¹ * x), (tan _).2 ?_, ?_⟩
    · rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, hra, Category.id_comp,
        inv_mul_cancel]
    · have h₁ := ((TorusModel.isAdd_iff _ _ _).1 (ha _ ((a ≫ r) ≫ x) (((a ≫ r) ≫ x)⁻¹ * x))).1
      have h₂ := ((TorusModel.isPull_iff _ _ _).1 (hp _ _ (a ≫ r) x)).1
      have h₃ : r ≫ b = 1 := Over.OverMorphism.ext (hb.trans (Category.id_comp _).symm)
      rw [mul_inv_cancel_left, h₂, hg, Category.assoc, h₃, MonObj.comp_one, _root_.one_mul] at h₁
      exact h₁.symm
  · obtain ⟨x, rfl⟩ := (Φ (epsR R)).surjective g
    obtain ⟨x', rfl⟩ := (Φ (epsR R)).surjective g'
    refine ⟨_, ha _ x x', fun h h' => (tan _).2 ?_⟩
    rw [MonObj.comp_mul, (tan _).1 h, (tan _).1 h', _root_.mul_one]
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    exact ⟨_, hp _ _ h x⟩

end GlobalTheory.MBLow.GtVec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilOperatorDiagonalIntegralHeisenbergPoi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilOperatorDiagonalIntegralHeisenbergPoi
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.InertLagChar

theorem at_mul_left' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {a b c : Type} [Fintype b] (P : Matrix a b (AE F E)) {z : Matrix b c (AE F E)} (hz : At (evFin F v) z) :
    At (evFin F v) (P * z) := fun u hu => by rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem at_mul_right' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {a b c : Type} [Fintype b] {z : Matrix a b (AE F E)} (hz : At (evFin F v) z) (P : Matrix b c (AE F E)) :
    At (evFin F v) (z * P) := fun u hu => by rw [← Matrix.smul_mul, hz u hu, Matrix.zero_mul]

theorem at_fromCols_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {a b c : Type} {u : Matrix a b (AE F E)} (hu : At (evFin F v) u) :
    At (evFin F v) (Matrix.fromCols uᵀ (0 : Matrix b c (AE F E))) := fun t ht => by
  ext i j
  rcases j with j | j
  · have := congrArg (fun M => M j i) (hu t ht)
    simpa using this
  · simp

theorem fromCols_add_fromCols {R : Type} [Add R] {a b c : Type} (x z : Matrix a b R) (y w : Matrix a c R) :
    Matrix.fromCols x y + Matrix.fromCols z w = Matrix.fromCols (x + z) (y + w) := by
  ext i j; rcases j with j | j <;> rfl

theorem fromCols_mul_transpose_split {R : Type} [CommRing R] {a b : Type} [Fintype a] (u : Matrix a b R)
    (P : Matrix (a ⊕ a) (a ⊕ a) R) :
    Matrix.fromCols uᵀ (0 : Matrix b a R) * Pᵀ =
      Matrix.fromCols (P.toBlocks₂₁ * u)ᵀ (P.toBlocks₂₁ * u)ᵀ + Matrix.fromCols ((P.toBlocks₁₁ - P.toBlocks₂₁) * u)ᵀ 0 := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
  rw [fromCols_add_fromCols]
  simp only [Matrix.zero_mul, add_zero, Matrix.transpose_mul, Matrix.transpose_sub, Matrix.mul_sub]
  congr 1
  abel

theorem diagW_omd_point : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    ∀ d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' dd →
    ∀ omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
    IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    ∀ l : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ z : Matrix (Fin d) (Fin n) (AE F E), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l (dd.rho ψ (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) Φ) = l Φ) →
    ∀ r₀ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ,
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), Rest (evFin F v) φ r₀) →
    ∀ c₀ : ℂ, c₀ ≠ 0 → ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) →
    ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) (ρ₀ : ℂ),
    (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l (omd p Φ) = ρ₀ * l Φ) →
    ∀ Φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), ∀ Φ₁ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
    Acts (evFin F v) (omd p) Φ Φ₁ → ∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z →
      diagW (psiAt ψ v) μ Φ₁ (locCo M.co v (z * Cᵀ)) = ρ₀ * diagW (psiAt ψ v) μ Φ (locCo M.co v
        (((((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).toBlocks₂₁) * z) * Cᵀ)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ v m C hL d' hd' dd hdd omd hsp l hlinv r₀ hr₀ c₀ hc₀ μ hlint p ρ₀ hρ Φ hΦ Φ₁ hΦ₁ hacts z hz

  have hstep : ∀ γ, At (evFin F v) γ → ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      dd.rho ψ γ (tens (evFin F v) φ r₀) = tens (evFin F v) (schr (psiAt ψ v) (locCo dd v γ) φ) r₀ :=
    fun γ hγ φ hφ => GlobalTheory.VacBridge.rho_acts_locCo dd ψ v γ hγ φ r₀ (hr₀ φ hφ)
  have hmem : ∀ γ, At (evFin F v) γ → ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      dd.rho ψ γ (tens (evFin F v) φ r₀) ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := fun γ hγ φ hφ => by
    rw [hstep γ hγ φ hφ]
    exact (hr₀ _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ v _ φ hφ)).2
  have hW : ∀ u : Matrix (Fin n) (Fin d) (AE F E), locCo dd v (Matrix.fromCols uᵀ 0) =
      (Sum.elim (locCo M.co v u).1 0, Sum.elim (locCo M.co v u).2 0) := fun u => by
    ext k <;> rcases k with k | k <;> simp [locCo, hdd uᵀ 0, hd' u]
  have hkey : ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u →
      ∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
      c₀ * diagW (psiAt ψ v) μ φ (locCo M.co v u) = l (dd.rho ψ (Matrix.fromCols uᵀ 0) (tens (evFin F v) φ r₀)) :=
    fun u hu φ hφ => by
      rw [hstep _ (at_fromCols_zero hu) φ hφ, hlint _ (GlobalTheory.SchrSB.schr_mem_SB ψ hψ v _ φ hφ), hW, diagW]

  set P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) := ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) with hP
  set u : Matrix (Fin n) (Fin d) (AE F E) := z * Cᵀ with hu
  set u' : Matrix (Fin n) (Fin d) (AE F E) := ((P.toBlocks₁₁ - P.toBlocks₂₁) * z) * Cᵀ with hu'
  have hzat : At (evFin F v) u := at_mul_right' hz _
  have hu'at : At (evFin F v) u' := at_mul_right' (at_mul_left' _ hz) _
  set xm : Matrix (Fin d) (Fin n) (AE F E) := (P.toBlocks₂₁ * u)ᵀ with hxm
  set δ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    xm * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ with hδ
  have hδc : δ = Matrix.fromCols xm xm := by
    rw [hδ, diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
  set Ψ := tens (evFin F v) Φ r₀ with hΨ
  have hΨm : Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := (hr₀ Φ hΦ).2
  have h1 : tens (evFin F v) Φ₁ r₀ = omd p Ψ := (hacts r₀ (hr₀ Φ hΦ)).symm
  set γ := actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ (Matrix.fromCols uᵀ (0 : Matrix (Fin d) (Fin n) (AE F E))) with hγ
  have hγat : At (evFin F v) γ := at_mul_right' (at_fromCols_zero hzat) _
  have hinv : dd.rho ψ (Matrix.fromCols uᵀ 0) (omd p Ψ) = omd p (dd.rho ψ γ Ψ) := by
    have h := hsp.impl p⁻¹ (Matrix.fromCols uᵀ 0) (omd p Ψ) (hsp.pres p Ψ hΨm)
    have e1 : ∀ Y, omd p⁻¹ (omd p Y) = Y := fun Y => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have e2 : ∀ Y, omd p (omd p⁻¹ Y) = Y := fun Y => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [e1] at h
    rw [← h, e2]
  have hdec : γ = δ + Matrix.fromCols u'ᵀ 0 := by
    have e : u' = (P.toBlocks₁₁ - P.toBlocks₂₁) * u := by rw [hu', hu, Matrix.mul_assoc]
    rw [e, hδc, hxm]
    exact fromCols_mul_transpose_split u P
  have hsum : ∀ Y, dd.rho ψ γ Y = dd.rho ψ δ (dd.rho ψ (Matrix.fromCols u'ᵀ 0) Y) := fun Y => by
    rw [hdec]
    unfold Darboux.rho
    rw [map_add (f := _)]
    apply GlobalTheory.MixXEvUniq.schr_add
    rw [hδc, hdd xm xm, hdd u'ᵀ 0, hd' u', map_zero, hxm, hd' (P.toBlocks₂₁ * u)]
    simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, sumElim_dotProduct_sumElim, dotProduct_zero,
      zero_dotProduct, add_zero]
    have hform := M.co.form (P.toBlocks₂₁ * u) u'
    have h0 := GlobalTheory.InertVacIso.symp_eq_zero_of_lagAt σ X.J W v C hL (-1) (P.toBlocks₂₁ * u) u'
      ⟨at_mul_left' _ hzat, P.toBlocks₂₁ * z, by rw [hu, Matrix.mul_assoc]⟩ ⟨hu'at, (P.toBlocks₁₁ - P.toBlocks₂₁) * z, rfl⟩
    rw [h0] at hform
    exact (sub_eq_zero.mp hform.symm)
  have hW'm : dd.rho ψ (Matrix.fromCols u'ᵀ 0) Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) :=
    hmem _ (at_fromCols_zero hu'at) Φ hΦ
  have hγm : dd.rho ψ γ Ψ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)) := hmem γ hγat Φ hΦ
  apply mul_left_cancel₀ hc₀
  rw [hkey u hzat Φ₁ hΦ₁, h1, hinv, hρ _ hγm, hsum, hδ, hlinv xm _ hW'm, ← hkey u' hu'at Φ hΦ]
  ring

end GlobalTheory.InertLagChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilOperatorDiagonalIntegralHeisenbergPoiStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilOperator_diagonalIntegral_heisenberg_point : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ (v : Pl (F := F)) (m : ℕ) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), IsLagrAt σ W v C →
    ∀ d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = M.co.e x) →
    ∀ dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' dd →
    ∀ omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
    IsSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    ∀ l : (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ℂ,
    (∀ z : Matrix (Fin d) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)),
      l (dd.rho ψ (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) Φ) = l Φ) →
    ∀ r₀ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ,
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), Rest (evFin F v) φ r₀) →
    ∀ c₀ : ℂ, c₀ ≠ 0 → ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
    (∀ φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) →
    ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) (ρ₀ : ℂ),
    (∀ Φ ∈ schA F ((Fin n × Fin d) ⊕ (Fin n × Fin d)), l (omd p Φ) = ρ₀ * l Φ) →
    ∀ Φ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v), ∀ Φ₁ ∈ SB ((Fin n × Fin d) ⊕ (Fin n × Fin d) → Fv F v),
    Acts (evFin F v) (omd p) Φ Φ₁ → ∀ z : Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      diagW (psiAt ψ v) μ Φ₁ (locCo M.co v (z * Cᵀ)) = ρ₀ * diagW (psiAt ψ v) μ Φ (locCo M.co v
        (((((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₁₁ - ((p⁻¹).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).toBlocks₂₁) * z) * Cᵀ)) := by
  first | exact @GlobalTheory.InertLagChar.diagW_omd_point | exact GlobalTheory.InertLagChar.diagW_omd_point | (intros; apply GlobalTheory.InertLagChar.diagW_omd_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPointIntegralRelativeLocalBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPointIntegralRelativeLocalBasis
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisInt

open Matrix

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖(l : PadicAlgCl l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_natCast_eq_one (l : ℕ) [Fact l.Prime] {s : ℕ} (hs : ¬ l ∣ s) : ‖(s : PadicAlgCl l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs)

theorem norm_le_one_of_cols {C : Type} [NormedField C] [IsUltrametricDist C] {n : ℕ} (U : Matrix (Fin n) (Fin n) C) (p : C)
    (hp : ‖p‖ < 1) (h : ∀ b, ∃ T : Fin n → C, (∀ c, ‖T c‖ ≤ 1) ∧ ∀ a, ‖U a b - p * ∑ c, U a c * T c‖ ≤ 1) (a b : Fin n) :
    ‖U a b‖ ≤ 1 := by
  haveI : Nonempty (Fin n × Fin n) := ⟨(a, b)⟩
  obtain ⟨⟨a₀, b₀⟩, hmax⟩ := Finite.exists_max fun q : Fin n × Fin n => ‖U q.1 q.2‖
  refine (hmax (a, b)).trans ?_
  obtain ⟨T, hT, hU⟩ := h b₀
  by_contra hm
  have hm : 1 < ‖U a₀ b₀‖ := not_le.1 hm
  have h1 : ‖∑ c, U a₀ c * T c‖ ≤ ‖U a₀ b₀‖ :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun c _ => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hT c)).trans (hmax (a₀, c))
  have h2 : ‖p * ∑ c, U a₀ c * T c‖ < ‖U a₀ b₀‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans_lt (mul_lt_of_lt_one_left (one_pos.trans hm) hp)
  have h3 := IsUltrametricDist.norm_add_le_max (U a₀ b₀ - p * ∑ c, U a₀ c * T c) (p * ∑ c, U a₀ c * T c)
  rw [sub_add_cancel] at h3
  exact absurd h3 (not_le.2 (max_lt ((hU a₀).trans_lt hm) h2))

theorem exists_col {A E : Type} [CommRing A] [CommRing E] (j : E →+* A) (S : Subring A) {n : ℕ}
    (happ : ∀ M : ℕ, 0 < M → ∀ z : A, ∃ (e : E) (s : A), s ∈ S ∧ z = j e + (M : A) * s)
    (Y Yi : Matrix (Fin n) (Fin n) A) (hY : Yi * Y = 1) {N : ℕ} (hN : 0 < N) (hNm : ∀ a b, (N : A) * Yi a b ∈ S)
    {p : ℕ} (hp : 0 < p) (b : Fin n) :
    ∃ (x : Fin n → E) (t : Fin n → A), (∀ c, t c ∈ S) ∧ Yi *ᵥ (fun i => j (x i)) = Pi.single b 1 - (p : A) • t := by
  choose x s hs hx using fun i => happ (p * N) (Nat.mul_pos hp hN) (Y i b)
  refine ⟨x, ((N : A) • Yi) *ᵥ s, fun c => ?_, ?_⟩
  · rw [Matrix.mulVec, dotProduct]
    exact S.sum_mem fun k _ => S.mul_mem (hNm c k) (hs k)
  · have e : (fun i => j (x i)) = Y *ᵥ Pi.single b 1 - (p : A) • (N : A) • s := by
      funext i
      rw [Matrix.mulVec_single_one]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
      rw [hx i]
      push_cast
      ring
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hY, Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.smul_mulVec]

theorem read_col {A E C : Type} [CommRing A] [CommRing E] [CommRing C] (j : E →+* A) (ev : A →+* C) (inc : E →+* C)
    (hj : ∀ e, ev (j e) = inc e) {n : ℕ} (Y Yi : Matrix (Fin n) (Fin n) A) (hY : Y * Yi = 1) (Bi : Matrix (Fin n) (Fin n) E)
    {p : ℕ} {b : Fin n} {x : Fin n → E} {t : Fin n → A}
    (h : Yi *ᵥ (fun i => j (x i)) = Pi.single b 1 - (p : A) • t) (a : Fin n) :
    (Bi.map inc * Y.map ev) a b - (p : C) * ∑ c, (Bi.map inc * Y.map ev) a c * ev (t c) = inc ((Bi *ᵥ x) a) := by
  have h1 : Y *ᵥ (Pi.single b 1 - (p : A) • t) = fun i => j (x i) := by
    rw [← h, Matrix.mulVec_mulVec, hY, Matrix.one_mulVec]
  have h2 : (ev ∘ (Pi.single b 1 - (p : A) • t : Fin n → A)) = Pi.single b 1 - (p : C) • fun c => ev (t c) := by
    funext c
    simp only [Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_natCast,
      Pi.single_apply, apply_ite ev, map_one, map_zero]
  have h3 : Y.map ev *ᵥ (Pi.single b 1 - (p : C) • fun c => ev (t c)) = inc ∘ x := by
    funext i
    rw [← h2, ← RingHom.map_mulVec, h1, hj]
    rfl
  rw [RingHom.map_mulVec, ← h3, Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

theorem stdLat_of {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (h : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)) :
    Seed.FrmC.StdLat V := by
  intro x
  show (∑ i, x i • V.frame i ∈ V.L0) ↔ _
  rw [h, V.frame.mem_span_iff_repr_mem (𝓞 D.host.E), V.frame.repr_sum_self]
  exact forall_congr' fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem approx (M : ℕ) (hM : 0 < M) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ (e : E) (s : E ⊗[F] FiniteAdeleRing (𝓞 F) F), s ∈ Formalism.L2.Herm.intAf F E ∧
      z = e ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) + (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * s := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y hx hy =>
    obtain ⟨e₁, s₁, h₁, rfl⟩ := hx
    obtain ⟨e₂, s₂, h₂, rfl⟩ := hy
    refine ⟨e₁ + e₂, s₁ + s₂, add_mem h₁ h₂, ?_⟩
    rw [TensorProduct.add_tmul]
    ring
  | tmul b α =>
    obtain ⟨d, hd, ho⟩ := GlobalTheory.AdIdem.exists_nat_mul_integral E b
    obtain ⟨x, β, hβ, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F (M * d) (Nat.mul_pos hM hd) α
    refine ⟨x • b, ((d : E) * b) ⊗ₜ[F] β, GlobalTheory.PlaceDatum.tmul_mem_int ho (α := β) hβ, ?_⟩
    rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, TensorProduct.tmul_smul,
      ← nsmul_eq_mul, ← nsmul_eq_mul, mul_smul]
    rfl

theorem norm_ev_le_one {l : ℕ} [Fact l.Prime] {inc : E →+* PadicAlgCl l}
    {ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l} (hev : EvOk inc ev) {r : E ⊗[F] FiniteAdeleRing (𝓞 F) F}
    (hr : r ∈ Formalism.L2.Herm.intAf F E) :
    ‖ev ((Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm r)‖ ≤ 1 := by
  induction hr using Subring.closure_induction with
  | mem r hr =>
    rcases hr with ⟨⟨_, o, rfl⟩, rfl⟩ | ⟨⟨β, hβ⟩, rfl⟩
    · refine (congrArg norm (hev.1 (algebraMap (𝓞 E) E o))).le.trans ?_
      exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int inc o.isIntegral_coe)
    · exact hev.2.1 β hβ
  | zero => simp
  | one => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, map_neg, norm_neg]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy

end General


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem norm_le_one_of_isLocBasis : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map inc B)⁻¹ * Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).val a b‖ ≤ 1 := by
  intro D V l hl inc ev hev hL0 y B hB
  have hV := stdLat_of V hL0
  have hY := GlobalTheory.HLatStd.invM_mul y
  obtain ⟨N, hN, hNm⟩ := GlobalTheory.PlaceDatum.exists_den_matrix (GlobalTheory.StdFrameExist.SI D) GlobalTheory.PlaceDatum.exists_den_adele
    (GlobalTheory.HLatStd.invM y)
  let j : D.host.E →+* Lev.EAf D := Algebra.TensorProduct.includeLeftRingHom
  let ev' : Lev.EAf D →+* PadicAlgCl l := ev.comp (GlobalTheory.HeckeTrans.unswap D)
  have hU : ((Matrix.GeneralLinearGroup.map inc B)⁻¹ * Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).val =
      (B⁻¹).val.map inc * ((Units.val ((y : Bridge.Gf V) : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).map (Lev.swapAE D)).map ev' := by
    rw [← map_inv, Units.val_mul]
    congr 1
    ext a b
    exact (congrArg ev (GlobalTheory.HeckeTrans.unswap_swap _)).symm
  rw [hU]
  refine norm_le_one_of_cols _ (l : PadicAlgCl l) (norm_natCast_lt_one l) fun b => ?_
  obtain ⟨x, t, ht, hx⟩ := exists_col j (GlobalTheory.StdFrameExist.SI D) (fun M hM z => approx M hM z) _ _
    (mul_eq_one_comm.1 hY) hN hNm hl.out.pos b
  refine ⟨fun c => ev' (t c), fun c => norm_ev_le_one hev (ht c), fun a => ?_⟩
  rw [read_col j ev' inc (fun e => hev.1 e) _ _ hY _ hx a]
  have hmem : x ∈ Bridge.hLat V y := by
    refine GlobalTheory.HLatStd.mem_hLat_of hV y fun i => ?_
    have hi : (GlobalTheory.HLatStd.invM y *ᵥ GlobalTheory.HLatStd.iv x) i = _ := congrFun hx i
    rw [hi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    refine sub_mem ?_ (mul_mem (natCast_mem _ _) (ht i))
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨s, hs, hint⟩ := (hB x).1 ⟨1, hl.out.not_dvd_one, by rw [Nat.cast_one, one_smul]; exact hmem⟩
  obtain ⟨o, ho⟩ := hint a
  have h1 : ‖inc (algebraMap (𝓞 D.host.E) D.host.E o)‖ ≤ 1 :=
    GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int inc o.isIntegral_coe)
  rwa [ho, map_mul, map_natCast, norm_mul, norm_natCast_eq_one l hs, one_mul] at h1

end GlobalTheory.LocBasisInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPointIntegralRelativeLocalBasisStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPoint_integral_relative_localBasis : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map inc B)⁻¹ * Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))).val a b‖ ≤ 1 := by
  first | exact @GlobalTheory.LocBasisInt.norm_le_one_of_isLocBasis | exact GlobalTheory.LocBasisInt.norm_le_one_of_isLocBasis | (intros; apply GlobalTheory.LocBasisInt.norm_le_one_of_isLocBasis <;> assumption)
end
end
