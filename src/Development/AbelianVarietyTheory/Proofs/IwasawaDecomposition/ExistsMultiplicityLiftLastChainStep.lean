module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnHighestWeightPolynomialMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnHighestRowIntertwinersProportional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralInvariantRealTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralInvariantRealTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder NNReal ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftShift

theorem map_mul_right_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 C : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (k : G) :
    Measure.map (fun g => g * k) μ = μ := by
  have hle : μ 𝓕 ≤ μ C := by
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro h hh
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hh⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hC.measure_lt_top).ne
  have hpos : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ
  set c := Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ with hc
  have hq : Measure.QuasiMeasurePreserving (fun g : G => g * k) μ μ :=
    ⟨(measurable_mul_const k).aemeasurable, by rw [h]; exact Measure.smul_absolutelyContinuous⟩
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hq (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have h1 : Measure.map (fun g => g * k) μ 𝓕 = μ 𝓕 := by
    have := (MeasurableEquiv.mulRight k).map_apply (μ := μ) 𝓕
    rw [MeasurableEquiv.coe_mulRight] at this
    rw [this]
    exact h2.measure_eq h𝓕
  have h3 : (c : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕 := by
    rw [one_mul]
    conv_rhs => rw [← h1, h]
    simp
  have h4 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 : c = 1 := by exact_mod_cast h4
  rw [h, h5, one_smul]

theorem liftInt_shift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → ∀ k ∈ GinfC W, Lift.liftInt ν 𝓕 (thetaKO ω) (ω (1, k) s) (rTr W k F) = Lift.liftInt ν 𝓕 (thetaKO ω) s F := by
  intro D ψ V W χS χT ω ν 𝓕 s F H hpos hν h𝓕 hs hF hinv k _
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W.gram
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable W
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact W hpos
  obtain ⟨hcont, hθ⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω H s hs
  have hk := map_mul_right_of_cocompact (GQ W) ν 𝓕 C h𝓕 hC hcov k
  funext g
  have hΦ : ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) s * F (γ * h) = thetaKO ω g h s * F h := by
    intro γ hγ h
    have := hθ 1 (one_mem _) γ hγ g h
    rw [one_mul] at this
    rw [this, hinv γ hγ]
  have hi : IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν :=
    GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain W ν 𝓕 C hν h𝓕 hC hcov _
      ((hcont.comp (Continuous.prodMk_right g)).mul hF) hΦ
  have key := (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ W) ν 𝓕 h𝓕 k hk
    (fun h => thetaKO ω g h s * F h) hΦ hi).2
  have hsh : ∀ h, thetaKO ω g h (ω (1, k) s) = thetaKO ω g (h * k) s := by
    intro h
    have h1 : ω (g, h * k) = ω (g, h) * ω (1, k) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    unfold thetaKO
    rw [h1]
    rfl
  unfold Lift.liftInt
  simp only [hsh, rTr]
  exact key

end GlobalTheory.LiftShift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralInvariantRealTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteThetaIntegral_invariant_real_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → ∀ k ∈ GinfC W, Lift.liftInt ν 𝓕 (thetaKO ω) (ω (1, k) s) (rTr W k F) = Lift.liftInt ν 𝓕 (thetaKO ω) s F := by
  first | exact @GlobalTheory.LiftShift.liftInt_shift | exact GlobalTheory.LiftShift.liftInt_shift | (intros; apply GlobalTheory.LiftShift.liftInt_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDegreeBoundOfRowUnitaryInvariantPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDegreeBoundOfRowUnitaryInvariantPairing
noncomputable section

open GlobalTheory.DefLift

namespace GlobalTheory.RowSupport

theorem exp_I_pow_injective : Function.Injective fun e : ℕ => Complex.exp Complex.I ^ e := by
  intro a b h
  simp only [← Complex.exp_nat_mul] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have h2 : (a : ℝ) = b + k * (2 * Real.pi) := by
    have := congrArg Complex.im hk
    simpa using this
  by_cases h0 : k = 0
  · subst h0
    exact_mod_cast (by simpa using h2 : (a : ℝ) = b)
  · exfalso
    have h3 : (2 * k : ℤ) ≠ 0 := mul_ne_zero two_ne_zero h0
    refine (irrational_pi.intCast_mul h3).ne_int ((a : ℤ) - b) ?_
    push_cast
    linarith

def scal (m : ℕ) : Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨Complex.exp Complex.I • 1, by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, mul_one]
    have : Complex.exp Complex.I * star (Complex.exp Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp
    rw [this, one_smul]⟩

open Classical in
theorem rowSub_scal {ι : Type} [Fintype ι] {m n : ℕ} (τ : ι) (α : ι × Fin m × Fin n →₀ ℕ) :
    rowSub n τ (scal m) (MvPolynomial.monomial α 1) =
      Complex.exp Complex.I ^ (∑ v, if v.1 = τ then α v else 0) • MvPolynomial.monomial α 1 := by
  have hv : ∀ v : ι × Fin m × Fin n,
      (∑ i, ∑ c, ((if v.1 = τ then (scal m : Matrix (Fin m) (Fin m) ℂ) else 1) i v.2.1 *
        (1 : Matrix (Fin n) (Fin n) ℂ) v.2.2 c) • (MvPolynomial.X (v.1, i, c) : Pol ι m n)) =
      (if v.1 = τ then Complex.exp Complex.I else 1) • MvPolynomial.X v := by
    rintro ⟨ρ, j, d⟩
    by_cases h : ρ = τ
    · simp [h, scal, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [h, Matrix.one_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']
  unfold rowSub subst
  rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, map_one, one_mul, MvPolynomial.monomial_eq, map_one, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [hv, smul_pow]
  rw [Finset.prod_smul, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem exists_degree_bound (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X) (β : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ)
    (h : ∀ τ u P x, β (rowSub n τ u P) (π τ u x) = β P x) :
    ∃ d : ℕ, ∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → β (MvPolynomial.monomial α 1) = 0 := by
  classical
  have hfin : ∀ τ, ∃ d : ℕ, ∀ e : ℕ,
      Module.End.HasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
        (Complex.exp Complex.I ^ e)⁻¹ → e ≤ d := by
    intro τ
    have h1 := Module.End.finite_hasEigenvalue (LinearMap.dualMap (π τ (scal m)) : Module.End ℂ (Module.Dual ℂ X))
    have h2 := h1.preimage (f := fun e : ℕ => (Complex.exp Complex.I ^ e)⁻¹)
      (inv_injective.comp exp_I_pow_injective).injOn
    obtain ⟨d, hd⟩ := h2.bddAbove
    exact ⟨d, fun e he => hd he⟩
  choose d hd using hfin
  refine ⟨∑ τ, d τ, fun α hα => ?_⟩
  by_contra hne
  have hdeg : α.degree = ∑ τ, ∑ v, if v.1 = τ then α v else 0 := by
    rw [Finset.sum_comm, Finsupp.degree_eq_sum]
    simp
  refine absurd hα (not_lt.2 ?_)
  rw [hdeg]
  refine Finset.sum_le_sum fun τ _ => hd τ _ ?_
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := β (MvPolynomial.monomial α 1)) ⟨?_, hne⟩
  rw [Module.End.mem_eigenspace_iff]
  ext x
  have := h τ (scal m) (MvPolynomial.monomial α 1) x
  rw [rowSub_scal, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  rw [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ (Complex.exp_ne_zero _))]
  convert this

end GlobalTheory.RowSupport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDegreeBoundOfRowUnitaryInvariantPairingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degree_bound_of_rowUnitary_invariant_pairing : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X) (β : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ), (∀ τ u P x, β (rowSub n τ u P) (π τ u x) = β P x) → ∃ d : ℕ, ∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → β (MvPolynomial.monomial α 1) = 0 := by
  first | exact @GlobalTheory.RowSupport.exists_degree_bound | exact GlobalTheory.RowSupport.exists_degree_bound | (intros; apply GlobalTheory.RowSupport.exists_degree_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColStableDisjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalTotalDegreeLe
universe u_1
namespace GlobalTheory.AevalTotalDegreeBound
open MvPolynomial

theorem aeval_totalDegree_le {σ : Type u_1} (f : σ → MvPolynomial σ ℂ)
    (hf : ∀ v, (f v).totalDegree ≤ 1) (P : MvPolynomial σ ℂ) :
    (aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  unfold Finsupp.sum
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (s i) (hf i)

theorem main : ∀ {σ : Type u_1} (f : σ → MvPolynomial σ ℂ), (∀ (v : σ), MvPolynomial.totalDegree (f v) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial σ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial σ ℂ → MvPolynomial σ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => aeval_totalDegree_le f hf P

end GlobalTheory.AevalTotalDegreeBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColStableDisjoint
noncomputable section

open MvPolynomial GlobalTheory.MvPoly GlobalTheory.Harm Matrix

namespace GlobalTheory.DefLift

namespace Compl

theorem exists_sub_perp {E : Type*} [AddCommGroup E] [Module ℂ E] (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x, B x x = 0 → x = 0) (W : Submodule ℂ E) [FiniteDimensional ℂ W] (P : E) :
    ∃ Q ∈ W, ∀ w ∈ W, B (P - Q) w = 0 := by
  let b := Module.finBasis ℂ W
  let L : E →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearMap.pi fun i => B.flip (b i)
  have hL (P) (h : L P = 0) (w) (hw : w ∈ W) : B P w = 0 := by
    have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Submodule.subtype_apply] at this
    change _ = w at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smulₛₗ]
    exact smul_eq_zero_of_right _ (congrFun h i)
  have hinj : Function.Injective (L ∘ₗ W.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hB _ (hL x hx x x.2))
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
    (L P)
  exact ⟨x, x.2, hL _ (by rw [map_sub, ← hx]; simp)⟩

theorem totalDegree_aeval_le {σ : Type*} (f : σ → MvPolynomial σ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeBound.main
  | exact _root_.GlobalTheory.AevalTotalDegreeBound.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeBound.main ..)

variable {ι : Type} {m n : ℕ}

theorem totalDegree_subst_le (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ) (P : Pol ι m n) :
    (subst a b P).totalDegree ≤ P.totalDegree := by
  refine totalDegree_aeval_le _ (fun v => ?_) P
  refine totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le fun c _ => ?_
  exact (totalDegree_smul_le _ _).trans (totalDegree_X _).le

theorem totalDegree_colSub_le (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P : Pol ι m n) :
    (colSub m τ g P).totalDegree ≤ P.totalDegree := by
  unfold colSub
  rw [AlgHom.toLinearMap_apply]
  exact totalDegree_subst_le _ _ _

theorem fockInner_subst [Fintype ι] (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ)
    (P Q : Pol ι m n) :
    fockInner (subst a b P) Q = fockInner P (subst (fun τ => star (a τ)) (fun τ => star (b τ)) Q) := by
  classical
  refine fockInner_algHom_of_linear _ _
    (fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0) ?_ ?_ P Q
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type]
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type, apply_ite star, mul_comm]

theorem fockInner_colSub [Fintype ι] (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P Q : Pol ι m n) :
    fockInner (colSub m τ g P) Q = fockInner P (colSub m τ g⁻¹ Q) := by
  unfold colSub
  simp only [AlgHom.toLinearMap_apply]
  rw [fockInner_subst]
  congr 3
  · funext ρ
    split_ifs
    · rfl
    · simp
  · funext ρ
    simp

end Compl


open Compl in
theorem exists_colStable_disjoint (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (U W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n))
    (hU : ∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) (hW : ∀ Φ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ W) (hlt : U < W) :
    ∃ U' : Submodule ℂ (X →ₗ[ℂ] Pol ι m n), U' ≠ ⊥ ∧ U' ≤ W ∧ U ⊓ U' = ⊥ ∧
      ∀ Φ ∈ U', ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U' := by
  classical
  let b := Module.finBasis ℂ X
  let B : (X →ₗ[ℂ] Pol ι m n) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Φ Ψ => ∑ i, fockInner (Φ (b i)) (Ψ (b i)))
      (fun _ _ _ => by simp [fockInner_add_left, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_left, Finset.mul_sum])
      (fun _ _ _ => by simp [fockInner_add_right, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_right, Finset.mul_sum])
  have hBa (Φ Ψ) : B Φ Ψ = ∑ i, fockInner (Φ (b i)) (Ψ (b i)) := rfl
  have hB (Φ) (h : B Φ Φ = 0) : Φ = 0 := by
    rw [hBa] at h
    simp only [fockInner_self] at h
    have h' : ∑ i, fockNormSq (Φ (b i)) = 0 := by
      rw [← RCLike.ofReal_sum] at h
      exact RCLike.ofReal_eq_zero.mp h
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => fockNormSq_nonneg _] at h'
    exact b.ext fun i => fockNormSq_eq_zero.mp (h' i (Finset.mem_univ i))
  have hadj (Φ Ψ τ g) : B (colSub m τ g ∘ₗ Φ) Ψ = B Φ (colSub m τ g⁻¹ ∘ₗ Ψ) := by
    simp only [hBa, LinearMap.comp_apply, fockInner_colSub]
  clear hBa
  clear_value B
  obtain ⟨β, hβW, hβU⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ∀ i, (β (b i)).totalDegree ≤ d :=
    ⟨_, fun i => Finset.le_sup (f := fun i => (β (b i)).totalDegree) (Finset.mem_univ i)⟩
  obtain ⟨R, hRf, hR⟩ : ∃ R : Submodule ℂ (Pol ι m n), FiniteDimensional ℂ R ∧ ∀ P, P ∈ R ↔ P.totalDegree ≤ d :=
    ⟨restrictTotalDegree (ι × Fin m × Fin n) ℂ d, inferInstance, fun P => mem_restrictTotalDegree _ _ _⟩
  let ψ : (X →ₗ[ℂ] R) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) :=
    { toFun := fun Ψ => R.subtype ∘ₗ Ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let D : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := LinearMap.range ψ
  have hD (Φ) : Φ ∈ D ↔ ∀ x, Φ x ∈ R := by
    constructor
    · rintro ⟨Ψ, rfl⟩ x
      exact (Ψ x).2
    · intro h
      exact ⟨Φ.codRestrict R h, rfl⟩
  haveI : FiniteDimensional ℂ D := inferInstance
  clear_value D
  have hDs (Φ) (h : Φ ∈ D) (τ g) : colSub m τ g ∘ₗ Φ ∈ D := by
    rw [hD] at h ⊢
    intro x
    have := h x
    rw [hR] at this ⊢
    rw [LinearMap.comp_apply]
    exact (totalDegree_colSub_le τ g _).trans this
  have hβD : β ∈ D := by
    rw [hD]
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine R.sum_mem fun i _ => ?_
    rw [map_smul]
    exact R.smul_mem _ ((hR _).2 (hd i))
  haveI : FiniteDimensional ℂ (U ⊓ D : Submodule ℂ _) := Submodule.finiteDimensional_inf_right _ _
  let T : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := ⨅ w ∈ U ⊓ D, LinearMap.ker (B.flip w)
  have hT (Φ) : Φ ∈ T ↔ ∀ w ∈ U ⊓ D, B Φ w = 0 := by simp [T, Submodule.mem_iInf]
  obtain ⟨Q, hQ, hperp⟩ := exists_sub_perp B hB (U ⊓ D) β
  refine ⟨W ⊓ D ⊓ T, ?_, inf_le_left.trans inf_le_left, ?_, ?_⟩
  · intro h
    have hm : β - Q ∈ W ⊓ D ⊓ T :=
      ⟨⟨W.sub_mem hβW (hlt.le hQ.1), D.sub_mem hβD hQ.2⟩, (hT _).2 hperp⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at hm
    exact hβU (hm ▸ hQ.1)
  · rw [Submodule.eq_bot_iff]
    rintro Φ ⟨h1, ⟨-, h2⟩, h3⟩
    exact hB Φ ((hT Φ).1 h3 Φ ⟨h1, h2⟩)
  · rintro Φ ⟨⟨h1, h2⟩, h3⟩ τ g
    refine ⟨⟨hW Φ h1 τ g, hDs Φ h2 τ g⟩, (hT _).2 fun w hw => ?_⟩
    rw [hadj]
    exact (hT Φ).1 h3 _ ⟨hU w hw.1 τ _, hDs w hw.2 τ _⟩

end GlobalTheory.DefLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColStableDisjointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_colStable_complement_of_lt : ∀ (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (U W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)), (∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) → (∀ Φ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ W) → U < W → ∃ U' : Submodule ℂ (X →ₗ[ℂ] Pol ι m n), U' ≠ ⊥ ∧ U' ≤ W ∧ U ⊓ U' = ⊥ ∧ ∀ Φ ∈ U', ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U' := by
  first | exact @GlobalTheory.DefLift.exists_colStable_disjoint | exact GlobalTheory.DefLift.exists_colStable_disjoint | (intros; apply GlobalTheory.DefLift.exists_colStable_disjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStep
noncomputable section

namespace GlobalTheory.DefLift

section Algebra

open Matrix

variable {ι : Type} {m n : ℕ}

theorem subst_subst (a a' : ι → Matrix (Fin n) (Fin n) ℂ) (b b' : ι → Matrix (Fin m) (Fin m) ℂ) (P : Pol ι m n) :
    subst a b (subst a' b' P) = subst (fun τ => a' τ * a τ) (fun τ => b τ * b' τ) P := by
  refine DFunLike.congr_fun (?_ : (subst a b).comp (subst a' b') = _) P
  refine MvPolynomial.algHom_ext fun v => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [subst, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_smul, Finset.smul_sum, smul_smul,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul]
  calc _ = ∑ i, ∑ c, ∑ i', ∑ c', (b v.1 i' i * b' v.1 i v.2.1 * (a' v.1 v.2.2 c * a v.1 c c')) •
        (MvPolynomial.X (v.1, i', c') : Pol ι m n) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i' _ =>
          Finset.sum_congr rfl fun c' _ => ?_
        congr 1; ring
    _ = _ := by
        rw [Finset.sum_comm]
        refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i' _ => ?_
        refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
        rw [Finset.sum_comm]

theorem subst_one (P : Pol ι m n) : subst (fun _ => 1) (fun _ => 1) P = P := by
  refine DFunLike.congr_fun (?_ : subst (fun _ => 1) (fun _ => 1) = AlgHom.id ℂ _) P
  refine MvPolynomial.algHom_ext fun v => ?_
  simp [subst, Matrix.one_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_smul]

theorem colSub_rowSub (τ ρ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (u : Matrix.unitaryGroup (Fin m) ℂ) (P : Pol ι m n) :
    colSub m τ g (rowSub n ρ u P) = rowSub n ρ u (colSub m τ g P) := by
  simp only [colSub, rowSub, AlgHom.toLinearMap_apply, subst_subst, Matrix.one_mul, Matrix.mul_one]

theorem rowSub_rowSub_inv (τ : ι) (u : Matrix.unitaryGroup (Fin m) ℂ) (P : Pol ι m n) :
    rowSub n τ u (rowSub n τ u⁻¹ P) = P := by
  simp only [rowSub, AlgHom.toLinearMap_apply, subst_subst, Matrix.one_mul]
  refine Eq.trans (congrArg (fun b => subst (fun _ => 1) b P) (funext fun ρ => ?_)) (subst_one P)
  split_ifs
  · rw [← Submonoid.coe_mul, mul_inv_cancel]; rfl
  · exact Matrix.one_mul _

def utr {k : ℕ} (u : Matrix.unitaryGroup (Fin k) ℂ) : Matrix.unitaryGroup (Fin k) ℂ :=
  ⟨(u : Matrix (Fin k) (Fin k) ℂ)ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h := congrArg Matrix.transpose (Matrix.mem_unitaryGroup_iff'.1 u.2)
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h
    exact h⟩

theorem utr_utr {k : ℕ} (u : Matrix.unitaryGroup (Fin k) ℂ) : utr (utr u) = u := rfl

variable [Fintype ι] {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]

theorem mem_of_intertwiner (hnm : n ≤ m) {π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X} (hπ : IrrFam π)
    (U : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)) (hU0 : U ≠ ⊥)
    (hU : ∀ Φ ∈ U, ∀ τ u x, Φ (π τ u x) = rowSub n τ u (Φ x)) (hst : ∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U)
    (Φ : X →ₗ[ℂ] Pol ι m n) (hΦ : ∀ τ u x, Φ (π τ u x) = rowSub n τ u (Φ x)) : Φ ∈ U := by
  let W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) :=
    { carrier := {Ψ | ∀ τ u x, Ψ (π τ u x) = rowSub n τ u (Ψ x)}
      add_mem' := fun ha hb τ u x => by simp only [LinearMap.add_apply, map_add (f := _), ha τ u x, hb τ u x]
      zero_mem' := fun τ u x => by simp
      smul_mem' := fun c _ ha τ u x => by simp only [LinearMap.smul_apply, map_smul, ha τ u x] }
  have hW : ∀ Ψ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Ψ ∈ W := fun Ψ h τ g ρ u x => by
    simp only [LinearMap.comp_apply, h ρ u x, colSub_rowSub]
  by_contra hn
  obtain ⟨U', h0, hle, hd, hst'⟩ := GlobalTheory.T.exists_colStable_complement_of_lt ι m n X U W hst hW (lt_of_le_of_ne hU fun e => hn (e ▸ hΦ))
  obtain ⟨Φ₁, h1, h1', a1, μ, b1⟩ := GlobalTheory.T.exists_column_highest_weight_polynomial_map ι m n X U' h0 hst'
  obtain ⟨Φ₂, h2, h2', a2, μ', b2⟩ := GlobalTheory.T.exists_column_highest_weight_polynomial_map ι m n X U hU0 hst
  obtain ⟨r, hr⟩ := GlobalTheory.T.columnHighest_rowIntertwiners_proportional ι m n hnm X π hπ Φ₁ Φ₂ μ μ' h1' (fun τ u x => ⟨hle h1 τ u x, hU _ h2 τ u x⟩)
    (fun τ k l h => ⟨a1 τ k l h, a2 τ k l h⟩) fun τ k => ⟨b1 τ k, b2 τ k⟩
  have : Φ₂ ∈ U ⊓ U' := ⟨h2, hr ▸ U'.smul_mem r h1⟩
  rw [hd] at this
  exact h2' this

theorem mem_of_invariant (hnm : n ≤ m) {π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X} (hπ : IrrFam π)
    (U : Submodule ℂ (Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ)) (hU0 : U ≠ ⊥)
    (hU : ∀ β ∈ U, ∀ τ u P x, β (rowSub n τ u P) (π τ u x) = β P x) (hst : ∀ β ∈ U, ∀ τ g, β ∘ₗ colSub m τ g ∈ U)
    (β : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ) (hβ : ∀ τ u P x, β (rowSub n τ u P) (π τ u x) = β P x) : β ∈ U := by
  obtain ⟨B, hB0, hBt, hBr⟩ := GlobalTheory.T.exists_bilinearFischerPairing_matrixEntryPolynomialRing ι m n
  have hinj : Function.Injective B.flip := (injective_iff_map_eq_zero _).2 fun Q h => hB0 Q fun P => LinearMap.congr_fun h P
  let Θ : (X →ₗ[ℂ] Pol ι m n) →ₗ[ℂ] (Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ) :=
    { toFun := fun Φ => B.compl₂ Φ
      map_add' := fun a b => LinearMap.ext₂ fun P x => by simp
      map_smul' := fun c a => LinearMap.ext₂ fun P x => by simp }
  have hrow : ∀ τ u P Q, B (rowSub n τ u P) Q = B P (rowSub n τ (utr u) Q) := fun τ u P Q => by
    simp only [rowSub, AlgHom.toLinearMap_apply, hBt, Matrix.transpose_one]
    refine congrArg (fun b => B P (subst (fun _ => 1) b Q)) (funext fun ρ => ?_)
    split_ifs
    · rfl
    · exact Matrix.transpose_one
  have hcol : ∀ τ g P Q, B (colSub m τ (utr g) P) Q = B P (colSub m τ g Q) := fun τ g P Q => by
    simp only [colSub, AlgHom.toLinearMap_apply, hBt, Matrix.transpose_one]
    refine congrArg (fun a => B P (subst a (fun _ => 1) Q)) (funext fun ρ => ?_)
    split_ifs
    · rfl
    · exact Matrix.transpose_one
  have hrep : ∀ γ : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ, (∀ τ u P x, γ (rowSub n τ u P) (π τ u x) = γ P x) → ∃ Φ, Θ Φ = γ := by
    intro γ hγ
    obtain ⟨d, hd⟩ := GlobalTheory.T.exists_degree_bound_of_rowUnitary_invariant_pairing ι m n X π γ hγ
    have hx : ∀ x, γ.flip x ∈ LinearMap.range B.flip := fun x => by
      obtain ⟨Q, hQ⟩ := hBr (γ.flip x) d fun α hα => by rw [LinearMap.flip_apply, hd α hα]; rfl
      exact ⟨Q, LinearMap.ext hQ⟩
    refine ⟨(LinearEquiv.ofInjective _ hinj).symm.toLinearMap ∘ₗ γ.flip.codRestrict _ hx, ?_⟩
    refine LinearMap.ext₂ fun P x => ?_
    exact LinearMap.congr_fun (LinearEquiv.ofInjective_symm_apply B.flip (h := hinj) ⟨_, hx x⟩) P
  have hint : ∀ Φ, (∀ τ u P x, Θ Φ (rowSub n τ u P) (π τ u x) = Θ Φ P x) →
      ∀ τ u x, Φ (π τ (utr u⁻¹) x) = rowSub n τ u (Φ x) := fun Φ h τ u x => by
    have e : rowSub n τ u⁻¹ (Φ (π τ (utr u⁻¹) x)) = Φ x :=
      hinj (LinearMap.ext fun P => (hrow τ (utr u⁻¹) P _).symm.trans (h τ (utr u⁻¹) P x))
    rw [← e, rowSub_rowSub_inv]
  have hπ' : IrrFam fun τ u => π τ (utr u⁻¹) := fun V hV => hπ V fun τ u x hx => by
    have := hV τ (utr u)⁻¹ x hx
    simpa only [inv_inv, utr_utr] using this
  obtain ⟨Φ, rfl⟩ := hrep β hβ
  refine mem_of_intertwiner hnm hπ' (U.comap Θ) ?_ (fun Ψ h => hint Ψ (hU _ h)) (fun Ψ h τ g => ?_) Φ (hint Φ hβ)
  · obtain ⟨γ, hγ, hγ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨Ψ, rfl⟩ := hrep γ (hU γ hγ)
    exact (Submodule.ne_bot_iff _).2 ⟨Ψ, hγ, fun e => hγ0 (by rw [e, map_zero])⟩
  · have e : Θ (colSub m τ g ∘ₗ Ψ) = Θ Ψ ∘ₗ colSub m τ (utr g) := by
      refine LinearMap.ext₂ fun P x => ?_
      exact (hcol τ g P (Ψ x)).symm
    rw [Submodule.mem_comap, e]
    exact hst _ h τ _

theorem exists_factor (hnm : n ≤ m) {π : ι → Matrix.unitaryGroup (Fin m) ℂ → Module.End ℂ X} (hπ : IrrFam π)
    {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (ρ : ι → Matrix.unitaryGroup (Fin n) ℂ → Module.End ℂ Y) (It : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] Y) (h0 : It ≠ 0)
    (hinv : ∀ τ u P x, It (rowSub n τ u P) (π τ u x) = It P x)
    (heq : ∀ τ g P x, It (colSub m τ g P) x = ρ τ g (It P x)) (B : Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] Z)
    (hB : ∀ τ u P x, B (rowSub n τ u P) (π τ u x) = B P x) : ∃ L : Y →ₗ[ℂ] Z, ∀ P x, L (It P x) = B P x := by
  let Θ : Module.Dual ℂ Y →ₗ[ℂ] (Pol ι m n →ₗ[ℂ] X →ₗ[ℂ] ℂ) :=
    { toFun := fun l => It.compr₂ l
      map_add' := fun a b => LinearMap.ext₂ fun P x => by simp
      map_smul' := fun c a => LinearMap.ext₂ fun P x => by simp }
  have key : ∀ l : Module.Dual ℂ Z, ∃ l' : Module.Dual ℂ Y, ∀ P x, l' (It P x) = l (B P x) := fun l => by
    have : B.compr₂ l ∈ LinearMap.range Θ := by
      refine mem_of_invariant hnm hπ _ (fun e => h0 ?_) ?_ ?_ _ fun τ u P x => congrArg l (hB τ u P x)
      · refine LinearMap.ext₂ fun P x => ?_
        refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l' => ?_
        have : Θ l' = 0 := by rw [← Submodule.mem_bot ℂ, ← e]; exact ⟨l', rfl⟩
        exact LinearMap.congr_fun₂ this P x
      · rintro _ ⟨l', rfl⟩ τ u P x
        exact congrArg l' (hinv τ u P x)
      · rintro _ ⟨l', rfl⟩ τ g
        exact ⟨l' ∘ₗ ρ τ g, LinearMap.ext₂ fun P x => (congrArg l' (heq τ g P x)).symm⟩
    obtain ⟨l', hl'⟩ := this
    exact ⟨l', fun P x => LinearMap.congr_fun₂ hl' P x⟩
  have hker : LinearMap.ker (TensorProduct.lift It) ≤ LinearMap.ker (TensorProduct.lift B) := fun t ht => by
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
    obtain ⟨l', hl'⟩ := key l
    have e : l' ∘ₗ TensorProduct.lift It = l ∘ₗ TensorProduct.lift B := TensorProduct.ext' hl'
    rw [← LinearMap.comp_apply, ← e, LinearMap.comp_apply, LinearMap.mem_ker.1 ht, map_zero]
  obtain ⟨L, hL⟩ := LinearMap.exists_extend
    (((LinearMap.ker (TensorProduct.lift It)).liftQ _ hker) ∘ₗ (TensorProduct.lift It).quotKerEquivRange.symm.toLinearMap)
  refine ⟨L, fun P x => ?_⟩
  have := LinearMap.congr_fun hL ⟨_, ⟨P ⊗ₜ[ℂ] x, rfl⟩⟩
  exact this.trans (congrArg ((LinearMap.ker (TensorProduct.lift It)).liftQ _ hker)
    (LinearMap.quotKerEquivRange_symm_apply_image (TensorProduct.lift It) (P ⊗ₜ[ℂ] x) ⟨_, rfl⟩))

end Algebra

section Lift

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_integralForm {X : Type} [MeasurableSpace X] (μ : Measure X) :
    ∃ I : (X → ℂ) →ₗ[ℂ] ℂ, ∀ φ, Integrable φ μ → I φ = ∫ x, φ x ∂μ := by
  let U : Submodule ℂ (X → ℂ) :=
    { carrier := {φ | Integrable φ μ}
      add_mem' := fun ha hb => Integrable.add ha hb
      zero_mem' := integrable_zero _ _ _
      smul_mem' := fun c _ h => Integrable.smul c h }
  let l : U →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ x, φ.1 x ∂μ
      map_add' := fun a b => integral_add a.2 b.2
      map_smul' := fun c a => integral_smul c a.1 }
  obtain ⟨I, hI⟩ := LinearMap.exists_extend l
  exact ⟨I, fun φ h => LinearMap.congr_fun hI ⟨φ, h⟩⟩

theorem exists_trilinear {G H S P Ds : Type} [MeasurableSpace H] [AddCommGroup S] [Module ℂ S] [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Ds] [Module ℂ Ds] (ν : Measure H) (𝓕 : Set H) (th : G → H → S →ₗ[ℂ] ℂ) (pt : P →ₗ[ℂ] S)
    (C : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ)))
    (hint : ∀ F : C, ∀ φ v g, IntegrableOn (fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h) 𝓕 ν) :
    ∃ B : P →ₗ[ℂ] Ds →ₗ[ℂ] C →ₗ[ℂ] (G → ℂ), ∀ φ v F,
      B φ v F = Lift.liftInt ν 𝓕 (fun g h s => th g h s) (pt φ) ((F : Ds →ₗ[ℂ] (H → ℂ)) v) := by
  obtain ⟨I, hI⟩ := exists_integralForm (ν.restrict 𝓕)
  let b : P → Ds → C →ₗ[ℂ] (G → ℂ) := fun φ v =>
    { toFun := fun F g => I fun h => th g h (pt φ) * (F : Ds →ₗ[ℂ] (H → ℂ)) v h
      map_add' := fun F F' => funext fun g => by
        rw [Pi.add_apply, ← map_add (f := _)]; congr 1; funext h; simp [mul_add]
      map_smul' := fun c F => funext fun g => by
        rw [Pi.smul_apply, ← map_smul]; congr 1; funext h; simp [mul_left_comm] }
  refine ⟨LinearMap.mk₂ ℂ b ?_ ?_ ?_ ?_, fun φ v F => funext fun g => hI _ (hint F φ v g)⟩
  · refine fun φ φ' v => LinearMap.ext fun F => funext fun g => ?_
    show I _ = I _ + I _
    rw [← map_add (f := _)]; congr 1; funext h; simp [add_mul]
  · refine fun c φ v => LinearMap.ext fun F => funext fun g => ?_
    show I _ = c • I _
    rw [← map_smul]; congr 1; funext h; simp [mul_assoc]
  · refine fun φ v v' => LinearMap.ext fun F => funext fun g => ?_
    show I _ = I _ + I _
    rw [← map_add (f := _)]; congr 1; funext h; simp [mul_add]
  · refine fun c φ v => LinearMap.ext fun F => funext fun g => ?_
    show I _ = c • I _
    rw [← map_smul]; congr 1; funext h; simp [mul_left_comm]

variable {D : D7}


set_option maxHeartbeats 800000 in
theorem ioExists_definite {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')
    {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hV : V.SigOK) (hW : W.SigOK) (hrk : V.rank ≤ W.rank)
    (hM : AllPlus M) (hM' : AllPlus M') (hpt : ∀ P, IsThetaFunO ψ V W (ptOf ψ θ M M' f P))
    (hvac : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f)
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (hIt : IsItW θ M M' ω (ptOf ψ θ M M' f) It)
    {J : Set (GA D V)} {χ : GA D V → ℂ} (hJ : ∀ κ ∈ J, κ ∈ GfC V ∧ ω (κ, 1) f = χ κ • f)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1)
    {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    {J' : Set (GA D W)} {χ' : GA D W → ℂ} {C : Submodule ℂ (SmT M' →ₗ[ℂ] (GA D W → ℂ))} (hC : C ≤ MultT θ M' J' χ') :
    Lift.IoExists ν 𝓕 (thetaKO ω) (ptOf ψ θ M M' f) It C (MultT θ M J χ) := by
  have hf : IsThetaFunO ψ V W f := by
    have := hpt 1
    rwa [ptOf, GlobalTheory.FiniteFock.pureTensorO_one] at this
  have m1 := GlobalTheory.T.finiteDimensional_smooth_irreducible_of_allPlus D V S M hM
  have m2 := GlobalTheory.T.finiteDimensional_smooth_irreducible_of_allPlus D W S' M' hM'
  obtain ⟨fd, inj, π, hπ, irr⟩ := GlobalTheory.T.tensorProduct_definiteUnitary_localModels_irreducible D V S M m1 hM
  obtain ⟨fd', inj', π', hπ', irr'⟩ := GlobalTheory.T.tensorProduct_definiteUnitary_localModels_irreducible D W S' M' m2 hM'
  have hfock := GlobalTheory.T.definiteUnitary_realPoints_act_fock_substitution D ψ V W χS χT ω θ S S' M M' f hω hθ hV hW hM hM' hf hvac
  choose cV hcV0 hcV using fun τ => (hfock τ).1
  choose cW hcW0 hcW using fun τ => (hfock τ).2
  have hF := fun F : C => GlobalTheory.T.multiplicitySpace_definite_continuous_invariant_equivariant D θ W S' M' π' J' χ' hM' (fun τ => (m2 τ).2.1) inj' hπ' F (hC F.2)
  have hL := fun (F : C) φ v => GlobalTheory.T.definiteThetaIntegral_integrable_continuous D ψ V W χS χT ω ν 𝓕 _ _ hω hM'.posDef hν h𝓕 (hpt φ) (hF F v).1 (hF F v).2.1
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) := pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f
  have hpe : ∀ P, ptOf ψ θ M M' f P = pt P := fun _ => rfl
  obtain ⟨B, hB⟩ := exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω (g, h)) pt C fun F φ v => (hL F φ v).1
  replace hB : ∀ φ v F, B φ v F =
      Lift.liftInt ν 𝓕 (thetaKO ω) (ptOf ψ θ M M' f φ) ((F : SmT M' →ₗ[ℂ] (GA D W → ℂ)) v) := hB

  have hcol : ∀ τ g P x, It (cV τ g • colSub W.rank τ g P) x = π τ g (It P x) := fun τ g P x => inj <| by
    rw [hπ]
    exact hIt.eqK τ _ (hM.unfr_mem τ g) P _ (by rw [hcV, hpe, hpe, map_smul]) x
  have hrow : ∀ τ u P x, It (cW τ u • rowSub V.rank τ u P) (π' τ u x) = It P x := fun τ u P x =>
    hIt.invK τ _ (hM'.unfr_mem τ u) P _ x _ (by rw [hcW, hpe, hpe, map_smul]) (hπ' τ u x)
  have hBrow : ∀ τ u P x, B (cW τ u • rowSub V.rank τ u P) (π' τ u x) = B P x := fun τ u P x =>
    LinearMap.ext fun F => by
      rw [hB, hB, (hF F x).2.2, hpe, map_smul, ← hpe, ← hcW]
      exact GlobalTheory.T.definiteThetaIntegral_invariant_real_translate D ψ V W χS χT ω ν 𝓕 _ _ hω hM'.posDef hν h𝓕 (hpt P) (hF F x).1 (hF F x).2.1 _
        (GlobalTheory.PointAtPlaceHom.atTau_spec hθ W τ (hM'.unfr_mem τ u)).1
  have irr'' : IrrFam fun τ u => cW τ u • π' τ u := fun U h => irr' U fun τ u x hx =>
    (U.smul_mem_iff (hcW0 τ u)).1 (h τ u x hx)
  obtain ⟨L, hLB⟩ := exists_factor hrk irr'' (fun τ g => (cV τ g)⁻¹ • π τ g) It hIt.ne
    (fun τ u P x => by rw [← hrow τ u P x]; simp only [LinearMap.smul_apply, map_smul])
    (fun τ g P x => by
      rw [LinearMap.smul_apply, ← hcol, map_smul, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ (hcV0 τ g), one_smul])
    B (fun τ u P x => by rw [← hBrow τ u P x]; simp only [LinearMap.smul_apply, map_smul])

  have hspan : Submodule.span ℂ {y | ∃ P x, It P x = y} = ⊤ := by
    refine (irr _ fun τ g y hy => ?_).resolve_left fun e => hIt.ne (LinearMap.ext₂ fun P x => ?_)
    · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (π τ g) _)).2 ?_ hy)
      rintro _ ⟨P, x, rfl⟩
      exact Submodule.subset_span ⟨_, _, hcol τ g P x⟩
    · exact (Submodule.span_eq_bot.1 e) _ ⟨P, x, rfl⟩
  have hind : ∀ p : SmT M → Prop, (∀ P x, p (It P x)) → p 0 → (∀ x y, p x → p y → p (x + y)) → ∀ y, p y := by
    intro p h1 h2 h3 y
    have hy : y ∈ Submodule.span ℂ {y | ∃ P x, It P x = y} := hspan ▸ Submodule.mem_top
    suffices ∀ c : ℂ, p (c • y) by simpa using this 1
    induction hy using Submodule.span_induction with
    | mem _ h => obtain ⟨P, x, rfl⟩ := h; intro c; rw [← map_smul]; exact h1 _ _
    | zero => intro c; rwa [smul_zero]
    | add _ _ _ _ a b => intro c; rw [smul_add]; exact h3 _ _ (a c) (b c)
    | smul a _ _ h => intro c; rw [smul_smul]; exact h _
  have hshift : ∀ (k : GA D V) s F g, Lift.liftInt ν 𝓕 (thetaKO ω) s F (g * k) =
      Lift.liftInt ν 𝓕 (thetaKO ω) (ω (k, 1) s) F g := fun k s F g => by
    unfold Lift.liftInt thetaKO
    congr 1; funext h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hmem : ∀ F : C, L.flip F ∈ MultT θ M J χ := fun F => by
    have hlev : ∀ x, ∀ k ∈ J, ∀ g, L.flip F x (g * k) = χ k * L.flip F x g := by
      refine hind _ (fun P x k hk g => ?_) (fun k _ g => by simp) fun x y a b k hk g => by
        simp only [map_add (f := _), Pi.add_apply, a k hk g, b k hk g, mul_add]
      have e : ω (k, 1) (pt P) = χ k • pt P := by
        exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite ψ θ V W χS χT ω hθ hω (cart M) (cart M') (onb M) (onb M') f hpt k (hJ k hk).1 1 (one_mem _) _
          (hJ k hk).2 P
      have e2 : B (χ k • P) x F g = χ k * B P x F g := by rw [map_smul]; rfl
      rw [LinearMap.flip_apply, hLB, ← e2, hB, hB, hshift, hpe, hpe, e, pt.map_smul]
    refine GlobalTheory.T.mem_multT_of_equivariant' D θ V S M π J χ _ hθ hV hM (fun τ => ⟨(m1 τ).1, (m1 τ).2.1⟩) fd inj hπ (fun x => ⟨?_, ?_, ?_⟩) hlev
      fun τ g => ?_
    · revert x
      refine hind _ (fun P x γ hγ g => ?_) (fun γ _ g => by simp) fun x y a b γ hγ g => by
        simp only [map_add (f := _), Pi.add_apply, a γ hγ g, b γ hγ g]
      rw [LinearMap.flip_apply, hLB, hB]
      unfold Lift.liftInt
      congr 1; funext h
      rw [← (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hω _ (hpt P)).2 γ hγ 1 (one_mem _) g h, one_mul]
    · obtain ⟨U, hU1, hU2⟩ := hU
      exact ⟨U, hU1, fun k hk hk' g => by rw [hlev x k (hU2 k hk hk').1, (hU2 k hk hk').2, one_mul]⟩
    · revert x
      refine hind _ (fun P x => ?_) (by rw [map_zero]; exact continuous_const) fun x y a b => by
        rw [map_add (f := _)]; exact a.add b
      rw [LinearMap.flip_apply, hLB, hB]
      exact (hL F P x).2
    · refine hind _ (fun P x => ?_) (by rw [map_zero, map_zero]; rfl) fun x y a b => by
        rw [map_add (f := _), map_add (f := _), map_add (f := _), a, b]; rfl
      funext h
      rw [← hcol, LinearMap.flip_apply, LinearMap.flip_apply, hLB, hLB, hB, hB, rTr, hshift, hcV, hpe, hpe, map_smul]
  exact ⟨L.flip.codRestrict _ hmem, fun F φ v => (hL F φ v).1, fun F φ v g => by
    rw [← hB, ← hLB]; rfl⟩

end Lift

section Last

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
  Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem allPlus_of_le {D : D7} {V : HSp D} (P : TPar D) {j : ℕ} (hj : D.R.m - 1 ≤ j) (M : DSModel V (parB P j)) :
    AllPlus M := by
  intro τ a
  obtain ⟨-, q, -, hq⟩ := M.enum τ
  have h : (q a, M.ε τ a) ∈ parB P j τ := hq ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)
  simp only [parB, dualPar, TPar.Dpar, Finset.mem_image, Finset.mem_union, Finset.mem_biUnion, Prod.mk.injEq] at h
  obtain ⟨_, ⟨x, hx, rfl⟩, -, h⟩ := h
  rw [← h]
  rcases hx with (⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | ⟨i, -, y, -, rfl⟩
  · rfl
  · exact decide_eq_true (Or.inl (by have := i.2; omega))
  · rfl

theorem isFockVacAt_stepVec {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT LS χj Q ξ}
    {f₀ f : WO S T → ℂ} (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) (hf : IsThetaFunO ψ S T f) (τ) :
    IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := h
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf ho.infPart_eq ho.conj.infPart_eq hth hv.theta hf (hv.fock τ)

theorem exists_lift_last : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam →
    R.IsModels → R.chain_ωX → R.chain_vX → R.chain_ptX → R.chain_ItX →
    ∃ io, ({ R with ioX := io } : RealDat D A Ks).chain_ioX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL _ hM hω hv hpt hIt
  have h : IoXSt R := fun t => by
    obtain ⟨J', χ', hC⟩ := GlobalTheory.DefiniteEnd.endForms D G Pl0 T A Ks R hM.inf hM.cX hM.prX hM.HX t
    have hf : IsThetaFunO R.ψ _ _ (R.vX t) := by
      have := hpt t 1
      rwa [RealDat.ptX, GlobalTheory.FiniteFock.pureTensorO_one] at this
    refine ioExists_definite (J := levS _ (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)) (R.MY (D.R.m - 1)) R.MX hM.inf (hω t) (D.sp.Y_sig _) D.sp.X'_sig ?_
      (allPlus_of_le _ (le_min le_rfl (Nat.sub_le _ _)) _) (allPlus_of_le _ (Nat.sub_le _ _) _) (hpt t)
      (isFockVacAt_stepVec (hv t) hf) (hIt t) (fun κ hκ => ⟨hκ.1, ?_⟩) (GlobalTheory.GoodFiniteDim.exists_open_subgroup _ _ _)
      (hM.νX t).1.1 (hM.νX t).2 hC
    · rw [D.sp.Y_rank _ (min_le_right _ _), D.sp.X'_rank]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (min_le_right _ _)) _
    · exact SourceLaw.law_of_pair (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) R.βX (R.datXt t)
        (GlobalTheory.T.lastVector_lift_pair_flagLevel_characters R hL hM.inf hω hv t 1 κ 1 (SourceLaw.isLift_of_mem _ _ (R.datYt t (D.R.m - 1) R.triv) hκ)
          (SourceLaw.isLift_one _ _ (R.datXt t)))
  exact ⟨fun t => (h t).choose, fun t => (h t).choose_spec⟩

end Last

end GlobalTheory.DefLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStepStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicityLift_lastChainStep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.chain_ωX → R.chain_vX → R.chain_ptX → R.chain_ItX → ∃ io, ({ R with ioX := io } : RealDat D A Ks).chain_ioX := by
  first | exact @GlobalTheory.DefLift.exists_lift_last | exact GlobalTheory.DefLift.exists_lift_last | (intros; apply GlobalTheory.DefLift.exists_lift_last <;> assumption)
end
