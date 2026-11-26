module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomSpaceDualIsotropicMiddleDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestriction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorHeis

open GlobalTheory.SplitScalar GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

theorem wAt_wAt (p : Place D) (w : WO S T) : wAt p (wAt p w) = wAt p w := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p]

theorem wAt_off {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∉ P) :
    wAt p w = wAt p r := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [e, Finset.sum_eq_zero, zero_add]
  intro q hq
  rw [(GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q (fun hpq => hp (hpq ▸ hq)), zero_smul]

theorem wAt_on {P : Finset (Place D)} {w r : WO S T} (h : w = ∑ q ∈ P, wAt q w + r) {p : Place D} (hp : p ∈ P) :
    wAt p r = 0 := by
  have e : wAt p w = wAt p (∑ q ∈ P, wAt q w + r) := by rw [← h]
  simp only [wAt_eq_smul, smul_add, Finset.smul_sum, smul_smul] at e ⊢
  rw [Finset.sum_eq_single p (fun q _ hqp => by rw [(GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q (Ne.symm hqp), zero_smul])
    (fun hn => absurd hp hn), (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p] at e
  exact add_left_cancel (e.symm.trans (add_zero _).symm)

theorem symplO_wAt (p : Place D) (x y : WO S T) : symplO S T (wAt p x) y = symplO S T x (wAt p y) := by
  rw [wAt_eq_smul, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p]

private theorem symplO_sum_wAt_left (P : Finset (Place D)) (x y : WO S T) :
    symplO S T (∑ q ∈ P, wAt q x) y = ∑ q ∈ P, symplO S T (wAt q x) (wAt q y) := by
  induction P using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, GlobalTheory.SplitScalar.symplO_zero_left]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, GlobalTheory.LatVac.symplO_add_left, ih, ← symplO_wAt, wAt_wAt]

private theorem wAt_add' (p : Place D) (x y : WO S T) : wAt p (x + y) = wAt p x + wAt p y := by
  rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

theorem symplO_split {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplO S T w w' = ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') + symplO S T r r' := by
  have hr : ∀ q ∈ P, wAt q r = 0 := fun q hq => wAt_on h hq
  have hr' : ∀ q ∈ P, wAt q r' = 0 := fun q hq => wAt_on h' hq
  have hB : ∀ q ∈ P, wAt q (∑ q' ∈ P, wAt q' w') = wAt q w' := by
    intro q hq
    have e : wAt q w' = wAt q (∑ q' ∈ P, wAt q' w' + r') := by rw [← h']
    rw [wAt_add', hr' q hq, add_zero] at e
    exact e.symm
  have s1 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q (∑ q' ∈ P, wAt q' w')) =
      ∑ q ∈ P, symplO S T (wAt q w) (wAt q w') :=
    Finset.sum_congr rfl fun q hq => by rw [hB q hq]
  have s2 : ∑ q ∈ P, symplO S T (wAt q w) (wAt q r') = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr' q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  have s3 : ∑ q ∈ P, symplO S T (wAt q w') (wAt q r) = 0 :=
    Finset.sum_eq_zero fun q hq => by rw [hr q hq, GlobalTheory.SplitScalar.symplO_zero_right]
  conv_lhs => rw [h, h']
  rw [GlobalTheory.LatVac.symplO_add_left, GlobalTheory.LatVac.symplO_add_right, GlobalTheory.LatVac.symplO_add_right,
    symplO_sum_wAt_left, symplO_sum_wAt_left, GlobalTheory.SplitScalar.symplO_skew S T (∑ q ∈ P, wAt q w') r,
    symplO_sum_wAt_left, s1, s2, s3, add_zero, neg_zero, zero_add]

variable {ψ : AddChar (AF D.host.F) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem cocycle_two (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {u u' : WO S T}
    (hu : u ∈ latO S T ΛS ΛT fun _ => True) (hu' : u' ∈ latO S T ΛS ΛT fun _ => True) :
    ψ (symplOH S T (2 • u) (2 • u')) = 1 := by
  have hd : ψ (symplO S T u u') = 1 :=
    ((GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hS hT).1 u (GlobalTheory.SplitScalar.latO_fin hu)).mp hu u' hu'
  rw [two_nsmul, two_nsmul, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_right,
    GlobalTheory.SplitScalar.symplOH_add_self, AddChar.map_add_eq_mul, hd, one_mul]

theorem wAt_mem {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) (p : Place D) :
    wAt p u ∈ latO S T ΛS ΛT fun _ => True :=
  latO_mono (fun _ _ => trivial) (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).1

theorem wAt_two (p : Place D) (u : WO S T) : wAt p (2 • u) = 2 • wAt p u := by
  rw [two_nsmul, two_nsmul, wAt_eq_smul, wAt_eq_smul, smul_add]

private theorem eq_zero_of_add_self_eq_zero_AF {a : AF D.host.F} (h : a + a = 0) : a = 0 := by
  have h2 : IsUnit (2 : AF D.host.F) := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  rw [← two_mul] at h
  exact h2.mul_right_eq_zero.mp h

private theorem symplOH_eq_sum_wAt_add_of_decomp {P : Finset (Place D)} {w r w' r' : WO S T} (h : w = ∑ q ∈ P, wAt q w + r)
    (h' : w' = ∑ q ∈ P, wAt q w' + r') :
    symplOH S T w w' = ∑ q ∈ P, symplOH S T (wAt q w) (wAt q w') + symplOH S T r r' := by
  apply sub_eq_zero.mp
  apply eq_zero_of_add_self_eq_zero_AF
  rw [sub_add_sub_comm, GlobalTheory.SplitScalar.symplOH_add_self, add_add_add_comm, ← Finset.sum_add_distrib]
  simp only [GlobalTheory.SplitScalar.symplOH_add_self]
  rw [symplO_split h h', sub_self]

private theorem addChar_sum_eq_prod' (ψ : AddChar (AF D.host.F) ℂ) (s : Finset (Place D)) (g : Place D → AF D.host.F) :
    ψ (∑ p ∈ s, g p) = ∏ p ∈ s, ψ (g p) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, AddChar.map_add_eq_mul, ih]

theorem cocycle_prod (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (w w' : WO S T) :
    ∃ P : Finset (Place D), (∀ p ∉ P, ψ (symplOH S T (wAt p w) (wAt p w')) = 1) ∧
      ψ (symplOH S T w w') = ∏ p ∈ P, ψ (symplOH S T (wAt p w) (wAt p w')) := by
  classical
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w'
  obtain ⟨u, hu, hw⟩ := hP₀ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_left _ hx)
  obtain ⟨u', hu', hw'⟩ := hP₁ (P₀ ∪ P₁) (fun _ hx => Finset.mem_union_right _ hx)
  refine ⟨P₀ ∪ P₁, fun p hp => ?_, ?_⟩
  · rw [wAt_off hw hp, wAt_off hw' hp, wAt_two, wAt_two]
    exact cocycle_two hψ hS hT (wAt_mem hu p) (wAt_mem hu' p)
  · rw [symplOH_eq_sum_wAt_add_of_decomp hw hw', AddChar.map_add_eq_mul, cocycle_two hψ hS hT hu hu', mul_one,
      addChar_sum_eq_prod']

theorem isPure_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ w : WO S T, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => heisO ψ S T (wAt p w) (x p)) (heisO ψ S T w f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx w
  classical
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hB' := hB
  unfold IsBase at hB'
  have hS : IsSelfDualC S ΛS := hB'.2.2.1
  have hT : IsSelfDualC T ΛT := hB'.2.2.2.1
  have laws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  unfold IsPure IsRestricted at hx ⊢
  obtain ⟨⟨hloc, hfin⟩, hf, hprod⟩ := hx
  have hxθ : ∀ p, IsThetaFunO ψ S T (x p) := fun p => by
    have hl := hloc p
    unfold IsLocal at hl
    exact hl.1
  have hneg : ∀ (p : Place D) (a : WO S T), wAt p (-a) = -wAt p a := fun p a => by
    rw [wAt_eq_smul, wAt_eq_smul, smul_neg]
  have hadd : ∀ (p : Place D) (a b : WO S T), wAt p (a + b) = wAt p a + wAt p b := fun p a b => by
    rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT hS hT w
  obtain ⟨u, hu, hwu⟩ := hP₀ P₀ (Finset.Subset.refl _)
  have hvac : ∀ p, p ∉ P₀ → (∀ τ, p ≠ .inr τ) → heisO ψ S T (wAt p w) f₀ = f₀ := by
    intro p hp hτ
    rcases p with v | τ
    · have hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt hB (.inl v)
      rw [wAt_off hwu hp, wAt_two]
      refine hv.1 _ (latO_mono ?_ (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inl v)).1)
      rintro v' ⟨-, hv'⟩
      exact Sum.inl_injective hv'
    · exact absurd rfl (hτ τ)
  have hfinV : {p : Place D | heisO ψ S T (wAt p w) f₀ ≠ f₀}.Finite := by
    refine ((P₀.finite_toSet).union (Set.finite_range (Sum.inr : D.what₂.Tau → Place D))).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_range, not_or, not_exists] at hc
    exact hp (hvac p hc.1 fun τ h => hc.2 τ h.symm)
  refine ⟨⟨fun p => ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x p) (hxθ p)).2 p (hloc p)).1 w, ?_⟩,
    laws.1 w f hf, fun w' => ?_⟩
  · refine (hfin.union hfinV).subset ?_
    intro p hp
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hp
    show heisO ψ S T (wAt p w) (x p) = f₀
    rw [hc.1, hc.2]

  have hfac : ∀ p, ipO μ 𝓕 (heisO ψ S T (wAt p w) (x p)) (heisO ψ S T (wAt p w') f₀) =
      (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w'))) *
        ipO μ 𝓕 (x p) (heisO ψ S T (wAt p (-w + w')) f₀) := by
    intro p
    have I := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p (-w + w')) f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    have J := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x p) (heisO ψ S T (wAt p w') f₀) (hxθ p) (laws.1 _ f₀ hf₀)
    rw [(J.2.2.2.2.2.2.1 (wAt p w)).2, laws.2.1, ← hneg, ← hadd, (I.2.2.1 _).2]
  obtain ⟨P, hP1, hP2⟩ := cocycle_prod hψ hS hT (-w) w'
  have hcfin : (Function.mulSupport fun p => (starRingEnd ℂ) (ψ (symplOH S T (wAt p (-w)) (wAt p w')))) ⊆ ↑P := by
    intro p hp
    by_contra hc
    simp only [Function.mem_mulSupport] at hp
    exact hp (by rw [hP1 p (fun h => hc (Finset.mem_coe.mpr h)), map_one])
  have hgfin := (hprod (-w + w')).1
  beta_reduce
  simp only [hfac]
  refine ⟨((P.finite_toSet.subset hcfin).union hgfin).subset (Function.mulSupport_mul _ _), ?_⟩
  have K0 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w' f₀) hf (laws.1 _ _ hf₀)
  have K1 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T (-w + w') f₀) hf (laws.1 _ _ hf₀)
  rw [(K0.2.2.2.2.2.2.1 w).2, laws.2.1, (K1.2.2.1 _).2, (hprod (-w + w')).2, hP2, map_prod,
    finprod_mul_distrib (P.finite_toSet.subset hcfin) hgfin, finprod_eq_prod_of_mulSupport_subset _ hcfin]

end GlobalTheory.PlaceTensorHeis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ w : WO S T, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => heisO ψ S T (wAt p w) (x p)) (heisO ψ S T w f) := by
  first | exact @GlobalTheory.PlaceTensorHeis.isPure_heisO | exact GlobalTheory.PlaceTensorHeis.isPure_heisO | (intros; apply GlobalTheory.PlaceTensorHeis.isPure_heisO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaDecay

variable {D : D7}

theorem omO_of_single (V W : HSp D) (τ : D.what₂.Tau) (x y : GlobalTheory.FockCompare.RW W V) (hy : ∀ b, b ≠ τ → y b = 0) :
    GlobalTheory.OrientedHeis.omO V W y x = GlobalTheory.OrientedHeis.formAt V W τ (y τ) (x τ) := by
  show ∑ b, GlobalTheory.OrientedHeis.formAt V W b (y b) (x b) = _
  refine Finset.sum_eq_single τ (fun b _ hb => ?_) (by simp)
  rw [hy b hb]
  simp [GlobalTheory.OrientedHeis.formAt]

theorem omO_piW_lineAt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (V W : HSp D) (ξ : WO V W) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    GlobalTheory.OrientedHeis.omO V W (GlobalTheory.FockCompare.piW θ W V ξ) (GlobalTheory.FockCompare.piW θ W V (lineAt θ τ z 1)) =
      -symplAt V W τ z (compAt θ τ ξ) := by
  have skew : ∀ x y, GlobalTheory.OrientedHeis.omO V W x y = -GlobalTheory.OrientedHeis.omO V W y x := fun x y => by
    have e := GlobalTheory.OrientedHeis.omO_self (S := V) (T := W) h (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, GlobalTheory.OrientedHeis.omO_self h] at e
    linarith
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt h.inf (m := W.rank) (n := V.rank) τ z
  have hc : ∀ b, GlobalTheory.FockCompare.piW θ W V (lineAt θ τ z 1) b = compAt θ b (lineAt θ τ z 1) := fun b => rfl
  rw [skew, omO_of_single V W τ _ _ (fun b hb => by rw [hc, hL.2.2 1 b, if_neg hb]; rfl), hc, hL.2.2 1 τ, if_pos rfl,
    Complex.ofReal_one, one_smul]
  exact congrArg Neg.neg (GlobalTheory.OrientedRealForm.formAt_eq V W τ z (compAt θ τ ξ))

theorem psi_symplOH_lineAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) (V W : HSp D) (ξ : WO V W) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (t : ℝ) :
    ψ (symplOH V W ξ (lineAt θ τ z t)) =
      Complex.exp ((Real.pi * Complex.I) * ((t * symplAt V W τ z (compAt θ τ ξ) : ℝ) : ℂ)) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (GlobalTheory.FockCompare.smooth_iff_sm_and_real_lines D θ σ h W V).2.1 _
    (GlobalTheory.OrientedHeis.isRealDir_lineAt (S := V) (T := W) hθ τ z) t
  rw [e, GlobalTheory.OrientedHeis.psi_symplOH h hψ, LinearMap.map_smul, smul_eq_mul, omO_piW_lineAt h]
  congr 1
  push_cast
  ring

theorem dRho_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (ξ : WO V W) {H : WO V W → ℂ}
    (hH : IsThetaFunO ψ V W H) :
    dRho (heisO ψ V W) θ τ z (heisO ψ V W ξ H) =
      heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z H) +
        (-(2 * Real.pi * Complex.I) * (symplAt V W τ z (compAt θ τ ξ) : ℂ)) • heisO ψ V W ξ H := by
  have hA := (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ
  have hU := hA.2.1
  have hDS := ((hA.2.2 θ hθ).1 τ z).1 H hH
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  set a := symplAt V W τ z (compAt θ τ ξ) with ha
  set c : ℂ := -(2 * Real.pi * Complex.I) * (a : ℂ) with hc
  funext x
  let g : ℝ → ℂ := fun t => heisO ψ V W ξ (heisO ψ V W (lineAt θ τ z t) H) x
  have hfun : (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) (heisO ψ V W ξ H) x) =
      fun t : ℝ => Complex.exp (c * (t : ℂ)) * g t := by
    funext t
    simp only [g]
    rw [hU.1 (lineAt θ τ z t) ξ H, hU.1 ξ (lineAt θ τ z t) H, add_comm (lineAt θ τ z t) ξ, skew ξ,
      Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, AddChar.map_neg_eq_inv,
      psi_symplOH_lineAt hψ hθ V W ξ τ z t, ← Complex.exp_neg, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hc]
    push_cast
    ring
  have hg : HasDerivAt g (ψ (symplOH V W x ξ) * dRho (heisO ψ V W) θ τ z H (x + ξ)) 0 :=
    (hDS (x + ξ)).const_mul _
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (Complex.exp (c * ((0 : ℝ) : ℂ)) * (c * 1)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul c).cexp
  have hg0 : g 0 = heisO ψ V W ξ H x := by
    simp only [g, map_zero]
    unfold heisO
    rw [GlobalTheory.ThetaSquare.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  show deriv (fun t : ℝ => heisO ψ V W (lineAt θ τ z t) (heisO ψ V W ξ H) x) 0 = _
  rw [hfun]
  refine (hexp.mul hg).deriv.trans ?_
  rw [hg0]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  show _ = ψ (symplOH V W x ξ) * dRho (heisO ψ V W) θ τ z H (x + ξ) + _
  ring

theorem pow_bound {X F : Type*} (P : F → Prop) (Dop : F → F) (B : X → F → F → ℂ) (a : X → ℝ)
    (hD : ∀ G, P G → P (Dop G)) (h0 : ∀ G G', P G → P G' → ∃ C : ℝ, ∀ ξ, ‖B ξ G G'‖ ≤ C)
    (h1 : ∀ ξ G G', P G → P G' → |a ξ| * ‖B ξ G G'‖ ≤ ‖B ξ G (Dop G')‖ + ‖B ξ (Dop G) G'‖) :
    ∀ (m : ℕ) (G G' : F), P G → P G' → ∃ C : ℝ, ∀ ξ, |a ξ| ^ m * ‖B ξ G G'‖ ≤ C := by
  intro m
  induction m with
  | zero =>
    intro G G' hG hG'
    obtain ⟨C, hC⟩ := h0 G G' hG hG'
    exact ⟨C, fun ξ => by simpa using hC ξ⟩
  | succ m ih =>
    intro G G' hG hG'
    obtain ⟨C₁, hC₁⟩ := ih G (Dop G') hG (hD _ hG')
    obtain ⟨C₂, hC₂⟩ := ih (Dop G) G' (hD _ hG) hG'
    refine ⟨C₁ + C₂, fun ξ => ?_⟩
    calc |a ξ| ^ (m + 1) * ‖B ξ G G'‖ = |a ξ| ^ m * (|a ξ| * ‖B ξ G G'‖) := by ring
      _ ≤ |a ξ| ^ m * (‖B ξ G (Dop G')‖ + ‖B ξ (Dop G) G'‖) :=
        mul_le_mul_of_nonneg_left (h1 ξ G G' hG hG') (by positivity)
      _ = |a ξ| ^ m * ‖B ξ G (Dop G')‖ + |a ξ| ^ m * ‖B ξ (Dop G) G'‖ := by ring
      _ ≤ C₁ + C₂ := add_le_add (hC₁ ξ) (hC₂ ξ)

theorem norm_coef_le {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    {V W : HSp D} {ν : Measure (WO V W)} {𝓕 : Set (WO V W)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (ξ : WO V W) {G G' : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (hG' : IsThetaFunO ψ V W G') :
    |symplAt V W τ z (compAt θ τ ξ)| * ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤
      ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (dRho (heisO ψ V W) θ τ z G' x) ∂ν‖ +
        ‖∫ x in 𝓕, heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G) x * star (G' x) ∂ν‖ := by
  have hA := (GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ
  have hU := hA.2.1
  have hDS := (hA.2.2 θ hθ).1 τ z
  have hDG := hDS.2.1 G hG
  have e := hDS.2.2 ν 𝓕 hν h𝓕 (heisO ψ V W ξ G) G' (hU.2.2.1 ξ G hG) hG'
  rw [dRho_heisO hψ hθ τ z ξ hG] at e
  set a := symplAt V W τ z (compAt θ τ ξ) with ha
  set c : ℂ := -(2 * Real.pi * Complex.I) * (a : ℂ) with hc
  have hI1 := GlobalTheory.Size.integrableOn_mul_conj hψ hν h𝓕 (hU.2.2.1 ξ _ hDG) hG'
  have hI2 := GlobalTheory.Size.integrableOn_mul_conj hψ hν h𝓕 (hU.2.2.1 ξ _ hG) hG'
  have hsplit : GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G) + c • heisO ψ V W ξ G) G' =
      GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G)) G' + c * GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G' := by
    unfold GlobalTheory.Ker.ipO
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
    rw [integral_add hI1 (hI2.const_mul c), integral_const_mul]
  rw [hsplit] at e
  have e2 : c * GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G' =
      -GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) (dRho (heisO ψ V W) θ τ z G') -
        GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G)) G' := by
    linear_combination e
  have hn : ‖c‖ = 2 * Real.pi * |a| := by
    rw [hc, norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  have h3 : ‖c‖ * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ ≤
      ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) (dRho (heisO ψ V W) θ τ z G')‖ +
        ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ (dRho (heisO ψ V W) θ τ z G)) G'‖ := by
    rw [← norm_mul, e2, sub_eq_add_neg, ← neg_add]
    rw [norm_neg]
    exact norm_add_le _ _
  have h4 : |a| * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ ≤ ‖c‖ * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ := by
    rw [hn]
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h0 : 0 ≤ |a| * ‖GlobalTheory.Ker.ipO ν 𝓕 (heisO ψ V W ξ G) G'‖ := by positivity
    nlinarith
  exact h4.trans h3

theorem norm_coef_bdd {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D}
    {ν : Measure (WO V W)} {𝓕 : Set (WO V W)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) {G G' : WO V W → ℂ} (hG : IsThetaFunO ψ V W G)
    (hG' : IsThetaFunO ψ V W G') :
    ∃ C : ℝ, ∀ ξ : WO V W, ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤ C := by
  have hSI := ((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).1
  obtain ⟨a, ha⟩ := (hSI G hG).2.1
  obtain ⟨b, hb⟩ := (hSI G' hG').2.1
  have hfin : ν 𝓕 < ⊤ := lt_top_iff_ne_top.2 (GlobalTheory.Size.measure_dom hν h𝓕).2
  refine ⟨a * b * (ν 𝓕).toReal, fun ξ => ?_⟩
  refine norm_setIntegral_le_of_norm_le_const hfin fun x _ => ?_
  rw [norm_mul, norm_star, GlobalTheory.ThetaSquare.norm_heisO hψ]
  exact mul_le_mul (ha _) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha 0))

theorem coef_decay : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∀ θ : InfFam D, IsInfFam θ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ ξ : WO V W, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ ξ)| ^ m * ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤ C := by
  intro D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG' θ hθ τ z m
  have hDS := (((GlobalTheory.ThetaSquare.thetaFunctions_squareIntegrable_heisenbergUnitary D V W).2 ψ hψ).2.2 θ hθ).1 τ z
  exact pow_bound (IsThetaFunO ψ V W) (dRho (heisO ψ V W) θ τ z)
    (fun ξ F F' => ∫ x in 𝓕, heisO ψ V W ξ F x * star (F' x) ∂ν) (fun ξ => symplAt V W τ z (compAt θ τ ξ))
    (fun F hF => hDS.2.1 F hF) (fun F F' hF hF' => norm_coef_bdd hψ hν h𝓕 hF hF')
    (fun ξ F F' hF hF' => norm_coef_le hψ hθ hν h𝓕 τ z ξ hF hF') m G G' hG hG'

end GlobalTheory.ThetaDecay

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctionalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMatrixCoeff_rapid_decay_real_functional : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∀ θ : InfFam D, IsInfFam θ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (m : ℕ), ∃ C : ℝ, ∀ ξ : WO V W, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt V W τ z (compAt θ τ ξ)| ^ m * ‖∫ x in 𝓕, heisO ψ V W ξ G x * star (G' x) ∂ν‖ ≤ C := by
  first | exact @GlobalTheory.ThetaDecay.coef_decay | exact GlobalTheory.ThetaDecay.coef_decay | (intros; apply GlobalTheory.ThetaDecay.coef_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalarAnnih

open IsDedekindDomain GlobalTheory.Idele
open scoped nonZeroDivisors

theorem exists_compact_annihilator_finiteAdeles_traceChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hc : Continuous ψ)
    (hfin : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)))
    (O : Set (Af F)) (hO : O ∈ nhds (0 : Af F)) : ∃ K : Set (Af F), IsCompact K ∧
      ∀ x : Af F, (∀ t ∈ O, ψ (pairA F 0 (t * x)) = 1) → x ∈ K := by
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O hO
  obtain ⟨t, ht⟩ := exists_idealOf_eq (GlobalTheory.StdDual.codiff_ne_zero (F := F))
  let c : Af F := algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F)
  refine ⟨(fun a => c * a) '' {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F},
    (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id), ?_⟩
  intro x hx
  have h1 : (N : Af F) * x ∈ adelicIdeal (GlobalTheory.StdDual.codiff F) := by
    rw [GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hc hfin]
    intro α hα
    have := hx _ (hNO α hα)
    rwa [nsmul_eq_mul, mul_assoc, mul_left_comm] at this
  have h2 : (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x)) ∈
      adelicIdeal (t • (1 : FractionalIdeal (𝓞 F)⁰ F)) := by
    rw [Units.mul_inv_cancel_left, smul_one_eq, ht]; exact h1
  rw [mul_mem_adelicIdeal_smul, mem_adelicIdeal] at h2
  refine ⟨_, fun v => (mem_localIdeal_one_iff v _).1 (h2 v), ?_⟩
  have hN0 : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e : algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) = 1 := by
    rw [← map_natCast (algebraMap F (Af F)) N, ← map_mul, inv_mul_cancel₀ hN0, map_one]
  simp only [c]
  calc algebraMap F (Af F) ((N : F)⁻¹) * (t : Af F) * (((t⁻¹ : (Af F)ˣ) : Af F) * ((N : Af F) * x))
      = algebraMap F (Af F) ((N : F)⁻¹) * (N : Af F) * x := by
        rw [mul_assoc, Units.mul_inv_cancel_left, mul_assoc]
    _ = x := by rw [e, one_mul]

theorem exists_compact_of_annih : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧
      ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K :=
  fun D ψ hψ O hO =>
    exists_compact_annihilator_finiteAdeles_traceChar D.host.F ψ hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) O hO

end GlobalTheory.ScalarAnnih

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_annihilator_finiteAdeles_stdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧ ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K := by
  first | exact @GlobalTheory.ScalarAnnih.exists_compact_of_annih | exact GlobalTheory.ScalarAnnih.exists_compact_of_annih | (intros; apply GlobalTheory.ScalarAnnih.exists_compact_of_annih <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCost
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCost
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped ENNReal

namespace GlobalTheory.Size.SupWord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OrientedHeis

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {f f' : WO V W → ℂ}
  {p : (WO V W → ℂ) → ℝ≥0∞}

theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool))
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') :
    wordAct (heisDer ψ θ) l (f + f') = wordAct (heisDer ψ θ) l f + wordAct (heisDer ψ θ) l f' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, wordAct_cons, wordAct_cons, ih]
    exact dRho_add hψ hθ a.1 _ (theta_word hψ hθ l h) (theta_word hψ hθ l h')

theorem word_smul (l : List (D.what₂.Tau × Fin W.rank × Fin V.rank × Bool)) (c : ℂ) (f : WO V W → ℂ) :
    wordAct (heisDer ψ θ) l (c • f) = c • wordAct (heisDer ψ θ) l f :=
  wordAct_rel (R := fun g g' => g = c • g') l (fun a _ _ _ e => e ▸ dRho_smul a.1 _ c _) rfl

theorem ws_add_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W f') (k : ℕ) :
    wordSum (heisDer ψ θ) p k (f + f') ≤ wordSum (heisDer ψ θ) p k f + wordSum (heisDer ψ θ) p k f' :=
  wordSum_le_add fun l => by rw [word_add hψ hθ l h h']; exact hp _ _

theorem ws_smul (hp : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) (k : ℕ) (c : ℂ) (f : WO V W → ℂ) :
    wordSum (heisDer ψ θ) p k (c • f) = ‖c‖ₑ * wordSum (heisDer ψ θ) p k f :=
  wordSum_eq_mul fun l => by rw [word_smul]; exact hp _ _

theorem ws_sum_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (hs : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ}
    (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) (k : ℕ) :
    wordSum (heisDer ψ θ) p k (∑ i ∈ s, g i) ≤ ∑ i ∈ s, wordSum (heisDer ψ θ) p k (g i) := by
  refine Finset.le_sum_of_subadditive_on_pred (wordSum (heisDer ψ θ) p k) (IsThetaFunO ψ V W) ?_
    (fun _ _ a b => ws_add_le hψ hθ hp a b k) (fun _ _ => theta_add) g hg
  have := ws_smul (ψ := ψ) (θ := θ) hs k 0 (0 : WO V W → ℂ)
  rw [zero_smul, enorm_zero, zero_mul] at this
  simp [this]

theorem ws_dRho_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hp : ∀ g g', p (g + g') ≤ p g + p g')
    (hs : ∀ (c : ℂ) g, p (c • g) = ‖c‖ₑ * p g) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (k : ℕ) :
    wordSum (heisDer ψ θ) p k (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) ≤
      ENNReal.ofReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)) * wordSum (heisDer ψ θ) p (k + 1) f := by
  have ht : ∀ (c : ℂ) a, IsThetaFunO ψ V W (c • heisDer ψ θ a f) := fun c a =>
    theta_smul c (theta_dRho hθ hψ a.1 _ hf)
  have hb : ∀ (c : ℝ) a, wordSum (heisDer ψ θ) p k ((c : ℂ) • heisDer ψ θ a f) ≤
      ENNReal.ofReal |c| * wordSum (heisDer ψ θ) p (k + 1) f := fun c a => by
    rw [ws_smul hs, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact wordSum_letter_le k a f
  rw [dRho_eq_sum_heisDer hψ hθ hf, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (ws_sum_le hψ hθ hp hs _ (fun i _ => theta_finsetSum _ fun j _ => theta_add (ht _ _) (ht _ _)) k).trans
    (Finset.sum_le_sum fun i _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, Finset.sum_mul]
  refine (ws_sum_le hψ hθ hp hs _ (fun j _ => theta_add (ht _ _) (ht _ _)) k).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), add_mul]
  exact (ws_add_le hψ hθ hp (ht _ _) (ht _ _) k).trans (add_le_add (hb _ _) (hb _ _))

theorem supN_add_le (g g' : WO V W → ℂ) : (⨆ w, ‖(g + g') w‖ₑ) ≤ (⨆ w, ‖g w‖ₑ) + ⨆ w, ‖g' w‖ₑ :=
  iSup_le fun w => (enorm_add_le (g w) (g' w)).trans (add_le_add (le_iSup (fun w => ‖g w‖ₑ) w)
    (le_iSup (fun w => ‖g' w‖ₑ) w))

theorem supN_smul (c : ℂ) (g : WO V W → ℂ) : (⨆ w, ‖(c • g) w‖ₑ) = ‖c‖ₑ * ⨆ w, ‖g w‖ₑ := by
  simp only [Pi.smul_apply, enorm_smul, ENNReal.mul_iSup]

theorem wordSum_sup_sub_and_derAlong :
    ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → (∀ (G H : WO V W → ℂ) (c : ℂ) (k : ℕ), IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (G - c • H) ≤ GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G + ‖c‖ₑ * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k H) ∧ ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E), ∃ c : ℝ, 0 ≤ c ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ k : ℕ, GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (derAlong ψ θ V W C x G) ≤ ENNReal.ofReal c * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (k + 1) G := by
  intro D V W ψ hψ θ hθ
  have ha : ∀ g g' : WO V W → ℂ, (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (g + g') ≤
      (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g + (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g' := supN_add_le
  have hs : ∀ (c : ℂ) (g : WO V W → ℂ), (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (c • g) =
      ‖c‖ₑ * (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) g := supN_smul
  refine ⟨fun G H c k hG hH => ?_, fun r C x => ?_⟩
  · rw [sub_eq_add_neg, ← neg_smul]
    refine (ws_add_le hψ hθ ha hG (theta_smul _ hH) k).trans ?_
    rw [ws_smul hs, enorm_neg]
  · refine ⟨∑ τ, ∑ i, ∑ j, (|(dirAt V W C τ (x.map (tauE D τ)) i j).re| +
      |(dirAt V W C τ (x.map (tauE D τ)) i j).im|), by positivity, fun G hG k => ?_⟩
    unfold derAlong
    refine (ws_sum_le hψ hθ ha hs _ (fun τ _ => theta_dRho hθ hψ τ _ hG) k).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun τ _ => by positivity), Finset.sum_mul]
    exact Finset.sum_le_sum fun τ _ => ws_dRho_le hψ hθ ha hs hG τ _ k

end GlobalTheory.Size.SupWord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCostStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supNormWordSum_sub_le_and_derivative_cost : ∀ (D : D7) (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → (∀ (G H : WO V W → ℂ) (c : ℂ) (k : ℕ), IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (G - c • H) ≤ GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k G + ‖c‖ₑ * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k H) ∧ ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E), ∃ c : ℝ, 0 ≤ c ∧ ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ k : ℕ, GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) k (derAlong ψ θ V W C x G) ≤ ENNReal.ofReal c * GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO V W → ℂ => ⨆ w, ‖φ w‖ₑ) (k + 1) G := by
  first | exact @GlobalTheory.Size.SupWord.wordSum_sup_sub_and_derAlong | exact GlobalTheory.Size.SupWord.wordSum_sup_sub_and_derAlong | (intros; apply GlobalTheory.Size.SupWord.wordSum_sup_sub_and_derAlong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointInjOfParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjointInjectiveOfParts

theorem adjoint_inj_of_parts {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (T : H' →ₗ[ℂ] H) {ι : Type*}
    (P : ι → Submodule ℂ H) (s : ι → ℂ) (hs : ∀ c, s c ≠ 0)
    (hP : ∀ c, ∀ x ∈ P c, T (LinearMap.adjoint T x) = s c • x) {x : H} (hx : x ∈ ⨆ c, P c)
    (h0 : LinearMap.adjoint T x = 0) : x = 0 := by
  have hle : (⨆ c, P c) ≤ LinearMap.range T := by
    refine iSup_le fun c y hy => ⟨LinearMap.adjoint T ((s c)⁻¹ • y), ?_⟩
    rw [hP c _ ((P c).smul_mem _ hy), smul_smul, mul_inv_cancel₀ (hs c), one_smul]
  obtain ⟨w, rfl⟩ := hle hx
  have h1 : ⟪T w, T w⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_right, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

end GlobalTheory.AdjointInjectiveOfParts


open GlobalTheory.Hk3 in
theorem GlobalTheory.LiftRows.upInj_of_scal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, GlobalTheory.Hk3.IsSF R SF → Scal R SF → UpInj R ∧ UpInjW R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hI SF hSF hScal
  obtain ⟨lam, κ, hκ, hl, hW, hE⟩ := hScal
  constructor
  · intro t
    refine (injective_iff_map_eq_zero _).2 fun x h0 => ?_
    obtain ⟨h, -, -, hsp, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R F hC hS SF hSF
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.Th t) (fun c => EEc R SF c)
      (fun c => ((κ * ∏ i, lam i t c : ℝ) : ℂ))
      (fun c => Complex.ofReal_ne_zero.2 (mul_pos hκ (Finset.prod_pos fun i _ => hl i t c)).ne')
      (fun c x hx => hE t c x hx) ?_ h0
    rw [hsp]; trivial
  · intro i t x hx h0
    obtain ⟨h, -, -, -, hsp, -⟩ := GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hI SF hSF i
    refine GlobalTheory.AdjointInjectiveOfParts.adjoint_inj_of_parts (R.thG i t) (fun c => Wcc R SF i c)
      (fun c => ((lam i t c : ℝ) : ℂ)) (fun c => Complex.ofReal_ne_zero.2 (hl i t c).ne')
      (fun c x hx => hW i t c x hx) ?_ h0
    rw [hsp]; exact ⟨x, hx⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

variable {D : D7}

def halfPair (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) : AE D :=
  ∑ i, ∑ j, ∑ k, cA D (a k j) * incA D (W.gram k i) * t i j

def halfSympl (W : HSp D) {r : ℕ} (a t : Mx D W.rank r) : AF D.host.F :=
  Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * halfPair W a t)

theorem halfSympl_add_right (W : HSp D) {r : ℕ} (a t t' : Mx D W.rank r) :
    halfSympl W a (t + t') = halfSympl W a t + halfSympl W a t' := by
  simp only [halfSympl, halfPair]
  rw [← map_add (f := _), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_add]

theorem halfSympl_add_left (W : HSp D) {r : ℕ} (a a' t : Mx D W.rank r) :
    halfSympl W (a + a') t = halfSympl W a t + halfSympl W a' t := by
  simp only [halfSympl, halfPair]
  rw [← map_add (f := _), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [add_mul]

theorem halfSympl_zero_right (W : HSp D) {r : ℕ} (a : Mx D W.rank r) : halfSympl W a 0 = 0 := by
  simp [halfSympl, halfPair]

theorem halfSympl_zero_left (W : HSp D) {r : ℕ} (t : Mx D W.rank r) : halfSympl W 0 t = 0 := by
  simp [halfSympl, halfPair]

end GlobalTheory.HalfAverage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftDat

open GlobalTheory.LiftLevel

variable {D : D7}

def rowAdj (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (v : Fin T.rank → D.host.E) :
    Matrix (Fin 1) (Fin T.rank) (EAf D) :=
  toEAf D a • HMul.hMul ((Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] v k) * incA D (T.gram k l)).map (toEAf D)) βT.val

def rowRed (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E)
    (v : Fin T.rank → D.host.E) : Fin T.rank → Formalism.L2.DIV.kP PP :=
  fun j => redM PP (rowAdj T βT a e v) 0 j

theorem liftI_le {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ Pg ∪ Q) :
    liftI Pg Q ≤ conjI PP.asIdeal :=
  Ideal.prod_le_inf.trans (Finset.inf_le h)

def toConj (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (h : PP ∈ Pg ∪ Q) :
    𝓞 D.host.E ⧸ liftI Pg Q →+* 𝓞 D.host.E ⧸ conjI PP.asIdeal :=
  Ideal.quotientMap (conjI PP.asIdeal) (RingHom.id _) (fun _ hx => liftI_le h hx)

def conjRes (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (h : PP ∈ Pg ∪ Q) :
    𝓞 D.host.E ⧸ liftI Pg Q →+* Formalism.L2.DIV.kP PP :=
  Ideal.quotientMap PP.asIdeal GlobalTheory.SW.Lev.bar (fun _ hx => GlobalTheory.SW.Lev.mem_conjI.1 (liftI_le h hx))

def Jgrp (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ) : Subgroup (GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q)) :=
  ⨅ PP : Pg, (Matrix.GeneralLinearGroup.map (toConj Pg Q PP.1 (Finset.mem_union_left _ PP.2))).ker

def lamHom (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) : Jgrp Pg Q r →* ℂˣ :=
  (∏ PP ∈ Q.attach, (ξ PP.1).comp ((Units.map (conjRes Pg Q PP.1 (Finset.mem_union_right _ PP.2)).toMonoidHom).comp
    (Matrix.GeneralLinearGroup.det.comp (Jgrp Pg Q r).subtype)))⁻¹

theorem mem_Jgrp {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ} {κ : GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q)} :
    κ ∈ Jgrp Pg Q r ↔ ∀ PP (h : PP ∈ Pg),
      Matrix.GeneralLinearGroup.map (toConj Pg Q PP (Finset.mem_union_left _ h)) κ = 1 := by
  simp [Jgrp, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem lamHom_apply {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ}
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (κ : Jgrp Pg Q r) :
    lamHom Pg Q r ξ κ = (∏ PP ∈ Q.attach, ξ PP.1 (Units.map (conjRes Pg Q PP.1
      (Finset.mem_union_right _ PP.2)).toMonoidHom (Matrix.GeneralLinearGroup.det (κ : GL (Fin r) _))))⁻¹ := by
  simp [lamHom]

def mkLevel {S T : HSp D} (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E))
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : liftI Pg Q ≠ ⊤) (h2 : liftI Pg Q ≠ ⊥)
    (h3 : IsCoprime (liftI Pg Q) (conjI (liftI Pg Q))) (h4 : IsCoprime (liftI Pg Q) (Ideal.span {2}))
    (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ)
    (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ liftI Pg Q • C.X.Λ)
    (Lv0 : GlobalTheory.SW.Level C.X) : GlobalTheory.SW.Level C.X where
  𝔪 := liftI Pg Q
  proper := h1
  ne_bot := h2
  cop := h3
  odd := h4
  β := β
  β_mem := hβ
  β_span := hsp
  J := Jgrp Pg Q T.rank
  lam := lamHom Pg Q T.rank ξ
  w := Lv0.w
  w_int := Lv0.w_int
  w_tr := Lv0.w_tr

end GlobalTheory.LiftDat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviGL
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviGLRes

variable {D : D7}

theorem covolOne_integral_mul_right {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (GlobalTheory.MixModel.ratMx D m n) μ 𝓕) (M M' : Mx D n n) (hM'M : M' * M = 1) (hMM' : M * M' = 1)
    (hM : M ∈ GlobalTheory.MixModel.ratMx D n n) (hM' : M' ∈ GlobalTheory.MixModel.ratMx D n n) (φ : Mx D m n → ℂ)
    (hφ : ∀ γ ∈ GlobalTheory.MixModel.ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓕, φ (a * M) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  let e : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => a * M
      invFun := fun a => a * M'
      left_inv := fun a => by simp only [Matrix.mul_assoc, hMM', Matrix.mul_one]
      right_inv := fun a => by simp only [Matrix.mul_assoc, hM'M, Matrix.mul_one]
      map_add' := fun a b => Matrix.add_mul _ _ _ }
  have he : Continuous e := continuous_id.matrix_mul continuous_const
  have he' : Continuous e.symm := continuous_id.matrix_mul continuous_const
  have hr : ∀ x, e x ∈ GlobalTheory.MixModel.ratMx D m n ↔ x ∈ GlobalTheory.MixModel.ratMx D m n := fun x =>
    ⟨fun h => by
      have h2 := GlobalTheory.MixModel.ratMx_mul h hM'
      have h3 : e x * M' = x := e.symm_apply_apply x
      rwa [h3] at h2,
     fun h => GlobalTheory.MixModel.ratMx_mul h hM⟩
  obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hμ e he he' hr
  rw [← GlobalTheory.MixModel.covolOne_integral_eq hμ h1 φ hφ, hemb.setIntegral_map, Set.preimage_image_eq _ e.injective]
  rfl

end GlobalTheory.LeviGLRes

namespace GlobalTheory.LeviGLRes

theorem res_levi_GL : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) D.host.E) (f : WO V W → ℂ), IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (d.levi (Matrix.GeneralLinearGroup.map (incA D) a), 1) f) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs d hC hB ψ χS χT ω hω μ 𝓨 hcov a f hf
  subst hC hB
  set A : GL (Fin r) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a with hA
  have hA1 : A.1 = GlobalTheory.MixModel.rat a.1 := rfl
  have hAi : (A⁻¹).1 = GlobalTheory.MixModel.rat (a⁻¹).1 := rfl
  have hmem : d.levi A ∈ GQ V :=
    d.levi_mem_GQ (by rw [hA1]; exact GlobalTheory.MixModel.rat_mem _) (by rw [hAi]; exact GlobalTheory.MixModel.rat_mem _)
  have hsub : ∀ w : WO V W, ω (d.levi A, 1) f w = f (w * Formalism.L2.Theta.mt V (d.levi A)) := fun w => by
    have h := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω _ hmem 1 (one_mem _) f hf
      (w * Formalism.L2.Theta.mt V (d.levi A))
    rwa [GlobalTheory.LeviRes.actO_mul_mt] at h
  set M : Mx D r r := GlobalTheory.MixModel.adj (A⁻¹).1 with hMdef
  set M' : Mx D r r := GlobalTheory.MixModel.adj A.1 with hM'def
  have hMM' : M * M' = 1 := by
    rw [hMdef, hM'def, ← GlobalTheory.MixModel.adj_mul, Units.mul_inv, GlobalTheory.MixModel.adj_one]
  have hM'M : M' * M = 1 := by
    rw [hMdef, hM'def, ← GlobalTheory.MixModel.adj_mul, Units.inv_mul, GlobalTheory.MixModel.adj_one]
  have hM : M ∈ GlobalTheory.MixModel.ratMx D r r := GlobalTheory.MixModel.ratMx_adj (by rw [hAi]; exact GlobalTheory.MixModel.rat_mem _)
  have hM' : M' ∈ GlobalTheory.MixModel.ratMx D r r := GlobalTheory.MixModel.ratMx_adj (by rw [hA1]; exact GlobalTheory.MixModel.rat_mem _)
  funext x
  have key : ∀ y : Mx D W.rank r,
      ω (d.levi A, 1) f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) =
        f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e (y * M) + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) := by
    intro y
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y * Formalism.L2.Theta.mt V (d.levi A) =
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e (y * M) := by
      show (y * d.pY) * Formalism.L2.Theta.mt V (d.levi A) = (y * M) * d.pY
      rw [Matrix.mul_assoc, d.pY_levi, ← Matrix.mul_assoc]
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x * Formalism.L2.Theta.mt V (d.levi A) =
        GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x := by
      rw [GlobalTheory.Bridge.orthProjPartHomToHermitian_eq_wittDecompositionCore, GlobalTheory.MixModel.HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, d.wittDecomp_projAnisotropic_levi]
    rw [hsub, Matrix.add_mul, e1, e2]
  show ∫ y in 𝓨, ω (d.levi A, 1) f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) ∂μ =
    ∫ y in 𝓨, f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x) ∂μ
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact covolOne_integral_mul_right hcov M M' hM'M hMM' hM hM'
    (fun y => f (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W d.e y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W d.i₀ x))
    (GlobalTheory.LeviRes.periodic hs hf x)

end GlobalTheory.LeviGLRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviGLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRestriction_invariant_rationalLeviGL : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) D.host.E) (f : WO V W → ℂ), IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (d.levi (Matrix.GeneralLinearGroup.map (incA D) a), 1) f) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f := by
  first | exact @GlobalTheory.LeviGLRes.res_levi_GL | exact GlobalTheory.LeviGLRes.res_levi_GL | (intros; apply GlobalTheory.LeviGLRes.res_levi_GL <;> assumption)
end
end
