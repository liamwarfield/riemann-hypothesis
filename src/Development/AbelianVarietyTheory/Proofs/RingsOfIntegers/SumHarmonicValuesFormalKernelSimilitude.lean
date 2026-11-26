module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSymmetricTranslationUnitsEqKappaRatio
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffInvariantOperatorAlongMatrix
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.JacobianNonzeroSplittingOfProduct
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SplitKernelFormalGroupOfRationalTorsion
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsTranslateUnitSymmetricFormalGroupPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConnectionValueLevelKappaMulPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConnectionValueLevelKappaMulPullback
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem kappa_mul_pullM_mul_expS {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O)
    (K : Type) [CommRing K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O)
    (hh : MvPowerSeries.constantCoeff h = 0) {n : ℕ} (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d)
    (hκ : IsKappa B K h w0 mu N κ) (g : PS V n d) :
    FB.toK K (κ * pullM B mu g) * FB.expS K ((N : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i))
        (FB.toK K g * FB.expS K (((1 : ℕ) : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0))) := by
  have hpt : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V :=
    fun b i => by rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b i]; exact Ideal.zero_mem _
  have h0 : ∀ (b : Fin n) (i : Fin d),
      MvPowerSeries.constantCoeff (matV B mu (fun j => pt V (n := n) d j) b i) = 0 :=
    (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n mu mu (fun j => pt V (n := n) d j) (fun j => pt V (n := n) d j) hpt hpt).2.2.2.2.2.1
  have hy : ∀ b : Fin n,
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GP (fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) := by
    intro b i
    show MvPowerSeries.constantCoeff (MvPowerSeries.map (algebraMap V K) (matV B mu (fun j => pt V (n := n) d j) b i)) = 0
    rw [MvPowerSeries.constantCoeff_map, h0, map_zero]
  have hact : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GP (B.actK K w0) := by
    intro i
    unfold FB.actK
    rw [MvPowerSeries.constantCoeff_map, B.A.const w0 i, map_zero]
  have hL0 : MvPowerSeries.constantCoeff (B.hL K h w0) = 0 := by
    unfold FB.hL
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _ (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.pair_points_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0)
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_comp1 _ _ hact (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0))) _ hh
  have hsm : ∀ (c : K) (f : PS K n d), MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (c • f) = 0 := by
    intro c f hf
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]
  have hS : MvPowerSeries.constantCoeff (∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b)) _ hL0
  have hA : MvPowerSeries.constantCoeff (∑ b : Fin n, ev (n := n)
      ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_const_ev _
      (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (hy b)) _ hL0
  have hsub : MvPowerSeries.HasSubst
      (fun p : Fin n × Fin d => matV B mu (fun j => pt V (n := n) d j) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h0 p.1 p.2
  have hpull : FB.toK K (pullM B mu g) =
      ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)) (FB.toK K g) := by
    have hC := (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin n × Fin d) (Fin n × Fin d) (Fin n × Fin d)
      (fun p : Fin n × Fin d => matV B mu (fun j => pt V (n := n) d j) p.1 p.2)
      (fun p => by rw [h0]; exact Ideal.zero_mem _)).2.2.1 (fun p => h0 p.1 p.2)
    unfold pullM evV
    rw [hC]
    unfold FB.toK ev
    exact MvPowerSeries.map_subst hsub _
  have hevy : ev (n := n) (fun b i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i))
      (∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) =
      ∑ b : Fin n, ev (n := n) ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0) := by
    rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.ev_sum hy]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_ev' _ _ hy (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.single_point_zero_constant (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt b))]
    congr 1
    funext j
    fin_cases j
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.evP_pt _ hy b
  have hm : FB.toK K (κ * pullM B mu g) = FB.toK K κ * FB.toK K (pullM B mu g) :=
    map_mul (MvPowerSeries.map (algebraMap V K)) κ (pullM B mu g)
  have hk := hκ
  unfold IsKappa at hk
  have hAS := hsm (N : K) _ hS
  rw [Nat.cast_one, one_smul, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_mul _ hy, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_ev_expS _ hy _ hS,
    hevy, ← hpull, hm, hk, _root_.mul_comm (FB.expS K _) (FB.toK K (pullM B mu g)), _root_.mul_assoc,
    ← ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_expS_add _ _ (by rw [map_sub, hA, hAS, sub_zero]) hAS, sub_add_cancel]

theorem nabValN_kappa_mul_pullM : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O), MvPowerSeries.constantCoeff h = 0 → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d), IsKappa B K h w0 mu N κ → ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → ∀ (P : MvPolynomial (Letter Ty r n) K) (g : PS V n d), nabValN B K h w0 N (FB.toK K (κ * pullM B mu g)) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B K h w0 1 (FB.toK K g) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (fun ℓ : Letter Ty r n => ∑ b, MvPolynomial.C (σ ℓ.1 (mu b ℓ.2.2)) * MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) P) := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ h w0 hh n mu N κ hκ Ty _ r σ u hu P g
  unfold nabValN
  rw [kappa_mul_pullM_mul_expS B K h w0 hh mu N κ hκ g]
  exact GlobalTheory.T.constantCoeff_invariant_operator_along_matrix V d O B K n mu Ty r σ u hu P _

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConnectionValueLevelKappaMulPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectionValueLevel_kappa_mul_pullback : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (h : PS K 2 d) (w0 : O), MvPowerSeries.constantCoeff h = 0 → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ) (κ : PS V n d), IsKappa B K h w0 mu N κ → ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → ∀ (P : MvPolynomial (Letter Ty r n) K) (g : PS V n d), nabValN B K h w0 N (FB.toK K (κ * pullM B mu g)) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B K h w0 1 (FB.toK K g) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun ℓ => u ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.aeval (fun ℓ : Letter Ty r n => ∑ b, MvPolynomial.C (σ ℓ.1 (mu b ℓ.2.2)) * MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : Letter Ty r n)) P) := by
  first | exact @GlobalTheory.PlaceInt.nabValN_kappa_mul_pullM | exact GlobalTheory.PlaceInt.nabValN_kappa_mul_pullM | (intros; apply GlobalTheory.PlaceInt.nabValN_kappa_mul_pullM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleEq
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open MvPowerSeries
open scoped Kronecker
namespace GlobalTheory.JacVal

section Series
variable {V : Type} [CommRing V] {σ τ : Type}

theorem exists_decomp [Fintype σ] (g : MvPowerSeries σ V) :
    ∃ k : σ → MvPowerSeries σ V, g = C (constantCoeff g) + ∑ i, X i * k i := by
  classical
  obtain ⟨k, -, hk⟩ := exists_eq_sum_X_mul (n := 0) (g := g - C (constantCoeff g))
    fun d hd => by
      have : d = 0 := by
        rw [← Finsupp.degree_eq_zero_iff]; omega
      subst this
      simp
  exact ⟨k, by rw [← hk]; ring⟩

theorem coeff_single_eq (q : τ) (f : MvPowerSeries τ V) :
    coeff (Finsupp.single q 1) f = constantCoeff (pderiv (R := V) q f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

theorem coeff_single_mul (q : τ) (a b : MvPowerSeries τ V) (ha : constantCoeff a = 0) :
    coeff (Finsupp.single q 1) (a * b) = coeff (Finsupp.single q 1) a * constantCoeff b := by
  rw [coeff_single_eq, coeff_single_eq, Derivation.leibniz]
  simp [ha, _root_.mul_comm]

theorem coeff_single_C (q : τ) (c : V) : coeff (Finsupp.single q 1) (C c : MvPowerSeries τ V) = 0 := by
  rw [coeff_single_eq]; simp

theorem coeff_single_X [DecidableEq τ] (q p : τ) :
    coeff (Finsupp.single q 1) (X p : MvPowerSeries τ V) = if q = p then 1 else 0 := by
  rw [coeff_X]
  by_cases h : q = p
  · simp [h]
  · rw [if_neg, if_neg h]
    intro h'
    exact h (Finsupp.single_left_injective one_ne_zero h')

theorem const_hom [Fintype σ] (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V)
    (h : ∀ j, constantCoeff (ψ (X j)) = 0) (f : MvPowerSeries σ V) : constantCoeff (ψ f) = constantCoeff f := by
  obtain ⟨k, hk⟩ := exists_decomp f
  have hC : ψ (C (constantCoeff f)) = C (constantCoeff f) := ψ.commutes _
  conv_lhs => rw [hk]
  simp [hC, h]

theorem coeff_hom [Fintype σ] (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V)
    (h : ∀ j, constantCoeff (ψ (X j)) = 0) (f : MvPowerSeries σ V) (q : τ) :
    coeff (Finsupp.single q 1) (ψ f) = ∑ j, coeff (Finsupp.single j 1) f * coeff (Finsupp.single q 1) (ψ (X j)) := by
  classical
  obtain ⟨k, hk⟩ := exists_decomp f
  have hC : ψ (C (constantCoeff f)) = C (constantCoeff f) := ψ.commutes _
  have h1 : ∀ j, coeff (Finsupp.single j 1) f = constantCoeff (k j) := by
    intro j
    conv_lhs => rw [hk]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), coeff_single_C, zero_add, map_sum]
    rw [Finset.sum_congr rfl fun i _ => coeff_single_mul j (X i) (k i) (by simp)]
    simp [coeff_single_X]
  conv_lhs => rw [hk]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), hC, map_add (f := _), coeff_single_C, zero_add, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coeff_single_mul _ _ _ (h j), const_hom ψ h, h1, _root_.mul_comm]

theorem evC_hom [Fintype σ] (a : σ → MvPowerSeries τ V) (ha : ∀ j, constantCoeff (a j) = 0) :
    ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (X j) = a j) ∧ ∀ f, evC a f = ψ f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h : ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j :=
    ⟨substAlgHom hs, fun j => substAlgHom_X hs j⟩
  exact ⟨h.choose, h.choose_spec, fun f => by unfold PlaceInt.evC; rw [dite_eq_left h]⟩

theorem const_evC [Fintype σ] (a : σ → MvPowerSeries τ V) (ha : ∀ j, constantCoeff (a j) = 0)
    (f : MvPowerSeries σ V) : constantCoeff (evC a f) = constantCoeff f := by
  obtain ⟨ψ, h1, h2⟩ := evC_hom a ha
  rw [h2, const_hom ψ fun j => by rw [h1, ha]]

theorem coeff_evC [Fintype σ] (a : σ → MvPowerSeries τ V) (ha : ∀ j, constantCoeff (a j) = 0)
    (f : MvPowerSeries σ V) (q : τ) :
    coeff (Finsupp.single q 1) (evC a f) = ∑ j, coeff (Finsupp.single j 1) f * coeff (Finsupp.single q 1) (a j) := by
  obtain ⟨ψ, h1, h2⟩ := evC_hom a ha
  rw [h2, coeff_hom ψ fun j => by rw [h1, ha]]
  simp only [h1]

variable {d m : ℕ}

theorem addV_lin (G : FGLaw V d) (x y : Pt V m d) (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (i : Fin d) :
    constantCoeff (addV G.F x y i) = 0 ∧ ∀ q, coeff (Finsupp.single q 1) (addV G.F x y i) =
      coeff (Finsupp.single q 1) (x i) + coeff (Finsupp.single q 1) (y i) := by
  have ha : ∀ p : Fin 2 × Fin d, constantCoeff ((![x, y] : Fin 2 → Pt V m d) p.1 p.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    · exact hx j
    · exact hy j
  refine ⟨(const_evC _ ha _).trans (G.const i), fun q => (coeff_evC _ ha _ q).trans ?_⟩
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PullbackSections.Pf.EigA.formal_group_coeff_first_linear, PullbackSections.Pf.EigA.formal_group_coeff_second_linear, ite_mul, _root_.one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem fold_lin (G : FGLaw V d) (l : List (Pt V m d)) (hl : ∀ x ∈ l, ∀ i, constantCoeff (x i) = 0) :
    (∀ i, constantCoeff (l.foldr (addV G.F) 0 i) = 0) ∧ ∀ i q, coeff (Finsupp.single q 1) (l.foldr (addV G.F) 0 i) =
      (l.map fun x => coeff (Finsupp.single q 1) (x i)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨h1, h2⟩ := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hx := hl x List.mem_cons_self
    refine ⟨fun i => (addV_lin G x _ hx h1 i).1, fun i q => ?_⟩
    rw [List.foldr_cons, (addV_lin G x _ hx h1 i).2, h2, List.map_cons, List.sum_cons]

theorem compV_pt (φ : Pt V 1 d) (j : Fin m) (i : Fin d) :
    constantCoeff (compV φ (pt V d j) i) = constantCoeff (φ i) ∧
      ∀ q : Fin m × Fin d, coeff (Finsupp.single q 1) (compV φ (pt V d j) i) =
        if q.1 = j then coeff (Finsupp.single ((0 : Fin 1), q.2) 1) (φ i) else 0 := by
  have ha : ∀ p : Fin 1 × Fin d, constantCoeff ((![pt V d j] : Fin 1 → Pt V m d) p.1 p.2) = 0 := by
    rintro ⟨a, j⟩
    fin_cases a
    simp [pt]
  refine ⟨const_evC _ ha _, fun q => (coeff_evC _ ha _ q).trans ?_⟩
  obtain ⟨a, b⟩ := q
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  by_cases h : a = j <;> simp [pt, coeff_single_X, h]

variable {O : Type} [CommRing O] [StarRing O]

theorem coeff_matV (B : FB V d O) {n : ℕ} (p : Matrix (Fin n) (Fin n) O) (x q : Fin n × Fin d) :
    coeff (Finsupp.single q 1) (matV B p (fun j => pt V (n := n) d j) x.1 x.2) =
      coeff (Finsupp.single ((0 : Fin 1), q.2) 1) (B.A.act (p x.1 q.1) x.2) := by
  unfold matV
  rw [(fold_lin B.G _ ?_).2, List.map_ofFn, List.sum_ofFn]
  · simp only [Function.comp, (compV_pt _ _ _).2]
    simp
  · intro y hy i
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    rw [(compV_pt _ _ _).1, B.A.const]

end Series

theorem det_blocks {K O L : Type} [CommRing K] [CommRing O] [Fintype L] {d n : ℕ} (M : O → Matrix (Fin d) (Fin d) K)
    (p : Matrix (Fin n) (Fin n) O) (s : L → O →+* K) (u : L → Fin d → K)
    (he : ∀ ℓ a, (M a).mulVec (u ℓ) = s ℓ a • u ℓ)
    (hb : ∀ v : Fin d → K, ∃! a : L → K, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) :
    (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2).det = ∏ ℓ, s ℓ p.det := by
  classical
  let U : Matrix (Fin d) L K := Matrix.of fun j ℓ => u ℓ j
  let W : Matrix L (Fin d) K := Matrix.of fun ℓ t => (hb (Pi.single t 1)).exists.choose ℓ
  have hUW : U * W = 1 := by
    ext j t
    have := (hb (Pi.single t 1)).exists.choose_spec j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [U, W, Matrix.of_apply]
    rw [Finset.sum_congr rfl fun ℓ _ => _root_.mul_comm _ _, this, Pi.single_apply]
  have hWU : W * U = 1 := by
    have h3 : U * (W * U) = U * (1 : Matrix L L K) := by rw [← Matrix.mul_assoc, hUW, Matrix.one_mul, Matrix.mul_one]
    ext ℓ ℓ'
    have := (hb fun j => (U * (1 : Matrix L L K)) j ℓ').unique (y₁ := fun ℓ => (W * U) ℓ ℓ')
      (y₂ := fun ℓ => (1 : Matrix L L K) ℓ ℓ')
      (fun j => by
        rw [← h3, Matrix.mul_apply (M := U)]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _)
      (fun j => by
        rw [Matrix.mul_apply (M := U)]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _)
    exact congrFun this ℓ
  have h1 : ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hUW, Matrix.mul_one, Matrix.one_kronecker_one]
  have h2 : ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hWU, Matrix.mul_one, Matrix.one_kronecker_one]
  have h3 : (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2) * ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) =
      ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * Matrix.blockDiagonal fun ℓ => (s ℓ).mapMatrix p := by
    ext ⟨i, a⟩ ⟨j, ℓ⟩
    have := congrFun (he ℓ (p i j)) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply, U,
      Matrix.blockDiagonal_apply, ite_mul, mul_ite, zero_mul, mul_zero, _root_.one_mul, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [this, _root_.mul_comm]
    rfl
  have h4 : (Matrix.of fun x q : Fin n × Fin d => M (p x.1 q.1) x.2 q.2) =
      ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ U) * (Matrix.blockDiagonal fun ℓ => (s ℓ).mapMatrix p) *
        ((1 : Matrix (Fin n) (Fin n) K) ⊗ₖ W) := by
    rw [← h3, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [h4, Matrix.det_conj_of_mul_eq_one h1 h2, Matrix.det_blockDiagonal]
  exact Finset.prod_congr rfl fun ℓ _ => ((s ℓ).map_det p).symm

theorem jacM_eq_prod : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (n : ℕ) (p : Matrix (Fin n) (Fin n) O) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (σ : Ty → O →+* K) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → K), (∀ ℓ a, (dAct K B a).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ v : Fin d → K, ∃! a : (Σ τ : Ty, Fin (r τ)) → K, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) → algebraMap V K (jacM B p) = ∏ τ, σ τ p.det ^ r τ := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ n p Ty _ r σ u he hb
  have h := det_blocks (dAct K B) p (fun ℓ : Σ τ : Ty, Fin (r τ) => σ ℓ.1) u he hb
  rw [Fintype.prod_sigma] at h
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h, jacM, RingHom.map_det]
  congr 1
  ext x q
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, coeff_matV]
  show _ = coeff _ (MvPowerSeries.map (algebraMap V K) _)
  rw [coeff_map]

end GlobalTheory.JacVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumHarmonicValuesFormalKernelSimilitude
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.FormSum
open GlobalTheory.PlaceInt.ShiftPf

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O) {n : ℕ}

omit [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem sm_one {x : Pt V n d} (hx : Sm1 x) : Sm ![x] := by
  intro b
  fin_cases b
  exact hx

theorem copy_shift {α : Fin n → Fin d → V} (hα : ∀ b, Small (α b)) (b : Fin n) (f : PS V 1 d) :
    evV (n := n) ![pt V d b] (shift B.G.F (fun _ => α b) f) = shift B.G.F α (evV (n := n) ![pt V d b] f) := by
  have h1 : Sm (![pt V d b] : Fin 1 → Pt V n d) := sm_one (sm_pt b)
  have h2 : Sm (fun c : Fin 1 => addV B.G.F (pt V d c) (cpt ((fun _ => α b) c)) : Fin 1 → Pt V 1 d) :=
    sm_shift B (fun _ => hα b)
  have h3 : Sm (fun c => addV B.G.F (pt V d c) (cpt (α c)) : Fin n → Pt V n d) := sm_shift B hα
  unfold GlobalTheory.PlaceInt.shift
  rw [evV_comp h2 h1, evV_comp h1 h3]
  congr 1
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  have eL := evV_addV B.G.F h1 (sm_pt (V := V) (d := d) (n := 1) 0) (sm_cpt (n := 1) (hα b))
  rw [evV_pt h1, evV_cpt h1] at eL
  refine eL.trans ?_
  exact (evV_pt h3 b).symm

theorem box_shift {α : Fin n → Fin d → V} (hα : ∀ b, Small (α b)) (u f : Fin n → PS V 1 d) :
    ∏ b, evV (n := n) ![pt V d b] (u b * shift B.G.F (fun _ => α b) (f b)) =
      (∏ b, evV (n := n) ![pt V d b] (u b)) * shift B.G.F α (∏ b, evV (n := n) ![pt V d b] (f b)) := by
  have hmul : ∀ b (x y : PS V 1 d), evV (n := n) ![pt V d b] (x * y) =
      evV (n := n) ![pt V d b] x * evV (n := n) ![pt V d b] y := by
    intro b x y
    obtain ⟨ψ, -, hψ⟩ := evV_hom (sm_one (n := n) (sm_pt (V := V) (d := d) b))
    rw [hψ, hψ, hψ, _root_.map_mul]
  obtain ⟨ψ, hψ⟩ := shift_equiv B hα
  calc ∏ b, evV (n := n) ![pt V d b] (u b * shift B.G.F (fun _ => α b) (f b))
      = ∏ b, (evV (n := n) ![pt V d b] (u b) * ψ (evV (n := n) ![pt V d b] (f b))) := by
        refine Finset.prod_congr rfl (fun b _ => ?_)
        rw [hmul, copy_shift B hα, hψ]
    _ = _ := by rw [Finset.prod_mul_distrib, hψ, _root_.map_prod]

theorem box_smul (r : Fin n → V) (hr : ∏ b, r b = 1) (f : Fin n → PS V 1 d) :
    ∏ b, evV (n := n) ![pt V d b] (r b • f b) = ∏ b, evV (n := n) ![pt V d b] (f b) := by
  have hsm : ∀ b (x : PS V 1 d) (t : V), evV (n := n) ![pt V d b] (t • x) = t • evV (n := n) ![pt V d b] x := by
    intro b x t
    obtain ⟨ψ, -, hψ⟩ := evV_hom (sm_one (n := n) (sm_pt (V := V) (d := d) b))
    rw [hψ, hψ, _root_.map_smul]
  have hA : ∏ b, algebraMap V (PS V n d) (r b) = 1 := by
    rw [← _root_.map_prod (algebraMap V (PS V n d)) r Finset.univ, hr, _root_.map_one]
  simp_rw [hsm, Algebra.smul_def]
  rw [Finset.prod_mul_distrib, hA, _root_.one_mul]

theorem kerM_subset (p q : Matrix (Fin n) (Fin n) O) : kerM B q ⊆ kerM B (p * q) := by
  rintro α ⟨hsm, hk⟩
  show (∀ b, Small (α b)) ∧ matV B (m := 0) (p * q) (fun j => cpt (α j)) = 0
  refine ⟨hsm, ?_⟩
  have hc : ∀ b i, MvPowerSeries.constantCoeff ((fun j => (cpt (α j) : Pt V 0 d)) b i) ∈ maximalIdeal V := by
    intro b i
    simpa [cpt] using hsm b i
  rw [(GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n 0 p q _ _ hc hc).2.1, hk, matV_zero]

theorem sum_twisted (p q : Matrix (Fin n) (Fin n) O) (t : V)
    (htr : ∀ f : PS V n d, (∀ α ∈ kerM B q, shift B.G.F α f = f) → (kerM B (p * q)).Finite ∧ ∃ g : PS V n d,
      ∑ᶠ α ∈ kerM B (p * q), shift B.G.F α f = MvPowerSeries.C t * pullM B (p * q) g)
    (κ : PS V n d) (hκ : MvPowerSeries.constantCoeff κ = 1) {J : Type} [Fintype J] (α : J → Fin n → Fin d → V)
    (hinj : Function.Injective α) (hr : Set.range α = kerM B (p * q)) (f : PS V n d) (U : J → PS V n d)
    (hU : ∀ i, U i * shift B.G.F (α i) κ = κ) (hq : ∀ i, α i ∈ kerM B q → U i * shift B.G.F (α i) f = f) :
    ∃ g : PS V n d, ∑ i, U i * shift B.G.F (α i) f = t • (κ * pullM B (p * q) g) := by
  have hκu : IsUnit κ := MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hκ]; exact isUnit_one)
  obtain ⟨κu, rfl⟩ := hκu
  have hsm : ∀ i b, Small (α i b) := by
    intro i
    have hi : α i ∈ kerM B (p * q) := by rw [← hr]; exact ⟨i, rfl⟩
    obtain ⟨h1, -⟩ := hi
    exact h1
  have hA : ∀ i, U i * shift B.G.F (α i) f = (κu : PS V n d) * shift B.G.F (α i) (↑κu⁻¹ * f) := by
    intro i
    obtain ⟨ψ, hψ⟩ := shift_equiv B (hsm i)
    have h1 := hU i
    simp only [hψ] at h1 ⊢
    rw [_root_.map_mul]
    calc U i * ψ f = U i * ψ (↑κu * ↑κu⁻¹) * ψ f := by rw [Units.mul_inv, _root_.map_one, _root_.mul_one]
      _ = (U i * ψ ↑κu) * ψ ↑κu⁻¹ * ψ f := by rw [_root_.map_mul]; ring
      _ = _ := by rw [h1, _root_.mul_assoc]
  have hB : ∀ β ∈ kerM B q, shift B.G.F β (↑κu⁻¹ * f) = ↑κu⁻¹ * f := by
    intro β hβ
    obtain ⟨i, rfl⟩ : β ∈ Set.range α := by rw [hr]; exact kerM_subset B p q hβ
    have e := (hA i).symm.trans (hq i hβ)
    calc shift B.G.F (α i) (↑κu⁻¹ * f) = ↑κu⁻¹ * (↑κu * shift B.G.F (α i) (↑κu⁻¹ * f)) := by
          rw [← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
      _ = _ := by rw [e]
  obtain ⟨-, g, hg⟩ := htr (↑κu⁻¹ * f) hB
  refine ⟨g, ?_⟩
  have hsum : ∑ᶠ β ∈ kerM B (p * q), shift B.G.F β (↑κu⁻¹ * f) = ∑ i, shift B.G.F (α i) (↑κu⁻¹ * f) := by
    rw [← hr, finsum_mem_range hinj, finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl (fun i _ => hA i), ← Finset.mul_sum, ← hsum, hg, MvPowerSeries.smul_eq_C_mul]
  ring

end

theorem sim_two_sided {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (s mu : Matrix (Fin n) (Fin n) O) (c : O) (hc : c ≠ 0)
    (h : s * mu = c • (1 : Matrix (Fin n) (Fin n) O)) :
    mu.det ≠ 0 ∧ mu * s = c • (1 : Matrix (Fin n) (Fin n) O) := by
  have hdet : mu.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, MulZeroClass.mul_zero, Matrix.det_smul, Matrix.det_one, MulOneClass.mul_one] at e
    exact pow_ne_zero _ hc e.symm
  refine ⟨hdet, ?_⟩
  have key : (mu * s) * mu = (c • (1 : Matrix (Fin n) (Fin n) O)) * mu := by
    rw [Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have e2 : (mu * s) * (mu * mu.adjugate) = (c • (1 : Matrix (Fin n) (Fin n) O)) * (mu * mu.adjugate) := by
    rw [← Matrix.mul_assoc, key, Matrix.mul_assoc]
  rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one] at e2
  ext i j
  have e3 := congrFun (congrFun e2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at e3
  exact mul_left_cancel₀ hdet e3

theorem map_pushL {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (c : Coeff l) {K : Type} [Field K] (io : c.F →+* K) {n : ℕ} (mu : Matrix (Fin n) (Fin n) (𝓞 E))
    (P : MvPolynomial (LtN Dw n) c.F) :
    MvPolynomial.map io (pushL c (mu.map (algebraMap (𝓞 E) E)) P) =
      MvPolynomial.aeval (fun ℓ : LtN Dw n => ∑ b, MvPolynomial.C ((io.comp (embK c ℓ.1)) (mu b ℓ.2.2)) *
        MvPolynomial.X (⟨ℓ.1, ℓ.2.1, b⟩ : LtN Dw n)) (MvPolynomial.map io P) := by
  unfold pushL
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p1 p2 h1 h2 => simp only [_root_.map_add (f := _), h1, h2]
  | mul_X p ℓ h =>
    simp only [Matrix.map_apply] at h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [_root_.map_mul, h, MvPolynomial.aeval_X, MvPolynomial.map_X, _root_.map_sum, MvPolynomial.map_C,
      Matrix.map_apply, RingHom.coe_comp, Function.comp_apply]
    rfl

private theorem isLinearMap_nabValN {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O) (m : ℕ) {n : ℕ} {Ix : Type} [Fintype Ix]
    (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) :
    IsLinearMap k (fun f : PS k n d => nabValN B k h w0 m f cp u P) := by
  have hD := fun mo => GlobalTheory.PowGerm.NabJet.isLinearMap_DmonN (B.FK k) cp u mo
  refine ⟨fun f g => ?_, fun a f => ?_⟩
  · show nabValN B k h w0 m (f + g) cp u P = nabValN B k h w0 m f cp u P + nabValN B k h w0 m g cp u P
    unfold nabValN
    rw [GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq _ cp u P _ P.support subset_rfl,
      GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq _ cp u P _ P.support subset_rfl,
      GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq _ cp u P _ P.support subset_rfl, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun mo _ => ?_)
    rw [add_mul, (hD mo).map_add (f := _), _root_.map_add (f := _), mul_add]
  · show nabValN B k h w0 m (a • f) cp u P = a • nabValN B k h w0 m f cp u P
    unfold nabValN
    rw [GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq _ cp u P _ P.support subset_rfl,
      GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq _ cp u P _ P.support subset_rfl, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun mo _ => ?_)
    rw [smul_mul_assoc, (hD mo).map_smul, MvPowerSeries.smul_eq_C_mul, _root_.map_mul, MvPowerSeries.constantCoeff_C]
    ring

private theorem nabValN_C_mul {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O) (m : ℕ) {n : ℕ} {Ix : Type} [Fintype Ix]
    (f : PS k n d) (cp : Ix → Fin n) (u : Ix → Fin d → k) (a : k) (P : MvPolynomial Ix k) :
    nabValN B k h w0 m f cp u (MvPolynomial.C a * P) = a * nabValN B k h w0 m f cp u P := by
  have hS : (MvPolynomial.C a * P).support ⊆ P.support := by
    rw [MvPolynomial.C_mul']
    exact MvPolynomial.support_smul
  unfold nabValN
  rw [GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq _ cp u (MvPolynomial.C a * P) _ P.support hS,
    GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq _ cp u P _ P.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun mo _ => ?_)
  rw [MvPolynomial.coeff_C_mul]
  ring

theorem sum_hv_formal_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (N k M : ℕ) (p q : Matrix (Fin n) (Fin n) (𝓞 E)), Odd N → IsSim H (p * q) (N ^ 2) → N ^ 2 = k * M → Nat.Coprime k ℓ → AllRat Xo (xOf y) M → ∀ (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)), Function.Injective a → (∀ u : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ i, a i = u) ↔ (Kills Xo (p * q) u ∧ ∀ b, ∃ α, FormPt C (u b) α)) → ∀ (F : Fin n → SecN Xo (xOf y) (N ^ 2)) (G : J → Fin n → SecN Xo (xOf y) (N ^ 2)), (∀ b, Regular C (N ^ 2) (F b)) → (∀ i b, Moves Xo (a i b) (F b) (G i b)) → (∀ i, Kills Xo q (a i) → ∃ r : Fin n → T.V, ∏ b, r b = 1 ∧ ∀ b j, (G i b).f j = liftFun Xo.univ.t.G _ (T := ptO Xo (xOf y)) (toΓ T.Fr (algebraMap T.V T.Fr (r b))) * (F b).f j) → ∀ (P : MvPolynomial (LtN Dw n) c.F) (s : c.F), P ∈ HH c w n → MvPolynomial.map io (MvPolynomial.C s * pushL c ((p * q).map (algebraMap (𝓞 E) E)) P) ∈ FFV (Dw := Dw) T w n → letI := io.toAlgebra; ∃ z : T.Fr, ((-ρ : ℝ) : EReal) ≤ nval T.V e z ∧ io s * ∑ i, hv Xo c nab y.1 (N ^ 2) (G i) P = (Nat.card {i : J // Kills Xo q (a i)} : T.Fr) * io (∏ τ : E →+* ℂ, embK c τ p.det ^ Dw.mult τ) * z := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hG nab hnab e ρ w n he hCh ℓ hℓ hℓu N k M p q hN hsim hNk hkℓ hrat J _ a ha
    hiff F G hF hmove hkill P s hP hFF
  let _ := io.toAlgebra
  obtain ⟨B, hB, hBall⟩ := GlobalTheory.T.integralChart_formalBiextension_gauge_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hcan, hg0, heig, hbd⟩ := hBall B hB
  obtain ⟨⟨Θ, hΘ⟩, jo, hjo⟩ := GlobalTheory.T.gauge_thirdDifference_symmetry_integral_exponentials T.V (chD C.ch) (𝓞 E) B T.Fr (gaugeOf C) H.w0 hcan
  have hNpos : N ^ 2 ≠ 0 := pow_ne_zero 2 (Odd.pos hN).ne'
  have hN2 : ((N ^ 2 : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hNpos

  let sM : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun j i => star ((p * q) i j)
  have hsimS : ∀ j1 k1, ∑ i, star ((p * q) i j1) * (p * q) i k1 = if j1 = k1 then ((N ^ 2 : ℕ) : 𝓞 E) else 0 := by
    intro j1 k1
    simp only [hstar]
    exact hsim j1 k1
  have hsM : sM * (p * q) = ((N ^ 2 : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) := by
    ext j1 k1
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [sM, Matrix.of_apply]
    rw [hsimS j1 k1]
    split_ifs <;> simp
  obtain ⟨hdet, hsM'⟩ := sim_two_sided sM (p * q) _ hN2 hsM

  have h51 := fun (kk : ℕ) (Fk : SecN Xo (xOf y) kk) => GlobalTheory.T.regular_section_integral_germ_unique_scale E H Dw l Xo c hstar T io y C hG.1 kk Fk
  choose f hf using fun b => (h51 (N ^ 2) (F b)).1 (hF b)
  have hkpq : ∀ i, Kills Xo (p * q) (a i) := fun i => ((hiff (a i)).mp ⟨i, rfl⟩).1
  choose α hα using fun i b => ((hiff (a i)).mp ⟨i, rfl⟩).2 b
  have h66 := GlobalTheory.T.formal_group_points_of_integral_chart_spec E H Dw l Xo c hstar T io y C B hB
  have h67 := fun (mu : Matrix (Fin n) (Fin n) (𝓞 E)) => GlobalTheory.T.kills_formalPoints_iff_mem_coordinateKernel E H Dw l Xo c hstar T io y C B hB n mu
  have hker : ∀ i, α i ∈ kerM B (p * q) := fun i => (h67 (p * q) (a i) (α i) (hα i)).mp (hkpq i)
  have hsm : ∀ i b, Small (α i b) := fun i => by
    obtain ⟨h1, -⟩ := hker i
    exact h1
  have hinj : Function.Injective α := by
    intro i j hij
    apply ha
    funext b
    exact (h66.2.1 (a i b) (a j b) (α i b) (α j b) (hα i b) (hα j b)).mpr (congrFun hij b)
  have hrange : Set.range α = kerM B (p * q) := by
    ext β
    constructor
    · rintro ⟨i, rfl⟩
      exact hker i
    · intro hβ
      have hβs : ∀ b, Small (β b) := by
        obtain ⟨h1, -⟩ := hβ
        exact h1
      choose a' ha' using fun b => h66.2.2.2.2 (β b) (hβs b)
      obtain ⟨i, hi⟩ := (hiff a').mpr ⟨(h67 (p * q) a' β ha').mpr hβ, fun b => ⟨β b, ha' b⟩⟩
      refine ⟨i, funext fun b => ?_⟩
      exact (h66.2.1 (a i b) (a' b) (α i b) (β b) (hα i b) (ha' b)).mp (congrFun hi b)

  have htor : ∀ i b, a i b ^ (N ^ 2) = 1 := fun i b =>
    GlobalTheory.PtTie.IsSymAct.pow_eq_one Xo.univ.t.G Xo.univ.t.PP (hmove i b)
  have h70 := GlobalTheory.T.exists_translateUnit_symmetric_formalGroup_point E H Dw l Xo c hstar T io y C hG.1 B hB Θ jo hΘ hjo (N ^ 2) hN.pow
  choose u hu hgerm using fun i b => h70 (a i b) (α i b) (hα i b) (htor i b)
  obtain ⟨κ, hκ, hκ1⟩ := GlobalTheory.T.exists_integral_exponential_similitude_gauge T.V (chD C.ch) (𝓞 E) B T.Fr (gaugeOf C) H.w0 hcan n (p * q) (N ^ 2) hsimS
  have hU : ∀ i, (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (u i b)) * shift B.G.F (α i) κ = κ := fun i =>
    GlobalTheory.T.prod_symmetricTranslationUnits_eq_kappa_ratio T.V (chD C.ch) (𝓞 E) B T.Fr (gaugeOf C) H.w0 hcan Θ jo hΘ hjo n (p * q) (N ^ 2) hN.pow hsimS κ hκ
      (α i) (hker i) (u i) (fun b => hu i b)
  have hq : ∀ i, α i ∈ kerM B q → (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (u i b)) *
      shift B.G.F (α i) (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b)) =
      ∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b) := by
    intro i hiq
    obtain ⟨r, hr1, hr⟩ := hkill i ((h67 q (a i) (α i) (hα i)).mpr hiq)
    rw [← box_shift B (hsm i) (u i) f]
    conv_rhs => rw [← box_smul r hr1 f]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    congr 1
    exact (h51 (N ^ 2) (G i b)).2.1 _ _ (hgerm i b (F b) (G i b) (f b) (hF b) (hf b) (hmove i b))
      ((h51 (N ^ 2) (F b)).2.2 (G i b) (r b) (f b) (hr b) (hf b))

  have hFinHt := GlobalTheory.T.finiteHeight_formalGroup_uniformisedModel E H Dw l Xo c hstar T io y C hG B hB
  have hN1 : 1 ≤ N ^ 2 := Nat.one_le_iff_ne_zero.mpr hNpos
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · rw [h0, MulZeroClass.mul_zero] at hNk
      exact absurd hNk hNpos
    · exact h0
  have hsplit : SplitKer B (p * q) := by
    have e0 : sM * (p * q) = ((k * M : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) := by
      rw [← hNk]
      exact hsM
    exact (GlobalTheory.T.splitKernel_formalGroup_of_rational_torsion E H Dw l Xo c hstar T io y C hG B hB ℓ hℓ hℓu n (p * q) sM k M hkℓ hM0 e0 hrat).1
  have hjac : ∀ x : Matrix (Fin n) (Fin n) (𝓞 E), algebraMap T.V T.Fr (jacM B x) =
      ∏ τ : E →+* ℂ, (io.comp (embK c τ)) x.det ^ Dw.mult τ := fun x =>
    GlobalTheory.JacVal.jacM_eq_prod T.V (chD C.ch) (𝓞 E) B T.Fr n x (E →+* ℂ) Dw.mult (fun τ => io.comp (embK c τ))
      C.ch.uvec heig C.ch.chart.basis
  have hdetpq : ∀ τ : E →+* ℂ, io (embK c τ (p * q).det) ≠ 0 := by
    intro τ
    refine (map_ne_zero io).mpr ?_
    intro h0
    have e0 := congrArg Matrix.det hsM
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, MulOneClass.mul_one] at e0
    have e5 := congrArg (embK c τ) e0
    rw [_root_.map_mul, h0, MulZeroClass.mul_zero, _root_.map_pow, _root_.map_natCast] at e5
    exact (pow_ne_zero _ (Nat.cast_ne_zero.mpr hNpos)) e5.symm
  have hjpq : jacM B (p * q) ≠ 0 := by
    intro h0
    have e0 := hjac (p * q)
    rw [h0, _root_.map_zero] at e0
    exact (Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (hdetpq τ)) e0.symm
  obtain ⟨g, hg⟩ := sum_twisted B p q (((kerM B q).ncard : T.V) * jacM B p)
    (fun f0 hf0 => GlobalTheory.T.jacobian_nonzero_splitting_of_product T.V (chD C.ch) (𝓞 E) B hFinHt n p q sM (N ^ 2) hN1 hsM hsM' inferInstance hN2 hjpq
      hsplit f0 hf0)
    κ hκ1 α hinj hrange (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))
    (fun i => ∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (u i b)) hU hq

  have hhv : ∀ i, hv Xo c nab y.1 (N ^ 2) (G i) P = nabValN B T.Fr (gaugeOf C) H.w0 (N ^ 2)
      (FB.toK T.Fr ((∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (u i b)) *
        shift B.G.F (α i) (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))))
      (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
    intro i
    rw [← box_shift B (hsm i) (u i) f]
    exact GlobalTheory.T.harmonicValue_integralPoint_eq_value_on_biextensionCopies E H Dw l Xo c hstar T io y C nab hnab B hB (N ^ 2) n (G i) _
      (fun b => hgerm i b (F b) (G i b) (f b) (hF b) (hf b) (hmove i b)) w P hP
  have hlin := isLinearMap_nabValN B T.Fr (gaugeOf C) H.w0 (N ^ 2) (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P)
  have e1 : ∀ X : J → PS T.V n (chD C.ch), ∑ i, nabValN B T.Fr (gaugeOf C) H.w0 (N ^ 2) (FB.toK T.Fr (X i))
      (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) =
      nabValN B T.Fr (gaugeOf C) H.w0 (N ^ 2) (FB.toK T.Fr (∑ i, X i))
      (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
    intro X
    have e0 := _root_.map_sum (IsLinearMap.mk' _ hlin) (fun i => FB.toK T.Fr (X i)) Finset.univ
    simp only [IsLinearMap.mk'_apply] at e0
    rw [← e0]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [FB.toK, _root_.map_sum]
  have e2 : ∀ (t : T.V) (Y : PS T.V n (chD C.ch)), nabValN B T.Fr (gaugeOf C) H.w0 (N ^ 2) (FB.toK T.Fr (t • Y))
      (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) =
      algebraMap T.V T.Fr t * nabValN B T.Fr (gaugeOf C) H.w0 (N ^ 2) (FB.toK T.Fr Y)
      (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
    intro t Y
    have e0 := hlin.map_smul (algebraMap T.V T.Fr t) (FB.toK T.Fr Y)
    simp only [smul_eq_mul] at e0
    rw [← e0]
    congr 1
    simp only [FB.toK, MvPowerSeries.smul_eq_C_mul, _root_.map_mul, MvPowerSeries.map_C]
  have e3 := GlobalTheory.T.connectionValueLevel_kappa_mul_pullback T.V (chD C.ch) (𝓞 E) B T.Fr (gaugeOf C) H.w0 hg0 n (p * q) (N ^ 2) κ hκ (E →+* ℂ) Dw.mult
    (fun τ => io.comp (embK c τ)) C.ch.uvec heig (MvPolynomial.map io P) g
  have mpush := map_pushL c io (p * q) P
  have hcard : (kerM B q).ncard = Nat.card {i : J // Kills Xo q (a i)} := by
    have hset : kerM B q = α '' {i | Kills Xo q (a i)} := by
      ext β
      constructor
      · intro hβ
        obtain ⟨i, rfl⟩ : β ∈ Set.range α := by
          rw [hrange]
          exact kerM_subset B p q hβ
        exact ⟨i, (h67 q (a i) (α i) (hα i)).mpr hβ, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact (h67 q (a i) (α i) (hα i)).mp hi
    rw [hset, Set.ncard_image_of_injective _ hinj]
    exact (Nat.card_coe_set_eq _).symm
  refine ⟨nabValN B T.Fr (gaugeOf C) H.w0 1 (FB.toK T.Fr g) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩)
      (MvPolynomial.map io (MvPolynomial.C s * pushL c ((p * q).map (algebraMap (𝓞 E) E)) P)),
    hbd e ρ w n hCh 1 _ hFF g, ?_⟩
  rw [Finset.sum_congr rfl (fun i _ => hhv i), e1, hg, e2, e3, ← mpush,
    _root_.map_mul (MvPolynomial.map io), MvPolynomial.map_C, nabValN_C_mul,
    _root_.map_mul (algebraMap T.V T.Fr), _root_.map_natCast (algebraMap T.V T.Fr), hjac p, hcard, _root_.map_prod]
  simp only [_root_.map_pow, RingHom.coe_comp, Function.comp_apply]
  ring

end GlobalTheory.PlaceInt.FormSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumHarmonicValuesFormalKernelSimilitudeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_harmonicValues_formalKernel_similitude : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (N k M : ℕ) (p q : Matrix (Fin n) (Fin n) (𝓞 E)), Odd N → IsSim H (p * q) (N ^ 2) → N ^ 2 = k * M → Nat.Coprime k ℓ → AllRat Xo (xOf y) M → ∀ (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)), Function.Injective a → (∀ u : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ i, a i = u) ↔ (Kills Xo (p * q) u ∧ ∀ b, ∃ α, FormPt C (u b) α)) → ∀ (F : Fin n → SecN Xo (xOf y) (N ^ 2)) (G : J → Fin n → SecN Xo (xOf y) (N ^ 2)), (∀ b, Regular C (N ^ 2) (F b)) → (∀ i b, Moves Xo (a i b) (F b) (G i b)) → (∀ i, Kills Xo q (a i) → ∃ r : Fin n → T.V, ∏ b, r b = 1 ∧ ∀ b j, (G i b).f j = liftFun Xo.univ.t.G _ (T := ptO Xo (xOf y)) (toΓ T.Fr (algebraMap T.V T.Fr (r b))) * (F b).f j) → ∀ (P : MvPolynomial (LtN Dw n) c.F) (s : c.F), P ∈ HH c w n → MvPolynomial.map io (MvPolynomial.C s * pushL c ((p * q).map (algebraMap (𝓞 E) E)) P) ∈ FFV (Dw := Dw) T w n → letI := io.toAlgebra; ∃ z : T.Fr, ((-ρ : ℝ) : EReal) ≤ nval T.V e z ∧ io s * ∑ i, hv Xo c nab y.1 (N ^ 2) (G i) P = (Nat.card {i : J // Kills Xo q (a i)} : T.Fr) * io (∏ τ : E →+* ℂ, embK c τ p.det ^ Dw.mult τ) * z := by
  first | exact @GlobalTheory.PlaceInt.FormSum.sum_hv_formal_kernel | exact GlobalTheory.PlaceInt.FormSum.sum_hv_formal_kernel | (intros; apply GlobalTheory.PlaceInt.FormSum.sum_hv_formal_kernel <;> assumption)
end
