module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameAdjointnessSeriesTrivial
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticLineBundleFrameEqAppellHumbert
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameFirstPartialLawTrivial
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSecondPartialLawTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameExponentialImmersionAtOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameExponentialImmersionAtOrigin
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameImm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

section Group

variable {g : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}

theorem deriv_one (h0 : e 0 = (1 : Over.mk y ⟶ G).left) : IsDerivAt0 e 0 (1 : epsPt y ⟶ G).left := by
  let φ : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have h1 : (1 : epsPt y ⟶ G).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 := by
    rw [h0, ← MonObj.comp_one φ]
    rfl
  have h2 : spMap GlobalTheory.TangentOrigin.fstC ≫ spMap (algebraMap ℂ (DualNumber ℂ)) ≫ e 0 = e 0 := by
    rw [← Category.assoc, GlobalTheory.FrameTangent.spMap_comp']
    have : GlobalTheory.TangentOrigin.fstC.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
      RingHom.ext fun r => by simp
    rw [this]
    simp [spMap]
  rw [h1, GlobalTheory.PointUnif.isDerivAt0_iff]
  refine ⟨h2, fun U hU f => ?_⟩
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h2 ▸ (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp _ _ U hU0 hU, map_zero]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem deriv_list (h0 : e 0 = (1 : Over.mk y ⟶ G).left) :
    ∀ (m : ℕ) (w : Fin m → Fin g → ℂ) (v : Fin m → (epsPt y ⟶ G)), (∀ i, IsDerivAt0 e (w i) (v i).left) →
      IsDerivAt0 e (∑ i, w i) (List.ofFn v).prod.left
  | 0, w, v, _ => by simpa using deriv_one h0
  | m + 1, w, v, h => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons]
    exact GlobalTheory.PointUnif.deriv_mul h0 (h 0) (deriv_list h0 m _ _ fun i => h i.succ)

end Group

theorem anPt_imm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm := by
  classical
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ w hw
  by_contra hcon
  push Not at hcon
  apply hw
  have he0 : Φ.e 0 = 1 := (Φ.e_ker 0).2 (zero_mem _)
  have h0 : (fun z => (Φ.e z).left) 0 = (1 : Over.mk y.x ⟶ Xo.univ.t.G).left := congrArg (·.left) he0
  have d0 := deriv_one (e := fun z => (Φ.e z).left) h0
  have dw : IsDerivAt0 (fun z => (Φ.e z).left) w (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    refine ⟨d0.1, fun U hU f => (d0.2 U hU f).trans ?_⟩
    rw [map_zero]
    refine (hcon U f ?_).symm
    have h3 := (GlobalTheory.TangentOrigin.top_le_preimage_iff _ U).1 hU
    exact (congrArg (fun p : Sp ℂ ⟶ Xo.univ.t.G.left => ⊤ ≤ p ⁻¹ᵁ U) d0.1).mp h3
  let q := (Fintype.equivFin (Lt1 Dw)).symm
  have key : ∀ w' : Fin g → ℂ, IsDerivAt0 (fun z => (Φ.e z).left) w' (1 : epsPt y.x ⟶ Xo.univ.t.G).left →
      IsCombAt y.x (m := Fintype.card (Lt1 Dw)) (fun i => y.u (q i).1 (q i).2) (fun i => w' (el.symm (q i)))
        (1 : epsPt y.x ⟶ Xo.univ.t.G).left := by
    intro w' hw'
    let v : Fin (Fintype.card (Lt1 Dw)) → (epsPt y.x ⟶ Xo.univ.t.G) := fun i =>
      GlobalTheory.FrameTangent.smT y.x (w' (el.symm (q i)))
        (GlobalTheory.FrameTangent.ovT (t := Xo.univ.t) (y.tan (q i).1 (q i).2))
    refine ⟨v, fun i => rfl, GlobalTheory.PointUnif.deriv_unique ?_ hw'⟩
    have hs : w' = ∑ i, w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ) := by
      exact (pi_eq_sum_univ' w').trans
        (Equiv.sum_comp (q.trans el.symm) (fun j => w' j • (Pi.single j 1 : Fin g → ℂ))).symm
    have := deriv_list (e := fun z => (Φ.e z).left) h0 _
      (fun i => w' (el.symm (q i)) • (Pi.single (el.symm (q i)) 1 : Fin g → ℂ)) v
      fun i => GlobalTheory.PointUnif.deriv_smul (Φ.der (q i)) _
    rwa [← hs] at this
  have ht : IsTanAt y.x (1 : epsPt y.x ⟶ Xo.univ.t.G).left := ⟨Over.w _, d0.1.trans h0⟩
  have hu := (GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c ℂ y _ ht).unique
    (y₁ := fun ℓ => w (el.symm ℓ)) (y₂ := fun ℓ => (0 : Fin g → ℂ) (el.symm ℓ)) (key w dw) (key 0 d0)
  funext j
  simpa using congrFun hu (el j)

end GlobalTheory.FrameImm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameExponentialImmersionAtOriginStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFrame_exponential_immersion_at_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm := by
  first | exact @GlobalTheory.FrameImm.anPt_imm | exact GlobalTheory.FrameImm.anPt_imm | (intros; apply GlobalTheory.FrameImm.anPt_imm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameJetPairIsAnE
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameJetPairIsAnE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem jetMap_psum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el) (n m : ℕ) (xs : Fin n → (jO y g m n ⟶ Xo.univ.t.G))
    (Λ : Fin n → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hx : ∀ i, Φ.toAnFr.JetMap m (xs i).left (Λ i))
    (I : Finset (Fin n)) :
    Φ.toAnFr.JetMap m (psum Xo.univ.t.G xs I).left (∑ i ∈ I, Λ i) := by
  obtain ⟨-, h1, hmul, -⟩ := GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ n m
  have key : ∀ L : List (Fin n), Φ.toAnFr.JetMap m
      (L.foldr (fun k acc => padd Xo.univ.t.G (xs k) acc) (pzero Xo.univ.t.G (jO y g m n))).left
      (L.map Λ).sum := by
    intro L
    induction L with
    | nil => exact h1
    | cons k L ih => exact (hmul _ _ _ _ (hx k) ih).1
  have hs : (((List.finRange n).filter (fun x => decide (x ∈ I))).map Λ).sum = ∑ i ∈ I, Λ i := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    congr 1
    ext i
    simp
  rw [← hs]
  exact key _

theorem exists_isAnE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∃ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ
  have h : ∀ m, ∃ τ : FrTy y g Φ.jx m, τ.IsGen ∧ Φ.toAnFr.JetRd m
      (cφ ![jpt y g Φ.jx m (0 : Fin 2), jpt y g Φ.jx m (1 : Fin 2)]) (cε 2) τ (psumL 2 g) := by
    intro m
    refine GlobalTheory.T.exists_generator_jet_reading _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 m _
      (cφ ![jpt y g Φ.jx m (0 : Fin 2), jpt y g Φ.jx m (1 : Fin 2)]) (cε 2) (psumL 2 g) ?_
    intro I
    refine jetMap_psum Φ 2 m _ (fun i => LinearMap.proj i) ?_ I.down
    have h0 := (GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ 2 m).1
    intro i
    fin_cases i
    · exact h0 0
    · exact h0 1
  choose e he using h
  exact ⟨e, he⟩

end GlobalTheory.AnVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameJetPairIsAnEStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticFrame_jetPair_isAnE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∃ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e := by
  first | exact @GlobalTheory.AnVal.exists_isAnE | exact GlobalTheory.AnVal.exists_isAnE | (intros; apply GlobalTheory.AnVal.exists_isAnE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSymmetryTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSymmetryTrivial
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal.Sym

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem tay_coord {g : ℕ} (k : Fin g) :
    tay (fun v : Fin g → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin g → ℂ => v k) 0 := (contDiff_apply ℂ (fun _ => ℂ) k).contDiffAt
  have eq_of_cc (F G : MvPowerSeries (Fin 1 × Fin g) ℂ)
      (h : ∀ l : List (Fin 1 × Fin g), MvPowerSeries.constantCoeff (l.foldr (fun q H => MvPowerSeries.pderiv q H) F) =
        MvPowerSeries.constantCoeff (l.foldr (fun q H => MvPowerSeries.pderiv q H) G)) : F = G := by
    have coeff_foldr (l : List (Fin 1 × Fin g)) (m : (Fin 1 × Fin g) →₀ ℕ) :
        ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPowerSeries (Fin 1 × Fin g) ℂ,
          MvPowerSeries.coeff m (l.foldr (fun q G => MvPowerSeries.pderiv q G) F) =
            c * MvPowerSeries.coeff (m + (l.map fun q => Finsupp.single q 1).sum) F := by
      induction l generalizing m with
      | nil => exact ⟨1, one_ne_zero, fun F => by simp⟩
      | cons q l ih =>
        obtain ⟨c, hc, hF⟩ := ih (m + Finsupp.single q 1)
        refine ⟨c * ((m q : ℂ) + 1), mul_ne_zero hc (Nat.cast_add_one_ne_zero _), fun F => ?_⟩
        simp only [List.foldr_cons]
        rw [MvPowerSeries.coeff_pderiv, hF, List.map_cons, List.sum_cons, add_assoc]
        ring
    have sum_single_toList (m : (Fin 1 × Fin g) →₀ ℕ) :
        ((Finsupp.toMultiset m).toList.map fun q => Finsupp.single q 1).sum = m := by
      have hs : ∀ t : Multiset (Fin 1 × Fin g), (t.map fun q => Finsupp.single q 1).sum = Multiset.toFinsupp t := by
        intro t
        induction t using Multiset.induction_on with
        | empty => simp
        | cons a t ih =>
          rw [Multiset.map_cons, Multiset.sum_cons, ih, ← Multiset.singleton_add, Multiset.toFinsupp_add,
            Multiset.toFinsupp_singleton]
      have h2 := hs (Finsupp.toMultiset m)
      rw [Finsupp.toMultiset_toFinsupp] at h2
      calc
        _ = (Multiset.map (fun q => Finsupp.single q 1) (Finsupp.toMultiset m)).sum := by
          rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]
        _ = m := h2
    ext m
    have h1 := h (Finsupp.toMultiset m).toList
    obtain ⟨c, hc, h0⟩ := coeff_foldr (Finsupp.toMultiset m).toList 0
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      h0, h0, zero_add, sum_single_toList] at h1
    exact mul_left_cancel₀ hc h1
  refine eq_of_cc _ _ fun l => ?_
  rcases l.eq_nil_or_concat with rfl | ⟨l', ⟨a, j⟩, rfl⟩
  · simp only [List.foldr_nil, constantCoeff_tay, TM.mD_zero, MvPowerSeries.constantCoeff_X, Pi.zero_apply]
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    have hd : (fun y : Fin g → ℂ => fderiv ℂ (fun v : Fin g → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j (1 : ℂ) : Fin g → ℂ) k := by
      funext y
      exact congrArg (fun T : (Fin g → ℂ) →L[ℂ] ℂ => T (Pi.single j 1))
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g => ℂ) k).fderiv
    rw [List.concat_eq_append, List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hθ, hd, TM.tay_const, MvPowerSeries.pderiv_X]
    congr 2
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h, Pi.single_apply]


theorem psJet_X {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (s : κ) :
    psJet m (MvPowerSeries.X s : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X s) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem jetN_coord {n g : ℕ} (m : ℕ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j) = Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  unfold jetN jetOf
  show renN n g m (psJet m (tay (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) 0)) = _
  rw [tay_coord, psJet_X]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

def swapL (g : ℕ) : (Fin 2 → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Equiv.swap (0 : Fin 2) 1 i)

def swapI : ULift.{0} (Finset (Fin 2)) ≃ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.finsetCongr (Equiv.swap (0 : Fin 2) 1)).trans Equiv.ulift.symm)

theorem psumL_swap (g : ℕ) (I : ULift.{0} (Finset (Fin 2))) :
    psumL 2 g I ∘ₗ swapL g = psumL 2 g (swapI I) := by
  refine LinearMap.ext fun w => ?_
  simp [psumL, swapL, swapI, Equiv.finsetCongr_apply]

theorem cε_swap (I : ULift.{0} (Finset (Fin 2))) : cε 2 (swapI I) = cε 2 I := by
  simp [cε, swapI, Equiv.finsetCongr_apply]

theorem jetMap_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n m : ℕ} {ψ ψ' : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) (h' : Φ.JetMap m ψ' Λ) : ψ = ψ' := by
  obtain ⟨_, rfl⟩ := h
  obtain ⟨_, rfl⟩ := h'
  rfl

theorem sy_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m (anFB ty).sy ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m) (scaleGen _ _ (unitΓ u⁻¹) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e he m
  refine ⟨1, ?_, ?_⟩
  · show (1 : Jet ℂ (Fin 2 × Fin g) m) = psJet m 1
    rw [← MvPolynomial.coe_one, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, map_one]
  have hR := (he m).2
  have hS := GlobalTheory.T.jetReading_linearSubstitution_points _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr 2 2 m (swapL g)
    (fun p : Fin 2 × Fin g => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] :
      Fin 2 → Fin g → MvPolynomial (Fin 2 × Fin g) ℂ) p.1 p.2) (by
      rintro ⟨i, j⟩
      rw [psJet_X]
      refine Eq.trans ?_ (jetN_coord m (Equiv.swap (0 : Fin 2) 1 i) j).symm
      show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
      fin_cases i <;> simp) _ _ _ _ _ hR
  have hC := GlobalTheory.T.corr_of_jets_of_analytic_frame_products _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hI 2 m _ _ _ _ _ _ _ _ _ _ hR hS (by
    intro ψ
    refine (Fintype.sum_equiv swapI _ _ fun I => ?_).symm
    have h1 := hS.1 I
    beta_reduce at h1 ⊢
    rw [psumL_swap] at h1
    rw [jetMap_unique _ h1 (hR.1 (swapI I)), cε_swap])
  intro j j' h1 h2 h3
  refine (hC j j' h1 h2 h3).trans ?_
  congr 1
  show _ = res le_top (unitΓ (1 : (Jet ℂ (Fin 2 × Fin g) m)ˣ)⁻¹) * _
  rw [inv_one, unitΓ, map_one]
  have : ∀ (X : Scheme.{0}) (U : X.Opens), res (le_top : U ≤ ⊤) (1 : Γ(X, ⊤)ˣ) = 1 := fun X U => map_one _
  rw [this]
  exact (_root_.one_mul _).symm

end GlobalTheory.AnVal.Sym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameSymmetryTrivialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFrame_symmetry_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m (anFB ty).sy ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m) (scaleGen _ _ (unitΓ u⁻¹) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)])) := by
  first | exact @GlobalTheory.AnVal.Sym.sy_trivial | exact GlobalTheory.AnVal.Sym.sy_trivial | (intros; apply GlobalTheory.AnVal.Sym.sy_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameExponentialJetsIsChart
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameExponentialJetsIsChart
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal

attribute [local instance] Over.cartesianMonoidalCategory

theorem chart_isHolFam_comp_clm {Y : Scheme.{0}} {g N : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (A : (Fin N → ℂ) →L[ℂ] (Fin g → ℂ)) : IsHolFam fun v => e (A v) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage A.continuous, h2.comp A.differentiable.differentiableOn fun _ hv => hv⟩

theorem chart_holTo_of_isHolFam {Y : Scheme.{0}} {N : ℕ} {e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolFam e) :
    IsHolTo Set.univ e := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  simp only [Set.mem_univ, true_and]
  exact ⟨h1, h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
  {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem AnPt.chart_jx_left (m : ℕ) : (Φ.jx m).left = jetPt (fun z => (Φ.e z).left) Φ.hol m := rfl

theorem AnPt.chart_e_zero : Φ.e 0 = 1 := by
  have h := Φ.e_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem AnPt.chart_trunc (m : ℕ) :
    homAt y.x (jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) ≫ Φ.jx (m + 1) =
      Φ.jx m := by
  ext1
  rw [Over.comp_left, Φ.chart_jx_left, Φ.chart_jx_left]
  exact jetPt_trunc _ _ m

theorem AnPt.chart_zero (m : ℕ) :
    homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) ≫ Φ.jx m = 1 := by
  ext1
  rw [Over.comp_left, Φ.chart_jx_left, one_left'']
  have h1 := jetPt_aug (fun z => (Φ.e z).left) Φ.hol m
  refine h1.trans ?_
  show (Φ.e 0).left = _
  rw [Φ.chart_e_zero, one_left'']
  show y.x ≫ _ = (spMap (algebraMap ℂ ℂ) ≫ y.x) ≫ _
  rw [Algebra.algebraMap_self, spMap]
  simp

theorem AnPt.chart_act (m : ℕ) (a : 𝓞 E) :
    Φ.jx m ≫ Xo.univ.t.act.act a =
      homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2)) ≫ Φ.jx m := by
  ext1
  rw [Over.comp_left, Over.comp_left, Φ.chart_jx_left]
  have hlin : ∀ z, (Φ.e z).left ≫ (Xo.univ.t.act.act a).left = (Φ.e (fun k => ty k (a : E) * z k)).left := by
    intro z
    rw [← Over.comp_left, ← Φ.lin a z]
    rfl
  have hol' := isHolFam_comp (fun z => (Φ.e z).left) Φ.hol (Xo.univ.t.act.act a).left
  rw [jetPt_comp (fun z => (Φ.e z).left) Φ.hol _ _ hol' (fun z => rfl)]
  haveI : IsLocalHom ((jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) :
        Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) :=
    isLocalHom_jetMap (m := m)
      (fun p : Fin 1 × Fin g => psTrunc m (anAct ty a p.2) -
        MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m (anAct ty a p.2))))
      (fun _ => sub_const_mem_orig _)
  symm
  refine jetPt_precomp (fun z => (Φ.e z).left) _ Φ.hol hol' ?_ m _ ?_
  · show (Φ.e 0).left ≫ _ = (Φ.e 0).left
    rw [hlin]; congr 2; funext k; simp
  · intro U hU f
    change jetSubstP m _ (jetOf m _) = _
    rw [jetSubstP_anAct, ← jetOf_scale m _ (contDiffAt_val _ Φ.hol hU f)]
    congr 1
    funext z
    show valAt' (Φ.e _).left U f = valAt' ((Φ.e z).left ≫ _) U f
    rw [hlin]

theorem AnPt.chart_tan (j0 : Fin g) (vt : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)
    (hd : IsDerivAt0 (fun z => (Φ.e z).left) (Pi.single j0 1) vt) :
    IsCombAt y.x (m := g)
      (fun j => (homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫
        Φ.jx (0 + 1)).left) (fun j => if j = j0 then 1 else 0) vt := by
  classical
  let v : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j =>
    homAt y.x (jetTan ((0 : Fin 1), j) : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) ≫ Φ.jx (0 + 1)
  let u : Fin g → (tEps y.x ⟶ Xo.univ.t.G) := fun j => epsHom y.x (if j = j0 then 1 else 0) ≫ v j
  refine ⟨u, fun j => by simp [u, v, epsHom], ?_⟩
  have hone : ∀ j, j ≠ j0 → u j = 1 := by
    intro j hj
    ext1
    simp only [u, v, if_neg hj, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left]
    rw [← Category.assoc, spMap_epsMul_zero_jetTan, Category.assoc, jetPt_aug, one_left'']
    show spMap _ ≫ (Φ.e 0).left = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y.x) ≫ _
    rw [Φ.chart_e_zero, one_left'', Category.assoc]
    rfl
  have hprod : (List.ofFn u).prod = u j0 := by
    rw [List.prod_ofFn, Finset.prod_eq_single j0 (fun j _ hj => hone j hj) (by simp)]
  rw [hprod]
  simp only [u, v, if_pos rfl, ite_true, Over.comp_left, epsHom, Over.homMk_left, Formalism.L2.Pj.homAt, AnPt.chart_jx_left,
    epsMul_one]
  rw [show spMap (RingHom.id (DualNumber ℂ)) = 𝟙 _ from by simp [spMap]]
  exact (Category.id_comp _).trans (jetPt_tan (fun z => (Φ.e z).left) Φ.hol ((0 : Fin 1), j0) vt hd)

theorem AnPt.chart_pair : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (Φ.e (anPr 0 v)).left (Φ.e (anPr 1 v)).left
        ((Over.w (Φ.e (anPr 0 v))).trans (Over.w (Φ.e (anPr 1 v))).symm) :=
  chart_holTo_of_isHolFam (isHolFam_pullback_lift _ _ _ Xo.univ.t.G.hom Xo.univ.t.G.hom (2 * g)
    (fun v => (Φ.e (anPr 0 v)).left) (fun v => (Φ.e (anPr 1 v)).left) y.x
    (fun v => Over.w (Φ.e (anPr 0 v))) (fun v => Over.w (Φ.e (anPr 1 v)))
    (chart_isHolFam_comp_clm _ Φ.hol (anPr 0)) (chart_isHolFam_comp_clm _ Φ.hol (anPr 1)))

theorem AnPt.chart_law (m : ℕ) :
    homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) ≫ Φ.jx m =
      jpt y g Φ.jx m (0 : Fin 2) * jpt y g Φ.jx m (1 : Fin 2) :=
  jets_law y.x Φ.e Φ.hol Φ.jx (fun _ => rfl) Φ.e_add Φ.chart_pair m

theorem anPt_isChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el),
    IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec el) Φ.jx :=
  fun _ _ _ _ _ _ _ _ _ _ _ y _ _ el Φ =>
    { zero := fun m => Φ.chart_zero m
      trunc := fun m => Φ.chart_trunc m
      law := fun m => Φ.chart_law m
      act := fun m a => Φ.chart_act m a
      tan := fun ℓ => Φ.chart_tan (el.symm ℓ) (y.u ℓ.1 ℓ.2) (Φ.der ℓ)
      basis := fun v => basis_single el v }

end GlobalTheory.AnVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameExponentialJetsIsChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFrame_exponential_jets_isChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec el) Φ.jx := by
  first | exact @GlobalTheory.AnVal.anPt_isChart | exact GlobalTheory.AnVal.anPt_isChart | (intros; apply GlobalTheory.AnVal.anPt_isChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSection
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSection
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetVal

open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

section Pt

variable {K : Type} [Field K] {σ : Type} {m : ℕ}

theorem jet_pt_eq (p : PrimeSpectrum (Jet K σ m)) : p = IsLocalRing.closedPoint (Jet K σ m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_jetAug _ (by rwa [jetAug_mk]))
    have := jet_nilpotent_of_orig K σ m (sub_const_mem_orig (R := K) q)
    rwa [h0, map_zero, sub_zero] at this
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

end Pt

theorem gs_appLE_top {Y X : Scheme.{0}} (φ : Y ⟶ X) (y : Y) (U : X.Opens) (h : ⊤ ≤ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs φ y U a = gs (𝟙 Y) y ⊤ ((φ.appLE U ⊤ h).hom a) := by
  have hy : φ y ∈ U := h trivial
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, gs_res (𝟙 Y) y h trivial, gs_pull (𝟙 Y) φ y U hy, Category.id_comp]

section PullSec

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A)
  (hh : h ≫ snd T A = snd T' A)

def pullSecF (s : LB.Sec (LPow A L a T)) (j : Fin 1 → L.ι) : Γ((T' ⊗ A).left, (LPow A L a T').U j) :=
  ((T' ⊗ A).left.presheaf.map (homOfLE (chart_le_res A L h hh a j)).op).hom ((h.left.app _).hom (s.f j))

def pullSecLP (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') where
  f := pullSecF A L a h hh s
  compat i j := fn_ext fun y hy => by
    have hi : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) i := chart_le_res A L h hh a i hy.1
    have hj : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) j := chart_le_res A L h hh a j hy.2
    have v : ∀ j', y ∈ (LPow A L a T').U j' → gs (𝟙 _) y _ (pullSecF A L a h hh s j') =
        gs (𝟙 _ ≫ h.left) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j') (s.f j') := fun j' hj' =>
      (gs_res _ y _ hj' _).trans (gs_pull _ h.left y _ (chart_le_res A L h hh a j' hj') _)
    refine ((gs_res (𝟙 _) y _ hy _).trans ((v i hy.1).trans (sec_trans s (𝟙 _ ≫ h.left) y hi hj))).trans ?_
    refine Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm
    refine congrArg₂ (· * ·) ?_ ((v j hy.2).symm.trans (gs_res (𝟙 _) y _ hy _).symm)
    refine Eq.trans ?_ (gs_unit (𝟙 _) y _ hy _).symm
    refine congrArg Units.val (Eq.trans ?_
      (gm_linComb L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) (𝟙 _) y i j hy.1 hy.2).symm)
    simp only [trF, Category.assoc, ← Over.comp_left, hh]

theorem isPullSec_pullSecLP (s : LB.Sec (LPow A L a T)) : IsPullSec A L a h hh s (pullSecLP A L a h hh s) :=
  fun _ => rfl

end PullSec

section Fam

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (L : LB G.left) {x0 : Sp ℂ ⟶ X} {g : ℕ}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (hol : IsHolFam e) (he : ∀ z, e z ≫ G.hom = x0)

def jB (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 :=
  Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m))) rfl

def xJ (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ G :=
  Over.homMk (jetPt e hol m) (jetPt_over e hol G.hom x0 he m)

def ePt (z : Fin g → ℂ) : Over.mk x0 ⟶ G := Over.homMk (e z) (he z)

def lftJ (z : Fin g → ℂ) : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left := (ptSecT G (ePt e he z)).left

theorem lftJ_snd (z : Fin g → ℂ) : lftJ e he z ≫ (snd (Over.mk x0) G).left = e z := by
  rw [lftJ, ← Over.comp_left, ptSecT, lift_snd]
  rfl

theorem lftJ_fst (z : Fin g → ℂ) : lftJ e he z ≫ (fst (Over.mk x0) G).left = 𝟙 _ := by
  rw [lftJ, ← Over.comp_left, ptSecT, lift_fst]
  rfl

theorem lftJ_eq (holP : IsHolFam (lftJ e he)) (m : ℕ) :
    (ptSecT G (xJ e hol he m)).left ≫ (jB (x0 := x0) (g := g) m ▷ G).left = jetPt (lftJ e he) holP m := by
  have h1 : jetPt (lftJ e he) holP m ≫ (Over.mk x0 ⊗ G).hom =
      spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) ≫ x0 :=
    jetPt_over (lftJ e he) holP _ x0 (fun z => Over.w (ptSecT G (ePt e he z))) m
  let φ : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 ⊗ G := Over.homMk (jetPt (lftJ e he) holP m) h1
  suffices hs : ptSecT G (xJ e hol he m) ≫ jB m ▷ G = φ by
    rw [← Over.comp_left, hs]
    rfl
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, whiskerRight_fst, ptSecT, lift_fst_assoc, Category.id_comp]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    show spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)) = jetPt (lftJ e he) holP m ≫ (fst (Over.mk x0) G).left
    rw [jetPt_comp (lftJ e he) holP _ (fun _ => 𝟙 (Sp ℂ)) (isHolFam_const _) (lftJ_fst e he) m, ← jetPt_const,
      Category.comp_id]
  · rw [Category.assoc, whiskerRight_snd, ptSecT, lift_snd]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    show jetPt e hol m = jetPt (lftJ e he) holP m ≫ (snd (Over.mk x0) G).left
    rw [jetPt_comp (lftJ e he) holP _ e hol (lftJ_snd e he) m]

theorem isValueAt_jet (holP : IsHolFam (lftJ e he)) (m k : ℕ)
    (F : LB.Sec (LPow G L (k : ℤ) (Over.mk x0)))
    (F' : LB.Sec (LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))))
    (hF' : IsPullSec G L (k : ℤ) (jB m ▷ G) (whiskerRight_snd _ _) F F')
    (θF : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ)
    (hfr : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j})
    (hfr0 : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (hrd : ∀ j z (pt : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left), pt ≫ (snd (Over.mk x0) G).left = e z →
      pt ≫ (fst (Over.mk x0) G).left = 𝟙 (Sp ℂ) → ⊤ ≤ e z ⁻¹ᵁ L.U j →
      valAt' pt ((LPow G L (k : ℤ) (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θF z * fr j z ^ (k : ℤ))
    (τ : LB.Gen (LB.LinComb L (Y := (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) (K := Fin 1)
      (fun _ => (xJ e hol he m).left) (fun _ => (k : ℤ))))
    (hτ : ∀ (j : Fin 1 → L.ι) (h : ⊤ ≤ LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) j),
      ((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left.presheaf.map (homOfLE h).op).hom (τ.s j).val =
        toΓ _ (jetOf m (fun z => fr (j 0) z ^ k))) :
    IsValueAt G L (k : ℤ) F' (xJ e hol he m) τ (toΓ _ (jetOf m θF)) := by
  intro j
  obtain ⟨j0, rfl⟩ : ∃ j0, j = fun _ => j0 := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine fn_ext fun x hx => ?_
  let Φ := (ptSecT G (xJ e hol he m)).left
  let Ψ := (jB (x0 := x0) (g := g) m ▷ G).left
  let U := (LPow G L (k : ℤ) (Over.mk x0)).U (fun _ => j0)
  have key : Φ ≫ Ψ = jetPt (lftJ e he) holP m := lftJ_eq e hol he holP m
  have hW : ⊤ ≤ LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) (fun _ => j0) := fun p _ => by
    have e1 := jet_pt_eq (K := ℂ) (σ := Fin 1 × Fin g) (m := m) p
    have e2 := jet_pt_eq (K := ℂ) (σ := Fin 1 × Fin g) (m := m) x
    rw [e1, ← e2]
    exact hx
  have hmem1 : ∀ p, Φ p ∈ (LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))).U (fun _ => j0) := fun p =>
    val_le G L (xJ e hol he m) (fun _ => j0) (hW (show p ∈ (⊤ : (Sp (Jet ℂ (Fin 1 × Fin g) m)).Opens) from trivial))
  have hmem : ∀ p, Ψ (Φ p) ∈ U := fun p =>
    chart_le_res G L (T := Over.mk x0) (T' := overAt x0 (Jet ℂ (Fin 1 × Fin g) m)) (jB (x0 := x0) (g := g) m ▷ G)
      (whiskerRight_snd _ _) (k : ℤ) (fun _ => j0) (hmem1 p)
  have hU' : ⊤ ≤ jetPt (lftJ e he) holP m ⁻¹ᵁ U := fun p _ => by
    have h2 := hmem p
    rw [← Scheme.Hom.comp_apply, key] at h2
    exact h2
  have hU : lftJ e he 0 cpt ∈ U := by
    have h3 : jetPt (lftJ e he) holP m (IsLocalRing.closedPoint _) ∈ U := hU' trivial
    rwa [jetPt_closedPoint] at h3
  have hU0 : e 0 cpt ∈ L.U j0 := by
    have h4 : (snd (Over.mk x0) G).left (lftJ e he 0 cpt) ∈ L.U j0 := Set.mem_iInter.1 hU 0
    rwa [← Scheme.Hom.comp_apply, lftJ_snd] at h4

  have heq : ∀ᶠ z in nhds 0, valAt' (lftJ e he z) U (F.f (fun _ => j0)) = θF z * fr j0 z ^ k :=
    (eventually_mem e hol hU0).mono fun z hz => by
      rw [hrd j0 z (lftJ e he z) (lftJ_snd e he z) (lftJ_fst e he z) hz, zpow_natCast]
  have hval : ContDiffAt ℂ ω (fun z => valAt' (lftJ e he z) U (F.f (fun _ => j0))) 0 :=
    contDiffAt_val (lftJ e he) holP hU _
  have hfrA : ContDiffAt ℂ ω (fr j0) 0 :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ e z ⁻¹ᵁ L.U j0} (fr j0) (hol (L.U j0) 0).1 (hfr j0) 0
      (top_le_of_mem hU0)).contDiffAt
  have hfrk : ContDiffAt ℂ ω (fun z => fr j0 z ^ k) 0 := hfrA.pow k
  have hθ : ContDiffAt ℂ ω θF 0 := by
    refine (hval.div hfrk (pow_ne_zero _ (hfr0 j0 0 (top_le_of_mem hU0)))).congr_of_eventuallyEq ?_
    filter_upwards [heq, eventually_mem e hol hU0] with z hz hz'
    exact eq_div_of_mul_eq (pow_ne_zero _ (hfr0 j0 z hz')) hz.symm
  have hjet : jetOf m (fun z => valAt' (lftJ e he z) U (F.f (fun _ => j0))) =
      jetOf m θF * jetOf m (fun z => fr j0 z ^ k) := by
    rw [jetOf_congr m heq]
    exact jetOf_mul m hθ hfrk

  have s1 : gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x
      (LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) (fun _ => j0))
      ((((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left).presheaf.map
        (homOfLE (val_le G L (xJ e hol he m) (fun _ => j0))).op).hom
          (((ptSecT G (xJ e hol he m)).left.app _).hom (F'.f (fun _ => j0)))) =
      gs Φ x ((LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))).U (fun _ => j0)) (F'.f (fun _ => j0)) :=
    (gs_res (𝟙 _) x (val_le G L (xJ e hol he m) (fun _ => j0)) hx _).trans
      ((gs_pull (𝟙 _) Φ x _ (hmem1 x) _).trans (by rw [Category.id_comp]))
  have s2 : gs Φ x ((LPow G L (k : ℤ) (overAt x0 (Jet ℂ (Fin 1 × Fin g) m))).U (fun _ => j0)) (F'.f (fun _ => j0)) =
      gs (Φ ≫ Ψ) x U (F.f (fun _ => j0)) := by
    rw [hF' (fun _ => j0)]
    exact (gs_res Φ x (chart_le_res G L (T := Over.mk x0) (T' := overAt x0 (Jet ℂ (Fin 1 × Fin g) m))
        (jB (x0 := x0) (g := g) m ▷ G) (whiskerRight_snd _ _) (k : ℤ) (fun _ => j0)) (hmem1 x) _).trans
      (gs_pull Φ Ψ x U (hmem x) _)
  have s3 : gs (Φ ≫ Ψ) x U (F.f (fun _ => j0)) = gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x ⊤
      (toΓ _ (jetOf m θF * jetOf m (fun z => fr j0 z ^ k))) := by
    rw [key, gs_appLE_top _ x U hU', jetPt_appLE (lftJ e he) holP m U hU hU', CommRingCat.comp_apply, jetψ_apply,
      ← hjet]
    rfl

  have r1 : gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x
      (LB.wchart L (fun _ : Fin 1 => (xJ e hol he m).left) (fun _ => j0))
      ((((overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left).presheaf.map (homOfLE le_top).op).hom
          (toΓ _ (jetOf m θF)) * (τ.s (fun _ => j0)).val) =
      gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x ⊤
        (toΓ _ (jetOf m θF * jetOf m (fun z => fr j0 z ^ k))) := by
    refine (gs_mul (𝟙 _) x _ hx _ _).trans ?_
    refine (congrArg₂ (· * ·) (gs_res (𝟙 _) x le_top hx _)
      ((gs_res (𝟙 _) x hW trivial (τ.s (fun _ => j0)).val).symm.trans
        (congrArg (gs (𝟙 (overAt x0 (Jet ℂ (Fin 1 × Fin g) m)).left) x ⊤) (hτ _ hW)))).trans ?_
    rw [← gs_mul (𝟙 _) x ⊤ trivial, ← map_mul]
  exact (s1.trans (s2.trans s3)).trans r1.symm

theorem isHolFam_lftJ (hol : IsHolFam e) : IsHolFam (lftJ e he) := by
  have hl : lftJ e he = fun z => Limits.pullback.lift (f := x0) (g := G.hom) (𝟙 (Sp ℂ)) (e z)
      ((Category.id_comp x0).trans (he z).symm) := by
    funext z
    rw [lftJ, ptSecT, Over.lift_left]
    rfl
  rw [hl]
  exact GlobalTheory.AnVal.isHolFam_pullback_lift X (Sp ℂ) G.left x0 G.hom g (fun _ => 𝟙 (Sp ℂ)) e x0 (fun _ => Category.id_comp x0) he
    (isHolFam_const _) hol

end Fam

def onePr (g : ℕ) : (Fin (1 * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (1 * g) => ℂ)
    (finProdFinEquiv ((0 : Fin 1), j))

theorem onePr_apply {g : ℕ} (v : Fin (1 * g) → ℂ) (j : Fin g) : onePr g v j = v (finProdFinEquiv ((0 : Fin 1), j)) :=
  rfl

theorem anLin_onePr {g : ℕ} (p : Fin 1 × Fin g) :
    anLin (onePr g) p = MvPolynomial.X ((0 : Fin 1), finProdFinEquiv ((0 : Fin 1), p.2)) := by
  rw [anLin, Finset.sum_eq_single (finProdFinEquiv ((0 : Fin 1), p.2))]
  · rw [onePr_apply, Pi.single_eq_same, map_one]
    exact _root_.one_mul _
  · intro k _ hk
    rw [onePr_apply, Pi.single_eq_of_ne (Ne.symm hk), map_zero, zero_mul]
  · simp

theorem jetN_one {g : ℕ} (m : ℕ) {f : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) :
    jetN (n := 1) m (fun w => f (w 0)) = jetOf m f := by
  have h1 : (fun v => (fun w : Fin 1 → Fin g → ℂ => f (w 0)) (colsOf 1 g v)) = f ∘ onePr g := rfl
  rw [jetN, h1, jetOf_comp_anLin m hf, renN,
    anJetMap_comp _ _ _ _ (fun p => MvPolynomial.X p) (fun _ => X_mem_orig _) (fun p => by
      obtain ⟨a, j⟩ := p
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      simp only [anLin_onePr, MvPolynomial.aeval_X, Equiv.symm_apply_apply])]
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (jetOf m f)
  rw [← hp]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval MvPolynomial.X p) = _
  rw [MvPolynomial.aeval_X_left_apply]

theorem isValueAt_jetPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (m k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.Rd k F θ → Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → ∃ F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y g m 1)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y g m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧ IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (Φ.jx m) τ (toΓ _ (jetOf m θ)) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ m k F θ τ hF hτ
  have he : ∀ z, (Φ.e z).left ≫ Xo.univ.t.G.hom = y.x := fun z => Over.w (Φ.e z)
  refine ⟨pullSecLP _ _ _ _ (whiskerRight_snd _ _) F, isPullSec_pullSecLP _ _ _ _ _ F, ?_⟩
  refine isValueAt_jet Xo.univ.t.PP.L (fun z => (Φ.e z).left) Φ.hol he (isHolFam_lftJ _ he Φ.hol) m k F _
    (isPullSec_pullSecLP _ _ _ _ _ F) θ Φ.fr Φ.fr_hol Φ.fr_ne hF τ fun j h => ?_
  have hmem : jetPt (fun z => (Φ.e z).left) Φ.hol m (IsLocalRing.closedPoint _) ∈ Xo.univ.t.PP.L.U (j 0) :=
    Set.mem_iInter.1 (h trivial) 0
  rw [jetPt_closedPoint] at hmem
  have hA : ContDiffAt ℂ ω (Φ.fr (j 0)) 0 :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U (j 0)} (Φ.fr (j 0))
      (Φ.hol (Xo.univ.t.PP.L.U (j 0)) 0).1 (Φ.fr_hol (j 0)) 0 (top_le_of_mem hmem)).contDiffAt
  refine (hτ.2 j h).trans (congrArg _ ?_)
  rw [← jetN_one m (hA.pow k)]
  congr 1
  funext w
  simp

end GlobalTheory.JetVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsValueAtJetPointCmFrameSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isValueAt_jetPoint_cmFrame_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (m k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.Rd k F θ → Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → ∃ F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y g m 1)), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y g m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧ IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (Φ.jx m) τ (toΓ _ (jetOf m θ)) := by
  first | exact @GlobalTheory.JetVal.isValueAt_jetPt | exact GlobalTheory.JetVal.isValueAt_jetPt | (intros; apply GlobalTheory.JetVal.isValueAt_jetPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticBiextensionChartComplexPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] [StarRing (𝓞 E)] {y : FrPt Xo c ℂ} {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem isFrame_of_isAnE (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) :
    IsFrame y g Φ.jx (anFB ty).G.F (anFB ty).A.act (anFB ty).ph1 (anFB ty).ph2 (anFB ty).sy (anFB ty).ad e := by
  have hI := GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ
  exact ⟨fun m => (he m).1, GlobalTheory.T.analyticFrame_first_partial_law_trivial E H Dw l Xo c y g ty el Φ hI e he,
    GlobalTheory.T.analyticFrame_second_partial_law_trivial E H Dw l Xo c y g ty el Φ hI e he, GlobalTheory.T.analyticFrame_symmetry_trivial E H Dw l Xo c y g ty el Φ hI e he,
    GlobalTheory.T.analyticFrame_adjointness_series_trivial E H Dw l Xo c y g ty el Φ hI hst e he⟩

theorem isGerm_tay_of_rd (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (wP : PrimTy H Xo) (hw : IsPrim wP) (k : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ)
    (hF : Φ.toAnFr.Rd k F θ) : IsGerm y g Φ.jx (anFB ty).A.act e wP k F (tay θ 0) := by
  simp only [IsGerm]
  intro m
  have hJ : Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) :=
    (GlobalTheory.T.cmFrame_jetPoints_are_exponential_jets E H Dw l Xo c y g ty el Φ 1 m).2.2.2.2
  obtain ⟨τ, -, hτ⟩ := GlobalTheory.T.exists_generator_jet_reading _ _ _ _ _ Φ.toAnFr 1 m (Fin 1) (fun _ => (Φ.jx m).left) (fun _ => (k : ℤ))
    (fun _ => LinearMap.proj 0) (fun _ => hJ)
  obtain ⟨F', hpull, hval⟩ := GlobalTheory.T.isValueAt_jetPoint_cmFrame_section E H Dw l Xo c y g ty el Φ m k F θ τ hF hτ
  have hc := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ) e wP he hw).1 m k τ hτ
  exact ⟨F', τ, hpull, hc, hval⟩

noncomputable def AnPt.chartOf (hst : ∀ a : 𝓞 E, star a = H.bar a) (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e)
    (wP : PrimTy H Xo) (hw : IsPrim wP) : ChartAt Xo c y where
  d := g
  B := anFB ty
  uvec := anUvec el
  x := Φ.jx
  e := e
  wP := wP
  h := 0
  chart := GlobalTheory.T.cmFrame_exponential_jets_isChart E H Dw l Xo c y g ty el Φ
  frame := isFrame_of_isAnE Φ hst e he
  prim := hw
  gauge := anFB_canon ty
  rig0 := (GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert E H Dw l Xo c y g ty el Φ (GlobalTheory.T.analyticFrame_exponential_immersion_at_origin E H Dw l Xo c y g ty el Φ) e wP he hw).2

end

theorem rename_cast_refl {g : ℕ} (f : MvPowerSeries (Fin 1 × Fin g) ℂ) :
    MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) f = f := by
  have h : (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) = id := funext fun p => rfl
  rw [h]
  exact MvPowerSeries.rename_id_apply f

theorem exists_analytic_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hst
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_analyticFrame_jetPair_isAnE E H Dw l Xo c y g ty el Φ
  obtain ⟨wP, hw⟩ := (GlobalTheory.T.exists_normalisedIso_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ).1
  refine ⟨AnPt.chartOf Φ hst e he wP hw, rfl, rfl, ?_, ?_, ?_⟩
  · intro i
    first
      | rfl
      | simp [AnPt.chartOf, anFB, Germ.FB.triv, addFGLaw]
  · intro ℓ i'
    first
      | rfl
      | simp [AnPt.chartOf, anUvec, Pi.single_apply, eq_comm]
      | (simp only [AnPt.chartOf, anUvec]; done)
  · intro k F θ hF
    show IsGerm y g Φ.jx (anFB ty).A.act e wP k F
      (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast (rfl : g = g).symm p.2)) (tay θ 0))
    rw [rename_cast_refl]
    exact isGerm_tay_of_rd Φ e he wP hw k F θ hF

end GlobalTheory.AnVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticBiextensionChartComplexPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_biextension_chart_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), (∀ a : 𝓞 E, star a = H.bar a) → ∃ (C : ChartAt Xo c y) (hd : C.d = g), C.h = 0 ∧ (∀ i, C.B.G.F i = (MvPowerSeries.X (R := ℂ) ((0 : Fin 2), i) + MvPowerSeries.X (R := ℂ) ((1 : Fin 2), i))) ∧ (∀ (ℓ : Lt1 Dw) (i' : Fin C.d), C.uvec ℓ i' = if Fin.cast hd i' = el.symm ℓ then 1 else 0) ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (θ : (Fin g → ℂ) → ℂ), Φ.toAnFr.Rd k F θ → IsGerm y C.d C.x C.B.A.act C.e C.wP k F (MvPowerSeries.rename (fun p : Fin 1 × Fin g => (p.1, Fin.cast hd.symm p.2)) (tay θ 0)) := by
  first | exact @GlobalTheory.AnVal.exists_analytic_chart | exact GlobalTheory.AnVal.exists_analytic_chart | (intros; apply GlobalTheory.AnVal.exists_analytic_chart <;> assumption)
end
