module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsTorsionPointFiniteAdicCombinatio

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsRescaleByGeneratorMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsRescaleByGeneratorMultiple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
noncomputable section
namespace GlobalTheory.Mum.Rescale

theorem valF_resTop_scal {R F : Type} [CommRing R] [Field F] {X : Scheme.{0}} (p : X ⟶ Sp R) (f : R →+* F)
    (y : Sp F ⟶ X) (hy : y ≫ p = spMap f) (W : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ W) (r : R) :
    valF y W (resTop W (scal p r)) = f r := by
  have e1 : resTop W (scal p r) = (p.appLE ⊤ W (le_top.trans (by simp))).hom (ZH.fn r) := rfl
  rw [e1]
  refine (GlobalTheory.MatchCoord.valF_appLE p ⊤ _ h (ZH.fn r)).trans ?_
  rw [hy]
  exact GlobalTheory.OriginFrame.valF_spMap_fn f r

theorem sF_scal {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (s t : H0 D.P.L 1) (r : R) (hs : ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * t.f j)
    (y : TF (R := R) F ⟶ D.P.A) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) :
    GlobalTheory.Ex.sF s y.left J = algebraMap (FractionRing R) F (algebraMap R _ r) * GlobalTheory.Ex.sF t y.left J := by
  unfold GlobalTheory.Ex.sF
  have hs' := hs (fun k => J (y.left ≫ (fun _ : Fin 1 => 𝟙 D.P.A.left) k))
  erw [hs']
  by_cases h : ⊤ ≤ y.left ⁻¹ᵁ LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun k => J (y.left ≫ (fun _ : Fin 1 => 𝟙 D.P.A.left) k))
  · erw [GlobalTheory.MatchCoord.valF_mul h]
    congr 1
    refine valF_resTop_scal D.P.A.hom ((algebraMap (FractionRing R) F).comp (algebraMap R _)) y.left ?_ _ h r
    rw [Over.w y, GlobalTheory.Ex.spMap_comp']
    rfl
  · simp only [valF, dif_neg h, mul_zero]

end GlobalTheory.Mum.Rescale

noncomputable section
namespace GlobalTheory.Mum.Rescale

theorem txT_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F]
    [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D F N) (th : H0 D.P.L 1) (r : R),
    (∀ j, ν.th.f j = resTop _ (scal D.P.A.hom r) * th.f j) →
    (∀ s : H0 D.P.L 1, ∃ r' : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r') * th.f j) →
    ∃ (N' : GlobalTheory.Ex.NumD F) (ν' : GlobalTheory.Ex.NumOf D F N') (e : N'.X ≃+ N.X), ν'.th = th ∧
      ∀ (m : ℕ) (p : QkPt D F (m ^ 2)) (q : N.QT (m ^ 2)) (q' : N'.QT (m ^ 2)), ν.QPt p q → ν'.QPt p q' →
        ∀ χ, N.txT m q (e χ) = algebraMap (FractionRing R) F (algebraMap R _ r) * N'.txT m q' χ := by
  intro R _ _ D _ _ F _ _ N ν th r h1 h2
  have hrg := GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν
  have key : ∀ x, GlobalTheory.Ex.sF ν.th (ν.eA x).left ν.J =
      algebraMap (FractionRing R) F (algebraMap R _ r) * GlobalTheory.Ex.sF th (ν.eA x).left ν.J :=
    fun x => sF_scal D ν.th th r h1 (ν.eA x) ν.J
  let N' : GlobalTheory.Ex.NumD F := { N with th := fun x => GlobalTheory.Ex.sF th (ν.eA x).left ν.J / ν.rg }
  let ν' : GlobalTheory.Ex.NumOf D F N' :=
    { ν with th := th, th_gen := h2, th_eq := fun x => div_mul_cancel₀ _ hrg }
  have hth : ∀ x, N.th x = algebraMap (FractionRing R) F (algebraMap R _ r) * N'.th x := fun x => by
    show N.th x = _ * (GlobalTheory.Ex.sF th (ν.eA x).left ν.J / ν.rg)
    rw [mul_div_assoc', ← key, eq_div_iff hrg]
    exact ν.th_eq x
  refine ⟨N', ν', AddEquiv.refl _, rfl, ?_⟩
  intro m p q q' hq hq' χ
  let φ : N'.Gt →* N.Gt :=
    { toFun := fun g => ⟨g.b, g.s, g.mult⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hb : φ q'.1.2 = q.1.2 := ν.pt_unique (show ν.Pt p.g (φ q'.1.2) from hq'.2) hq.2
  have hb1 : q'.1.2.b = q.1.2.b := congrArg GlobalTheory.Ex.NumD.Gt.b hb
  have hs1 : q'.1.2.s = q.1.2.s := congrArg GlobalTheory.Ex.NumD.Gt.s hb
  have hpm : φ (q'.1.2 ^ m) = q.1.2 ^ m := (map_pow φ _ m).trans (congrArg (· ^ m) hb)
  have hpb : (q'.1.2 ^ m).b = (q.1.2 ^ m).b := congrArg GlobalTheory.Ex.NumD.Gt.b hpm
  have hps : (q'.1.2 ^ m).s = (q.1.2 ^ m).s := congrArg GlobalTheory.Ex.NumD.Gt.s hpm
  have hy : q'.1.1.toAdd = q.1.1.toAdd := ν.eX.injective (hq'.1.trans hq.1.symm)
  have lhs : N.txT m q (AddEquiv.refl N'.X χ) = ((N.wS (m ^ 2) q.1.2.b (N.ψ q.1.1.toAdd) (q.1.2.s q.1.1.toAdd) /
      GlobalTheory.Ex.mulq N.θ N.σ m q.1.2.b : Fˣ) : F) * (((N.ψ χ * (q.1.2 ^ m).s χ : Fˣ) : F) * N.th (N.c χ * (q.1.2 ^ m).b)) := rfl
  have rhs : N'.txT m q' χ = ((N.wS (m ^ 2) q'.1.2.b (N.ψ q'.1.1.toAdd) (q'.1.2.s q'.1.1.toAdd) /
      GlobalTheory.Ex.mulq N.θ N.σ m q'.1.2.b : Fˣ) : F) * (((N.ψ χ * (q'.1.2 ^ m).s χ : Fˣ) : F) * N'.th (N.c χ * (q'.1.2 ^ m).b)) := rfl
  rw [lhs, rhs, hy, hb1, hs1, hpb, hps, hth]
  ring

end GlobalTheory.Mum.Rescale
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesTermsRescaleByGeneratorMultipleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_terms_rescale_by_generator_multiple : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D F N) (th : H0 D.P.L 1) (r : R), (∀ j, ν.th.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D.P.L 1, ∃ r' : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r') * th.f j) → ∃ (N' : GlobalTheory.Ex.NumD F) (ν' : GlobalTheory.Ex.NumOf D F N') (e : N'.X ≃+ N.X), ν'.th = th ∧ ∀ (m : ℕ) (p : QkPt D F (m ^ 2)) (q : N.QT (m ^ 2)) (q' : N'.QT (m ^ 2)), ν.QPt p q → ν'.QPt p q' → ∀ χ, N.txT m q (e χ) = algebraMap (FractionRing R) F (algebraMap R _ r) * N'.txT m q' χ := by
  first | exact @GlobalTheory.Mum.Rescale.txT_rescale | exact GlobalTheory.Mum.Rescale.txT_rescale | (intros; apply GlobalTheory.Mum.Rescale.txT_rescale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumFieldOfCoeffTendstoZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumFieldOfCoeffTendstoZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem exists_adic_sum_of_finsets {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {Ix : Type} (c : Ix → R) (S : ℕ → Finset Ix) (hmono : Monotone S)
    (hS : ∀ n i, i ∉ S n → c i ∈ I ^ n) :
    ∃ a : R, ∀ n, ∀ T : Finset Ix, S n ⊆ T → a - ∑ i ∈ T, c i ∈ I ^ n := by
  classical
  have key : ∀ n, ∀ T : Finset Ix, S n ⊆ T → ∑ i ∈ T, c i - ∑ i ∈ S n, c i ∈ I ^ n := by
    intro n T hT
    rw [← Finset.sum_sdiff hT, add_sub_cancel_right]
    exact Ideal.sum_mem _ fun i hi => hS n i (Finset.mem_sdiff.mp hi).2
  have hsm : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    simp
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance
    (f := fun n => ∑ i ∈ S n, c i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_mem_iff, neg_sub]
      exact key m _ (hmono hmn))
  refine ⟨a, fun n T hT => ?_⟩
  have h1 := ha n
  rw [SModEq.sub_mem, hsm] at h1
  have h2 := key n T hT
  have h3 := Ideal.add_mem _ h1 h2
  rw [← neg_mem_iff]
  convert h3 using 1
  ring

theorem exists_sumI_of_coeff {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {E : Type} [AddCommGroup E] [Module R E] {Jx : Type} [Fintype Jx] (g : Jx → E)
    {Ix : Type} (c : Ix → Jx → R) (h : ∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ I ^ n}.Finite) :
    ∃ s : E, GlobalTheory.UT.SumI I (fun i => ∑ k, c i k • g k) s := by
  classical
  have hmono : Monotone (fun n => (h n).toFinset) := by
    intro m n hmn i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hk => hi fun k => Ideal.pow_le_pow_right hmn (hk k)
  have hS : ∀ k n i, i ∉ (h n).toFinset → c i k ∈ I ^ n := by
    intro k n i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    exact hi k
  choose a ha using fun k =>
    exists_adic_sum_of_finsets I (fun i => c i k) (fun n => (h n).toFinset) hmono (hS k)
  have hg : ∀ k, g k ∈ Submodule.span R (Set.range g) := fun k =>
    Submodule.subset_span ⟨k, rfl⟩
  refine ⟨∑ k, a k • g k, Submodule.span R (Set.range g),
    Submodule.fg_span (Set.finite_range g),
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun i => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k),
    fun n => ⟨(h n).toFinset, fun T hT => ?_⟩⟩
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← Finset.sum_smul, ← sub_smul]
  exact Submodule.smul_mem_smul (ha k n T hT) (hg k)

theorem exists_sumF_of_coeff : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Jx : Type) [Fintype Jx] (g : Jx → F) (Ix : Type) (c : Ix → Jx → R), (∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ maximalIdeal R ^ n}.Finite) → ∃ s : F, GlobalTheory.UT.SumF (maximalIdeal R) F (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k) s := by
  intro R _ _ _ _ hc F _ _ Jx _ g Ix c h
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨s, hs⟩ := exists_sumI_of_coeff (maximalIdeal R) g c h
  refine ⟨s, ?_⟩
  have e : (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k)
      = fun i => ∑ k, c i k • g k := by
    funext i
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.smul_def]
    rfl
  rw [e]
  exact hs

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumFieldOfCoeffTendstoZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adic_sum_field_of_coeff_tendsto_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Jx : Type) [Fintype Jx] (g : Jx → F) (Ix : Type) (c : Ix → Jx → R), (∀ n : ℕ, {i | ¬ ∀ k, c i k ∈ maximalIdeal R ^ n}.Finite) → ∃ s : F, GlobalTheory.UT.SumF (maximalIdeal R) F (fun i => ∑ k, algebraMap (FractionRing R) F (algebraMap R _ (c i k)) * g k) s := by
  first | exact @GlobalTheory.Mum.exists_sumF_of_coeff | exact GlobalTheory.Mum.exists_sumF_of_coeff | (intros; apply GlobalTheory.Mum.exists_sumF_of_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFiel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ThetaSer

theorem hasSum_map_of_sumF {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {I : Ideal R} {F C : Type} [Field F]
    [Algebra (FractionRing R) F] [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing R) C]
    (hC : GlobalTheory.Ex.CExt R I C) (em : F →ₐ[FractionRing R] C) {Ix : Type} {x : Ix → F} {s : F}
    (h : GlobalTheory.UT.SumF I F x s) : HasSum (fun i => em (x i)) (em s) := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  letI : Module R C := Module.compHom C (algebraMap R (FractionRing R))
  let f : F →ₗ[R] C :=
    { toFun := em
      map_add' := em.map_add
      map_smul' := fun r y => by
        change em ((algebraMap R (FractionRing R) r) • y) = (algebraMap R (FractionRing R) r) • em y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes] }
  refine GlobalTheory.Ex.AdicNormSum.main R I C hC Ix _ _ ?_
  obtain ⟨M, hfg, hs, hx, hn⟩ := h
  refine ⟨M.map f, hfg.map f, Submodule.mem_map_of_mem hs, fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hn n
  refine ⟨S, fun T hT => ?_⟩
  have := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at this
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [f, map_sub, map_sum] using this

theorem theta_series_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (Ix : Type) (p : Ix → QkPt D.toPre (Kb R) (m ^ 2)), ∃ v : Ix → Kb R, ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : Ix → QkPt D.toPre C (m ^ 2)) (q : Ix → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom (p i) (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i) := by
  intro R _ _ _ hB D m hm hu Ix p
  obtain ⟨⟨hN, -, -, hAC⟩, -⟩ := id hB
  haveI := hN
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  obtain ⟨N₀, ν₀, -⟩ := GlobalTheory.ValuesExist.exists_integral_values hL R D.toPre D.psi_even D.tau_bimult (Kb R) ⊤
    (fun _ => trivial)
  have hq₀ : ∀ i, ∃ q₀ : N₀.QT (m ^ 2), ν₀.QPt (p i) q₀ := fun i =>
    (((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult (Kb R) N₀ ν₀).2.2.2.2 (m ^ 2)).1 (p i)).exists
  choose q₀ hq₀ using hq₀
  have hv : ∀ i, ∃ v, GlobalTheory.UT.SumF (maximalIdeal R) (Kb R) (N₀.txT m (q₀ i)) v := fun i => by
    obtain ⟨Jx, _, g, c, hc, hfin⟩ := GlobalTheory.T.thetaSeriesTerms_torsionPoint_finite_adic_combination R hB D N₀ ν₀ m hm hu (p i) (q₀ i) (hq₀ i)
    obtain ⟨s, hs⟩ := GlobalTheory.T.exists_adic_sum_field_of_coeff_tendsto_zero R hAC (Kb R) Jx g N₀.X c hfin
    refine ⟨s, ?_⟩
    rwa [show N₀.txT m (q₀ i) = _ from funext hc]
  choose v hv using hv
  refine ⟨v, fun C _ _ _ _ _ hC em N nu p₁ q hp hq => ?_⟩
  obtain ⟨r, hr⟩ := ν₀.th_gen nu.th
  obtain ⟨N', ν', e, hth, htx⟩ := GlobalTheory.T.thetaSeries_terms_rescale_by_generator_multiple R D.toPre D.psi_even D.tau_bimult C N nu ν₀.th r hr ν₀.th_gen
  obtain ⟨I, hlam, -, hI⟩ := GlobalTheory.GaugeHom.exists_hom R D.toPre (Kb R) C em.toRingHom
    (RingHom.ext fun x => em.commutes x) N₀ N' ν₀ ν' hth
  have hq' : ∀ i, ∃ q' : N'.QT (m ^ 2), ν'.QPt (p₁ i) q' := fun i =>
    (((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult C N' ν').2.2.2.2 (m ^ 2)).1 (p₁ i)).exists
  choose q' hq' using hq'
  let a : C := algebraMap (FractionRing R) C (algebraMap R _ r)
  have hterm : ∀ i χ, N.txT m (q i) (e (I.e χ)) = a * em (N₀.txT m (q₀ i) χ) := fun i χ => by
    obtain ⟨h1, h2⟩ := hI (m ^ 2) (p i) (p₁ i) (q₀ i) (q' i) (hp i) (hq₀ i) (hq' i)
    rw [htx m (p₁ i) (q i) (q' i) (hq i) (hq' i), I.txT_eq hm (q₀ i) (q' i) h1 h2 χ, hlam, Units.val_one, _root_.one_mul]
    rfl
  have htx' : ∀ i, N.tx m (q i) = a * em (v i) := fun i => by
    have hs := (hasSum_map_of_sumF hC em (hv i)).mul_left a
    simp only [← hterm] at hs
    unfold GlobalTheory.Ex.NumD.tx
    rw [← (I.e.trans e).toEquiv.tsum_eq]
    exact hs.tsum_eq
  by_cases hr0 : r = 0
  · subst hr0
    have hz : ∀ j, nu.th.f j = 0 := fun j => by rw [hr j]; simp [scal]
    obtain ⟨r', hr'⟩ := nu.th_gen ν₀.th
    have hz₀ : ∀ j, ν₀.th.f j = 0 := fun j => by rw [hr' j, hz j, mul_zero]
    obtain ⟨N'', ν'', e'', -, htx''⟩ := GlobalTheory.T.thetaSeries_terms_rescale_by_generator_multiple R D.toPre D.psi_even D.tau_bimult (Kb R) N₀ ν₀ ν₀.th 0
      (fun j => by rw [hz₀ j, mul_zero]) ν₀.th_gen
    have h0 : ∀ i, em (v i) = 0 := fun i => by
      obtain ⟨q'', hq''⟩ := (((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult (Kb R) N'' ν'').2.2.2.2
        (m ^ 2)).1 (p i)).exists
      have hs := hasSum_map_of_sumF hC em (hv i)
      have e0 : (fun χ => em (N₀.txT m (q₀ i) χ)) = fun _ => 0 := funext fun χ => by
        rw [← e''.apply_symm_apply χ, htx'' m (p i) (q₀ i) q'' (hq₀ i) hq''] ; simp
      rw [e0] at hs
      exact hs.unique hasSum_zero
    refine ⟨1, fun i => ?_⟩
    rw [h0 i, htx' i, h0 i, mul_zero, mul_zero]
  · have ha : a ≠ 0 := by
      intro h
      apply hr0
      have h' : algebraMap R (FractionRing R) r = 0 := (algebraMap (FractionRing R) C).injective (by rw [map_zero]; exact h)
      exact (IsFractionRing.injective R (FractionRing R)) (by rw [h', map_zero])
    refine ⟨(Units.mk0 a ha)⁻¹, fun i => ?_⟩
    rw [htx' i, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel_left₀ ha]

end GlobalTheory.Mum.ThetaSer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFielStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (Ix : Type) (p : Ix → QkPt D.toPre (Kb R) (m ^ 2)), ∃ v : Ix → Kb R, ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : Ix → QkPt D.toPre C (m ^ 2)) (q : Ix → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom (p i) (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i) := by
  first | exact @GlobalTheory.Mum.ThetaSer.theta_series_algebraic | exact GlobalTheory.Mum.ThetaSer.theta_series_algebraic | (intros; apply GlobalTheory.Mum.ThetaSer.theta_series_algebraic <;> assumption)
end
