module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubstSame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
noncomputable section

namespace GlobalTheory.PlaceMono

section SlopeTestRemainingChoices

open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

private theorem isDomain_of_span {A : Type} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {π : A} (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (hreg : π ∈ nonZeroDivisors A) :
    IsDomain A := by
  classical
  have hkrull : ⨅ i : ℕ, (IsLocalRing.maximalIdeal A) ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top

  have hfac : ∀ a : A, a ≠ 0 → ∃ (k : ℕ) (u : A), IsUnit u ∧ a = π ^ k * u := by
    intro a ha
    have hex : ∃ n : ℕ, a ∉ (IsLocalRing.maximalIdeal A) ^ n := by
      by_contra h
      push_neg at h
      apply ha
      have hmem : a ∈ ⨅ i : ℕ, (IsLocalRing.maximalIdeal A) ^ i := Submodule.mem_iInf _ |>.2 h
      rwa [hkrull, Ideal.mem_bot] at hmem
    have hn : a ∉ (IsLocalRing.maximalIdeal A) ^ Nat.find hex := Nat.find_spec hex
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero fun h0 => hn ?_
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    have hak : a ∈ (IsLocalRing.maximalIdeal A) ^ k := by
      by_contra h
      exact Nat.find_min hex (by omega) h
    rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hak
    obtain ⟨u, hu⟩ := hak
    refine ⟨k, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    apply hn
    have hum : u ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal u).2 hu'
    rw [hπ, Ideal.mem_span_singleton'] at hum
    obtain ⟨c, hc⟩ := hum
    rw [hk, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨c, by rw [← hu, ← hc, pow_succ]; ring⟩
  have hnzd : NoZeroDivisors A := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨k, u, hu, rfl⟩ := hfac a h.1
    obtain ⟨l, v, hv, rfl⟩ := hfac b h.2
    have h1 : (u * v) * π ^ (k + l) = 0 := by rw [← hab]; ring
    have h2 : u * v = 0 :=
      (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hreg (k + l))).1 h1
    exact (hu.mul hv).ne_zero h2
  exact NoZeroDivisors.to_isDomain A

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

private theorem exists_dvr [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
    (w : Place p R) : ∃ _ : IsDomain w.Ow, IsDiscreteValuationRing w.Ow := by
  classical
  have := GlobalTheory.OnePrime.nontrivial_Ow w
  obtain ⟨P, hP, hpP, hm, hQ⟩ := GlobalTheory.OnePrime.exists_prime_under p R w
  have : IsLocalRing w.Ow :=
    IsLocalRing.of_unique_max_ideal ⟨_, hm, fun N hN => GlobalTheory.OnePrime.maximal_unique w _ N hm hN⟩
  have : IsNoetherianRing w.Ow := IsNoetherianRing.of_finite ℤ_[p] w.Ow
  have hM : IsLocalRing.maximalIdeal w.Ow = P.map w.toOw := (IsLocalRing.eq_maximalIdeal hm).symm
  have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hP0 : P ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hpP)
  have hpow : ∀ a : R, a ≠ 0 → ∃ (k : ℕ) (Q : Ideal R), Ideal.span {a} = P ^ k * Q ∧ P ⊔ Q = ⊤ ∧
      Ideal.span {w.toOw a} = P.map w.toOw ^ k := by
    intro a ha
    have ha0 : Ideal.span {a} ≠ ⊥ := by simpa using ha
    obtain ⟨Q, hPQ, hQe⟩ := Ideal.eq_prime_pow_mul_coprime ha0 P
    generalize Multiset.count P _ = e at hQe
    have hQ0 : Q ≠ ⊥ := by rintro rfl; exact ha0 (by simpa using hQe)
    refine ⟨e, Q, hQe, hPQ, ?_⟩
    have := congrArg (Ideal.map w.toOw) hQe
    rwa [Ideal.map_span, Set.image_singleton, Ideal.map_mul, Ideal.map_pow,
      GlobalTheory.Proof.different_power_unramified_iff.map_eq_top_of_coprime _ P hP hQ Q hQ0 hPQ, Ideal.mul_top] at this
  obtain ⟨a, ha1, ha2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP0 hP.ne_top 1
  have ha0 : a ≠ 0 := by rintro rfl; exact ha2 (zero_mem _)
  have hπ : IsLocalRing.maximalIdeal w.Ow = Ideal.span {w.toOw a} := by
    obtain ⟨k, Q, h1, h2, h3⟩ := hpow a ha0
    rw [pow_one] at ha1
    have hk : k ≤ 1 := by
      by_contra hk
      apply ha2
      refine (Ideal.span_singleton_le_iff_mem _).1 ?_
      rw [h1]
      exact Ideal.mul_le_left.trans (Ideal.pow_le_pow_right (Nat.succ_le_of_lt (not_le.1 hk)))
    rw [hM]
    apply le_antisymm
    · rw [h3]
      conv_lhs => rw [← pow_one (P.map w.toOw)]
      exact Ideal.pow_le_pow_right hk
    · exact (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ ha1)
  have hpM : (p : w.Ow) ∈ IsLocalRing.maximalIdeal w.Ow := by
    rw [hM, ← map_natCast w.toOw]; exact Ideal.mem_map_of_mem _ hpP
  have hpreg : (p : w.Ow) ∈ nonZeroDivisors w.Ow :=
    mem_nonZeroDivisors_iff_left.2 (GlobalTheory.Proof.different_power_unramified_iff.ow_p_torsionFree p R w)
  have hreg : w.toOw a ∈ nonZeroDivisors w.Ow := by
    have h := hpM
    rw [hπ, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    rw [hc] at hpreg
    exact (mul_mem_nonZeroDivisors.1 hpreg).1
  have hd := isDomain_of_span hπ hreg
  refine ⟨hd, ?_⟩
  have hnf : ¬ IsField w.Ow := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    intro h
    rw [h, Ideal.mem_bot] at hpM
    exact nonZeroDivisors.ne_zero hpreg hpM
  have hpr : (IsLocalRing.maximalIdeal w.Ow).IsPrincipal := ⟨_, hπ⟩
  exact ((IsDiscreteValuationRing.TFAE w.Ow hnf).out 1 5).2 hpr

private def cutEquiv (w : Place p R) :
    LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e) ≃ₗ[ℤ_[p]] w.Ow :=
  LinearEquiv.ofBijective
    ((Ideal.Quotient.mkₐ ℤ_[p] (Ideal.span {1 - w.e})).toLinearMap ∘ₗ
      (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)).subtype) (by
      constructor
      · rw [injective_iff_map_eq_zero]
        rintro ⟨_, a, rfl⟩ ha
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 ha)
        have hc' : c * (1 - w.e) = w.e * a := hc
        apply Subtype.ext
        show w.e * a = 0
        linear_combination (-w.e) * hc' - (a + c) * w.idem.eq
      · intro s
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
        refine ⟨⟨w.e * a, a, rfl⟩, Ideal.Quotient.eq.2 ?_⟩
        exact Ideal.mem_span_singleton'.2 ⟨-a, by
          show -a * (1 - w.e) = w.e * a - a
          ring⟩)

private theorem cutEquiv_symm (w : Place p R) (a : Op p R) :
    ((cutEquiv w).symm (Ideal.Quotient.mk _ a) : Op p R) = w.e * a := by
  have : (cutEquiv w).symm (Ideal.Quotient.mk _ a) = ⟨w.e * a, a, rfl⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨a, ?_⟩)
    show a * (1 - w.e) = a - w.e * a
    ring
  rw [this]

private theorem exists_basis [IsDedekindDomain R] [CharZero R] [Module.Free ℤ R]
    [Module.Finite ℤ R] (w : Place p R) :
    ∃ (α : Op p R) (b : Module.Basis
      (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)))) ℤ_[p]
      (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))), ∀ k, (b k : Op p R) = w.e * α ^ (k : ℕ) := by
  obtain ⟨_, _⟩ := exists_dvr w
  have : Module.Free ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) := inferInstance
  have : Module.Free ℤ_[p] w.Ow := Module.Free.of_equiv (cutEquiv w)
  have : IsLocalHom (algebraMap ℤ_[p] w.Ow) := Algebra.IsIntegral.isLocalHom _ _
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField (p := p)).toEquiv.symm
  obtain ⟨θ, hθ⟩ : ∃ θ : w.Ow, Algebra.adjoin ℤ_[p] {θ} = ⊤ :=
    Formalism.L2.Pj.AvAlg.exists_adjoin_eq_top (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective θ
  let pb := PowerBasis.ofAdjoinEqTop' (Algebra.IsIntegral.isIntegral _) hθ
  have hg : pb.gen = Ideal.Quotient.mk _ α := by simp [pb]
  have hn : pb.dim = Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) := by
    rw [(cutEquiv w).finrank_eq, pb.finrank]
  refine ⟨α, (pb.basis.map (cutEquiv w).symm).reindex (finCongr hn), fun k => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, pb.basis_eq_pow, hg, ← map_pow,
    cutEquiv_symm]
  rfl

end SlopeTestRemainingChoices

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

theorem place_monogenic : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE), IsDomain ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ IsPrincipalIdealRing ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ ∃ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))), ∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ) := by
  intro p _ OE _ _ _ _ _ w
  let w' : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p OE := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  obtain ⟨h1, h2⟩ := exists_dvr w'
  exact ⟨h1, h2.toIsPrincipalIdealRing, exists_basis w'⟩

end GlobalTheory.PlaceMono
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasisStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_unit_quotient_principal_basis : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE), IsDomain ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ IsPrincipalIdealRing ((ℤ_[p] ⊗[ℤ] OE) ⧸ Ideal.span {1 - w.e}) ∧ ∃ (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))), ∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ) := by
  first | exact @GlobalTheory.PlaceMono.place_monogenic | exact GlobalTheory.PlaceMono.place_monogenic | (intros; apply GlobalTheory.PlaceMono.place_monogenic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimit
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ActionLimit

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)
variable {d : ℕ} {I : Fin 2 → Type} (X : RawChart C d I (Fin dd))
  (hlg : X.lg = fun i => un1 (Y.lg i)) (hex : X.ex = fun i => un1 (Y.ex i)) (hh : X.h = Y.h)

include hlg hex in
theorem matrixEnd_linearMap' (M : Matrix (Fin dd) (Fin dd) C)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP X M a i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) i) := by
  have h0 := gp_lg Y
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  have hL : GP (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) := gp_comp1 _ _ (gp_linMap _) h0
  have e0 : endP X M a i =
    MvPowerSeries.subst (fun x => ∑ y, M x y • MvPowerSeries.subst a (un1 (Y.lg y))) (un1 (Y.ex i)) := by
    unfold endP
    rw [hlg, hex]
  rw [e0, funext (subst_linMap M Y.lg h0 a ha)]
  generalize comp1 (LogExpAdaptedGauge.linMap M) Y.lg = L at hL ⊢
  have hz : ∀ x, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (L x)) = 0 :=
    fun x => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (fun q : Fin 1 × Fin dd => ha q.2) (hL x)
  rw [subst_singlePointUncurry _ hz, germComp1_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => hL q.2) hs]

include hlg hex in
theorem matrixEnd_eq_subst' (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP X (dLin e) a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  rw [matrixEnd_linearMap' Y X hlg hex _ a ha, ← eq_exp_lin_log Y e he hhom]

include hlg hex in
theorem matrixEnd_eq_comp' (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {n : ℕ} (a : Pt C n dd) (ha : GP a) : endP X (dLin e) a = comp1 e a := by
  funext i
  rw [matrixEnd_eq_subst' Y X hlg hex e he hhom a ha, germComp1_eq_subst]

include hh in
theorem hAt_eq_ev_raw {n : ℕ} (a b : Pt C n dd) : hAt X a b = ev ![a, b] Y.h := by
  unfold hAt
  rw [hh]
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

include hlg hex hh in
theorem isEnd_of_hom_raw (e e' : Pt C 1 dd) (he : GP e) (he' : GP e')
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    (hhom' : comp1 e' (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e' (pt C (n := 2) dd 0)) (comp1 e' (pt C (n := 2) dd 1)))
    (hi : ∀ i, IntS V (e i)) (hi' : ∀ i, IntS V (e' i))
    (hx : IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 e' (pt C dd 1)] Y.h))) :
    IsEnd X V (dLin e) (dLin e') := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have hc : MvPowerSeries.constantCoeff Y.h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt (0 : Fin 1))) Y.h, Y.gauge.ax0, map_zero]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_eq_subst' Y X hlg hex e he hhom _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi i _
  · rw [matrixEnd_eq_subst' Y X hlg hex e' he' hhom' _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi' i _
  · have g0 : gp C (Fin dd) (0 : Fin 2) = pt C dd 0 := rfl
    have g1 : gp C (Fin dd) (1 : Fin 2) = pt C dd 1 := rfl
    rw [g0, g1, matrixEnd_eq_comp' Y X hlg hex e he hhom _ (gp_pt 0), matrixEnd_eq_comp' Y X hlg hex e' he' hhom' _ (gp_pt 1),
      hAt_eq_ev_raw Y X hh, hAt_eq_ev_raw Y X hh, ← subst_exp_eq_mvExp]
    · exact hx
    · rw [map_sub, gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ he (gp_pt 0)) (gp_pt 1)) _ hc,
        gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ he' (gp_pt 1))) _ hc, sub_zero]

end Chart

theorem exists_isEnd_of_limit_raw : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) (I : Fin 2 → Type) (X : RawChart C d I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h → ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd X V M M' ∧ IsEnd X V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  intro C _ _ V O _ _ dd Y d I X hlg hex hh a ha
  obtain ⟨c1, c2⟩ := GlobalTheory.T.actionConverges_ladic_cauchy_and_star C V O dd Y a ha
  obtain ⟨e, eb, i1, i2, l1, l2, h1, x1⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y a c1 c2
  obtain ⟨f, fb, -, -, l3, l4, h2, x2⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y (fun n => star (a n)) c2
    (by simpa only [star_star] using c1)
  simp only [star_star] at l4
  obtain rfl : f = eb := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l3 N i μ) (fun N => l2 N i μ)
  obtain rfl : fb = e := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l4 N i μ) (fun N => l1 N i μ)
  have hz : ∀ (g : Pt C 1 dd) (s : ℕ → O), (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (g i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) → GP g := by
    intro g s hg i
    refine limit_unique V (fun n => MvPowerSeries.coeff 0 (Y.B.A.act (s n) i)) _ _ (fun N => hg N i 0)
      fun N => ⟨0, fun n _ => ?_⟩
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.B.A.const, sub_zero]
    exact VF.Ge.zero _
  have g1 := hz fb a l1
  have g2 := hz f (fun n => star (a n)) l2
  exact ⟨dLin fb, dLin f, isEnd_of_hom_raw Y X hlg hex hh fb f g1 g2 h1 h2 i1 i2 x1, isEnd_of_hom_raw Y X hlg hex hh f fb g2 g1 h2 h1 i2 i1 x2,
    linear_limit V fb _ l1, linear_limit V f _ l2⟩

end GlobalTheory.ActionLimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfLadicActionLimitStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralEnd_of_ladic_action_limit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) (I : Fin 2 → Type) (X : RawChart C d I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h → ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd X V M M' ∧ IsEnd X V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  first | exact @GlobalTheory.ActionLimit.exists_isEnd_of_limit_raw | exact GlobalTheory.ActionLimit.exists_isEnd_of_limit_raw | (intros; apply GlobalTheory.ActionLimit.exists_isEnd_of_limit_raw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsLiftIntegersIdempotentsConjugation
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsLiftIntegersIdempotentsConjugation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem existsUnique_lift_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {OE : Type} [CommRing OE] [Module.Finite ℤ OE]
    (τ : OE →+* C) : ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ := by
  have h : ∀ x : OE, ∃ y : O, algebraMap O C y = τ x := fun x => by
    have h1 : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    have h2 : IsIntegral ℤ (τ x) := h1.map τ.toIntAlgHom
    have h3 : IsIntegral O (τ x) := h2.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h3)
  choose f hf using h
  refine ⟨{ toFun := f
            map_one' := hv.hom_inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hv.hom_inj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hv.hom_inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hv.hom_inj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }, ?_, ?_⟩
  · exact RingHom.ext hf
  · intro g hg
    refine RingHom.ext fun x => hv.hom_inj ?_
    change algebraMap O C (g x) = algebraMap O C (f x)
    rw [hf, ← hg]
    rfl

theorem embeddings_idempotents_conjugation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE], (∀ τ : OE →+* C, ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ) ∧ (∀ (e : ℤ_[p] ⊗[ℤ] OE) (τ : OE →+* O), e * e = e → tauExt τ e = 0 ∨ tauExt τ e = 1) ∧ ∀ [StarRing OE] (τ : OE →+* O) (x : ℤ_[p] ⊗[ℤ] OE), tauExt (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) x = tauExt τ (sigE p OE x) ∧ sig p OE x = sigE p OE x := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _
  have : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  refine ⟨existsUnique_lift_integers hv, fun e τ he => ?_, ?_⟩
  · have h : IsIdempotentElem (tauExt τ e) := by
      unfold IsIdempotentElem
      rw [← map_mul, he]
    exact IsIdempotentElem.iff_eq_zero_or_one.1 h
  · intro _ τ x
    have h2 : sig p OE x = sigE p OE x := rfl
    refine ⟨?_, h2⟩
    rw [← h2]
    clear h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [tauExt, sig]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsLiftIntegersIdempotentsConjugationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddings_lift_integers_idempotents_conjugation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [Module.Finite ℤ OE], (∀ τ : OE →+* C, ∃! τ' : OE →+* O, ((algebraMap O C).comp τ') = τ) ∧ (∀ (e : ℤ_[p] ⊗[ℤ] OE) (τ : OE →+* O), e * e = e → tauExt τ e = 0 ∨ tauExt τ e = 1) ∧ ∀ [StarRing OE] (τ : OE →+* O) (x : ℤ_[p] ⊗[ℤ] OE), tauExt (τ.comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) x = tauExt τ (sigE p OE x) ∧ sig p OE x = sigE p OE x := by
  first | exact @GlobalTheory.ChF.embeddings_idempotents_conjugation | exact GlobalTheory.ChF.embeddings_idempotents_conjugation | (intros; apply GlobalTheory.ChF.embeddings_idempotents_conjugation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SquarefreeMapMinpolyInt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem squarefree_map_minpoly_int (C : Type) [Field C] [CharZero C] (OE : Type)
    [CommRing OE] [IsDomain OE] [Module.Finite ℤ OE] (a : OE) :
    Squarefree ((minpoly ℤ a).map (Int.castRingHom C)) := by
  have hi : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
  have h1 : Irreducible (minpoly ℤ a) := minpoly.irreducible hi
  have h2 : Irreducible ((minpoly ℤ a).map (algebraMap ℤ ℚ)) :=
    ((minpoly.monic hi).irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp h1
  have h3 := (h2.separable.map (f := algebraMap ℚ C)).squarefree
  rw [Polynomial.map_map] at h3
  have h4 : (algebraMap ℚ C).comp (algebraMap ℤ ℚ) = Int.castRingHom C := RingHom.ext_int _ _
  rwa [h4] at h3

private theorem aeval_map_minpoly_int (C : Type) [Field C] (OE : Type)
    [CommRing OE] (A : Type) [Ring A] [Algebra C A] (ρ : OE →+* A) (a : OE) :
    Polynomial.aeval (ρ a) ((minpoly ℤ a).map (Int.castRingHom C)) = 0 := by
  have h4 : Int.castRingHom C = algebraMap ℤ C := RingHom.ext_int _ _
  rw [h4, Polynomial.aeval_map_algebraMap]
  have := Polynomial.aeval_algHom_apply ρ.toIntAlgHom a (minpoly ℤ a)
  rw [minpoly.aeval, map_zero] at this
  exact this

private theorem finite_ringHom_order (C : Type) [Field C] [CharZero C] (OE : Type)
    [CommRing OE] [IsDomain OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] :
    Finite (OE →+* C) := by
  classical
  let b := Module.Free.chooseBasis ℤ OE
  let p : OE → Polynomial C := fun a => (minpoly ℤ a).map (Int.castRingHom C)
  have hfin : ∀ a, Finite ((p a).rootSet C) := fun a => (Polynomial.rootSet_finite _ _).to_subtype
  let F : (OE →+* C) → ∀ i, (p (b i)).rootSet C := fun τ i =>
    ⟨τ (b i), Polynomial.mem_rootSet.mpr
      ⟨(squarefree_map_minpoly_int C OE (b i)).ne_zero, aeval_map_minpoly_int C OE C τ (b i)⟩⟩
  refine Finite.of_injective F fun τ σ h => ?_
  have : τ.toAddMonoidHom.toIntLinearMap = σ.toAddMonoidHom.toIntLinearMap :=
    b.ext fun i => congrArg Subtype.val (congrFun h i)
  exact RingHom.ext fun a => LinearMap.congr_fun this a

private theorem mem_iSup_of_eigenvector (C : Type) [Field C] (OE : Type) [CommRing OE]
    (V : Type) [AddCommGroup V] [Module C V] (ρ : OE →+* Module.End C V) (χ : OE → C) (x : V)
    (hx : ∀ a, ρ a x = χ a • x) :
    x ∈ ⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a) := by
  by_cases h0 : x = 0
  · rw [h0]; exact Submodule.zero_mem _
  have hinj : Function.Injective fun c : C => c • x := smul_left_injective C h0
  let τ : OE →+* C :=
    { toFun := χ
      map_one' := hinj (by simp only [← hx, map_one, one_smul, Module.End.one_apply])
      map_mul' := fun a b => hinj (by
        simp only
        rw [← hx, map_mul, Module.End.mul_apply, hx b, map_smul, hx a, smul_smul, mul_comm])
      map_zero' := hinj (by simp only [← hx, map_zero, zero_smul, LinearMap.zero_apply])
      map_add' := fun a b => hinj (by
        simp only
        rw [← hx, map_add (f := _), LinearMap.add_apply, hx a, hx b, add_smul]) }
  refine Submodule.mem_iSup_of_mem τ ((Submodule.mem_iInf _).mpr fun a => ?_)
  exact Module.End.mem_eigenspace_iff.mpr (hx a)

theorem order_rep_diagonalisable : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE], Finite (OE →+* C) ∧ ∀ (V : Type) [AddCommGroup V] [Module C V] (ρ : OE →+* Module.End C V), iSupIndep (fun τ : OE →+* C => ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) ∧ (⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) = ⊤ := by
  intro C _ _ _ OE _ _ _ _ _
  refine ⟨finite_ringHom_order C OE, fun V _ _ ρ => ⟨?_, ?_⟩⟩
  · have hcomm : ∀ a b : OE, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : OE => ρ a)
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
    have h2 := h.comp (f := fun τ : OE →+* C => (τ : OE → C)) DFunLike.coe_injective
    refine h2.mono fun τ => ?_
    exact iInf_mono fun a => (Module.End.genEigenspace (ρ a) (τ a)).mono le_top
  · have hcomm : ∀ a b : OE, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    have hss : ∀ a, (ρ a).IsSemisimple := fun a =>
      Module.End.isSemisimple_of_squarefree_aeval_eq_zero (squarefree_map_minpoly_int C OE a)
        (aeval_map_minpoly_int C OE _ ρ a)
    rw [eq_top_iff]
    rintro v -
    let W : Submodule C V := Submodule.span C (Set.range fun a : OE => ρ a v)
    have hW : ∀ a, W ∈ (ρ a).invtSubmodule := by
      intro a
      rw [Module.End.mem_invtSubmodule, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      refine Submodule.subset_span ⟨a * b, ?_⟩
      simp only [map_mul, Module.End.mul_apply]
    have hfin : FiniteDimensional C W := by
      let b := Module.Free.chooseBasis ℤ OE
      have hle : W ≤ Submodule.span C (Set.range fun i => ρ (b i) v) := by
        rw [Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        have ha : a ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
        simp only [SetLike.mem_coe]
        induction ha using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add x y _ _ hx hy =>
          rw [map_add (f := _), LinearMap.add_apply]
          exact Submodule.add_mem _ hx hy
        | smul n x _ hx =>
          rw [map_zsmul, LinearMap.smul_apply]
          exact zsmul_mem hx n
      have : FiniteDimensional C (Submodule.span C (Set.range fun i => ρ (b i) v)) :=
        FiniteDimensional.span_of_finite C (Set.finite_range _)
      exact Submodule.finiteDimensional_of_le hle
    let f : OE → Module.End C W := fun a => (ρ a).restrict (hW a)
    have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f (fun a b _ => LinearMap.restrict_commute (hcomm a b) (hW a) (hW b))
      (fun a => Module.End.iSup_maxGenEigenspace_eq_top (f a))
    have hv : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
    have hle : (⊤ : Submodule C W) ≤ Submodule.comap W.subtype
        (⨆ τ : OE →+* C, ⨅ a : OE, Module.End.eigenspace (ρ a) (τ a)) := by
      rw [← htop]
      refine iSup_le fun χ x hx => ?_
      refine mem_iSup_of_eigenvector C OE V ρ χ x fun a => ?_
      have h1 := (Submodule.mem_iInf _).mp hx a
      have h2 : (f a).IsSemisimple := (hss a).restrict (hW a)
      rw [h2.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
        Module.End.mem_eigenspace_iff] at h1
      exact congrArg Subtype.val h1
    exact hle (Submodule.mem_top (x := (⟨v, hv⟩ : W)))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenbasisRestrictionSurjectiveEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenbasisRestrictionSurjectiveEquivariant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ChF

private theorem exists_leftInv {O OE : Type} [CommRing O] [IsDomain O] [ValuationRing O] [CommRing OE] {d n : ℕ}
    (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O) (h : EigB ρ τ W) :
    ∃ G : Matrix (Fin n) (Fin d) O, ∀ i, G *ᵥ W i = Pi.single i 1 := by
  classical
  let φ : (Fin n → O) →ₗ[O] (Fin d → O) := Fintype.linearCombination O W
  have hφ : ∀ c, φ c = ∑ i, c i • W i := fun c => Fintype.linearCombination_apply O W c
  have heig : ∀ c a, (ρ a) *ᵥ φ c = τ a • φ c := by
    intro c a
    rw [hφ, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, h.1, smul_comm]
  have hinj : Function.Injective φ := by
    intro c c' hc
    obtain ⟨c₀, -, hu⟩ := h.2 (φ c) (heig c)
    rw [hu c (hφ c).symm, hu c' (by rw [hc]; exact (hφ c').symm)]
  have htf : Submodule.torsion O ((Fin d → O) ⧸ LinearMap.range φ) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨t, ht⟩, hx⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have ht0 : t ≠ 0 := nonZeroDivisors.ne_zero ht
    have hx' : (Submodule.Quotient.mk (t • y) : (Fin d → O) ⧸ LinearMap.range φ) = 0 := by
      rw [Submodule.Quotient.mk_smul]; exact hx
    rw [Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨c, hc⟩ := hx'
    have hy : ∀ a, (ρ a) *ᵥ y = τ a • y := by
      intro a
      have := heig c a
      rw [hc, Matrix.mulVec_smul, smul_comm] at this
      exact smul_right_injective _ ht0 this
    obtain ⟨c₀, hc₀, -⟩ := h.2 y hy
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨c₀, (hφ c₀).trans hc₀⟩
  haveI : Module.Flat O ((Fin d → O) ⧸ LinearMap.range φ) :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr htf
  haveI : Module.Free O ((Fin d → O) ⧸ LinearMap.range φ) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range φ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ y, (LinearMap.id - s ∘ₗ (LinearMap.range φ).mkQ : (Fin d → O) →ₗ[O] (Fin d → O)) y ∈ LinearMap.range φ := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs ((LinearMap.range φ).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this, sub_self]
  let g : (Fin d → O) →ₗ[O] (Fin n → O) :=
    (LinearEquiv.ofInjective φ hinj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ _ hmem
  have hg : ∀ c, g (φ c) = c := by
    intro c
    have h0 : (LinearMap.range φ).mkQ (φ c) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨c, rfl⟩
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearEquiv.symm_apply_eq]
    ext1
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, h0,
      map_zero, sub_zero, LinearEquiv.ofInjective_apply]
  refine ⟨LinearMap.toMatrix' g, fun i => ?_⟩
  rw [LinearMap.toMatrix'_mulVec, ← hg (Pi.single i 1), hφ]
  congr 1
  simp [Pi.single_apply]

theorem eigB_res_surjective : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (OE : Type) [CommRing OE] (d n : ℕ) (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O), EigB ρ τ W → Function.Surjective (Pdiv.ChartF.res W) ∧ (∀ a f, Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) = τ a • Pdiv.ChartF.res W f) ∧ eigDim C ρ ((algebraMap O C).comp τ) = n := by
  classical
  intro C _ v O _ _ hv OE _ d n ρ τ W h
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsFractionRing O C := hv.isFractionRing
  obtain ⟨G, hG⟩ := exists_leftInv ρ τ W h
  refine ⟨fun c => ⟨Gᵀ *ᵥ c, ?_⟩, fun a f => ?_, ?_⟩
  · have h1 : Matrix.of W * Gᵀ = 1 := by
      ext i k
      have := congrFun (hG i) k
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm (a := i), ← this, mul_comm]
    simp only [Pdiv.ChartF.res, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · ext i
    have : Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) i = W i ⬝ᵥ ((ρ a)ᵀ *ᵥ f) := rfl
    rw [this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h.1, smul_dotProduct]
    rfl
  · let W' : Fin n → Fin d → C := fun i => algebraMap O C ∘ W i
    have hmap : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin d) O) (y : Fin d → O),
        M.map (algebraMap O C) *ᵥ (algebraMap O C ∘ y) = algebraMap O C ∘ (M *ᵥ y) := by
      intro m M y
      ext k
      exact (RingHom.map_mulVec (algebraMap O C) M y k).symm
    have hli : LinearIndependent C W' := by
      refine LinearIndependent.of_comp (Matrix.mulVecLin (G.map (algebraMap O C))) ?_
      have : (Matrix.mulVecLin (G.map (algebraMap O C))) ∘ W' = Pi.basisFun C (Fin n) := by
        funext i
        simp only [Function.comp_apply, Matrix.mulVecLin_apply, W', hmap, hG]
        ext k
        simp [Pi.single_apply, apply_ite]
      rw [this]
      exact (Pi.basisFun C (Fin n)).linearIndependent
    have hsp : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
        (((algebraMap O C).comp τ) a)) = Submodule.span C (Set.range W') := by
      apply le_antisymm
      · intro x hx
        simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx
        obtain ⟨⟨b, hb⟩, hbx⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
        choose y hy using hbx
        have hb0 : algebraMap O C b ≠ 0 := by
          rw [map_ne_zero_iff _ hv.hom_inj]; exact nonZeroDivisors.ne_zero hb
        have hyx : algebraMap O C ∘ y = algebraMap O C b • x := by
          ext k
          simp only [Function.comp_apply, hy k, Pi.smul_apply, Algebra.smul_def]
          rfl
        have hye : ∀ a, (ρ a) *ᵥ y = τ a • y := by
          intro a
          ext k
          apply hv.hom_inj
          have := congrFun (hmap (ρ a) y) k
          rw [hyx, Matrix.mulVec_smul, hx a, smul_comm, ← hyx] at this
          simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, RingHom.comp_apply] at this
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← this]
        obtain ⟨c, hc, -⟩ := h.2 y hye
        rw [← Submodule.smul_mem_iff _ hb0, ← hyx, ← hc]
        have : algebraMap O C ∘ (∑ i, c i • W i) = ∑ i, algebraMap O C (c i) • W' i := by
          ext k
          simp [W', Finset.sum_apply, Algebra.smul_def]
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
        intro a
        simp only [W', hmap, h.1]
        ext k
        simp
    unfold eigDim
    rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenbasisRestrictionSurjectiveEquivariantStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenbasis_restriction_surjective_equivariant : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (OE : Type) [CommRing OE] (d n : ℕ) (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O) (W : Fin n → Fin d → O), EigB ρ τ W → Function.Surjective (Pdiv.ChartF.res W) ∧ (∀ a f, Pdiv.ChartF.res W ((ρ a)ᵀ *ᵥ f) = τ a • Pdiv.ChartF.res W f) ∧ eigDim C ρ ((algebraMap O C).comp τ) = n := by
  first | exact @GlobalTheory.ChF.eigB_res_surjective | exact GlobalTheory.ChF.eigB_res_surjective | (intros; apply GlobalTheory.ChF.eigB_res_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateDatumHypothesesPeriodTower
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateDatumHypothesesPeriodTower
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem hodgeTateSetting_ainfTower_of_isPrimitiveRoot : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE], HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) (show O from (Ainf.ainfTowerL p O hv ε hε).c) := by
  intro p hp C _ _ _ v O _ _ hu _ hv ε hε _ OE _ _
  refine ⟨hv, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne (hv.map_le_one _) (fun e => hu.out (hv.isUnit_of_one' e))
  · rw [map_natCast]
    exact fun h => Nat.cast_ne_zero.2 hp.out.ne_zero ((Valuation.zero_iff v).1 h)
  · rw [map_natCast]
    exact Ainf.c_val p O hv ε hε
  · intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have h : ∀ (x : ℤ_[p]) (y : OE), sigE p OE (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℤ] star y := fun _ _ => rfl
      rw [h, h, star_star]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateDatumHypothesesPeriodTowerStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_datum_hypotheses_period_tower : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE], HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) (show O from (Ainf.ainfTowerL p O hv ε hε).c) := by
  first | exact @GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot | exact GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot | (intros; apply GlobalTheory.ChF.hodgeTateSetting_ainfTower_of_isPrimitiveRoot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearPartPairingSeriesEqHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearPartPairingSeriesEqHeight
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem dl_pairSer_eq_height : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (p : ℕ) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) (g : ℕ) (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)), TanMat B Tw.O Y gb S → ∀ (τ : ℕ → B.G Tw.O) (u : PS (Tw.O : Type) 1 g), MvPowerSeries.constantCoeff u = 1 → PairSer B Tw.O Y p τ u → ∀ ht : B.gg →ₗ[R₀] (Tw.O : Type), (∀ n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ n)) ((Tw.q n).1.toLinearMap ∘ₗ ht)) → Sᵀ *ᵥ dl u = fun l => ht (gb l) := by
  intro R₀ _ B p Tw Dt g Y gb S hS τ u hu hP ht hH
  funext l
  rw [← sub_eq_zero]
  refine Tw.sep _ fun n => (Dt.Dp n).free _ ?_
  set Dp := Dt.Dp n
  obtain ⟨z, hz, hz'⟩ := hH n (gb l)
  let s : LHom Tw.O Dp.D := Dp.σ.comp (Tw.q n)
  have hs : ∀ x, s.1 x = Dp.σ.1 ((Tw.q n).1 x) := fun _ => rfl
  have hc : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type)) = 0 := by
    rw [← map_natCast (Tw.π n).1, Tw.char n, map_zero]
  have hp : IsNilpotent (p : (Dp.D : Type)) :=
    ⟨n + 1, by rw [← Nat.cast_pow, ← map_natCast Dp.σ.1, hc, map_zero]⟩
  have hsq : ∀ x y : (Dp.D : Type), x * Dp.η * (y * Dp.η) = 0 := fun x y => by
    rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  have ha : ∀ k, IsNilpotent (s.1 (S k l) * Dp.η) := fun k => ⟨2, by rw [pow_two, hsq]⟩
  rw [hS Dp.D _ s Dp.π Dp.sqZero l Dp.ηk, ← B.map_comp] at hz
  have h1 := hP Dp.D s (fun k => s.1 (S k l) * Dp.η) n z hp ha hz
  have h2 := (nv_calculus _ _ s.1.toRingHom 1 g ![fun k => s.1 (S k l) * Dp.η]
    (fun i j => by simpa using ha j)).2.2.2.2.2 (fun i j i' j' => by simpa using hsq _ _) u
  rw [h2, hz', hu, map_one, add_right_inj, Fintype.sum_prod_type, Fin.sum_univ_one] at h1
  rw [← hs, map_sub, sub_mul, sub_eq_zero]
  refine Eq.trans ?_ h1.symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, transpose_apply, dl, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.cons_val_fin_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearPartPairingSeriesEqHeightStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_part_pairing_series_eq_height : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (p : ℕ) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) (g : ℕ) (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)), TanMat B Tw.O Y gb S → ∀ (τ : ℕ → B.G Tw.O) (u : PS (Tw.O : Type) 1 g), MvPowerSeries.constantCoeff u = 1 → PairSer B Tw.O Y p τ u → ∀ ht : B.gg →ₗ[R₀] (Tw.O : Type), (∀ n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ n)) ((Tw.q n).1.toLinearMap ∘ₗ ht)) → Sᵀ *ᵥ dl u = fun l => ht (gb l) := by
  first | exact @GlobalTheory.ChF.dl_pairSer_eq_height | exact GlobalTheory.ChF.dl_pairSer_eq_height | (intros; apply GlobalTheory.ChF.dl_pairSer_eq_height <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDerivationPolynomialEqJetAt0
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDerivationPolynomialEqJetAt0
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.DerivJet

variable {C : Type} [Field C] {W : Type} [Fintype W]

theorem jetAt0_mul_lin (c : W → C) (Q : MvPolynomial W C) (G : MvPowerSeries W C) :
    jetAt0 (Q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X w) G =
      jetAt0 Q (∑ w, c w • MvPowerSeries.pderiv (R := C) w G) := by
  rw [Finset.mul_sum, GlobalTheory.MinorShiftJet.jetAt0_sum_left, GlobalTheory.MinorShiftJet.jetAt0_sum_smul_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_left_comm, GlobalTheory.MinorShiftJet.jetAt0_C_mul, GlobalTheory.MinorShiftJet.jetAt0_mul_X]

theorem jetAt0_iterate {A : Type} (S : A → MvPowerSeries W C) (D : A → A) (c : W → C) (k : ℕ)
    (h : k ≠ 0 → ∀ G, S (D G) = ∑ w, c w • MvPowerSeries.pderiv (R := C) w (S G)) (Q : MvPolynomial W C) (G : A) :
    jetAt0 Q (S (D^[k] G)) = jetAt0 (Q * (∑ w, MvPolynomial.C (c w) * MvPolynomial.X w) ^ k) (S G) := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
    have h' := h (Nat.succ_ne_zero k)
    rw [Function.iterate_succ_apply, ih (fun _ => h'), h', ← jetAt0_mul_lin, pow_succ, mul_assoc]

theorem jetAt0_foldr {A ι : Type} (S : A → MvPowerSeries W C) (D : ι → A → A) (c : ι → W → C) (m : ι → ℕ)
    (h : ∀ l, m l ≠ 0 → ∀ G, S (D l G) = ∑ w, c l w • MvPowerSeries.pderiv (R := C) w (S G)) (L : List ι)
    (Q : MvPolynomial W C) (G : A) :
    jetAt0 Q (S (L.foldr (fun l g => (D l)^[m l] g) G)) =
      jetAt0 (Q * (L.map fun l => (∑ w, MvPolynomial.C (c l w) * MvPolynomial.X w) ^ m l).prod) (S G) := by
  induction L generalizing Q with
  | nil => simp
  | cons l L ih =>
    rw [List.foldr_cons, jetAt0_iterate S (D l) (c l) (m l) (h l), ih, List.map_cons, List.prod_cons, mul_assoc]

theorem jetAt0_one_left {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 1 G = MvPowerSeries.constantCoeff G := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', GlobalTheory.MinorShiftJet.jetAt0_monomial]
  simp [mfact]

theorem constantCoeff_DpolyN_eq_jetAt0 : ∀ (C : Type) [Field C] (dd n : ℕ) (F : Fin dd → PS C 2 dd) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (W : Type) [Fintype W] (E : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (E s) = 0) → ∀ (co : ι → W → C) (P : MvPolynomial ι C), (∀ ℓ ∈ P.vars, ∀ G : PS C n dd, MvPowerSeries.subst E (DofN F (cp ℓ) (uv ℓ) G) = ∑ w, co ℓ w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst E G)) → ∀ G : PS C n dd, MvPowerSeries.constantCoeff (DpolyN F cp uv P G) = jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ w, MvPolynomial.C (co ℓ w) * MvPolynomial.X w) P : MvPolynomial W C) (MvPowerSeries.subst E G) := by
  intro C _ dd n F ι _ cp uv W _ E hE co P h G
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', GlobalTheory.MinorShiftJet.jetAt0_sum_left, DpolyN, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_mul, MvPowerSeries.constantCoeff_C, MvPolynomial.algebraMap_eq, GlobalTheory.MinorShiftJet.jetAt0_C_mul]
  congr 1
  rw [← cc_subst hE, ← jetAt0_one_left, DmonN,
    jetAt0_foldr (fun g => MvPowerSeries.subst E g) (fun l => DofN F (cp l) (uv l)) co m
      (fun l hl => h l ((MvPolynomial.mem_vars_iff_mem_support l).2 ⟨m, hm, Finsupp.mem_support_iff.2 hl⟩)),
    one_mul, Finset.prod_map_toList]

end GlobalTheory.DerivJet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffDerivationPolynomialEqJetAt0Statement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_derivationPolynomial_eq_jetAt0 : ∀ (C : Type) [Field C] (dd n : ℕ) (F : Fin dd → PS C 2 dd) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (W : Type) [Fintype W] (E : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (E s) = 0) → ∀ (co : ι → W → C) (P : MvPolynomial ι C), (∀ ℓ ∈ P.vars, ∀ G : PS C n dd, MvPowerSeries.subst E (DofN F (cp ℓ) (uv ℓ) G) = ∑ w, co ℓ w • MvPowerSeries.pderiv (R := C) w (MvPowerSeries.subst E G)) → ∀ G : PS C n dd, MvPowerSeries.constantCoeff (DpolyN F cp uv P G) = jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ w, MvPolynomial.C (co ℓ w) * MvPolynomial.X w) P : MvPolynomial W C) (MvPowerSeries.subst E G) := by
  first | exact @GlobalTheory.DerivJet.constantCoeff_DpolyN_eq_jetAt0 | exact GlobalTheory.DerivJet.constantCoeff_DpolyN_eq_jetAt0 | (intros; apply GlobalTheory.DerivJet.constantCoeff_DpolyN_eq_jetAt0 <;> assumption)
end
end
