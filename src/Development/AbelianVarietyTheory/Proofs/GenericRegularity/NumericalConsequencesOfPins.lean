module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointVectorsIntegralInCell
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.PinNum

theorem goodAt_of_two_primes {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (hM : l.M = a * b) (p : ℕ) : l.GoodAt p := by
  have hodd := l.odd
  rw [hM, Nat.odd_mul] at hodd
  have ha3 : 3 ≤ a := by
    have := ha.two_le
    obtain ⟨k, hk⟩ := hodd.1
    omega
  have hb3 : 3 ≤ b := by
    have := hb.two_le
    obtain ⟨k, hk⟩ := hodd.2
    omega
  unfold Level.GoodAt
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  by_cases hp : p.Prime
  swap
  · simpa [Nat.factorization_eq_zero_of_not_prime _ hp] using l.three_le
  have key : ∀ c, 3 ≤ c → c ∣ l.M → ¬ p ∣ c → 3 ≤ l.M / p ^ l.M.factorization p := fun c hc hd hn =>
    hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
  by_cases h : p ∣ a
  · refine key b hb3 (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
    exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_primes ha hb).2 hab) h h'
  · exact key a ha3 (hM ▸ dvd_mul_right _ _) h

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  exact_mod_cast h

theorem xiR_pos_le_one (D : D7) (Q : Par D) (h : Q.PinHost) : 0 < xiR D ∧ xiR D ≤ 1 := by
  obtain ⟨-, -, h3, -⟩ := h
  have hsq := Q.H.sqrt_neg_disc_sq
  rw [h3] at hsq
  have hd : (1 : ℝ) ≤ Q.H.d := by exact_mod_cast Q.H.d_prime.one_le
  have hn : ‖D.host.φ₀ D.host.sqrtMinusD‖ ^ 2 = Q.H.d := by
    rw [← norm_pow, hsq, norm_neg, Complex.norm_natCast]
  have h1 : 1 ≤ ‖D.host.φ₀ D.host.sqrtMinusD‖ := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)]
  have hN : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hx : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖) := by
    unfold xiR Formalism.BasicNotions.Host.xi0
    rw [map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul,
      Complex.norm_natCast]
  have h2 : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    one_le_mul_of_one_le_of_one_le hN h1
  rw [hx]
  exact ⟨by positivity, (div_le_one (by positivity)).2 h2⟩

theorem numerics_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ Q.l.M' = Q.l.M ∧ 0 < xiR D ∧ xiR D ≤ 1 ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ ∀ j, InR D j → (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ 1 ≤ D.R.r ∧ (Q.Dw j).dim + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j := by
  intro D Q ⟨hH, ⟨hM, hA⟩, _, hD⟩
  have hx := xiR_pos_le_one D Q hH
  refine ⟨fun p _ => goodAt_of_two_primes Q.l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, hA, ?_,
    hx.1, hx.2, finrank_host D, fun j hj => ?_⟩
  · rw [Level.M', hA, Nat.lcm_one_right]
  · obtain ⟨hp, hq, -⟩ := hD j hj
    have hk := D.R.m_add_three_le_k
    obtain ⟨hj1, hj2⟩ := hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hp, hq]
      simp only [Ranks.sigW, Ranks.r]
      omega
    · unfold Ranks.r
      omega
    · rw [GlobalTheory.FlagDim.dim_add_card_flagVar, finrank_host, Nat.mul_div_cancel_left _ two_pos, hp, hq]
      rfl

end GlobalTheory.PinNum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPinsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_consequences_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ Q.l.M' = Q.l.M ∧ 0 < xiR D ∧ xiR D ≤ 1 ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ ∀ j, InR D j → (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ 1 ≤ D.R.r ∧ (Q.Dw j).dim + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j := by
  first | exact @GlobalTheory.PinNum.numerics_of_pins | exact GlobalTheory.PinNum.numerics_of_pins | (intros; apply GlobalTheory.PinNum.numerics_of_pins <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem MChart.tie_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R S : Type) [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S] (f : Γ(Y.X, M.U) →+* R) (ψ : R →ₐ[c.F] S) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R) (y : FrPt Xo c R) (z : FrPt Xo c S), M.Comparison₂ f u y → FrMap ψ y z → M.Comparison₂ (ψ.toRingHom.comp f) (fun τ => (u τ).map ψ) z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R S _ _ _ _ f ψ u y z hT hF
  obtain ⟨Λ, hL, hS⟩ := hT
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hF
  have hbase := GlobalTheory.T.lift_baseChange_alt E H Dw l Xo c O β Y M R f y.x Λ S ψ
  obtain ⟨Λ', hV, hTh⟩ := hbase
  rcases z with ⟨zx⟩
  dsimp only at hx hu h1 h2 h3 ⊢
  subst hx
  refine ⟨Λ', fun τ i => ?_, hTh _ _ pm h1 h2 h3 hS⟩
  have hv := hV _ _ (hL τ i)
  rw [← hu τ i] at hv
  exact hv

end GlobalTheory.Reg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieIntegral
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem tie_integral : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  intro hS E _ _ _ H Dw l Xo c O _ β Y M hP T io f₀ ix u₀ hu
  letI := io.toAlgebra
  intro z ⟨Λ, hL, hT⟩
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f₀ ≫ M.hU.fromSpec) Y.t
  have e : spMap ((algebraMap T.V T.Fr).comp f₀) ≫ M.hU.fromSpec =
      spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec := by
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : ∀ (g : Sp T.Fr ⟶ Y.X) (n : SABMap Λ.t' Y.t g),
      g = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec →
      ∃ m2 : SABMap Λ.t' _ (spMap (algebraMap T.V T.Fr)), m2.φ ≫ m.φ = n.φ := by
    intro g n hg
    subst hg
    obtain ⟨m2, h⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
    exact ⟨m2, h.symm⟩
  obtain ⟨m2, h2⟩ := key _ Λ.m2 e
  exact ⟨_, Λ.t', Λ.m1, m2,
    GlobalTheory.T.framedPoint_vectors_integral_in_cell E H Dw l Xo c O β Y M T io f₀ ix u₀ hu z Λ hL _ m m2 h2,
    GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr hS E H Dw l Xo c O β Y M hP T io f₀ z.x z.s Λ hT _ m m2 h2⟩

end GlobalTheory.Reg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppLEInjective
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Reg.TieUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem eq_of_loc {X : Scheme.{0}} {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ p ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), p ∈ W ∧ resG X hW a = resG X hW b) : a = b := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro p hp
  obtain ⟨W, hW, hpW, e⟩ := h p hp
  have e1 := X.presheaf.germ_res_apply (homOfLE hW) p hpW a
  have e2 := X.presheaf.germ_res_apply (homOfLE hW) p hpW b
  exact e1.symm.trans ((congrArg _ e).trans e2)

theorem sec_ext {X : Scheme.{0}} {L : LB X} {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s
  cases t
  congr 1
  exact funext h

theorem isoMaps_unique {X : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (w : LB.Iso L M) (σ : LB.Sec L)
    {s s' : LB.Sec M} (h : IsoMaps w σ s) (h' : IsoMaps w σ s') : s = s' := by
  refine sec_ext fun i => eq_of_loc _ _ fun p hp => ?_
  obtain ⟨k, hk⟩ := exists_chart hL p
  exact ⟨M.U i ⊓ L.U k, inf_le_left, ⟨hp, hk⟩, (h i k).trans (h' i k).symm⟩

theorem appLE_injective {X Y : Scheme.{0}} (g : Y ⟶ X) [IsIso g] (U : X.Opens) (V : Y.Opens) (h : V ≤ g ⁻¹ᵁ U)
    (h' : g ⁻¹ᵁ U ≤ V) : Function.Injective (g.appLE U V h).hom := by
  obtain rfl : V = g ⁻¹ᵁ U := le_antisymm h h'
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (g.app U)).1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {M : MChart Y} {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x : Sp R ⟶ Xo.X}

theorem rigIso_unique {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {g : S' ⟶ S} (m : SABMap t' t g)
    (hab : IsAbelianScheme t'.G) {w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} (h : RigIso m w) (h' : RigIso m w') :
    w = w' :=
  GlobalTheory.iso_eq_of_maps_along_section (S := S') (exists_chart t'.PP.isLB)
    (fun y => (exists_chart t.PP.isLB (m.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    t'.G.hom (eSec t'.G) (Over.w η[t'.G]) (GlobalTheory.globalFns_holds _ _ hab).2 h.1 h'.1 h.2 h'.2

theorem lift_abelian (Λ : M.Lift f x) : IsAbelianScheme Λ.t'.G := by
  have hp : IsProper Λ.t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) Λ.m1.cart.1 Xo.univ.proper
  exact ⟨Λ.t'.semi.comm, Λ.t'.semi.smooth, hp, Λ.t'.semi.geomConnected⟩

theorem lift_mem (Λ : M.Lift f x) (p : Λ.t'.G.left) : Y.t.G.hom (Λ.m2.φ p) ∈ M.U := by
  have e : Λ.m2.φ ≫ Y.t.G.hom = Λ.t'.G.hom ≫ spMap f ≫ M.hU.fromSpec := Λ.m2.cart.1.w
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  have := M.hU.range_fromSpec
  exact this.le ⟨_, rfl⟩

theorem thTie_unique (Λ : M.Lift f x) {s s' : LB.Sec (PPx x)} (h : Λ.ThTie s) (h' : Λ.ThTie s') : s = s' := by
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, a, b⟩ := h
  obtain ⟨w1', w2', σ', s1', r1', r2', i1', a', b'⟩ := h'
  obtain rfl : w1 = w1' := rigIso_unique Λ.m1 (lift_abelian Λ) r1 r1'
  obtain rfl : w2 = w2' := rigIso_unique Λ.m2 (lift_abelian Λ) r2 r2'
  obtain rfl : σ = σ' := by
    refine sec_ext fun k => eq_of_loc _ _ fun p hp => ?_
    obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (Λ.m2.φ p)
    have h₁ : (Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k ≤
        Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) := fun q hq => ⟨lift_mem Λ q, mem_pull.1 hq.1⟩
    refine ⟨(Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k, inf_le_right, ⟨mem_pull.2 hj, hp⟩, ?_⟩
    have e := (a j k _ h₁ le_rfl).symm.trans (a' j k _ h₁ le_rfl)
    exact (((w2.s (fun _ => j, k)).isUnit.map _).mul_left_cancel e)
  obtain rfl : s1 = s1' := isoMaps_unique Λ.t'.PP.isLB w1 σ i1 i1'
  have hc : IsPullback Λ.t'.G.hom Λ.m1.φ x Xo.univ.t.G.hom := Λ.m1.cart.1.flip
  let g : Λ.t'.G.left ⟶ Gx x := hc.isoPullback.hom
  have hg : IsIso g := inferInstanceAs (IsIso hc.isoPullback.hom)
  have g1 : g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ := hc.isoPullback_hom_snd
  have g2 : g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom := hc.isoPullback_hom_fst
  refine sec_ext fun i => ?_
  obtain ⟨j, rfl⟩ : ∃ j : Xo.univ.t.PP.L.ι, i = fun _ => j := ⟨i (0 : Fin 1), funext fun k => congrArg i (Subsingleton.elim (α := Fin 1) k 0)⟩
  have hm : ∀ q : Λ.t'.G.left, q ∈ g ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ Λ.m1.φ q ∈ Xo.univ.t.PP.L.U j := by
    intro q
    rw [← g1, Scheme.Hom.comp_apply]
    exact ⟨fun hq => Set.mem_iInter.1 hq (0 : Fin 1), fun hq => Set.mem_iInter.2 fun _ => hq⟩
  have h₁ : (Xo.univ.t.PP.L.pull Λ.m1.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j) :=
    fun q hq => (hm q).2 (mem_pull.1 hq)
  exact appLE_injective g _ _ h₁ (fun q hq => mem_pull.2 ((hm q).1 hq))
    ((b g g1 g2 (fun _ => j) h₁).symm.trans (b' g g1 g2 (fun _ => j) h₁))

theorem frPt_eq_of_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (y z : FrPt Xo c L), M.Comparison₂ f u y → M.Comparison₂ f u z → y.x = z.x → y = z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f u y z hy hz hx
  obtain ⟨x, xo, v, t1, t2, t3, s, t4⟩ := y
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := z
  obtain rfl : x = x' := hx
  obtain ⟨Λ, hv, hs⟩ := hy
  obtain ⟨Λ', hv', hs'⟩ := hz
  obtain ⟨k1, k2⟩ := GlobalTheory.T.modelChartLift_coords_generator_indep E H Dw l Xo c O β Y M L f x Λ' Λ
  obtain rfl : v = v' := by
    funext τ i
    exact ((GlobalTheory.T.lieBasis_coordinates_bijective_tangent E H Dw l Xo c O β Y M L f x Λ).1 _).unique (hv τ i) (k1 _ _ (hv' τ i))
  obtain rfl : s = s' := thTie_unique Λ hs (k2 _ hs')
  rfl

end GlobalTheory.Reg.TieUniq
end
end
