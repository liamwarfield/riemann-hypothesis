module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousPeriodBasisAlongArcStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerFurther
theorem UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] {N : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E N) (v : Fin N → E),
    ∃ (n : ℕ),
      (0 : ℕ) < n ∧
        (↑n : E) • v ∈
          X.Λ := by
  intro E _ _ _ N X v
  refine Submodule.span_induction (fun x hx => ⟨1, one_pos, by simpa using hx⟩) ⟨1, one_pos, by simp⟩
    ?_ ?_ (X.Λ_span ▸ Submodule.mem_top : v ∈ Submodule.span E (X.Λ : Set (Fin N → E)))
  · rintro x y - - ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    convert X.Λ.add_mem (nsmul_mem hx b) (nsmul_mem hy a) using 1
    ext i; simp; ring
  · rintro c x - ⟨a, ha, hx⟩
    obtain ⟨m, s, hm, hs⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (.of_finite ℚ c)).exists_nsmul_eq (NumberField.RingOfIntegers E)
    refine ⟨m * a, mul_pos (Nat.pos_of_ne_zero hm) ha, ?_⟩
    convert X.Λ.smul_mem s hx using 1
    rw [← algebraMap_smul E s, ← hs]; ext i; simp; ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsPolynomialGrowthLatticeVectorArc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsPolynomialGrowthLatticeVectorArc
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerPoly


open scoped CategoryTheory.MonObj in
theorem exists_transfer_iff {S S' S0 : Scheme.{0}} {G : Over S} {G' : Over S'} {G0 : Over S0} [GrpObj G] [GrpObj G']
    [GrpObj G0] {f : S' ⟶ S} {f0 : S' ⟶ S0} {φ : G'.left ⟶ G.left} {φ0 : G'.left ⟶ G0.left}
    (h : IsGrpPullback G' G f φ) (h0 : IsGrpPullback G' G0 f0 φ0) (q : Sp ℂ ⟶ S') {y : Sp ℂ ⟶ S} {y0 : Sp ℂ ⟶ S0}
    (hy : q ≫ f = y) (hy0 : q ≫ f0 = y0) {g : ℕ} (ex0 : (Fin g → ℂ) → (Over.mk y0 ⟶ G0))
    (hadd : ∀ z w, ex0 (z + w) = ex0 z * ex0 w)
    (hol : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G0.left from (ex0 z).left))) :
    ∃ ex : (Fin g → ℂ) → (Over.mk y ⟶ G), (∀ z w, ex (z + w) = ex z * ex w) ∧
      IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (ex z).left)) ∧
      (∀ (d : Fin g → ℂ) (w : Sp (DualNumber ℂ) ⟶ G'.left),
        w ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ q →
        IsDerivAt0 (fun z => (ex0 z).left) d (w ≫ φ0) → IsDerivAt0 (fun z => (ex z).left) d (w ≫ φ)) ∧
      ∀ z, ex z = 1 ↔ ex0 z = 1 := by
  subst hy hy0
  let ex' : (Fin g → ℂ) → (Over.mk q ⟶ G') := fun z =>
    Over.homMk (h0.1.lift (ex0 z).left q (Over.w (ex0 z))) (h0.1.lift_snd _ _ _)
  have e0 : ∀ z, pushHom h0 (Over.mk q) (ex' z) = ex0 z := fun z =>
    Over.OverMorphism.ext (h0.1.lift_fst _ _ _)
  have e0' : ∀ z, (ex' z).left ≫ φ0 = (ex0 z).left := fun z => h0.1.lift_fst _ _ _
  have e1 : ∀ z, (ex' z).left ≫ G'.hom = q := fun z => Over.w (ex' z)
  have inj0 : Function.Injective (pushHom h0 (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h0.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have inj : Function.Injective (pushHom h (Over.mk q)) := fun a b hab =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  have hA : ∀ t, HolHom.HolAt (fun z => (show Sp ℂ ⟶ G'.left from (ex' z).left)) t := fun t =>
    HolHom.holAt_of_isPullback h0.1
      (by simp only [e0']; exact HolHom.holAt_of_isHolTo hol (Set.mem_univ t))
      (by simp only [e1]; exact HolHom.holAt_const _ _)
  refine ⟨fun z => pushHom h (Over.mk q) (ex' z), fun z w => ?_, ?_, fun d w hw hd => ?_, fun z => ⟨fun hz => ?_,
    fun hz => ?_⟩⟩
  · have : ex' (z + w) = ex' z * ex' w := inj0 (by rw [map_mul, e0, e0, e0]; exact hadd z w)
    exact (congrArg _ this).trans (map_mul _ _ _)
  · exact HolHom.isHolTo_of_holAt isOpen_univ fun t _ => (hA t).comp φ
  · obtain ⟨v, hv⟩ := (hA 0).exists_isDerivAt d
    have h1 := hv.comp φ0
    simp only [e0'] at h1
    have h2 : v = w := h0.1.hom_ext (h1.unique ((HolHom.isDerivAt0_iff _ _ _).1 hd))
      ((HolHom.IsDerivAt.over (a := ex') hv).trans hw.symm)
    subst h2
    exact (HolHom.isDerivAt0_iff _ _ _).2 (hv.comp φ)
  · have : ex' z = 1 := inj (hz.trans (map_one _).symm)
    rw [← e0, this]
    exact map_one _
  · have : ex' z = 1 := inj0 ((e0 z).trans (hz.trans (map_one _).symm))
    show pushHom h (Over.mk q) (ex' z) = 1
    rw [this]
    exact map_one _

def zComb {m : ℕ} {V : Type} [AddCommGroup V] (lam : Fin m → V) : (Fin m → ℤ) →+ V :=
  (Fintype.linearCombination ℤ lam).toAddMonoidHom

theorem zComb_apply {m : ℕ} {V : Type} [AddCommGroup V] (lam : Fin m → V) (n : Fin m → ℤ) :
    zComb lam n = ∑ j, n j • lam j := Fintype.linearCombination_apply ℤ lam n

theorem zComb_lattice {m g : ℕ} (lam : Fin m → Fin g → ℂ) (hli : LinearIndependent ℝ lam)
    (hsp : Submodule.span ℝ (Set.range lam) = ⊤) :
    Function.Injective (zComb lam) ∧ DiscreteTopology (zComb lam).range ∧
      Submodule.span ℝ (Set.range (zComb lam)) = ⊤ := by
  refine ⟨fun n n' h => ?_, ?_, ?_⟩
  · rw [zComb_apply, zComb_apply] at h
    have h0 : ∑ j, ((n j - n' j : ℤ) : ℝ) • lam j = 0 := by
      simp only [Int.cast_smul_eq_zsmul, sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext j
    have := Fintype.linearIndependent_iff.1 hli _ h0 j
    exact sub_eq_zero.1 (by exact_mod_cast this)
  · let bas := Module.Basis.mk hli hsp.ge
    have hr : (zComb lam).range = (Submodule.span ℤ (Set.range bas)).toAddSubgroup := by
      ext x
      simp only [bas, AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Module.Basis.coe_mk, Module.Basis.mk_apply,
        Submodule.mem_span_range_iff_exists_fun, zComb_apply]
    rw [hr]
    exact (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range bas)))
  · refine eq_top_iff.2 (hsp.ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    rw [zComb_apply]
    simp [Pi.single_apply]

end GlobalTheory.ShFam.PerPoly

namespace GlobalTheory.ShFam.PerPoly

theorem periods_le_of_mem_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ v ∈ (U.X k).Λ, ∀ R : ℝ, ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift v hv R
  obtain ⟨hN, hX, -, -, -, g, e, F, ik, φL, -, hfr⟩ := hU
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  swap
  · refine ⟨0, 0, Filter.Eventually.of_forall fun w _ τ i hτ => ?_⟩
    exfalso
    have hp0 := (hX k).1
    rcases hτ with ⟨_, hi⟩ | ⟨_, hi⟩ <;> omega
  have hoff : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ∀ s, (spMap (ψ u) ≫ x) s ∉ genBd Z := by
    intro u hu hu0 s hb
    obtain ⟨hm1, -⟩ := hm u hu hu0
    have hm1' : GlobalTheory.AllWt.ptF (y u) ≫ Z.jQ = spMap (ψ u) ≫ x := hm1
    exact hb ⟨GlobalTheory.AllWt.ptF (y u) s, by rw [← hm1']; rfl⟩
  obtain ⟨T₀, m, lam, hT₀, hcont, hbas, hker, hgrow⟩ :=
    GlobalTheory.T.exists_continuous_period_basis_along_arc E H Dw l Xo c O β Z σ A φ x fr ψ r g e hσ hpq harc hoff
  obtain ⟨-, -, hxd, hxm, -⟩ := horb
  set T₁ := max T T₀ with hT₁def
  have hT₁ : ∀ w : ℂ, T₁ < w.im → T < w.im ∧ T₀ < w.im := fun w hw =>
    ⟨(le_max_left _ _).trans_lt hw, (le_max_right _ _).trans_lt hw⟩
  let B := {w : ℂ // w ∈ {w : ℂ | T₁ < w.im}}
  haveI : PreconnectedSpace B := Subtype.preconnectedSpace (convex_halfSpace_im_gt T₁).isPreconnected
  have hdom : ∀ b : B, xx b ∈ (U.X k).dom := fun b => hxm b (hT₁ b b.2).1
  choose Pm hPm hper hpt hder hrest using fun b : B => hfr k ⟨xx b, hdom b⟩
  clear hrest
  set a₀ := (φL k).symm ⟨v, hv⟩ with ha₀
  have hva : ((φL k a₀ : (U.X k).Λ) : Fin N → E) = v := by rw [ha₀, LinearEquiv.apply_symm_apply]
  have key : ∀ b : B, ∃ n : Fin m → ℤ, Pm b a₀ = zComb (lam b) n := fun b => by
    have hb := hT₀ b (hT₁ b b.2).2
    obtain ⟨_, hx1, hx2⟩ := hlift b (hT₁ b b.2).1
    obtain ⟨hm1, hm2⟩ := hm _ hb (Complex.exp_ne_zero _)
    have h0 : GlobalTheory.AllWt.ptF (y (eTwoPi b)) ≫ pullback.fst _ _ = (y (eTwoPi b)).x := pullback.lift_fst _ _ _
    obtain ⟨ex, a1, a2, a3, a4⟩ := exists_transfer_iff Z.m.cart Z.m0.toSABMap.cart
      (GlobalTheory.AllWt.ptF (S := CAt σ) (y (eTwoPi b)) :)
      (y := spMap (ψ (eTwoPi b)) ≫ x ≫ genι Z) (y0 := F.u (ik k) (Pm b))
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ genι Z) hm1).trans (Category.assoc _ _ _)))
      (h0.trans (hx1.symm.trans (hpt b))) (F.ex (ik k) (Pm b)) (F.ex_add _ _ (hper b))
      (HolHom.isHolTo_ex F _ (hper b))
    have hk := hker b (hT₁ b b.2).2 ex a1 a2 (fun jj => by
      obtain ⟨w, w1, w2, w3⟩ := hm2 (e jj).1 (e jj).2
      have hd := hder b (e jj).1 (e jj).2
      rw [hx2, ← w2, Sigma.eta, Equiv.symm_apply_apply] at hd
      exact w3 ▸ a3 _ w w1 hd) (Pm b a₀)
    obtain ⟨n, hn⟩ := hk.1 ((a4 _).2 ((F.ex_ker _ _ (hper b) _).2 ⟨a₀, rfl⟩))
    exact ⟨n, hn.trans (zComb_apply _ _).symm⟩
  choose n hn using key
  have hxc : Continuous fun b : B => xx b :=
    (hxd.continuousOn.mono fun w hw => (hT₁ w hw).1).restrict
  have hPc : ∀ z, Continuous fun b : B => Pm b z := fun z => continuous_pi fun jj => by
    simp only [hPm]
    exact PerLim.continuous_perFr _ hdom hxc _ _ _
  have hlc : ∀ j, Continuous fun b : B => lam b j := fun j =>
    (continuous_apply j).comp (hcont.comp_continuous continuous_subtype_val fun b => (hT₁ b b.2).2)
  have hZc : ∀ z, Continuous fun b : B => zComb (lam b) z := fun z => by
    simp only [zComb_apply]
    exact continuous_finsetSum _ fun j _ => (hlc j).const_smul (z j)
  let b₀ : B := ⟨(T₁ + 1 : ℝ) * Complex.I, by simp⟩
  have hconst : ∀ b, n b = n b₀ := fun b => by
    refine IsLocallyConstant.apply_eq_of_preconnectedSpace (f := n)
      ((IsLocallyConstant.iff_eventually_eq _).2 fun b' => ?_) b b₀
    obtain ⟨hi, hd, hs⟩ := zComb_lattice (lam b') (hbas b' (hT₁ b' b'.2).2).1 (hbas b' (hT₁ b' b'.2).2).2
    refine PerLim.eventually_eq_of_lattice (fun b : B => zComb (lam b)) hZc b' hi hd hs n ?_
    exact (hPc a₀).congr fun b => hn b
  obtain ⟨C, Bx, hC⟩ := hgrow R
  have hidx : ∀ (τ : E →+* ℂ) (m : ℕ), m = (if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q) →
      ∃ s : Fin m → Fin g, Function.Injective s ∧ ∀ i, relab c σ (e (s i)).1 = τ ∧ ((e (s i)).2 : ℕ) = i := by
    intro τ m hmτ
    obtain ⟨τ', rfl⟩ := Finite.injective_iff_surjective.1 (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_injective c σ) τ
    have h1 : m = Dw.mult τ' := by
      rw [hmτ, Datum.mult]
      exact if_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.UH.relab_rt c σ hσ τ') rfl rfl
    subst h1
    refine ⟨fun i => e.symm ⟨τ', i⟩, fun i i' h => ?_, fun i => ?_⟩
    · exact eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2
    · rw [Equiv.apply_symm_apply]
      exact ⟨rfl, rfl⟩
  have hlet : ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨
      (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) → ∃ jj : Fin g, relab c σ (e jj).1 = τ ∧ ((e jj).2 : ℕ) = i := by
    intro τ i hτ
    rcases hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨s, -, hs⟩ := hidx τ (N - (U.X k).p0) (by
        rw [if_pos (((hX k).2 _).1 h1), (hX k).1, hN, Nat.add_sub_cancel])
      exact ⟨s ⟨i, h2⟩, hs _⟩
    · have hcc : NumberField.ComplexEmbedding.conjugate (conjEmb τ) = τ := RingHom.ext fun a => by
        simp [conjEmb, NumberField.ComplexEmbedding.conjugate_coe_eq]
      have hne : ¬ τ (H.rt : E) = H.rt0 := fun h =>
        ((U.X k).cmType (conjEmb τ)).1 h1 (by rw [hcc]; exact ((hX k).2 τ).2 h)
      obtain ⟨s, -, hs⟩ := hidx τ (U.X k).p0 (by rw [if_neg hne, (hX k).1])
      exact ⟨s ⟨i, h2⟩, hs _⟩
  refine ⟨(∑ j, (|n b₀ j| : ℝ)) * C, Bx, ?_⟩
  filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T₁)]
    with w hw hR τ i hτ
  obtain ⟨jj, hj1, hj2⟩ := hlet τ i hτ
  have hP : perFr (U.X k) (xx w) v τ i = Pm ⟨w, hw⟩ a₀ jj := by
    rw [hPm, hva, hj1, hj2]
  rw [hP, hn, hconst, zComb_apply]
  have hl := hC w (hT₁ w hw).2 hR
  calc ‖(∑ j, n b₀ j • lam (⟨w, hw⟩ : B) j) jj‖ ≤ ‖∑ j, n b₀ j • lam (⟨w, hw⟩ : B) j‖ := norm_le_pi_norm _ _
    _ ≤ ∑ j, ‖n b₀ j • lam w j‖ := norm_sum_le _ _
    _ ≤ ∑ j, (|n b₀ j| : ℝ) * ‖lam w‖ := Finset.sum_le_sum fun j _ => by
        rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs, ← Int.cast_abs]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) (by positivity)
    _ = (∑ j, (|n b₀ j| : ℝ)) * ‖lam w‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ j, (|n b₀ j| : ℝ)) * (C * w.im ^ Bx) :=
        mul_le_mul_of_nonneg_left hl (Finset.sum_nonneg fun j _ => by positivity)
    _ = _ := (mul_assoc _ _ _).symm

end GlobalTheory.ShFam.PerPoly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsPolynomialGrowthLatticeVectorArcStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_polynomial_growth_lattice_vector_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ v ∈ (U.X k).Λ, ∀ R : ℝ, ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C * w.im ^ B := by
  first | exact @GlobalTheory.ShFam.PerPoly.periods_le_of_mem_lattice | exact GlobalTheory.ShFam.PerPoly.periods_le_of_mem_lattice | (intros; apply GlobalTheory.ShFam.PerPoly.periods_le_of_mem_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsBoundedOutsideCmTypeOfDefiniteArcLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsBoundedOutsideCmTypeOfDefiniteArcLift
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerLim

theorem tendsto_of_inv_mulVec_span {α : Type} {l : Filter α} {N n : ℕ} (M : α → Matrix (Fin N) (Fin N) ℂ)
    (u : Fin n → Fin N → ℂ) (L : Fin n → Fin N → ℂ) (hdet : ∀ᶠ w in l, (M w).det ≠ 0)
    (ht : ∀ j, Tendsto (fun w => Matrix.mulVec (M w)⁻¹ (u j)) l (𝓝 (L j)))
    (hs : Submodule.span ℂ (Set.range L) = ⊤) : ∃ L0, Tendsto M l (𝓝 L0) := by
  have hc : ∀ a : Fin N, ∃ c : Fin n → ℂ, ∑ j, c j • L j = Pi.single a 1 := fun a =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hs ▸ Submodule.mem_top)
  choose c hc using hc
  let W : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun b a => ∑ j, c a j * u j b
  have hR : Tendsto (fun w => (M w)⁻¹ * W) l (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a' => tendsto_pi_nhds.2 fun a => ?_
    have e : ∀ w, ((M w)⁻¹ * W) a' a = ∑ j, c a j * (Matrix.mulVec (M w)⁻¹ (u j)) a' := by
      intro w
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, W, Matrix.of_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
    have lim : (1 : Matrix (Fin N) (Fin N) ℂ) a' a = ∑ j, c a j * L j a' := by
      have := congrFun (hc a) a'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this, Pi.single_apply, Matrix.one_apply]
    simp only [e]
    rw [lim]
    exact tendsto_finsetSum _ fun j _ => ((ht j).apply_nhds a').const_mul _
  have hRi : Tendsto (fun w => ((M w)⁻¹ * W)⁻¹) l (𝓝 1) := by
    have h0 : ContinuousAt Ring.inverse (1 : Matrix (Fin N) (Fin N) ℂ).det := by
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h1 := ((continuousAt_matrix_inv (1 : Matrix (Fin N) (Fin N) ℂ) h0).tendsto).comp hR
    rw [inv_one] at h1
    exact h1
  have hRd : ∀ᶠ w in l, ((M w)⁻¹ * W).det ≠ 0 := by
    have h1 : Tendsto (fun w => ((M w)⁻¹ * W).det) l (𝓝 (1 : Matrix (Fin N) (Fin N) ℂ).det) :=
      ((Continuous.matrix_det continuous_id).tendsto (1 : Matrix (Fin N) (Fin N) ℂ)).comp hR
    rw [Matrix.det_one] at h1
    exact h1.eventually_ne one_ne_zero
  refine ⟨W, ?_⟩
  have hlim : Tendsto (fun w => W * ((M w)⁻¹ * W)⁻¹) l (𝓝 (W * 1)) :=
    ((continuous_const.matrix_mul continuous_id).tendsto _).comp hRi
  rw [Matrix.mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hdet, hRd] with w h1 h2
  have e1 : M w * ((M w)⁻¹ * W) = W := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.one_mul]
  calc W * ((M w)⁻¹ * W)⁻¹ = M w * ((M w)⁻¹ * W) * ((M w)⁻¹ * W)⁻¹ := by rw [e1]
    _ = M w := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h2), Matrix.mul_one]

theorem periods_bounded_outside_cmType_of_definite_arc_lift_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → (U.X k).p0 = 0 → ∀ v : Fin N → E, ∃ C : ℝ, ∀ᶠ w in imTop, ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift hp0 v
  obtain ⟨n, vv, Lp, Lm, hLp, -, hsp⟩ := GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x
    fr ψ r y k T M γ xx hσ hU harc hm horb hlift
  have hdom : ∀ᶠ w in imTop, xx w ∈ (U.X k).dom := by
    filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)] with w hw
    exact horb.2.2.2.1 w hw
  have hmat : ∀ τ' : (U.X k).Ψ, ∃ L0, Tendsto (fun w => mat (xx w) τ') imTop (𝓝 L0) := by
    intro τ'
    refine tendsto_of_inv_mulVec_span (fun w => mat (xx w) τ') (fun j => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 (vv j))
      (fun j i => Lp j τ' ⟨i, by omega⟩) ?_ ?_ ?_
    · filter_upwards [hdom] with w hw
      exact (hw τ').1
    · intro j
      refine tendsto_pi_nhds.2 fun i => ?_
      have hi : (i : ℕ) < N - (U.X k).p0 := by omega
      refine (hLp j τ' ⟨i, hi⟩).congr fun w => ?_
      unfold perFr
      rw [dite_eq_left τ'.2, dite_eq_left (by simp only [hp0]; omega)]
      congr 1
      ext
      simp [hp0]
    · exact span_proj (fun j => Lp j τ') (hsp τ').1 (fun i => ⟨i, by omega⟩)
        (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
  choose L0 hL0 using hmat
  let F : ℂ → ((U.X k).Ψ → Fin N → ℂ) := fun w τ' a =>
    ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (mat (xx w) τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v)
  have hF : Tendsto F imTop (𝓝 (fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v))) := by
    refine tendsto_pi_nhds.2 fun τ' => tendsto_pi_nhds.2 fun a => ?_
    have hc : Continuous fun Mx : Matrix (Fin N) (Fin N) ℂ =>
        ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col Mx a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.hermC col
      fun_prop
    exact (hc.tendsto _).comp (hL0 τ')
  refine ⟨‖(fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) :
      (U.X k).Ψ → Fin N → ℂ)‖ + 1, ?_⟩
  filter_upwards [hF.norm.eventually (gt_mem_nhds (lt_add_one _))] with w hw
  intro τ i hτ
  unfold perFr
  rw [dite_eq_right hτ]
  split_ifs with h' hj
  · exact ((norm_le_pi_norm (F w ⟨_, h'⟩) ⟨_, hj⟩).trans (norm_le_pi_norm (F w) ⟨_, h'⟩)).trans hw.le
  · simp only [norm_zero]; positivity
  · simp only [norm_zero]; positivity

end GlobalTheory.ShFam.PerLim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsBoundedOutsideCmTypeOfDefiniteArcLiftStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_bounded_outside_cmType_of_definite_arc_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → (U.X k).p0 = 0 → ∀ v : Fin N → E, ∃ C : ℝ, ∀ᶠ w in imTop, ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C := by
  first | exact @GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt | exact GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt | (intros; apply GlobalTheory.ShFam.PerLim.periods_bounded_outside_cmType_of_definite_arc_lift_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBound
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.ShFam.PerPoly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_nat_smul_mem {N : ℕ} (X : Data E N) (v : Fin N → E) :
    ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ :=
  _root_.UpperTheory.Reformulated.B.Ga5b.exists_nat_smul_mem X v

theorem perFr_natCast_smul {N : ℕ} (X : Data E N) (x : Frame X.Ψ N) (v : Fin N → E) (n : ℕ) (τ : E →+* ℂ) (i : ℕ) :
    perFr X x ((n : E) • v) τ i = (n : ℂ) * perFr X x v τ i := by
  have he : ∀ τ : E →+* ℂ, Data.emb τ ((n : E) • v) = (n : ℂ) • Data.emb τ v := fun τ => funext fun a => by
    simp [Data.emb, map_natCast]
  unfold perFr
  split_ifs <;> simp [he, Matrix.mulVec_smul, ReciprocityTheory.ChartRestriction.G.FD.hermC, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

end GlobalTheory.ShFam.PerPoly

namespace GlobalTheory.ShFam.PerPoly

theorem periods_le_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ (v : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr (U.X k) (xx w) v ρ i‖ ≤ C * w.im ^ B := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift v R
  obtain ⟨n, hn, hnv⟩ := exists_nat_smul_mem (U.X k) v
  obtain ⟨C₁, B, h₁⟩ := GlobalTheory.T.periods_polynomial_growth_lattice_vector_arc E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
    _ hnv R
  obtain ⟨C₃, h₃⟩ : ∃ C₃ : ℝ, ∀ᶠ w in imTop, (U.X k).p0 = 0 → ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := by
    by_cases h0 : (U.X k).p0 = 0
    · obtain ⟨C₃, h⟩ := GlobalTheory.T.periods_bounded_outside_cmType_of_definite_arc_lift E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift
        h0 v
      exact ⟨C₃, h.mono fun w hw _ => hw⟩
    · exact ⟨0, .of_forall fun w h => absurd h h0⟩
  have him : ∀ᶠ w in imTop, 1 ≤ w.im :=
    (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_ge_atTop 1)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨max (C₁ / n) 0 + max C₃ 0, B, ?_⟩
  filter_upwards [h₁, h₃, him] with w hw1 hw3 hwi hR τ i
  have hpow : 1 ≤ w.im ^ B := one_le_pow₀ hwi
  have hK0 : 0 ≤ max (C₁ / n) 0 + max C₃ 0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hK1 : C₁ / n ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
  have hK3 : C₃ ≤ max (C₁ / n) 0 + max C₃ 0 := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  have hlat : ∀ (τ : E →+* ℂ) (i : ℕ), (τ ∈ (U.X k).Ψ ∧ i < N - (U.X k).p0) ∨ (conjEmb τ ∈ (U.X k).Ψ ∧ i < (U.X k).p0) →
      ‖perFr (U.X k) (xx w) v τ i‖ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := by
    intro τ i h
    have h2 := hw1 hR τ i h
    rw [perFr_natCast_smul, norm_mul, Complex.norm_natCast] at h2
    have h3 : ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₁ / n * w.im ^ B := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hn']
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_right hK1 (by positivity))
  have hzero : 0 ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := mul_nonneg hK0 (by positivity)
  by_cases hτ : τ ∈ (U.X k).Ψ
  · by_cases hi : i < N - (U.X k).p0
    · exact hlat τ i (Or.inl ⟨hτ, hi⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dite_eq_left hτ, dite_eq_right (by omega)]
      rw [e, norm_zero]
      exact hzero
  · by_cases hc : conjEmb τ ∈ (U.X k).Ψ
    · by_cases h0 : (U.X k).p0 = 0
      · calc ‖perFr (U.X k) (xx w) v τ i‖ ≤ C₃ := hw3 h0 τ i hτ
          _ ≤ max (C₁ / n) 0 + max C₃ 0 := hK3
          _ ≤ (max (C₁ / n) 0 + max C₃ 0) * w.im ^ B := le_mul_of_one_le_right hK0 hpow
      · by_cases hi : i < (U.X k).p0
        · exact hlat τ i (Or.inr ⟨hc, hi⟩)
        · have e : perFr (U.X k) (xx w) v τ i = perFr (U.X k) (xx w) v τ ((U.X k).p0 - 1) := by
            have e1 : (U.X k).p0 - 1 - i = (U.X k).p0 - 1 - ((U.X k).p0 - 1) := by omega
            unfold perFr
            rw [dite_eq_right hτ, dite_eq_right hτ, dite_eq_left hc, dite_eq_left hc]
            simp only [e1]
          rw [e]
          exact hlat τ _ (Or.inr ⟨hc, by omega⟩)
    · have e : perFr (U.X k) (xx w) v τ i = 0 := by
        unfold perFr
        rw [dite_eq_right hτ, dite_eq_right hc]
      rw [e, norm_zero]
      exact hzero

end GlobalTheory.ShFam.PerPoly
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBoundStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_specialization_uniform_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → ∀ (v : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr (U.X k) (xx w) v ρ i‖ ≤ C * w.im ^ B := by
  first | exact @GlobalTheory.ShFam.PerPoly.periods_le_pow | exact GlobalTheory.ShFam.PerPoly.periods_le_pow | (intros; apply GlobalTheory.ShFam.PerPoly.periods_le_pow <;> assumption)
end
