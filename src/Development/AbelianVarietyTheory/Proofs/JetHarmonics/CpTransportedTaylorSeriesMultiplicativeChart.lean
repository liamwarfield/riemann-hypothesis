module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLawsStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

lemma hatmul_DT_C_mul {q : ℕ} [Fact q.Prime] (c : ℂ_[q]) (f : ℂ_[q]⟦X⟧) :
    DT (C c * f) = C c * DT f := by
  unfold DT
  rw [← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul]
  ring

lemma hatmul_const_log {q : ℕ} [Fact q.Prime] (ω : ℂ_[q]) :
    constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [logS]
  simp [this]

lemma hatmul_DT_hat {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ)
    (hG : AnalyticAt ℂ G 0) :
    DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G) := by
  obtain ⟨-, -, -, -, hd, -, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
  obtain ⟨-, -, -, -, hl, -⟩ := GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q
  have h1 : DT (C ω * logS : ℂ_[q]⟦X⟧) = C ω := by rw [hatmul_DT_C_mul, hl, mul_one]
  unfold DT at h1 ⊢
  have hd' : d⁄dX (hat ι (C ω * logS) G) =
      d⁄dX (C ω * logS) * hat ι (C ω * logS) (deriv G) := hd G hG
  rw [hd', ← mul_assoc, h1]

lemma hatmul_iter {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (k : ℕ) :
    ∀ (G : ℂ → ℂ), AnalyticAt ℂ G 0 →
      DT^[k] (hat ι (C ω * logS) G) = C (ω ^ k) * hat ι (C ω * logS) (iteratedDeriv k G) := by
  induction k with
  | zero => intro G _; simp
  | succ k ih =>
    intro G hG
    have hk : AnalyticAt ℂ (iteratedDeriv k G) 0 := by
      rw [iteratedDeriv_eq_iterate]
      exact hG.iterated_deriv k
    rw [Function.iterate_succ_apply', ih G hG, hatmul_DT_C_mul, hatmul_DT_hat ι ω _ hk,
      iteratedDeriv_succ, pow_succ, map_mul, mul_assoc]

lemma hatmul_subst {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ) (a : ℤ_[q]) :
    hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  obtain ⟨-, -, -, -, -, -, hs⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
  obtain ⟨hm, -⟩ := GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q
  obtain ⟨-, h0, -, hl⟩ := hm a
  have hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' h0
  rw [hs G _ h0, ← smul_eq_C_mul (a := ω), subst_smul hsub, hl, smul_eq_C_mul, map_mul, mul_assoc]

theorem hat_multiplicative_chart : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), AnalyticAt ℂ G 0 → (DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G)) ∧ (∀ k : ℕ, constantCoeff (DT^[k] (hat ι (C ω * logS) G)) = ω ^ k * ι (iteratedDeriv k G 0)) ∧ (∀ (α : ℂ) (a : ℤ_[q]), ι α = zc a → hat ι (C ω * logS) (fun z => G (α * z)) = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧)) ∧ ∀ a : ℤ_[q], hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  intro q _ ι ω G hG
  refine ⟨hatmul_DT_hat ι ω G hG, fun k => ?_, fun α a ha => ?_, hatmul_subst ι ω G⟩
  · obtain ⟨-, -, -, hc, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
    rw [hatmul_iter ι ω k G hG, map_mul, hc, constantCoeff_C]
  · obtain ⟨-, -, -, -, -, hα, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
    rw [hα G α hG, ← hatmul_subst, ha, map_mul, ← mul_assoc, mul_comm (C (zc a))]

end GlobalTheory.MomOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChartStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_multiplicativeChart : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), AnalyticAt ℂ G 0 → (DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G)) ∧ (∀ k : ℕ, constantCoeff (DT^[k] (hat ι (C ω * logS) G)) = ω ^ k * ι (iteratedDeriv k G 0)) ∧ (∀ (α : ℂ) (a : ℤ_[q]), ι α = zc a → hat ι (C ω * logS) (fun z => G (α * z)) = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧)) ∧ ∀ a : ℤ_[q], hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  first | exact @GlobalTheory.MomOne.hat_multiplicative_chart | exact GlobalTheory.MomOne.hat_multiplicative_chart | (intros; apply GlobalTheory.MomOne.hat_multiplicative_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRepresentableOfCover
noncomputable section

namespace GlobalTheory.GenTorsor

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Z : Scheme.{0}}

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

end Cover

theorem isRepresentable_of_cover (F : Scheme.{0}ᵒᵖ ⥤ Type)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) (p : F ⟶ yoneda.obj X)
    {J : Type} (W : J → X.Opens) (hW : iSup W = ⊤) (T : J → Scheme.{0})
    (y : ∀ i, F.obj (op (T i))) (π : ∀ i, T i ⟶ W i)
    (hπ : ∀ i, p.app _ (y i) = π i ≫ (W i).ι)
    (h : ∀ i (Z : Scheme.{0}) (x : F.obj (op Z)) (b : Z ⟶ W i), p.app _ x = b ≫ (W i).ι →
      ∃! c : Z ⟶ T i, F.map c.op (y i) = x) : F.IsRepresentable := by
  let G : Sheaf Scheme.zariskiTopology.{0} Type := ⟨F, (isSheaf_iff_isSheaf_of_type _ _).2 hF⟩
  let f : ∀ i, yoneda.obj (T i) ⟶ G.1 := fun i => yonedaEquiv.symm (y i)
  have hp : ∀ i (Z : Scheme.{0}) (c : Z ⟶ T i), p.app _ (F.map c.op (y i)) = c ≫ π i ≫ (W i).ι := by
    intro i Z c
    rw [← hπ]
    exact ConcreteCategory.congr_hom (p.naturality c.op) (y i)
  have hf : ∀ i, IsOpenImmersion.presheaf (f i) := by
    intro i
    have : IsPullback (f i) (yoneda.map (π i)) p (yoneda.map (W i).ι) := by
      apply IsPullback.of_forall_isPullback_app
      rintro ⟨Z⟩
      rw [Types.isPullback_iff]
      refine ⟨?_, ?_, ?_⟩
      · ext c
        exact (hp i Z c).trans (Category.assoc _ _ _).symm
      · rintro c c' ⟨h1, -⟩
        exact (h i Z (F.map (Quiver.Hom.op c) (y i)) (c ≫ π i)
          ((hp i Z c).trans (Category.assoc _ _ _).symm)).unique rfl h1.symm
      · intro x b hb
        obtain ⟨c, hc, -⟩ := h i Z x b hb
        refine ⟨c, hc, ?_⟩
        change c ≫ π i = b
        rw [← cancel_mono (W i).ι, Category.assoc, ← hp, hc]
        exact hb
    exact (MorphismProperty.relative_isStableUnderBaseChange @IsOpenImmersion).of_isPullback this.flip
      (MorphismProperty.relative_map (inferInstanceAs (IsOpenImmersion (W i).ι)))
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
    constructor
    intro Z x
    let q : Z ⟶ X := p.app _ x
    let 𝒰 := Z.openCoverOfIsOpenCover (fun i => q ⁻¹ᵁ W i) (by
      rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hW]; rfl)
    refine GrothendieckTopology.superset_covering _ ?_ 𝒰.mem_grothendieckTopology
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    obtain ⟨c, hc, -⟩ := h i _ (F.map (q ⁻¹ᵁ W i).ι.op x) (q ∣_ W i) (by
      rw [morphismRestrict_ι]
      exact ConcreteCategory.congr_hom (p.naturality (q ⁻¹ᵁ W i).ι.op) x)
    refine ⟨(Sigma.ι (fun i => yoneda.obj (T i)) i).app _ c, ?_⟩
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (Sigma.ι_desc f i) _) c).trans hc
  exact Scheme.LocalRepresentability.isRepresentable hf

end GlobalTheory.GenTorsor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscProperties
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem intg_nMul_for_point {K : Type} [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  induction n with
  | zero =>
    rw [nMul_zero]
    exact GlobalTheory.BddAlg.intg_zero
  | succ n ih =>
    rw [nMul_succ]
    have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1
    refine GlobalTheory.BddAlg.Le.subst (c := 1) (fun j => ?_) (fun j => ?_) hF
    · fin_cases j
      · exact ih
      · exact hX
    · fin_cases j
      · exact nMul_constantCoeff F n
      · exact PowerSeries.constantCoeff_X

private lemma ev1_zero {K : Type} [NormedField K] (y : K) : ev1 (0 : PowerSeries K) y = 0 := by
  simp [ev1]

theorem nMul_point : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (F : FormalGroup K), Intg F.toPowerSeries → (∀ n, Intg (nMul F n)) ∧ ∀ x : K, ‖x‖ < 1 → ev1 (nMul F 0) x = 0 ∧ ev1 (nMul F 1) x = x ∧ (∀ j, ‖ev1 (nMul F j) x‖ ≤ ‖x‖ ∧ (‖(j : K)‖ = 1 → ‖ev1 (nMul F j) x‖ = ‖x‖)) ∧ (∀ i j, ev F.toPowerSeries ![ev1 (nMul F i) x, ev1 (nMul F j) x] = ev1 (nMul F (i + j)) x) ∧ (∀ i j, ev1 (nMul F i) (ev1 (nMul F j) x) = ev1 (nMul F (i * j)) x) ∧ (∀ y : K, ‖y‖ < 1 → ev F.toPowerSeries ![0, y] = y ∧ ev F.toPowerSeries ![y, 0] = y) := by
  intro K _ _ _ F hF
  have hI : ∀ n, Intg (nMul F n) := intg_nMul_for_point F hF
  have hB : Bdd F.toPowerSeries := GlobalTheory.BddAlg.bdd_of_intg hF
  have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1

  have hleft : MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_succ F 0
    rw [nMul_zero, nMul_one] at h
    exact h.symm
  have hright : MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_add F 1 0
    rw [nMul_zero, nMul_one] at h
    simpa using h
  refine ⟨hI, fun x hx => ?_⟩
  obtain ⟨-, -, -, hevX, -, -, hnorm, hsub, hpair, -, -⟩ := _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  refine ⟨by rw [nMul_zero]; exact ev1_zero x, by rw [nMul_one]; exact hevX, fun j => ?_,
    fun i j => ?_, fun i j => ?_, fun y hy => ?_⟩
  · obtain ⟨-, h1, h2⟩ := hnorm (nMul F j) (hI j)
    have h0 : PowerSeries.coeff 0 (nMul F j) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact nMul_constantCoeff F j
    rw [h0, sub_zero] at h1 h2
    rw [nMul_coeff_one] at h2
    refine ⟨h1, fun hj => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using h1
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hsq : ‖x‖ ^ 2 < ‖x‖ := by nlinarith
      have hjx : ‖(j : K) * x‖ = ‖x‖ := by rw [norm_mul, hj, one_mul]
      set v := ev1 (nMul F j) x
      have hlt : ‖v - (j : K) * x‖ < ‖(j : K) * x‖ := by rw [hjx]; exact lt_of_le_of_lt h2 hsq
      have hdecomp : v = (j : K) * x + (v - (j : K) * x) := by ring
      rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne',
        max_eq_left hlt.le, hjx]
  · rw [← hpair F.toPowerSeries (nMul F i) (nMul F j) hB (hI i) (hI j)
      (nMul_constantCoeff F i) (nMul_constantCoeff F j), nMul_add]
  · rw [← hsub (nMul F i) (nMul F j) (hI j) (nMul_constantCoeff F j)
      (GlobalTheory.BddAlg.bdd_of_intg (hI i)), nMul_subst_nMul]
  · obtain ⟨-, -, -, hevXy, -, -, -, -, hpairy, -, -⟩ := _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K y hy
    have hz : Intg (0 : PowerSeries K) := GlobalTheory.BddAlg.intg_zero
    have hc0 : PowerSeries.constantCoeff (0 : PowerSeries K) = 0 := by simp
    have hcX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
    constructor
    · have h := hpairy F.toPowerSeries 0 PowerSeries.X hB hz hX hc0 hcX
      rw [hleft, hevXy, ev1_zero] at h
      exact h.symm
    · have h := hpairy F.toPowerSeries PowerSeries.X 0 hB hX hz hcX hc0
      rw [hright, hevXy, ev1_zero] at h
      exact h.symm

end GlobalTheory.ConvSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscPropertiesStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (F : FormalGroup K), Intg F.toPowerSeries → (∀ n, Intg (nMul F n)) ∧ ∀ x : K, ‖x‖ < 1 → ev1 (nMul F 0) x = 0 ∧ ev1 (nMul F 1) x = x ∧ (∀ j, ‖ev1 (nMul F j) x‖ ≤ ‖x‖ ∧ (‖(j : K)‖ = 1 → ‖ev1 (nMul F j) x‖ = ‖x‖)) ∧ (∀ i j, ev F.toPowerSeries ![ev1 (nMul F i) x, ev1 (nMul F j) x] = ev1 (nMul F (i + j)) x) ∧ (∀ i j, ev1 (nMul F i) (ev1 (nMul F j) x) = ev1 (nMul F (i * j)) x) ∧ (∀ y : K, ‖y‖ < 1 → ev F.toPowerSeries ![0, y] = y ∧ ev F.toPowerSeries ![y, 0] = y) := by
  first | exact @GlobalTheory.ConvSer.nMul_point | exact GlobalTheory.ConvSer.nMul_point | (intros; apply GlobalTheory.ConvSer.nMul_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RingHomPointBijective
open PowerSeries GlobalTheory.MomOne WeierstrassCurve WeierstrassCurve.Affine
open scoped ComplexConjugate BigOperators Topology
open Classical

noncomputable section

namespace GlobalTheory.MomOne

def ringHomPointFun {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => 0
  | .some x y hP => .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr hP)

def ringHomPoint {k k' : Type*} [Field k] [Field k'] (f : k →+* k') (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (W.map f).toAffine.Point :=
  AddMonoidHom.mk' (ringHomPointFun f W) <| by
    refine GlobalTheory.map_add_of_triples _ rfl ?_ ?_
    · rintro (_ | ⟨x, y, hP⟩)
      · rfl
      · simp only [Point.neg_some, ringHomPointFun, Point.some.injEq, true_and, negY,
          map_a₁, map_a₃, map_sub, map_neg, map_mul]
    · rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) (_ | ⟨x₃, y₃, h₃⟩) hP hQ hR h
      any_goals first | exact absurd rfl hP | exact absurd rfl hQ | exact absurd rfl hR
      obtain ⟨l, n, e₁, e₂, e₃, s₁, s₂, -⟩ := GlobalTheory.exists_line_of_add_add_eq_zero h
      refine GlobalTheory.add_add_eq_zero_of_line _ _ _ (f l) (f n) ?_ ?_ ?_ ?_ ?_
      · rw [e₁]; simp
      · rw [e₂]; simp
      · rw [e₃]; simp
      · simpa using congrArg f s₁
      · simpa [map_ofNat] using congrArg f s₂

private lemma ringHomPoint_some {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W (.some x y h) =
      .some (f x) (f y) ((W.toAffine.map_nonsingular f.injective x y).mpr h) := rfl

private lemma ringHomPoint_surjective_of_ringEquiv {k k' : Type*} [Field k] [Field k']
    (e : k ≃+* k') (W : WeierstrassCurve k) :
    Function.Surjective (_root_.GlobalTheory.MomOne.ringHomPoint (e : k →+* k') W) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, map_zero _⟩
  · have h' : W.toAffine.Nonsingular (e.symm x) (e.symm y) := by
      rw [← WeierstrassCurve.Affine.map_nonsingular W.toAffine (f := (e : k →+* k')) e.injective]
      simpa using h
    refine ⟨.some _ _ h', ?_⟩
    rw [ringHomPoint_some]
    simp

private lemma ringHomPoint_eq_zero_iff {k k' : Type*} [Field k] [Field k']
    (f : k →+* k') (W : WeierstrassCurve k) (P : W.toAffine.Point) :
    _root_.GlobalTheory.MomOne.ringHomPoint f W P = 0 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [ringHomPoint_some]
    simp

theorem _root_.GlobalTheory.MomOne.Mdl.exists_pointHom (q : ℕ) [Fact q.Prime]
    (M : _root_.GlobalTheory.MomOne.Mdl q) (hM : M.Ok) :
    ∃ φ : ℂ →+ M.W.toAffine.Point, Function.Surjective φ ∧
      (∀ z, φ z = 0 ↔ z ∈ M.L.lattice) ∧
      ∀ z ∉ M.L.lattice, ∃ h,
        φ z = WeierstrassCurve.Affine.Point.some (M.ι (M.x z))
          (M.ι (M.y z)) h := by
  obtain ⟨hc, -, -, -, -, -, -, h₄, h₆⟩ := hM
  have hιc : M.ι M.c ≠ 0 :=
    (map_ne_zero M.ι).mpr hc
  obtain ⟨C, hCu, hCr, hCs, hCt⟩ : ∃ C : VariableChange ℂ_[q],
      (C.u : ℂ_[q]) = (M.ι M.c)⁻¹ ∧
      C.r = -(M.W.b₂ / 12) ∧ C.s = -(M.W.a₁ / 2) ∧
      C.t = M.W.a₁ * M.W.b₂ / 24 -
        M.W.a₃ / 2 :=
    ⟨⟨Units.mk0 _ (inv_ne_zero hιc), _, _, _⟩, rfl, rfl, rfl, rfl⟩
  have hCu' : ((C.u⁻¹ : ℂ_[q]ˣ) : ℂ_[q]) = M.ι M.c := by
    rw [Units.val_inv_eq_inv_val, hCu, inv_inv]
  have hE : (_root_.GlobalTheory.latticeCurve M.L).a₁ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₂ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₃ = 0 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₄ = -M.L.g₂ / 4 ∧
      (_root_.GlobalTheory.latticeCurve M.L).a₆ = -M.L.g₃ / 4 := by
    simp [_root_.GlobalTheory.latticeCurve]
  obtain ⟨hE₁, hE₂, hE₃, hE₄, hE₆⟩ := hE
  have hg₂ : M.ι M.L.g₂ =
      M.W.c₄ / 12 * M.ι M.c ^ 4 := by
    rw [h₄, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 4 hιc)]
  have hg₃ : M.ι M.L.g₃ =
      M.W.c₆ / 216 * M.ι M.c ^ 6 := by
    rw [h₆, map_div₀, map_pow, div_mul_cancel₀ _ (pow_ne_zero 6 hιc)]
  have hC : C • M.W =
      (_root_.GlobalTheory.latticeCurve M.L).map (M.ι : ℂ →+* ℂ_[q]) := by
    ext
    · rw [variableChange_a₁, hCu', hCs, map_a₁, hE₁]; simp only [map_zero]; ring
    · rw [variableChange_a₂, hCu', hCs, hCr, map_a₂, hE₂]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₃, hCu', hCt, hCr, map_a₃, hE₃]
      simp only [map_zero, WeierstrassCurve.b₂]; ring
    · rw [variableChange_a₄, hCu', hCs, hCt, hCr, map_a₄, hE₄]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₂, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    · rw [variableChange_a₆, hCu', hCt, hCr, map_a₆, hE₆]
      simp only [RingHom.coe_coe, map_div₀, map_neg, map_ofNat, hg₃, WeierstrassCurve.c₆,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      ring
  let φ : ℂ →+ M.W.toAffine.Point :=
    (_root_.GlobalTheory.variableChangePoint C hC).comp
      ((_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)).comp
        (_root_.GlobalTheory.latticePointHom M.L))
  have hφ : ∀ z, φ z = _root_.GlobalTheory.variableChangePoint C hC
      (_root_.GlobalTheory.MomOne.ringHomPoint (M.ι : ℂ →+* ℂ_[q])
        (_root_.GlobalTheory.latticeCurve M.L)
        (_root_.GlobalTheory.latticePoint M.L z)) := by
    intro z
    simp only [φ, AddMonoidHom.coe_comp, Function.comp_apply, _root_.GlobalTheory.latticePointHom_apply]
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro P
    obtain ⟨P₁, rfl⟩ := (_root_.GlobalTheory.variableChangePoint_bijective C hC).2 P
    obtain ⟨P₂, rfl⟩ := ringHomPoint_surjective_of_ringEquiv M.ι _ P₁
    obtain ⟨z, rfl⟩ := _root_.GlobalTheory.latticePoint_surjective M.L P₂
    exact ⟨z, hφ z⟩
  · intro z
    rw [hφ, map_eq_zero_iff _ (_root_.GlobalTheory.variableChangePoint_bijective C hC).1,
      ringHomPoint_eq_zero_iff, _root_.GlobalTheory.latticePoint_eq_zero_iff]
  · intro z hz
    have key : ∀ {a b a' b' : ℂ_[q]} (h : M.W.toAffine.Nonsingular a b),
        a = a' → b = b' → ∃ h', (Point.some a b h : M.W.toAffine.Point) =
          Point.some a' b' h' := by
      rintro a b a' b' h rfl rfl
      exact ⟨h, rfl⟩
    have hx : (C.u : ℂ_[q]) ^ 2 * M.ι (M.L.weierstrassP z) + C.r =
        M.ι (M.x z) := by
      show _ = M.ι (M.L.weierstrassP z / M.c ^ 2 -
        M.ι.symm (M.W.b₂ / 12))
      rw [map_sub, map_div₀, map_pow, RingEquiv.apply_symm_apply, hCu, hCr]
      field_simp
      ring
    have hy : (C.u : ℂ_[q]) ^ 3 * M.ι (M.L.derivWeierstrassP z / 2) +
        (C.u : ℂ_[q]) ^ 2 * C.s * M.ι (M.L.weierstrassP z) + C.t =
        M.ι (M.y z) := by
      show _ = M.ι ((M.L.derivWeierstrassP z /
        M.c ^ 3 - M.ι.symm M.W.a₁ *
        M.x z - M.ι.symm M.W.a₃) / 2)
      simp only [map_div₀, map_sub, map_mul, map_pow, RingEquiv.apply_symm_apply, map_ofNat]
      rw [← hx, hCu, hCr, hCs, hCt]
      field_simp
      ring
    rw [hφ, _root_.GlobalTheory.latticePoint_of_notMem M.L hz,
      ringHomPoint_some, _root_.GlobalTheory.variableChangePoint_some]
    exact key _ hx hy

end GlobalTheory.MomOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGroupedOfSublist
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpSNegMulExpS
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.NablaExpConj

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

section Lift

variable (k : Type) [CommRing k]

end Lift

variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem Dof_expS (F : Fin d → PS k 2 d) (u : Fin d → k) {g : PS k 1 d}
    (hg : constantCoeff g = 0) : Dof F u (FB.expS k g) = FB.expS k g * Dof F u g := by
  have e : ∀ i, pderiv (R := k) i (FB.expS k g) = FB.expS k g * pderiv (R := k) i g :=
    FormalCalc.pderiv_formalExp hg
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e]
  ring

end GlobalTheory.NablaExpConj
end
end

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ExpCong

section Abstract

variable {A k ι : Type} [CommRing A] [CommRing k] (D : ι → A → A) (c : A →+* k)

def along (w : List ι) (f : A) : A := w.foldl (fun g a => D a g) f

theorem along_nil (f : A) : along D [] f = f := rfl

theorem along_cons (a : ι) (w : List ι) (f : A) : along D (a :: w) f = along D w (D a f) := rfl

theorem along_add (hadd : ∀ a f g, D a (f + g) = D a f + D a g) (w : List ι) (f g : A) :
    along D w (f + g) = along D w f + along D w g := by
  induction w generalizing f g with
  | nil => rfl
  | cons a w ih => rw [along_cons, along_cons, along_cons, hadd, ih]

theorem along_mul_mem (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (w : List ι) (f g : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hg : ∀ v, v.Sublist w → c (along D v g) ∈ J) :
    c (along D w (f * g)) ∈ J := by
  induction w generalizing f g with
  | nil =>
    rw [along_nil, map_mul]
    exact hSJ _ (hf [] (List.Sublist.refl _)) _ (hg [] (List.Sublist.refl _))
  | cons a w ih =>
    rw [along_cons, hmul, along_add D hadd, map_add (f := _), mul_comm g]
    refine J.add_mem (ih _ _ ?_ ?_) (ih _ _ ?_ ?_)
    · exact fun v hv => hf v (hv.cons a)
    · exact fun v hv => hg (a :: v) (hv.cons_cons a)
    · exact fun v hv => hf (a :: v) (hv.cons_cons a)
    · exact fun v hv => hg v (hv.cons a)

theorem along_mul_exp (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (hJS : ∀ j ∈ J, j ∈ S) (E φ : A) (hE : ∀ a, D a E = E * D a φ)
    (hE1 : c E = 1) (w : List ι) (f : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hφ : ∀ v, v.Sublist w → c (along D v φ) ∈ J) :
    c (along D w (f * E)) - c (along D w f) ∈ J := by
  induction w generalizing f with
  | nil =>
    rw [along_nil, along_nil, map_mul, hE1, mul_one, sub_self]
    exact J.zero_mem
  | cons a w ih =>
    have hφ' : ∀ v, v.Sublist w → c (along D v φ) ∈ J := fun v hv => hφ v (hv.cons a)
    have h1 : ∀ v, v.Sublist w → c (along D v (f * D a φ)) ∈ J := fun v hv =>
      along_mul_mem D c hadd hmul S J hSJ v f (D a φ)
        (fun v' hv' => hf v' ((hv'.trans hv).cons a))
        (fun v' hv' => hφ (a :: v') ((hv'.trans hv).cons_cons a))
    have h2 := ih (f * D a φ) (fun v hv => hJS _ (h1 v hv)) hφ'
    have h3 := ih (D a f) (fun v hv => hf (a :: v) (hv.cons_cons a)) hφ'
    have h4 := J.add_mem (J.add_mem h2 (h1 w (List.Sublist.refl _))) h3
    rw [along_cons, along_cons, hmul, hE, along_add D hadd, map_add (f := _),
      show f * (E * D a φ) = f * D a φ * E by ring, mul_comm E]
    convert h4 using 1
    ring

def grouped (L : List ι) (m : ι → ℕ) : List ι := L.flatMap fun l => List.replicate (m l) l

theorem grouped_cons (a : ι) (L : List ι) (m : ι → ℕ) :
    grouped (a :: L) m = List.replicate (m a) a ++ grouped L m := by
  simp [grouped]

theorem exists_grouped_of_sublist {L : List ι} (hL : L.Nodup) (m : ι → ℕ) (v : List ι)
    (hv : v.Sublist (grouped L m)) : ∃ m' : ι → ℕ, v = grouped L m' := by
  classical
  induction L generalizing v with
  | nil => exact ⟨m, by simpa [grouped] using hv⟩
  | cons a L ih =>
    rw [grouped_cons, List.sublist_append_iff] at hv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv
    obtain ⟨n, -, rfl⟩ := List.sublist_replicate_iff.1 h₁
    rw [List.nodup_cons] at hL
    obtain ⟨m', rfl⟩ := ih hL.2 v₂ h₂
    refine ⟨Function.update m' a n, ?_⟩
    rw [grouped_cons, Function.update_self]
    congr 1
    unfold grouped
    refine List.flatMap_congr fun l hl => ?_
    rw [Function.update_of_ne]
    rintro rfl
    exact hL.1 hl

theorem foldr_replicate (a : ι) (n : ℕ) (g : A) :
    (List.replicate n a).foldr (fun a g => D a g) g = (D a)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

theorem along_reverse_grouped (L : List ι) (m : ι → ℕ) (f : A) :
    along D (grouped L m).reverse f = L.foldr (fun l g => (D l)^[m l] g) f := by
  unfold along
  rw [List.foldl_reverse]
  induction L with
  | nil => rfl
  | cons a L ih => rw [grouped_cons, List.foldr_append, ih, foldr_replicate, List.foldr_cons]

end Abstract

variable {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)

theorem dmonOf_eq_along (m : ι →₀ ℕ) (f : PS k 1 d) :
    DmonOf F u m f =
      along (fun l => Dof F (u l)) (grouped (Finset.univ : Finset ι).toList m).reverse f :=
  (along_reverse_grouped _ _ _ _).symm

theorem exists_along_eq_dmonOf (m : ι →₀ ℕ) (v : List ι)
    (hv : v.Sublist (grouped (Finset.univ : Finset ι).toList m).reverse) :
    ∃ m' : ι →₀ ℕ, ∀ f : PS k 1 d, along (fun l => Dof F (u l)) v f = DmonOf F u m' f := by
  obtain ⟨m', hm'⟩ := exists_grouped_of_sublist (Finset.nodup_toList _) m v.reverse
    (by simpa using hv.reverse)
  refine ⟨Finsupp.equivFunOnFinite.symm m', fun f => ?_⟩
  rw [dmonOf_eq_along, Finsupp.coe_equivFunOnFinite_symm, ← hm', List.reverse_reverse]

end GlobalTheory.ExpCong

namespace GlobalTheory

theorem dmonOf_mul_expS_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (φ : PS k 1 d), constantCoeff φ = 0 → (∀ m : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m φ) = algebraMap R k r) → ∀ (f : PS R 1 d) (m : ι →₀ ℕ), ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m (FB.toK k f * FB.expS k φ)) = algebraMap R k (constantCoeff (DmonOf F u m f) + r) := by
  intro R _ d k _ _ _ F I ι _ u φ hφ0 hφ f m
  set F' : Fin d → PS k 2 d := fun i => MvPowerSeries.map (algebraMap R k) (F i) with hF'
  set u' : ι → Fin d → k := fun l i => algebraMap R k (u l i) with hu'
  have hmap : ∀ m' : ι →₀ ℕ, constantCoeff (DmonOf F' u' m' (FB.toK k f)) =
      algebraMap R k (constantCoeff (DmonOf F u m' f)) := fun m' => by
    rw [hF', hu', FB.toK, ← map_dmonOf, constantCoeff_map]
  have key := ExpCong.along_mul_exp (fun l => Dof F' (u' l)) (constantCoeff : PS k 1 d →+* k)
    (fun a => GE.dof_add F' (u' a)) (fun a => GE.dof_mul F' (u' a)) (Set.range (algebraMap R k))
    (I.toAddSubgroup.map (algebraMap R k).toAddMonoidHom)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨j, hj, rfl⟩
      exact ⟨s * j, I.mul_mem_left s hj, map_mul (algebraMap R k) s j⟩)
    (by
      rintro _ ⟨j, -, rfl⟩
      exact ⟨j, rfl⟩)
    (FB.expS k φ) φ (fun a => NablaExpConj.Dof_expS k F' (u' a) hφ0) (WickVanishing.constantCoeff_exp hφ0)
    (ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (FB.toK k f)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      exact ⟨_, by rw [hm', hmap]⟩)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      obtain ⟨r, hr, e⟩ := hφ m'
      exact ⟨r, hr, by rw [hm', e]; rfl⟩)
  rw [← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along, hmap] at key
  obtain ⟨r, hr, e⟩ := key
  refine ⟨r, hr, ?_⟩
  have e' : algebraMap R k r = _ := e
  rw [map_add (f := _), e']
  ring

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinPartEigenMemRange
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem bilinPart_eigen_mem_range : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (a : O) (u u' : Fin d → R) (α α' : R), (dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k α • (fun i => algebraMap R k (u i)) → (dAct k B (star a)).mulVec (fun i => algebraMap R k (u' i)) = algebraMap R k α' • (fun i => algebraMap R k (u' i)) → IsUnit (α - α') → dotProduct (fun i => algebraMap R k (u i)) ((bilinPart k h).mulVec (fun i => algebraMap R k (u' i))) ∈ (algebraMap R k).range := by
  intro R _ d O _ _ k _ _ _ B h hc a u u' α α' hu hu' hα
  choose M hM using fun i j => WickVanishing.M_int B h hc a i j
  set v : Fin d → k := fun i => algebraMap R k (u i) with hv
  set v' : Fin d → k := fun i => algebraMap R k (u' i) with hv'
  have hS : sg1 k h = -(bilinPart k h).transpose := by
    ext i j
    simp only [WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, Matrix.neg_apply, Matrix.transpose_apply, bilinPart]
  have e1 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      -(algebraMap R k (α - α') * dotProduct v ((bilinPart k h).mulVec v')) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, dotProduct_sub,
      Matrix.dotProduct_mulVec v' (dAct k B (star a)).transpose, Matrix.vecMul_transpose, hu', Matrix.mulVec_smul,
      dotProduct_smul, smul_dotProduct, hS, Matrix.neg_mulVec, dotProduct_neg,
      Matrix.dotProduct_mulVec v', Matrix.vecMul_transpose, dotProduct_comm _ v, map_sub]
    simp only [smul_eq_mul]
    ring
  have e2 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      algebraMap R k (∑ i, u' i * ∑ j, M i j * u j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hM, dotProduct, Matrix.mulVec, hv, hv']
  obtain ⟨w, hw⟩ := hα.exists_left_inv
  refine ⟨-(w * ∑ i, u' i * ∑ j, M i j * u j), ?_⟩
  rw [map_neg, map_mul, ← e2, e1, mul_neg, neg_neg, ← mul_assoc, ← map_mul, hw, map_one, one_mul]

end GlobalTheory
end
