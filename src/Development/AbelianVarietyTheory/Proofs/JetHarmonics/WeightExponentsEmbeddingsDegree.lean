module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

noncomputable section

namespace GlobalTheory.WeightExponents

theorem tauEmb_injective (D : D7) : Function.Injective (DV.tauEmb D) := by
  intro s t h
  exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_eq {E : Type} [Field E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ = ComplexEmbedding.conjugate τ := by
  ext x; simp

theorem not_inPsi_conj {D : D7} {Q : Par D} (hp : Q.PinHost) (t : D.what₂.Tau) :
    ¬ InPsi Q.H (ComplexEmbedding.conjugate (DV.tauEmb D t)) := fun h =>
  ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both Q.H _ ⟨hp.2.2.2 t, h⟩

theorem tauEmb_ne_conj {D : D7} {Q : Par D} (hp : Q.PinHost) (s t : D.what₂.Tau) :
    DV.tauEmb D s ≠ ComplexEmbedding.conjugate (DV.tauEmb D t) := fun h =>
  not_inPsi_conj hp t (h ▸ (hp.2.2.2 s : InPsi Q.H (DV.tauEmb D s)))

open Classical in
theorem wtA_apply {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (τ : D.host.E →+* ℂ) (i : ℕ) :
    wtA w (τ, i) = ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ext0 (w.aP t) i else 0) +
      if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then ext0 (w.aM t) i else 0) := by
  unfold wtA
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← conjEmb_eq]
  rfl

theorem wtA_tauEmb {D : D7} {Q : Par D} (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  rw [wtA_apply, Finset.sum_eq_single t]
  · rw [if_pos rfl, if_neg (tauEmb_ne_conj hp t t), add_zero]
  · intro s _ hs
    rw [if_neg fun h => hs (tauEmb_injective D h).symm, if_neg (tauEmb_ne_conj hp t s), add_zero]
  · intro h; exact absurd (Finset.mem_univ t) h

theorem wtA_conj {D : D7} {Q : Par D} (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (ComplexEmbedding.conjugate (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  rw [wtA_apply, Finset.sum_eq_single t]
  · rw [if_pos rfl, if_neg (tauEmb_ne_conj hp t t).symm, zero_add]
  · intro s _ hs
    rw [if_neg (tauEmb_ne_conj hp s t).symm, if_neg fun h =>
      hs (tauEmb_injective D ((ComplexEmbedding.involutive_conjugate _).injective h)).symm, add_zero]
  · intro h; exact absurd (Finset.mem_univ t) h

theorem DF_wtA {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    Formalism.L2.Pj.DF (Q.Dw j) (wtA w) = WeightAlgebra.DF w := by
  classical
  unfold Formalism.L2.Pj.DF WeightAlgebra.DF WeightAlgebra.degP
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then
          ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [wtA_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  have hs : ∀ {p m : ℕ} (f : Fin p → ℕ), m = p → ∑ i : Fin m, ext0 f i = ∑ i, f i := by
    rintro p m f rfl
    exact Finset.sum_congr rfl fun i _ => by simp [ext0, i.isLt]
  rw [Finset.sum_congr rfl fun τ _ => hsw τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have ht := hQ.1.2.2.2 t
  have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 := not_inPsi_conj hQ.1 t
  rw [hs _ (by rw [Datum.mult, if_pos ht, hp]), hs _ (by rw [Datum.mult, if_neg hc, hq])]

theorem weight_exponents : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, DF (Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ Function.Injective (DV.tauEmb D) ∧ (∀ τ, InPsi Q.H τ ↔ ∃ t, τ = DV.tauEmb D t) ∧ (∀ τ, ¬ InPsi Q.H τ ↔ ∃ t, τ = ComplexEmbedding.conjugate (DV.tauEmb D t)) ∧ ∀ t i, wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i ∧ wtA w (ComplexEmbedding.conjugate (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  intro D Q hQ j hj w
  have hΨ : ∀ τ, InPsi Q.H τ ↔ ∃ t, τ = DV.tauEmb D t := fun τ =>
    ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q hQ.1 τ, by rintro ⟨t, rfl⟩; exact hQ.1.2.2.2 t⟩
  refine ⟨DF_wtA hQ hj w, tauEmb_injective D, hΨ, fun τ => ⟨fun h => ?_, ?_⟩,
    fun t i => ⟨wtA_tauEmb hQ.1 w t i, wtA_conj hQ.1 w t i⟩⟩
  · obtain ⟨t, ht⟩ := (hΨ _).1 ((ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or Q.H τ).resolve_left h)
    exact ⟨t, by rw [← ht, ComplexEmbedding.involutive_conjugate _ τ]⟩
  · rintro ⟨t, rfl⟩
    exact not_inPsi_conj hQ.1 t

end GlobalTheory.WeightExponents
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegreeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightExponents_embeddings_degree : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, DF (Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ Function.Injective (DV.tauEmb D) ∧ (∀ τ, InPsi Q.H τ ↔ ∃ t, τ = DV.tauEmb D t) ∧ (∀ τ, ¬ InPsi Q.H τ ↔ ∃ t, τ = ComplexEmbedding.conjugate (DV.tauEmb D t)) ∧ ∀ t i, wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i ∧ wtA w (ComplexEmbedding.conjugate (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  first | exact @GlobalTheory.WeightExponents.weight_exponents | exact GlobalTheory.WeightExponents.weight_exponents | (intros; apply GlobalTheory.WeightExponents.weight_exponents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.FormalSeriesBounds
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PairKernel

open GlobalTheory.KerPow

theorem mulA_finite_flat_surjective (S : Scheme.{0}) (P : PolAV S) (n : ℕ) (hn : 1 ≤ n) :
    IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left := by
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hf : IsFinite (mulA P.A n).left := GlobalTheory.MulFinite.isFinite_mulA
    (GlobalTheory.MulPull.mulPull_of_cube_of_symm GlobalTheory.AbLaw.CubeAssembly.cube_gen
      (GlobalTheory.exists_gen_negLB GlobalTheory.laws_without_cohomology.1)).1 GlobalTheory.laws_without_cohomology.2.2.1 gi S P n hn
  have hc := P.isAb.comm
  have hsm := P.isAb.smooth
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA P.A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map (mulA P.A n)).left ∧
        Surjective ((Over.pullback t).map (mulA P.A n)).left := fun K _ _ t =>
    GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd gi K _ (TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hf)
  exact ⟨hf, GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance
    inferInstance hf fun K _ _ t => (hgeo K t).1,
    GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2⟩

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

end Alg

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

end GlobalTheory.PairKernel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.CuspFamilyCompare

section Pairing

variable {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

end Pairing

theorem exp_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ}
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (Pi.single i 1) (u i)) : e = e' := by
  have h0 : e 0 = e' 0 := (HolHom.map_zero_eq_one he).trans (HolHom.map_zero_eq_one he').symm
  refine HolHom.eq_of_fderiv_eq he he' hol hol' fun U hU f => ContinuousLinearMap.coe_injective ((Pi.basisFun ℂ _).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact (((HolHom.isDerivAt0_iff _ _ _).1 (hd i)).2 U hU f).symm.trans
    (((HolHom.isDerivAt0_iff _ _ _).1 (hd' i)).2 U (h0 ▸ hU :) f)

section Tangent

open GlobalTheory.ArcQ GlobalTheory.TorusTangent ReciprocityTheory.ChartRestriction.G.DVR

variable {K : Type} [Field K] {D₀ : Out.DegPre K}

variable [NumberField K]

end Tangent

section Exponents

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Type} [AddCommGroup X]
  [Module (𝓞 E) X] {g : ℕ} {ξ : Module.Dual ℤ X} {be : LinearMap.BilinForm ℤ X}

end Exponents

section Fibre

variable {K : Type} [Field K]

variable [NumberField K] {D₀ : Out.DegPre K}

end Fibre

variable {D : D7} {T : Core D} {j : ℕ}

section Family

variable {n' : ℕ} {La c₁ : ℝ}


end Family

section Comparison₂

variable {σ : T.Q.c.F →+* ℂ} {k : (T.U j σ).Comp} {x : ((T.U j σ).X k).dom} {ξ : Fin D.R.r → D.host.E}
  {ν : ((T.U j σ).X k).Ψ → ℝ} {lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E}


end Comparison₂

section Claims

variable {n' : ℕ} {La c₁ : ℝ} {Wp : ValuationSubring ℂ} {Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype}
  {σ : T.Q.c.F →+* ℂ} {k : (T.U j σ).Comp} {x : ((T.U j σ).X k).dom} {ξ : Fin D.R.r → D.host.E}
  {ν : ((T.U j σ).X k).Ψ → ℝ} {lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E}


end Claims

end GlobalTheory.CuspFamilyCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstRowsBoundAndSizesBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstRowsBoundAndSizesBounds
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FirstRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem sum_ite_le {ι β : Type} [Fintype ι] (φ : ι → β) (hφ : Function.Injective φ) (y : β)
    [∀ t, Decidable (y = φ t)] (g : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (hg : ∀ t, g t ≤ B) :
    (∑ t, if y = φ t then g t else 0) ≤ B := by
  classical
  by_cases h : ∃ t, y = φ t
  · obtain ⟨t, rfl⟩ := h
    rw [Finset.sum_eq_single t]
    · simpa using hg t
    · intro t' _ ht'
      rw [if_neg fun h => ht' (hφ h).symm]
    · simp
  · rw [Finset.sum_eq_zero fun t _ => if_neg fun h' => h ⟨t, h'⟩]
    exact hB

theorem tauEmb_injective (D : D7) : Function.Injective (DV.tauEmb D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conj_tauEmb_injective (D : D7) :
    Function.Injective fun t => ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t) := by
  intro s t h
  apply tauEmb_injective D
  ext x
  have := RingHom.congr_fun h x
  exact (starRingEnd ℂ).injective this

theorem mul_wtA_le {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (i : ℕ)
    (hP : ∀ t, T * (ext0 (w.aP t) i : ℝ) ≤ A) (hM : ∀ t, T * (ext0 (w.aM t) i : ℝ) ≤ B) (τ : D.host.E →+* ℂ) :
    T * wtA w (τ, i) ≤ A + B := by
  classical
  unfold wtA
  push_cast
  rw [Finset.mul_sum]
  simp only [mul_add, mul_ite, mul_zero]
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · convert sum_ite_le (DV.tauEmb D) (tauEmb_injective D) τ _ A hA hP
  · convert sum_ite_le _ (conj_tauEmb_injective D) τ _ B hB hM

theorem b'_pos (s : Scale) : 0 < s.b' := by
  unfold Scale.b' Scale.a Scale.X' Scale.b
  have : 0 < s.x := by linarith [s.one_lt_alt]
  positivity

theorem w''_le (s : Scale) (n : ℕ) (hn : 1 ≤ n) (hx : 3 ≤ s.x) : s.w'' n ≤ s.b' / 3 := by
  unfold Scale.w''
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left (b'_pos s).le (by norm_num) (by nlinarith)

theorem first_rows_and_sizes : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  (∀ τ : D.host.E →+* ℂ, (Tp.TO : ℝ) * wtA (lR Tp hK j) (τ, 0) ≤ 3 * L.sc.b) ∧ ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z ∧ (numOf D L).w j z ≤ 2 * L.sc.b := by
  intro D L Pm Tp hK j hj hx hkb
  obtain ⟨-, hsz⟩ := GlobalTheory.RunDepth.sizes_le_two_mul D L Pm hx hkb
  obtain ⟨hw, -, hnum⟩ := hsz j hj
  have hb' := b'_pos L.sc
  have hn : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hw3 := w''_le L.sc D.R.n hn hx
  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hbb : L.sc.b' ≤ L.sc.b := by nlinarith
  have hSc : L.Sc ≤ L.sc.b' / 3 := by nlinarith [Pm.kS_le, L.Sc_pos]
  have heta : L.etaSz ≤ L.sc.b' / 3 := by
    have h1 := Pm.teta
    have h2 := L.t_win.1
    have h3 := L.etaSz_pos
    have h0 : 0 ≤ L.sc.w'' D.R.n := by nlinarith [Pm.kS_le, L.Sc_pos]
    have h4 : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n := div_le_self h0 L.sc.one_lt_alt.le
    nlinarith
  have hScp := L.Sc_pos
  have hetap := L.etaSz_pos
  refine ⟨fun τ => ?_, fun z => ⟨?_, ?_⟩⟩
  · have := mul_wtA_le (lR Tp hK j) (Tp.TO : ℝ) (2 * L.sc.b + L.Sc) L.etaSz (by linarith) hetap.le 0 ?_ ?_ τ
    · linarith
    · intro t
      unfold ext0
      split_ifs with h
      · have h1 := (GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).1 ⟨0, h⟩
        have h2 := (GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t).1 ⟨0, h⟩ (by show 0 < D.R.k - 1; omega)
        have h3 : (Tp.TO : ℝ) * ((lR Tp hK j).aP t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aP t ⟨0, h⟩ : ℝ) := by exact_mod_cast h1
        linarith [(hw t).2]
      · simp only [Nat.cast_zero, mul_zero]; linarith
    · intro t
      unfold ext0
      split_ifs with h
      · have h1 := (GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).2.1 ⟨0, h⟩
        have h2 := (GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t).2.2 ⟨0, h⟩
        have h3 : (Tp.TO : ℝ) * ((lR Tp hK j).aM t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aM t ⟨0, h⟩ : ℝ) := by exact_mod_cast h1
        linarith
      · simp only [Nat.cast_zero, mul_zero]; linarith
  · rw [hnum z]
    set τ := plOf D z
    by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · classical
      unfold Host.topPlaces at htop
      obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
      have h1 := (L.win_top j hj.1 hj.2 τ ⟨t, ht⟩ hte.symm).1
      have h2 := L.bT_ge ⟨t, ht⟩
      have h3 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb'.le (by linarith)
      linarith
    · by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
      · have h1 := (L.win_thick j hj.1 hj.2 τ hth).1
        linarith
      · exact (L.win_thin j hj.1 hj.2 τ ⟨(D.eTau τ).2, htop, hth⟩).1
  · rw [hnum z]
    exact (hw _).2

end GlobalTheory.FirstRows
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstRowsBoundAndSizesBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstRows_bound_and_sizes_bounds : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  (∀ τ : D.host.E →+* ℂ, (Tp.TO : ℝ) * wtA (lR Tp hK j) (τ, 0) ≤ 3 * L.sc.b) ∧ ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z ∧ (numOf D L).w j z ≤ 2 * L.sc.b := by
  first | exact @GlobalTheory.FirstRows.first_rows_and_sizes | exact GlobalTheory.FirstRows.first_rows_and_sizes | (intros; apply GlobalTheory.FirstRows.first_rows_and_sizes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBound
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBound
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem sum_fin_le_two_blocks {n K j : ℕ} (hn : n = K + j) (a : Fin n → ℝ) (A B : ℝ)
    (h1 : ∀ i, i.1 < K → a i ≤ A) (h2 : ∀ i, K ≤ i.1 → a i ≤ B) : ∑ i, a i ≤ K * A + j * B := by
  subst hn
  rw [Fin.sum_univ_add]
  have e1 : ∑ i : Fin K, a (Fin.castAdd j i) ≤ ∑ _i : Fin K, A :=
    Finset.sum_le_sum fun i _ => h1 _ (by simp)
  have e2 : ∑ i : Fin j, a (Fin.natAdd K i) ≤ ∑ _i : Fin j, B :=
    Finset.sum_le_sum fun i _ => h2 _ (by simp)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e1 e2
  linarith

theorem four_sq_lt_of_eighth {k b g : ℝ} (hk : 5 ≤ k) (hb : 1 ≤ b) (hg : (k * b) ^ 8 ≤ g) :
    4 * k ^ 2 * b < (g - 2) / 2 := by
  have h5 : 5 ≤ k * b := by nlinarith
  have h0 : k ^ 2 * b ≤ (k * b) ^ 2 := by
    have : 0 ≤ k ^ 2 * b * (b - 1) := by
      have : 0 ≤ b - 1 := by linarith
      have : 0 ≤ b := by linarith
      positivity
    nlinarith
  set y := k * b
  have h2 : 25 ≤ y ^ 2 := by nlinarith
  have h6 : 25 ≤ y ^ 6 := h2.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  have h8 : y ^ 8 = y ^ 6 * y ^ 2 := by ring
  nlinarith

theorem DF_kaR_le : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ j, InR D j → (WeightAlgebra.DF (kaR Tp hK j) : ℝ) ≤ (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz)) ∧ ∀ i, (WeightAlgebra.DF (kaR Tp hK j) : ℝ) < ((D.host.g i : ℝ) - 2) / 2 := by
  intro D L Pm Tp hK hx hkb j hj
  obtain ⟨hSe, hw⟩ := GlobalTheory.T.cloudSizes_between_zero_and_twice_b D L Pm hx hkb
  have hw := (hw j hj).1
  have hrow := GlobalTheory.T.kappaRows_entries_le_sizes D L Pm Tp hK j hj
  have hcard := (GlobalTheory.T.realPlaceLabel_bijective_card_eq_f D).2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hj1 := hj.1
  have hj2 := hj.2
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hmkR : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast hmk
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (D.R.f_le_k : D.R.f ≤ D.R.k)
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hb : 1 ≤ L.sc.b := by
    unfold Scale.b
    apply Real.one_le_exp
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hτ : ∀ τ : D.what₂.Tau, ((∑ i, ((kaR Tp hK j).aP τ i : ℝ)) + ∑ i, ((kaR Tp hK j).aM τ i : ℝ)) ≤
      (D.R.k : ℝ) * (2 * L.sc.b + (L.Sc + L.etaSz)) := by
    intro τ
    obtain ⟨r1, r2, r3⟩ := hrow τ
    have s1 := sum_fin_le_two_blocks (n := (D.R.sigW j).1) (K := D.R.k - 1) (j := j)
      (by show D.R.k + j - 1 = _; omega) (fun i => ((kaR Tp hK j).aP τ i : ℝ)) (2 * L.sc.b + L.Sc) L.etaSz
      (fun i hi => (r1 i hi).trans (by linarith [(hw τ).2])) r2
    have s2 := sum_fin_le_two_blocks (n := (D.R.sigW j).2) (K := 0) (j := D.R.m - j)
      (by show D.R.m - j = _; omega) (fun i => ((kaR Tp hK j).aM τ i : ℝ)) 0 L.etaSz
      (fun i hi => absurd hi (Nat.not_lt_zero _)) (fun i _ => r3 i)
    rw [Nat.cast_sub (by omega : 1 ≤ D.R.k)] at s1
    rw [Nat.cast_sub hj2] at s2
    have t1 : (D.R.m : ℝ) * L.etaSz ≤ D.R.k * L.etaSz := mul_le_mul_of_nonneg_right hmkR he.le
    push_cast at s1 s2
    nlinarith
  have hmain : (WeightAlgebra.DF (kaR Tp hK j) : ℝ) ≤
      (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz)) := by
    unfold WeightAlgebra.DF WeightAlgebra.degP
    push_cast
    refine (Finset.sum_le_sum fun τ _ => hτ τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    apply le_of_eq
    ring
  refine ⟨hmain, fun i => ?_⟩
  obtain ⟨Y, hY, -, -, hg⟩ := Pm.g_Y
  refine lt_of_le_of_lt (hmain.trans ?_) (four_sq_lt_of_eighth hkR hb (hY.trans (hg i).1))
  have u1 : (D.R.f : ℝ) * (L.Sc + L.etaSz) ≤ D.R.f * (2 * L.sc.b) := mul_le_mul_of_nonneg_left hSe hf0
  have u2 : (D.R.f : ℝ) * L.sc.b ≤ D.R.k * L.sc.b := mul_le_mul_of_nonneg_right hfk (by linarith)
  calc _ ≤ (D.R.k : ℝ) * (4 * (D.R.k * L.sc.b)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = _ := by ring

end GlobalTheory.RunDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_weightKappa_le_pageBound : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ j, InR D j → (WeightAlgebra.DF (kaR Tp hK j) : ℝ) ≤ (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz)) ∧ ∀ i, (WeightAlgebra.DF (kaR Tp hK j) : ℝ) < ((D.host.g i : ℝ) - 2) / 2 := by
  first | exact @GlobalTheory.RunDepth.DF_kaR_le | exact GlobalTheory.RunDepth.DF_kaR_le | (intros; apply GlobalTheory.RunDepth.DF_kaR_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHarishChandraParamOfTypeOfUnitaryW
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besType_continuous_blockW (k r : ℕ) : Continuous (PI.UpqRep.blockW k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold PI.UpqRep.blockW
  split_ifs
  · exact continuous_apply_apply _ _
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem besType_hcParam : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → Q.IsType k r z π u → ∃ u₀, PI.UpqRep.IsHCTypeW k r z u₀ π := by
  intro k r Wp _ _ _ z π u hz hT hπ
  obtain ⟨g, hg, hin, honto⟩ := GlobalTheory.T.exists_frame_conj_unitaryBlock_eq_unitaryComplement k r z hz hT
  obtain ⟨hnt, ⟨h1, hmul⟩, hcont, hnorm, hirr, -⟩ := hπ
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hg.1
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hg.1
  have hc : Continuous (fun x : Matrix (Fin k) (Fin k) ℂ => g * PI.UpqRep.blockW k r x * g⁻¹) :=
    (continuous_const.matrix_mul (besType_continuous_blockW k r)).matrix_mul continuous_const
  haveI := hnt
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.exists_highestWeight_irreducible_unitaryRep_U k Wp (fun x => π (g * PI.UpqRep.blockW k r x * g⁻¹))
    (by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show π (g * PI.UpqRep.blockW k r 1 * g⁻¹) = 1
        rw [PI.HwUniqW.blockW_one, Matrix.mul_one, hgg]
        exact h1
      · intro x hx y hy
        have e : g * PI.UpqRep.blockW k r (x * y) * g⁻¹ =
            g * PI.UpqRep.blockW k r x * g⁻¹ * (g * PI.UpqRep.blockW k r y * g⁻¹) := by
          rw [← PI.HwUniqW.blockW_mul]
          calc g * (PI.UpqRep.blockW k r x * PI.UpqRep.blockW k r y) * g⁻¹
              = g * PI.UpqRep.blockW k r x * (g⁻¹ * g) * PI.UpqRep.blockW k r y * g⁻¹ := by
                rw [hgg', Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Matrix.mul_assoc]
        show π (g * PI.UpqRep.blockW k r (x * y) * g⁻¹) = _
        rw [e]
        exact hmul _ (hin x hx) _ (hin y hy)
      · intro x hx v
        exact hnorm _ (hin x hx) v
      · intro v
        have h2 : ContinuousOn (fun x : Matrix (Fin k) (Fin k) ℂ => π (g * PI.UpqRep.blockW k r x * g⁻¹))
            (PI.UpqRep.UJset (PI.UpqRep.allPos k)) :=
          hcont.comp hc.continuousOn (fun x hx => hin x hx)
        exact h2.clm_apply continuousOn_const)
    (by
      intro S hS
      refine hirr S ?_
      intro h hh v hv
      obtain ⟨x, hx, rfl⟩ := honto h hh
      exact hS x hx v hv)
  exact ⟨u₀, g, hg, hu₀⟩

end GlobalTheory
end
