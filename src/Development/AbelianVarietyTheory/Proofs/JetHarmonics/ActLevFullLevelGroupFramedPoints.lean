module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrMoveTransfer
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueNormalisedPullbackChainRule
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedPullbackConjugateTranslateEqTranslateL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPoints
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FullLevelAction

open GlobalTheory.LevelActionLaws

theorem actLaws_levFull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) :
    ActLaws (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
      (fun {S : Type} [CommRing S] [Algebra c.F S] (g' : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (y y' : FrPt Xo c S) =>
        levActR (Xo := Xo) (c := c) (levFull Dw l) g' y y') := by
  obtain ⟨⟨ι, hι, hone⟩, hmul, hnb⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    obtain ⟨ρ, ν, i, h⟩ := exists_move hpq hA Xo g
    obtain ⟨y', hy'⟩ := (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).1
    exact ⟨y', ρ, ν, i, h, hy'⟩
  · intro g S _ _ y y' y'' h' h''
    obtain ⟨ρ, ν, i, h, hm⟩ := h'
    have hm' := frMove_transfer hpq hA Xo c g i h h''
    obtain rfl := (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).2 y' y'' ν rfl hm hm'
    exact (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S (AlgHom.id c.F S) y').2.1
  · intro S _ _ y
    refine ⟨𝟙 _, ι, inferInstance, ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩, hone S y⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (eta_congr Xo (liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  · intro g g' S _ _ y y' y'' h h'
    obtain ⟨ρ, ν, i, h, hm⟩ := h
    obtain ⟨ρ', ν', i', h', hm'⟩ := h'
    obtain ⟨μ, hμ, hc⟩ := hmul ρ ρ' ν ν'
    refine ⟨ρ ≫ ρ', μ, inferInstance, ⟨?_, fun a => ?_, fun a => ?_⟩, hc S y y' y'' hm hm'⟩
    · rw [Category.assoc, h'.1, h.1]
    · have e : Xo.univ.eta ((levFull Dw l (g * g')).1 a) =
          Xo.univ.eta ((levFull Dw l g).1 ((levFull Dw l g').1 a)) :=
        eta_congr Xo (liftLa_mul_sub g g' a)
      rw [e, hμ, ← Category.assoc, h.2.1, Category.assoc, h'.2.1, Category.assoc]
    · have e : (levFull Dw l (g * g')).2 a = (levFull Dw l g).2 ((levFull Dw l g').2 a) := rfl
      rw [e, hμ, ← Category.assoc, h.2.2, Category.assoc, h'.2.2, Category.assoc]
  · intro g S T _ _ _ _ φ y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).1 S T φ y y' z z' hyz hm (frMove_transfer hpq hA Xo c g i h hz)
  · intro g S _ _ t y y' z z' hyz hy hz
    obtain ⟨ρ, ν, i, h, hm⟩ := hy
    exact (hnb ρ ν).2 S t y y' z z' hyz hm (frMove_transfer hpq hA Xo c g i h hz)

theorem actLev_levFull : ∀ (D : D7) (Q : Par D) (j : ℕ), 1 ≤ (Q.Dw j).p + (Q.Dw j).q → Q.l.A = 1 → ActLev (Xo := Q.Xo j) Q.c (levFull (Q.Dw j) Q.l) := by
  intro D Q j hpq hA
  exact actLaws_levFull (Q.Xo j) Q.c hpq (by rw [hA]; exact Nat.coprime_one_left _)

end GlobalTheory.FullLevelAction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPointsStatement
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actLev_full_level_group_framedPoints : ∀ (D : D7) (Q : Par D) (j : ℕ), 1 ≤ (Q.Dw j).p + (Q.Dw j).q → Q.l.A = 1 → ActLev (Xo := Q.Xo j) Q.c (levFull (Q.Dw j) Q.l) := by
  first | exact @GlobalTheory.FullLevelAction.actLev_levFull | exact GlobalTheory.FullLevelAction.actLev_levFull | (intros; apply GlobalTheory.FullLevelAction.actLev_levFull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ThetaRuleValue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_field_isVtOver {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K) (n : ℕ) (x : Fin n → Dw.La) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra c.F F) (κ : K →ₐ[c.F] F) (z : FrPt Xo c F)
      (Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo z.x))),
      FrMap κ y z ∧
      ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) z.s (levPt Xo z.x (x b)) (Fs b) := by
  obtain ⟨U, iU, jU, κ, u, G, hff, hu, hG⟩ :=
    exists_faithfullyFlat_isVtOver firstFiveLaws.1 E H Dw l Xo c K y n x
  have hκ : Function.Injective κ := hff.injective
  have : Nontrivial U := hκ.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal U
  let iF : Field (U ⧸ m) := Ideal.Quotient.field m
  let ψ : U →ₐ[c.F] U ⧸ m := Ideal.Quotient.mkₐ c.F m
  obtain ⟨z, hz⟩ := FramedBaseChange.exists_frMap firstFiveLaws.1 E H Dw l Xo c U (U ⧸ m) ψ u
  let h : ptO Xo z.x ⟶ ptO Xo u.x := Over.homMk (spMap ψ.toRingHom) hz.1.symm
  choose F' hF' using fun b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2)
    (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (G b)
  refine ⟨U ⧸ m, iF, inferInstance, ψ.comp κ, z, F', FramedBaseChange.trans κ ψ hu hz, fun b => ?_⟩
  have e : h ≫ levPt Xo u.x (x b) = levPt Xo z.x (x b) := by
    unfold levPt
    rw [← Category.assoc, comp_toUnit]
  rw [← e]
  exact (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo l.M (l.Mb ^ 2) _ _ h u.s z.s
    (GlobalTheory.FramedBaseChange.isPullSec ψ hz h rfl) (G b) (F' b) (hF' b)).1 _ (hG b)

theorem map_evI_eq_thExpr (nab : NabV Xo c) (hnab : letI := H.starRing; IsNab Xo c nab) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (F : Type) [Field F] [inst : Algebra c.F F] :
    letI := io.toAlgebra
    ∀ (κ : T.Fr →ₐ[c.F] F) (z : FrPt Xo c F), FrMap κ y.1 z →
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∀ Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo z.x)),
      (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) z.s (levPt Xo z.x (x b)) (Fs b)) →
      ∀ f, IsThRule Xo c nab x P f → κ (evI y f) = thExpr Xo c nab z P Fs := by
  let := io.toAlgebra
  intro κ
  obtain ⟨g, hg⟩ : ∃ g : T.Fr →+* F, κ.toRingHom = g := ⟨_, rfl⟩
  have hi : inst = (g.comp io).toAlgebra := by
    refine Algebra.algebra_ext _ _ fun r => ?_
    rw [← hg]
    exact (κ.commutes r).symm
  subst hi
  let := g.toAlgebra
  intro z hz a n x P hP Fs hF f hf
  have key := GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field E H Dw l Xo c nab hnab T io y F κ hg z hz a n x P hP Fs hF f hf
  exact (congrArg (fun k : T.Fr →+* F => k (evI y f)) hg).trans key

theorem evI_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io'), letI := io.toAlgebra; letI := io'.toAlgebra; ∀ φ : T.Fr →ₐ[c.F] T'.Fr, FrMap φ y.1 y'.1 → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ), ∀ f ∈ thGen Xo c nab a n, φ (evI y f) = evI y' f := by
  intro E _ _ _ H Dw l Xo c nab hnab T T' io io' y y' φ hφ a n f hf
  let := io.toAlgebra
  let := io'.toAlgebra
  obtain ⟨x, P, hP, hf⟩ := hf
  obtain ⟨F, iF, jF, κ, z, Fs, hz, hF⟩ := exists_field_isVtOver y'.1 n x
  apply κ.toRingHom.injective
  have h₁ := map_evI_eq_thExpr nab hnab T io y F (κ.comp φ) z (FramedBaseChange.trans φ κ hφ hz)
    a n x P hP Fs hF f hf
  have h₂ := map_evI_eq_thExpr nab hnab T' io' y' F κ z hz a n x P hP Fs hF f hf
  exact h₁.trans h₂.symm

end GlobalTheory.ThetaRuleValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRule_integralPoint_value_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io'), letI := io.toAlgebra; letI := io'.toAlgebra; ∀ φ : T.Fr →ₐ[c.F] T'.Fr, FrMap φ y.1 y'.1 → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ), ∀ f ∈ thGen Xo c nab a n, φ (evI y f) = evI y' f := by
  first | exact @GlobalTheory.ThetaRuleValue.evI_baseChange | exact GlobalTheory.ThetaRuleValue.evI_baseChange | (intros; apply GlobalTheory.ThetaRuleValue.evI_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlphaFormHarmonicValueAtFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelPointEqOfKilledByHalfLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelPointEqOfKilledByHalfLevel
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem LevelPoints.comp_act_natCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  induction n with
  | zero =>
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h0 : t.act.act 0 = 1 := by simpa using h
    rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem exists_levPt_eq_of_killedBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (t : ptO Xo yF.x ⟶ Xo.univ.t.G), KilledBy Xo l.Mb t → ∃ a : Dw.La, levPt Xo yF.x a = t := by
  intro E _ _ _ H Dw l Xo c F _ _ _ yF t ht
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom F yF.x (Spec.preimage (yF.x ≫ Xo.s)).hom (Spec.map_preimage _).symm
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hpow : t ^ l.M = 1 := by
    rw [← LevelPoints.comp_act_natCast]
    exact ht _ (LevelPoints.natCast_mem l)
  obtain ⟨a, ha⟩ := (I.onto l.M hM t).1 hpow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (l.coprime ▸ Submodule.mem_top :
    (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  refine ⟨v • a, (hI _ (Submodule.smul_mem_smul hv Submodule.mem_top)).trans ?_⟩
  have h1 : I.ev l.M (u • a) = 1 := by
    rw [I.lin, ha]
    exact ht u hu
  have h2 := I.add l.M (u • a) (v • a)
  rw [← add_smul, huv, one_smul, h1, _root_.one_mul] at h2
  exact h2.symm.trans ha

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelPointEqOfKilledByHalfLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPoint_eq_of_killedByHalfLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (t : ptO Xo yF.x ⟶ Xo.univ.t.G), KilledBy Xo l.Mb t → ∃ a : Dw.La, levPt Xo yF.x a = t := by
  first | exact @GlobalTheory.exists_levPt_eq_of_killedBy | exact GlobalTheory.exists_levPt_eq_of_killedBy | (intros; apply GlobalTheory.exists_levPt_eq_of_killedBy <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.AlphaForm

theorem totalDegree_harm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n) (h0 : P ≠ 0) :
    P.totalDegree = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
  simp only [harmA, HaO, HHa, RowDeg, Set.mem_setOf_eq] at hP
  obtain ⟨⟨-, -, hD⟩, -⟩ := hP
  have hR : ∀ m ∈ P.support, (m.sum fun _ e => e) = ∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i) := by
    intro m hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    refine (Fintype.sum_sigma (fun ℓ => m ℓ)).trans ?_
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => hD m hm τ i
  apply le_antisymm
  · exact Finset.sup_le fun m hm => (hR m hm).le
  · obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.2 (mt MvPolynomial.support_eq_empty.1 h0)
    rw [← hR m hm]
    exact MvPolynomial.le_totalDegree hm

theorem nrm_mul_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {l : Level H}
    (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (α β : 𝓞 E) (N : ℕ) (h : α * β = (N : 𝓞 E)) :
    nrm Dw c a α * nrm Dw c a β = (N : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) := by
  simp only [nrm]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← mul_pow, ← map_mul, h, map_natCast]

theorem alphaForm_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (α : 𝓞 E), α * star α = (l.M : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (n : ℕ) (b : Fin n → (ptO Xo yF.x ⟶ Xo.univ.t.G)) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (l.M : ℤ) (ptO Xo yF.x))), (∀ i, b i ≫ Xo.univ.t.act.act (star α) = 1) → (∀ i, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) l.M yF.s (b i) (hh i)) → ∃ (xx : Fin n → Dw.La) (Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x))), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (l.M : ℤ) (hh i) (colOf m i) = algebraMap c.F F (nrm Dw c a α) * thExpr Xo c nab yF Pp Fs := by
  intro E _ _ _ H Dw l Xo c nab hnab F _ _ _ yF α hα hMb n b hh hb hT
  letI := H.starRing
  have hI := fun i => GlobalTheory.T.normalizedPullback_conjugate_translate_eq_translate_level E H Dw l Xo c F yF.x α hα hMb yF.s (b i) (hh i) (hb i) (hT i)
  choose Fs hN hV using hI
  have hK : ∀ i, KilledBy Xo l.Mb (b i ≫ Xo.univ.t.act.act α) := by
    intro i
    unfold KilledBy
    intro x hx
    rw [hMb, Ideal.mem_span_singleton'] at hx
    obtain ⟨r, rfl⟩ := hx
    have e : α * (r * star α) = star α * (α * r) := by ring
    rw [Category.assoc, ← Xo.univ.t.act.mul, e, Xo.univ.t.act.mul, ← Category.assoc, hb i]
    haveI := Xo.univ.t.act.hom (α * r)
    simp
  choose xx hxx using fun i => GlobalTheory.T.exists_levelPoint_eq_of_killedByHalfLevel E H Dw l Xo c F yF (b i ≫ Xo.univ.t.act.act α) (hK i)
  refine ⟨xx, Fs, fun i => by rw [hxx i]; exact hV i, ?_⟩
  intro a Pp hPp
  have hs : star α * star (star α) = ((l.M : ℕ) : 𝓞 E) := by rw [star_star, _root_.mul_comm]; exact hα
  have hz : ((l.M : ℤ) ^ 2) = ((l.M * l.M : ℕ) : ℤ) := by push_cast; ring
  have h := GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab F yF (star α) l.M l.M ((l.M : ℤ) ^ 2) hs hz n hh Fs hN a Pp hPp
  have hM : ((l.M : ℕ) : c.F) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  unfold thExpr
  rw [h]
  by_cases h0 : Pp = 0
  · subst h0
    simp
  have key : nrm Dw c a α * ((l.M : c.F) ^ Pp.totalDegree)⁻¹ * nrm Dw c a (star α) = 1 := by
    rw [totalDegree_harm c hPp h0, _root_.mul_right_comm, nrm_mul_nrm Dw c a α (star α) l.M hα]
    exact mul_inv_cancel₀ (pow_ne_zero _ hM)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← map_mul, ← map_mul, key, map_one, _root_.one_mul]

end GlobalTheory.AlphaForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSimInducing
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Classical

namespace GlobalTheory.CoverCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem sup_eq_top_of_level (l l₂ : Level H) (p : ℕ) (I : Ideal (𝓞 E)) (hM : l₂.M = l.M * p)
    (hp : Nat.Coprime p l.M) (hI : l₂.Mb = l.Mb * I) : l.Mb ⊔ I = ⊤ := by
  have h0 : (Ideal.span {(l.M : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    have := l.three_le
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    omega
  have h1 : Ideal.span {(l.M : 𝓞 E)} * (I * I.map (H.bar : 𝓞 E →+* 𝓞 E)) =
      Ideal.span {(l.M : 𝓞 E)} * Ideal.span {(p : 𝓞 E)} := by
    have h := l₂.prod
    rw [hI, Ideal.map_mul, hM, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton] at h
    rw [← h, ← l.prod]
    ring
  have h2 := mul_left_cancel₀ h0 h1
  have hpI : (p : 𝓞 E) ∈ I := by
    have : (p : 𝓞 E) ∈ I * I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [h2]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf this).1
  have hMM : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf this).1
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hp).map (Int.castRingHom (𝓞 E))
  rw [Ideal.eq_top_iff_one, ← huv]
  refine Ideal.add_mem _ (Ideal.mem_sup_right (I.mul_mem_left _ ?_)) (Ideal.mem_sup_left (l.Mb.mul_mem_left _ ?_))
  · simpa using hpI
  · simpa using hMM

theorem exists_sim_inducing (D : Datum H) (hpq : 1 ≤ D.p + D.q) (l l₂ : Level H) (p : ℕ) (I : Ideal (𝓞 E))
    (hd : l.Dvd l₂) (hM : l₂.M = l.M * p) (hp : Nat.Coprime p l.M) (hI : l₂.Mb = l.Mb * I) (hA : l₂.A = 1)
    (k : (D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)) ≃ₗ[𝓞 E] (D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La))) :
    ∃ g : Sim D, g.InGam l l₂ ∧
      ∀ a : D.La, (Submodule.Quotient.mk (g.f l₂.M a) : D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)) =
        k (Submodule.Quotient.mk a) := by
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.1
    (show (1 : 𝓞 E) ∈ l.Mb ⊔ I by rw [sup_eq_top_of_level l l₂ p I hM hp hI]; trivial)
  haveI : Module.Projective (𝓞 E) D.La := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (I • ⊤ : Submodule (𝓞 E) D.La).mkQ
    (k.toLinearMap ∘ₗ (I • ⊤ : Submodule (𝓞 E) D.La).mkQ) (Submodule.mkQ_surjective _)
  have hf' : ∀ a, (Submodule.Quotient.mk (f a) : D.La ⧸ (I • ⊤ : Submodule (𝓞 E) D.La)) =
      k (Submodule.Quotient.mk a) := fun a => LinearMap.congr_fun hf a
  set F : D.La →ₗ[𝓞 E] D.La := e • f + e' • LinearMap.id with hF
  have h1 : ∀ x, F x - f x ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := fun x => by
    have : F x - f x = e' • (x - f x) := by
      have h : e = 1 - e' := by linear_combination hee
      simp only [hF, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [h, sub_smul, one_smul, smul_sub]; abel
    rw [this]
    exact Submodule.smul_mem_smul he' Submodule.mem_top
  have h2 : ∀ x, F x - x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) D.La) := fun x => by
    have : F x - x = e • (f x - x) := by
      have h : e' = 1 - e := by linear_combination hee
      simp only [hF, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [h, sub_smul, one_smul, smul_sub]; abel
    rw [this]
    exact Submodule.smul_mem_smul he Submodule.mem_top
  have lM : (l₂.Mb • ⊤ : Submodule (𝓞 E) D.La) ≤ l.Mb • ⊤ := Submodule.smul_mono_left hd.2.1
  have lI : (l₂.Mb • ⊤ : Submodule (𝓞 E) D.La) ≤ I • ⊤ :=
    Submodule.smul_mono_left (by rw [hI]; exact Ideal.mul_le_inf.trans inf_le_right)
  obtain ⟨g, g1, -⟩ := GlobalTheory.exists_sim_of_aut_mod E H D l₂ 1 F hpq one_pos (Nat.coprime_one_left _) (by
    intro x hx
    have x1 : x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) D.La) := by
      have := Submodule.sub_mem _ (lM hx) (h2 x)
      rwa [sub_sub_cancel] at this
    have x2 : x ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := by
      have := Submodule.sub_mem _ (lI hx) (h1 x)
      rw [sub_sub_cancel, ← Submodule.Quotient.mk_eq_zero, hf', k.map_eq_zero_iff,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
    have : x = e • x + e' • x := by rw [← add_smul, hee, one_smul]
    rw [this, hI]
    refine Submodule.add_mem _ ?_ ?_
    · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he x2
    · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul he' x1)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hp0 : 0 < p := by
    have := l₂.three_le
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [hM, h] at this; omega
    · exact h
  have hMM : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf this).1
  have hA1 : l.A = 1 := Nat.dvd_one.1 (hA ▸ hd.2.2)
  refine ⟨g, ⟨by rw [hA]; simp, fun a => ?_, fun a => ⟨g.f l.A a - a, by rw [hA1, one_smul]⟩⟩, fun a => ?_⟩
  · obtain ⟨b, hb⟩ := g.tower l.M p hM0 hp0 a
    rw [← hM] at hb
    have h3 : g.f l₂.M a - g.f l.M a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) D.La) := by
      rw [hb, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul hMM Submodule.mem_top
    have := Submodule.sub_mem _ (Submodule.add_mem _ (lM (g1 a)) (h2 a)) h3
    convert this using 1
    abel
  · rw [← hf', Submodule.Quotient.eq]
    have := Submodule.add_mem _ (lI (g1 a)) (h1 a)
    rwa [sub_add_sub_cancel] at this

theorem psi_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k], Nonempty (FrPt d.Xo₂ d.c₂ k) → ∀ ψ ψ' : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ, d.PsiTie ψ → d.PsiTie ψ' → ψ = ψ' := by
  intro E _ _ _ H Dw l Xo c n d hpq hlev hA K _ _ _ ⟨y⟩ ψ ψ' h h'
  obtain ⟨hd, hM, hp, hI, -, -, -, -, hne⟩ := hlev
  ext k
  obtain ⟨g, hg, hk⟩ := exists_sim_inducing Dw hpq l d.l₂ d.pd d.I hd hM hp hI hA k
  obtain ⟨ρ, hρ⟩ := GlobalTheory.LevelActionLaws.exists_levAut hpq d.Xo₂ g hg.1
  obtain ⟨hs, ν, -⟩ := id hρ
  obtain ⟨y', hy'⟩ := (GlobalTheory.exists_unique_frMove E H Dw d.l₂ d.Xo₂ d.c₂ ρ.hom ν hs K y).1
  have hgA : ∀ a, Dw.ModN d.l₂.A (g.f d.l₂.A a - a) := fun a => ⟨g.f d.l₂.A a - a, by rw [hA, one_smul]⟩
  have e1 := h k g ρ hg hgA hρ hk K y y' hy'.1
  have e2 := h' k g ρ hg hgA hρ hk K y y' hy'.1
  have e3 := mul_right_cancel₀ (hne K y) (e1.symm.trans e2)
  have e4 := d.eF.injective ((algebraMap d.c₂.F K).injective e3)
  rw [e4]

end GlobalTheory.CoverCharacter
end
