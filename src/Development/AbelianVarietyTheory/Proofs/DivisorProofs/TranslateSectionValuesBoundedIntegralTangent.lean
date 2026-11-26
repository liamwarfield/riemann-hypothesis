module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsSecNeZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.TwistSpanExample

theorem span_holds : TwistBCSpanStatement := twistBCSpan_of GlobalTheory.twistBaseChange

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) {k : ℕ}

end GlobalTheory.TwistSpanExample
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombination
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualLin

theorem sp_dual_subsingleton (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem sE_comb : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) (n : ℕ) (a : Fin n → F) (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))), (∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) → ∀ (r : Sp (DualNumber F) ⟶ (DegPre.BF D F).left) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → r ≫ (fst (TF (R := V) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) → sE s r J = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i) r J := by
  intro V _ _ D F _ _ k β s n a σF hs r J hJ hr
  have hW : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D F β)
      (fun k' => J (redE F ≫ r ≫ DegPre.famφ D F β k')) := by
    intro y _
    haveI := sp_dual_subsingleton F
    let z : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
    have hy : y = (redE F).base z := Subsingleton.elim _ _
    refine Set.mem_iInter.2 fun k' => ?_
    have := hJ (redE F ≫ r ≫ DegPre.famφ D F β k') (Set.mem_univ z)
    subst hy
    simpa using this
  unfold sE
  refine (congrArg (valR r _) (hs _)).trans ((GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).trans ((map_sum _ _ _).trans
    (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans ?_)))
  congr 1
  · refine (GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).symm.trans ?_
    rw [← TrivSqZeroExt.algebraMap_eq_inl]
    exact GlobalTheory.ZH.FormCount.valR_scal (algebraMap F (DualNumber F)) r _ hr _ hW (a i)
  · exact (GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).symm

end GlobalTheory.DualLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombinationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumberSectionValue_linearCombination : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) (n : ℕ) (a : Fin n → F) (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))), (∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) → ∀ (r : Sp (DualNumber F) ⟶ (DegPre.BF D F).left) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → r ≫ (fst (TF (R := V) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) → sE s r J = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i) r J := by
  first | exact @GlobalTheory.DualLin.sE_comb | exact GlobalTheory.DualLin.sE_comb | (intros; apply GlobalTheory.DualLin.sE_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem trF_dualPoint_of_isPull : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  intro V _ _ D C _ _ gm₀ gm hp mu
  have hsq : spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TE V C).hom := by
    simp only [epsR, TE, TF, jFK, jK, spMap, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : TE V C ⟶ epsR V := Over.homMk (spMap (dualMap (toF V C))) hsq
  have hb : gm.b = k ≫ gm₀.b := by
    ext1
    simpa [k] using hp.1
  set e : TE V C ⟶ TF (R := V) C := Over.homMk (spMap (algebraMap C (DualNumber C))) rfl with he
  refine ⟨?_, Over.w _, ?_⟩
  · have h1 : lift e gm.b ≫ DegPre.trF D C mu ≫ DegPre.prB D C = k ≫ padd D.P.A gm₀.b (toUnit _ ≫ D.c mu) := by
      simp only [DegPre.trF, DegPre.prB, lift_snd, padd, comp_lift_assoc, comp_lift, hb, Category.assoc, comp_toUnit_assoc]
    have h2 := congrArg CommaMorphism.left h1
    simpa [k] using h2
  · have h1 : lift e gm.b ≫ DegPre.trF D C mu ≫ fst _ _ = e := by
      simp [DegPre.trF]
    have h2 := congrArg CommaMorphism.left h1
    simpa [he] using h2

end GlobalTheory.MBLow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedDualPointOfIntegralTorusExtPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (C : Type) [Field C] [Algebra (FractionRing V) C] (gm₀ : GtPt D (epsR V)) (gm : GtPt D (TE V C)), GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ mu : D.X, ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (DegPre.prB D C).left = spMap (dualMap (toF V C)) ≫ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ∧ (padd D.P.A gm₀.b (toUnit _ ≫ D.c mu)).left ≫ D.P.A.hom = spMap (algebraMap V (DualNumber V)) ∧ ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫ (DegPre.trF D C mu).left) ≫ (fst (TF (R := V) C) D.P.A).left = spMap (algebraMap C (DualNumber C)) := by
  first | exact @GlobalTheory.MBLow.trF_dualPoint_of_isPull | exact GlobalTheory.MBLow.trF_dualPoint_of_isPull | (intros; apply GlobalTheory.MBLow.trF_dualPoint_of_isPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilySectionSpanPullbacksUnitBall
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilySectionSpanPullbacksUnitBall
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing

noncomputable section
namespace GlobalTheory.SpanBall
open TWM TWO SectionScalarValuation

section Gen

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] (S : ValuationSubring F) (g : V →+* S)
  (hg : (algebraMap S F).comp g = algVF (F := F) (V := V))

abbrev TS : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom g))

abbrev ιT : TF (R := V) F ⟶ TS S g :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap S F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap S F)) ≫ Spec.map (CommRingCat.ofHom g) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

abbrev jT : DegPre.BF D.toPre F ⟶ TS S g ⊗ D.toPre.P.A := ιT S g hg ▷ D.toPre.P.A

theorem jT_snd : (jT S g hg (D := D)).left ≫ (snd (TS S g) D.toPre.P.A).left = (DegPre.prB D.toPre F).left := by
  rw [← Over.comp_left, whiskerRight_snd]

theorem jT_fst : (jT S g hg (D := D)).left ≫ (fst (TS S g) D.toPre.P.A).left =
    (fst (TF (R := V) F) D.toPre.P.A).left ≫ (ιT S g hg).left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

abbrev ιs (r : Γ(Spec (CommRingCat.of S), ⊤)) : F :=
  algebraMap S F ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom r)

theorem gs_jT {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (r : Γ(Spec (CommRingCat.of S), ⊤)) :
    gs (ρ ≫ (jT S g hg (D := D)).left) z ⊤ ((fst (TS S g) D.toPre.P.A).left.appTop.hom r) =
      gs ρ z ⊤ (gF D.toPre F (ιs S r)) := by
  have e1 : gs (ρ ≫ (jT S g hg (D := D)).left) z ⊤ ((fst (TS S g) D.toPre.P.A).left.appTop.hom r) =
      gs ((ρ ≫ (jT S g hg (D := D)).left) ≫ (fst (TS S g) D.toPre.P.A).left) z ⊤ r := gs_pull _ _ z ⊤ trivial r
  rw [e1, Category.assoc, jT_fst, ← Category.assoc]
  have e2 : gs ((ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ (ιT S g hg).left) z ⊤ r =
      gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤ ((ιT S g hg).left.appTop.hom r) :=
    (gs_pull _ _ z ⊤ trivial r).symm
  have e3 : gs ρ z ⊤ (gF D.toPre F (ιs S r)) = gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (ιs S r)) := gs_pull _ _ z ⊤ trivial _
  rw [e2, e3, show (ιT S g hg).left = Spec.map (CommRingCat.ofHom (algebraMap S F)) from rfl, appTop_specMap]
  rfl

theorem isPullback_jT : IsPullback (jT S g hg (D := D)).left (fst (TF (R := V) F) D.toPre.P.A).left
    (fst (TS S g) D.toPre.P.A).left (Spec.map (CommRingCat.ofHom (algebraMap S F))) := by
  have H₁ : IsPullback (snd (TS S g) D.toPre.P.A).left (fst (TS S g) D.toPre.P.A).left D.toPre.P.A.hom
      (TS S g).hom := (IsPullback.of_hasPullback (TS S g).hom D.toPre.P.A.hom).flip
  have H₀ : IsPullback (DegPre.prB D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left D.toPre.P.A.hom
      (TF (R := V) F).hom := (IsPullback.of_hasPullback (TF (R := V) F).hom D.toPre.P.A.hom).flip
  rw [← jT_snd S g hg, ← Over.w (ιT S g hg)] at H₀
  exact H₀.of_right (jT_fst S g hg) H₁


include hg in
theorem span_gen (hloc : IsLocalHom g) {k : ℕ} (hk : 1 ≤ k) {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) :
    ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.toPre.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (σF i) (D.toPre.famφB α)
        (DegPre.famε k) (σ i) (DegPre.prB D.toPre F).left 1) ∧
      ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre F (a i) _ * (σF i).f j := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have hp : IsProper (fst (TS S g) D.toPre.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TS S g).hom D.toPre.P.A.hom))
  have : CompactSpace (TS S g).left := inferInstanceAs (CompactSpace (Spec (CommRingCat.of S)))
  have : QuasiSeparatedSpace (TS S g).left := inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of S)))
  have : CompactSpace (TS S g ⊗ D.toPre.P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst (TS S g) D.toPre.P.A).left
  have : QuasiSeparatedSpace (TS S g ⊗ D.toPre.P.A).left :=
    (quasiSeparated_iff_quasiSeparatedSpace (fst (TS S g) D.toPre.P.A).left).mp inferInstance
  obtain ⟨s₁, hs₁⟩ := exists_sec hL (φ' := fun i => (jT S g hg (D := D)).left ≫
      (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α i) (ε' := DegPre.famε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      rw [GC.famφ_eq, ← jT_snd S g hg, Category.assoc]) s
  obtain ⟨t, ht, S₀, hS₀⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors S) (isPullback_jT S g hg (D := D)) hL
    (fun i => (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) s₁
  obtain ⟨n, rr, σ, hσ⟩ := GlobalTheory.TwistSpanExample.span_holds V D.toPre k hk α S g hloc S₀
  choose σF hσF using fun i => FamInt.exists_pull (D := D) (F := F) (σ i)
  have ht0 : (t : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := F) ht
  refine ⟨n, fun i => (t : F)⁻¹ * ιs S (rr i), σ, σF, hσF, fun j => ?_⟩
  refine (sec_ext_val hL (s' := FamInt.secLin (fun i => gF D.toPre F ((t : F)⁻¹ * ιs S (rr i))) σF)
    (fun y J hJ => ?_) j).trans rfl
  rw [sval_lin (s := FamInt.secLin _ _) (fun i => gF D.toPre F ((t : F)⁻¹ * ιs S (rr i))) σF (fun _ => rfl) _ y hJ]
  have e₁ : sval S₀ (𝟙 _ ≫ (jT S g hg (D := D)).left) y J = gs (𝟙 _) y ⊤ (gF D.toPre F t) * sval s (𝟙 _) y J := by
    rw [← hs₁ _ _ y J hJ, sval_of S₀ (𝟙 _ ≫ (jT S g hg (D := D)).left) y J (fun a => J (𝟙 _ ≫ (jT S g hg (D := D)).left ≫
      (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α a)) (fun a => by rw [Category.assoc])]
    refine (hS₀ _ (𝟙 _) y _ (hJ.mem (fun a => (jT S g hg (D := D)).left ≫
      (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
    have e := gs_jT S g hg (D := D) (𝟙 _) y ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom t)
    rw [show ιs S ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom t) = (t : F) by simp [ιs]] at e
    rw [← e, ← Category.assoc]
    exact (gs_pull _ _ y ⊤ trivial _).symm
  have e₂ := sval_lin (fun l => (fst (TS S g) D.toPre.P.A).left.appTop.hom (rr l))
      (fun l => pullSec D.toPre.P.L _ _ (σ l) (snd (TS S g) D.toPre.P.A).left) (fun j => hσ j)
      (𝟙 _ ≫ (jT S g hg).left) y hJ
  have g' : ∀ a b : F, gs (𝟙 _) y ⊤ (gF D.toPre F (a * b)) =
      gs (𝟙 _) y ⊤ (gF D.toPre F a) * gs (𝟙 _) y ⊤ (gF D.toPre F b) := fun a b => by
    rw [map_mul, gs_mul _ y ⊤ trivial]
  have g₁ : gs (𝟙 _) y ⊤ (gF D.toPre F (t : F)⁻¹) * gs (𝟙 _) y ⊤ (gF D.toPre F t) = 1 := by
    rw [← g', inv_mul_cancel₀ ht0, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]
  rw [← _root_.one_mul (sval s _ y J), ← g₁, _root_.mul_assoc, ← e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g', gs_jT, sval_pullSec _ _ _ _ _ y hJ, Category.assoc, jT_snd, secScal_sval (hσF i) _ y hJ, _root_.mul_assoc]

end Gen

theorem isLocalHom_ball {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing V) C]
    (hC : CExt V (maximalIdeal V) C) (S : ValuationSubring C) (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) :
    IsLocalHom ((algVF (F := C) (V := V)).codRestrict S.toSubring fun x => (hS _).2 (hC.1 x)) where
  map_nonunit x hx := by
    by_contra hxu
    have hm : x ∈ maximalIdeal V := (mem_maximalIdeal x).2 hxu
    have h1 : ‖algVF (F := C) (V := V) x‖ < 1 := hC.2 x hm
    obtain ⟨u, hu⟩ := hx
    have a1 : ‖((u : S) : C)‖ ≤ 1 := (hS _).1 (u : S).2
    have a2 : ‖(((u⁻¹ : Sˣ) : S) : C)‖ ≤ 1 := (hS _).1 ((u⁻¹ : Sˣ) : S).2
    have e : ((u : S) : C) * (((u⁻¹ : Sˣ) : S) : C) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
    have e' : ‖((u : S) : C)‖ * ‖(((u⁻¹ : Sˣ) : S) : C)‖ = 1 := by rw [← norm_mul, e, norm_one]
    have hux : ((u : S) : C) = algVF (F := C) (V := V) x := by rw [hu]; rfl
    rw [← hux] at h1
    nlinarith [mul_le_mul_of_nonneg_left a2 (norm_nonneg ((u : S) : C)), norm_nonneg (((u⁻¹ : Sˣ) : S) : C)]

theorem span_ball : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (S : ValuationSubring C), (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) → ∀ (k : ℕ), 1 ≤ k → ∀ (β : D.toPre.X) (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), ∃ (n : ℕ) (a : Fin n → C) (σ : Fin n → D.toPre.SecB k β) (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) (σF i) (D.toPre.famφB β) (DegPre.famε k) (σ i) (DegPre.prB D.toPre C).left 1) ∧ ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre C (a i) _ * (σF i).f j := by
  intro V _ _ _ D C _ _ hC S hS k hk β s
  exact span_gen (D := D) S _ rfl (isLocalHom_ball hC S hS) hk s

end GlobalTheory.SpanBall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilySectionSpanPullbacksUnitBallStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familySection_span_pullbacks_unitBall : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (S : ValuationSubring C), (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) → ∀ (k : ℕ), 1 ≤ k → ∀ (β : D.toPre.X) (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), ∃ (n : ℕ) (a : Fin n → C) (σ : Fin n → D.toPre.SecB k β) (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) (σF i) (D.toPre.famφB β) (DegPre.famε k) (σ i) (DegPre.prB D.toPre C).left 1) ∧ ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre C (a i) _ * (σF i).f j := by
  first | exact @GlobalTheory.SpanBall.span_ball | exact GlobalTheory.SpanBall.span_ball | (intros; apply GlobalTheory.SpanBall.span_ball <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackSectionIntegralValueDualPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackSectionIntegralValueDualPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntGaugePull

theorem top_le_of_redE {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp (DualNumber A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (redE A ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro z _
  let w : Sp A := (Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A)))).base z
  have hw : (redE A).base w = z := by
    simp only [w, redE, spMap, Spec.map_base]
    refine PrimeSpectrum.ext (Ideal.ext fun t => ?_)
    simp only [TopCat.hom_ofHom, ContinuousMap.coe_mk, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      CommRingCat.hom_ofHom]
    have hn : TrivSqZeroExt.inr (TrivSqZeroExt.snd t) ∈ z.asIdeal := by
      apply z.isPrime.mem_of_pow_mem 2
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact z.asIdeal.zero_mem
    have ht : t = algebraMap A (DualNumber A) ((TrivSqZeroExt.fstHom A A A).toRingHom t) +
        TrivSqZeroExt.inr (TrivSqZeroExt.snd t) := by
      rw [TrivSqZeroExt.algebraMap_eq_inl]; exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq t).symm
    constructor
    · intro h1; rw [ht]; exact z.asIdeal.add_mem h1 hn
    · intro h1
      have e : algebraMap A (DualNumber A) ((TrivSqZeroExt.fstHom A A A).toRingHom t) =
          t - TrivSqZeroExt.inr (TrivSqZeroExt.snd t) := eq_sub_of_add_eq ht.symm
      change algebraMap A (DualNumber A) ((TrivSqZeroExt.fstHom A A A).toRingHom t) ∈ z.asIdeal
      rw [e]; exact z.asIdeal.sub_mem h1 hn
  have := h (show w ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← hw]
  exact this

theorem sep_unique {C : Type} [Field C] (S : ValuationSubring C) {X Y : Scheme.{0}} (p : X ⟶ Y) [IsSeparated p]
    (x₁ x₂ : Sp S ⟶ X) (h₁ : x₁ ≫ p = x₂ ≫ p) (h : spMap S.subtype ≫ x₁ = spMap S.subtype ≫ x₂) : x₁ = x₂ := by
  have hU : ValuativeCriterion.Uniqueness p := IsSeparated.valuativeCriterion p
  let Q : ValuativeCommSq p :=
    { R := S, K := C, i₁ := Spec.map (CommRingCat.ofHom (algebraMap S C)) ≫ x₁, i₂ := x₁ ≫ p,
      commSq := ⟨by rw [Category.assoc]⟩ }
  have := (hU Q).elim ⟨x₁, rfl, rfl⟩ ⟨x₂, h.symm, h₁.symm⟩
  exact congrArg CommSq.LiftStruct.l this

theorem spMap_subtype_cancel {C : Type} [Field C] (S : ValuationSubring C) {A : Type} [CommRing A]
    (f g : Sp S ⟶ Sp A) (h : spMap S.subtype ≫ f = spMap S.subtype ≫ g) : f = g := by
  obtain ⟨f', rfl⟩ := Spec.map_surjective f
  obtain ⟨g', rfl⟩ := Spec.map_surjective g
  simp only [spMap, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext a
  have := congrArg (fun u => u.hom a) h'
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

end GlobalTheory.IntGaugePull

namespace GlobalTheory.IntGaugePull

theorem spMap_comp_spMap {A B E : Type} [CommRing A] [CommRing B] [CommRing E] (f : B →+* E) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem redE_dual {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    redE B ≫ spMap (dualMap f) = spMap f ≫ redE A := by
  simp only [redE, spMap_comp_spMap]
  congr 1
  ext z <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp {A B E : Type} [CommRing A] [CommRing B] [CommRing E] (f : B →+* E) (g : A →+* B) :
    spMap (dualMap f) ≫ spMap (dualMap g) = spMap (dualMap (f.comp g)) := by
  rw [spMap_comp_spMap]
  congr 1
  ext z <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem famφB_hom {V : Type} [CommRing V] [IsDomain V] (D : DegPre V) (β : D.X) (i : Fin 4) :
    D.famφB β i ≫ D.P.A.hom = D.P.A.hom := by
  fin_cases i
  · exact Category.id_comp _
  all_goals exact Over.w _

end GlobalTheory.IntGaugePull

namespace GlobalTheory.IntGaugePull

theorem sE_norm_le_one_of_pull : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ) (β : D.toPre.X) (σ : D.toPre.SecB k β) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) σF (D.toPre.famφB β) (DegPre.famε k) σ (DegPre.prB D.toPre C).left 1 → ∀ (Q : Sp (DualNumber V) ⟶ D.toPre.P.A.left), Q ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) → ∀ (r : Sp (DualNumber C) ⟶ (DegPre.BF D.toPre C).left), r ≫ (DegPre.prB D.toPre C).left = spMap (dualMap (toF V C)) ≫ Q → ‖(sE σF r ν.J).fst‖ ≤ 1 ∧ ‖(sE σF r ν.J).snd‖ ≤ 1 := by
  intro V _ _ _ D C _ _ hC N ν hI k β σ σF hS Q hQ r hr
  obtain ⟨S, hSmem, hInt⟩ := hI
  have hle : ∀ v : V, toF V C v ∈ S := fun v => (hSmem _).2 (hC.1 v)
  let toS : V →+* S := (toF V C).codRestrict S hle
  have htoS : S.subtype.comp toS = toF V C := by ext v; rfl
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have hpt : ∀ i : Fin 4, ⊤ ≤ (spMap (dualMap toS) ≫ Q ≫ D.toPre.famφB β i) ⁻¹ᵁ
      D.toPre.P.L.U (ν.J (redE C ≫ spMap (dualMap (toF V C)) ≫ Q ≫ D.toPre.famφB β i)) := by
    intro i
    have hQi : (Q ≫ D.toPre.famφB β i) ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) := by
      rw [Category.assoc, famφB_hom, hQ]
    let xi : TF (R := V) C ⟶ D.toPre.P.A :=
      Over.homMk (redE C ≫ spMap (dualMap (toF V C)) ≫ Q ≫ D.toPre.famφB β i) (by
        simp only [Category.assoc]
        rw [famφB_hom, hQ, spMap_comp_spMap, redE, spMap_comp_spMap]
        simp only [TF, Over.mk_hom, jFK, jK]
        rw [← Spec.map_comp]
        congr 1
        ext v
        simp [dualMap, toF, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl)
    obtain ⟨x₀, hx₀, hU⟩ := hInt xi
    have hxy : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ (spMap toS ≫ redE V ≫ Q ≫ D.toPre.famφB β i) := by
      rw [hx₀]
      simp only [xi, Over.homMk_left]
      rw [← Category.assoc (spMap S.subtype), spMap_comp_spMap, htoS, ← Category.assoc, redE_dual, Category.assoc]
    have heq : x₀ = spMap toS ≫ redE V ≫ Q ≫ D.toPre.famφB β i :=
      sep_unique S D.toPre.P.A.hom _ _ (spMap_subtype_cancel S _ _ (by simp only [← Category.assoc] at hxy ⊢; rw [hxy])) hxy
    apply top_le_of_redE
    rw [← Category.assoc, redE_dual, Category.assoc, ← heq]
    exact hU

  have hj : ∀ i, ν.J (redE C ≫ r ≫ D.toPre.famφ C β i) =
      ν.J (redE C ≫ spMap (dualMap (toF V C)) ≫ Q ≫ D.toPre.famφB β i) := by
    intro i; rw [ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq, ← Category.assoc r, hr, Category.assoc]
  unfold sE
  set j : Fin 4 → D.toPre.P.L.ι := fun k => ν.J (redE C ≫ r ≫ D.toPre.famφ C β k) with hjdef
  have hQ' : ⊤ ≤ (spMap (dualMap toS) ≫ Q) ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := by
    intro z _
    show (spMap (dualMap toS) ≫ Q).base z ∈ ⋂ k, (D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _)
    refine Set.mem_iInter.2 fun i => ?_
    have := hpt i (show z ∈ (⊤ : (Sp (DualNumber S)).Opens) from trivial)
    rw [← hj i] at this
    exact this
  obtain ⟨hrB0, hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (dualMap S.subtype) (spMap (dualMap toS) ≫ Q) _ hQ'
  have hrq : spMap (dualMap S.subtype) ≫ spMap (dualMap toS) ≫ Q = r ≫ (D.toPre.prB C).left := by
    rw [← Category.assoc, dualMap_comp, htoS, hr]
  rw [hrq] at hrB0 hval

  have hW2 : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j := by
    intro z hz
    have h' : (r ≫ (D.toPre.prB C).left).base z ∈
        ⋂ k, (D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _) := hrB0 hz
    show r.base z ∈ ⋂ k, ((D.toPre.prB C).left ≫ D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _)
    exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 h' k
  have hWeq : LB.wchart D.toPre.P.L (D.toPre.famφ C β) j =
      LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j :=
    congrArg (fun φ => LB.wchart D.toPre.P.L φ j) (funext (ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq D.toPre C β))
  have hW1 : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφ C β) j := hWeq ▸ hW2
  have hW : ⊤ ≤ r ⁻¹ᵁ (LB.wchart D.toPre.P.L (D.toPre.famφ C β) j ⊓
      LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j) :=
    fun z hz => ⟨hW1 hz, hW2 hz⟩
  have hcoh : D.toPre.P.L.Coh (Sum.elim (D.toPre.famφ C β) fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k)
      (Sum.elim j j) := by
    have key : ∀ a, Sum.elim j j a = ν.J (redE C ≫ r ≫ (Sum.elim (D.toPre.famφ C β)
        (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) a)) := by
      rintro (a | a)
      · rfl
      · simp only [Sum.elim_inr, hjdef]; rw [ReciprocityTheory.ChartRestriction.G.DVR.GC.famφ_eq]
    intro a b hab; rw [key a, key b, hab]
  have E := hS j j hcoh
  simp only [map_one, _root_.one_mul] at E

  have hv : valR r (LB.wchart D.toPre.P.L (D.toPre.famφ C β) j) (σF.f j) =
      dualMap S.subtype (valR (spMap (dualMap toS) ≫ Q) (LB.wchart D.toPre.P.L (D.toPre.famφB β) j) (σ.f j)) := by
    refine Eq.trans ?_ (hval (σ.f j))
    have hrB1 : ⊤ ≤ r ⁻¹ᵁ (D.toPre.prB C).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) j :=
      fun z hz => hrB0 hz
    refine Eq.trans ?_ (GlobalTheory.ZH.EvCrd.valR_comp r (D.toPre.prB C).left
      (LB.wchart D.toPre.P.L (D.toPre.famφB β) j) hrB1 (σ.f j))
    have hle2 : LB.wchart D.toPre.P.L (D.toPre.famφ C β) j ⊓
        LB.wchart D.toPre.P.L (fun k => (D.toPre.prB C).left ≫ D.toPre.famφB β k) j ≤
        (D.toPre.prB C).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) j := by
      intro z hz
      have h' : z ∈ ⋂ k, ((D.toPre.prB C).left ≫ D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _) := hz.2
      show (D.toPre.prB C).left.base z ∈ ⋂ k, (D.toPre.famφB β k).base ⁻¹' (D.toPre.P.L.U (j k) : Set _)
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 h' k
    refine Eq.trans (GlobalTheory.ZH.CrdCalc.valR_res r inf_le_left hW (σF.f j)).symm ?_
    refine Eq.trans ?_ (GlobalTheory.ZH.CrdCalc.valR_res r hle2 hW _)
    congr 1
    exact E.symm
  rw [hv]
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add]
  exact ⟨(hSmem _).1 (Subtype.prop _), (hSmem _).1 (Subtype.prop _)⟩

end GlobalTheory.IntGaugePull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackSectionIntegralValueDualPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBackSection_integralValue_dualPoint : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ) (β : D.toPre.X) (σ : D.toPre.SecB k β) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) σF (D.toPre.famφB β) (DegPre.famε k) σ (DegPre.prB D.toPre C).left 1 → ∀ (Q : Sp (DualNumber V) ⟶ D.toPre.P.A.left), Q ≫ D.toPre.P.A.hom = spMap (algebraMap V (DualNumber V)) → ∀ (r : Sp (DualNumber C) ⟶ (DegPre.BF D.toPre C).left), r ≫ (DegPre.prB D.toPre C).left = spMap (dualMap (toF V C)) ≫ Q → ‖(sE σF r ν.J).fst‖ ≤ 1 ∧ ‖(sE σF r ν.J).snd‖ ≤ 1 := by
  intro V _ _ _ D C _ _ hC N ν hI k β σ σF hS Q hQ r hr
  exact GlobalTheory.IntGaugePull.sE_norm_le_one_of_pull V D C hC N ν hI k β σ σF hS Q hQ r hr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateSectionValuesBoundedIntegralTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem trVal_bounded : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α : N.X, ∃ b : ℝ, ∀ mu : N.X, ‖(trVal ν s gm α mu).fst‖ ≤ b ∧ ‖(trVal ν s gm α mu).snd‖ ≤ b := by
  intro V _ _ _ D C _ _ _ _ _ hC N ν hν k hk s gm₀ gm _ hpull α
  obtain ⟨S, hS, hint⟩ := hν
  obtain ⟨n, a, σ, σF, hsc, hsum⟩ := GlobalTheory.T.familySection_span_pullbacks_unitBall V D C hC S hS k hk (ν.eX α) (s.s (ν.eX α))
  refine ⟨∑ i, ‖a i‖, fun mu => ?_⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.translatedDualPoint_of_integralTorusExtPoint V D.toPre C gm₀ gm hpull (ν.eX mu)
  have e := GlobalTheory.T.dualNumberSectionValue_linearCombination V D.toPre C k (ν.eX α) (s.s (ν.eX α)) n a σF hsum _ ν.J ν.good h3
  have hb := fun i => GlobalTheory.T.pulledBackSection_integralValue_dualPoint V D C hC N ν ⟨S, hS, hint⟩ k _ (σ i) (σF i) (hsc i) _ h2 _ h1
  have hv : trVal ν s gm α mu = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i)
      ((lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left ≫
        (DegPre.trF D.toPre C (ν.eX mu)).left) ν.J := e
  rw [hv]
  constructor
  · rw [TrivSqZeroExt.fst_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb i).1
  · rw [TrivSqZeroExt.snd_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, add_zero, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb i).2

end GlobalTheory.MBLow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateSectionValuesBoundedIntegralTangentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_section_values_bounded_integral_tangent : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α : N.X, ∃ b : ℝ, ∀ mu : N.X, ‖(trVal ν s gm α mu).fst‖ ≤ b ∧ ‖(trVal ν s gm α mu).snd‖ ≤ b := by
  exact @GlobalTheory.MBLow.trVal_bounded
end
