module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueThetaOf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AnalyticDictionaryExpHolomorphicOverUnif

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantSectionMulCoordDualNumberPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantSectionMulCoordDualNumberPoint
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanAlg

open ConstTerm

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    {R₀ : Type} [CommRing R₀] [IsDomain R₀] {D₀ : Out.DegPre R₀} {S₀ : Type} [CommRing S₀] {σ₀ : Sp S₀ ⟶ Sp R₀}
    (κ : R →+* S) (ρ : S₀ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ)))
    (g₀ : Out.GtPt D₀ (Over.mk σ₀)) {α : D.toPre.X} {α₀ : D₀.X}
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (k : Fin 4 → D₀.P.L.ι)
    (hj : FormalValue.CohCharts g α jM jf jt)
    (cg : ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) :
    valR (A := S) g.b.left _ (w.s (fun _ => k 2, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (valR (A := S₀) g₀.b.left (LB.wchart D₀.P.L (D₀.famφB α₀) ![k 2, k 0, k 1, k 3])
        (s₀.f ![k 2, k 0, k 1, k 3]) *
        valR (A := S₀) (𝟙 _) (LB.wchart D₀.P.L (Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀) k) ((g₀.s α₀).s k).val) := by
  have hφ : ∀ i, FormalValue.coordφ g α i ≫ φ =
      spMap ρ ≫ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) := hg.1
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have hq₀ := comp_famφB D₀ g₀.b α₀
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have hk : ∀ i, ⊤ ≤ (show Sp S₀ ⟶ _ from Out.DegPre.gtφT D₀ (Over.mk σ₀) g₀.b α₀ i) ⁻¹ᵁ D₀.P.L.U (k i) :=
    fun i => cg.trans (LB.wchart_le _ _ _ i)
  have ek : ![k 2, k 0, k 1, k 3] = fun i => k (![2, 0, 1, 3] i) := by
    funext i; fin_cases i <;> rfl
  rw [ek]
  subst ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have cf : ⊤ ≤ (show Sp S₀ ⟶ _ from g₀.b.left) ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) :=
    fun z hz => Set.mem_iInter.2 fun i =>
      (congrArg (fun q => q z ∈ D₀.P.L.U (k (![2, 0, 1, 3] i))) (hq₀ i)).mpr (hk _ hz)
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      (FormalValue.valR_spMap ρ (show Sp S₀ ⟶ _ from g₀.b.left) _ cf _)
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    (valR_pullGen ρ (g₀.s α₀) k cg))
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₅] at e₁
  rw [map_mul, ← _root_.mul_assoc (κ r)]
  refine Eq.trans ?_ (congrArg (· * _) e₁)
  exact (congrArg (_ * ·) (_root_.mul_left_comm _ _ _)).trans
    ((_root_.mul_assoc _ _ _).symm.trans (_root_.mul_assoc _ _ _).symm)

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (j : ℕ) (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) (jM : W.P.D.toPre.P.L.ι) (jf jt : Fin 4 → W.P.D.toPre.P.L.ι) (jt₀ : Fin 4 → a.D₀.P.L.ι), TanRel W ν g₁ → IsConstMul W j x s₀ f r → FormalValue.CohCharts g₁ (W.e x) jM jf jt → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀ → valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ (W.w.s (fun _ => jt₀ 2, jM)).val ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e x) jt) = TrivSqZeroExt.inl r * constEps (valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB x) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀) ((ν.s x).s jt₀).val) := by
  intro E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν g₁ j x s₀ f r jM jf jt jt₀ hg hf hj hc
  have := isLocalRing_dual ℂ⟦X⟧
  exact core (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) constEps W.w g₁ ν (hg x) s₀ f r (fun p => hf _ p _) jM jf jt jt₀
    hj hc

end GlobalTheory.ConstTanAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantSectionMulCoordDualNumberPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantSection_mul_coord_dualNumberPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (j : ℕ) (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) (jM : W.P.D.toPre.P.L.ι) (jf jt : Fin 4 → W.P.D.toPre.P.L.ι) (jt₀ : Fin 4 → a.D₀.P.L.ι), TanRel W ν g₁ → IsConstMul W j x s₀ f r → FormalValue.CohCharts g₁ (W.e x) jM jf jt → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀ → valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ (W.w.s (fun _ => jt₀ 2, jM)).val ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e x) jt) = TrivSqZeroExt.inl r * constEps (valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB x) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) jt₀) ((ν.s x).s jt₀).val) := by
  first | exact @GlobalTheory.ConstTanAlg.main | exact GlobalTheory.ConstTanAlg.main | (intros; apply GlobalTheory.ConstTanAlg.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FirstOrderJetConstSectionMulCoordinate
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FirstOrderJetConstSectionMulCoordinate
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanJet

open FrameValue

theorem jet_comp_equiv {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    (e : V' ≃L[ℂ] V) (F : V → ℂ) (z : V') : jet (fun w => F (e w)) z = jet F (e z) := by
  have h := e.comp_right_fderiv (f := F) (x := 0)
  rw [map_zero] at h
  ext
  · simp
  · rw [snd_jet, snd_jet]
    exact congrArg (fun q : V' →L[ℂ] ℂ => q z) h

theorem valR_eq_jet {g : ℕ} {X : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {z : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e z v) (U : X.Opens) (hU : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR v U f = jet (fun w => valAt' (e w) U f) z := by
  ext
  · rw [fst_jet, ← hd.1]
    exact (FormalValue.valR_spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom v U hU f).symm
  · rw [snd_jet, ← hd.2 U hU f, valR, dite_eq_left hU]

theorem frameProd_mul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {n : ℕ} (u : HolUnif A L n) (j : ℕ)
    (c z : Fin n → ℂ) (k : Fin 4 → L.ι) (hk : ∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ L.U (k i)) :
    FrameValue.frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] ![k 2, k 0, k 1, k 3] *
      FrameValue.frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
  have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
  have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
  have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
  have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
  simp only [FrameValue.frameProd, Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
    zpow_neg, zpow_one, zpow_natCast, add_comm z c]
  field_simp

theorem jet_sec_mul_coord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (jt₀ : Fin 4 → a.D₀.P.L.ι), IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (h.symm z)).b.left)) z₀ ν.b.left → (∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (Λ.ex0 (h.symm 0)) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (Λ.ex0 (h.symm z)) x j) 0 z₀)) → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀ → valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀) ((ν.s (Λ.ε α)).s jt₀).val = jet (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) (h.symm z₀) * jet (fun v : Λ.A.V => Λ.u.fr (jt₀ 2) v.2) (h.symm z₀) ^ j := by
  intro E _ _ _ H _ D l c O _ β _ _ b a Λ g h z₀ ν j α s₀ jt hd hs hj
  have hU : ⊤ ≤ (show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    intro y hy
    refine Set.mem_iInter.2 fun i => ?_
    have h₁ := Set.mem_iInter.1 (hj hy) (![2, 0, 1, 3] i)
    have h₂ : (![jt 2, jt 0, jt 1, jt 3] : Fin 4 → _) i = jt (![2, 0, 1, 3] i) := by fin_cases i <;> rfl
    rw [h₂]
    exact (congrArg (fun q => q y ∈ a.D₀.P.L.U (jt (![2, 0, 1, 3] i)))
      (ConstTerm.comp_famφB a.D₀ ν.b (Λ.ε α) i)).mpr h₁
  have h0 : ⊤ ≤ (Λ.u.ex (0 : Λ.A.V).2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] := by
    have h₁ := FormalValue.top_le_comp hU (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    have h₂ := hd.1.trans (Λ.ex0_b (h.symm 0))
    rw [map_zero] at h₂
    exact h₂ ▸ h₁
  obtain ⟨ho, hh⟩ := Λ.u.hol _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  have hn : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ
      LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] :=
    (ho.preimage continuous_snd).mem_nhds h0
  have lf := ConstTerm.isLift_famφB Λ.u (Λ.ct α)
  have hk : ∀ z, ⊤ ≤ (Λ.u.ex z).left ⁻¹ᵁ LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt 2, jt 0, jt 1, jt 3] →
      ∀ i, ⊤ ≤ (Λ.u.ex (![Λ.A.ct α + z, Λ.A.ct α, z, 0] i)).left ⁻¹ᵁ a.D₀.P.L.U (jt i) := fun z hz i => by
    have h₁ := ((lf z).le_iff _).1 hz
    fin_cases i
    exacts [add_comm z (Λ.A.ct α) ▸ h₁ 1, h₁ 2, h₁ 0, h₁ 3]
  have hg : ∀ᶠ v : Λ.A.V in nhds 0, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (Λ.ex0 v).b (Λ.ε α)) jt :=
    hn.mono fun v hv => ((gtHol_isLift a.D₀ Λ.u _ _ _ _ (Λ.ct α) (Λ.ex0_b v)).le_iff jt).2 (hk _ hv)
  obtain ⟨hc₁, hc₂⟩ := (analyticDictionaryExp_holomorphic_over_unif E H D l c O β b a Λ).2 (Λ.ε α) jt
  simp only [LinearEquiv.symm_apply_apply] at hc₂
  have dF : DifferentiableAt ℂ (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) 0 :=
    (hh.differentiableAt (ho.mem_nhds h0)).comp (0 : Λ.A.V) differentiableAt_snd
  have dG : DifferentiableAt ℂ (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) 0 := hc₁.differentiableAt hg
  have dfn : Differentiable ℂ (Λ.fn j α s₀) := by
    have := differentiable_secVal a.D₀.P.isLB s₀ (𝟙 _) (q := id) differentiable_id
      (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0])
      (fun k => by fin_cases k <;> simp <;> fun_prop) (fun w => by rw [id, Category.comp_id]; exact lf w)
    simp only [id, Category.comp_id] at this
    exact this
  have dP : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) 0 := by
    have : Differentiable ℂ (fun z : Λ.A.V => z.1 α) := (Λ.A.evalCLM α).differentiable.comp differentiable_fst
    exact ((dfn.comp differentiable_snd).fun_mul (this.const_mul _).cexp) 0
  have dQ : DifferentiableAt ℂ (fun v : Λ.A.V => Λ.u.fr (jt 2) v.2) 0 :=
    ((Λ.u.fr_hol (jt 2)).differentiableAt ((Λ.u.hol _ 0).1.mem_nhds (hk _ h0 2))).comp (0 : Λ.A.V)
      differentiableAt_snd
  have e₁ := valR_eq_jet hd _ hU (s₀.f ![jt 2, jt 0, jt 1, jt 3])
  simp only [Λ.ex0_b] at e₁
  replace e₁ := e₁.trans (jet_comp_equiv h.symm
    (fun v : Λ.A.V => valAt' (Λ.u.ex v.2).left _ (s₀.f ![jt 2, jt 0, jt 1, jt 3])) z₀)
  have e₂ := (hs (Λ.ε α) jt hj).trans (jet_comp_equiv h.symm (fun v : Λ.A.V => chiVal (Λ.ex0 v) (Λ.ε α) jt) z₀)
  refine (congrArg₂ (· * ·) e₁ e₂).trans ?_
  rw [← jet_mul dF dG, ← jet_pow dQ, ← jet_mul dP (dQ.fun_pow j)]
  refine jet_congr ?_ _
  filter_upwards [hn, hg] with v hv hv'
  refine (congrArg₂ (· * ·) (valAt'_sec a.D₀.P.isLB s₀ (lf v.2) hv) (hc₂ v hv')).trans ?_
  rw [← frameProd_mul Λ.u j (Λ.A.ct α) v.2 jt (hk _ hv), _root_.mul_mul_mul_comm]
  rfl

end GlobalTheory.ConstTanJet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FirstOrderJetConstSectionMulCoordinateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstOrderJet_constSection_mul_coordinate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (jt₀ : Fin 4 → a.D₀.P.L.ι), IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Λ.ex0 (h.symm z)).b.left)) z₀ ν.b.left → (∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (Λ.ex0 (h.symm 0)) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (Λ.ex0 (h.symm z)) x j) 0 z₀)) → ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀ → valR (A := DualNumber ℂ) ν.b.left (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) (s₀.f ![jt₀ 2, jt₀ 0, jt₀ 1, jt₀ 3]) * valR (A := DualNumber ℂ) (𝟙 _) (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) jt₀) ((ν.s (Λ.ε α)).s jt₀).val = jet (fun v : Λ.A.V => Λ.fn j α s₀ v.2 * eTwoPi (v.1 α)) (h.symm z₀) * jet (fun v : Λ.A.V => Λ.u.fr (jt₀ 2) v.2) (h.symm z₀) ^ j := by
  first | exact @GlobalTheory.ConstTanJet.jet_sec_mul_coord | exact GlobalTheory.ConstTanJet.jet_sec_mul_coord | (intros; apply GlobalTheory.ConstTanJet.jet_sec_mul_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentValueEqJetConstantExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentValueEqJetConstantExpansion
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstTanExp

theorem approx {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
    {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G)
    {e j : ℕ} {σ : Out.H0 U.LG.L j} {f : ∀ α : D.toPre.X, D.toPre.SecB j α} (h : U.ExpandsAt e j σ f)
    {K : Type} (q : K ≃ D.toPre.X) : ∃ F : Finset K, ∀ (S : Type) [CommRing S] [IsLocalRing S] (J : Ideal S)
      [IsAdicComplete J S] (s : Sp S ⟶ Sp R) (g : Out.GtPt D.toPre (Over.mk s)) (x : Sp S ⟶ G.left),
      FormalValue.IsFormalPt U J g x → ∀ (jL : U.LG.L.ι) (jM : D.toPre.P.L.ι), ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL →
      ⊤ ≤ FormalValue.basePt g ⁻¹ᵁ D.toPre.P.L.U jM → ∀ (ω τ φ p : S) (B : K → S), IsUnit ω → IsUnit τ →
      ω * τ = (FormalValue.tau U J x jL jM).val * φ →
      (∀ α jf jt, FormalValue.CohCharts g (q α) jM jf jt →
        ω ^ j * (FormalValue.famVal g (f (q α)) jf * FormalValue.coordVal g (q α) jt) = B α * φ ^ j) →
      FormalValue.secVal U σ x jL = p * τ ^ j → p - ∑ α ∈ F, B α ∈ J ^ (e + 1) := by
  obtain ⟨F, hF⟩ := FormalValue.map_secVal_eq U h
  refine ⟨F.map q.symm.toEmbedding, fun S _ _ J _ s g x hx jL jM hL hM ω τ φ p B hω hτ e₁ hB hp => ?_⟩
  haveI := isLocalRing_quotient_pow (ne_top_of_isHausdorff J) e
  choose jf jt hc using FormalValue.exists_cohCharts g jM hM
  have e₂ := Ideal.Quotient.eq.1 ((hF S J s g x hx _ (Ideal.Quotient.mk _) Ideal.mk_ker.ge).2
    ((F.map q.symm.toEmbedding).map q.toEmbedding) jL jM jf jt
    (fun α hα => Finset.mem_map.2 ⟨q.symm α, Finset.mem_map_of_mem _ hα, q.apply_symm_apply α⟩) hL hM
    (fun α _ => hc α))
  rw [Finset.sum_map, hp] at e₂
  have e₃ : ω ^ j * ∑ α ∈ F.map q.symm.toEmbedding, FormalValue.famVal g (f (q α)) (jf (q α)) *
      FormalValue.coordVal g (q α) (jt (q α)) = (∑ α ∈ F.map q.symm.toEmbedding, B α) * φ ^ j := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => hB α _ _ (hc _)
  rw [← Ideal.unit_mul_mem_iff_mem _ ((hω.mul hτ).pow j)]
  have e₄ := Ideal.mul_mem_left _ (ω ^ j) e₂
  have e₅ : (ω * τ) ^ j = (FormalValue.tau U J x jL jM).val ^ j * φ ^ j := by rw [e₁, mul_pow]
  refine (congrArg (· ∈ J ^ (e + 1)) ?_).mp e₄
  rw [mul_sub, mul_sub, mul_left_comm (ω ^ j) (_ ^ j)]
  refine congrArg₂ (· - ·) (by ring) ((congrArg (_ * ·) e₃).trans ?_)
  rw [e₅]
  ring

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}
  (Ξ : ConstPts W Λ)

theorem exists_charts (v : Λ.A.V) : ∃ (jM : W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι),
    ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) ∧
    ⊤ ≤ (Λ.u.ex v.2).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex v.2).left :=
    ((Ξ.g_rel v 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b v))
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g v).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex v.2).left
  refine ⟨jM, _, (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ?_, hM⟩, h₀⟩
  exact (congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) hb).mpr (FormalValue.top_le_comp h₀ _ trivial)

theorem isUnit_frame (v : Λ.A.V) (k : W.P.U.LG.L.ι) (h : ⊤ ≤ (Ξ.x v).left ⁻¹ᵁ W.P.U.LG.L.U k) :
    IsUnit (Ξ.τ v k) := by
  obtain ⟨jM, j₀, hj, h₀⟩ := exists_charts Ξ v
  refine isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq v k jM j₀ h hj)).mpr ?_)
  exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne j₀ v.2 h₀)).map _)

theorem differentiable_term (j : ℕ) (α : Λ.A.X) (s : a.D₀.SecB j (Λ.ε α)) :
    Differentiable ℂ fun u : Λ.A.V => Λ.fn j α s u.2 * eTwoPi (u.1 α) := by
  have h₁ := FrameValue.differentiable_secVal (u := Λ.u) a.D₀.P.isLB s (𝟙 _) (q := id) differentiable_id
    (z := fun z => ![z, z + Λ.A.ct α, Λ.A.ct α, 0]) (fun k => by fin_cases k <;> simp <;> fun_prop)
    (fun w => by rw [id, Category.comp_id]; exact ConstTerm.isLift_famφB Λ.u (Λ.ct α) w)
  simp only [id, Category.comp_id] at h₁
  have h₂ : Differentiable ℂ (fun z : Λ.A.V => z.1 α) := (Λ.A.evalCLM α).differentiable.comp differentiable_fst
  exact (h₁.comp differentiable_snd).fun_mul (h₂.const_mul _).cexp

end Points

theorem exists_eq_mul_pow {S : Type} [CommRing S] (s : S) {t : S} (ht : IsUnit t) (j : ℕ) : ∃ p, s = p * t ^ j := by
  obtain ⟨p, hp⟩ := (ht.pow j).dvd (a := s)
  exact ⟨p, hp.trans (_root_.mul_comm _ _)⟩

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ W.t.G.left) (z : Λ.A.V) (jL : W.P.U.LG.L.ι) (jM : W.P.D.toPre.P.L.ι) (ω φ₁ τ : DualNumber ℂ⟦X⟧) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v → ⊤ ≤ v ⁻¹ᵁ W.P.U.LG.L.U jL → ⊤ ≤ FormalValue.basePt g₁ ⁻¹ᵁ W.P.D.toPre.P.L.U jM → IsUnit ω → IsUnit τ → ω * τ = (FormalValue.tau W.P.U.toUnifPre idealEps v jL jM).val * φ₁ → (∀ (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧) jf jt, IsConstMul W j (Λ.ε α) s₀ f r → FormalValue.CohCharts g₁ (W.e (Λ.ε α)) jM jf jt → ω ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e (Λ.ε α)) jt) = TrivSqZeroExt.inl r * constEps (jet (fun u : Λ.A.V => Λ.fn j α s₀ u.2 * eTwoPi (u.1 α)) z) * φ₁ ^ j) → HasConstExp W σ → ∃ (x : Λ.A.V → ℂ⟦X⟧) (y : DualNumber ℂ⟦X⟧), IsJet x z y ∧ (∀ u k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k → FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = x u * Ξ.τ u k ^ j) ∧ FormalValue.secVal W.P.U.toUnifPre σ v jL = y * τ ^ j := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ g₁ v z jL jM ω φ₁ τ j σ hv hL hM hω hτ e₁ hB ⟨f, hf, hs⟩
  have hJ : (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) = Ideal.span {PowerSeries.X} := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
  haveI : IsAdicComplete ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) ℂ⟦X⟧ := by
    rw [hJ]; infer_instance
  haveI := isAdicComplete_idealEps
  haveI := isLocalRing_dual ℂ⟦X⟧
  choose s₀ r hs using fun α : Λ.A.X => hs (Λ.ε α)
  choose F hF using fun e => approx W.P.U.toUnifPre (hf e) (Λ.ε.trans W.e).toEquiv
  have key : ∀ e u k p, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k →
      FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = p * Ξ.τ u k ^ j →
      p - ∑ α ∈ F e, r α * PowerSeries.C (Λ.fn j α (s₀ α) u.2 * eTwoPi (u.1 α)) ∈
        (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) ^ (e + 1) := by
    intro e u k p hk hp
    obtain ⟨iM, i₀, hi, -⟩ := exists_charts Ξ u
    refine hF e _ _ _ (Ξ.g u) _ (Ξ.x_fm u) k iM hk (fun y hy => (hi hy).2) _ _ _ p _
      (FormalValue.isUnit_valR (A := ℂ⟦X⟧) (Ξ.g u).b.left _ hi (W.w.s (fun _ => i₀, iM)))
      (isUnit_frame Ξ u k hk) (Ξ.τ_eq u k iM i₀ hk hi) (fun α jf jt hc => ?_) hp
    refine (ConstTerm.main h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α (s₀ α) _ (r α) (hs α) u iM i₀ jf jt hc hi).trans ?_
    rw [map_mul, map_pow, _root_.mul_assoc]
  have hk : ∀ u, ∃ k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k := fun u => by
    obtain ⟨k, hk⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x u).left) (cpt ℂ⟦X⟧))
    exact ⟨k, (top_le_iff_cpt _ _).2 hk⟩
  choose k hk using hk
  choose x hx using fun u => exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left (k u))
    (isUnit_frame Ξ u (k u) (hk u)) j
  obtain ⟨y, hy⟩ := exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ v jL) hτ j
  refine ⟨x, y, isJet_of_approx fun e => ⟨_, _, IsJet.sum (F e) fun α _ =>
    (isJet_C (differentiable_term j α (s₀ α) 0) z).const_mul (r α), fun u => ?_, ?_⟩, fun u k' hk' => ?_, hy⟩
  · have := key e u _ _ (hk u) (hx u)
    rwa [hJ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  · exact hF e _ _ _ g₁ v hv jL jM hL hM ω τ φ₁ y _ hω hτ e₁ (fun α jf jt hc => hB α (s₀ α) _ (r α) jf jt (hs α) hc) hy
  · obtain ⟨p, hp⟩ := exists_eq_mul_pow (FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k')
      (isUnit_frame Ξ u k' hk') j
    rw [hp]
    refine congrArg (· * _) (FormalValue.eq_of_forall_mk_eq
      ((Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ ℂ⟦X⟧)) fun e => ?_)
    exact (Ideal.Quotient.eq.2 (key e u _ _ hk' hp)).trans (Ideal.Quotient.eq.2 (key e u _ _ (hk u) (hx u))).symm

end GlobalTheory.ConstTanExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentValueEqJetConstantExpansionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentValue_eq_jet_constantExpansion : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ W.t.G.left) (z : Λ.A.V) (jL : W.P.U.LG.L.ι) (jM : W.P.D.toPre.P.L.ι) (ω φ₁ τ : DualNumber ℂ⟦X⟧) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), FormalValue.IsFormalPt W.P.U.toUnifPre idealEps g₁ v → ⊤ ≤ v ⁻¹ᵁ W.P.U.LG.L.U jL → ⊤ ≤ FormalValue.basePt g₁ ⁻¹ᵁ W.P.D.toPre.P.L.U jM → IsUnit ω → IsUnit τ → ω * τ = (FormalValue.tau W.P.U.toUnifPre idealEps v jL jM).val * φ₁ → (∀ (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧) jf jt, IsConstMul W j (Λ.ε α) s₀ f r → FormalValue.CohCharts g₁ (W.e (Λ.ε α)) jM jf jt → ω ^ j * (FormalValue.famVal g₁ f jf * FormalValue.coordVal g₁ (W.e (Λ.ε α)) jt) = TrivSqZeroExt.inl r * constEps (jet (fun u : Λ.A.V => Λ.fn j α s₀ u.2 * eTwoPi (u.1 α)) z) * φ₁ ^ j) → HasConstExp W σ → ∃ (x : Λ.A.V → ℂ⟦X⟧) (y : DualNumber ℂ⟦X⟧), IsJet x z y ∧ (∀ u k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k → FormalValue.secVal W.P.U.toUnifPre σ (Ξ.x u).left k = x u * Ξ.τ u k ^ j) ∧ FormalValue.secVal W.P.U.toUnifPre σ v jL = y * τ ^ j := by
  first | exact @GlobalTheory.ConstTanExp.main | exact GlobalTheory.ConstTanExp.main | (intros; apply GlobalTheory.ConstTanExp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentGenericFibreOfThetaSections
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentGenericFibreOfThetaSections
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.GenericTan

section Charts

variable {R : Type} [CommRing R] [IsLocalRing R] {Z Z' : Scheme.{0}} {L : LB Z}

theorem valR_cocycle (hL : L.IsLB) (x : Sp R ⟶ Z) {i j k : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valR x (L.U i ⊓ L.U j) (L.g i j).val * valR x (L.U j ⊓ L.U k) (L.g j k).val =
      valR x (L.U i ⊓ L.U k) (L.g i k).val := by
  apply toStkA_injective
  rw [map_mul, FormalValue.toStkA_valR_eq_gs x (L.U i ⊓ L.U j) _ (fun _ hz => ⟨hi hz, hj hz⟩) _, gs_unit x (cpt R) (L.U i ⊓ L.U j) ⟨hi trivial, hj trivial⟩ (L.g i j),
    FormalValue.toStkA_valR_eq_gs x (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩) _, gs_unit x (cpt R) (L.U j ⊓ L.U k) ⟨hj trivial, hk trivial⟩ (L.g j k),
    FormalValue.toStkA_valR_eq_gs x (L.U i ⊓ L.U k) _ (fun _ hz => ⟨hi hz, hk hz⟩) _, gs_unit x (cpt R) (L.U i ⊓ L.U k) ⟨hi trivial, hk trivial⟩ (L.g i k), ← Units.val_mul,
    gm_cocycle hL x _ (hi trivial) (hj trivial) (hk trivial)]

theorem valR_self (hL : L.IsLB) (x : Sp R ⟶ Z) {j : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [FormalValue.toStkA_valR_eq_gs x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩) _, gs_unit x (cpt R) (L.U j ⊓ L.U j) ⟨h trivial, h trivial⟩ (L.g j j), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem isFrm_spread (hL : L.IsLB) (x : Sp R ⟶ Z) {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) {a : R} (ha : IsUnit a) :
    IsFrm L x (fun j => valR x (L.U j ⊓ L.U k) (L.g j k).val * a) := by
  refine ⟨fun j hj => (FormalValue.isUnit_valR x (L.U j ⊓ L.U k) (fun _ hz => ⟨hj hz, hk hz⟩) _).mul ha,
    fun j j' h => ?_⟩
  rw [← _root_.mul_assoc, valR_cocycle hL x (fun _ hz => (h hz).1) (fun _ hz => (h hz).2) hk]

theorem sval_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {j k : L.ι}
    (hj : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) :
    ArcPts.sval s q j = valR (q ≫ p) (L.U j ⊓ L.U k) (L.g j k).val ^ m * ArcPts.sval s q k := by
  have wj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => hj hz
  have wk : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => k) :=
    fun z hz => Set.mem_iInter.2 fun _ => hk hz
  apply toStkA_injective
  rw [map_mul, map_pow, FormalValue.toStkA_valR_eq_gs (q ≫ p) (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩) _, gs_unit (q ≫ p) (cpt R) (L.U j ⊓ L.U k) ⟨hj trivial, hk trivial⟩ (L.g j k)]
  refine (FormalValue.toStkA_valR_eq_gs q _ _ wj _).trans ((sec_trans s q _ (wj trivial) (wk trivial)).trans
    (congrArg₂ (· * ·) ?_ (FormalValue.toStkA_valR_eq_gs q _ _ wk _).symm))
  rw [trF, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]

theorem hasVal_of_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {τ : L.ι → R}
    (hτ : IsFrm L (q ≫ p) τ) {k : L.ι} (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) {r : R}
    (h : ArcPts.sval s q k = r * τ k ^ m) : HasVal s q τ r := fun j hj => by
  rw [sval_chart s q hj hk, h, hτ.2 j k (fun _ hz => ⟨hj hz, hk hz⟩), mul_pow, mul_left_comm]

def pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) : SecP L p m :=
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => p) j ≤ p ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  { f := fun j => (p.appLE _ _ (l j)).hom (σ.f j)
    compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
      have v : ∀ j : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => p) j →
          gs (𝟙 Z') y _ ((p.appLE _ _ (l j)).hom (σ.f j)) =
          gs (𝟙 Z' ≫ p) y (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j) (σ.f j) := fun j hj =>
        (gs_res (𝟙 Z') y (l j) hj _).trans (gs_pull _ p y _ (l j hj) _)
      refine ((gs_res (𝟙 Z') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Z') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Z') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Z') y j j' hy.1 hy.2)))
          ((gs_res (𝟙 Z') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans σ (𝟙 Z' ≫ p) y (l j hy.1) (l j' hy.2)]
      simp only [trF, Category.comp_id] }

omit [IsLocalRing R] in
theorem sval_pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) (q : Sp R ⟶ Z') {k : L.ι}
    (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) : ArcPts.sval (pullPow p σ) q k =
      valR (q ≫ p) (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k)) (σ.f (fun _ => k)) :=
  HolHom.valR_appLE q p _ _ _ _ (fun z hz => Set.mem_iInter.2 fun _ => hk hz)

omit [IsLocalRing R] in
theorem le_powChart {x : Sp R ⟶ Z} {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hk hz

end Charts

theorem isTan_of_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (A : AnArc (𝓞 E)) (t : SAB H (Sp ℂ⟦X⟧)) (Φ : GenPts A t gen) (L : RigLB t.G) (x : A.V → (Sp ℂ⟦X⟧ ⟶ t.G.left)) (τ : A.V → L.L.ι → ℂ⟦X⟧) (z : A.V) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ t.G.left) (k₀ : L.L.ι) (τ₁ : DualNumber ℂ⟦X⟧) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom gen), L = t.PP → (∀ u, (Φ.x u).left = gen ≫ x u ∧ ∀ (k : L.L.ι) (k' : t.PP.L.ι), HEq k k' → ⊤ ≤ x u ⁻¹ᵁ L.L.U k → Φ.τ u k' = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k)) → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v = x 0 → ⊤ ≤ v ⁻¹ᵁ L.L.U k₀ → IsUnit τ₁ → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → (∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∀ F, IsDFSum A j α th z F → ∃ (m : ℕ) (σ : Out.H0 L.L j), (∀ u k, ⊤ ≤ x u ⁻¹ᵁ L.L.U k → algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (valR (x u) (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) (σ.f (fun _ => k))) = HahnSeries.single (m : ℤ) (1 : ℂ) * A.FSum j α th u * algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k) ^ j) ∧ ρ (valR v (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k₀)) (σ.f (fun _ => k₀))) = TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) * (TrivSqZeroExt.inl (A.FSum j α th 0) + TrivSqZeroExt.inr F) * ρ τ₁ ^ j) → Φ.IsTan z νK := by
  intro E _ _ _ H _ A t Φ L x τ z v k₀ τ₁ ρ νK hL hx hv hk₀ hτ₁ hρ hε hfst hsnd hsec
  subst hL
  have hρ' := eq_dualMapR _ ρ hρ hε
  have hK : ⊤ ≤ (νK ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U k₀ := by
    rw [hfst]; exact FormalValue.top_le_comp hk₀ _
  haveI := isLocalRing_dual ℂ⸨X⸩
  have hfrm := isFrm_spread t.PP.isLB (νK ≫ pullback.fst _ _) hK (hτ₁.map ρ)
  refine ⟨hsnd, ?_, _, hfrm, fun j _ α th hth F hF => ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, fib, pullback.lift_fst, (hx 0).1, ← hv, ← Category.assoc, ← Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext1
      refine RingHom.ext fun a => ?_
      rw [hρ']
      exact fst_dualMapR _ a
    · rw [Category.assoc, hsnd, fib, pullback.lift_snd, ← Spec.map_comp, ← Spec.map_id]
      congr 1
  · obtain ⟨m, σ, h₁, h₂⟩ := hsec j α th hth F hF
    have key := sval_eq_sum_of_hasVal E H _ A t gen Φ j (pullPow (pullback.fst t.G.hom gen) σ) 1
      (fun _ => HahnSeries.single (m : ℤ) (1 : ℂ)) (fun _ => α) (fun _ => th) (fun _ => hth) (fun u => by
        have e : fib (Φ.x u) ≫ pullback.fst t.G.hom gen = gen ≫ x u := by
          rw [fib, pullback.lift_fst, (hx u).1]
        obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (x u (cpt ℂ⟦X⟧))
        have hk' := (top_le_iff_cpt _ _).2 hk
        have hk'' : ⊤ ≤ (fib (Φ.x u) ≫ pullback.fst t.G.hom gen) ⁻¹ᵁ t.PP.L.U k := by
          rw [e]; exact FormalValue.top_le_comp hk' _
        refine hasVal_of_chart _ _ ?_ hk'' ?_
        · rw [e, ← (hx u).1]; exact Φ.frm u
        · rw [sval_pullPow _ _ _ hk'', e, Fin.sum_univ_one, (hx u).2 k k HEq.rfl hk', ← h₁ u k hk']
          exact FormalValue.valR_spMap _ _ _ (le_powChart hk') _)
      _ _ νK hsnd k₀ hK
    refine hasVal_of_chart _ _ hfrm hK ?_
    rw [sval_pullPow _ _ _ hK, hfst, Fin.sum_univ_one, TrivSqZeroExt.algebraMap_eq_inl] at key
    replace key := (h₂.symm.trans (FormalValue.valR_spMap ρ v _ (le_powChart hk₀) _).symm).trans key
    rw [_root_.mul_assoc] at key
    have hu : IsUnit (TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) : DualNumber ℂ⸨X⸩) :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit (by simp))
    rw [valR_self t.PP.isLB _ hK, _root_.one_mul]
    exact (hu.mul_left_cancel key).symm

end GlobalTheory.GenericTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentGenericFibreOfThetaSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTangent_genericFibre_of_thetaSections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (A : AnArc (𝓞 E)) (t : SAB H (Sp ℂ⟦X⟧)) (Φ : GenPts A t gen) (L : RigLB t.G) (x : A.V → (Sp ℂ⟦X⟧ ⟶ t.G.left)) (τ : A.V → L.L.ι → ℂ⟦X⟧) (z : A.V) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ t.G.left) (k₀ : L.L.ι) (τ₁ : DualNumber ℂ⟦X⟧) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom gen), L = t.PP → (∀ u, (Φ.x u).left = gen ≫ x u ∧ ∀ (k : L.L.ι) (k' : t.PP.L.ι), HEq k k' → ⊤ ≤ x u ⁻¹ᵁ L.L.U k → Φ.τ u k' = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k)) → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v = x 0 → ⊤ ≤ v ⁻¹ᵁ L.L.U k₀ → IsUnit τ₁ → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → (∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∀ F, IsDFSum A j α th z F → ∃ (m : ℕ) (σ : Out.H0 L.L j), (∀ u k, ⊤ ≤ x u ⁻¹ᵁ L.L.U k → algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (valR (x u) (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) (σ.f (fun _ => k))) = HahnSeries.single (m : ℤ) (1 : ℂ) * A.FSum j α th u * algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k) ^ j) ∧ ρ (valR v (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k₀)) (σ.f (fun _ => k₀))) = TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) * (TrivSqZeroExt.inl (A.FSum j α th 0) + TrivSqZeroExt.inr F) * ρ τ₁ ^ j) → Φ.IsTan z νK := by
  first | exact @GlobalTheory.GenericTan.isTan_of_sections | exact GlobalTheory.GenericTan.isTan_of_sections | (intros; apply GlobalTheory.GenericTan.isTan_of_sections <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantTorusExtensionTangentRel
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantTorusExtensionTangentRel
namespace GlobalTheory.ConstTan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem exists_tanRel : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)), ∃ g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧), TanRel W ν g₁ := by
  intro _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W ν
  haveI := isLocalRing_dual ℂ⟦X⟧
  obtain ⟨gp, hw, -, -, hc, -⟩ := W.spec
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_genRelR (A := DualNumber ℂ⟦X⟧) globalFns_holds gp hw
    W.e.symm.toAddEquiv.toAddMonoidHom
    (fun y => by have := hc (W.e.symm y); rwa [LinearEquiv.apply_symm_apply] at this)
    (T := epsR ℂ) (spMap (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧))) (spMap constEps)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun r => dualMapR_inl _ r)).trans (spMap_comp _ _))) ν
  refine ⟨g, fun x => ?_⟩
  have := hg (W.e x)
  rw [show W.e.symm.toAddEquiv.toAddMonoidHom (W.e x) = x from W.e.symm_apply_apply x] at this
  exact this

end GlobalTheory.ConstTan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantTorusExtensionTangentRelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constantTorusExtension_tangentRel : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (ν : Out.GtPt a.D₀ (epsR ℂ)), ∃ g₁ : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧), TanRel W ν g₁ := by
  first | exact @GlobalTheory.ConstTan.exists_tanRel | exact GlobalTheory.ConstTan.exists_tanRel | (intros; apply GlobalTheory.ConstTan.exists_tanRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowMulEqSumConstantExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowMulEqSumConstantExpansion
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.ConstExpSpan

open GlobalTheory.ConstFam GlobalTheory.FieldBaseChange

theorem exists_rep (M : Type) [AddCommGroup M] (j : ℕ) :
    ∃ (C : Type) (rep : C → M), ∀ α, ∃! x, ∃ mu, rep x + j • mu = α := by
  refine ⟨M ⧸ (nsmulAddMonoidHom j : M →+ M).range, Quotient.out, fun α => ⟨QuotientAddGroup.mk α, ?_, ?_⟩⟩
  · obtain ⟨mu, h⟩ := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk α :
      M ⧸ (nsmulAddMonoidHom j : M →+ M).range))
    exact ⟨mu, by rw [show j • mu = _ from h, add_neg_cancel_left]⟩
  · rintro x ⟨mu, rfl⟩
    exact (QuotientAddGroup.out_eq' x).symm.trans (QuotientAddGroup.eq.2 ⟨mu, (neg_add_cancel_left _ _).symm⟩)

def valLin {R Z : Type} [CommRing R] [CommRing Z] [IsLocalRing Z] {Y : Scheme.{0}} (π : Y ⟶ Sp R) (M : LB Y)
    (κ : R →+* Z) (p : Sp Z ⟶ Y) (hp : p ≫ π = spMap κ) (i : M.ι) (hi : ⊤ ≤ p ⁻¹ᵁ M.U i) :
    SecOver π M →ₛₗ[κ] Z where
  toFun s := valR p (M.U i) (LB.Sec.f s i)
  map_add' s t := toStkA_injective (by
    rw [map_add (f := _), FormalValue.toStkA_valR_eq_gs _ _ _ hi, FormalValue.toStkA_valR_eq_gs _ _ _ hi,
      FormalValue.toStkA_valR_eq_gs _ _ _ hi]
    exact gs_add p _ _ (hi trivial) _ _)
  map_smul' r s := toStkA_injective (by
    have H : constVal (p ≫ π) (cpt Z) r = toStkA (cpt Z) (κ r) := by
      rw [hp, ← Category.id_comp (spMap κ)]
      exact (constVal_specMap _ κ _ r).trans (gs_eq (𝟙 _) _ ⊤ trivial _)
    rw [smul_eq_mul, map_mul, FormalValue.toStkA_valR_eq_gs _ _ _ hi, FormalValue.toStkA_valR_eq_gs _ _ _ hi, ← H]
    exact gs_smul π p _ _ (hi trivial) r _)

theorem exists_pow_mul_eq_sum : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), 1 ≤ j → ∃ (N n : ℕ) (r : Fin n → ℂ⟦X⟧) (s : Fin n → Out.H0 W.P.U.LG.L j), (∀ i, HasConstExp W (s i)) ∧ ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (κ : ℂ⟦X⟧ →+* Z) (p : Sp Z ⟶ W.t.G.left) (k : W.P.U.LG.L.ι), p ≫ W.t.G.hom = spMap κ → ⊤ ≤ p ⁻¹ᵁ W.P.U.LG.L.U k → κ PowerSeries.X ^ N * FormalValue.secVal W.P.U.toUnifPre σ p k = ∑ i, κ (r i) * FormalValue.secVal W.P.U.toUnifPre (s i) p k := by
  intro hL E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W j σ hj
  have hW : WitData a W.P.D W.P.oD W.φ W.he W.w W.e :=
    ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1, W.spec.2.2.2.2.1,
      fun F _ _ _ _ uF h₁ h₂ => (W.spec.2.2.2.2.2 F uF h₁ h₂).1⟩
  obtain ⟨C, rep, hrep⟩ := exists_rep a.D₀.X j
  let bas := fun x => Module.Basis.ofVectorSpace ℂ (SecBMod a.D₀ j (rep x))
  have ex := fun i : Σ x, Module.Basis.ofVectorSpaceIndex ℂ (SecBMod a.D₀ j (rep x)) =>
    exists_expandsAt hW hL.globalFns hj W.P.U (rep i.1) (bas i.1 i.2)
  choose m hm using ex
  choose f s hf hE using fun i => hm i (m i) le_rfl
  obtain ⟨N, hN⟩ := exists_pow_smul_mem_span hW hL.globalFns hj W.P.U rep hrep bas m f s hf hE σ
  obtain ⟨n, r, t, ht⟩ := Submodule.mem_span_set'.1 hN
  refine ⟨N, n, r, fun i => (t i).1, fun i => ?_, fun Z _ _ κ p k hp hk => ?_⟩
  · obtain ⟨q, hq⟩ := (t i).2
    refine (congrArg (HasConstExp W) hq).mp ⟨f q, hE q, fun x => ?_⟩
    rcases eq_or_off W.e j (rep q.1) (W.e x) with ⟨mu, h⟩ | h
    · obtain rfl := W.e.injective h
      refine ⟨feTranslate a.D₀ j mu _ (bas q.1 q.2), PowerSeries.X ^ ((m q : ℤ) + expo a j (rep q.1) mu).toNat,
        fun Z _ _ p κ jf j₀ hp hi => ?_⟩
      rw [((hf q).1 mu).2]
      exact ConstThetaSections.valR_smul_pullB hW j _ _ _ Z p κ jf j₀ hp hi
    · refine ⟨(0 : SecBMod a.D₀ j x), 0, fun Z _ _ p κ jf j₀ hp hi => ?_⟩
      rw [(hf q).2 _ h, ← zero_smul ℂ⟦X⟧ (pullB hW j x 0)]
      exact ConstThetaSections.valR_smul_pullB hW j _ _ _ Z p κ jf j₀ hp hi
  · let v := valLin W.t.G.hom
      (LB.LinComb W.P.U.LG.L (K := Fin 1) (fun _ => 𝟙 W.t.G.left) (fun _ => (j : ℤ))) κ p hp (fun _ => k)
      (FormalValue.top_le_secChart hk)
    refine (congrArg (· * _) (map_pow κ _ N).symm).trans ((v.map_smulₛₗ _ σ).symm.trans
      ((congrArg v ht.symm).trans ((map_sum v _ _).trans (Finset.sum_congr rfl fun i _ => v.map_smulₛₗ _ _))))

end GlobalTheory.ConstExpSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowMulEqSumConstantExpansionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_eq_sum_constantExpansion : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ) (σ : Out.H0 W.P.U.LG.L j), 1 ≤ j → ∃ (N n : ℕ) (r : Fin n → ℂ⟦X⟧) (s : Fin n → Out.H0 W.P.U.LG.L j), (∀ i, HasConstExp W (s i)) ∧ ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (κ : ℂ⟦X⟧ →+* Z) (p : Sp Z ⟶ W.t.G.left) (k : W.P.U.LG.L.ι), p ≫ W.t.G.hom = spMap κ → ⊤ ≤ p ⁻¹ᵁ W.P.U.LG.L.U k → κ PowerSeries.X ^ N * FormalValue.secVal W.P.U.toUnifPre σ p k = ∑ i, κ (r i) * FormalValue.secVal W.P.U.toUnifPre (s i) p k := by
  first | exact @GlobalTheory.ConstExpSpan.exists_pow_mul_eq_sum | exact GlobalTheory.ConstExpSpan.exists_pow_mul_eq_sum | (intros; apply GlobalTheory.ConstExpSpan.exists_pow_mul_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentConstantCoordsGenericFibre
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstTan

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}
  {W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ} {Λ : GtAn a}

theorem exists_isUnit_tau (Ξ : ConstPts W Λ) (u : Λ.A.V) :
    ∃ k, ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k ∧ IsUnit (Ξ.τ u k) := by
  obtain ⟨k, hk⟩ := exists_chart W.P.U.LG.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.x u).left) (cpt ℂ⟦X⟧))
  have hk' : ⊤ ≤ (Ξ.x u).left ⁻¹ᵁ W.P.U.LG.L.U k := (top_le_iff_cpt (A := ℂ⟦X⟧) _ _).2 hk
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB ((show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g u).b.left) (cpt ℂ⟦X⟧))
  have h₀ := FrameValue.le_chartAt a.D₀.P.isLB (Λ.u.ex u.2).left
  have hb : (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g u).b.left) ≫ W.φ = spMap (PowerSeries.C (R := ℂ)) ≫ (Λ.u.ex u.2).left :=
    ((Ξ.g_rel u 0).1 2).trans (congrArg (spMap (PowerSeries.C (R := ℂ)) ≫ ·) (Λ.ex0_b u))
  have hj : ⊤ ≤ (show Sp ℂ⟦X⟧ ⟶ _ from (Ξ.g u).b.left) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U
      (fun _ => FrameValue.chartAt a.D₀.P.isLB (Λ.u.ex u.2).left, jM) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ((congrArg (fun q => q (cpt ℂ⟦X⟧) ∈ a.D₀.P.L.U _) hb).mpr
      (FormalValue.top_le_comp h₀ _ trivial)), hM⟩
  refine ⟨k, hk', isUnit_of_mul_isUnit_right ((congrArg IsUnit (Ξ.τ_eq u k jM _ hk' hj)).mpr ?_)⟩
  exact (Units.isUnit _).mul ((Ne.isUnit (Λ.u.fr_ne _ u.2 h₀)).map _)

end

theorem isTan_of_diffHyp : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback W.t.G.hom gen), Ξ.IsGen Φ → DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v.left → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → Φ.IsTan (h.symm z₀) νK := by
  intro h₁ h₂ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ Φ g h z₀ ν v ρ νK hΦ hd hρ hε hν₁ hν₂
  haveI := isLocalRing_dual ℂ⟦X⟧
  haveI := isLocalRing_dual ℂ
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.T.exists_constantTorusExtension_tangentRel h₁ E H D l Xo c O β Y b a χ W ν
  have hf := GlobalTheory.T.constantTangent_eq_formalPoint_transported E H D l Xo c O β Y b a χ W g _ z₀ ν v g₁ hd hg₁
  have hr := GlobalTheory.T.constantTangent_reduction_eq_origin E H D l Xo c O β Y b a χ W Λ g h z₀ ν Ξ v g₁ hd hg₁ hf
  obtain ⟨jL, hL⟩ := exists_chart W.P.U.LG.isLB
    ((show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from v.left) (cpt (DualNumber ℂ⟦X⟧)))
  replace hL : ⊤ ≤ v.left ⁻¹ᵁ W.P.U.LG.L.U jL := (top_le_iff_cpt (A := DualNumber ℂ⟦X⟧) _ _).2 hL
  obtain ⟨jM, hM⟩ := exists_chart W.P.D.toPre.P.isLB
    ((show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from g₁.b.left) (cpt (DualNumber ℂ⟦X⟧)))
  obtain ⟨j₀, h₀⟩ := exists_chart a.D₀.P.isLB ((show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) (cpt (DualNumber ℂ)))
  have h₀' : ⊤ ≤ (show Sp (DualNumber ℂ) ⟶ _ from ν.b.left) ⁻¹ᵁ a.D₀.P.L.U j₀ := (top_le_iff_cpt _ _).2 h₀
  have hb : (show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from g₁.b.left) ≫ W.φ = spMap constEps ≫ ν.b.left := (hg₁ 0).1 2
  have hj : ⊤ ≤ (show Sp (DualNumber ℂ⟦X⟧) ⟶ _ from g₁.b.left) ⁻¹ᵁ
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 ((congrArg (fun q => q (cpt (DualNumber ℂ⟦X⟧)) ∈ a.D₀.P.L.U _) hb).mpr
      (FormalValue.top_le_comp h₀' _ trivial)), hM⟩
  obtain ⟨ω, hω⟩ := FormalValue.isUnit_valR (A := DualNumber ℂ⟦X⟧) g₁.b.left _ hj (W.w.s (fun _ => j₀, jM))
  have hz : ⊤ ≤ (Λ.u.ex 0).left ⁻¹ᵁ a.D₀.P.L.U j₀ := by
    have e := hd.1.1.trans (Λ.ex0_b (h.symm 0))
    rw [map_zero] at e
    exact (congrArg (fun q : Sp ℂ ⟶ _ => ⊤ ≤ q ⁻¹ᵁ a.D₀.P.L.U j₀) e).mp (FormalValue.top_le_comp h₀' _)
  let φ₁ := constEps (jet (fun u : Λ.A.V => Λ.u.fr j₀ u.2) (h.symm z₀))
  have hφ : IsUnit φ₁ := IsUnit.map _ (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    rw [fst_jet]; exact Ne.isUnit (Λ.u.fr_ne j₀ 0 hz)))
  let τ₁ : DualNumber ℂ⟦X⟧ := ω⁻¹.val * ((FormalValue.tau W.P.U.toUnifPre idealEps v.left jL jM).val * φ₁)
  have hτ : IsUnit τ₁ := (Units.isUnit _).mul ((Units.isUnit _).mul hφ)
  refine GlobalTheory.T.isTangent_genericFibre_of_thetaSections E H Λ.A W.t Φ W.P.U.LG (fun u => (Ξ.x u).left) Ξ.τ (h.symm z₀) v.left jL τ₁ ρ νK W.P.bundle hΦ hr hL
    hτ hρ hε hν₁ hν₂ fun j _ α th hth F hF => ?_
  obtain ⟨m, σ, hσ⟩ := GlobalTheory.T.exists_section_values_formalThetaSum h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ j α th hth
  refine ⟨m, σ, fun u k hk => hσ u k hk, ?_⟩
  obtain ⟨N, n, r, s, hs, hsum⟩ := GlobalTheory.T.exists_pow_mul_eq_sum_constantExpansion h₁ E H D l Xo c O β Y b a χ W j σ NeZero.one_le
  choose x y hx hxv hy using fun i => GlobalTheory.T.tangentValue_eq_jet_constantExpansion h₁ h₂ E H D l Xo c O β Y b a χ W Λ Ξ g₁ v.left (h.symm z₀) jL jM ω φ₁ τ₁
    j (s i) hf hL (fun z hz => (hj hz).2) ω.isUnit hτ (Units.mul_inv_cancel_left _ _)
    (fun α s₀ f r jf jt hc hcoh => by
      choose k hk using fun i => exists_chart a.D₀.P.isLB
        ((show Sp (DualNumber ℂ) ⟶ _ from Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α) i) (cpt (DualNumber ℂ)))
      have ht : ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) ![k 0, k 1, j₀, k 3] :=
        (top_le_iff_cpt (𝟙 (Sp (DualNumber ℂ)))
          (LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b (Λ.ε α)) ![k 0, k 1, j₀, k 3])).2
          (Set.mem_iInter.2 fun i => by
            fin_cases i
            exacts [hk 0, hk 1, h₀, hk 3])
      have e₁ := GlobalTheory.T.constantSection_mul_coord_dualNumberPoint E H D l Xo c O β Y b a χ W ν g₁ j _ s₀ f r jM jf jt _ hg₁ hc hcoh ht
      have e₂ := GlobalTheory.T.firstOrderJet_constSection_mul_coordinate E H D l c O β b a Λ g h z₀ ν j α s₀ _ hd.1 hd.2.1 ht
      rw [e₂, map_mul, map_pow] at e₁
      rw [hω]
      exact e₁.trans (_root_.mul_assoc _ _ _).symm) (hs i)
  have hJ := IsJet.sum Finset.univ fun i _ => (hx i).const_mul (r i)
  have hX : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ^ N = HahnSeries.single (N : ℤ) (1 : ℂ) := by
    rw [LaurentSeries.coe_algebraMap, PowerSeries.coe_X, HahnSeries.single_pow]; simp
  have e₀ : HahnSeries.single ((N : ℤ) + m) (1 : ℂ) =
      (HahnSeries.single (N : ℤ) (1 : ℂ) * HahnSeries.single (m : ℤ) (1 : ℂ) : ℂ⸨X⸩) := by
    rw [HahnSeries.single_mul_single, _root_.one_mul]
  have key := hJ.dualMapR_eq (N + m) (fun u => Λ.A.FSum j α th u) (fun u => by
    obtain ⟨k, hk, hu⟩ := exists_isUnit_tau Ξ u
    have e := congrArg (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)
      (hsum ℂ⟦X⟧ (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (Ξ.x u).left k (Over.w (Ξ.x u)) hk)
    simp only [hxv _ u k hk, Algebra.algebraMap_self, RingHom.id_apply, ← _root_.mul_assoc, ← Finset.sum_mul] at e
    rw [map_mul, map_mul, map_pow, map_pow, hσ u k hk, hX] at e
    refine ((hu.map (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)).pow j).mul_right_cancel (e.symm.trans ?_)
    rw [e₀]; ring) F hF
  have e := congrArg ρ (hsum _ (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧)) v.left jL (Over.w v) hL)
  simp only [hy, TrivSqZeroExt.algebraMap_eq_inl, ← _root_.mul_assoc, ← Finset.sum_mul] at e
  rw [← eq_dualMapR _ ρ hρ hε] at key
  rw [map_mul, map_mul, map_pow, map_pow, key, hρ, TrivSqZeroExt.inl_pow, hX, e₀, TrivSqZeroExt.inl_mul] at e
  have hu : IsUnit (TrivSqZeroExt.inl (HahnSeries.single (N : ℤ) (1 : ℂ)) : DualNumber ℂ⸨X⸩) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit (by simp))
  refine hu.mul_left_cancel (e.trans ?_)
  ring

end GlobalTheory.ConstTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTangentConstantCoordsGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTangent_constant_coords_generic_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (g : ℕ) (h : Λ.A.V ≃L[ℂ] (Fin g → ℂ)) (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback W.t.G.hom gen), Ξ.IsGen Φ → DiffHyp W (fun z => Λ.ex0 (h.symm z)) z₀ ν v → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v.left → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → Φ.IsTan (h.symm z₀) νK := by
  first | exact @GlobalTheory.ConstTan.isTan_of_diffHyp | exact GlobalTheory.ConstTan.isTan_of_diffHyp | (intros; apply GlobalTheory.ConstTan.isTan_of_diffHyp <;> assumption)
end
