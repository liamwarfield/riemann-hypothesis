module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningFamilyMulTwistingSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningFamilyMulTwistingSection
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SpanShortProd

theorem eLpNorm_homN_ne_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (x : ℝ)
    {D : D7} {W : HSp D} (dict : GA D W → Σ k, Frame (V.X k).Ψ r) (μ : MeasureTheory.Measure (AutQ W))
    (hμ : μ Set.univ ≤ 1) (G : WTZ E) (f : Rul Xo c) (hf : rdU V f ∈ holSub V.X (GlobalTheory.AllWt.modelWt V G)) :
    MeasureTheory.eLpNorm' (fun q : AutQ W => GlobalTheory.AllWt.homN V x G f (dict q.out)) 2 μ ≠ ⊤ := by
  have hb : ∀ q : AutQ W, ‖GlobalTheory.AllWt.homN V x G f (dict q.out)‖ₑ ≤
      ENNReal.ofReal (GlobalTheory.AllWt.lieFacZ Dw x G) * supE V.X (GlobalTheory.AllWt.modelWt V G) (rdU V f) := by
    intro q
    rw [Real.enorm_eq_ofReal (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _), GlobalTheory.AllWt.homN,
      ENNReal.ofReal_mul (GlobalTheory.AllWt.lieFacZ_pos _ _).le]
    gcongr
    by_cases h : (dict q.out).2 ∈ (V.X (dict q.out).1).dom
    · exact le_iSup (fun p : FPt V.X => ENNReal.ofReal ((V.X p.1).pnorm (GlobalTheory.AllWt.modelWt V G p.1) (rdU V f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, h⟩⟩
    · have h0 : rdU V f (dict q.out).1 (dict q.out).2 = 0 := by simp [rdU, h]
      have h1 : GlobalTheory.AllWt.ptN (GlobalTheory.AllWt.modelWt V G) (rdU V f) (dict q.out) = 0 := by
        show ‖rdU V f (dict q.out).1 (dict q.out).2‖ * _ = 0
        rw [h0, norm_zero, zero_mul]
      rw [h1, ENNReal.ofReal_zero]; exact bot_le
  have hbound := MeasureTheory.eLpNorm'_mono_eNorm_ae (μ := μ) (q := 2)
    (f := fun q : AutQ W => GlobalTheory.AllWt.homN V x G f (dict q.out))
    (g := fun _ : AutQ W => ENNReal.ofReal (GlobalTheory.AllWt.lieFacZ Dw x G) *
      supE V.X (GlobalTheory.AllWt.modelWt V G) (rdU V f)) (by norm_num)
    (Filter.Eventually.of_forall (fun q => by simpa using hb q))
  rw [MeasureTheory.eLpNorm'_const _ (by norm_num)] at hbound
  apply ne_top_of_le_ne_top _ hbound
  simp only [enorm_eq_self]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (supE_ne_top _ _ hf))
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_top_of_le_ne_top ENNReal.one_ne_top hμ))

theorem petOn_mul_sig_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) {Z : Comp Xo c} {G G₀ : WTZ D.host.E}
    (t : GlobalTheory.FlatTw.TwSec U x Z G₀) (hG : Even G.2) {F : Rul Xo c} (hF : F ∈ cuspW Xo c U G) (σ : c.F →+* ℂ) :
    petOn U x V dict Z (G + G₀) σ (F * t.sig) ≤ t.cInf σ * petOn U x V dict Z G σ F := by
  unfold petOn
  rw [GlobalTheory.AllWt.petAt_eq, GlobalTheory.AllWt.petAt_eq]
  have hpt : ∀ q : AutQ (V (goodOf c σ)),
      ‖GlobalTheory.AllWt.homN (U (goodOf c σ)) x (G + G₀) (F * t.sig) (dict (goodOf c σ) q.out)‖ ≤
        (t.cInf σ • fun q : AutQ (V (goodOf c σ)) => GlobalTheory.AllWt.homN (U (goodOf c σ)) x G F (dict (goodOf c σ) q.out)) q := by
    intro q
    rw [Real.norm_of_nonneg (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _), Pi.smul_apply, smul_eq_mul]
    by_cases hz : dict (goodOf c σ) q.out ∈ GlobalTheory.AllWt.framesOn (U (goodOf c σ)) Z
    · rw [t.homN_mul_sig hG F hz, mul_comm]
    · have h0 : rdU (U (goodOf c σ)) (F * t.sig) (dict (goodOf c σ) q.out).1 (dict (goodOf c σ) q.out).2 = 0 :=
        GlobalTheory.AllWt.rdU_eq_zero _ (GlobalTheory.AllWt.mul_mem_suppOn F t.sig_mem_suppOn) hz
      have h1 : GlobalTheory.AllWt.homN (U (goodOf c σ)) x (G + G₀) (F * t.sig) (dict (goodOf c σ) q.out) = 0 := by
        show _ * (‖rdU (U (goodOf c σ)) (F * t.sig) (dict (goodOf c σ) q.out).1 (dict (goodOf c σ) q.out).2‖ * _) = 0
        rw [h0, norm_zero, zero_mul, mul_zero]
      rw [h1]
      exact mul_nonneg (t.cInf_pos σ).le (GlobalTheory.AllWt.homN_nonneg _ _ _ _ _)
  have h1 := MeasureTheory.eLpNorm'_mono_ae (q := 2) (μ := GlobalTheory.AllWt.muOn (U (goodOf c σ)) (V (goodOf c σ))
    (dict (goodOf c σ)) Z) (by norm_num) (Filter.Eventually.of_forall (fun q =>
      (hpt q).trans (le_abs_self _ |>.trans_eq (Real.norm_eq_abs _).symm)))
  rw [MeasureTheory.eLpNorm'_const_smul _ (by norm_num), Real.enorm_eq_ofReal (t.cInf_pos σ).le] at h1
  have hfin := eLpNorm_homN_ne_top (U (goodOf c σ)) x (dict (goodOf c σ))
    (GlobalTheory.AllWt.muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z) (GlobalTheory.AllWt.muPart_univ_le _ _ _) G F
    ((GlobalTheory.AllWt.mem_cuspW.1 hF).2 _ (goodEmb_goodOf c σ))
  calc _ ≤ (ENNReal.ofReal (t.cInf σ) * MeasureTheory.eLpNorm' (fun q : AutQ (V (goodOf c σ)) =>
        GlobalTheory.AllWt.homN (U (goodOf c σ)) x G F (dict (goodOf c σ) q.out)) 2
          (GlobalTheory.AllWt.muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (t.cInf_pos σ).le]

theorem exists_span_mul_twSec : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G G₀ : WTZ D.host.E) (t : GlobalTheory.FlatTw.TwSec U x Z G₀), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ w, 0 ≤ t.lo w) → ∀ s₀ : Set (Rul Xo c), s₀ ⊆ (cuspW Xo c U G : Set (Rul Xo c)) → (∀ f ∈ s₀, ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) → cuspW Xo c U G ≤ Submodule.span c.F s₀ → ∃ s : Set (cuspOn U Z (G + G₀)), s ⊆ (latOn U Z (G + G₀) : Set (cuspOn U Z (G + G₀))) ∧ Submodule.span c.F s = ⊤ ∧ ∀ y ∈ s, ∃ f ∈ s₀, ∀ σ, normOn U x V dict Z (G + G₀) σ y ≤ t.cInf σ * petOn U x V dict Z G σ f := by
  intro D H Dw l Xo c r U x V dict Z G G₀ t hU hG hlo s₀ hsub hval hspan
  let Q : cuspW Xo c U G →ₗ[c.F] cuspOn U Z G :=
    LinearMap.codRestrict (cuspOn U Z G) ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype)
      (fun F => GlobalTheory.CuspSplit.idem_mul_mem_cuspOn hU Z F)
  let ψ : cuspW Xo c U G →ₗ[c.F] cuspOn U Z (G + G₀) := (GlobalTheory.FlatTw.Mul.mulEquiv t G hG).toLinearMap ∘ₗ Q
  let s₁ : Set (cuspW Xo c U G) := {F | (F : Rul Xo c) ∈ s₀}
  have hQ : Function.Surjective Q := fun g =>
    ⟨⟨g, GlobalTheory.AllWt.cuspOn_le U Z G g.2⟩, Subtype.ext (GlobalTheory.CuspSplit.idem_mul_of_mem_cuspOn g.2)⟩
  have hψ : Function.Surjective ψ := (GlobalTheory.FlatTw.Mul.mulEquiv t G hG).surjective.comp hQ
  have hs₁ : Submodule.span c.F s₁ = ⊤ := by
    apply Submodule.map_injective_of_injective (cuspW Xo c U G).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    have e : (cuspW Xo c U G).subtype '' s₁ = s₀ := by
      ext f
      constructor
      · rintro ⟨F, hF, rfl⟩; exact hF
      · intro hf; exact ⟨⟨f, hsub hf⟩, hf, rfl⟩
    rw [e]
    exact le_antisymm (Submodule.span_le.2 hsub) hspan
  refine ⟨ψ '' s₁, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    have hFl : F ∈ GlobalTheory.AllWt.latW U G := hval F hF
    have hQF : Q F ∈ latOn U Z G := GlobalTheory.CuspSplit.mem_latOn_part hU F hFl Z
    exact GlobalTheory.FlatTw.Mul.mem_latOn_of_mul t 1 one_ne_zero (fun w => by
      have h1 : vAdd w (1 : c.F) = 0 := by simp [vAdd]
      rw [h1, Int.cast_zero, zero_add]; exact hlo w)
      (Q F) hQF (ψ F) (by rw [one_smul]; rfl)
  · rw [Submodule.span_image, hs₁, Submodule.map_top, LinearMap.range_eq_top]
    exact hψ
  · rintro _ ⟨F, hF, rfl⟩
    refine ⟨F, hF, fun σ => ?_⟩
    have e : ((ψ F : cuspOn U Z (G + G₀)) : Rul Xo c) = (F : Rul Xo c) * t.sig := by
      show idem Z * (F : Rul Xo c) * t.sig = _
      rw [mul_comm (idem Z), mul_assoc, t.idem_sig]
    show petOn U x V dict Z (G + G₀) σ _ ≤ _
    rw [e]
    exact petOn_mul_sig_le U x V dict t hG F.2 σ

end GlobalTheory.SpanShortProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningFamilyMulTwistingSectionStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_spanning_family_mul_twistingSection : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G G₀ : WTZ D.host.E) (t : GlobalTheory.FlatTw.TwSec U x Z G₀), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ w, 0 ≤ t.lo w) → ∀ s₀ : Set (Rul Xo c), s₀ ⊆ (cuspW Xo c U G : Set (Rul Xo c)) → (∀ f ∈ s₀, ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) → cuspW Xo c U G ≤ Submodule.span c.F s₀ → ∃ s : Set (cuspOn U Z (G + G₀)), s ⊆ (latOn U Z (G + G₀) : Set (cuspOn U Z (G + G₀))) ∧ Submodule.span c.F s = ⊤ ∧ ∀ y ∈ s, ∃ f ∈ s₀, ∀ σ, normOn U x V dict Z (G + G₀) σ y ≤ t.cInf σ * petOn U x V dict Z G σ f := by
  exact @GlobalTheory.SpanShortProd.exists_span_mul_twSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightAndFlatExponentSizeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightAndFlatExponentSizeBound
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

theorem GlobalTheory.spanShortSize : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (la : AllWt.Weight Dw) (n₀ : Psi H → ℤ) (hp : 1 ≤ Dw.p), laOf Dw a n = la + GlobalTheory.FlatLine.parWt Dw n₀ → (∀ τ, n₀ τ = 1 + ((n / 2 : ℕ) : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) → sizeK Dw a n ≤ (1 + ((Dw.p + Dw.q : ℕ) : ℝ)) * ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) ∧ ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
  intro E _ _ _ H Dw a n la n₀ hp hla hn₀
  have hS : ∀ τ, |(n₀ τ : ℝ)| ≤ ∑ k, |(la τ k : ℝ)| + (((n / 2 : ℕ) : ℝ) + 1) := by
    intro τ
    have h1 : (n₀ τ : ℝ) = 1 + ((n / 2 : ℕ) : ℝ) - (la τ ⟨Dw.p - 1, by omega⟩ : ℝ) := by
      rw [hn₀ τ]; simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_natCast]
    have h2 : |(la τ ⟨Dw.p - 1, by omega⟩ : ℝ)| ≤ ∑ k, |(la τ k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(la τ k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
    have h3 : (0:ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [h1]
    calc |1 + ((n / 2 : ℕ) : ℝ) - (la τ ⟨Dw.p - 1, by omega⟩ : ℝ)|
        ≤ |1 + ((n / 2 : ℕ) : ℝ)| + |(la τ ⟨Dw.p - 1, by omega⟩ : ℝ)| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg (by linarith)]; linarith
  have hsum : ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
    calc ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, (∑ k, |(la τ k : ℝ)| + (((n / 2 : ℕ) : ℝ) + 1)) := Finset.sum_le_sum (fun τ _ => hS τ)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  refine ⟨?_, hsum⟩
  have hK : sizeK Dw a n = ∑ τ, ∑ k : Fin (Dw.p + Dw.q), |((la τ k : ℝ) + (n₀ τ : ℝ))| := by
    unfold sizeK
    refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hla]
    simp [GlobalTheory.FlatLine.parWt]
  have hT : sizeK Dw a n ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * ∑ τ, |(n₀ τ : ℝ)| := by
    rw [hK, Finset.mul_sum]
    calc ∑ τ, ∑ k : Fin (Dw.p + Dw.q), |((la τ k : ℝ) + (n₀ τ : ℝ))|
        ≤ ∑ τ, ∑ k : Fin (Dw.p + Dw.q), (|(la τ k : ℝ)| + |(n₀ τ : ℝ)|) :=
          Finset.sum_le_sum (fun τ _ => Finset.sum_le_sum (fun k _ => abs_add_le _ _))
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpq : (0:ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := Nat.cast_nonneg _
  have hS0 : (0:ℝ) ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hsum hpq]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightAndFlatExponentSizeBoundStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaWeight_and_flatExponent_size_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (la : AllWt.Weight Dw) (n₀ : Psi H → ℤ) (hp : 1 ≤ Dw.p), laOf Dw a n = la + GlobalTheory.FlatLine.parWt Dw n₀ → (∀ τ, n₀ τ = 1 + ((n / 2 : ℕ) : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) → sizeK Dw a n ≤ (1 + ((Dw.p + Dw.q : ℕ) : ℝ)) * ∑ τ, ∑ k, |(la τ k : ℝ)| + ((Dw.p + Dw.q : ℕ) : ℝ) * (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) ∧ ∑ τ, |(n₀ τ : ℝ)| ≤ ∑ τ, ∑ k, |(la τ k : ℝ)| + (Nat.card (Psi H) : ℝ) * (((n / 2 : ℕ) : ℝ) + 1) := by
  first | exact @GlobalTheory.spanShortSize | exact GlobalTheory.spanShortSize | (intros; apply GlobalTheory.spanShortSize <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWeightExponentsOfLargeGapStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWeightExponentsOfLargeGap
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.AllWt (Psi wtOf)

namespace GlobalTheory.ThetaWtGap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wtOf_nonneg_antitone (la : AllWt.Weight Dw) (m : ℤ) (ha : ∀ τ, Antitone (la τ))
    (hb : ∀ τ (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → m ≤ la τ k)
    (hs : ∀ τ (k : Fin (Dw.p + Dw.q)), Dw.p ≤ (k : ℕ) → la τ k ≤ -m) :
    (∀ x, 0 ≤ (wtOf Dw la m).1 x) ∧ ∀ τ, Antitone fun i => (wtOf Dw la m).1 (τ, i) := by
  have h0 : ∀ x, 0 ≤ (wtOf Dw la m).1 x := by
    intro x
    simp only [wtOf]
    split_ifs with h hi h' hi
    · have := hb ⟨x.1, h⟩ ⟨x.2, by omega⟩ hi
      omega
    · exact le_rfl
    · have := hs ⟨_, h'⟩ ⟨Dw.p + (Dw.q - 1 - x.2), by omega⟩ (Nat.le_add_right _ _)
      omega
    · exact le_rfl
    · exact le_rfl
  refine ⟨h0, fun τ i j hij => ?_⟩
  have hi0 := h0 (τ, i)
  simp only [wtOf] at hi0 ⊢
  by_cases h : τ (H.rt : E) = H.rt0
  · simp only [dif_pos h] at hi0 ⊢
    by_cases hj : j < Dw.p
    · have hi : i < Dw.p := by omega
      simp only [dif_pos hi, dif_pos hj]
      have := ha ⟨τ, h⟩ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨j, by omega⟩ from hij)
      omega
    · simpa only [dif_neg hj] using hi0
  · have h' := AllWt.conj_mem h
    simp only [dif_neg h, dif_pos h'] at hi0 ⊢
    by_cases hj : j < Dw.q
    · have hi : i < Dw.q := by omega
      simp only [dif_pos hi, dif_pos hj]
      have := ha ⟨_, h'⟩ (show (⟨Dw.p + (Dw.q - 1 - j), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
        ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
      omega
    · simpa only [dif_neg hj] using hi0

theorem exists_exponents (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (m : ℕ) (la : AllWt.Weight Dw) (hp : 1 ≤ Dw.p) (ha : ∀ τ, Antitone (la τ))
    (hg : ∀ τ, ((2 * m + 2 : ℕ) : ℤ) ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) :
    ∃ a : (E →+* ℂ) × ℕ → ℕ, Formalism.L2.Pj.Dom a (2 * m) ∧
      GlobalTheory.CovTop.laOf Dw a (2 * m) =
        la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) ∧
      ∀ (τ : Psi H) (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p →
        (((2 * m) / 2 : ℕ) : ℤ) < GlobalTheory.CovTop.laOf Dw a (2 * m) τ k := by
  set lb : AllWt.Weight Dw := la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) with hlb
  have e : ∀ τ k, lb τ k = la τ k + (1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) := fun _ _ => rfl
  have hb : ∀ τ (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → (m : ℤ) < lb τ k := by
    intro τ k hk
    have := ha τ (show k ≤ (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) from Fin.le_def.2 (by simp only; omega))
    rw [e]; omega
  have hs : ∀ τ (k : Fin (Dw.p + Dw.q)), Dw.p ≤ (k : ℕ) → lb τ k ≤ -(m : ℤ) := by
    intro τ k hk
    have hk2 := k.2
    have hlt : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
    have h1 := hg τ
    rw [GlobalTheory.CompHS.gap, dif_pos hlt] at h1
    have h2 := ha τ (show (⟨Dw.p - 1 + 1, hlt⟩ : Fin (Dw.p + Dw.q)) ≤ k from Fin.le_def.2 (by simp only; omega))
    rw [e]; push_cast at h1; omega
  have hanti : ∀ τ, Antitone (lb τ) := fun τ i j hij => by
    have := ha τ hij
    rw [e, e]; omega
  obtain ⟨h0, h1⟩ := wtOf_nonneg_antitone lb m hanti (fun τ k hk => (hb τ k hk).le) hs
  have hm : 2 * m / 2 = m := by omega
  have hla : GlobalTheory.CovTop.laOf Dw (fun x => ((wtOf Dw lb m).1 x).toNat) (2 * m) = lb := by
    rw [GlobalTheory.CovTop.laOf, hm]
    simp only [Int.toNat_of_nonneg (h0 _)]
    exact AllWt.weightOf_wtOf lb m
  refine ⟨fun x => ((wtOf Dw lb m).1 x).toNat, ⟨fun τ i j hij => Int.toNat_le_toNat (h1 τ hij), even_two_mul m⟩, hla, ?_⟩
  intro τ k hk
  rw [hla, hm]
  exact hb τ k hk

end GlobalTheory.ThetaWtGap
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaWeight_exponents_of_large_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (m : ℕ) (la : AllWt.Weight Dw) (hp : 1 ≤ Dw.p), (∀ τ, Antitone (la τ)) → (∀ τ, ((2 * m + 2 : ℕ) : ℤ) ≤ gap (la τ) (Dw.p - 1)) → ∃ a : (E →+* ℂ) × ℕ → ℕ, Dom a (2 * m) ∧ laOf Dw a (2 * m) = la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) ∧ ∀ (τ : Psi H) (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → (((2 * m) / 2 : ℕ) : ℤ) < laOf Dw a (2 * m) τ k := by
  first | exact @GlobalTheory.ThetaWtGap.exists_exponents | exact GlobalTheory.ThetaWtGap.exists_exponents | (intros; apply GlobalTheory.ThetaWtGap.exists_exponents <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortIntegralFlatLineTwistingSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortIntegralFlatLineTwistingSection
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatShort

open NumberField IsDedekindDomain Module NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem prod_places_eq (r : (K →+* ℂ) → ℝ) (hr : ∀ σ, r (ComplexEmbedding.conjugate σ) = r σ) :
    ∏ w : InfinitePlace K, r w.embedding ^ w.mult = ∏ σ : K →+* ℂ, r σ := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ) r]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h : ∀ σ ∈ (Finset.univ.filter fun σ : K →+* ℂ => InfinitePlace.mk σ = w), r σ = r w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases InfinitePlace.embedding_mk_eq σ with h | h <;> rw [h]
    exact (hr σ).symm
  rw [Finset.prod_congr rfl h, Finset.prod_const, InfinitePlace.card_filter_mk_eq]

theorem apply_embedding_mk (r : (K →+* ℂ) → ℝ) (hr : ∀ σ, r (ComplexEmbedding.conjugate σ) = r σ)
    (σ : K →+* ℂ) : r (InfinitePlace.mk σ).embedding = r σ := by
  rcases InfinitePlace.embedding_mk_eq σ with h | h <;> rw [h]
  exact hr σ

end GlobalTheory.FlatShort

namespace GlobalTheory.FlatShort

open NumberField IsDedekindDomain Module NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

def idealOf (N : ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton _ (N : K) * ∏ w ∈ S, (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ ⌊-ρ w⌋

theorem idealOf_ne_zero {N : ℕ} (hN : N ≠ 0) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    idealOf N ρ S ≠ 0 :=
  mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 (Nat.cast_ne_zero.2 hN))
    (Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot))

theorem count_idealOf {N : ℕ} (hN : N ≠ 0) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w, w ∉ S → ρ w = 0) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w (idealOf N ρ S) = vAdd w (N : K) + ⌊-ρ w⌋ := by
  classical
  rw [idealOf, FractionalIdeal.count_mul K w (FractionalIdeal.spanSingleton_ne_zero_iff.2 (Nat.cast_ne_zero.2 hN))
    (Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot)),
    FractionalIdeal.count_prod K w S _ (fun w _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot))]
  congr 1
  · exact (GlobalTheory.Core.Int.ProdPrimePow.vAdd_eq_count w (Nat.cast_ne_zero.2 hN)).symm
  rw [Finset.sum_congr rfl fun w' _ => by rw [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal]]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [hS w h, neg_zero, Int.floor_zero]

theorem le_vAdd_of_mem {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (hI : GlobalTheory.FlatTw.IntOff B ρ) (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ w, w ∉ S → ρ w = 0) {a : K}
    (ha : a ∈ idealOf (∏ p ∈ B, p) ρ S) (ha0 : a ≠ 0) (w : HeightOneSpectrum (𝓞 K)) :
    0 ≤ (vAdd w a : ℝ) + ρ w := by
  have hN : (∏ p ∈ B, p) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero
  have h1 : FractionalIdeal.count K w (idealOf (∏ p ∈ B, p) ρ S) ≤ vAdd w a := by
    rw [GlobalTheory.Core.Int.ProdPrimePow.vAdd_eq_count w ha0]; exact FractionalIdeal.count_mono K w (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0)
      (FractionalIdeal.spanSingleton_le_iff_mem.2 ha)
  rw [count_idealOf hN ρ S hS] at h1
  have hNK : ((∏ p ∈ B, p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((∏ p ∈ B, p : ℕ) : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hNK
  have h0 : 0 ≤ vAdd w ((∏ p ∈ B, p : ℕ) : K) := by
    have := FractionalIdeal.count_mono K w hsp (J := 1)
      (FractionalIdeal.spanSingleton_le_iff_mem.2 ((FractionalIdeal.mem_one_iff _).2 ⟨((∏ p ∈ B, p : ℕ) : 𝓞 K), by simp⟩))
    rwa [FractionalIdeal.count_one, ← GlobalTheory.Core.Int.ProdPrimePow.vAdd_eq_count w hNK] at this
  by_cases h : ∀ p ∈ B, ((p : ℕ) : 𝓞 K) ∉ w.asIdeal
  · obtain ⟨m, hm⟩ := hI w h
    rw [hm, ← Int.cast_neg, Int.floor_intCast] at h1
    rw [hm]
    have : (-m : ℤ) ≤ vAdd w a := by linarith
    have : ((-m : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  · push_neg at h
    obtain ⟨p, hp, hpw⟩ := h
    have hmem : ((∏ p ∈ B, p : ℕ) : 𝓞 K) ∈ w.asIdeal :=
      Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem _ hp)) hpw
    have h2 : 1 ≤ vAdd w ((∏ p ∈ B, p : ℕ) : K) := by
      have := FractionalIdeal.count_mono K w hsp (J := (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K))
        (FractionalIdeal.spanSingleton_le_iff_mem.2 ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hmem, by simp⟩))
      rwa [FractionalIdeal.count_self, ← GlobalTheory.Core.Int.ProdPrimePow.vAdd_eq_count w hNK] at this
    have h3 := Int.lt_floor_add_one (-ρ w)
    have h4 : ((vAdd w ((∏ p ∈ B, p : ℕ) : K) + ⌊-ρ w⌋ : ℤ) : ℝ) ≤ (vAdd w a : ℝ) := by exact_mod_cast h1
    have h5 : ((1 : ℤ) : ℝ) ≤ (vAdd w ((∏ p ∈ B, p : ℕ) : K) : ℝ) := by exact_mod_cast h2
    push_cast at h4 h5
    linarith

end GlobalTheory.FlatShort

namespace GlobalTheory.FlatShort

open NumberField IsDedekindDomain Module NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_idealOf (N : ℕ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ((FractionalIdeal.absNorm (idealOf N ρ S) : ℚ) : ℝ) =
      (N : ℝ) ^ finrank ℚ K * ∏ w ∈ S, ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ⌊-ρ w⌋ := by
  rw [idealOf, map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 K), map_prod,
    show (N : K) = algebraMap ℚ K (N : ℚ) from (map_natCast _ N).symm, Algebra.norm_algebraMap]
  simp only [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rw [abs_of_nonneg (by positivity)]

theorem absNorm_idealOf_pos {N : ℕ} (hN : N ≠ 0) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : 0 < ((FractionalIdeal.absNorm (idealOf N ρ S) : ℚ) : ℝ) := by
  rw [absNorm_idealOf]
  refine mul_pos (pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)) _) (Finset.prod_pos fun w _ => zpow_pos ?_ _)
  exact Nat.cast_pos.2 (Nat.pos_of_ne_zero (by
    have := one_lt_absNorm_real w
    intro h; rw [h] at this; norm_num at this))

theorem log_absNorm_idealOf_le {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ w, w ∉ S → ρ w = 0) :
    Real.log ((FractionalIdeal.absNorm (idealOf (∏ p ∈ B, p) ρ S) : ℚ) : ℝ) ≤
      (finrank ℚ K : ℝ) * (GlobalTheory.FlatTw.logSum B - ∑ᶠ w, ρ w * lw K w) := by
  have hNw : ∀ w : HeightOneSpectrum (𝓞 K), (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := fun w => by
    have := one_lt_absNorm_real w; linarith
  have hn : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.2 finrank_pos
  have hN : (0 : ℝ) < ((∏ p ∈ B, p : ℕ) : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero))
  rw [absNorm_idealOf, Real.log_mul (pow_pos hN _).ne' (Finset.prod_pos fun w _ => zpow_pos (hNw w) _).ne',
    Real.log_pow, Real.log_prod (fun w _ => (zpow_pos (hNw w) _).ne')]
  have hlog : Real.log ((∏ p ∈ B, p : ℕ) : ℝ) = GlobalTheory.FlatTw.logSum B := by
    rw [Nat.cast_prod, Real.log_prod (fun p hp => Nat.cast_ne_zero.2 (hB p hp).ne_zero), GlobalTheory.FlatTw.logSum]
  have hfin : ∑ᶠ w, ρ w * lw K w = ∑ w ∈ S, ρ w * lw K w := by
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    by_contra h
    exact hw (by simp [hS w h])
  rw [hlog, hfin, mul_sub, Finset.mul_sum]
  have key : ∀ w ∈ S, Real.log (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ⌊-ρ w⌋) ≤
      -((finrank ℚ K : ℝ) * (ρ w * lw K w)) := by
    intro w _
    rw [Real.log_zpow, lw]
    have h0 : 0 ≤ Real.log ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := Real.log_nonneg (by
      have := one_lt_absNorm_real w; linarith)
    have h1 : ((⌊-ρ w⌋ : ℤ) : ℝ) ≤ -ρ w := Int.floor_le _
    have e : (finrank ℚ K : ℝ) * (ρ w * (Real.log ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) / (finrank ℚ K : ℝ))) =
        ρ w * Real.log ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by field_simp
    rw [e]
    nlinarith
  have := Finset.sum_le_sum key
  rw [Finset.sum_neg_distrib] at this
  linarith

end GlobalTheory.FlatShort

namespace GlobalTheory.FlatShort

open NumberField IsDedekindDomain Module NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem exists_short_elt (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (r : (K →+* ℂ) → ℝ) (hr : ∀ σ, 0 < r σ)
    (hc : ∀ σ, r (ComplexEmbedding.conjugate σ) = r σ) (ρ : HeightOneSpectrum (𝓞 K) → ℝ)
    (hρ : (Function.support ρ).Finite) (hI : GlobalTheory.FlatTw.IntOff B ρ) :
    ∃ a : K, a ≠ 0 ∧ (∀ w, 0 ≤ (vAdd w a : ℝ) + ρ w) ∧ ∀ σ : K →+* ℂ,
      Real.log (r σ * ‖σ a‖) ≤ -GlobalTheory.FlatLine.lineDeg r ρ +
        Real.log |(discr K : ℝ)| / (2 * (finrank ℚ K : ℝ)) + GlobalTheory.FlatTw.logSum B + 1 := by
  classical
  set S := hρ.toFinset with hSdef
  have hS : ∀ w, w ∉ S → ρ w = 0 := fun w h => by
    rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support, not_not] at h; exact h
  set n := finrank ℚ K with hn_def
  have hn : 0 < n := finrank_pos
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hN : (∏ p ∈ B, p) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hB p hp).ne_zero
  set J1 := idealOf (K := K) (∏ p ∈ B, p) ρ S with hJ1def
  have hJ1 : J1 ≠ 0 := idealOf_ne_zero hN ρ S
  set A : ℝ := ((FractionalIdeal.absNorm J1 : ℚ) : ℝ) with hAdef
  have hA : 0 < A := absNorm_idealOf_pos hN ρ S
  have hD : 0 < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  set P : ℝ := ∏ σ, r σ with hPdef
  have hP : 0 < P := Finset.prod_pos fun σ _ => hr σ
  set X : ℝ := A * Real.sqrt |(discr K : ℝ)| * P with hX_def
  have hX : 0 < X := mul_pos (mul_pos hA hD) hP
  set R : ℝ := 5 / 2 * X ^ ((n : ℝ)⁻¹) with hR_def
  have hR : 0 < R := by positivity
  have hRn : R ^ n = (5 / 2) ^ n * X := by
    rw [hR_def, mul_pow, ← Real.rpow_natCast (X ^ ((n : ℝ)⁻¹)), ← Real.rpow_mul hX.le,
      inv_mul_cancel₀ hn'.ne', Real.rpow_one]
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 J1 hJ1
  let f : InfinitePlace K → NNReal := fun w => ⟨R / r w.embedding, (div_pos hR (hr _)).le⟩
  have hL : (minkowskiBound K J).toReal =
      A * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n := by
    simp_rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis,
      volume_fundamentalDomain_latticeBasis, toReal_mul, toReal_pow, toReal_inv, coe_toReal, toReal_ofNat,
      mixedEmbedding.finrank]
    rw [ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _))]
    simp only [J, Units.val_mk0, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs, hAdef]
    ring
  have hV : volume (convexBodyLT K f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact mul_ne_top coe_ne_top coe_ne_top
  have hR' : (volume (convexBodyLT K f)).toReal = (convexBodyLTFactor K : ℝ) * (R ^ n / P) := by
    rw [convexBodyLT_volume, toReal_mul, coe_toReal, coe_toReal]
    congr 1
    rw [NNReal.coe_prod]
    have e : ∀ w : InfinitePlace K, ((f w ^ w.mult : NNReal) : ℝ) = R ^ w.mult / r w.embedding ^ w.mult :=
      fun w => by rw [NNReal.coe_pow, ← div_pow]; rfl
    rw [Finset.prod_congr rfl fun w _ => e w, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_mult_eq,
      prod_places_eq r hc]
  have h : minkowskiBound K J < volume (convexBodyLT K f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top K J).ne hV, hL, hR', hRn]
    have h1 : (1 : ℝ) ≤ convexBodyLTFactor K := by exact_mod_cast one_le_convexBodyLTFactor K
    have h2 : (2 : ℝ)⁻¹ ^ nrComplexPlaces K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h3 : (2 : ℝ) ^ n < (5 / 2) ^ n := pow_lt_pow_left₀ (by norm_num) (by norm_num) hn.ne'
    have e : (5 / 2 : ℝ) ^ n * X / P = (5 / 2) ^ n * (A * Real.sqrt |(discr K : ℝ)|) := by
      rw [hX_def]; field_simp
    rw [e]
    have hY : 0 < A * Real.sqrt |(discr K : ℝ)| := mul_pos hA hD
    calc A * (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| * 2 ^ n
        = (A * Real.sqrt |(discr K : ℝ)| * 2 ^ n) * (2 : ℝ)⁻¹ ^ nrComplexPlaces K := by ring
      _ ≤ (A * Real.sqrt |(discr K : ℝ)| * 2 ^ n) * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ < (A * Real.sqrt |(discr K : ℝ)|) * (5 / 2) ^ n := by rw [mul_one]; exact mul_lt_mul_of_pos_left h3 hY
      _ = 1 * ((5 / 2) ^ n * (A * Real.sqrt |(discr K : ℝ)|)) := by ring
      _ ≤ (convexBodyLTFactor K : ℝ) * ((5 / 2) ^ n * (A * Real.sqrt |(discr K : ℝ)|)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt K J h
  refine ⟨a, hne, le_vAdd_of_mem hB ρ hI S hS ha hne, fun σ => ?_⟩
  have h1 : ‖σ a‖ < R / r σ := by
    have := hlt (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at this
    rw [← apply_embedding_mk r hc σ]
    exact this
  have h2 : r σ * ‖σ a‖ < R := by
    rw [lt_div_iff₀ (hr σ)] at h1; linarith
  have h3 : 0 < r σ * ‖σ a‖ := mul_pos (hr σ) (norm_pos_iff.2 ((map_ne_zero σ).2 hne))
  have h4 : Real.log (r σ * ‖σ a‖) ≤ Real.log R := Real.log_le_log h3 h2.le
  have hlogR : Real.log R = Real.log (5 / 2) + Real.log A / n + Real.log |(discr K : ℝ)| / (2 * n) +
      (∑ σ, Real.log (r σ)) / n := by
    rw [hR_def, Real.log_mul (by norm_num) (by positivity), Real.log_rpow hX, hX_def,
      Real.log_mul (mul_pos hA hD).ne' hP.ne', Real.log_mul hA.ne' hD.ne', Real.log_sqrt (abs_nonneg _), hPdef,
      Real.log_prod (fun σ _ => (hr σ).ne')]
    ring
  have h52 : Real.log (5 / 2) ≤ 1 := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (by norm_num) (by linarith [Real.exp_one_gt_d9])
  have hAle := log_absNorm_idealOf_le hB ρ S hS
  have h5 : Real.log A / n ≤ GlobalTheory.FlatTw.logSum B - ∑ᶠ w, ρ w * lw K w := by
    rw [div_le_iff₀ hn']; linarith
  unfold GlobalTheory.FlatLine.lineDeg
  linarith

end GlobalTheory.FlatShort

namespace GlobalTheory.FlatShort

theorem exists_short_flat_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (B : Finset ℕ), Nonempty (GlobalTheory.ShFam.KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → (∀ p ∈ B, p.Prime) → GlobalTheory.FlatTw.UnramPts Xo c B → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt U x c₁ → ∀ (Z : Comp Xo c), GlobalTheory.FlatLine.HasPts U Z → ∀ w : Psi H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec U x Z (wtOf Dw (GlobalTheory.FlatLine.parWt Dw w) 0), (∀ v, 0 ≤ t.lo v) ∧ ∀ σ, Real.log (t.cInf σ) ≤ (|c₁| + (Dw.q : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E) * ∑ τ, |(w τ : ℝ)| + GlobalTheory.FlatTw.logSum B + Real.log |(NumberField.discr c.F : ℝ)| / (2 * (Module.finrank ℚ c.F : ℝ)) + 1 := by
  intro E _ _ _ H Dw l Xo c r U x B hK hU hpq hBp hUn c₁ hF Z hZ w
  obtain ⟨t, htI, -, hdeg⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat E H Dw l Xo c r U x B hK hU hpq hUn).2 ⟨c₁, hF⟩ Z w hZ
  have hc1 : ∀ τ, c1 U x τ = c₁ := fun τ => hF.c1_eq ⟨Z⟩ τ
  have hconj : ∀ σ, t.cInf (NumberField.ComplexEmbedding.conjugate σ) = t.cInf σ :=
    fun σ => t.cInf_congr (GlobalTheory.CompHt.goodOf_conj σ)
  obtain ⟨a, ha0, hval, hlog⟩ := exists_short_elt B hBp t.cInf t.cInf_pos hconj t.lo t.finite_lo htI
  obtain ⟨-, hci, hlo, -, -⟩ := TwSec.const_spec (x := x) hZ a ha0
  refine ⟨(t.mul (TwSec.const x hZ a ha0)).copy (add_zero _), fun v => ?_, fun σ => ?_⟩
  · show 0 ≤ t.lo v + (TwSec.const x hZ a ha0).lo v
    rw [hlo]; linarith [hval v]
  · show Real.log (t.cInf σ * (TwSec.const x hZ a ha0).cInf σ) ≤ _
    rw [hci]
    have h1 := hlog σ
    have e : t.degLo = GlobalTheory.FlatLine.lineDeg t.cInf t.lo := rfl
    simp only [hc1] at hdeg
    have hs : -(∑ τ, (w τ : ℝ) * c₁) ≤ |c₁| * ∑ τ, |(w τ : ℝ)| := by
      rw [← Finset.sum_mul, mul_comm |c₁|]
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    have h2 : -t.degLo ≤ (|c₁| + (Dw.q : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E) * ∑ τ, |(w τ : ℝ)| := by
      rw [add_mul]; linarith
    linarith

end GlobalTheory.FlatShort
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortIntegralFlatLineTwistingSectionStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_integral_flatLine_twistingSection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (B : Finset ℕ), Nonempty (GlobalTheory.ShFam.KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → (∀ p ∈ B, p.Prime) → GlobalTheory.FlatTw.UnramPts Xo c B → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt U x c₁ → ∀ (Z : Comp Xo c), GlobalTheory.FlatLine.HasPts U Z → ∀ w : Psi H → ℤ, ∃ t : GlobalTheory.FlatTw.TwSec U x Z (wtOf Dw (GlobalTheory.FlatLine.parWt Dw w) 0), (∀ v, 0 ≤ t.lo v) ∧ ∀ σ, Real.log (t.cInf σ) ≤ (|c₁| + (Dw.q : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E) * ∑ τ, |(w τ : ℝ)| + GlobalTheory.FlatTw.logSum B + Real.log |(NumberField.discr c.F : ℝ)| / (2 * (Module.finrank ℚ c.F : ℝ)) + 1 := by
  first | exact @GlobalTheory.FlatShort.exists_short_flat_section | exact GlobalTheory.FlatShort.exists_short_flat_section | (intros; apply GlobalTheory.FlatShort.exists_short_flat_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNumericalBoundsCollect
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNumericalBoundsCollect
open Real

namespace GlobalTheory

theorem covol_numerical_collect : ∀ (CG CB f r Lb S N0 sz c₁ q ℓ lb dd : ℝ), 0 ≤ CG → 0 ≤ CB → 1 ≤ f → 1 ≤ r → 1 ≤ Lb → 0 ≤ S → 0 ≤ q → q ≤ r → 0 ≤ ℓ → ℓ ≤ 3 * Lb → |c₁| ≤ 9 * r * Lb → 0 ≤ N0 → N0 ≤ S + f * (4 * (f * r + 1) + 1) → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → lb ≤ CB * (f * r * Lb) ^ 2 → dd ≤ 391 / 2 * (f * r * Lb) ^ 2 → (f * r + 1) * (2 * (f * r) * Real.log (2 * Real.pi)) + ((|c₁| + q * ℓ) * N0 + lb + dd + 1) + CG * (f * r * Lb) ^ 2 * sz ≤ (11 * CG + CB + 500) * ((f * r * Lb) ^ 3 * S + (f * r * Lb) ^ 5) := by
  intro CG CB f r Lb S N0 sz c₁ q ℓ lb dd hCG hCB hf hr hLb hS hq hqr hℓ hℓL hc hN0 hN0u hsz hszu hlb hdd
  have hfr : 1 ≤ f * r := by nlinarith
  have hfrF : f * r ≤ f * r * Lb := by nlinarith
  have hrLbF : r * Lb ≤ f * r * Lb := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ Lb)]
  have hrF : r ≤ f * r * Lb := by nlinarith
  obtain ⟨F, hFd⟩ : ∃ F, F = f * r * Lb := ⟨_, rfl⟩
  rw [← hFd] at hlb hdd hfrF hrLbF hrF ⊢
  have hF : 1 ≤ F := by linarith
  have hF2 : F ^ 2 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF3 : F ^ 3 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF4 : F ^ 4 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF1 : F ≤ F ^ 3 := by simpa using pow_le_pow_right₀ hF (by norm_num : 1 ≤ 3)
  have hY : 1 ≤ F ^ 5 := one_le_pow₀ hF
  have hX : 0 ≤ F ^ 3 * S := mul_nonneg (by positivity) hS

  have hlog : Real.log (2 * π) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * π)
    have := Real.pi_le_four
    linarith
  have hfrsq : (f * r) ^ 2 ≤ F ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hfrF) (by linarith : (0:ℝ) ≤ F + f * r)]
  have hT1a : (f * r + 1) * (2 * (f * r) * Real.log (2 * π)) ≤ (f * r + 1) * (2 * (f * r) * 7) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by linarith)) (by linarith)
  have hT1 : (f * r + 1) * (2 * (f * r) * Real.log (2 * π)) ≤ 28 * F ^ 5 := by nlinarith

  have hql : q * ℓ ≤ r * (3 * Lb) := mul_le_mul hqr hℓL hℓ (by linarith)
  have hA : |c₁| + q * ℓ ≤ 12 * (r * Lb) := by linarith
  have hffr : f ≤ f * (f * r) := by nlinarith
  have hB : N0 ≤ S + 9 * (f * (f * r)) := by
    have e : f * (4 * (f * r + 1) + 1) = 4 * (f * (f * r)) + 5 * f := by ring
    linarith
  have hAB : (|c₁| + q * ℓ) * N0 ≤ 12 * (r * Lb) * (S + 9 * (f * (f * r))) :=
    mul_le_mul hA hB hN0 (by positivity)
  have hrLbS : r * Lb * S ≤ F ^ 3 * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hFfr : r * Lb * (f * (f * r)) ≤ F ^ 5 := by
    have e : r * Lb * (f * (f * r)) = F * (f * r) := by rw [hFd]; ring
    rw [e]
    have : F * (f * r) ≤ F * F := mul_le_mul_of_nonneg_left hfrF (by linarith)
    nlinarith
  have hT2 : (|c₁| + q * ℓ) * N0 ≤ 12 * (F ^ 3 * S) + 108 * F ^ 5 := by
    have e : 12 * (r * Lb) * (S + 9 * (f * (f * r))) = 12 * (r * Lb * S) + 108 * (r * Lb * (f * (f * r))) := by ring
    linarith

  have hsz1 : (1 + r) * S ≤ 2 * F * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hsz2 : r * f * (4 * (f * r + 1) + 1) ≤ 9 * F ^ 2 := by
    have e : r * f * (4 * (f * r + 1) + 1) = 4 * (f * r) ^ 2 + 5 * (f * r) := by ring
    rw [e]; nlinarith
  have hsz' : sz ≤ 2 * F * S + 9 * F ^ 2 := by linarith
  have hT6a : CG * F ^ 2 * sz ≤ CG * F ^ 2 * (2 * F * S + 9 * F ^ 2) :=
    mul_le_mul_of_nonneg_left hsz' (by positivity)
  have hT6b : CG * F ^ 4 ≤ CG * F ^ 5 := mul_le_mul_of_nonneg_left hF4 hCG
  have hT6 : CG * F ^ 2 * sz ≤ 2 * (CG * (F ^ 3 * S)) + 9 * (CG * F ^ 5) := by
    have e : CG * F ^ 2 * (2 * F * S + 9 * F ^ 2) = 2 * (CG * (F ^ 3 * S)) + 9 * (CG * F ^ 4) := by ring
    linarith
  have hlb' : lb ≤ CB * F ^ 5 := le_trans hlb (mul_le_mul_of_nonneg_left hF2 hCB)
  have hdd' : dd ≤ 196 * F ^ 5 := by linarith
  have p1 : 0 ≤ CG * (F ^ 3 * S) := mul_nonneg hCG hX
  have p2 : 0 ≤ CB * (F ^ 3 * S) := mul_nonneg hCB hX
  have p3 : 0 ≤ CG * F ^ 5 := mul_nonneg hCG (by positivity)
  have e : (11 * CG + CB + 500) * (F ^ 3 * S + F ^ 5)
      = 11 * (CG * (F ^ 3 * S)) + CB * (F ^ 3 * S) + 500 * (F ^ 3 * S) + 11 * (CG * F ^ 5) + CB * F ^ 5 + 500 * F ^ 5 := by ring
  rw [e]
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNumericalBoundsCollectStatement
open Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_numerical_bounds_collect : ∀ (CG CB f r Lb S N0 sz c₁ q ℓ lb dd : ℝ), 0 ≤ CG → 0 ≤ CB → 1 ≤ f → 1 ≤ r → 1 ≤ Lb → 0 ≤ S → 0 ≤ q → q ≤ r → 0 ≤ ℓ → ℓ ≤ 3 * Lb → |c₁| ≤ 9 * r * Lb → 0 ≤ N0 → N0 ≤ S + f * (4 * (f * r + 1) + 1) → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → lb ≤ CB * (f * r * Lb) ^ 2 → dd ≤ 391 / 2 * (f * r * Lb) ^ 2 → (f * r + 1) * (2 * (f * r) * Real.log (2 * Real.pi)) + ((|c₁| + q * ℓ) * N0 + lb + dd + 1) + CG * (f * r * Lb) ^ 2 * sz ≤ (11 * CG + CB + 500) * ((f * r * Lb) ^ 3 * S + (f * r * Lb) ^ 5) := by
  first | exact @GlobalTheory.covol_numerical_collect | exact GlobalTheory.covol_numerical_collect | (intros; apply GlobalTheory.covol_numerical_collect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogThetaWeightSizeLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogThetaWeightSizeLe
open Real

namespace GlobalTheory

theorem log_theta_weight_size_le (f r Lb S sz : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ Lb)
    (hlog : Real.log (f * r) ≤ Lb) (hS : ∃ N : ℕ, S = N) (hlogS : Real.log S ≤ 10 * Lb)
    (hsz0 : 0 ≤ sz) (hsz : sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1)) :
    Real.log sz ≤ 20 * Lb := by
  obtain ⟨N, rfl⟩ := hS
  have hx : 0 < f * r := by positivity
  have hE : 2 ≤ Real.exp Lb := by have := Real.add_one_le_exp Lb; linarith
  have hxE : f * r ≤ Real.exp Lb := by
    rw [← Real.exp_log hx]; exact Real.exp_le_exp.mpr hlog
  have hpow : ∀ n : ℕ, Real.exp Lb ^ n = Real.exp (n * Lb) := fun n => (Real.exp_nat_mul Lb n).symm
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hSE : (N:ℝ) ≤ Real.exp Lb ^ 10 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp; positivity
    · have hNp : (0:ℝ) < N := by exact_mod_cast h
      rw [hpow, ← Real.exp_log hNp]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
  set E := Real.exp Lb with hEdef
  set x := f * r with hxdef
  have hE1 : 1 ≤ E := by linarith
  have hr1 : 1 + r ≤ 2 * x := by rw [hxdef]; nlinarith
  have h1 : (1 + r) * (N:ℝ) ≤ 2 * E ^ 11 := by
    calc (1 + r) * (N:ℝ) ≤ (2 * x) * N := mul_le_mul_of_nonneg_right hr1 hN0
      _ ≤ (2 * E) * E ^ 10 := by
          apply mul_le_mul (by linarith) hSE hN0 (by positivity)
      _ = 2 * E ^ 11 := by ring
  have h2 : r * f * (4 * (f * r + 1) + 1) ≤ 9 * E ^ 2 := by
    have : r * f * (4 * (f * r + 1) + 1) = x * (4 * x + 5) := by rw [hxdef]; ring
    rw [this]
    have hx1 : 1 ≤ x := by rw [hxdef]; nlinarith
    nlinarith
  have h3 : E ^ 2 ≤ E ^ 11 := pow_le_pow_right₀ hE1 (by norm_num)
  have h4 : (2:ℝ) ^ 9 ≤ E ^ 9 := pow_le_pow_left₀ (by norm_num) hE 9
  have h5 : 11 * E ^ 11 ≤ E ^ 20 := by
    have : E ^ 20 = E ^ 9 * E ^ 11 := by ring
    rw [this]
    have : (0:ℝ) ≤ E ^ 11 := by positivity
    nlinarith
  have key : sz ≤ Real.exp (20 * Lb) := by
    have : Real.exp (20 * Lb) = E ^ 20 := by rw [hEdef, hpow]; norm_num
    rw [this]; linarith
  rcases hsz0.eq_or_lt with h | h
  · subst h; simp; linarith
  · exact (Real.log_le_iff_le_exp h).mpr key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogThetaWeightSizeLeStatement
open Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_le_twenty_mul_of_bounds : ∀ (f r Lb S sz : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ Lb → Real.log (f * r) ≤ Lb → (∃ N : ℕ, S = N) → Real.log S ≤ 10 * Lb → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → Real.log sz ≤ 20 * Lb := by
  first | exact @GlobalTheory.log_theta_weight_size_le | exact GlobalTheory.log_theta_weight_size_le | (intros; apply GlobalTheory.log_theta_weight_size_le <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

namespace GlobalTheory.ShortSpanComp

theorem petOn_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G')
    (σ : c.F →+* ℂ) (f : Rul Xo c) : petOn U x V dict Z G σ f = petOn U x V dict Z G' σ f := by
  unfold petOn AllWt.petAt
  have hm : AllWt.modelWt (U (goodOf c σ)) G = AllWt.modelWt (U (goodOf c σ)) G' :=
    AllWt.modelWt_congr _ (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) h
  have hl : AllWt.lieFacZ Dw x G = AllWt.lieFacZ Dw x G' := by
    unfold AllWt.lieFacZ
    have hs : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), G.1 (τ, (i : ℕ)) = G'.1 (τ, (i : ℕ)) := fun τ i =>
      congrFun h (some ⟨τ, i⟩)
    simp only [hs]
  rw [hm, hl]

theorem exZ_laOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) :
    exZ Dw (wtOf Dw (laOf Dw a n) ((n / 2 : ℕ) : ℤ)) = exZ Dw (wtZ a n) := by
  have h := AllWt.exOf_weightOf (Dw := Dw) (fun x => (a x : ℤ)) ((n / 2 : ℕ) : ℤ)
  have h2 : (2 * ((n / 2 : ℕ) : ℤ)) = (n : ℤ) := by
    obtain ⟨k, rfl⟩ := hn
    have : (k + k) / 2 = k := by omega
    rw [this]; push_cast; ring
  rw [h2] at h
  exact h

theorem cuspW_laOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) :
    cuspW Xo c U (wtZ a n) = cuspW Xo c U (wtOf Dw (laOf Dw a n) ((n / 2 : ℕ) : ℤ)) := by
  have h := AllWt.cuspZ_weightOf (Dw := Dw) hU a (n / 2)
  have h2 : 2 * (n / 2) = n := by obtain ⟨k, rfl⟩ := hn; omega
  rw [h2] at h
  rw [AllWt.cuspW_wtZ, ← h]
  rfl

theorem lrd_bounds (K : Type) [Field K] [NumberField K] : 0 ≤ lrd K ∧ lrd K ≤ fieldSz K := by
  have hd : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have h := Int.one_le_abs (discr_ne_zero K)
    rw [← Int.cast_abs]; exact_mod_cast h
  have hdpos : (0 : ℝ) < |(discr K : ℝ)| := lt_of_lt_of_le one_pos hd
  have e : lrd K = Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
    unfold lrd
    rw [NumberField.rootDiscr_def, Int.cast_abs, Real.log_rpow hdpos]
    ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact div_nonneg (Real.log_nonneg hd) (Nat.cast_nonneg _)
  · rw [e]; exact log_rd_le_fieldSz K

end GlobalTheory.ShortSpanComp

namespace GlobalTheory.ShortSpanComp


end GlobalTheory.ShortSpanComp
