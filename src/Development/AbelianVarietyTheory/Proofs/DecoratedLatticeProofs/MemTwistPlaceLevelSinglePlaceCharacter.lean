module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodUnfoldingOfWittDescent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LevGlue

theorem mem_levS_datY_single : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ Q → (∀ PP' ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → ∀ (κ : GA D V), κ ∈ GfC V → (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Lev.finE V κ ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1) → (κ ∈ levS V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) ↔ Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧ Formalism.L2.DIV.redFn β PP (Lev.finE V κ) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) ∧ (Lev.finE V κ ∈ Formalism.L2.DIV.St β → Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) κ = (((ξ PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 (Formalism.L2.DIV.redFn β PP (Lev.finE V κ))))⁻¹ : ℂˣ) : ℂ)) := by
  intro D V β r t j hr Pg Q P χ ξ PP hPQ hPg hQ κ hκ hoff
  have hPgoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP => hoff PP' (hPg PP' hP) hSt
  have hQoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Q, PP' ≠ PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP hne => hoff PP' (fun e => hne (hQ PP' hP e)) hSt
  have hrt : Lev.finE V κ ∈ Formalism.L2.DIV.St β →
      Formalism.L2.DIV.rTup β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) (Lev.finE V κ) = 1 := by
    intro hSt
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP'.1 _) = 1
    rw [hPgoff hSt _ PP'.2]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  refine ⟨⟨fun h => ?_, fun ⟨hSt, hP⟩ => ?_⟩, fun hSt => ?_⟩
  · have h' : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) := h
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev] at h'
    obtain ⟨_, ⟨_, hSt, _, hq⟩, _⟩ := h'
    exact ⟨hSt, hq PP hPQ⟩
  · show κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B)
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    refine ⟨hκ, ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, ?_, ?_⟩, ?_⟩
    · intro PP' hP'
      rw [hPgoff hSt PP' hP']
      exact one_mem _
    · intro PP' hP'
      by_cases e : PP' = PP
      · rw [e]
        exact hP
      · rw [hQoff hSt PP' hP' e]
        exact one_mem _
    · rw [hrt hSt]
      exact one_mem _
  · simp only [Lev.levChi]
    congr 1
    simp only [Formalism.L2.DIV.levFn]
    rw [hrt hSt, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul]
    rw [Finset.prod_eq_one (fun PP' hP' => Finset.prod_eq_one fun c _ => by
      rw [hPgoff hSt PP' hP', Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]), one_mul]
    rw [Finset.prod_eq_single_of_mem (s := (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B).Q) PP hPQ fun PP' hP hne => by
      rw [hQoff hSt PP' hP hne, Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]]
    simp [Lev.datY]

end GlobalTheory.LevGlue

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_twistPlaceLevel_single_place_character : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ Q → (∀ PP' ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ PP' ∈ Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → ∀ (κ : GA D V), κ ∈ GfC V → (∀ PP' : Formalism.L2.DIV.Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → Lev.finE V κ ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1) → (κ ∈ levS V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) ↔ Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧ Formalism.L2.DIV.redFn β PP (Lev.finE V κ) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) ∧ (Lev.finE V κ ∈ Formalism.L2.DIV.St β → Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) κ = (((ξ PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 (Formalism.L2.DIV.redFn β PP (Lev.finE V κ))))⁻¹ : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.LevGlue.mem_levS_datY_single | exact GlobalTheory.LevGlue.mem_levS_datY_single | (intros; apply GlobalTheory.LevGlue.mem_levS_datY_single <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedTranslatesCombinationCommutesSchrodinge
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedTranslatesCombinationCommutesSchrodinge
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PlaceModelComb

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem mxAt_of_idemAt {es : AE D} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP) {Q : GlobalTheory.FinPl.Pl D → Prop}
    (hQ : Q ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) {m n : ℕ} {w : Mx D m n} (hw : IsHalf (es + cA D es) w) : GlobalTheory.FinPl.MxAt Q w := by
  obtain ⟨v, ε, hε, hsum⟩ := h.1.2.2
  obtain ⟨q, hqe, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v es ε h.1 hε hsum
  have hv : q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under q (hqe ▸ h)
  exact GlobalTheory.LevPin.mxAt_of_half q (hv ▸ hQ) w (hqe ▸ hw)

theorem mxAt_of_idemSum {e : AE D} {Pg : Finset (Pl D.host.E)} (hs : IsIdemSum e Pg) {m n : ℕ} {x : Mx D m n}
    (hx : IsHalf e x ∨ IsHalf (cA D e) x) :
    GlobalTheory.FinPl.MxAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hs
  intro i j
  rcases hx with hx | hx
  · rw [← hx i j, Finset.sum_mul]
    refine Ideal.sum_mem _ fun PP hPP => ?_
    have hw : IsHalf (es PP + cA D (es PP)) (es PP • x) := fun a b => by
      obtain ⟨h1, h2, -⟩ := (hes PP hPP).1
      rw [Matrix.smul_apply, smul_eq_mul, add_mul, ← mul_assoc, h1, ← mul_assoc, mul_comm (cA D (es PP)), h2,
        zero_mul, add_zero]
    have := mxAt_of_idemAt (Q := fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (hes PP hPP) ⟨PP, hPP, rfl⟩ hw i j
    rwa [Matrix.smul_apply, smul_eq_mul] at this
  · rw [← hx i j, map_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun PP hPP => ?_
    have hw : IsHalf (es PP + cA D (es PP)) (cA D (es PP) • x) := fun a b => by
      obtain ⟨h1, h2, -⟩ := (hes PP hPP).1
      rw [Matrix.smul_apply, smul_eq_mul, add_mul, ← mul_assoc, h2, zero_mul, zero_add, ← mul_assoc, ← map_mul, h1]
    have := mxAt_of_idemAt (Q := fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (hes PP hPP) ⟨PP, hPP, rfl⟩ hw i j
    rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (Pg : Finset (Pl D.host.E)) (P' : GlobalTheory.FinPl.Pl D → Prop), IsIdemSum e Pg → (∀ PP ∈ Pg, ¬ P' ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) → ∀ (d : WO S T →₀ ℂ), GlobalTheory.FinPl.CombAt P' d → ∀ (f₁ : WO S T → ℂ) (T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₁ T₁ → (∀ Φ, T₂ Φ = comb ψ S T d (T₁ Φ)) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (comb ψ S T d f₁) T₂ := by
  intro D ψ hψ S T Λ e Pg P' hs hd d hdc f₁ T₁ T₂ hT₁ hT₂
  have hd' : ∀ p, (∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → ¬ P' p := by
    rintro p ⟨PP, hPP, rfl⟩
    exact hd PP hPP
  have hcomm : ∀ x : WO S T, GlobalTheory.FinPl.MxAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x → ∀ f,
      heisO ψ S T x (comb ψ S T d f) = comb ψ S T d (heisO ψ S T x f) := by
    intro x hx f
    have h := (GlobalTheory.DisjComb.main D ψ hψ S T _ P' hd').1 (Finsupp.single x 1) d (fun u hu => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
      subst hu
      exact hx) hdc f
    simpa only [GlobalTheory.DisjComb.comb_single] using h
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [hT₂, hT₁.trans Φ hΦ x hx, ← hcomm x (mxAt_of_idemSum hs (Or.inl hx)), hT₂]
  · rw [hT₂, hT₁.modul Φ hΦ y hy, ← hcomm y (mxAt_of_idemSum hs (Or.inr hy)), hT₂]
  · rw [hT₂, hT₁.vac]

end GlobalTheory.PlaceModelComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedTranslatesCombinationCommutesSchrodingeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedTranslatesCombination_commutes_schrodinger : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (Pg : Finset (Pl D.host.E)) (P' : GlobalTheory.FinPl.Pl D → Prop), IsIdemSum e Pg → (∀ PP ∈ Pg, ¬ P' ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) → ∀ (d : WO S T →₀ ℂ), GlobalTheory.FinPl.CombAt P' d → ∀ (f₁ : WO S T → ℂ) (T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₁ T₁ → (∀ Φ, T₂ Φ = comb ψ S T d (T₁ Φ)) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (comb ψ S T d f₁) T₂ := by
  first | exact @GlobalTheory.PlaceModelComb.main | exact GlobalTheory.PlaceModelComb.main | (intros; apply GlobalTheory.PlaceModelComb.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentAtSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QGeoAt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable def glOf (p : Place D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) :
    GL Y k →* GA D S where
  toFun gk := Classical.choose (((GlobalTheory.LocGrp.local_groups D k p).1 S Y F).1 gk)
  map_one' := by
    have h := ((GlobalTheory.LocGrp.local_groups D k p).1 S Y F)
    set g0 := Classical.choose (h.1 1)
    have h0 : p.IsLoc F g0 1 := (Classical.choose_spec (h.1 1)).1
    have h00 : p.IsLoc F (g0 * g0) 1 := by simpa using h.2.2 _ _ _ _ h0 h0
    have e := (Classical.choose_spec (h.1 1)).2 _ h00
    exact mul_left_cancel (a := g0) (by rw [mul_one]; exact e)
  map_mul' a b := by
    have h := ((GlobalTheory.LocGrp.local_groups D k p).1 S Y F)
    have ha := (Classical.choose_spec (h.1 a)).1
    have hb := (Classical.choose_spec (h.1 b)).1
    exact ((Classical.choose_spec (h.1 (a * b))).2 _ (h.2.2 _ _ _ _ ha hb)).symm

theorem glOf_loc (p : Place D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (g : GL Y k) :
    p.IsLoc F (glOf p S F g) g :=
  (Classical.choose_spec (((GlobalTheory.LocGrp.local_groups D k p).1 S Y F).1 g)).1

end GlobalTheory.QGeoAt


open GlobalTheory.QGeoAt in
theorem GlobalTheory.QGeoAt.geo_of_frames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → ∀ (PP : Pl D.host.E), QAll W PP → ∀ (l : LocX a (pk W).βX PP), LocY l y v.N (pk W).βY b (fun _ _ _ => 1) → (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (l.FX j hj)) → IsStdFr GlobalTheory.SymBridge.zPos l.FT → ∃ G : GlobalTheory.QTw.QGeo v (baseOf (pk W) (lvP W) u (mkGeo m b)) PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (G.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos G.FT ∧ G.z₀ = fun r => (ofSplit G.q).pr (a.ζ₀ r) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b v hv hτ hNT PP hPP l hY hFX hFT
  obtain ⟨⟨ψk, hchar, hcond⟩, ⟨ν, hν⟩, hϖ⟩ := GlobalTheory.T.local_character_conductor_one_exists W u hW a PP (Or.inr hPP) l
  obtain ⟨ϖ, hunif, hcompl⟩ := hϖ hPP
  refine ⟨{
    k := l.k
    ν := ν
    unitVol := hν
    q := l.q
    idem := l.idem
    unit := l.unit
    ψk := ψk
    char := hchar
    cond := hcond
    ϖ := ϖ
    unif := hunif
    compl := hcompl
    s := l.s
    hs := l.hs
    FX := l.FX
    FT := l.FT
    FM := l.FM
    FY := hY.FY
    sc := hY.sc
    sc_ne := fun j h => by simpa [h] using hY.sc_unit j
    sc_step := hY.sc_step
    bes := hY.bes
    jac := hY.jac
    z₀ := fun r => (ofSplit l.q).pr (a.ζ₀ r)
    last := l.last
    tau := fun h => by rw [hτ]; exact hY.tau h
    latX := l.latX
    latM := l.latM
    latY := hY.latY
    latT := by rw [hNT]; exact l.latT
    gl := fun j d hd => glOf (ofSplit l.q) _ (hY.FY j d hd)
    gl_loc := fun j d hd g => glOf_loc (ofSplit l.q) _ (hY.FY j d hd) g
    frame := fun j d hd => by
      obtain ⟨e, he, hm⟩ := hY.frame j d hd
      refine ⟨e, he, ?_⟩
      simpa using hm
    frameTop := l.frameTop }, hFX, hFT, rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_at_split_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → ∀ (PP : Pl D.host.E), QAll W PP → ∀ (l : LocX a (pk W).βX PP), LocY l y v.N (pk W).βY b (fun _ _ _ => 1) → (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (l.FX j hj)) → IsStdFr GlobalTheory.SymBridge.zPos l.FT → ∃ G : GlobalTheory.QTw.QGeo v (baseOf (pk W) (lvP W) u (mkGeo m b)) PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (G.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos G.FT ∧ G.z₀ = fun r => (ofSplit G.q).pr (a.ζ₀ r) := by
  first | exact @GlobalTheory.QGeoAt.geo_of_frames | exact GlobalTheory.QGeoAt.geo_of_frames | (intros; apply GlobalTheory.QGeoAt.geo_of_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepUnfoldingOfDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepUnfoldingOfUnfoldingsAndLink
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepUnfoldingOfUnfoldingsAndLink
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem om_comp_one {D : D7} {S T : HSp D} (om : Om S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    om (1, h) (om (g, 1) f) = om (g, h) f := by
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  ext <;> simp

theorem rTrans_liftS {D : D7} {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T))
    (G : GA D T → ℂ) (f : WO S T → ℂ) (g : GA D S) :
    rTrans g (liftS om ν 𝓕 G f) = liftS om ν 𝓕 G (om (g, 1) f) := by
  funext x
  simp only [rTrans, liftS_apply]
  congr 1
  funext h
  have e : ((x, h) : GA D S × GA D T) * (g, 1) = (x * g, h) := by simp
  rw [← e, map_mul, Module.End.mul_apply]

theorem doubleStep_of_laws : ∀ D : D7, UnfBF D → UnfFB D → LinkLaw D → HandFBLaw D → FlatLaw D → DoubleStep D := by
  intro D hBF hFB hLink hHand hFlat ψ σ B J B' s₁ s₂ l vL Φ₁ Φ₂ φ G g hΦ₁ hΦ₂ hφ hG hG'
  have hfl := GlobalTheory.T.flatThetaMaps_preserve_thetaFunctions D hFlat ψ
  have hΞ₁ : ∀ h₁, IsThetaFunO ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h₁) Φ₁)) := fun h₁ =>
    hfl.1 _ B J s₁ _ (s₁.weil.om_pres _ _ hΦ₁)
  have hΞ₂ : ∀ h₁ h₂, IsThetaFunO ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := fun h₁ h₂ =>
    hfl.2 _ J B' s₂ _ (s₂.weil.om_pres _ _ hΦ₂)
  have hL := fun h₁ => hLink ψ (σ + 1) B J s₁ B'.L B'.ζ B'.line l φ _ hφ (hΞ₁ h₁)
  refine ⟨fun h₁ h₂ => hHand ψ σ J B' s₂ vL _ _ (hL h₁).1 (hΞ₂ h₁ h₂), ?_⟩
  refine ⟨fun h₁ => J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)), ?_, ?_⟩
  · have := hBF ψ (σ + 1) B J s₁ φ (s₂.lift G Φ₂) (s₁.om (g, 1) Φ₁) hφ hG' (s₁.weil.om_pres _ _ hΦ₁)
    simp only [om_comp_one] at this
    convert this using 2
    exact rTrans_liftS _ _ _ _ _ _
  · intro h₁
    have := hFB ψ σ J B' s₂ vL _ G (s₂.om (h₁, 1) Φ₂) (hL h₁).1 hG (s₂.weil.om_pres _ _ hΦ₂)
    simp only [om_comp_one] at this
    convert this using 1
    · rfl
    · show J.perAll ψ B s₁.om₀ φ (rTrans h₁ (s₂.lift G Φ₂)) (flatBF s₁ (s₁.om (g, h₁) Φ₁)) = _
      rw [(hL h₁).2]
      congr 1
      exact rTrans_liftS _ _ _ _ _ _

end GlobalTheory.Unf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepUnfoldingOfUnfoldingsAndLinkStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDoubleStepUnfolding_of_unfoldings_and_link : ∀ D : D7, UnfBF D → UnfFB D → LinkLaw D → HandFBLaw D → FlatLaw D → DoubleStep D := by
  first | exact @GlobalTheory.Unf.doubleStep_of_laws | exact GlobalTheory.Unf.doubleStep_of_laws | (intros; apply GlobalTheory.Unf.doubleStep_of_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepUnfoldingOfDescent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem doubleStep_of_descent : ∀ D : D7, Descent D → DoubleStep D := fun D hD =>
  GlobalTheory.T.besselDoubleStepUnfolding_of_unfoldings_and_link D (GlobalTheory.T.besselPeriod_thetaLift_unfolding D hD) (GlobalTheory.T.fourierJacobi_period_unfolding_of_witt_descent D hD) (GlobalTheory.T.bessel_level_step_fourierJacobi_period_link D) (GlobalTheory.T.fourierJacobiHandOff_automorphic D) (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D)

end GlobalTheory.Unf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepUnfoldingOfDescentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent : ∀ D : D7, Descent D → DoubleStep D := by
  first | exact @GlobalTheory.Unf.doubleStep_of_descent | exact GlobalTheory.Unf.doubleStep_of_descent | (intros; apply GlobalTheory.Unf.doubleStep_of_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionBlockTriangularIffMemParahoricLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionBlockTriangularIffMemParahoricLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section
namespace GlobalTheory.TwLevRed

theorem reGL_symm_mem_KO_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    {x : GL b k} : (reGL e).symm x ∈ KO k a ↔ x ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem blockTri_iff_mem_lev : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k), x ∈ KO k _ → ∀ (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → (R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) ↔ x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) := by
  intro E _ _ k _ _ _ _ PP ι hPP K T s j d hd δ hδ η n e he x hx R hR
  have hent : ∀ a b, R.val a b = 0 ↔ valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a))
      (stdOrd (Fin K) (Fin T) j d hd (e.symm b))) < 1 := by
    intro a b
    constructor
    · intro h0
      have := hR a b 0 (by rw [h0, map_zero])
      simpa using this
    · intro hv
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (R.val a b)
      have h1 := hR a b z hz.symm
      have h2 : valuation k (ι (z : E)) < 1 := by
        have : ι (z : E) = x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm b)) -
            (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm b)) - ι (z : E)) := by
          ring
        rw [this]
        exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
      rw [← hz, Ideal.Quotient.eq_zero_iff_mem]
      exact hPP z h2
  have hblk : ∀ q : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j,
      Formalism.L2.DIV.blk2 (K + (s + 1)) (e q) = Sum.elim (fun _ => 0) (fun _ => 1) q := by
    intro q
    have h := he q
    unfold Formalism.L2.DIV.blk2
    rcases q with (i | i) | p
    · have : (e (.inl (.inl i))).val < K + (s + 1) := by rw [h]; simp [GlobalTheory.SymBridge.zPos]; omega
      simp [this]
    · have : (e (.inl (.inr i))).val < K + (s + 1) := by rw [h]; simp [GlobalTheory.SymBridge.zPos]; omega
      simp [this]
    · have : ¬ (e (.inr p)).val < K + (s + 1) := by
        rw [h, not_lt]; simp only [GlobalTheory.SymBridge.zPos]
        exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
      simp [this]
  have hJ : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J ↔
      ∀ (p : Fin j × Fin T) (i : Fin K ⊕ Fin (s + 1)),
        valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (.inr p)) (stdOrd (Fin K) (Fin T) j d hd (.inl i))) < 1 := by
    change (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x ∈
      (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).J ↔ _
    rw [mem_parahoric]
    have e' : (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x =
        (reGL (stdOrd (Fin K) (Fin T) j d hd)).symm x := by
      simp [LatFrame.conj, plainFrame]
      rfl
    rw [e', reGL_symm_mem_KO_iff]
    simp only [hx, true_and]
    rfl
  rw [hJ, Formalism.L2.DIV.mem_blockTri]
  constructor
  · intro h p i
    have := h (e (.inr p)) (e (.inl i)) (by rw [hblk, hblk]; simp)
    rw [hent] at this
    simpa using this
  · intro h a b hab
    obtain ⟨q, rfl⟩ := e.surjective a
    obtain ⟨q', rfl⟩ := e.surjective b
    rw [hblk, hblk] at hab
    rw [hent]
    rcases q with q | q <;> rcases q' with q' | q' <;> simp at hab
    simpa using h q q'

end GlobalTheory.TwLevRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionBlockTriangularIffMemParahoricLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reductionBlockTriangular_iff_mem_parahoricLevel : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k), x ∈ KO k _ → ∀ (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → (R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) ↔ x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) := by
  first | exact @GlobalTheory.TwLevRed.blockTri_iff_mem_lev | exact GlobalTheory.TwLevRed.blockTri_iff_mem_lev | (intros; apply GlobalTheory.TwLevRed.blockTri_iff_mem_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataAtTypePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataAtTypePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SymReadEx
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem tame_step {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Pl D.host.E} (hP : PP ∈ L.Pg)
    (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {μ : kˣ →* ℂˣ}
    (hμ : (ofSplit q).IsComp (Lift.chrStep L.mu0 L.eta j).1⁻¹ μ) : IsTame μ := by
  intro x hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have e1 : L.mu0 (i + 1) (idl q x) = 1 := res_idl q h (hL.mu0 ⟨i, h2⟩) (hL.chi ⟨i, h2⟩ PP hP) x hx
  have hr : IsRes L.C.eta PP 1 := fun z y v hy hv => by
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    have hzP : z ∉ PP.asIdeal := fun hm => v.ne_zero (hv.trans (Ideal.Quotient.eq_zero_iff_mem.2 hm))
    rw [GlobalTheory.NormOneUnit.locK_unr (L.C.isEta.unr PP) (y := y)
      (by rw [hy]; exact (PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 hzP)]
    rfl
  have e2 : L.eta (idl q x) = 1 := res_idl q h hL.eta hr x hx
  have e3 : (Lift.chrStep L.mu0 L.eta (i + 1)).1 (idl q x) = 1 := by
    unfold Lift.chrStep
    split_ifs
    · change L.mu0 (i + 1) (idl q x) * (L.eta (idl q x))⁻¹ = 1
      rw [e2, inv_one, mul_one]
      exact e1
    · exact e1
  refine Units.ext ((hμ x (idl q x) rfl).trans ?_)
  rw [MonoidHom.inv_apply, e3]
  simp

theorem red_sym {D : D7} {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP)
    (S : SymData l.k l.s D.R.k) {π : Equiv.Perm (Fin D.R.r)} (hπ : IsSymOrd D.R.rS D.R.k π)
    (g g' : GL (Fin D.R.r) (kP PP)) (hg : ∀ i j, g'.val i j = g.val (π i) (π j)) :
    ((∃ x, l.Red S x g) ↔ g' ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧
    ∀ ψ₀ : AddChar (kP PP) ℂ,
      (∀ z, (S.ψ (((S.ϖ⁻¹ : l.kˣ) : l.k) * prO l.q z) : ℂ) = ψ₀ (Ideal.Quotient.mk _ z)) → ∀ x, l.Red S x g →
        (S.P.lam x : ℂ) = ψ₀ (edgeSum (symEdge D.R.rS D.R.k) g') := by
  have h1 := l.hs
  have h2 := S.odd
  have hρ : D.R.rS = S.ρ := by unfold Ranks.rS; omega
  let e : Fin D.R.k ⊕ Fin (l.s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by unfold Ranks.r; omega))
  have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]
  have hr : ∀ x, l.Red S x g ↔ ∀ a b z, Ideal.Quotient.mk PP.asIdeal z = g.val (e a) (e b) →
      valuation l.k ((x : GL (Fin D.R.k ⊕ Fin (l.s + 1)) l.k).val a b - prO l.q z) < 1 := fun x =>
    ⟨fun h a b => h a b _ _ (he a) (he b), fun h a b a' b' ha hb => by
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      exact h a b⟩
  rw [hρ] at hπ ⊢
  simp only [hr]
  exact ⟨sym_grp S (prO l.q) (prO_le l.q l.idem) (prO_lt l.q l.idem) e he hπ g g' hg,
    fun ψ₀ h x hx => sym_chr S (prO l.q) e he hπ g g' hg ψ₀ h x hx⟩

theorem exists_symRead : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (a : XGeo D) (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1), ∃ S : ∀ PP, SymData (l PP).k (l PP).s D.R.k, SymRead W l S := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW _ a l
  obtain ⟨ψ₀, hψ₀, -, π, hπ, hH, hχ⟩ := W.Q.charW.base.grp.levels
  have hlev := W.Q.charW.base.lev
  have loc : ∀ PP : (pk W).Pg, ∃ S : SymData (l PP).k (l PP).s D.R.k, (ofSplit (l PP).q).IsChar (pk W).ψ S.ψ ∧
      (∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ (S.μ j)) ∧
      ∀ z, (S.ψ (((S.ϖ⁻¹ : (l PP).kˣ) : (l PP).k) * prO (l PP).q z) : ℂ) = ψ₀ PP.1 (Ideal.Quotient.mk _ z) := by
    intro PP
    obtain ⟨⟨ψk, hch, hcond⟩, -⟩ := GlobalTheory.WeilCondUnif.cond_unif W u hW a PP.1 (Or.inl PP.2) (l PP)
    obtain ⟨ϖ, hϖ, hres⟩ := exists_unif (l PP).q (l PP).idem hcond (hψ₀ PP.1 PP.2)
    obtain ⟨ρ, hρ⟩ : ∃ ρ, (l PP).s + 1 = 2 * ρ + 1 := by
      obtain ⟨b, hb⟩ := D.R.m_even
      have := (l PP).hs
      exact ⟨b - 1, by omega⟩
    obtain ⟨P, hP'⟩ := GlobalTheory.SymLevelExists.exists_isSymLevel (l PP).k ψk hcond ϖ hϖ ρ D.R.k ((l PP).s + 1)
    choose μ hμ using fun j => GlobalTheory.LocMod.Witness.exists_isComp (ofSplit (l PP).q) (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹
    refine ⟨⟨ψk, ϖ, ρ, P, fun j => if 1 ≤ j ∧ j ≤ D.R.m then μ j else 1, fun j => ?_, hcond, hϖ, hρ, hP'⟩, hch,
      fun j h1 h2 => ?_, hres⟩
    · split_ifs with h
      · exact tame_step (pk W).toLevCh hlev (l PP).q PP.2 (l PP).idem h.1 h.2 (hμ j)
      · exact fun _ _ => rfl
    · simp only [if_pos (And.intro h1 h2)]
      exact hμ j
  choose S h1 h2 h3 using loc
  refine ⟨S, h1, h2, fun x => (hH x).trans ?_, fun x hx y hxy => ?_⟩
  · exact ⟨fun h PP => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.2 (h PP (Set.mem_univ _)),
      fun h PP _ => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.1 (h PP)⟩
  · refine (hχ x hx ((hH _).1 hx)).trans ?_
    refine (map_prod (MonoidHom.eval _) _ _).trans (Finset.prod_congr rfl fun PP _ => Units.ext ?_)
    exact ((red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).2 _ (h3 PP) _ (hxy PP)).symm

end GlobalTheory.SymReadEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataAtTypePlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_data_at_type_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (a : XGeo D) (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1), ∃ S : ∀ PP, SymData (l PP).k (l PP).s D.R.k, SymRead W l S := by
  first | exact @GlobalTheory.SymReadEx.exists_symRead | exact GlobalTheory.SymReadEx.exists_symRead | (intros; apply GlobalTheory.SymReadEx.exists_symRead <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalTwist
noncomputable section

section Col

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Formalism.UG.P GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.LevRead Matrix
open scoped TensorProduct

namespace GlobalTheory.FamTraceChiCol.ColRead

theorem lamJ_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {gp : Fin 2 → ℕ} (G : Formalism.L2.Forms.GLoc F E σ gp) (i : Fin 2) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    {w : HeightOneSpectrum (𝓞 E)} (ρ : 𝓞 E ⧸ w.asIdeal →+* Formalism.L2.Forms.kv F v)
    (hres : ∀ (z : AfE F E) (c : 𝓞 E ⧸ w.asIdeal), HasRes w (adAt F w z) c →
        ∃ hh : G.phi i v h (prV (E := E) v z) ∈ v.adicCompletionIntegers F,
          IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hh⟩ = ρ c)
    {xa : GL (Fin n) (AfE F E)} {A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.asIdeal)} (hA : IsRed w xa A)
    (χ : ℕ → MulChar (Formalism.L2.Forms.kv F v) ℂ) (k t : ℕ) (z : 𝓞 E)
    (hz : Ideal.Quotient.mk w.asIdeal z =
      ∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < k ∧ (y : ℕ) ≠ k then A x y else 0)
    (fr : GL (Fin n) (v.adicCompletion F)) (hfr : fr = 1) :
    ∃ w' : v.adicCompletionIntegers F, (w' : v.adicCompletion F) = G.phi i v h ((z : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∧
      Formalism.L2.Forms.lamJ (G.psi0 i v h) χ k t 0 k (Formalism.L2.Forms.redM F v (G.mat i v h fr (bc (prV (E := E) v) xa))) =
        G.psi0 i v h (IsLocalRing.residue _ w') := by
  subst hfr
  obtain ⟨hh, e⟩ := hres (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z : E)) _ (by rw [adAt_inclE]; exact hasRes_coe w z)
  refine ⟨⟨_, hh⟩, rfl, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, TC.GLev0.redM_mat G i h ρ hres hA, Formalism.L2.Forms.lamJ, Finset.range_zero, Finset.prod_empty, mul_one, hz, map_sum ρ]
  refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum ρ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [apply_ite ρ, map_zero]
  rfl

end GlobalTheory.FamTraceChiCol.ColRead

end Col

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.FamTraceChiCol.ColRead

open GlobalTheory.SymBridge GlobalTheory.RootEx


set_option maxHeartbeats 1000000 in
theorem exists_close {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) {n κ τ : ℕ} (hr : V.rank = n) (hn : n = κ) (F : Frame k V.rank (XIx (Fin κ) (Fin τ) 0)) (hF : IsStdFr xPos F)
    {x : GA D V} {y : GL (Fin n) (GlobalTheory.AdForm.EF D)} (hy : GlobalTheory.AdForm.finM V hr x = y.1)
    {A : Matrix (Fin n) (Fin n) (𝓞 D.host.E ⧸ PP.asIdeal)} (hA : LevRead.IsRed (F := D.host.F) PP y A)
    (g : GL (XIx (Fin κ) (Fin τ) 0) k) (hg : (mt V x).map q.pr = F.β * g.val * F.γ) :
    ∃ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z =
        (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) + 1 = b ∧ (b : ℕ) < κ ∧ (b : ℕ) ≠ κ then A a b else 0) ∧
      valuation k ((∑ a : Fin κ, ∑ b : Fin κ, if b.val = a.val + 1 then g.val (Sum.inl (Sum.inl a)) (Sum.inl (Sum.inl b)) else 0) -
        (ofSplit q).pr (z : D.host.E)) < 1 := by
  subst hr
  subst hn
  obtain ⟨e, he, hβ⟩ := hF
  choose R hR hR' using hA
  have hM : ∀ i j, valuation k ((mt V x).map q.pr i j - q.pr (incA D (R i j))) < 1 := fun i j => by
    have h2 : y.1 i j = toEAf D (mt V x i j) := by
      rw [← hy]
      rfl
    have h3 := LevChi.val_pr_lt q hq (z := mt V x i j - incA D (R i j)) (by
      rw [RingHom.map_sub, ← h2, RingHom.map_sub]
      exact (congrArg (fun t => Valued.v (adAt D.host.F PP (y.1 i j) - t)) (adAt_inclE D.host.F PP _)).trans_lt (hR' i j))
    rwa [RingHom.map_sub] at h3
  have hgM : ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := fun a b => by
    have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    have h2 := congrFun (congrFun h1 (e a)) b
    rw [hβ] at h2
    simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm
  have he' : ∀ a : Fin V.rank, e (Sum.inl (Sum.inl a)) = a := fun a => Fin.ext (he _)
  have hc : ∀ a b : Fin V.rank, ((a : ℕ) + 1 = b ∧ (b : ℕ) < V.rank ∧ (b : ℕ) ≠ V.rank) ↔ b.val = a.val + 1 := fun a b =>
    ⟨fun h => h.1.symm, fun h => ⟨h.symm, b.2, b.2.ne⟩⟩
  refine ⟨∑ a : Fin V.rank, ∑ b : Fin V.rank, if b.val = a.val + 1 then R a b else 0, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [apply_ite (Ideal.Quotient.mk PP.asIdeal), map_zero, hR]
    exact if_congr (hc a b).symm rfl rfl
  · let φ : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)
    have hφ : ∀ r : 𝓞 D.host.E, (ofSplit q).pr (r : D.host.E) = φ r := fun _ => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, map_sum φ, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun a _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum φ, ← Finset.sum_sub_distrib]
    refine (valuation k).map_sum_lt one_ne_zero fun b _ => ?_
    split_ifs
    · rw [hgM, he', he']
      exact hM a b
    · rw [map_zero, sub_zero, map_zero]
      exact zero_lt_one

end GlobalTheory.FamTraceChiCol.ColRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapMovedCoreLatticeVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapMovedCoreLatticeVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl.MovedVac

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin S₀.rank → AE D} (hz : z ∈ latA S₀ L₀ (· = v)) :
    d.j0 *ᵥ z ∈ latA S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S₀ L₀ (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    refine smul_mem_latA ha ((hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩)
    · rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
      have : colMul d.jX i ((0 : Fin ρ → AE D) i) = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
      have : colMul d.jY i ((0 : Fin ρ → AE D) i) = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
      exact hy'm
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem wittExt_wittInc_core_hom_eq {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) (u : WO J.W₀ B.V₀) :
    J.d.ext0 B.V (B.d.inc0 J.W₀ u) = B.d.j0 * u * J.d.p0 := rfl

theorem wittExt_wittInc_mem_completed_hom_lattice {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) {LV : Lat J.W} {LV₀ : Lat J.W₀} {L : Lat B.V}
    {M : Lat B.V₀} {v : Pl D} (hV : IsSelfDualC J.W LV) (hV₀ : IsSelfDualC J.W₀ LV₀) (hL : IsSelfDualC B.V L)
    (hmV : MonoAt J.d LV LV₀ v) (hmW : MonoAt B.d L M v) {u : WO J.W₀ B.V₀}
    (hu : u ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (M : Set _) (· = v)) :
    J.d.ext0 B.V (B.d.inc0 J.W₀ u) ∈ latO J.W B.V (LV : Set _) (L : Set _) (· = v) := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D J.W B.V LV L hV hL (· = v)]
  have hmx := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [wittExt_wittInc_core_hom_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (B.d.j0 * u * J.d.p0) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace B.d hmW (GlobalTheory.FinPl.LatMem.latO_maps hV₀ hu ((hmV y).1 hy).2.2)

theorem wittExt_wittInc_isHalf {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) {e : AE D} {u : WO J.W₀ B.V₀}
    (hu : IsHalf e u) : IsHalf e (J.d.ext0 B.V (B.d.inc0 J.W₀ u)) := by
  intro i j
  rw [wittExt_wittInc_core_hom_eq]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  linear_combination (B.d.j0 i k * J.d.p0 l j) * hu k l

end GlobalTheory.FinPl.MovedVac


open GlobalTheory.FinPl.MovedVac in
theorem GlobalTheory.FinPl.movedVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ γ ∈ grpAt B.V₀ (· = v), ∃ M : Lat B.V₀, IsSelfDualC B.V₀ M ∧ Moves B.V₀ γ LW₀ M (· = v) ∧ Vac ψ J.W₀ B.V₀ LV₀ M (· = v) (flatFB s (s.om (1, B.d.emb0 γ) f)) := by
  intro D ψ σ J B s LV LV₀ LW LW₀ v hA _ f hf γ _
  have hflat : IsFlatFB s (· = v) (flatFB s) := (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B s
  obtain ⟨M, hM, hMv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V₀ LW₀ hA.sdW₀).1 γ
  obtain ⟨L', hL', hL'v⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V LW hA.sdW).1 (B.d.emb0 γ)
  have hmono : MonoAt B.d L' M v :=
    (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D B.V LW hA.sdW).2 B.V₀ σ B.d LW₀ M L' γ v hA.monoW (hMv _) (hL'v _)
  have h1 : Moves J.W 1 LV LV (· = v) := fun y _ => by
    rw [show mt J.W 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.one_mulVec]
  have hf' : Vac ψ J.W B.V LV L' (· = v) (s.om (1, B.d.emb0 γ) f) :=
    ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hA.sdV hA.sdW (· = v)
      (fun w hw => hw ▸ hA.tame) f).2.2 hf 1 (B.d.emb0 γ) LV L' hA.sdV hL' h1 (hL'v _))
  refine ⟨M, hM, hMv _, hflat.Heisenberg₂.theta _ hf'.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hu2 : 2 • u ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (M : Set _) (· = v) := nsmul_mem hu 2
    rw [← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu2), map_nsmul, map_nsmul]
    rw [hf'.2.1 _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu)]
  · rw [← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)]
    rw [hf'.2.2 e he _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu) (wittExt_wittInc_isHalf J B hh)]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapMovedCoreLatticeVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondFlatMap_moved_core_lattice_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ γ ∈ grpAt B.V₀ (· = v), ∃ M : Lat B.V₀, IsSelfDualC B.V₀ M ∧ Moves B.V₀ γ LW₀ M (· = v) ∧ Vac ψ J.W₀ B.V₀ LV₀ M (· = v) (flatFB s (s.om (1, B.d.emb0 γ) f)) := by
  first | exact @GlobalTheory.FinPl.movedVac | exact GlobalTheory.FinPl.movedVac | (intros; apply GlobalTheory.FinPl.movedVac <;> assumption)
end
end
