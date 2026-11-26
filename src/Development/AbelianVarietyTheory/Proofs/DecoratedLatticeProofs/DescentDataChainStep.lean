module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinations
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCombinationsComposeFinitelyManyPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCombinationsComposeFinitelyManyPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.LocComp

theorem combAt_o {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (l : GlobalTheory.SeeSaw.LocPl ψ S T M M') {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P l.q.v) : GlobalTheory.FinPl.CombAt P l.o :=
  fun x hx i j => GlobalTheory.LocMod.PinInhab.mem_idAt_of_supp l.q hP (l.o_at x hx i j)

theorem combAt_comp {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {P : GlobalTheory.FinPl.Pl D → Prop} {e e' : WO S T →₀ ℂ} (he : GlobalTheory.FinPl.CombAt P e) (he' : GlobalTheory.FinPl.CombAt P e') :
    ∃ e'', GlobalTheory.FinPl.CombAt P e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f) := by
  have h4 := (GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.2.2.1
  have hm : ∀ {c : WO S T →₀ ℂ}, GlobalTheory.FinPl.CombAt P c → GlobalTheory.FinPl.CombAt (fun p => P p ∨ False) c :=
    fun hc x hx i j => by simpa only [or_false] using hc x hx i j
  obtain ⟨e'', h1, h2⟩ := h4 e e' (hm he) (hm he')
  exact ⟨e'', fun x hx i j => by simpa only [or_false] using h1 x hx i j, h2⟩

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ i, P (L i).q.v) → ∃ o' : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P o' ∧ ∀ F, comb ψ S T o' F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F := by
  intro D ψ hψ S T M M' _ _ n
  induction n with
  | zero =>
    intro L _ P _
    refine ⟨Finsupp.single 0 1, GlobalTheory.FinPl.OffTest.combAt_single_zero P 1, fun F => ?_⟩
    rw [GlobalTheory.FinPl.OffTest.comb_single_zero]
    simp
  | succ n ih =>
    intro L hinj P hP
    obtain ⟨o₁, h₁, h₁'⟩ := ih (fun i => L i.succ) (fun a b h => Fin.succ_injective _ (hinj h)) P (fun i => hP i.succ)
    obtain ⟨o', h', h''⟩ := combAt_comp hψ (combAt_o (L 0) (hP 0)) h₁
    refine ⟨o', h', fun F => ?_⟩
    rw [h'', h₁', List.finRange_succ, List.foldr_cons, List.foldr_map]

end GlobalTheory.LocComp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCombinationsComposeFinitelyManyPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCombinations_compose_finitely_many_places : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ i, P (L i).q.v) → ∃ o' : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P o' ∧ ∀ F, comb ψ S T o' F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F := by
  first | exact @GlobalTheory.LocComp.main | exact GlobalTheory.LocComp.main | (intros; apply GlobalTheory.LocComp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationsDistinctSplitPlacesCollect
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationsDistinctSplitPlacesCollect
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.CollectComb

theorem foldr_comp_eq {ι X : Type} (c o : ι → X → X) (hc : ∀ a b, a ≠ b → ∀ x, c a (o b x) = o b (c a x)) :
    ∀ (l : List ι), l.Nodup → ∀ F : X,
      l.foldr (fun i g => c i (o i g)) F = l.foldr (fun i g => c i g) (l.foldr (fun i g => o i g) F) := by
  have hpast : ∀ (b : ι) (t : List ι), b ∉ t → ∀ x,
      o b (t.foldr (fun i g => c i g) x) = t.foldr (fun i g => c i g) (o b x) := by
    intro b t hb x
    induction t with
    | nil => rfl
    | cons a t ih =>
      have hab : a ≠ b := fun h => hb (h ▸ List.mem_cons_self)
      have hbt : b ∉ t := fun h => hb (List.mem_cons_of_mem _ h)
      simp only [List.foldr_cons]
      rw [← ih hbt, hc a b hab]
  intro l hl F
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    rw [ih hl.2, hpast a t hl.1]

end GlobalTheory.CollectComb

theorem GlobalTheory.CollectComb.main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e g) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F) := by
  intro D ψ hψ S T M M' hM hM' n L hinj F
  have hat : ∀ i, GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).e ∧ GlobalTheory.FinPl.CombAt (· = (L i).q.v) (L i).o := fun i =>
    ⟨fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).e_is.1 u hu),
     fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (L i).q u ((L i).o_at u hu)⟩
  refine GlobalTheory.CollectComb.foldr_comp_eq (fun i g => comb ψ S T (L i).e g) (fun i g => comb ψ S T (L i).o g) ?_ _
    (List.nodup_finRange n) F
  intro a b hab x
  have hdisj : ∀ p, p = (L a).q.v → ¬ p = (L b).q.v := fun p ha hb => hab (hinj (ha.symm.trans hb))
  exact (GlobalTheory.DisjComb.main D ψ hψ S T _ _ hdisj).1 _ _ (hat a).1 (hat b).2 x
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationsDistinctSplitPlacesCollectStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombinations_distinct_split_places_collect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e g) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F) := by
  first | exact @GlobalTheory.CollectComb.main | exact GlobalTheory.CollectComb.main | (intros; apply GlobalTheory.CollectComb.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrSplitPlaceSecondCombinationsVacuumNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrSplitPlaceSecondCombinationsVacuumNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section
namespace GlobalTheory.VacComb

variable {D : D7}

theorem isThetaFunO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T 0 := {
  quasi _ _ := by simp
  level := ⟨⊤, isOpen_univ, fun _ _ _ => funext fun _ => by simp [heisO]⟩
  cont := continuous_const
  smooth _ _ _ _ _ := by simpa using (contDiff_const : ContDiff ℝ _ fun _ : Fin _ → ℝ => (0 : ℂ)) }

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u 0 = 0 :=
  funext fun _ => by simp [heisO]

theorem isModel_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) :
    p.IsModel ψ FS FT (0 : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ)) := {
  theta _ := isThetaFunO_zero ψ S T
  trans _ _ _ _ := by simp [heisO_zero]
  modul _ _ _ _ _ := by simp [heisO_zero] }

theorem model_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {Y Y' : Type} [Fintype Y]
    [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y} {Tm}
    (hTm : p.IsModel ψ FS FT Tm) {Φ₀ : SB (Matrix Y Y' k)} (h₀ : Tm Φ₀ ≠ 0) {O : SB (Matrix Y Y' k)} (hO : O ≠ 0) :
    Tm O ≠ 0 := by
  intro h
  have := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k p Y Y' S T FS FT ψ hψ).1 Tm 0 hTm (isModel_zero p ψ FS FT) O hO (by simpa using h)
  exact h₀ (by rw [this]; rfl)

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

theorem exists_adapted_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (M : GlobalTheory.FinPl.Lat S), IsSelfDualC S M → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y), ∃ G : Frame k S.rank Y, ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((G.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S M (· = q.v) := by
  intro D k _ _ _ _ q S M hM Y _ _ F
  obtain ⟨gl, h1, h2⟩ := GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis D k q S Y F.β F.γ F.βγ F.γβ
  let α : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, h1, h2⟩
  obtain ⟨Λ, hΛ, hα, -⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y α M hM
  have : Λ.IsFullLattice k := by
    refine { toIsLattice := hΛ, span_eq_top := eq_top_iff.mpr fun x _ => ?_ }
    obtain ⟨m, s, c, hs, hc, -⟩ := GlobalTheory.FinPl.FrameLat.exists_gen (p := q) hM
    have hx := congrArg (F.γ *ᵥ ·) (hc (F.β *ᵥ x))
    simp only [Matrix.mulVec_mulVec, F.γβ, Matrix.one_mulVec, Matrix.mulVec_sum,
      Matrix.mulVec_smul] at hx
    rw [hx]
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    apply (hα _).2
    change (fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ fun a => q.pr (incA D (s l a)))) i)) ∈ _
    rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    exact GlobalTheory.FinPl.FrameLat.sec_inc_mem (p := q) (hs l)
  obtain ⟨g, hg⟩ := GlobalTheory.LatPair.exists_smul_lat (GlobalTheory.LatPair.stdLat k Y) Λ
  have hgg : g.1 * (g⁻¹).1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hgg' : (g⁻¹).1 * g.1 = 1 := by rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  refine ⟨⟨F.β * g.1, (g⁻¹).1 * F.γ, ?_, ?_⟩, fun y => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.1, hgg, Matrix.one_mul, F.βγ]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, hgg']
  · have e1 : (∀ i, y i ∈ 𝒪[k]) ↔ g • y ∈ Λ := by
      rw [← hg, GlobalTheory.LatPair.mem_smul_iff, inv_smul_smul, GlobalTheory.LatPair.mem_stdLat]
    rw [e1, hα (g • y)]
    show _ ∈ _ ↔ _ ∈ _
    have e2 : F.β *ᵥ (g • y) = (F.β * g.1) *ᵥ y := by
      rw [← Matrix.mulVec_mulVec]; rfl
    change (fun i => q.sec ((F.β *ᵥ (g • y)) i)) ∈ _ ↔ _
    rw [e2]

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem down_up {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (x : Matrix Y Y' k) : p.down FS FT (p.up FS FT x) = x := by
  unfold Place.down Place.up
  have h : ((FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ := by
    ext i j; simp [p.π_ι]
  rw [h, Matrix.mul_assoc FT.β, ← Matrix.mul_assoc FT.γ, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem exists_model_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ G, GlobalTheory.FinPl.Vac ψ S T M M' (· = q.v) G → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)} (fun _ => 1) → Tm Φ₀ = G := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ hψ M M' hM hM' G hG
  obtain ⟨GS, hGS⟩ := exists_adapted_frame D k q S M hM Y' FS
  obtain ⟨GT, hGT⟩ := exists_adapted_frame D k q T M' hM' Y FT
  obtain ⟨ψk, hch, hcond⟩ := GlobalTheory.SplitWeilChar.weil_char_conductor_one D k q ψ hψ hU
  obtain ⟨Tm', hTm', hO'⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D k q hU Y Y' S T GS GT ψ ψk hψ hch hcond M M' hM hM' hGS hGT).2 G hG
  obtain ⟨Tm, hTm, hrel⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k (ofSplit q) Y Y' S T GS GT Y Y' FS FT ψ Tm' hTm'
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  refine ⟨Tm, hTm, fun Φ₀ h₀ => ?_⟩
  rw [hrel O Φ₀ ?_, hO' O hO]
  intro x
  have hup : (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) = (ofSplit q).up GS GT x :=
    GlobalTheory.LocMod.Place.up_chg (ofSplit q) GS GT FS FT x
  rw [hO, h₀]
  by_cases hx : ∀ r s, x r s ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (show x ∈ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_mem]
    show (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v)
    rw [hup]
    exact GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT x hx
  · rw [Set.indicator_of_notMem (show x ∉ {x : Matrix Y Y' k | ∀ r s, x r s ∈ 𝒪[k]} from hx), Set.indicator_of_notMem]
    intro hmem
    change (ofSplit q).up FS FT (FT.γ * GT.β * x * (GS.γ * FS.β)) ∈ latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) (· = q.v) at hmem
    rw [hup] at hmem
    obtain ⟨x', hx', he⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T GS GT M M' hM hM' hGS hGT _ hmem
      (GlobalTheory.LocMod.Witness.up_half (ofSplit q) GS GT x)
    have : x = x' := by rw [← down_up (ofSplit q) GS GT x, he, down_up]
    exact hx (this ▸ hx')

end GlobalTheory.VacComb

namespace GlobalTheory.VacComb

variable {D : D7}

theorem comb_o_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hM : IsSelfDualC S M) (hM' : IsSelfDualC T M')
    (L : LocPl ψ S T M M') {G : WO S T → ℂ} (hG : GlobalTheory.FinPl.Vac ψ S T M M' (· = L.q.v) G) (hG0 : G ≠ 0) :
    comb ψ S T L.o G ≠ 0 := by
  obtain ⟨Tm, hTm, hTG⟩ := exists_model_vac D L.k L.q L.unit L.Y L.Y' S T L.FS L.FT ψ hψ M M' hM hM' G hG
  obtain ⟨Φ₀, h₀⟩ := GlobalTheory.SeeSaw.LocPlModel.exists_latInd L.q L.unit L.FS L.FT hM hM'
  obtain ⟨O, hO, hO0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := L.k) (Y := L.Y) (Y' := L.Y')
  have hO' : O ≠ 0 := by rintro rfl; simp at hO0
  rw [← hTG Φ₀ h₀, ← L.o_is Tm hTm Φ₀ O hO h₀]
  exact model_ne_zero _ hψ hTm (by rwa [hTG Φ₀ h₀]) hO'

theorem combAt_o {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T}
    (L : LocPl ψ S T M M') : GlobalTheory.FinPl.CombAt (· = L.q.v) L.o := fun u hu r c =>
  (GlobalTheory.FinPl.FrameLat.idem_iff L.q _).2 (L.o_at u hu r c)

theorem foldr_comb_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) F → F ≠ 0 → (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F ≠ 0 := by
  intro D ψ hψ S T M M' hM hM' n L hL F hF hF0
  have hI := fun P P' hd => GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D ψ hψ S T P P' hd
  let g : Fin n → (WO S T → ℂ) → (WO S T → ℂ) := fun i f => comb ψ S T (L i).o f
  have key : ∀ l : List (Fin n), l.Nodup → l.foldr g F ≠ 0 ∧
      ∀ j, j ∉ l → GlobalTheory.FinPl.Vac ψ S T M M' (· = (L j).q.v) (l.foldr g F) := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨hF0, fun j _ => GlobalTheory.GSuppComb.vac_mono (fun _ _ => trivial) hF⟩
    | cons a l ih =>
      intro hl
      obtain ⟨ha, hl'⟩ := List.nodup_cons.1 hl
      obtain ⟨h0, hv⟩ := ih hl'
      have hdisj : ∀ j, j ≠ a → ∀ p, p = (L a).q.v → ¬ p = (L j).q.v := fun j hj p hp hq =>
        hj (hL (hq.symm.trans hp))
      refine ⟨comb_o_ne_zero hψ hM hM' (L a) (hv a ha) h0, fun j hj => ?_⟩
      have hja : j ≠ a := fun h => hj (h ▸ List.mem_cons_self)
      have hjl : j ∉ l := fun h => hj (List.mem_cons_of_mem _ h)
      exact ((hI _ _ (hdisj j hja)).2.1 _ (combAt_o (L a))).2 M M' _ (hv j hjl)
  exact (key _ (List.nodup_finRange n)).1

end GlobalTheory.VacComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrSplitPlaceSecondCombinationsVacuumNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.foldr_splitPlaceSecondCombinations_vacuum_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, GlobalTheory.FinPl.Vac ψ S T M M' (fun _ => True) F → F ≠ 0 → (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F ≠ 0 := by
  first | exact @GlobalTheory.VacComb.foldr_comb_ne_zero | exact GlobalTheory.VacComb.foldr_comb_ne_zero | (intros; apply GlobalTheory.VacComb.foldr_comb_ne_zero <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDatum

theorem vac_true_mono {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    (P : GlobalTheory.FinPl.Pl D → Prop) {F : WO S T → ℂ} (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) F) :
    GlobalTheory.FinPl.Vac ψ S T LS LT P F := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun _ hv => (hv trivial).elim, rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

end GlobalTheory.MidDatum
