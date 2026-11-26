module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FramedPointGeneratorIsThetaLevelOne
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InvariantOperatorValueTriangularChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TranslExist

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

private theorem mem_wchart_lemma {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (y : Y) : y ∈ L.wchart φ j ↔ ∀ k, φ k y ∈ L.U (j k) := by
  unfold LB.wchart
  show y ∈ (⋂ k, (φ k) ⁻¹' (L.U (j k) : Set X)) ↔ _
  simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]

theorem twist_congr (hL : L.IsLB) {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    (h : ∀ y J, Good L y J → val α (𝟙 _) y J = val α' (𝟙 _) y J) {s : LB.Sec (LPow A L b T)}
    {s' s'' : LB.Sec (LPow A L a T)} (h' : IsTwistPull A L ψ m hm a b α s s')
    (h'' : IsTwistPull A L ψ m hm a b α' s s'') : s' = s'' := by
  unfold IsTwistPull at h' h''
  have hf : ∀ i, s'.f i = s''.f i := by
    intro i
    obtain ⟨i0, rfl⟩ : ∃ i0 : L.ι, i = (fun _ : Fin 1 => i0) := ⟨i 0, funext fun k => by fin_cases k; rfl⟩
    apply fn_ext
    intro x hx
    have hx0 : (snd T A).left x ∈ L.U i0 :=
      (mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) x).mp hx 0
    obtain ⟨j1, hj1, hj1'⟩ : ∃ j1 : L.ι, m.left x ∈ L.U j1 ∧ (m.left = (snd T A).left → j1 = i0) := by
      by_cases e : m.left = (snd T A).left
      · exact ⟨i0, by rw [e]; exact hx0, fun _ => rfl⟩
      · have hc : m.left x ∈ (⨆ k, L.U k) := by rw [hL.cover]; trivial
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
        exact ⟨k, hk, fun h => absurd h e⟩
    let j : Fin 2 → L.ι := ![i0, j1]
    have hxW : x ∈ L.wchart ![(snd T A).left, m.left] j := by
      rw [mem_wchart_lemma]
      intro k
      fin_cases k
      · exact hx0
      · exact hj1
    obtain ⟨J, hJ, hJk⟩ := exists_good L hL x ![(snd T A).left, m.left] j (by
      intro p q hpq
      fin_cases p <;> fin_cases q
      · rfl
      · exact (hj1' hpq.symm).symm
      · exact hj1' hpq
      · rfl) (by
      intro k
      fin_cases k
      · exact hx0
      · exact hj1)
    have hv := h x J hJ
    rw [val_of α (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k),
      val_of α' (𝟙 _) x J j (fun k => by rw [Category.id_comp]; exact hJk k)] at hv
    have hle : L.wchart ![(snd T A).left, m.left] j ≤ (LPow A L a T).U (fun _ : Fin 1 => i0) := by
      intro y hy
      exact (mem_wchart_lemma L (fun _ : Fin 1 => (snd T A).left) (fun _ => i0) y).mpr
        (fun _ => (mem_wchart_lemma L _ j y).mp hy 0)
    have e1 := congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h' j)
    have e2 := congrArg (gs (𝟙 _) x (L.wchart ![(snd T A).left, m.left] j)) (h'' j)
    rw [gs_mul _ _ _ hxW] at e1 e2
    have hu : gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α.s j).val =
        gs (𝟙 (T ⊗ A).left) x (L.wchart ![(snd T A).left, m.left] j) (α'.s j).val := by
      exact (gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α.s j)).trans
        ((congrArg Units.val hv).trans (gs_unit (𝟙 (T ⊗ A).left) x _ hxW (α'.s j)).symm)
    have r1 := gs_res (𝟙 (T ⊗ A).left) x hle hxW (s'.f fun _ => i0)
    have r2 := gs_res (𝟙 (T ⊗ A).left) x hle hxW (s''.f fun _ => i0)
    exact r1.symm.trans (e1.trans ((congrArg (· * _) hu).trans (e2.symm.trans r2)))
  obtain ⟨f1, p1⟩ := s'
  obtain ⟨f2, p2⟩ := s''
  have : f1 = f2 := funext hf
  subst this
  rfl

theorem act_congr (hL : L.IsLB) {T : Over S} {k : ℤ} {U U' : ThetaGrp A L k T} (hp : U.pt = U'.pt)
    (h : LB.Gen.Corr L _ _ _ _ U.φ U'.φ) {s s' s'' : LB.Sec (LPow A L k T)} (h' : IsActOf A L k U s s')
    (h'' : IsActOf A L k U' s s'') : s' = s'' := by
  obtain ⟨pt, φ, hφ⟩ := U
  obtain ⟨pt', φ', hφ'⟩ := U'
  simp only at hp
  subst hp
  unfold IsActOf at h' h''
  exact twist_congr hL (fun y J hJ => val_corr hJ h (𝟙 _)) h' h''

end TranslExist


open TranslExist in
theorem exists_isVtOver_and_existsUnique_isUUOver : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)), (∀ (ok : (T ⟶ Xo.univ.t.G) → Prop) (t t' : T ⟶ Xo.univ.t.G), t' ^ N = t → t' ^ (N ^ 2) = 1 → ok t' → ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F) ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → ∃! F, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F := by
  intro hLaws E _ _ _ H Dw l Xo N hN T s
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨α₀, hg₀, hn₀, hu₀, hT⟩ := GlobalTheory.T.universal_normalised_mulByNat_pullback_iso hLaws E H Dw l Xo N
  obtain ⟨α, hgα, hcα⟩ := hT T
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G T N)
      (snd T Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ :=
    (existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ α hgα s).exists
  have hact : ∀ (U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)
      (a : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)),
      ∃ b, IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U a b := by
    intro U a
    unfold IsActOf
    exact (existsUnique_isTwistPull _ _ _ hL _ _ _ _ _ _ U.φ U.isGen a).exists
  refine ⟨fun ok t t' h1 h2 h3 => ?_, fun x₁ x₂ hx₁ hx₂ => ?_⟩
  · obtain ⟨U, hU⟩ := (GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T t' h2).1
    obtain ⟨F, hF⟩ := hact U s₁
    exact ⟨F, t', α₀, α, s₁, U, h1, h3, hg₀, hn₀, hcα, hs₁, hU, hF⟩
  · have S₁ := GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T x₁ hx₁
    have S₂ := GlobalTheory.T.universal_symLift_exists_unique_global hLaws E H Dw l Xo N hN T x₂ hx₂
    obtain ⟨U₁, hU₁⟩ := S₁.1
    obtain ⟨U₂, hU₂⟩ := S₂.1
    obtain ⟨s₂, hs₂⟩ := hact U₁ s₁
    obtain ⟨F, hF⟩ := hact U₂ s₂
    refine ⟨F, ⟨α₀, α, s₁, s₂, U₁, U₂, hg₀, hn₀, hcα, hs₁, hU₁, hs₂, hU₂, hF⟩, ?_⟩
    rintro F' ⟨β₀, β, t₁, t₂, V₁, V₂, hgβ₀, hnβ₀, hcβ, ht₁, hV₁, ht₂, hV₂, hF'⟩
    have e₁ : t₁ = s₁ := by
      refine twist_congr hL (fun y J hJ => ?_) ht₁ hs₁
      exact (val_corr hJ hcβ _).trans ((val_pull hJ β₀ _ _).trans ((val_corr hJ (hu₀ β₀ hgβ₀ hnβ₀) _).trans
        ((val_corr hJ hcα _).trans (val_pull hJ α₀ _ _)).symm))
    rw [e₁] at ht₂
    have e₂ : t₂ = s₂ :=
      act_congr hL (hV₁.pt_eq.trans hU₁.pt_eq.symm) (S₁.2 V₁ U₁ hV₁ hU₁) ht₂ hs₂
    rw [e₂] at hF'
    exact act_congr hL (hV₂.pt_eq.trans hU₂.pt_eq.symm) (S₂.2 V₂ U₂ hV₂ hU₂) hF' hF

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translation_sections_universal_object : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)), (∀ (ok : (T ⟶ Xo.univ.t.G) → Prop) (t t' : T ⟶ Xo.univ.t.G), t' ^ N = t → t' ^ (N ^ 2) = 1 → ok t' → ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP N ok s t F) ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → ∃! F, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F := by
  first | exact @GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver | exact GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver | (intros; apply GlobalTheory.exists_isVtOver_and_existsUnique_isUUOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsVtOverIsUUOverBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VtBaseChange

theorem exists_mulTwist {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) (N : ℕ) {T T' : Over S}
    (h : T' ⟶ T) {s : LB.Sec (LPow A L 1 T)} {s' : LB.Sec (LPow A L 1 T')}
    (hs : IsPullSec A L 1 (h ▷ A) (whiskerRight_snd _ _) s s')
    {α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])} (g₀ : α₀.IsGen)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1])}
    (cα : LB.Gen.Corr L _ _ _ _ α (LB.pullGen L _ _ α₀ (snd T A).left))
    {s₁ : LB.Sec (LPow A L ((N : ℤ) ^ 2) T)}
    (tw : IsTwistPull A L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁) :
    ∃ α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, (snd T' A ^ N).left] ![(N : ℤ) ^ 2, -1]),
      LB.Gen.Corr L _ _ _ _ α' (LB.pullGen L _ _ α₀ (snd T' A).left) ∧
      IsTwistPull A L (mulT A T' N) (snd T' A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α' s'
        (GlobalTheory.VVRank.pullS A ((N : ℤ) ^ 2) h s₁) := by
  have e1 : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := GlobalTheory.VVRank.whisker_snd_left A h
  have e2 : (snd T' A).left ≫ (mulA A N).left = (snd T' A ^ N).left := by
    unfold mulA
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hm0 : mulT A T' N ≫ (h ▷ A) = (h ▷ A) ≫ mulT A T N := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [mulT]
    · simp [mulT, MonObj.comp_pow]
  have hm : (mulT A T' N).left ≫ (h ▷ A).left = (h ▷ A).left ≫ (mulT A T N).left := by
    rw [← Over.comp_left, hm0, Over.comp_left]
  obtain ⟨α', gα', vα'⟩ := GlobalTheory.VVRank.exists_gen_pullTo (φ' := ![(snd T' A).left, (snd T' A ^ N).left])
    α₀ g₀ (snd T' A).left (by intro k; fin_cases k; exacts [Category.comp_id _, e2])
  refine ⟨α', ?_, ?_⟩
  · refine corr_of_val hL fun y J hJ => ?_
    rw [vα' _ (𝟙 _) y J hJ, val_pull hJ]
  · obtain rfl := GlobalTheory.TwistBaseChange.eq_pullS_of_isPullSec A 1 h hs
    refine GlobalTheory.VVRank.isTwistPull_of_sv A hL gα' fun y J hJ => ?_
    rw [GlobalTheory.VVRank.sv_pullS A _ h s₁ _ y hJ, GlobalTheory.VVRank.sv_of_isTwistPull A tw _ y hJ,
      GlobalTheory.VVRank.sv_pullS A _ h s _ y hJ, vα' _ (𝟙 _) y J hJ, val_corr hJ cα, val_pull hJ]
    simp only [Category.id_comp, e1, hm]

theorem isVtOver_isUUOver_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ) (I : Ideal (𝓞 E)) (T T' : Over Xo.X) (h : T' ⟶ T) (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T)) (s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 T')), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) s s' → ∀ (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T)) (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T')), IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' → (∀ t : T ⟶ Xo.univ.t.G, IsVtOver Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo I) s t F → IsVtOver Xo.univ.t.G Xo.univ.t.PP N (KilledBy Xo I) s' (h ≫ t) F') ∧ ∀ x₁ x₂ : T ⟶ Xo.univ.t.G, IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s' (h ≫ x₁) (h ≫ x₂) F' := by
  intro E _ _ _ H Dw l Xo N I T T' h s s' hs F F' hF
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  refine ⟨fun t hV => ?_, fun x₁ x₂ hU => ?_⟩
  · unfold IsVtOver at hV ⊢
    obtain ⟨t₀, α₀, α, s₁, U, ht, hok, g₀, hnm, cα, tw, hsym, hact⟩ := hV
    obtain ⟨α', cα', tw'⟩ := exists_mulTwist Xo.univ.t.G hL N h hs g₀ cα tw
    obtain ⟨U', -, -, hsym', hact'⟩ := GlobalTheory.T.exists_symLift_pullback_isActOf _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U
    refine ⟨h ≫ t₀, α₀, α', _, U', ?_, ?_, g₀, hnm, cα', tw', hsym' _ _ hsym,
      hact' _ _ _ _ hact (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₁) hF⟩
    · rw [← MonObj.comp_pow, ht]
    · unfold KilledBy at hok ⊢
      intro a ha
      rw [Category.assoc, hok a ha, MonObj.comp_one]
  · unfold IsUUOver at hU ⊢
    obtain ⟨α₀, α, s₁, s₂, U₁, U₂, g₀, hnm, cα, tw, hsym₁, hact₁, hsym₂, hact₂⟩ := hU
    obtain ⟨α', cα', tw'⟩ := exists_mulTwist Xo.univ.t.G hL N h hs g₀ cα tw
    obtain ⟨U₁', -, -, hsym₁', hact₁'⟩ := GlobalTheory.T.exists_symLift_pullback_isActOf _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U₁
    obtain ⟨U₂', -, -, hsym₂', hact₂'⟩ := GlobalTheory.T.exists_symLift_pullback_isActOf _ Xo.univ.t.G Xo.univ.t.PP.L hL _ T T' h U₂
    exact ⟨α₀, α', _, _, U₁', U₂', g₀, hnm, cα', tw', hsym₁' _ _ hsym₁,
      hact₁' _ _ _ _ hact₁ (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₁) (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₂),
      hsym₂' _ _ hsym₂, hact₂' _ _ _ _ hact₂ (GlobalTheory.VVRank.isPullSec_pullS _ _ h s₂) hF⟩

end GlobalTheory.VtBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding perFr Unf relab toC gxFst gxSnd GoodEmb
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VSetup

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hcc : ∀ x : E, φ (cc x) = conj (φ x) := fun x => by
    simp [cc, IsCMField.complexEmbedding_complexConj]
  have hrt : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq
    simpa using this
  have htw : 2 * (H.w0 : E) = 1 + H.rt := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  have hz : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    simpa using congrArg φ hrt
  have hzc : conj (φ (H.rt : E)) = -φ (H.rt : E) := by
    set z := φ (H.rt : E)
    have hz' : conj z ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow, hz]; simp
    have h1 : (conj z - z) * (conj z + z) = 0 := by
      linear_combination hz' - hz
    rcases mul_eq_zero.1 h1 with h | h
    · exfalso
      have him : z.im = 0 := by
        have := congrArg Complex.im h
        simp at this
        linarith
      have hre := congrArg Complex.re hz
      simp [sq, him] at hre
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [mul_self_nonneg z.re]
    · linear_combination h
  have hw : 2 * φ (H.w0 : E) = 1 + φ (H.rt : E) := by
    have := congrArg φ htw
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  have hwc : 2 * conj (φ (H.w0 : E)) = 1 + conj (φ (H.rt : E)) := by
    have := congrArg conj hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat] at this
    exact this
  apply φ.injective
  rw [map_add (f := _), map_one, hcc]
  linear_combination (hw + hwc + hzc) / 2

theorem exists_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ k (x : (U.X k).dom), IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ (W : UW U) (Dc : Dic Dw c σ (U.X k) W.g Dw.p n a) (A : AnFib (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x)) (θ : (Fin W.g → ℂ) → ℂ) (v : TF n W.g) (κ : ℂ), Dc.e = W.e ∧ W.g = fdeg E * r ∧ (H.w0 : E) + cc (H.w0 : E) = 1 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ A.Marked (W.mark k) ∧ A.Reads 1 (unC U k x).s θ ∧ IsTheta1 (U.X k) Dc.bas Dc.idx (H.w0 : E) x.1 (U.X k).Λ θ ∧ MeanOne (U.X k) Dc.bas Dc.idx x.1 (U.X k).Λ θ ∧ IsVac (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v ∧ ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA (U.X k) Dc.bas Dc.idx v x.1 z := by
  intro E _ _ _ H Dw l Xo c σ r U hG hU hr a n hD k x hx
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hn : Even n := by unfold Dom at hD; exact hD.2
  have hrpq : r = Dw.p + Dw.q := by unfold Formalism.L2.PjFree.IsUnf at hU; exact hU.1
  have hXk : (U.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0 := by
    unfold Formalism.L2.PjFree.IsUnf at hU; exact hU.2.1 k
  obtain ⟨W⟩ := nonempty_uw hU
  obtain ⟨-, hSD, hMk, -⟩ := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hG hU hr W k
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.T.exists_letterRowWeightDictionary E H Dw l c σ r W.g n (U.X k) a W.e hG hrpq hXk.1 hXk.2 hSD hD
  have hper : ∀ y v j, pv (U.X k) Dc.idx y v j = perFr (U.X k) y v (relab c σ (W.e j).1) (W.e j).2 := by
    intro y v j; rw [← hDe]; exact Dc.per_eq y v j
  have hty : ∀ j, rowType (U.X k) (Dc.idx j) = relab c σ (W.e j).1 := by
    intro j; rw [← hDe]; exact Dc.ty_eq j
  obtain ⟨A, hAm, θ, hAr, hM1⟩ :=
    GlobalTheory.T.analyticFibre_unitFrame_uniformisation E H Dw l Xo c σ r U hG hU hr W k Dc.bas Dc.idx Dc.sympl hper hty x hx
  have hθ := GlobalTheory.T.framedPoint_generator_isThetaLevelOne E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x) A
    Dc.sympl x.2 hSD θ hAr
  have hw : (H.w0 : E) + cc (H.w0 : E) = 1 := hostHalfRoot_add_conj_eq_one H
  have hint : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _ hint hw _ hSD 1
    (stdL E n) (GlobalTheory.SW.Base.stdL_mem_Vset n 1)).1
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.prod_levelOne_theta_eq_vacuum_theta E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _ hint hw _ hSD v hv x.1 x.2 θ hθ
  have hg : W.g = fdeg E * r := by
    have hc := Fintype.card_congr Dc.idx
    rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin,
      ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi] at hc
    exact hc
  exact ⟨W, Dc, A, θ, v, κ, hDe, hg, hw, hSD, hMk, hAm, hAr, hθ, hM1, hv, hκ⟩

end GlobalTheory.Dict.VSetup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticDataUnitFrameFramedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding perFr Unf relab toC gxFst gxSnd GoodEmb
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticData_unitFrame_framedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ k (x : (U.X k).dom), IsUnitFr (U.X k) x.1 → letI : Algebra c.F ℂ := σ.toAlgebra; ∃ (W : UW U) (Dc : Dic Dw c σ (U.X k) W.g Dw.p n a) (A : AnFib (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x)) (θ : (Fin W.g → ℂ) → ℂ) (v : TF n W.g) (κ : ℂ), Dc.e = W.e ∧ W.g = fdeg E * r ∧ (H.w0 : E) + cc (H.w0 : E) = 1 ∧ SelfD (U.X k) (U.X k).Λ ∧ IsMark l (U.X k).Λ (W.mark k) ∧ A.Marked (W.mark k) ∧ A.Reads 1 (unC U k x).s θ ∧ IsTheta1 (U.X k) Dc.bas Dc.idx (H.w0 : E) x.1 (U.X k).Λ θ ∧ MeanOne (U.X k) Dc.bas Dc.idx x.1 (U.X k).Λ θ ∧ IsVac (U.X k) Dc.bas (H.w0 : E) (tens (stdL E n) (U.X k).Λ) v ∧ ∀ z : Fin n → Fin W.g → ℂ, ∏ b, θ (z b) = κ * thA (U.X k) Dc.bas Dc.idx v x.1 z := by
  first | exact @GlobalTheory.Dict.VSetup.exists_setup | exact GlobalTheory.Dict.VSetup.exists_setup | (intros; apply GlobalTheory.Dict.VSetup.exists_setup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicSumTriangularFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicSumTriangularFrameChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TriangularFrame

theorem basis_of_triangular {T : Type} [Fintype T] {r : T → ℕ} {S : Type} [CommRing S] {d : ℕ}
    (u : (Σ τ : T, Fin (r τ)) → Fin d → S) (cf : ∀ τ : T, Fin (r τ) → Fin (r τ) → S)
    (h0 : ∀ τ i j, i < j → cf τ i j = 0) (h1 : ∀ τ i, IsUnit (cf τ i i))
    (hb : ∀ v : Fin d → S, ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j) (v : Fin d → S) :
    ∃! a : (Σ τ : T, Fin (r τ)) → S, ∀ e, ∑ ℓ, a ℓ * (∑ j, cf ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) = v e := by
  classical
  have hdet : ∀ τ, IsUnit (Matrix.of (cf τ)).det := fun τ => by
    rw [Matrix.det_of_lowerTriangular (Matrix.of (cf τ)) (fun i j hij => h0 τ i j (by simpa using hij))]
    exact IsUnit.prod_iff.2 fun i _ => h1 τ i
  have key : ∀ (a : (Σ τ : T, Fin (r τ)) → S) e, ∑ ℓ, a ℓ * (∑ j, cf ℓ.1 ℓ.2 j * u ⟨ℓ.1, j⟩ e) =
      ∑ ℓ : (Σ τ : T, Fin (r τ)), Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1)) ℓ.2 * u ℓ e := by
    intro a e
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    simp only [_root_.mul_assoc]
    exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (i j : Fin (r τ)) => a ⟨τ, i⟩ * (cf τ i j * u ⟨τ, j⟩ e))
  simp only [key]
  obtain ⟨b, hb1, hb2⟩ := hb v
  have back : ∀ a : (Σ τ : T, Fin (r τ)) → S,
      (∀ e, ∑ ℓ : (Σ τ : T, Fin (r τ)), Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1)) ℓ.2 * u ℓ e = v e) →
      a = fun ℓ => Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹ ℓ.2 := by
    intro a ha
    have := hb2 _ ha
    subst this
    funext ℓ
    show _ = Matrix.vecMul (Matrix.vecMul (fun i => a ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))) _ _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (hdet _), Matrix.vecMul_one]
  refine ⟨fun ℓ => Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹ ℓ.2, fun e => ?_, back⟩
  rw [← hb1 e]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 1
  show Matrix.vecMul (Matrix.vecMul (fun i => b ⟨ℓ.1, i⟩) (Matrix.of (cf ℓ.1))⁻¹) _ _ = _
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hdet _), Matrix.vecMul_one]

theorem fst_comp_jetTan {S : Type} [CommRing S] {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (TrivSqZeroExt.fstHom S S S).comp (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show TrivSqZeroExt.fst (MvPolynomial.aeval
    (fun i => if i = ℓ then (DualNumber.eps : DualNumber S) else 0) (MvPolynomial.X i : MvPolynomial κ S)) =
    MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X i : MvPolynomial κ S)
  by_cases h : i = ℓ <;> simp [h]

theorem left_one {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  show (toUnit X ≫ η[M]).left = _
  rw [Over.comp_left]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem isTanAt_jetTan {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X) {κ : Type} [DecidableEq κ]
    (x : overAt x0 (Jet S κ (0 + 1)) ⟶ Xo.univ.t.G)
    (hx : homAt x0 (jetAug : Jet S κ (0 + 1) →ₐ[S] S) ≫ x = 1) (ℓ : κ) :
    IsTanAt x0 (homAt x0 (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S) ≫ x).left := by
  refine ⟨Over.w _, ?_⟩
  have h1 := congrArg (fun f => f.left) hx
  simp only [Over.comp_left, left_one] at h1 ⊢
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫
      (homAt x0 (jetTan ℓ : Jet S κ (0 + 1) →ₐ[S] DualNumber S)).left =
      (homAt x0 (jetAug : Jet S κ (0 + 1) →ₐ[S] S)).left := by
    rw [← fst_comp_jetTan ℓ]
    exact (Spec.map_comp _ _).symm
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) e)).trans (h1.trans ?_)
  have e' : spMap (algebraMap S S) = 𝟙 _ := Spec.map_id _
  show (spMap (algebraMap S S) ≫ x0) ≫ _ = x0 ≫ _
  rw [e', Category.id_comp]

theorem eq_of_isPullSec_id {X : Scheme.{0}} (A : Over X) [GrpObj A] (L : LB A.left) (k : ℤ) (T : Over X)
    (F F' : LB.Sec (LPow A L k T)) (h : IsPullSec A L k (𝟙 T ▷ A) (whiskerRight_snd _ _) F F') : F' = F := by
  have key : ∀ (g : T ⊗ A ⟶ T ⊗ A) (hg : g ≫ snd T A = snd T A), g = 𝟙 _ → IsPullSec A L k g hg F F' → F' = F := by
    intro g hg e h
    subst e
    obtain ⟨f, hf⟩ := F
    obtain ⟨f', hf'⟩ := F'
    congr
    funext j
    refine (h j).trans ?_
    show ((T ⊗ A).left.presheaf.map (𝟙 _)).hom (f j) = f j
    rw [CategoryTheory.Functor.map_id]
    rfl
  exact key _ _ (MonoidalCategory.id_whiskerRight _ _) h

theorem sum_eq (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (ho u' h1 h2 h3 s' h4)
    (cf : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin (Dw.mult τ) → S)
    (h0 : ∀ τ i j, i < j → cf τ i j = 0) (hu : ∀ τ i, IsUnit (cf τ i i))
    (hcomb : ∀ τ i, IsCombAt y.x (y.u τ) (cf τ i) (u' τ i)) (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) (k : ℕ)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
        ∏ b, nab (⟨y.x, ho, u', h1, h2, h3, s', h4⟩ : FrPt Xo c S) k (F b) (colOf m b) =
      (∏ ℓ : Lt1 Dw, cf ℓ.1 ℓ.2 ℓ.2 ^ a (ℓ.1, ℓ.2)) *
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y k (F b) (colOf m b) := by
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  set y' : FrPt Xo c S := ⟨y.x, ho, u', h1, h2, h3, s', h4⟩ with hy'
  obtain ⟨C, hex, hpin⟩ := hnab.2 S y
  obtain ⟨C', hex', hpin'⟩ := hnab.2 S y'
  choose f hf using fun b => hex k (F b)
  choose f' hf' using fun b => hex' k (F b)
  let uv : Lt1 Dw → Fin C.d → S := fun ℓ e => ∑ j, cf ℓ.1 ℓ.2 j * C.uvec ⟨ℓ.1, j⟩ e
  let D : ChartAt Xo c y' :=
    ⟨C.d, C.B, uv, C.x, C.e, C.wP, C.h,
      ⟨C.chart.zero, C.chart.trunc, C.chart.law, C.chart.act, fun ℓ => by
        have := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x _
          (fun j => isTanAt_jetTan y.x (C.x 1) (C.chart.zero 1) ((0 : Fin 1), j)) (y.u ℓ.1)
          (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e) (cf ℓ.1 ℓ.2) (u' ℓ.1 ℓ.2)
          (fun i => C.chart.tan ⟨ℓ.1, i⟩) (hcomb ℓ.1 ℓ.2)
        have e : (Matrix.of fun e j => C.uvec ⟨ℓ.1, j⟩ e).mulVec (cf ℓ.1 ℓ.2) = uv ℓ := by
          funext e
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, uv]
          exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
        rw [e] at this
        exact this,
        basis_of_triangular C.uvec cf h0 hu C.chart.basis⟩,
      ⟨C.frame.gen, C.frame.ph1, C.frame.ph2, C.frame.sy, C.frame.ad⟩, C.prim, C.gauge, C.rig0⟩
  obtain ⟨N, hN, hNP, hsupp⟩ := GlobalTheory.exists_natCast_smul_mem_harmA E H Dw l c a n P hP
  have hI := hC E H Dw l Xo c hnab.1 S y' C' D k n F f' f hf' hf a _ hNP
  have hNu : IsUnit (algebraMap c.F S (N : c.F)) :=
    (IsUnit.mk0 (N : c.F) (Nat.cast_ne_zero.2 hN.ne')).map _
  have hsc : ∀ (C₀ : ChartAt Xo c y') (g : Fin n → MvPowerSeries (Fin 1 × Fin C₀.d) S),
      chartVal C₀ k g ((N : c.F) • P) = algebraMap c.F S (N : c.F) * chartVal C₀ k g P := by
    intro C₀ g
    simp only [chartVal, hsupp, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]
  rw [hsc, hsc] at hI
  have hI' := hNu.mul_left_cancel hI
  have e₁ : ∀ m, ∏ b, nab y k (F b) (colOf m b) =
      ∏ b, C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin k (F b) (f b) (hf b) (colOf m b)
  have e₂ : ∀ m, ∏ b, nab y' k (F b) (colOf m b) =
      ∏ b, C'.B.nabVal S C'.h H.w0 k (f' b) C'.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin' k (F b) (f' b) (hf' b) (colOf m b)
  simp only [e₁]
  exact (Finset.sum_congr rfl fun m _ => congrArg _ (e₂ m)).trans <| hI'.trans (GlobalTheory.T.invariantOperator_value_triangular_change E H Dw l c S C.d C.B C.h C.gauge k n f C.uvec uv cf h0 (fun _ _ _ => rfl) hu a P hP)

theorem harmonic_sum_frBor : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = 𝟙 _ → ∀ (n : ℕ), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) = (∏ ℓ : Lt1 Dw, ((t (some ℓ) : Sˣ) : S) ^ a (ℓ.1, ℓ.2)) * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y y' t hb h hh n a P hP N
  obtain ⟨x', ho, u', h1, h2, h3, s', h4⟩ := y'
  obtain ⟨hx, hcf, -⟩ := hb
  dsimp only at hx
  subst hx
  choose cf hd h0 hcomb using hcf
  have e : h = 𝟙 _ := Over.OverMorphism.ext hh
  subst e
  have hk : ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) := (Nat.cast_pow N 2).symm
  generalize ((N : ℤ) ^ 2) = K at hk
  subst hk
  intro F F' hF
  have hFF : F' = F := funext fun b => eq_of_isPullSec_id _ _ _ _ _ _ (hF b)
  subst hFF
  have := sum_eq hC nab hnab y ho u' h1 h2 h3 s' h4 cf h0 (fun τ i => by rw [hd]; exact Units.isUnit _) hcomb
    n a P hP (N ^ 2) F'
  simp only [hd] at this
  exact this

end GlobalTheory.TriangularFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicSumTriangularFrameChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_sum_triangular_frameChange : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = 𝟙 _ → ∀ (n : ℕ), ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) = (∏ ℓ : Lt1 Dw, ((t (some ℓ) : Sˣ) : S) ^ a (ℓ.1, ℓ.2)) * ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) := by
  first | exact @GlobalTheory.TriangularFrame.harmonic_sum_frBor | exact GlobalTheory.TriangularFrame.harmonic_sum_frBor | (intros; apply GlobalTheory.TriangularFrame.harmonic_sum_frBor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorsionIsotropicCommutatorPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SqDvdSumAlternatingFormsOfKilledLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SqDvdSumAlternatingFormsOfKilledLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sq_dvd_sum_EF_of_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a a' : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a' j)) → ((N : ℤ) ^ 2) ∣ ∑ b, Dw.EF (a b) (a' b) := by
  intro E _ _ _ H Dw n Λ N hU hN hle a a' ha ha'
  obtain ⟨m, x, v, hv, hav⟩ := (GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN hle a).1 ha
  obtain ⟨m', x', v', hv', hav'⟩ := (GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN hle a').1 ha'
  have key : ∑ b, Dw.EF (a b) (a' b)
      = ∑ i, ∑ j, Dw.EF (x i) ((∑ b, H.bar (v i b) * v' j b) • x' j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hav, hav', Finset.sum_smul, map_sum, LinearMap.sum_apply, Dw.adj, mul_smul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin n)))]
    exact Finset.sum_comm
  rw [key]
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  obtain ⟨w, hw, hvw⟩ := hv i
  obtain ⟨w', hw', hvw'⟩ := hv' j
  obtain ⟨c, hc⟩ := (hU w).1 hw w' hw'
  have hs : (∑ b, H.bar (v i b) * v' j b) = ((N : ℤ) ^ 2) • c := by
    apply IsFractionRing.injective (𝓞 E) E
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zsmul, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, H.bar_eq,
      hvw, hvw', map_mul, map_natCast, zsmul_eq_mul]
    push_cast
    ring
  rw [hs, smul_assoc, map_zsmul, smul_eq_mul]
  exact dvd_mul_right _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SqDvdSumAlternatingFormsOfKilledLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_dvd_sum_alternating_forms_of_killed_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ a a' : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a' j)) → ((N : ℤ) ^ 2) ∣ ∑ b, Dw.EF (a b) (a' b) := by
  first | exact @GlobalTheory.sq_dvd_sum_EF_of_killed | exact GlobalTheory.sq_dvd_sum_EF_of_killed | (intros; apply GlobalTheory.sq_dvd_sum_EF_of_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorsionIsotropicCommutatorPairing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ThetaIsotropy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Tate

variable {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_sum (I : TateIso Dw k Q act e) (m : ℕ) (hm : 0 < m) {n : ℕ} (a : Fin n → Dw.La) :
    I.ev m (∑ j, a j) = ∏ j, I.ev m (a j) := by
  have h0 : I.ev m 0 = 1 := (I.ker m hm 0).2 ⟨0, (smul_zero _).symm⟩
  let f : Multiplicative Dw.La →* Q :=
    { toFun := fun x => I.ev m x.toAdd, map_one' := h0, map_mul' := fun x y => I.add m _ _ }
  exact map_prod f (fun j => Multiplicative.ofAdd (a j)) Finset.univ

theorem dvd_EF_of_killed (m j : ℕ) (a b : Dw.La) (ha : ∀ c ∈ l.Mb ^ j, Dw.ModN m (c • a))
    (hb : ∀ c ∈ l.Mb ^ j, Dw.ModN m (c • b)) : (m : ℤ) ∣ Dw.EF a b := by
  have cop : l.Mb ^ j ⊔ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ j = ⊤ :=
    Ideal.sup_pow_eq_top' (Ideal.pow_sup_eq_top l.coprime)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (cop.ge (Submodule.mem_top : (1 : 𝓞 E) ∈ ⊤))
  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  obtain ⟨a', ha'⟩ := ha r hr
  obtain ⟨b', hb'⟩ := hb p hp
  have e₁ : Dw.EF a b = Dw.EF a (p • b) + Dw.EF (r • a) b := by
    rw [Dw.adj, ← map_add (f := _), ← add_smul]
    have : p + H.bar r = 1 := hpq
    rw [this, one_smul]
  rw [e₁, ha', hb', map_nsmul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

end Tate

variable (Xo : Moduli Dw l) {B : Type} [CommRing B] (x0 : Sp B ⟶ Xo.X)

noncomputable def bc {K : Type} [CommRing K] (χ : B →+* K) : ptO Xo (spMap χ ≫ x0) ⟶ ptO Xo x0 :=
  Over.homMk (spMap χ) rfl

theorem unit_eq_one (hL : Laws) (N : ℕ) (hN : 0 < N) (u : Γ((ptO Xo x0).left, ⊤)ˣ) (hu : u ^ (N ^ 2) = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K),
      Units.map (bc Xo x0 χ).left.appTop.hom.toMonoidHom u = 1) : u = 1 := by
  let i₀ := (Scheme.ΓSpecIso (CommRingCat.of B)).hom
  have hi : Function.Injective i₀.hom := (ConcreteCategory.bijective_of_isIso i₀).1
  have hU : IsUnit ((N ^ 2 : ℕ) : B) := by
    have := ((baseKA l).unit (N ^ 2) (pow_pos hN 2)).map (Spec.preimage (x0 ≫ Xo.s)).hom
    rwa [map_natCast] at this
  have key := (T.universal_weilPairing_pullback_exists_unique hL E H Dw l Xo N hN).2.2 B (i₀.hom u.val) (N ^ 2) hU
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]) (fun K _ _ χ => by
      have nat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom χ)
      have e := congrArg (fun φ => φ.hom u.val) nat
      have h1 : (spMap χ).appTop.hom u.val = 1 := congrArg Units.val (h K χ)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [← e]
      exact (congrArg _ h1).trans (map_one _))
  exact Units.ext (hi (key.trans (map_one _).symm))

theorem exists_tate (hL : Laws) (N : ℕ) (hN : 0 < N) (K : Type) [Field K] [IsAlgClosed K] (χ : B →+* K) :
    ∃ I : TateIso Dw K (ptO Xo (spMap χ ≫ x0) ⟶ Xo.univ.t.G) (fun a g => g ≫ Xo.univ.t.act.act a)
        (fun n g g' c => WeilIs Xo.univ.t.G Xo.univ.t.PP.L n g g' (unitOn c)),
      ∀ (x y : ptO Xo x0 ⟶ Xo.univ.t.G) (e : Γ((ptO Xo x0).left, ⊤)ˣ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 →
        WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y e → ∀ a b, I.ev (N ^ 2) a = bc Xo x0 χ ≫ x →
        I.ev (N ^ 2) b = bc Xo x0 χ ≫ y →
        Units.map (bc Xo x0 χ).left.appTop.hom.toMonoidHom e = unitOn (I.ζ (N ^ 2) ^ Dw.EF a b) := by
  obtain ⟨-, I, -⟩ := Xo.univ.geom K (spMap χ ≫ x0) (Spec.preimage ((spMap χ ≫ x0) ≫ Xo.s)).hom
    (Spec.map_preimage _).symm
  refine ⟨I, fun x y e hx hy he a b ha hb => ?_⟩
  obtain ⟨W₁, W₂, -⟩ := T.universal_weilPairing_pullback_exists_unique hL E H Dw l Xo N hN
  have h₁ := W₁ _ _ (bc Xo x0 χ) x y e hx hy he
  have h₂ := I.isom (N ^ 2) (pow_pos hN 2) a b
  rw [ha, hb, Nat.cast_pow] at h₂
  obtain ⟨e₀, -, -, hu⟩ := W₂ _ (bc Xo x0 χ ≫ x) (bc Xo x0 χ ≫ y)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact (hu _ h₁).trans (hu _ h₂).symm

theorem unitOn_prod {K : Type} [CommRing K] {n : ℕ} (c : Fin n → Kˣ) : ∏ b, unitOn (c b) = unitOn (∏ b, c b) :=
  (map_prod (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom) c Finset.univ).symm

theorem prod_zpow_eq {U : Type} [CommGroup U] (z : U) {n : ℕ} (c : Fin n → ℤ) : ∏ b, z ^ c b = z ^ ∑ b, c b :=
  (map_prod (zpowersHom U z) (fun b => Multiplicative.ofAdd (c b)) Finset.univ).symm

theorem unitOn_one {K : Type} [CommRing K] : unitOn (1 : Kˣ) = 1 :=
  map_one (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)

theorem comp_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (h : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) : h ≫ (List.ofFn x).prod = ∏ j, h ≫ x j := by
  rw [List.prod_ofFn]
  let f : (T ⟶ G) →* (T' ⟶ G) :=
    { toFun := fun g => h ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun a b => MonObj.comp_mul _ _ _ }
  exact map_prod f x Finset.univ

end ThetaIsotropy


open ThetaIsotropy in
theorem zh_isotropic_and_half_isotropic : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → (∀ (a a' : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (e : Fin n → Γ((ptO Xo x0).left, ⊤)ˣ), InZh Xo Λ N a → InZh Xo Λ N a' → (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (a b) (a' b) (e b)) → ∏ b, e b = 1) ∧ ∀ (x y : ptO Xo x0 ⟶ Xo.univ.t.G) (j : ℕ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → KilledBy Xo (l.Mb ^ j) x → KilledBy Xo (l.Mb ^ j) y → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y 1 := by
  intro hL E _ _ _ H Dw l Xo B _ x0 n Λ N hΛ hN hle
  have hN2 : 0 < N ^ 2 := pow_pos hN 2
  obtain ⟨-, W₂, -⟩ := T.universal_weilPairing_pullback_exists_unique hL E H Dw l Xo N hN
  have tors : ∀ {K : Type} [CommRing K] (χ : B →+* K) {x : ptO Xo x0 ⟶ Xo.univ.t.G}, x ^ (N ^ 2) = 1 →
      (ThetaIsotropy.bc Xo x0 χ ≫ x) ^ (N ^ 2) = 1 := fun χ x hx => by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  refine ⟨fun a a' e ha ha' he => ?_, fun x y j hx hy kx ky => ?_⟩
  · refine ThetaIsotropy.unit_eq_one Xo x0 hL N hN _ ?_ fun K _ _ χ => ?_
    · rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun b _ => ?_
      obtain ⟨e₀, -, h₀, hu⟩ := W₂ _ (a b) (a' b) (ha.1 b) (ha'.1 b)
      rw [hu _ (he b), h₀]
    · obtain ⟨I, hI⟩ := ThetaIsotropy.exists_tate Xo x0 hL N hN K χ
      choose v hv using fun b => (I.onto _ hN2 _).1 (tors χ (ha.1 b))
      choose v' hv' using fun b => (I.onto _ hN2 _).1 (tors χ (ha'.1 b))
      have lat : ∀ {a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)} {v : Fin n → Dw.La}, InZh Xo Λ N a →
          (∀ b, I.ev (N ^ 2) (v b) = ThetaIsotropy.bc Xo x0 χ ≫ a b) →
          ∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) →
            ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) →
              ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • v j) := fun {a v} ha hv mu hmu cm hcm i => by
        refine (I.ker _ hN2 _).1 ?_
        have h₁ := congrArg (ThetaIsotropy.bc Xo x0 χ ≫ ·) (ha.2 mu hmu cm hcm i)
        simp only [MonObj.comp_one] at h₁
        rw [ThetaIsotropy.comp_prod] at h₁
        rw [ThetaIsotropy.ev_sum I _ hN2, ← h₁]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [I.lin, hv, Category.assoc]
      have hd := T.sq_dvd_sum_alternating_forms_of_killed_lattice E H Dw n Λ N hΛ hN hle v v' (lat ha hv) (lat ha' hv')
      rw [map_prod, Finset.prod_congr rfl fun b _ => hI _ _ _ (ha.1 b) (ha'.1 b) (he b) _ _ (hv b) (hv' b)]
      refine (ThetaIsotropy.unitOn_prod _).trans ?_
      rw [ThetaIsotropy.prod_zpow_eq,
        ((I.ζ_prim _ hN2).zpow_eq_one_iff_dvd _).2 (by rwa [Nat.cast_pow]), ThetaIsotropy.unitOn_one]
  · obtain ⟨e, he, h₀, -⟩ := W₂ _ x y hx hy
    suffices e = 1 by rwa [this] at he
    refine ThetaIsotropy.unit_eq_one Xo x0 hL N hN _ h₀ fun K _ _ χ => ?_
    obtain ⟨I, hI⟩ := ThetaIsotropy.exists_tate Xo x0 hL N hN K χ
    obtain ⟨v, hv⟩ := (I.onto _ hN2 _).1 (tors χ hx)
    obtain ⟨v', hv'⟩ := (I.onto _ hN2 _).1 (tors χ hy)
    have lat : ∀ {x : ptO Xo x0 ⟶ Xo.univ.t.G} {v : Dw.La}, KilledBy Xo (l.Mb ^ j) x →
        I.ev (N ^ 2) v = ThetaIsotropy.bc Xo x0 χ ≫ x → ∀ c ∈ l.Mb ^ j, Dw.ModN (N ^ 2) (c • v) := fun {x v} kx hv c hc => by
      refine (I.ker _ hN2 _).1 ?_
      rw [I.lin, hv, Category.assoc, kx c hc, MonObj.comp_one]
    have hd := ThetaIsotropy.dvd_EF_of_killed (N ^ 2) j v v' (lat kx hv) (lat ky hv')
    rw [hI _ _ _ hx hy he _ _ hv hv', ((I.ζ_prim _ hN2).zpow_eq_one_iff_dvd _).2 hd]
    exact ThetaIsotropy.unitOn_one

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorsionIsotropicCommutatorPairingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_isotropic_commutator_pairing : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → (∀ (a a' : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) (e : Fin n → Γ((ptO Xo x0).left, ⊤)ˣ), InZh Xo Λ N a → InZh Xo Λ N a' → (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (a b) (a' b) (e b)) → ∏ b, e b = 1) ∧ ∀ (x y : ptO Xo x0 ⟶ Xo.univ.t.G) (j : ℕ), x ^ (N ^ 2) = 1 → y ^ (N ^ 2) = 1 → KilledBy Xo (l.Mb ^ j) x → KilledBy Xo (l.Mb ^ j) y → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) x y 1 := by
  first | exact @GlobalTheory.zh_isotropic_and_half_isotropic | exact GlobalTheory.zh_isotropic_and_half_isotropic | (intros; apply GlobalTheory.zh_isotropic_and_half_isotropic <;> assumption)
end
end
