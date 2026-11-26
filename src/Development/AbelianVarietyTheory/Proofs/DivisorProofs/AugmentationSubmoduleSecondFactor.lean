module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicHighestWeight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLinearBarDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLinearBarDual
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeilTransfer

theorem transfer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∃ t : E →ₐ[F] Fv F v, ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (ν₀ : (Fv F v)ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
      Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
        ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0) ∧
      (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
      ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨t⟩ : Nonempty (E →ₐ[F] Fv F v) := GlobalTheory.T.split_place_embedding_exists F E σ hcm v hv.2
  let B' : Base F E := { B with v₁ := v, τ₁ := t }
  have hT' : IsTriple B' G X om om' :=
    { base := { hT.base with }
      geo := { hT.geo with hV := { hT.geo.hV with }, hV' := { hT.geo.hV' with }, hW := { hT.geo.hW with } }
      chars := { hT.chars with good := hv }
      weil := hT.weil
      weil' := hT.weil' }
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_bar_good_place hP F E σ B a a' G X om om' hT v hv t
  have hι' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι := hι

  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit (G.V'.J.map t).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w)
      (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have herm : ∀ i j, σ (G.V'.J j i) = algebraMap F E 1 * G.V'.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV'.herm i j
  let K := GlobalTheory.SplitUnitLift.liftU hcm t G.V'.J 1 herm hdet
  have hK : ∀ g, K g ∈ UAt σ G.V' (evFin F B'.v₁) ∧ (mat (K g)).map (piW B'.τ₁) = g.val ∧
      (mat (K g)).map (piW (B'.τ₁.comp σ)) = (G.V'.J.map B'.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map B'.τ₁ :=
    fun g => ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V' 1 herm hdet g, GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V'.J 1 herm hdet g,
      GlobalTheory.SplitUnitLift.liftU_piW_comp hcm t G.V'.J 1 herm hdet g⟩

  choose S hS using fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v (K g) (hK g).1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  have eqR : ∀ φ₁ φ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ, tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R → φ₁ = φ₂ := by
    intro φ₁ φ₂ h
    have hRc := (hR 0 (Submodule.zero_mem _)).1
    funext y
    have hp : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
    have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (y i))
    have e2 : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by simpa using hRc 0 _ hp
    simp only [tens, GlobalTheory.LatVac.evFin_liftV, e2] at e
    exact mul_right_cancel₀ hR0 e
  have hSR : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), om' (K g, 1) (tens (evFin F v) φ R) = tens (evFin F v) (S g φ) R :=
    fun g φ hφ => (hS g φ hφ).2 R (hR φ hφ)
  have h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ := fun g φ hφ => (hS g φ hφ).1
  have tensLin : ∀ (c : ℂ) (φ φ' : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • φ + φ') R = c • tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro c φ φ'; funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hlin : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro g φ hφ φ' hφ' c
    have hm : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    apply eqR
    rw [← hSR g _ hm, tensLin, map_add (f := _), map_smul, hSR g φ hφ, hSR g φ' hφ', tensLin]
  have h2 : ∀ g g', ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    apply eqR
    have e1 : ((K (g * g'), (1 : UA σ G.W.J))) = (K g, 1) * (K g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← hSR _ φ hφ, e1, map_mul, Module.End.mul_apply, hSR g' φ hφ, hSR g _ (h1 g' φ hφ)]
  have h3 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ hφ
    apply eqR
    have e1 : ((K 1, (1 : UA σ G.W.J))) = 1 := by rw [map_one]; rfl
    rw [← hSR _ φ hφ, e1, map_one, Module.End.one_apply]
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have restS : ∀ g φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r :=
    fun g φ r hφ hr => ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v)
            (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hT v (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  obtain ⟨ν, α, hν, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator B' G X om om' hT' K hK S h1 hlin h2 h3 h4 h5
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char B' G X om om' hT' K hK S h1 h4
  obtain ⟨hTι, hMι, -, -⟩ := hA ι hι'

  have hvac := hT.geo.hM'.vac v
  have hιv : ι (G.M'.vac v) ≠ 0 := fun h0 =>
    hvac.2.1 (hι.bij.injOn hvac.1 (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  set φ₀ := GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT Y₀) (G.M'.vac v) with hφ₀def
  have hφ₀ : φ₀ ∈ SB (Fin a' × Fin (a + a') → Fv F v) := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ _ hvac.1
  have hφ₀0 : ι φ₀ 0 ≠ 0 := by
    have e := congrFun (hTι Y₀ _ hvac.1) 0
    simp only [zero_add] at e
    rw [e]; exact hY₀

  obtain ⟨-, -, hcont⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' G.q (a' - G.q)
    (a + a' - (G.p + G.q)) (G.p + G.q) (GlobalTheory.ThK.Inhab.pairV' hT) v
  obtain ⟨U, hU, hUact⟩ := hcont φ₀ hφ₀
  have hKt : Tendsto K (𝓝 1) (𝓝 1) := GlobalTheory.T.split_unitary_lift_tendsto_one hcm t G.V'.J 1 herm hdet
  have hP1 : {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U} ∈ 𝓝 1 :=
    (hKt.prodMk_nhds tendsto_const_nhds) hU
  have hone : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := fun u _ => by simp [mat]
  have hsm : ∀ g ∈ {g : GL (Fin a') (Fv F v) | (K g, (1 : UA σ G.W.J)) ∈ U},
      (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) = 1 := by
    intro g hg
    have hact := hUact (K g, 1) hg (hK g).1 hone
    have hfix : S g φ₀ = φ₀ := eqR _ _ (by rw [← hSR g φ₀ hφ₀]; exact hact R (hR φ₀ hφ₀))
    have e := congrFun (hC ι hι' g φ₀ hφ₀) 0
    rw [hfix] at e
    simp only [GlobalTheory.SplitFlip.omB, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one, Matrix.mul_zero,
      Matrix.zero_mul] at e
    have e2 : ι φ₀ 0 * 1 = ι φ₀ 0 * ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2)) := by
      rw [mul_one]; nth_rw 1 [e]; ring
    exact (mul_left_cancel₀ hφ₀0 e2).symm
  have hsmooth : GlobalTheory.SmGL.IsSmoothChar ν := GlobalTheory.T.smooth_character_of_trivial_near_one (by have := (GlobalTheory.ThK.Inhab.two_le_rank hT).1; omega) ν _ _ hP1 hsm

  have hSo : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
      ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0 := by
    intro φ hφ
    constructor
    · rintro ⟨-, ι₂, hι₂, hvan⟩ Y hY
      have hι₂' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι₂ := hι₂
      obtain ⟨hT₂, hM₂, -, -⟩ := hA ι₂ hι₂'
      obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) hψc hψ1 ι₂ ι
        hι₂.bij (fun x _ y _ c => by rw [map_add (f := _), map_smul])
        (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT C))
        (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wM l))
        (fun C x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hT₂ C x hx, hTι C x hx⟩)
        (fun l x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hM₂ l x hx, hMι l x hx⟩)
      rw [hc φ hφ, Pi.smul_apply, hvan Y hY, smul_zero]
    · intro h
      exact ⟨hφ, ι, hι, h⟩
  refine ⟨t, ι, ν, hsmooth, hν, hι.bij, hSo, fun g₀ => ⟨K g₀, (hK g₀).1, fun φ hφ =>
    ⟨S g₀ φ, h1 g₀ φ hφ, (hS g₀ φ hφ).2, ?_⟩⟩, GlobalTheory.T.linear_bar_functional_good_place hP F E σ B a a' G X om om' hT v hv t ι hι⟩
  rw [hC ι hι' g₀ φ hφ]
  funext Y
  simp only [GlobalTheory.SplitFlip.omB, GlobalTheory.FullRankCoinv.lact, map_one, Units.val_one, mul_one, GlobalTheory.SplitFlip.apow_one,
    Matrix.mul_one, Fintype.card_fin]

end GlobalTheory.WeilTransfer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLinearBarDualStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_linear_bar_dual : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∃ t : E →ₐ[F] Fv F v, ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (ν₀ : (Fv F v)ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
      Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
        ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0) ∧
      (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
      ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  first | exact @GlobalTheory.WeilTransfer.transfer | exact GlobalTheory.WeilTransfer.transfer | (intros; apply GlobalTheory.WeilTransfer.transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleSecondFactor
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrCoinvSmall

theorem fullRk_irred : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ), GlobalTheory.FullRankCoinv.augRk n d ν ≤ N →
      N ≤ GlobalTheory.FullRankCoinv.fullRk k n d → (∀ h : GL (Fin d) k, ∀ Ψ ∈ N, (fun Y => Ψ (Y * h.1)) ∈ N) →
      N = GlobalTheory.FullRankCoinv.augRk n d ν ∨ N = GlobalTheory.FullRankCoinv.fullRk k n d := by
  intro hP k _ _ _ _ n d ν hnd hs hu N hA hNF hN
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := GlobalTheory.T.full_rank_coinvariant_induced_iso k n d ν hnd hs
  rcases GlobalTheory.T.induced_full_rank_irreducible hP k n d ν hnd hs hu (N.map Z) (by rintro _ ⟨Ψ, hΨ, rfl⟩; exact hZ1 Ψ (hNF hΨ)) (by
    rintro _ ⟨Ψ, hΨ, rfl⟩ h₀; exact ⟨_, hN h₀ Ψ hΨ, hZ4 Ψ (hNF hΨ) h₀⟩) with hE | hE
  · left
    refine le_antisymm (fun Ψ hΨ => hZ3 Ψ (hNF hΨ) ?_) hA
    have : Z Ψ ∈ N.map Z := ⟨Ψ, hΨ, rfl⟩
    rw [hE] at this
    exact (Submodule.mem_bot ℂ).1 this
  · right
    refine le_antisymm hNF (fun Ψ hΨ => ?_)
    have : Z Ψ ∈ N.map Z := hE ▸ hZ1 Ψ hΨ
    obtain ⟨Ψ', hΨ', he⟩ := this
    have h1 : Ψ - Ψ' ∈ GlobalTheory.FullRankCoinv.augRk n d ν :=
      hZ3 _ (Submodule.sub_mem _ hΨ (hNF hΨ')) (by simp [map_sub, he])
    have := N.add_mem hΨ' (hA h1)
    rwa [add_sub_cancel] at this

theorem irr_small : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), augAt om' v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om' v ∨ N = SB _ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν N hAN hNS hN
  obtain ⟨t, ι, ν₀, hs, hu, hbij, hso, hg, hh⟩ := GlobalTheory.T.exists_unramified_linear_bar_dual hP F E σ B a a' G X om om' hT v hv
  have hR := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' hT v hv hν t
  have haugSB : augAt om' v ≤ SB _ := Submodule.span_le.2 (by
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ)

  have hgen : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤
      (augAt om' v).map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g₀, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ.1
    obtain ⟨g, hgU, hg'⟩ := hg g₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hg' φ hφ
    refine ⟨⟨φ₁ - φ, Submodule.subset_span ⟨g, hgU, φ, hφ, φ₁, hφ₁, hA, rfl⟩, by simp [map_sub, he]⟩, ?_, ?_⟩
    · rw [← he]
      exact Submodule.sub_mem _ (hbij.mapsTo hφ₁) hΨ.1
    · intro Y hY
      rw [← he]
      show ι φ₁ Y - ι φ Y = 0
      rw [he, hΨ.2 Y hY]
      simp only [GlobalTheory.FullRankCoinv.lact, sub_zero]
      rw [hΨ.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by
        rw [Matrix.det_transpose]; exact (Matrix.GeneralLinearGroup.det g₀).isUnit)]), mul_zero]
  set N' := N.map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') with hN'
  have hA' : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤ N' :=
    hgen.trans (inf_le_inf_right _ (Submodule.map_mono hAN))
  have hst : ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∀ Ψ ∈ N', (fun Y => Ψ (Y * h₀.1)) ∈ N' := by
    rintro h₀ _ ⟨⟨φ, hφN, rfl⟩, hΨ⟩
    obtain ⟨h, hhU, c, hc, hh'⟩ := hh h₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hh' φ (hNS hφN)
    have h1 : (fun Y => ι φ (Y * h₀.1)) = c⁻¹ • ι φ₁ := by
      rw [he]; funext Y; simp [hc]
    refine ⟨⟨c⁻¹ • φ₁, N.smul_mem _ (hN h hhU φ hφN φ₁ hφ₁ hA), by rw [map_smul, h1]⟩, ?_, ?_⟩
    · rw [h1]; exact Submodule.smul_mem _ _ (hbij.mapsTo hφ₁)
    · intro Y hY
      exact hΨ.2 _ (by rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.GeneralLinearGroup.det h₀).isUnit])
  have hinj : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι φ = ι φ' → φ = φ' := fun φ hφ φ' hφ' e => hbij.injOn hφ hφ' e
  have hloc : ∀ φ₀ ∈ G.M'.SoLoc B.ψ t, ι φ₀ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') :=
    fun φ₀ h0 => ⟨hbij.mapsTo h0.1, (hso φ₀ h0.1).1 h0⟩
  rcases fullRk_irred hP (Fv F v) a' (a + a') ν₀ (by omega) hs hu N' hA' inf_le_right hst with hE | hE
  · left
    refine le_antisymm (fun φ hφN => ?_) hAN
    obtain ⟨φ₀, h0, hd⟩ := hR φ (hNS hφN)
    have h0N : φ₀ ∈ N := by
      have := N.sub_mem hφN (hAN hd); rwa [sub_sub_cancel] at this
    have h1 : ι φ₀ ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ := hE ▸ ⟨⟨φ₀, h0N, rfl⟩, hloc φ₀ h0⟩
    obtain ⟨⟨w, hw, hwe⟩, -⟩ := hgen h1
    have : w = φ₀ := hinj w (haugSB hw) φ₀ h0.1 hwe
    subst this
    have := (augAt om' v).add_mem hw hd
    rwa [add_sub_cancel] at this
  · right
    refine le_antisymm hNS (fun φ hφ => ?_)
    obtain ⟨φ₀, h0, hd⟩ := hR φ hφ
    have h1 : ι φ₀ ∈ N' := hE ▸ hloc φ₀ h0
    obtain ⟨⟨φ', hφ'N, he⟩, -⟩ := h1
    have : φ' = φ₀ := hinj φ' (hNS hφ'N) φ₀ h0.1 he
    subst this
    have := N.add_mem hφ'N (hAN hd)
    rwa [add_sub_cancel] at this

end GlobalTheory.IrrCoinvSmall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleSecondFactorStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_submodule_second_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), augAt om' v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om' v ∨ N = SB _ := by
  first | exact @GlobalTheory.IrrCoinvSmall.irr_small | exact GlobalTheory.IrrCoinvSmall.irr_small | (intros; apply GlobalTheory.IrrCoinvSmall.irr_small <;> assumption)
end
