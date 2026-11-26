module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntOfHomAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorActionUnitaryPolynomialBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

section SlopeTestRemainingChoices

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem cwb_val_mem (l : List (lie (Jm ε))) : ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε := by
  intro X hX
  obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
  exact Y.2

theorem cwb_isKFin_Dw (h : Std ε σ) {v : H} (hv : IsKFin ε σ v) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    IsKFin ε σ (Dw σ l v) := by
  induction l with
  | nil => exact hv
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem X hY)
    exact isKFin_dRep n ε H σ h _ (ih hl') X (hl X (by simp))

theorem cwb_dRep_lin (h : Std ε σ) {w : H} (hw : Sm ε σ w) (a : ℝ) {X Y : Mx n} (hX : X ∈ lieSet ε)
    (hY : Y ∈ lieSet ε) : dRep σ (a • X + Y) w = (a : ℂ) • dRep σ X w + dRep σ Y w := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have hh : (Formalism.REAL.Jm ε).IsHermitian := GlobalTheory.SmVec.gram_herm (ε := ε) (P := 1) (by simp)
  have hd : (Formalism.REAL.Jm ε).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hG).ne_zero
  exact GlobalTheory.HolDict.LieAct.dRep_lin hh hd h.1 hw a hX hY

theorem cwb_Dw_sub (h : Std ε σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x)
    (hy : Sm ε σ y) : Dw σ l x - Dw σ l y = Dw σ l (x - y) := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have hxy : x - y ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ := Submodule.sub_mem _ hx hy
  have e := GlobalTheory.SmVec.word_add hG h.1 hl hy hxy
  have e' : Dw σ l x = GlobalTheory.SmVec.word σ l (y + (x - y)) := by rw [add_sub_cancel]; rfl
  rw [e', e]
  change GlobalTheory.SmVec.word σ l y + GlobalTheory.SmVec.word σ l (x - y) - GlobalTheory.SmVec.word σ l y = GlobalTheory.SmVec.word σ l (x - y)
  abel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ρ : Mx n → (E →L[ℂ] E)}

theorem cwb_mem_Fam (h : Std ε σ) {T₀ : H →ₗ[ℂ] E}
    (hd : ∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v →
      HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0)
    {v : H} (hv : IsKFin ε σ v) : (fun l : List (lie (Jm ε)) => T₀ (Dw σ (l.map Subtype.val) v)) ∈ Fam ε ρ := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have happ : ∀ (L₁ L₂ : List (Mx n)) (x : H), Dw σ (L₁ ++ L₂) x = Dw σ L₁ (Dw σ L₂ x) :=
    fun L₁ L₂ x => GlobalTheory.SmVec.word_append (π := σ) L₁ L₂ x
  have hcons : ∀ (Z : Mx n) (L : List (Mx n)) (x : H), Dw σ (Z :: L) x = dRep σ Z (Dw σ L x) :=
    fun _ _ _ => rfl
  have hK : ∀ l : List (lie (Jm ε)), IsKFin ε σ (Dw σ (l.map Subtype.val) v) :=
    fun l => cwb_isKFin_Dw h hv (cwb_val_mem l)
  have hS : ∀ l : List (lie (Jm ε)), Sm ε σ (Dw σ (l.map Subtype.val) v) :=
    fun l => h.2.2.1 _ (hK l)
  have hmem : ∀ X : lie (Jm ε), (X : Mx n) ∈ lieSet ε := fun X => cwb_val_mem [X] _ (by simp)
  unfold Fam
  refine ⟨?_, ?_, ?_⟩
  · intro l X
    exact hd X (hmem X) _ (hK l)
  · intro l₁ l₂ a X Y
    have hc : ((a • X + Y : lie (Jm ε)) : Mx n) = a • (X : Mx n) + (Y : Mx n) := rfl
    simp only [List.map_append, List.map_cons, happ, hcons, hc]
    have hw := hS l₂
    rw [cwb_dRep_lin h hw a (hmem X) (hmem Y)]
    have h1 : dRep σ (X : Mx n) (Dw σ (l₂.map Subtype.val) v) ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem X)
    have h2 : dRep σ (Y : Mx n) (Dw σ (l₂.map Subtype.val) v) ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem Y)
    have e1 := GlobalTheory.SmVec.word_add hG h.1 (cwb_val_mem l₁) (Submodule.smul_mem _ (a : ℂ) h1) h2
    have e2 := GlobalTheory.SmVec.word_smul hG h.1 (cwb_val_mem l₁) (a : ℂ) h1
    change T₀ (GlobalTheory.SmVec.word σ _ _) = _ • T₀ (GlobalTheory.SmVec.word σ _ _) + T₀ (GlobalTheory.SmVec.word σ _ _)
    rw [e1, e2, map_add (f := _), map_smul]
  · intro l₁ l₂ X Y Z hZ
    simp only [List.map_append, List.map_cons, happ, hcons]
    have hw := hS l₂
    have h1 : dRep σ (X : Mx n) (dRep σ (Y : Mx n) (Dw σ (l₂.map Subtype.val) v)) ∈
        GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 (GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem Y)) (hmem X)
    have h2 : dRep σ (Y : Mx n) (dRep σ (X : Mx n) (Dw σ (l₂.map Subtype.val) v)) ∈
        GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ :=
      GlobalTheory.SmVec.dRep_mem hG h.1 (GlobalTheory.SmVec.dRep_mem hG h.1 hw (hmem X)) (hmem Y)
    rw [← map_sub, cwb_Dw_sub h (cwb_val_mem l₁) h1 h2,
      dRep_bracket n ε H σ h _ hw _ (hmem X) _ (hmem Y), ← hZ]

private theorem isKFin_add {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} {v w : H} (hv : IsKFin ε σ v) (hw : IsKFin ε σ w) :
    IsKFin ε σ (v + w) := by
  obtain ⟨S, hS, hvS, hSK⟩ := hv
  obtain ⟨S', hS', hwS, hSK'⟩ := hw
  refine ⟨S ⊔ S', ?_, Submodule.add_mem_sup hvS hwS, ?_⟩
  · haveI := hS
    haveI := hS'
    infer_instance
  · unfold IsKStableOn at hSK hSK' ⊢
    intro g hg x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hSK g hg y hy) (hSK' g hg z hz)

private theorem isKFin_smul {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} (c : ℂ) {v : H} (hv : IsKFin ε σ v) :
    IsKFin ε σ (c • v) := by
  obtain ⟨S, hS, hvS, hSK⟩ := hv
  exact ⟨S, hS, S.smul_mem c hvS, hSK⟩

private theorem isKFin_zero {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Mx n → (H →L[ℂ] H)} : IsKFin ε σ (0 : H) := by
  refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
  unfold IsKStableOn
  intro g _ x hx
  rw [Submodule.mem_bot] at hx
  rw [hx, map_zero]
  exact Submodule.zero_mem _

private theorem mem_UJset_of_mem_Kset_iwasawa_decomposition {n : ℕ} {ε : Fin n → Bool} {k : Mx n} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have hu' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
  show kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, show kᴴ * k = 1 from hu', Matrix.one_mul]

private theorem dw_apply_sigma_eq_sigma_dw_conj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {g : Mx n}
    (hg : g ∈ UJset ε) (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) {w : H} (hw : Sm ε σ w) :
    Dw σ l (σ g w) = σ g (Dw σ (l.map fun X => g⁻¹ * X * g) w) := by
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem X hY)
    have hX : X ∈ lieSet ε := hl X (by simp)
    change dRep σ X (Dw σ l (σ g w)) =
      σ g (dRep σ (g⁻¹ * X * g) (Dw σ (l.map fun X => g⁻¹ * X * g) w))
    rw [ih hl']
    have hs : Dw σ (l.map fun X => g⁻¹ * X * g) w ∈ GlobalTheory.SmVec.smSub (Formalism.REAL.Jm ε) σ := by
      have hl'' : ∀ Y ∈ l.map (fun X => g⁻¹ * X * g), Y ∈ GlobalTheory.SmVec.lieG (Formalism.REAL.Jm ε) := by
        intro Y hY
        obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
        exact GlobalTheory.SmVec.conj_mem_lieG hG hg (hl' Z hZ)
      exact GlobalTheory.SmVec.word_mem hG h.1 hl'' hw
    exact GlobalTheory.SmVec.dRep_rep hG h.1 hs hg hX

end SlopeTestRemainingChoices

theorem casselmanWallach_banach : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → ∀ T₀ : H →ₗ[ℂ] E, (∀ k ∈ Kset ε, ∀ v, IsKFin ε σ v → T₀ (σ k v) = ρ k (T₀ v)) → (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0) → ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ (∀ g ∈ UJset ε, ∀ w, Sm ε σ w → T (σ g w) = ρ g (T w)) ∧ ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ ∀ w, Sm ε σ w → ‖T w‖ ≤ C * sobNorm σ S w := by
  intro hCW n ε H _ _ _ σ hσ E _ _ _ ρ hρ T₀ hK hd
  unfold GlobalTheory.Published.CasselmanWallach at hCW
  obtain ⟨hcl, p, π, dπ, hsm, hπ, hdπ, hp0⟩ := GlobalTheory.T.smooth_vectors_moderate_growth_smooth_frechet_rep n ε E ρ hρ
  haveI : IsUniformAddGroup (Fam ε ρ) := (Fam ε ρ).toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace (Fam ε ρ) := hcl.completeSpace_coe
  have hG : IsUnit (Formalism.REAL.Jm ε) := GlobalTheory.SmVec.gram_unit (ε := ε) (P := 1) isUnit_one (by simp)
  have happ : ∀ (L₁ L₂ : List (Mx n)) (x : H), Dw σ (L₁ ++ L₂) x = Dw σ L₁ (Dw σ L₂ x) :=
    fun L₁ L₂ x => GlobalTheory.SmVec.word_append (π := σ) L₁ L₂ x
  have hcons : ∀ (Z : Mx n) (L : List (Mx n)) (x : H), Dw σ (Z :: L) x = dRep σ Z (Dw σ L x) :=
    fun _ _ _ => rfl
  have hnil : ∀ x : H, Dw σ [] x = x := fun _ => rfl
  let KF : Submodule ℂ H :=
    { carrier := {v | IsKFin ε σ v}
      add_mem' := fun ha hb => isKFin_add ha hb
      zero_mem' := isKFin_zero
      smul_mem' := fun c _ hv => isKFin_smul c hv }
  let J : KF →ₗ[ℂ] Fam ε ρ :=
    { toFun := fun v => ⟨fun l => T₀ (Dw σ (l.map Subtype.val) v.1), cwb_mem_Fam hσ hd v.2⟩
      map_add' := fun v w => by
        apply Subtype.ext
        funext l
        have e := GlobalTheory.SmVec.word_add hG hσ.1 (cwb_val_mem l) (hσ.2.2.1 _ v.2) (hσ.2.2.1 _ w.2)
        show T₀ (Dw σ _ (v.1 + w.1)) = T₀ (Dw σ _ v.1) + T₀ (Dw σ _ w.1)
        rw [← map_add (f := _)]
        exact congrArg T₀ e
      map_smul' := fun c v => by
        apply Subtype.ext
        funext l
        have e := GlobalTheory.SmVec.word_smul hG hσ.1 (cwb_val_mem l) c (hσ.2.2.1 _ v.2)
        show T₀ (Dw σ _ (c • v.1)) = c • T₀ (Dw σ _ v.1)
        rw [← map_smul]
        exact congrArg T₀ e }
  obtain ⟨T₁, hT₁⟩ := LinearMap.exists_extend J
  have hT₁v : ∀ (v : H) (hv : IsKFin ε σ v), T₁ v = J ⟨v, hv⟩ := fun v hv =>
    LinearMap.congr_fun hT₁ ⟨v, hv⟩
  have hJ : ∀ (v : H) (hv : IsKFin ε σ v) (l : List (lie (Jm ε))),
      (J ⟨v, hv⟩).1 l = T₀ (Dw σ (l.map Subtype.val) v) := fun _ _ _ => rfl
  have hGK : IsGKMap ε σ π dπ T₁ := by
    refine ⟨?_, ?_⟩
    · intro k hk v hv
      have hk' : k ∈ UJset ε := mem_UJset_of_mem_Kset_iwasawa_decomposition hk
      have hkv : IsKFin ε σ (σ k v) := by
        obtain ⟨S, hS, hvS, hSK⟩ := hv
        exact ⟨S, hS, hSK k hk v hvS, hSK⟩
      rw [hT₁v _ hkv, hT₁v _ hv]
      apply Subtype.ext
      funext l
      rw [hπ k hk' (J ⟨v, hv⟩) l, hJ, hJ, dw_apply_sigma_eq_sigma_dw_conj hσ hk' _ (cwb_val_mem l) (hσ.2.2.1 _ hv)]
      have hl : (l.map Subtype.val).map (fun X => k⁻¹ * X * k) = (l.map (adInv hk')).map Subtype.val := by
        simp only [List.map_map]
        rfl
      rw [hl, hK k hk _ (cwb_isKFin_Dw hσ hv (cwb_val_mem _))]
    · intro X hX v hv
      have hXv : IsKFin ε σ (dRep σ X v) := isKFin_dRep n ε H σ hσ v hv X hX
      rw [hT₁v _ hXv, hT₁v _ hv]
      apply Subtype.ext
      funext l
      rw [show (dπ X (J ⟨v, hv⟩)).1 l = (J ⟨v, hv⟩).1 (l ++ [⟨X, hX⟩]) from hdπ ⟨X, hX⟩ _ l, hJ, hJ]
      simp only [List.map_append, List.map_cons, List.map_nil, happ, hcons, hnil]
      try rfl
  obtain ⟨T', hT'0, hSG, -⟩ := hCW n ε H σ hσ.1 hσ.2.1 (Fam ε ρ) p π dπ hsm T₁ hGK
  unfold IsSmoothGMap at hSG
  obtain ⟨hTeq, hTbd⟩ := hSG
  refine ⟨(GlobalTheory.TypeSum.SmoothFrechet.ev ρ []).comp T', ?_, ?_, ?_⟩
  · intro v hv
    show (T' v).1 [] = T₀ v
    rw [hT'0 v hv, hT₁v v hv]
    rfl
  · intro g hg w hw
    show (T' (σ g w)).1 [] = ρ g ((T' w).1 [])
    rw [hTeq g hg w hw, hπ g hg (T' w) []]
    rfl
  · obtain ⟨S, C, hS, hSC⟩ := hTbd 0
    exact ⟨S, C, hS, fun w hw => (hp0 (T' w)).trans (hSC w hw)⟩

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTargetStatement
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casselmanWallach_extension_banach_target : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → ∀ T₀ : H →ₗ[ℂ] E, (∀ k ∈ Kset ε, ∀ v, IsKFin ε σ v → T₀ (σ k v) = ρ k (T₀ v)) → (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → HasDerivAt (fun t : ℝ => ρ (NormedSpace.exp (t • X)) (T₀ v)) (T₀ (dRep σ X v)) 0) → ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ (∀ g ∈ UJset ε, ∀ w, Sm ε σ w → T (σ g w) = ρ g (T w)) ∧ ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ ∀ w, Sm ε σ w → ‖T w‖ ≤ C * sobNorm σ S w := by
  first | exact @GlobalTheory.TypeSum.casselmanWallach_banach | exact GlobalTheory.TypeSum.casselmanWallach_banach | (intros; apply GlobalTheory.TypeSum.casselmanWallach_banach <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSum
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.TopGram


set_option maxHeartbeats 4000000 in
theorem topGram : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (x y : Fin (rDim D A (F.lvl b).P (F.lvl b).ψ t) → D.what₂.LL), (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ⟪R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x), R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A (F.lvl b).P (F.lvl b).ψ t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hW b t x y
  have hHX := (hW.models.HX t).2.2
  have hjX := hW.models.jX t
  rw [hHX, hjX, hjX]
  have hiso := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R t).pres).2.2
  have key : ∀ f f' : A.fam.amb.FR t, Bridge.adInner (Bridge.ratF D.sp.X') (levEnv D.sp.X' R.βX (R.datXt t)).J
      (R.B.R t).pres.y (R.B.jR t f) (R.B.jR t f') = D.what₂.embLL ((A.fam.R t).S.csum f f') := fun f f' => hiso f f'
  have hr : ∀ z, rowForm A (F.lvl b).P (F.lvl b).ψ t z =
      GlobalTheory.Mem.LiftForms.lvlForm (A.fam.R t).S (A.fam.R t).r (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P
        (A.fam.lvl (F.lvl b).P (F.lvl b).ψ).ψ z := fun z => rfl
  refine (congrArg (fun z => (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * z) (key (rowForm A (F.lvl b).P (F.lvl b).ψ t x) (rowForm A (F.lvl b).P (F.lvl b).ψ t y))).trans ?_
  rw [hr, hr, GlobalTheory.Mem.LiftForms.csum_lvlForm]
  have hc : (Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos).ne'
  have hn : (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) = ((Nat.card ↥(A.fam.lvl (F.lvl b).P (F.lvl b).ψ).P : ℂ))⁻¹ := by
    rw [Complex.ofReal_inv]
    rfl
  rw [map_mul, map_natCast, hn, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rfl

end GlobalTheory.Mem.TopGram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerRowFormsEqLevelClassSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_inner_rowForms_eq_level_class_sum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (x y : Fin (rDim D A (F.lvl b).P (F.lvl b).ψ t) → D.what₂.LL), (((RealDat.nP F b)⁻¹ : ℝ) : ℂ) * ⟪R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x), R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A (F.lvl b).P (F.lvl b).ψ t) x y) := by
  first | exact @GlobalTheory.Mem.TopGram.topGram | exact GlobalTheory.Mem.TopGram.topGram | (intros; apply GlobalTheory.Mem.TopGram.topGram <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFacePrim
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem reFace_prim (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : PrimRows3 R F) :
    PrimRows3 (R.withErr e) (reFace F Dc Sp Zsc) := by
  obtain ⟨⟨hE, hR⟩, ⟨hW, hL⟩⟩ := h.hecke
  exact
  { heckeR := h.heckeR
    heckeL := h.heckeL
    hecke := ⟨⟨hE, ⟨hR.intw, hR.comm, hR.parts⟩⟩, ⟨hW, ⟨hL.intw, hL.comm, hL.parts⟩⟩⟩
    gUnit := h.gUnit
    gEquiv := h.gEquiv
    block := h.block
    rowTest := h.rowTest
    liftTest := h.liftTest
    liftTestB := h.liftTestB
    liftOnto := fun hW' hh => h.liftOnto hW' ⟨hh.intw, hh.comm, hh.parts⟩
    pos := h.pos
    posScal := h.posScal
    levE := h.levE
    h2P := h.h2P
    thmB := h.thmB
    sumE := h.sumE
    unif := h.unif
    mLat := h.mLat
    levW := h.levW
    thmA := h.thmA
    sumW := h.sumW
    scalConj := h.scalConj
    dimParts := h.dimParts }

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepDatumBoundedAtTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepDatumBoundedAtTypePrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.BddG

open GlobalTheory.LastSteps GlobalTheory.ColPeriod

theorem homBdd_of_good {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
    {n' c' n c m : ℕ} (hc' : c' ≤ m) (hc : c + 1 ≤ m) {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ) :
    HomBdd P m Φ := by
  have hq : (qOf P : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  refine ⟨fun x hx => (intHom_iff _).2 fun s l => ?_, fun x y hy => ?_⟩
  · have h1 := mem_homS_sclLat.1 (h.1 x hx) l s
    have hs := s.2
    have e : 0 ≤ (m : ℤ) - (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
      unfold LocE.scE
      dsimp only
      split_ifs <;> omega
    convert h1.mul (intAt_zpow e) using 1
    rw [mul_assoc, ← zpow_add₀ hq, add_sub_cancel, zpow_natCast, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  · have h1 : ((qOf P : E) ^ ((m : ℤ) - 1)) • y ∈
        homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1) := by
      refine mem_homS_sclLat.2 fun l s => ?_
      have hl := l.2
      have e : 0 ≤ (m : ℤ) - 1 + (LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1) := by
        unfold LocE.scE
        dsimp only
        split_ifs <;> omega
      convert ((intHom_iff _).1 hy s l).mul (intAt_zpow e) using 1
      rw [zpow_add₀ hq, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 := h.2.1 x _ h1
    rwa [smul_smul, zpow_sub_one₀ hq, mul_comm _ (qOf P : E)⁻¹, mul_inv_cancel_left₀ hq, zpow_natCast] at h2

theorem good_omPhi_two {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    {hal : AutY X R i} {h : AutY X R (i + 1)} (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    Good P.1 (homS (LocE.lamY P.1 (qOf P.1) (R.N i) (cOf R i) fun i => i + 1)
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1)) (omPhi Ch sel mu cst i P hal h) := by
  have h1 : R.k ≤ R.N i := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (i + 1) := Nat.le_add_right _ _
  have h3 : R.r + (i + 1 - 1) * R.t = R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    rw [Nat.add_sub_cancel, mul_add i]
    omega
  have h4 : R.N i + cOf R i ≤ R.N (i + 1) + cOf R (i + 1) := by
    unfold Ranks.N cOf
    rw [add_mul i]
    omega
  unfold lamYat at ha hb
  rw [if_pos hP] at ha hb
  refine good_om_two ?_ _ _ _ ha hb
  unfold PhiAt
  rw [if_pos hP]
  split_ifs
  · exact good_PhiGS _ _ h1 h2 h3 h4
  · exact good_PhiG _ _ h1 h2 h3 h4

theorem omPhi_bdd_type {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hi : i + 2 ≤ R.m) (hP : P.1 ∈ Pr.vGs)
    (hal : AutY X R i) (h : AutY X R (i + 1)) (ha : hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hb : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) :
    HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧
      ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) * Loc.chArg x) := by
  have hg := good_omPhi_two Ch sel mu cst i P hi hP ha hb
  refine ⟨homBdd_of_good (by unfold cOf; omega) (by unfold cOf; omega) hg, fun x hx => ?_⟩
  have := GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (chArg_int (hg.1 x hx))
  rwa [mul_neg, neg_neg] at this

end GlobalTheory.Mem.Col2.BddG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepDatumBoundedAtTypePrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepDatum_bounded_at_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu), i + 2 ≤ R.m → P.1 ∈ Pr.vGs → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) → HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧ ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) * Loc.chArg x) := by
  first | exact @GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type | exact GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type | (intros; apply GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeJwIndexEqConcreteLiftIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeJwIndexEqConcreteLiftIndex
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.JwLift

theorem mem_dual_iff {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h y x := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]

theorem jwIdx_eq_jw : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hHZ : (lZ0 D A P0 ψ0 Zs i t)ᴴ * lH D A P0 ψ0 i t * lZ0 D A P0 ψ0 Zs i t = (A.side P0 ψ0 Zs).HT i t) (hsp : Submodule.span D.what₂.LL (↑((A.side P0 ψ0 Zs).Tl i t) : Set (Fin ((A.side P0 ψ0 Zs).dZ i t) → D.what₂.LL)) = ⊤) (hT : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL))) (w : D.what₂.places.Pl), Idx.jwIdx D (tup t) ((i : ℕ) + 1) w = Formalism.DivisionValues.jw ((A.side P0 ψ0 Zs).HT i t) (D.plEq w) ((A.side P0 ψ0 Zs).Tl i t) := by
  intro D G _ _ Pl0 T A P0 ψ0 Zs tup eMt i t hP hF hHZ hsp hT w
  set HT := (A.side P0 ψ0 Zs).HT i t with hHTdef
  set Tl := (A.side P0 ψ0 Zs).Tl i t with hTldef
  let Z : Matrix (Fin (lDim D A P0 ψ0 i t)) (Fin ((A.side P0 ψ0 Zs).dZ i t)) D.what₂.LL := lZ0 D A P0 ψ0 Zs i t
  let Pr : Matrix (Fin ((A.side P0 ψ0 Zs).dZ i t)) (Fin (lDim D A P0 ψ0 i t)) D.what₂.LL := lPrj D A P0 ψ0 Zs i t
  have hP1 : Pr * Z = 1 := hP.1
  have hHZ' : Zᴴ * lH D A P0 ψ0 i t * Z = HT := hHZ
  have hT' : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Tl.map ((Matrix.mulVecLin Z).restrictScalars (𝓞 D.what₂.LL))).map
      ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := hT
  let f : (Fin ((A.side P0 ψ0 Zs).dZ i t) → D.what₂.LL) →ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1) :=
    (eMt i t).toLinearMap ∘ₗ Matrix.mulVecLin Z
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : Z *ᵥ x = Z *ᵥ y := (eMt i t).injective hxy
    have h2 : Pr *ᵥ (Z *ᵥ x) = Pr *ᵥ (Z *ᵥ y) := by rw [h1]
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP1, Matrix.one_mulVec, Matrix.one_mulVec] at h2
  have hTL : Idx.TjL D (tup t) ((i : ℕ) + 1) = Tl.map (f.restrictScalars (𝓞 D.what₂.LL)) := by
    rw [hT', ← Submodule.map_comp]
    rfl
  have hTV : Idx.TjV D (tup t) ((i : ℕ) + 1) = LinearMap.range f := by
    unfold Idx.TjV
    rw [hTL, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hsp, Submodule.map_top]
  have hin : ∀ y z, inner ℂ (D.what₂.jMt (tup t) ((i : ℕ) + 1) (f y)) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (f z)) =
      D.what₂.embLL (Formalism.DivisionValues.hform HT y z) := by
    intro y z
    have := hF.inner (Z *ᵥ y) (Z *ᵥ z)
    have e1 : Formalism.DivisionValues.hform (lH D A P0 ψ0 i t) (Z *ᵥ y) (Z *ᵥ z) = Formalism.DivisionValues.hform HT y z := by
      rw [GlobalTheory.Mem.LiftForms.hform_dot HT, ← hHZ']
      exact GlobalTheory.Mem.LiftForms.hform_mulVec _ Z Z y z
    rw [← e1]
    exact this
  have hDual : Idx.TjDual D (tup t) ((i : ℕ) + 1) =
      (Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform HT) Tl).map (f.restrictScalars (𝓞 D.what₂.LL)) := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      rw [hTV] at hx
      obtain ⟨z, rfl⟩ := hx
      refine ⟨z, (mem_dual_iff _ _ _).2 fun y hy => ?_, rfl⟩
      obtain ⟨c, hc⟩ := hx2 (f y) (by rw [hTL]; exact ⟨y, hy, rfl⟩)
      rw [hin] at hc
      exact ⟨c, (D.what₂.embLL.injective hc).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨by rw [hTV]; exact ⟨z, rfl⟩, ?_⟩
      rintro a ha
      rw [hTL] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨c, hc⟩ := (mem_dual_iff _ _ _).1 hz y hy
      refine ⟨c, ?_⟩
      change _ = D.what₂.embLL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL c)
      rw [hc]
      exact hin y z
  unfold Idx.jwIdx Formalism.DivisionValues.jw Formalism.HermitianLatticesTheory.jIdx
  rw [hTL, hDual]
  exact Formalism.BasicNotions.SkeletonIndexLemmas.lidx_map (D.plEq w) f hf _ _

end GlobalTheory.Mem.JwLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeJwIndexEqConcreteLiftIndexStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_jw_index_eq_concrete_lift_index : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (i : Fin D.R.m) (t : T) (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t)) (hF : FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P0 ψ0 i t) (lE D A P0 ψ0 i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1))) (hHZ : (lZ0 D A P0 ψ0 Zs i t)ᴴ * lH D A P0 ψ0 i t * lZ0 D A P0 ψ0 Zs i t = (A.side P0 ψ0 Zs).HT i t) (hsp : Submodule.span D.what₂.LL (↑((A.side P0 ψ0 Zs).Tl i t) : Set (Fin ((A.side P0 ψ0 Zs).dZ i t) → D.what₂.LL)) = ⊤) (hT : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL))) (w : D.what₂.places.Pl), Idx.jwIdx D (tup t) ((i : ℕ) + 1) w = Formalism.DivisionValues.jw ((A.side P0 ψ0 Zs).HT i t) (D.plEq w) ((A.side P0 ψ0 Zs).Tl i t) := by
  first | exact @GlobalTheory.Mem.JwLift.jwIdx_eq_jw | exact GlobalTheory.Mem.JwLift.jwIdx_eq_jw | (intros; apply GlobalTheory.Mem.JwLift.jwIdx_eq_jw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherFaceStatementsIndependentOfError
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def reFaceErr (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) : type_of% R.err0 :=
  fun w _ => errOf ((R.toCx3 F).data (reFace F Dc Sp Zsc).cr false) ((reFace F Dc Sp Zsc).fc (R.toCx3 F).zs).Z.F0 w


set_option maxHeartbeats 4000000 in
theorem reFace_errEq (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ErrEq (R.withErr (reFaceErr R F Dc Sp Zsc)) (reFace F Dc Sp Zsc) := fun _ _ => rfl


set_option maxHeartbeats 4000000 in
theorem reFace_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : Keep (A3 := A3) R.toRealDat F.lv2 cG) :
    Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩


set_option maxHeartbeats 4000000 in
theorem reFace_keep_back (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (h : Keep (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 cG) : Keep (A3 := A3) R.toRealDat F.lv2 cG :=
  ⟨h.std, h.signs, h.frames, h.beta, h.prX, h.grp, h.psi, h.guard, h.valKs, h.frameKs, h.levKs⟩


set_option maxHeartbeats 4000000 in
theorem reFace_scal (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hs : R.IsScal F) : R.IsScal (reFace F Dc Sp Zsc) := by
  refine ⟨hs.lam0, hs.kap, hs.off, fun i t p hp => ?_, fun i p v hv hp => ?_, hs.tup⟩
  · refine (hs.abs0 i t p hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd hp (h.1 p)
  · refine (hs.abs i p v hv hp).trans ?_
    rcases hl6 i with h | h
    · exact congrArg Real.exp h.symm
    · exact absurd (h.2 p v hv) hp


set_option maxHeartbeats 4000000 in
theorem reFace_pins (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0)
    (hl6 : ∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨
      ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v))
    (hP : Pins R F cG) : Pins (R.withErr e) (reFace F Dc Sp Zsc) cG := by
  have h := RealDat3.weak_characterisation_with_error hP.char e
  have hl6' : ∀ i, (Zsc ((R.withErr e).toCx3 F).zs).l6m i = (F.Zsc ((R.withErr e).toCx3 F).zs).l6m i ∨
      ((∀ p, (R.withErr e).Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → (R.withErr e).PartAt F i p v) := fun i => by
    rw [RealDat3.zs_withErr]
    exact (hl6 i).imp id fun h => ⟨h.1, fun p v hv => (RealDat3.partAt_withErr e i p v).2 (h.2 p v hv)⟩
  exact ⟨⟨h.base, h.inert, h.fullY, h.fullX, h.fullP, reFace_scal (R.withErr e) F Dc Sp Zsc hl6' h.scal, h.tup, h.phase, h.allPl⟩,
    reFace_keep R F cG Dc Sp Zsc e hP.keep, hP.phs, hP.trSem⟩


set_option maxHeartbeats 4000000 in
theorem further_face_statements_independent_of_error (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : UnusedChoiceStatements R F) :
    UnusedChoiceStatements (R.withErr e) (reFace F Dc Sp Zsc) :=
  ⟨⟨h.ex.ItY, h.ex.ItX, h.ex.ioY, h.ex.ioX, h.ex.Th, h.ex.ioP, h.ex.thF, h.ex.thG⟩, h.conj, h.levelW, h.integral⟩


set_option maxHeartbeats 4000000 in
def reFaceRead (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) : Read (A3 := A3) (R.withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X0 :=
  { Y with
    mj := ⟨Y.mj.eW, Y.mj.eW_range, Y.mj.eW_norm, Y.mj.eW_lat⟩
    cen0 := fun cG hK => Y.cen0 cG (reFace_keep_back R F cG Dc Sp Zsc e hK)
    cen1 := fun cG hK => Y.cen1 cG (reFace_keep_back R F cG Dc Sp Zsc e hK) }


set_option maxHeartbeats 4000000 in
def reFaceReadL (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ReadL (R.withErr e) (reFace F Dc Sp Zsc) X0 (reFaceRead R F Dc Sp Zsc e X0 Y) :=
  { Z with }

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepThetaFunctionPolynomialGrowthRealPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepThetaFunctionPolynomialGrowthRealPoints
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.LiftBound

variable {D : D7}

theorem entry_le (θ : InfF D) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) (i j : Fin V.rank) :
    ‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖ ≤ normInf θ V g := by
  unfold normInf
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ))
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j =>
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ j)

theorem norm_mM_le (θ : InfF D) (S T : HSp D) (a : GA D S) (b : GA D T) (p q : GlobalTheory.RealWeil.Ix S T) :
    ‖GlobalTheory.RealWeil.mM θ S T (a, b) p q‖ ≤ normInf θ S a * normInf θ T b := by
  have ha := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a
  have hb := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b
  rw [GlobalTheory.RealWeil.mM_apply, GlobalTheory.RealWeil.blk, blockDiagonal_apply]
  split_ifs
  · rw [kroneckerMap_apply, transpose_apply, norm_mul, mul_comm]
    refine mul_le_mul ?_ ?_ (norm_nonneg _) ha
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans (entry_le θ S a p.2 q.1.2 p.1.2)
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans (entry_le θ T b p.2 p.1.1 q.1.1)
  · rw [norm_zero]
    exact mul_nonneg ha hb

theorem sum_mM_le (θ : InfF D) (S T : HSp D) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : GA D S) (b : GA D T),
    1 + ∑ p, ∑ q, ‖GlobalTheory.RealWeil.mM θ S T (a, b) p q‖ ≤ K * ((1 + normInf θ S a) * (1 + normInf θ T b)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (Fintype.card (GlobalTheory.RealWeil.Ix S T) : ℝ) := ⟨_, rfl⟩
  have c0 : 0 ≤ c := hc ▸ Nat.cast_nonneg _
  refine ⟨1 + c * c, by positivity, fun a b => ?_⟩
  have ha := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a
  have hb := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b
  have h1 : ∑ p, ∑ q, ‖GlobalTheory.RealWeil.mM θ S T (a, b) p q‖ ≤ c * (c * (normInf θ S a * normInf θ T b)) := by
    refine (Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => norm_mM_le θ S T a b p q).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  have h2 := mul_nonneg ha hb
  have h3 := mul_nonneg c0 c0
  nlinarith [mul_nonneg h3 ha, mul_nonneg h3 hb]

theorem one_add_normInf_mul (θ : InfF D) (V : HSp D) (g h : GA D V) :
    1 + normInf θ V (g * h) ≤ (1 + normInf θ V g) * (1 + normInf θ V h) := by
  have h1 := (GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V).1 g h
  have ha := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) g
  have hb := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h
  nlinarith

theorem om_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ N : ℕ, ∀ f, IsThetaFunO ψ S T f → ∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ w, ‖om (x * a, y * b) f w‖ ≤ C * ((1 + normInf θ S a) * (1 + normInf θ T b)) ^ N := by
  intro D ψ hψ S T om hom θ hθ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨Ω, hosc, ⟨N, hN⟩, -⟩ :=
    GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.HM S T) GlobalTheory.RealWeil.HM_herm GlobalTheory.RealWeil.HM_det
      (GlobalTheory.RealWeil.BB ψ S T) (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.isHeis_rhoB h hψ) (GA D S × GA D T)
      (GlobalTheory.RealWeil.mM θ S T) (GlobalTheory.RealWeil.mM_unitary hθ)
  obtain ⟨K, hK0, hK⟩ := sum_mM_le θ S T
  obtain ⟨-, -, -, -, -, s6, s7, -⟩ := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ S
  obtain ⟨-, -, -, -, -, t6, t7, -⟩ := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ T
  refine ⟨N, fun f hf x y => ?_⟩
  obtain ⟨k, hk, a₀, ha₀, rfl⟩ := s7 x
  obtain ⟨k', hk', b₀, hb₀, rfl⟩ := t7 y
  have hf' := hom.om_pres (k, k') f hf
  have hF : IsThetaFunO ψ S T (GlobalTheory.RealWeil.toB hψ _ hf').1 := by
    rw [GlobalTheory.RealWeil.coe_toB]; exact hf'
  obtain ⟨C, hC⟩ := hN _ (GlobalTheory.RealWeil.sm_of_theta h hψ _ hF)
  refine ⟨|C| * (K * ((1 + normInf θ S a₀) * (1 + normInf θ T b₀))) ^ N, fun a ha b hb w => ?_⟩
  have haa := mul_mem ha₀ ha
  have hbb := mul_mem hb₀ hb
  obtain ⟨c, hc, hcF⟩ := GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points D θ σ h ψ hψ S T om hom Ω hosc _ haa _ hbb
  have e : ((k * a₀ * a, k' * b₀ * b) : GA D S × GA D T) = (a₀ * a, b₀ * b) * (k, k') := by
    rw [Prod.mk_mul_mk, s6 _ haa k hk, t6 _ hbb k' hk', mul_assoc, mul_assoc]
  have e2 := hcF _ hF
  rw [GlobalTheory.RealWeil.coe_toB] at e2
  rw [e, map_mul, Module.End.mul_apply, e2, Pi.smul_apply, norm_smul, hc, one_mul]
  refine (GlobalTheory.RealWeil.norm_ev_le w _).trans ((hC _).trans ?_)
  have n1 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a₀
  have n2 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b₀
  have n3 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) a
  have n4 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) b
  have n5 := GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) (b₀ * b)
  rw [mul_assoc, ← mul_pow]
  refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by positivity) ((hK _ _).trans ?_) N) (by positivity)
    (abs_nonneg C)
  rw [mul_assoc K]
  refine mul_le_mul_of_nonneg_left ?_ hK0
  refine (mul_le_mul (one_add_normInf_mul θ S a₀ a) (one_add_normInf_mul θ T b₀ b) (by positivity)
    (by positivity)).trans_eq ?_
  ring

end GlobalTheory.Mem.LiftBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepThetaFunctionPolynomialGrowthRealPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_thetaFunction_polynomialGrowth_realPoints : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ N : ℕ, ∀ f, IsThetaFunO ψ S T f → ∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ w, ‖om (x * a, y * b) f w‖ ≤ C * ((1 + normInf θ S a) * (1 + normInf θ T b)) ^ N := by
  first | exact @GlobalTheory.Mem.LiftBound.om_growth | exact GlobalTheory.Mem.LiftBound.om_growth | (intros; apply GlobalTheory.Mem.LiftBound.om_growth <;> assumption)
end
end
