module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasselmanWallachAdmissible
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.Imports
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C3C
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.TendstoPiZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ZeroOnDense
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.PageTheorem

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.C7
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

theorem c7 : C7 := by
  classical
  intro hMax hC4 n ε H _ _ _ σ hU hI hD E hKD hM N
  obtain ⟨m, K, I0, hK0, hmax⟩ := hMax n ε (kfin ε σ) E hM N
  obtain ⟨S, C', hS, hC', hbd⟩ := hC4 n ε H σ hU hI hD E hKD m
  refine ⟨S, K * C', I0.image Subtype.val, hS, mul_nonneg hK0 hC', ?_, ?_⟩
  · intro e he
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
    exact x.2
  · intro F hcont hder hgrow B hB hI0 v hv
    let F' : kfin ε σ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ → ℂ := F ∘ₗ (kfin ε σ).subtype
    have key := hmax F' (fun w => hcont w w.2)
      (fun X hX w g hg => by
        have h1 := hder X hX.1 w w.2 g hg
        show HasDerivAt (fun t : ℝ => F (w : H) (g * NormedSpace.exp (t • X)))
          (F ((ReciprocityTheory.ChartRestriction.DS.actM E X w : kfin ε σ) : H) g) 0
        rw [hKD X hX.1 w]
        exact h1)
      (fun w => hgrow w w.2) B hB
      (fun e he g hg => hI0 e.1 (Finset.mem_image_of_mem _ he) g hg) ⟨v, hv⟩
    calc ‖F v 1‖ = ‖F' ⟨v, hv⟩ 1‖ := rfl
      _ ≤ K * B * ‖((1 + ReciprocityTheory.ChartRestriction.DS.casimirK ε E) ^ m) ⟨v, hv⟩‖ := key
      _ ≤ K * B * (C' * sobNorm σ S v) :=
        mul_le_mul_of_nonneg_left (hbd ⟨v, hv⟩) (mul_nonneg hK0 hB)
      _ = K * C' * B * sobNorm σ S v := by ring

end PositivityTheory.CW
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SeminormApproximation
open scoped InnerProductSpace
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary adjSign)

namespace PositivityTheory.CW.EigenOrthogonalForm

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem cas_symm (hu : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hu a b, hu b a]
  simp [adjSign, hab]

theorem inner_eq_zero_of_eig (hu : IsInfUnitary ε E) {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : ⟪v, y⟫_ℂ = 0 := by
  have h := cas_symm hu v y
  rw [hv, hy, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have h' : ((μ : ℂ) - μ') * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h0) hne
  · exact h0

theorem B_eq_zero (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y))
    {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : B v y = 0 := by
  have h := hB v y
  rw [hv, hy] at h
  simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Complex.conj_ofReal,
    RingHom.id_apply] at h
  have h2 : ((μ : ℂ) - μ') * B v y = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) hne
  · exact h3

end PositivityTheory.CW.EigenOrthogonalForm

namespace PositivityTheory.CW

open EigenOrthogonalForm in
theorem e2c : CasimirPairingBound := by
  intro n ε V _ _ E _ _ hM Q hQ η
  let S : Submodule ℂ V :=
    { carrier := {a | ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪a, y⟫_ℂ‖ ≤ C * Q y}
      add_mem' := by
        rintro a b ⟨C₁, h₁, ha⟩ ⟨C₂, h₂, hb⟩
        refine ⟨C₁ + C₂, add_nonneg h₁ h₂, fun y => ?_⟩
        rw [inner_add_left, add_mul]
        exact (norm_add_le _ _).trans (add_le_add (ha y) (hb y))
      zero_mem' := ⟨0, le_rfl, fun y => by simp⟩
      smul_mem' := by
        rintro c a ⟨C, h, ha⟩
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) h, fun y => ?_⟩
        rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
        exact mul_le_mul_of_nonneg_left (ha y) (norm_nonneg _) }
  suffices hS : S = ⊤ by
    have hη : η ∈ S := hS ▸ Submodule.mem_top
    exact hη
  rw [eq_top_iff, ← hM.span, Submodule.span_le]
  rintro w ⟨μ, hw⟩
  let W : Submodule ℂ V := Module.End.eigenspace (casimirK ε E) (μ : ℂ)
  have hWmem : ∀ v, v ∈ W ↔ casimirK ε E v = (μ : ℂ) • v := fun v => Module.End.mem_eigenspace_iff
  haveI : FiniteDimensional ℂ W := by
    haveI := hM.fin μ
    have hle : W ≤ Submodule.span ℂ {v | ∃ μ' ≤ μ, Eig ε E μ' v} :=
      fun v hv => Submodule.subset_span ⟨μ, le_rfl, (hWmem v).1 hv⟩
    exact Submodule.finiteDimensional_of_le hle
  let P : (V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) → Prop := fun B =>
    (∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y)) ∧ ∀ v y, ‖B v y‖ ≤ Q v * Q y
  let G : Set (Module.Dual ℂ W) := {g | ∃ B, P B ∧ ∃ v ∈ W, g = (B v).comp W.subtype}
  have hspan : Submodule.span ℂ G = ⊤ := by
    have hco : (Submodule.span ℂ G).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      by_contra hne
      have hy0 : (y : V) ≠ 0 := fun h => hne (Subtype.ext h)
      obtain ⟨B, hB1, hB2, hB3⟩ := hQ y hy0
      have hg : (B y).comp W.subtype ∈ Submodule.span ℂ G :=
        Submodule.subset_span ⟨B, ⟨hB1, hB2⟩, y, y.2, rfl⟩
      exact hB3 ((Submodule.mem_dualCoannihilator _).1 hy _ hg)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ G), hco,
      Submodule.dualAnnihilator_bot]
  have hl : (innerₛₗ ℂ w).comp W.subtype ∈ Submodule.span ℂ G := hspan ▸ Submodule.mem_top
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 hl
  choose B hB v hv hgv using fun i => (g i).2
  have hid : innerₛₗ ℂ w = ∑ i, f i • B i (v i) := by
    refine LinearMap.ext_on hM.span ?_
    rintro y ⟨lam, hy⟩
    by_cases hμ : lam = μ
    · subst hμ
      have hyW : y ∈ W := (hWmem y).2 hy
      have := LinearMap.congr_fun hfg ⟨y, hyW⟩
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hgv, LinearMap.comp_apply,
        Submodule.subtype_apply] at this
      rw [← this, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
    · have h0 : ⟪w, y⟫_ℂ = 0 := inner_eq_zero_of_eig hM.uni (Ne.symm hμ) hw hy
      have h1 : ∀ i, B i (v i) y = 0 := fun i =>
        B_eq_zero (B i) (hB i).1 (Ne.symm hμ) ((hWmem _).1 (hv i)) hy
      rw [LinearMap.sum_apply, innerₛₗ_apply_apply, h0]
      simp [h1]
  show ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪w, y⟫_ℂ‖ ≤ C * Q y
  refine ⟨∑ i, ‖f i‖ * Q (v i),
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg Q _), fun y => ?_⟩
  have hwy : ⟪w, y⟫_ℂ = ∑ i, f i * B i (v i) y := by
    have h := LinearMap.congr_fun hid y
    rw [innerₛₗ_apply_apply, LinearMap.sum_apply] at h
    rw [h]
    simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hwy, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hB i).2 _ _) (norm_nonneg _)

end PositivityTheory.CW
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenspacesOrthogonal
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)
open scoped InnerProductSpace

namespace PositivityTheory.CW

namespace HilbertSchmidtSqEq₂

theorem hs2_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : hs2 g = hs g := rfl

theorem smul_seminorm_cont {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {q : Seminorm ℂ E}
    (hq : Continuous q) (c : NNReal) : Continuous (c • q) := by
  rw [Seminorm.coe_smul]
  exact hq.const_smul c

end HilbertSchmidtSqEq₂

open HilbertSchmidtSqEq₂ in
theorem e3c : SmoothMapSeminormBound := by
  classical
  intro hM e3a e3b n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD A hA hMod T hG hd Q N hQc hQg hη
  obtain ⟨m, K, I₀, hK, hmax⟩ := hM n ε (kfin ε σ) A hMod N
  have hC : ∀ e : kfin ε σ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, Sm ε σ y → ‖⟪(e : H), y⟫_ℂ‖ ≤ C * Q (T y) :=
    fun e => hη e e.2
  choose Ce hCe0 hCe using hC
  set Cs : ℝ := ∑ e ∈ I₀, Ce e with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun e _ => hCe0 e
  have h3a := e3a n ε (kfin ε σ) A hMod.gl hMod.uni hMod m
  obtain ⟨D, hDm⟩ := e3b n ε H σ hU hI E p π dπ hπ A hA T hd m
  have key : ∀ y : kfin ε σ, ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) := by
    intro y
    obtain ⟨v, hv⟩ := h3a.1 y
    set w : H := ((((1 + casimirK ε A) ^ m) y : kfin ε σ) : H) with hwdef
    have hw : Sm ε σ w := hD.1 _ (((1 + casimirK ε A) ^ m) y).2
    let F : kfin ε σ →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) :=
      { toFun := fun η g => ⟪w, σ g (η : H)⟫_ℂ
        map_add' := fun a b => by funext g; simp [inner_add_right]
        map_smul' := fun c a => by funext g; simp [inner_smul_right] }
    have hF : ∀ (η : kfin ε σ) g, F η g = ⟪w, σ g (η : H)⟫_ℂ := fun _ _ => rfl
    have h1 : ∀ η : kfin ε σ, ContinuousOn (F η) (ReciprocityTheory.ChartRestriction.DS.UJset ε) := fun η => by
      have := (continuousOn_const (c := w) (s := UJset ε)).inner (𝕜 := ℂ) (hU.2.2 (η : H))
      exact this
    have h2 : ∀ X, ReciprocityTheory.ChartRestriction.DS.inP ε X → ∀ η : kfin ε σ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε,
        HasDerivAt (fun t : ℝ => F η (g * NormedSpace.exp (t • X))) (F (actM A X η) g) 0 := by
      intro X hX η g hg
      have hXl : X ∈ lieSet ε := hX.1
      have hg' : g ∈ UJset ε := hg
      have hη' : Sm ε σ (η : H) := hD.1 _ η.2
      have ho : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (η : H)) (dRep σ X η) 0 := by
        have := hasDerivAt_orbit hU hη' hXl 0
        rwa [zero_smul, NormedSpace.exp_zero, sigma_one hU] at this
      have h4 : HasDerivAt (fun t : ℝ => σ g (σ (NormedSpace.exp (t • X)) (η : H))) (σ g (dRep σ X η)) 0 :=
        ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 ho
      have h5 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h4
      simp only [ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at h5
      rw [hF, hA X hXl η]
      refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, hF, innerSL_apply_apply]
      rw [sigma_mul hU hg' (exp_mem_UJ hXl t)]
    have h3 : ∀ η : kfin ε σ, ∃ C : ℝ, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F η g‖ ≤ C * (1 + hs2 g) ^ N := by
      intro η
      refine ⟨‖w‖ * ‖(η : H)‖, fun g hg => ?_⟩
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq]
      have e1 : ‖⟪w, σ g (η : H)⟫_ℂ‖ ≤ ‖w‖ * ‖(η : H)‖ := by
        have := norm_inner_le_norm (𝕜 := ℂ) w (σ g (η : H))
        rwa [hU.2.1 g hg' (η : H)] at this
      have e2 : (1 : ℝ) ≤ (1 + hs g) ^ N := one_le_pow₀ (by linarith [hs_nonneg g])
      calc _ ≤ ‖w‖ * ‖(η : H)‖ := e1
        _ = ‖w‖ * ‖(η : H)‖ * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)
    have h5b : ∀ e ∈ I₀, ∀ g ∈ ReciprocityTheory.ChartRestriction.DS.UJset ε, ‖F e g‖ ≤ (Cs * Q (T w)) * (1 + hs2 g) ^ N := by
      intro e he g hg
      have hg' : g ∈ UJset ε := hg
      rw [hF, hs2_eq, inner_sigma hU hg' w (e : H), norm_inner_symm]
      have hgi : g⁻¹ ∈ UJset ε := inv_mem_UJ hg'
      have e1 := hCe e (σ g⁻¹ w) (Sm.translate hU hw hgi)
      rw [hG.1 g⁻¹ hgi w hw] at e1
      have e2 := hQg g⁻¹ hgi (T w)
      rw [hs_inv hg'] at e2
      have e3 : Ce e ≤ Cs := Finset.single_le_sum (f := Ce) (fun x _ => hCe0 x) he
      have hQ0 : 0 ≤ Q (T w) := apply_nonneg _ _
      have hW0 : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) _
      calc _ ≤ Ce e * Q (π g⁻¹ (T w)) := e1
        _ ≤ Ce e * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_left e2 (hCe0 e)
        _ ≤ Cs * ((1 + hs g) ^ N * Q (T w)) := mul_le_mul_of_nonneg_right e3 (mul_nonneg hW0 hQ0)
        _ = _ := by ring
    have hmv := hmax F h1 h2 h3 (Cs * Q (T w)) (mul_nonneg hCs0 (apply_nonneg _ _)) h5b v
    rw [hv, hF, sigma_one hU] at hmv
    have hin : ⟪w, (v : H)⟫_ℂ = ⟪(y : H), (y : H)⟫_ℂ := by
      rw [hwdef, ← Submodule.coe_inner, ← Submodule.coe_inner, h3a.2 y v, hv]
    have hn : ‖⟪(y : H), (y : H)⟫_ℂ‖ = ‖(y : H)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow]; simp
    rw [hin, hn] at hmv
    have hTw : T w = D (T y) := hDm y
    rw [hTw] at hmv
    have hy0 : 0 ≤ ‖(y : H)‖ := norm_nonneg _
    have hR0 : 0 ≤ K * Cs * Q (D (T y)) := mul_nonneg (mul_nonneg hK hCs0) (apply_nonneg _ _)
    rcases hy0.eq_or_lt with h0 | h0
    · rw [← h0]; exact hR0
    · have : ‖(y : H)‖ * ‖(y : H)‖ ≤ K * Cs * Q (D (T y)) * ‖(y : H)‖ := by
        have e : K * (Cs * Q (D (T y))) * ‖(y : H)‖ = K * Cs * Q (D (T y)) * ‖(y : H)‖ := by ring
        rw [← e, ← sq]
        exact hmv
      exact le_of_mul_le_mul_right this h0
  refine ⟨(K * Cs).toNNReal • Q.comp (D : E →ₗ[ℂ] E), smul_seminorm_cont ?_ _, fun v hv => ?_⟩
  · rw [Seminorm.coe_comp]
    exact hQc.comp D.continuous
  · rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (mul_nonneg hK hCs0),
      Seminorm.comp_apply]
    exact key ⟨v, hv⟩

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.E3D
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace PositivityTheory.CW

theorem e3d : SobolevNormDomination := by
  intro he2 n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT hd q hq hq1 S hS
  let Dop : List (Mx n) → (E →L[ℂ] E) := fun l =>
    l.foldr (fun X f => (dπ X).comp f) (ContinuousLinearMap.id ℂ E)
  have key : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v →
      IsKFin ε σ (Dw σ l v) ∧ T (Dw σ l v) = Dop l (T v) := by
    intro l
    induction l with
    | nil => intro _ v hv; exact ⟨hv, rfl⟩
    | cons X l ih =>
      intro hl v hv
      obtain ⟨h1, h2⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) v hv
      refine ⟨hD.2.1 _ h1 X (hl X List.mem_cons_self), ?_⟩
      show T (dRep σ X (Dw σ l v)) = dπ X (Dop l (T v))
      rw [hd X (hl X List.mem_cons_self) _ h1, h2]
  have hcont : ∀ l, Continuous (q.comp (Dop l : E →ₗ[ℂ] E)) := fun l => by
    rw [Seminorm.coe_comp, ContinuousLinearMap.coe_coe]
    exact hq.comp (Dop l).continuous
  have hw : ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ w, Sm ε σ w →
      ‖Dw σ l w‖ ≤ (q.comp (Dop l : E →ₗ[ℂ] E)) (T w) := by
    intro l hl
    refine (he2 n ε H σ hU hI E p π dπ hπ hD T hT _ (hcont l) l 0 0 hl).2 fun y hy => ?_
    obtain ⟨h1, h2⟩ := key l hl y hy
    calc ‖Dw σ l y‖ ≤ q (T (Dw σ l y)) := hq1 _ h1
      _ = _ := by rw [h2]; rfl
  have main : ∀ S : List (List (Mx n)), Words (lieSet ε) S →
      ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ w, Sm ε σ w → sobNorm σ S w ≤ q' (T w) := by
    intro S
    induction S with
    | nil =>
      intro _
      refine ⟨0, by rw [Seminorm.coe_zero]; exact continuous_zero, fun w _ => ?_⟩
      simp [sobNorm]
    | cons l S ih =>
      intro hS
      obtain ⟨q', hq', h'⟩ := ih (fun m hm => hS m (List.mem_cons_of_mem _ hm))
      have hl : ∀ X ∈ l, X ∈ lieSet ε := hS l List.mem_cons_self
      refine ⟨q.comp (Dop l : E →ₗ[ℂ] E) + q', ?_, fun w hw' => ?_⟩
      · rw [Seminorm.coe_add]
        exact (hcont l).add hq'
      · have e : sobNorm σ (l :: S) w = ‖Dw σ l w‖ + sobNorm σ S w := by
          first
            | rfl
            | simp [sobNorm]
        rw [e, Seminorm.add_apply]
        exact add_le_add (hw l hl w hw') (h' w hw')
  exact main S hS

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BilinearFormCasimir
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)
open scoped InnerProductSpace

namespace PositivityTheory.CW.ExponentialKSet

variable {n : ℕ}

theorem exp_mem_kset' {ε : Fin n → Bool} {X : Mx n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    have hs : (t • X)ᴴ = -(t • X) := by
      rw [Matrix.conjTranspose_smul, h1]
      simp
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs,
      ← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • X)).neg_left), neg_add_cancel,
      NormedSpace.exp_zero]
  · exact ((h2.smul_left t).exp_left).eq

theorem lie_of {ε : Fin n → Bool} {X : Mx n} (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) : X ∈ lieSet ε := by
  show Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0
  rw [h1, Matrix.neg_mul, h2.eq, neg_add_cancel]

theorem commute_Jm {ε : Fin n → Bool} {X : Mx n} (h : ∀ i j, X i j ≠ 0 → ε i = ε j) :
    Commute X (Formalism.REAL.Jm ε) := by
  show X * Jm ε = Jm ε * X
  ext i j
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul]
  by_cases hx : X i j = 0
  · simp [hx]
  · rw [h i j hx, mul_comm]

theorem single_conjTranspose (a b : Fin n) (c : ℂ) : (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]

theorem single_neg' (a b : Fin n) (c : ℂ) : Matrix.single a b (-c) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.single_apply, Matrix.neg_apply]
  split_ifs <;> simp

theorem hasDerivAt_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : Submodule ℂ H)
    {f : ℝ → S} {f' : S} (h : HasDerivAt (fun t => (f t : H)) (f' : H) 0) : HasDerivAt f f' 0 := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h ⊢
  convert h using 2 with t
  show ‖((f t - f 0 - (t - 0) • f' : S) : H)‖ = _
  rw [Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul_of_tower]

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem actM_single (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) (c : ℂ) :
    actM E (Matrix.single a b c) = c • E a b := by
  classical
  simp [actM, Matrix.single_apply, ite_smul, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem actM_add (E : Fin n → Fin n → Module.End ℂ V) (X Y : Mx n) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

end Act

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

theorem key (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {B : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ} (hB : KInv ε σ B) {X : Mx n}
    (h1 : Xᴴ = -X) (h2 : Commute X (Formalism.REAL.Jm ε)) (v y : kfin ε σ) :
    B (actM E X v) y = - B v (actM E X y) := by
  have hX : X ∈ lieSet ε := lie_of h1 h2
  have hKt : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Kset ε := exp_mem_kset' h1 h2
  have hKU : ∀ k ∈ Kset ε, k ∈ UJset ε := by
    rintro k ⟨hu, hc⟩
    have h1' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
    show kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε
    calc kᴴ * Formalism.REAL.Jm ε * k = star k * (k * Formalism.REAL.Jm ε) := by
          rw [Matrix.mul_assoc, ← hc]; rfl
      _ = Formalism.REAL.Jm ε := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have hkinv : ∀ t : ℝ, ∀ w : H,
      σ (NormedSpace.exp (t • X)) (σ (NormedSpace.exp ((-t) • X)) w) = w := by
    intro t w
    rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ (hKU _ (hKt t)) _ (hKU _ (hKt (-t))),
      ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left t).smul_right (-t)),
      ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero, hU.1.1]
    rfl
  obtain ⟨Sv, fv, hv, stv⟩ : IsKFin ε σ (v : H) := v.2
  obtain ⟨Sy, fy, hy, sty⟩ : IsKFin ε σ (y : H) := y.2
  let W : Submodule ℂ H := Sv ⊔ Sy
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_sup Sv Sy
  have stW : ∀ g ∈ Kset ε, ∀ x ∈ W, σ g x ∈ W := by
    intro g hg x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (stv g hg a ha) (sty g hg b hb)
  have hWk : W ≤ kfin ε σ := fun x hx => ⟨W, inferInstance, hx, stW⟩
  have hclosed : IsClosed (W : Set H) := Submodule.closed_of_finiteDimensional W
  have hvW : (v : H) ∈ W := Submodule.mem_sup_left hv
  have hyW : (y : H) ∈ W := Submodule.mem_sup_right hy
  have hder : ∀ x : kfin ε σ,
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) x) ((actM E X x : H)) 0 := by
    intro x
    rw [hE X hX x]
    exact GlobalTheory.LowTypeDetermined.hasDerivAt_dRep (G := Formalism.REAL.Jm ε) (hD.1 _ x.2) hX
  have hmemW : ∀ x : kfin ε σ, (x : H) ∈ W → (actM E X x : H) ∈ W := by
    intro x hx
    refine hclosed.mem_of_tendsto (hder x).tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
    exact W.smul_mem _ (W.sub_mem (stW _ (hKt _) _ hx) (stW _ (hKt _) _ hx))
  let cv : ℝ → W := fun t => ⟨σ (NormedSpace.exp (t • X)) v, stW _ (hKt t) _ hvW⟩
  let cy : ℝ → W := fun t => ⟨σ (NormedSpace.exp (t • X)) y, stW _ (hKt t) _ hyW⟩
  have hcv : HasDerivAt cv ⟨_, hmemW v hvW⟩ 0 := hasDerivAt_sub W (hder v)
  have hcy : HasDerivAt cy ⟨_, hmemW y hyW⟩ (-0) := by
    rw [neg_zero]
    exact hasDerivAt_sub W (hder y)
  let ι : W →ₗ[ℂ] kfin ε σ := Submodule.inclusion hWk
  let ℓ1 : W →ₗ[ℝ] ℂ :=
    { toFun := fun w => B (ι w) y
      map_add' := fun a b => by simp only [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [← Complex.coe_smul, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
        simp [Complex.coe_smul] }
  let ℓ2 : W →ₗ[ℝ] ℂ := ((B v).comp ι).restrictScalars ℝ
  let L1 : W →L[ℝ] ℂ := ⟨ℓ1, LinearMap.continuous_of_finiteDimensional ℓ1⟩
  let L2 : W →L[ℝ] ℂ := ⟨ℓ2, LinearMap.continuous_of_finiteDimensional ℓ2⟩
  have d1 := L1.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcv
  have d2 := L2.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hcy.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ)))
  have heq : (L1 ∘ cv) = (L2 ∘ (cy ∘ Neg.neg)) := by
    funext t
    show B (ι (cv t)) y = B v (ι (cy (-t)))
    exact hB _ (hKt t) v (ι (cy (-t))) (ι (cv t)) y rfl (hkinv t y).symm
  rw [heq] at d1
  have hu := d2.unique d1
  rw [neg_one_smul] at hu
  have e1 : ι ⟨_, hmemW v hvW⟩ = actM E X v := Subtype.ext rfl
  have e2 : ι ⟨_, hmemW y hyW⟩ = actM E X y := Subtype.ext rfl
  change B v (ι (-⟨_, hmemW y hyW⟩)) = B (ι ⟨_, hmemW v hvW⟩) y at hu
  rw [map_neg, map_neg, e1, e2] at hu
  rw [← hu]

theorem compact_pair (hU : IsURepOn (UJset ε) σ) (hD : Dens ε σ) {E : Fin n → Fin n → Module.End ℂ (kfin ε σ)}
    (hE : KDer ε σ E) {B : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ} (hB : KInv ε σ B) (a b : Fin n) (hab : ε a = ε b)
    (v y : kfin ε σ) : B (E a b v) y = B v (E b a y) := by
  have hsup : ∀ (c d : ℂ) (i j : Fin n),
      (Matrix.single a b c + Matrix.single b a d) i j ≠ 0 → ε i = ε j := by
    intro c d i j h
    by_contra hne
    apply h
    have e1 : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => hne (h1 ▸ h2 ▸ hab)
    have e2 : ¬ (b = i ∧ a = j) := fun ⟨h1, h2⟩ => hne (h1 ▸ h2 ▸ hab.symm)
    simp [Matrix.single_apply, e1, e2]
  have s1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ =
      -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1)) := by
    rw [Matrix.conjTranspose_add, single_conjTranspose, single_conjTranspose]
    simp only [star_one, star_neg, single_neg']
    abel
  have s2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [Matrix.conjTranspose_add, single_conjTranspose, single_conjTranspose]
    simp only [Complex.star_def, Complex.conj_I, single_neg']
    abel
  have k1 := key hU hD hE hB s1 (commute_Jm (hsup 1 (-1))) v y
  have k2 := key hU hD hE hB s2 (commute_Jm (hsup Complex.I Complex.I)) v y
  rw [actM_add, actM_single, actM_single] at k1 k2
  simp only [one_smul, neg_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    map_add, map_neg, LinearMap.map_smulₛₗ, LinearMap.smul_apply, Complex.conj_I, smul_eq_mul,
    RingHom.id_apply, LinearMap.add_apply, LinearMap.neg_apply] at k1 k2
  linear_combination (1 / 2 : ℂ) * k1 + (Complex.I / 2) * k2 +
    ((B (E a b v) y - B v (E a b y) - B v (E b a y) + B (E b a v) y) / 2) * Complex.I_sq

end PositivityTheory.CW.ExponentialKSet

namespace PositivityTheory.CW

open ExponentialKSet in
theorem e2a : E2a := by
  unfold E2a AllIrr
  intro n ε H _ _ _ σ hU hI hD E hE B hB v y
  have hterm : ∀ a b, ε b = ε a → B ((E a b * E b a) v) y = B v ((E a b * E b a) y) := by
    intro a b h
    rw [Module.End.mul_apply, Module.End.mul_apply, compact_pair hU hD hE hB a b h.symm,
      compact_pair hU hD hE hB b a h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ReciprocityTheory.ChartRestriction.DS.casimirK, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb =>
    hterm a b (Finset.mem_filter.mp hb).2

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionAdditive
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary IsKStableSub adjSign)
open scoped InnerProductSpace

namespace PositivityTheory.CW.CasimirNonnegative

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem casK_symm (hU : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hs : adjSign ε a b = 1 := by simp [adjSign, hab]
  rw [hU a b, hs, one_mul, ← inner_conj_symm x, hU a b, hs, one_mul, inner_conj_symm]

end PositivityTheory.CW.CasimirNonnegative

namespace PositivityTheory.CW

open CasimirNonnegative in
theorem c2b : CardSubmodulesAndLinearEquivBounds := by
  intro n ε V _ _ E hGl hU hLF
  rw [eq_top_iff]
  intro v _
  obtain ⟨S, hfin, hvS, hstab⟩ := hLF v
  have hK : ∀ w ∈ S, casimirK ε E w ∈ S := by
    intro w hw
    unfold casimirK
    simp only [LinearMap.sum_apply, Module.End.mul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
    have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hstab a b hab.symm _ (hstab b a hab _ hw)
  let T : S →ₗ[ℂ] S := (casimirK ε E).restrict hK
  have hT : T.IsSymmetric := by
    intro x y
    exact casK_symm hU x y
  have hn : Module.finrank ℂ S = Module.finrank ℂ S := rfl
  have hsum := (hT.eigenvectorBasis hn).sum_repr ⟨v, hvS⟩
  have hv : v = ∑ i, ((hT.eigenvectorBasis hn).repr ⟨v, hvS⟩ i) • ((hT.eigenvectorBasis hn i : S) : V) := by
    have h0 := congrArg Subtype.val hsum
    simpa using h0.symm
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨hT.eigenvalues hn i, ?_⟩)
  show casimirK ε E (hT.eigenvectorBasis hn i : V) = ((hT.eigenvalues hn i : ℝ) : ℂ) • (hT.eigenvectorBasis hn i : V)
  exact congrArg Subtype.val (hT.apply_eigenvectorBasis hn i)

end PositivityTheory.CW
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.HilbertSchmidtSqEq
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK)

namespace PositivityTheory.CW.MatrixActionLinear

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem actM_add (A : Fin n → Fin n → Module.End ℂ M) (X Y : Mx n) : actM A (X + Y) = actM A X + actM A Y := by
  unfold actM
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem actM_smul (A : Fin n → Fin n → Module.End ℂ M) (c : ℂ) (X : Mx n) : actM A (c • X) = c • actM A X := by
  unfold actM
  simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem actM_single (A : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : actM A (Matrix.single a b 1) = A a b := by
  classical
  unfold actM
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro d _ hd
      simp [Ne.symm hd]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [Ne.symm hc]
  · simp

end PositivityTheory.CW.MatrixActionLinear

namespace PositivityTheory.CW

open MatrixActionLinear in
theorem e3b : faceMap_castSucc_comp_eq_succ := by
  classical
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ A hA T hT m
  haveI : IsTopologicalAddGroup E := hπ.withSeminorms.topologicalAddGroup
  haveI : ContinuousSMul ℂ E := hπ.withSeminorms.continuousSMul

  let P : Module.End ℂ (kfin ε σ) → Prop := fun u => ∃ D : E →L[ℂ] E, ∀ v : kfin ε σ, T ((u v : kfin ε σ) : H) = D (T v)
  have hone : P 1 := ⟨1, fun v => rfl⟩
  have hadd : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ + u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁ + D₂, fun v => ?_⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add (f := _), h₁, h₂, _root_.add_apply]
  have hmul : ∀ u₁ u₂, P u₁ → P u₂ → P (u₁ * u₂) := by
    rintro u₁ u₂ ⟨D₁, h₁⟩ ⟨D₂, h₂⟩
    refine ⟨D₁.comp D₂, fun v => ?_⟩
    rw [Module.End.mul_apply, h₁, h₂]
    rfl
  have hzero : P 0 := ⟨0, fun v => by simp⟩
  have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → Module.End ℂ (kfin ε σ)), (∀ i ∈ s, P (f i)) → P (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have hgen : ∀ a b, P (A a b) := by
    intro a b
    obtain ⟨h1, h2, h3, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
    set X₁ := cpart1 ε (Matrix.single a b 1)
    set X₂ := cpart2 ε (Matrix.single a b 1)
    have hX₁ : X₁ ∈ lieSet ε := h1
    have hX₂ : X₂ ∈ lieSet ε := h2
    have eA : A a b = actM A X₁ + Complex.I • actM A X₂ := by
      rw [← actM_single A a b, h3, actM_add, actM_smul]
    refine ⟨dπ X₁ + Complex.I • dπ X₂, fun v => ?_⟩
    have hv : IsKFin ε σ (v : H) := v.2
    rw [eA, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hA X₁ hX₁ v,
      hA X₂ hX₂ v, map_add, map_smul, hT X₁ hX₁ v hv, hT X₂ hX₂ v hv]
    rfl
  have hcas : P (casimirK ε A) := by
    unfold casimirK
    exact hsum _ _ fun a _ => hsum _ _ fun b _ => hmul _ _ (hgen a b) (hgen b a)
  have hpow : ∀ k : ℕ, P ((1 + casimirK ε A) ^ k) := by
    intro k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih (hadd _ _ hone hcas)
  exact hpow m

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ExistsFunctional
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace KInvarianceAlt

theorem kinv {n : ℕ} {ε : Fin n → Bool} {k : Mx n} (hk : k ∈ Kset ε) : ∃ k' ∈ Kset ε, k' * k = 1 := by
  obtain ⟨hu, hJ⟩ := hk
  have hu' : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hu; rwa [Matrix.star_eq_conjTranspose] at this
  have hJh : (Jm ε)ᴴ = Jm ε := by
    ext i j; simp only [Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
  have hJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    have h := congrArg Matrix.conjTranspose hJ
    simp only [Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hs' : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have := Unitary.star_mem hu; rwa [Matrix.star_eq_conjTranspose] at this
  exact ⟨kᴴ, ⟨hs', hJ'⟩, hu'⟩

end KInvarianceAlt

theorem e1a : SmoothSeminormGrowth := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ i
  obtain ⟨q, N, hq, hg⟩ := hπ.growth i
  haveI : Nonempty (UJset ε) := ⟨⟨1, one_mem_UJ ε⟩⟩
  set W : Mx n → ℝ := fun g => (1 + hs g) ^ N with hWdef
  have hW : ∀ g, 0 < W g := fun g => pow_pos (by linarith [hs_nonneg g]) _
  have hWm : ∀ a b : Mx n, W (a * b) ≤ W a * W b := fun a b => by
    simp only [hWdef]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith [hs_nonneg (a * b)]) (one_add_hs_mul_le a b) N
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ x, π (a * b) x = π a (π b x) := fun a ha b hb x => by
    rw [hπ.map_mul a ha b hb]; rfl
  let f : UJset ε → Seminorm ℂ E := fun g => (Real.toNNReal (W g.1)⁻¹) • (p i).comp (π g.1 : E →ₗ[ℂ] E)
  have hf : ∀ g x, f g x = p i (π g.1 x) / W g.1 := fun g x => by
    show ((Real.toNNReal (W g.1)⁻¹ : NNReal) : ℝ) * p i (π g.1 x) = _
    rw [Real.coe_toNNReal _ (inv_nonneg.2 (hW _).le), div_eq_inv_mul]
  have hfq : ∀ g x, f g x ≤ q x := fun g x => by
    rw [hf, div_le_iff₀ (hW _), mul_comm]
    exact hg g.1 g.2 x
  have hbdd : BddAbove (Set.range f) := ⟨q, by
    rintro _ ⟨g, rfl⟩
    exact Pi.le_def.2 fun x => hfq g x⟩
  have hfb : ∀ x, BddAbove (Set.range fun g => f g x) := fun x => ⟨q x, by
    rintro _ ⟨g, rfl⟩
    exact hfq g x⟩
  set Q : Seminorm ℂ E := ⨆ g, f g with hQdef
  have hQ : ∀ x, Q x = ⨆ g, f g x := fun x => Seminorm.iSup_apply hbdd
  have hle : ∀ g x, f g x ≤ Q x := fun g x => by rw [hQ]; exact le_ciSup (hfb x) g
  have hQq : Q ≤ q := Pi.le_def.2 fun x => by rw [hQ]; exact ciSup_le fun g => hfq g x
  have h1 : ∀ g ∈ UJset ε, ∀ x, p i (π g x) ≤ W g * Q x := fun g hg x => by
    have := hle ⟨g, hg⟩ x
    rw [hf, div_le_iff₀ (hW _)] at this
    linarith
  have hKk : ∀ k ∈ Kset ε, ∀ x, Q (π k x) ≤ Q x := fun k hk x => by
    rw [hQ (π k x)]
    refine ciSup_le fun g => ?_
    have hgk : g.1 * k ∈ UJset ε := mul_mem_UJ g.2 (K_le_UJ hk)
    have := hle ⟨g.1 * k, hgk⟩ x
    rw [hf] at this ⊢
    have e : W (g.1 * k) = W g.1 := by
      simp only [hWdef, ((Formalism.REAL.hermitian_small_ball n ε).2 g.1 k hk).1]
    rw [← hmul g.1 g.2 k (K_le_UJ hk), ← e]
    exact this
  refine ⟨Q, N, Seminorm.continuous_of_le hq hQq, h1, fun h hh x => ?_, fun k hk x => ?_⟩
  · rw [hQ (π h x)]
    refine ciSup_le fun g => ?_
    rw [hf, hmul g.1 g.2 h hh x |>.symm, div_le_iff₀ (hW _)]
    calc p i (π (g.1 * h) x) ≤ W (g.1 * h) * Q x := h1 _ (mul_mem_UJ g.2 hh) x
      _ ≤ (W g.1 * W h) * Q x := mul_le_mul_of_nonneg_right (hWm _ _) (apply_nonneg _ _)
      _ = W h * Q x * W g.1 := by ring
  · refine le_antisymm (hKk k hk x) ?_
    obtain ⟨k', hk', e⟩ := KInvarianceAlt.kinv hk
    have := hKk k' hk' (π k x)
    rwa [← hmul k' (K_le_UJ hk') k (K_le_UJ hk), e, hπ.map_one] at this

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SlopeLimitConstant
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum Filter Topology

namespace PositivityTheory.CW

namespace ExistsNormingFunctional

theorem exists_norming {E : Type} [AddCommGroup E] [Module ℂ E] (q : Seminorm ℂ E) (x₀ : E) :
    ∃ φ : Module.Dual ℂ E, ‖φ x₀‖ = q x₀ ∧ ∀ x, ‖φ x‖ ≤ q x := by
  have H : ∀ c : ℂ, c • x₀ = 0 → (RingHom.id ℂ) c • ((q x₀ : ℝ) : ℂ) = 0 := by
    intro c hc
    have h0 : ‖c‖ * q x₀ = 0 := by rw [← map_smul_eq_mul q, hc, map_zero]
    rcases mul_eq_zero.1 h0 with h | h
    · simp [norm_eq_zero.1 h]
    · simp [h]
  let f : Module.Dual ℂ (Submodule.span ℂ {x₀}) :=
    (LinearPMap.mkSpanSingleton' x₀ ((q x₀ : ℝ) : ℂ) H).toFun
  have hf : ∀ (c : ℂ) (h : c • x₀ ∈ Submodule.span ℂ {x₀}), f ⟨c • x₀, h⟩ = c * (q x₀ : ℂ) := by
    intro c h
    exact (LinearPMap.mkSpanSingleton'_apply x₀ ((q x₀ : ℝ) : ℂ) H c h).trans (by simp)
  have h1 : f ⟨x₀, Submodule.mem_span_singleton_self x₀⟩ = (q x₀ : ℂ) :=
    LinearPMap.mkSpanSingleton'_apply_self x₀ ((q x₀ : ℝ) : ℂ) H _
  obtain ⟨g, hg, hgq⟩ := Module.Dual.exists_extension_of_le_seminorm
    (Submodule.span ℂ {x₀}) f (p := q) (by
      rintro ⟨z, hz⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]
      exact le_of_eq (map_smul_eq_mul q c x₀).symm)
  refine ⟨g, ?_, hgq⟩
  have h2 := hg ⟨x₀, Submodule.mem_span_singleton_self x₀⟩
  rw [h1] at h2
  rw [show g x₀ = (q x₀ : ℂ) from h2, Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q x₀)]

end ExistsNormingFunctional

private theorem exp_smul_mem_UJset_of_mem_lieSet {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : X ∈ lieSet ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε := by
  set J := ReciprocityTheory.ChartRestriction.DS.Jm ε with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef, ReciprocityTheory.ChartRestriction.DS.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨J, J, hJJ, hJJ⟩
  have hX' : Xᴴ * J + J * X = 0 := hX
  set Y : Matrix (Fin n) (Fin n) ℂ := t • X with hYdef
  have hYJ : Yᴴ * J = -(J * Y) := by
    rw [hYdef, Matrix.conjTranspose_smul, star_trivial, smul_mul_assoc, Matrix.mul_smul,
      eq_neg_of_add_eq_zero_left hX', smul_neg]
  have hY : Yᴴ = J * (-Y) * J := by
    calc Yᴴ = Yᴴ * J * J := by rw [mul_assoc, hJJ, mul_one]
      _ = J * (-Y) * J := by rw [hYJ, mul_neg, neg_mul]
  have hexp : NormedSpace.exp Yᴴ = J * NormedSpace.exp (-Y) * J := by
    have h := Matrix.exp_units_conj u (-Y)
    rw [hY]
    exact h
  have hdet : IsUnit (NormedSpace.exp Y).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  show (NormedSpace.exp Y)ᴴ * J * NormedSpace.exp Y = J
  rw [← Matrix.exp_conjTranspose, hexp, Matrix.exp_neg]
  simp only [mul_assoc]
  rw [← mul_assoc J J, hJJ, one_mul, Matrix.nonsing_inv_mul _ hdet, mul_one]

theorem d1b : D1 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hCore T₀ hT i
  obtain ⟨q, N, hq, hgrow⟩ := hπ.growth i
  obtain ⟨S, C, I₀, hS, hC, hI₀, hmain⟩ := hCore N
  refine ⟨S, C * ∑ e ∈ I₀, q (T₀ e), hS, ?_⟩
  intro w hw
  obtain ⟨φ, hφ1, hφ2⟩ := ExistsNormingFunctional.exists_norming (p i) (T₀ w)
  have hφc : Continuous φ :=
    hπ.withSeminorms.continuous_normedSpace_rng ℂ φ ⟨{i}, 1, by
      intro x
      simpa using hφ2 x⟩
  let F : H →ₗ[ℂ] Mx n → ℂ :=
    LinearMap.pi (fun g => φ ∘ₗ (π g).toLinearMap ∘ₗ T₀)
  have hF : ∀ v g, F v g = φ (π g (T₀ v)) := fun _ _ => rfl
  have hpos : ∀ g : Mx n, 0 ≤ (1 + hs g) ^ N := by
    intro g
    apply pow_nonneg
    have : 0 ≤ hs g := by
      unfold hs
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hB : 0 ≤ ∑ e ∈ I₀, q (T₀ e) := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  have key := hmain F
    (fun v _ => by
      show ContinuousOn (fun g => φ (π g (T₀ v))) (UJset ε)
      exact hφc.comp_continuousOn (hπ.continuousOn (T₀ v)))
    (fun X hX v hv g hg => by
      rw [hF, hT.2 X hX v hv, hasDerivAt_iff_tendsto_slope]
      have hΛ : Continuous fun z : E => φ (π g z) := hφc.comp (π g).continuous
      have heq : slope (fun t : ℝ => F v (g * NormedSpace.exp (t • X))) 0 =
          fun t : ℝ => φ (π g (((t : ℂ))⁻¹ • ((π (NormedSpace.exp (t • X))) (T₀ v) - T₀ v))) := by
        funext t
        rw [slope_def_module]
        simp only [hF, sub_zero, zero_smul, NormedSpace.exp_zero, mul_one,
          hπ.map_mul g hg _ (exp_smul_mem_UJset_of_mem_lieSet ε X hX t), ContinuousLinearMap.comp_apply, map_smul, map_sub,
          smul_eq_mul, Complex.real_smul, Complex.ofReal_inv]
      rw [heq]
      exact (hΛ.tendsto _).comp (hπ.hasDRep X hX (T₀ v)))
    (fun v _ => ⟨q (T₀ v), fun g hg => by
      rw [hF]
      calc ‖φ (π g (T₀ v))‖ ≤ p i (π g (T₀ v)) := hφ2 _
        _ ≤ (1 + hs g) ^ N * q (T₀ v) := hgrow g hg (T₀ v)
        _ = q (T₀ v) * (1 + hs g) ^ N := mul_comm _ _⟩)
    (∑ e ∈ I₀, q (T₀ e)) hB
    (fun e he g hg => by
      rw [hF]
      calc ‖φ (π g (T₀ e))‖ ≤ p i (π g (T₀ e)) := hφ2 _
        _ ≤ (1 + hs g) ^ N * q (T₀ e) := hgrow g hg (T₀ e)
        _ ≤ (1 + hs g) ^ N * ∑ e ∈ I₀, q (T₀ e) :=
          mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := fun e => q (T₀ e)) (fun _ _ => apply_nonneg _ _) he)
            (hpos g)
        _ = (∑ e ∈ I₀, q (T₀ e)) * (1 + hs g) ^ N := mul_comm _ _)
    w hw
  rw [hF, hπ.map_one, ContinuousLinearMap.one_apply] at key
  rw [← hφ1]
  exact key

end PositivityTheory.CW
end

namespace PositivityTheory.CW

theorem lift_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallachLift := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact lift_of_steps hM hmodel c4 c5 c6 c7 d0 d1b d2 d3 d4b d5

theorem cw_of (hM : MaxPr) : GlobalTheory.Published.CasselmanWallach := by
  have hmodel := model_of c1 c2a c2b c3a c3b (k_types_finite_of_highest_weight c3c)
  exact cw_of_steps hM hmodel c5 d0 (lift_of hM) e1a e1b e2a e2b e2c e2d e3a e3b e3c e3d

end PositivityTheory.CW
