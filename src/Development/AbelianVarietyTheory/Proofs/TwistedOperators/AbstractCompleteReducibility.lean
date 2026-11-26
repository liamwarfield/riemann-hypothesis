module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbstractCompleteReducibility
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbstractCompleteReducibility
open Module

namespace GlobalTheory

theorem exists_mem_sub_orth_of_finiteDimensional {E : Type} [AddCommGroup E] [Module ℂ E]
    (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (T : Submodule ℂ E) [FiniteDimensional ℂ T]
    (hT : ∀ t ∈ T, b t t = 0 → t = 0) (ψ : E) : ∃ s ∈ T, ∀ t ∈ T, b t (ψ - s) = 0 := by
  let bs := Module.finBasis ℂ T
  let F : E →ₗ[ℂ] (Fin (finrank ℂ T) → ℂ) := LinearMap.pi fun i => b (bs i : E)
  have key : ∀ x, F x = 0 → ∀ t ∈ T, b t x = 0 := by
    intro x hx t ht
    have h1 : (b.flip x) ∘ₛₗ T.subtype = 0 :=
      bs.ext fun i => by simpa [F] using congrFun hx i
    exact LinearMap.congr_fun h1 ⟨t, ht⟩
  have hinj : Function.Injective (F ∘ₗ T.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    exact Subtype.ext (hT z z.2 (key z hz z z.2))
  have hsurj : Function.Surjective (F ∘ₗ T.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨z, hz⟩ := hsurj (F ψ)
  refine ⟨z, z.2, key (ψ - z) ?_⟩
  rw [map_sub, ← hz]
  simp

theorem abstract_complete_reducibility :
    ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by
  classical
  intro E _ _ P hInf N hN b hpos _hherm hperp e he hidem hsa hfin ψ hψN hψe
  let S := ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A
  show ψ ∈ S
  let V := N.map e
  have hVN : V ≤ N := by rintro _ ⟨x, hx, rfl⟩; exact he N le_rfl hN x hx
  have heV : ∀ v ∈ V, e v = v := by rintro _ ⟨x, hx, rfl⟩; exact hidem x hx
  have hψV : ψ ∈ V := ⟨ψ, hψN, hψe⟩
  have hIrrS : ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → A ≤ S :=
    fun A hA => le_iSup₂_of_le (f := fun A (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) => A) A hA le_rfl
  have hpos0 : ∀ x ∈ N, b x x = 0 → x = 0 := by
    intro x hx h0
    by_contra hne
    have := hpos x hx hne
    rw [h0] at this
    simp at this
  have hGen : ∀ x : E, ∃ G : Submodule ℂ E, x ∈ G ∧ P G ∧ ∀ A, x ∈ A → P A → G ≤ A := fun x =>
    ⟨sInf {A | x ∈ A ∧ P A}, Submodule.mem_sInf.2 fun A hA => hA.1, hInf _ fun A hA => hA.2,
      fun A hx hA => sInf_le ⟨hx, hA⟩⟩
  let C : Submodule ℂ E := sInf (insert N {X | ∃ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
    ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) ∧ X = N ⊓ ⨅ a ∈ A, LinearMap.ker (b a)})
  have hCP : P C := by
    apply hInf
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hN
    · exact hperp A hA.1 hA.2.1
  have hCorth : ∀ x ∈ C, ∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0 := by
    intro x hx A hA a ha
    have : x ∈ N ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
      Submodule.mem_sInf.1 hx _ (Set.mem_insert_of_mem _ ⟨A, hA, rfl⟩)
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this.2 a ha
  have hCmem : ∀ x ∈ N, (∀ A : Submodule ℂ E, (A ≤ N ∧ P A ∧ A ≠ ⊥ ∧
      ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A) → ∀ a ∈ A, b a x = 0) → x ∈ C := by
    intro x hx h
    refine Submodule.mem_sInf.2 ?_
    rintro X (rfl | ⟨A, hA, rfl⟩)
    · exact hx
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
      exact ⟨hx, fun a ha => h A hA a ha⟩
  have hfinT : FiniteDimensional ℂ ↥(S ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hsT, hsorth⟩ := exists_mem_sub_orth_of_finiteDimensional b (S ⊓ V)
    (fun t ht h0 => hpos0 t (hVN ht.2) h0) ψ
  have hcV : ψ - s ∈ V := V.sub_mem hψV hsT.2
  have hcC : ψ - s ∈ C := by
    refine hCmem _ (hVN hcV) fun A hA a ha => ?_
    have haN : a ∈ N := hA.1 ha
    have heaT : e a ∈ S ⊓ V := ⟨hIrrS A hA (he A hA.1 hA.2.1 a ha), ⟨a, haN, rfl⟩⟩
    rw [← heV _ hcV, ← hsa a haN _ (hVN hcV)]
    exact hsorth _ heaT
  suffices hc0 : ψ - s = 0 by
    rw [sub_eq_zero] at hc0
    rw [hc0]
    exact hsT.1
  by_contra hc0
  obtain ⟨D, hcD, hDP, hDmin⟩ := hGen (ψ - s)
  have hDC : D ≤ C := hDmin C hcC hCP
  have hDN : D ≤ N := hDmin N (hVN hcV) hN
  have hex : ∃ n, ∃ B : Submodule ℂ E, B ≤ D ∧ P B ∧ B ⊓ V ≠ ⊥ ∧ finrank ℂ ↥(B ⊓ V) = n :=
    ⟨_, D, le_rfl, hDP, (Submodule.ne_bot_iff _).2 ⟨ψ - s, ⟨hcD, hcV⟩, hc0⟩, rfl⟩
  obtain ⟨B, hBD, hBP, hBV, hBn⟩ := Nat.find_spec hex
  have hmin : ∀ B₁ : Submodule ℂ E, B₁ ≤ D → P B₁ → B₁ ⊓ V ≠ ⊥ →
      Nat.find hex ≤ finrank ℂ ↥(B₁ ⊓ V) :=
    fun B₁ h1 h2 h3 => Nat.find_min' hex ⟨B₁, h1, h2, h3, rfl⟩
  obtain ⟨β, hβBV, hβ0⟩ := (Submodule.ne_bot_iff _).1 hBV
  obtain ⟨G, hβG, hGP, hGmin⟩ := hGen β
  have hGB : G ≤ B := hGmin B hβBV.1 hBP
  have hGN : G ≤ N := hGB.trans (hBD.trans hDN)
  have hβV : β ∈ V := hβBV.2
  have hβe : e β = β := heV β hβV
  have hGirr : G ≤ N ∧ P G ∧ G ≠ ⊥ ∧ ∀ B'' : Submodule ℂ E, B'' ≤ G → P B'' → B'' = ⊥ ∨ B'' = G := by
    refine ⟨hGN, hGP, (Submodule.ne_bot_iff _).2 ⟨β, hβG, hβ0⟩, fun B'' hle hP => ?_⟩
    have hB''N : B'' ≤ N := hle.trans hGN
    by_cases hV'' : B'' ⊓ V = ⊥
    · left
      have hey : ∀ y ∈ B'', e y = 0 := by
        intro y hy
        have : e y ∈ B'' ⊓ V := ⟨he B'' hB''N hP y hy, ⟨y, hB''N hy, rfl⟩⟩
        rw [hV''] at this
        exact (Submodule.mem_bot ℂ).1 this
      have hβperp : β ∈ N ⊓ ⨅ a ∈ B'', LinearMap.ker (b a) := by
        simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
        refine ⟨hVN hβV, fun y hy => ?_⟩
        rw [← hβe, ← hsa y (hB''N hy) β (hVN hβV), hey y hy, map_zero, LinearMap.zero_apply]
      have hGperp := hGmin _ hβperp (hperp B'' hB''N hP)
      rw [eq_bot_iff]
      intro y hy
      have hyp := hGperp (hle hy)
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hyp
      exact (Submodule.mem_bot ℂ).2 (hpos0 y (hB''N hy) (hyp.2 y hy))
    · right
      have hle' : B'' ⊓ V ≤ B ⊓ V := inf_le_inf_right _ (hle.trans hGB)
      have hfinBV : FiniteDimensional ℂ ↥(B ⊓ V) := Submodule.finiteDimensional_of_le inf_le_right
      have heq : B'' ⊓ V = B ⊓ V := Submodule.eq_of_le_of_finrank_le hle' (by
        rw [hBn]; exact hmin B'' (hle.trans (hGB.trans hBD)) hP hV'')
      have hβB'' : β ∈ B'' := by
        have h2 := hβBV
        rw [← heq] at h2
        exact h2.1
      exact le_antisymm hle (hGmin B'' hβB'' hP)
  exact hβ0 (hpos0 β (hVN hβV) (hCorth β (hDC (hBD hβBV.1)) G hGirr β hβG))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbstractCompleteReducibilityStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_iSup_irreducible_of_fixed_projector : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by
  first | exact @GlobalTheory.abstract_complete_reducibility | exact GlobalTheory.abstract_complete_reducibility | (intros; apply GlobalTheory.abstract_complete_reducibility <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelation
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate

noncomputable section

namespace GlobalTheory.WrongSignGauss

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def sesq : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ).flip.comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).flip

@[simp] theorem sesq_apply (u w : ℂ) : sesq u w = u * conj w := by
  simp [sesq]; ring

def mulForm (ℓ : V →ₗ[ℝ] ℝ) : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (⇑(LinearMap.toContinuousLinearMap ℓ))

theorem mulForm_apply (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    mulForm ℓ f x = (ℓ x : ℂ) * f x := by
  rw [mulForm, SchwartzMap.smulLeftCLM_apply_apply (ContinuousLinearMap.hasTemperateGrowth _)]
  simp [Complex.real_smul]

theorem lineDerivOp_mulForm (v : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (mulForm ℓ f) x = (ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x := by
  have e : (⇑(mulForm ℓ f)) = ⇑(LinearMap.toContinuousLinearMap ℓ) • ⇑f := by
    funext y; rw [Pi.smul_apply', mulForm_apply, Complex.real_smul]; rfl
  have h2 := ((LinearMap.toContinuousLinearMap ℓ).hasFDerivAt (x := x)).smul (f.hasFDerivAt x)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, e, h2.fderiv]
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, Complex.real_smul]

theorem lineDerivOp_comm' (u v : V) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (∂_{u} f) x = ∂_{u} (∂_{v} f) x := by
  have key : ∀ (u v : V) x, ∂_{v} (∂_{u} f) x = fderiv ℝ (fderiv ℝ f) x v u := by
    intro u v x
    have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      ((SchwartzMap.fderivCLM ℝ _ ℂ f).differentiableAt (x := x)).hasFDerivAt
    have h1 := ((ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt (x := fderiv ℝ f x)).comp x hd
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have e : (⇑(∂_{u} f : 𝓢(V, ℂ))) = (ContinuousLinearMap.apply ℝ ℂ u) ∘ fderiv ℝ f := by
      funext y; rfl
    rw [e, h1.fderiv]
    rfl
  rw [key, key]
  exact ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

def twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f - (2 * Real.pi * Complex.I) • mulForm ℓ f

theorem twD_apply (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    twD a ℓ f x = ∂_{a} f x - 2 * Real.pi * Complex.I * ((ℓ x : ℂ) * f x) := by
  simp [twD, mulForm_apply]

section integrals

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

def ip (u w : 𝓢(V, ℂ)) : ℂ := ∫ x, u x * conj (w x) ∂μ

theorem integrable_ip (u w : 𝓢(V, ℂ)) : Integrable (fun x => u x * conj (w x)) μ := by
  have h := (pairing sesq u w).integrable (μ := μ)
  simpa [pairing_apply] using h

theorem ip_smul_left (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ (c • u) w = c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem ip_smul_right (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ u (c • w) = conj c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem ip_sub_left (u v w : 𝓢(V, ℂ)) : ip μ (u - v) w = ip μ u w - ip μ v w := by
  simp only [ip, SchwartzMap.sub_apply, sub_mul]
  exact integral_sub (integrable_ip μ u w) (integrable_ip μ v w)

theorem ip_sub_right (u v w : 𝓢(V, ℂ)) : ip μ w (u - v) = ip μ w u - ip μ w v := by
  simp only [ip, SchwartzMap.sub_apply, map_sub, mul_sub]
  exact integral_sub (integrable_ip μ w u) (integrable_ip μ w v)

theorem ip_lineDerivOp (a : V) (u w : 𝓢(V, ℂ)) : ip μ (∂_{a} u) w = - ip μ u (∂_{a} w) := by
  have h := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ) u w sesq a
  simp only [sesq_apply] at h
  simp only [ip, h, neg_neg]

theorem ip_mulForm (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) : ip μ (mulForm ℓ u) w = ip μ u (mulForm ℓ w) := by
  simp only [ip, mulForm_apply, map_mul, Complex.conj_ofReal]
  congr 1; funext x; ring

theorem ip_twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) :
    ip μ (twD a ℓ u) w = - ip μ u (twD a ℓ w) := by
  simp only [twD, ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, ip_lineDerivOp, ip_mulForm]
  simp [map_mul, Complex.conj_ofReal, map_ofNat]
  ring

end integrals

theorem lineDerivOp_twD (v a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (twD a ℓ f) x = ∂_{v} (∂_{a} f) x -
      2 * Real.pi * Complex.I * ((ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x) := by
  rw [twD, ← LineDeriv.lineDerivOpCLM_apply (R := ℂ), map_sub, map_smul,
    LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOpCLM_apply]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, lineDerivOp_mulForm]

theorem twD_comm (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    twD a₁ ℓ₁ (twD a₂ ℓ₂ f) - twD a₂ ℓ₂ (twD a₁ ℓ₁ f) =
      (-(2 * Real.pi * Complex.I) * ((ℓ₂ a₁ - ℓ₁ a₂ : ℝ) : ℂ)) • f := by
  ext x
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, twD_apply _ _ (twD _ _ f),
    lineDerivOp_twD]
  rw [twD_apply, twD_apply, lineDerivOp_comm' a₁ a₂ f x]
  push_cast
  ring

section main

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

theorem ip_self (h : 𝓢(V, ℂ)) : ip μ h h = ((∫ x, ‖h x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [ip]
  rw [← integral_complex_ofReal]
  congr 1; funext x
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_sq_twD (f : 𝓢(V, ℂ)) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ)
    (hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f) :
    ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ = Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h1 : ip μ (twD a₁ ℓ₁ (twD a₂ ℓ₂ f)) f = -(Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_left]
  have h2 : ip μ (twD a₂ ℓ₂ (twD a₁ ℓ₁ f)) f = -(conj Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_right]
  have h3 := congrArg (fun u => ip μ u f) (twD_comm a₁ a₂ ℓ₁ ℓ₂ f)
  simp only [ip_sub_left, ip_smul_left, h1, h2, Complex.conj_I, ip_self] at h3
  have E : ((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ((Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    push_cast at h3 ⊢
    linear_combination (Complex.I / 2) * h3 +
      (((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) - Real.pi * ((ℓ₂ a₁ : ℂ) - ℓ₁ a₂) *
        ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)) * Complex.I_sq
  exact_mod_cast E

end main

theorem vanish : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ),
    (∀ y, fderiv ℝ f y a₂ + (-(2 * Real.pi * Complex.I) * (ℓ₂ y : ℂ)) * f y =
      Complex.I * (fderiv ℝ f y a₁ + (-(2 * Real.pi * Complex.I) * (ℓ₁ y : ℂ)) * f y)) →
    ℓ₂ a₁ - ℓ₁ a₂ < 0 → f = 0 := by
  intro V _ _ _ f a₁ a₂ ℓ₁ ℓ₂ hf hc
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  have hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f := by
    ext y
    simp only [SchwartzMap.smul_apply, smul_eq_mul, twD_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    linear_combination hf y
  have hk := norm_sq_twD μ f a₁ a₂ ℓ₁ ℓ₂ hD
  have hG : 0 ≤ ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hF : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hP : Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) < 0 := mul_neg_of_pos_of_neg Real.pi_pos hc
  have hF0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by nlinarith
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    refine (integrable_ip μ f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  rw [integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint] at hF0
  have hcont : Continuous (fun x => ‖f x‖ ^ 2) := f.continuous.norm.pow 2
  have h0 := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hF0
  ext x
  have hx := congrFun h0 x
  simpa using hx

end GlobalTheory.WrongSignGauss
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_eq_zero_of_wrong_sign_gaussian_relation : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ),
    (∀ y, fderiv ℝ f y a₂ + (-(2 * Real.pi * Complex.I) * (ℓ₂ y : ℂ)) * f y =
      Complex.I * (fderiv ℝ f y a₁ + (-(2 * Real.pi * Complex.I) * (ℓ₁ y : ℂ)) * f y)) →
    ℓ₂ a₁ - ℓ₁ a₂ < 0 → f = 0 := by
  first | exact @GlobalTheory.WrongSignGauss.vanish | exact GlobalTheory.WrongSignGauss.vanish | (intros; apply GlobalTheory.WrongSignGauss.vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairIsUnitDetBlocks
open scoped Matrix

namespace GlobalTheory

theorem exists_det_add_mul_ne_zero_of_ker_inf {k : Type} [Field k] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) k)
    (h : ∀ v : Fin n → k, A *ᵥ v = 0 → C *ᵥ v = 0 → v = 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, (A + X * C).det ≠ 0 := by
  classical
  set a := Matrix.toLin' A with ha
  set c := Matrix.toLin' C with hc
  obtain ⟨L', hL'⟩ := Submodule.exists_isCompl (LinearMap.ker c)
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl ((LinearMap.ker c).map a)

  have hkey : ∀ x ∈ LinearMap.ker c, a x = 0 → x = 0 := by
    intro x hx hax
    rw [LinearMap.mem_ker] at hx
    exact h x (by simpa [ha] using hax) (by simpa [hc] using hx)
  have hinj : Function.Injective (a.domRestrict (LinearMap.ker c)) := by
    intro x y hxy
    have hxy' : a ((x : Fin n → k) - y) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr (by simpa using hxy)
    have := hkey _ (Submodule.sub_mem _ x.2 y.2) hxy'
    exact Subtype.ext (sub_eq_zero.mp this)
  have hrank : Module.finrank k L' = Module.finrank k U := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hL'
    have h2 := Submodule.finrank_add_eq_of_isCompl hU
    have h3 : Module.finrank k ((LinearMap.ker c).map a) = Module.finrank k (LinearMap.ker c) := by
      rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
    omega
  let e : L' ≃ₗ[k] U := LinearEquiv.ofFinrankEq L' U hrank
  let g : (Fin n → k) →ₗ[k] (Fin n → k) :=
    LinearMap.ofIsCompl hL' (a.domRestrict (LinearMap.ker c)) (U.subtype ∘ₗ e.toLinearMap)
  have hgL : ∀ x (hx : x ∈ LinearMap.ker c), g x = a x := fun x hx =>
    LinearMap.ofIsCompl_apply_left hL' ⟨x, hx⟩
  have hgL' : ∀ y (hy : y ∈ L'), g y = (e ⟨y, hy⟩ : Fin n → k) := fun y hy =>
    LinearMap.ofIsCompl_apply_right hL' ⟨y, hy⟩

  have hg_inj : ∀ v, g v = 0 → v = 0 := by
    intro v hv
    have hvmem : v ∈ LinearMap.ker c ⊔ L' := by rw [hL'.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hvmem
    rw [map_add (f := _), hgL x hx, hgL' y hy] at hv
    have hax : a x ∈ (LinearMap.ker c).map a ⊓ U := by
      refine ⟨Submodule.mem_map_of_mem hx, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hv]
      exact U.neg_mem (e ⟨y, hy⟩).2
    rw [hU.inf_eq_bot, Submodule.mem_bot] at hax
    have hx0 := hkey x hx hax
    rw [hax, zero_add] at hv
    have hy0 : e ⟨y, hy⟩ = 0 := Subtype.ext hv
    rw [LinearEquiv.map_eq_zero_iff] at hy0
    rw [hx0, zero_add]
    exact congrArg Subtype.val hy0

  have hle : LinearMap.ker c ≤ LinearMap.ker (g - a) := fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hgL x hx, sub_self]
  let f0 : LinearMap.range c →ₗ[k] (Fin n → k) :=
    ((LinearMap.ker c).liftQ (g - a) hle) ∘ₗ (c.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨Y, hY⟩ := LinearMap.exists_extend f0
  have hfac : ∀ v, Y (c v) = g v - a v := by
    intro v
    have h0 := LinearMap.congr_fun hY ⟨c v, LinearMap.mem_range_self c v⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h0
    rw [h0]
    simp only [f0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.sub_apply]
  refine ⟨LinearMap.toMatrix' Y, fun hdet => ?_⟩
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply hg_inj
  have hmv : (A + LinearMap.toMatrix' Y * C) *ᵥ v = g v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    have hcv : C *ᵥ v = c v := by rw [hc, Matrix.toLin'_apply]
    have hav : A *ᵥ v = a v := by rw [ha, Matrix.toLin'_apply]
    rw [hcv, hfac, hav]
    abel
  rw [← hmv, hv]

theorem exists_isUnit_det_toBlocks_add_mul {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ}
    (H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hH : IsUnit H.det) :
    ∃ X : Matrix (Fin n) (Fin n) R, IsUnit (H.toBlocks₁₁ + X * H.toBlocks₂₁).det := by
  classical
  set Hb := H.map (IsLocalRing.residue R) with hHb_def
  have hHb : Hb.det ≠ 0 := by
    rw [hHb_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hH.map (IsLocalRing.residue R)).ne_zero
  obtain ⟨Xb, hXb⟩ := exists_det_add_mul_ne_zero_of_ker_inf Hb.toBlocks₁₁ Hb.toBlocks₂₁ (by
    intro v h1 h2
    by_contra hv
    apply hHb
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, ?_, ?_⟩
    · intro h0
      apply hv
      funext i
      simpa using congrFun h0 (Sum.inl i)
    · funext i
      cases i with
      | inl i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁] using congrFun h1 i
      | inr i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁] using congrFun h2 i)
  choose X hX using fun i j => IsLocalRing.residue_surjective (R := R) (Xb i j)
  refine ⟨Matrix.of X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hm : (IsLocalRing.residue R).mapMatrix (H.toBlocks₁₁ + Matrix.of X * H.toBlocks₂₁) =
      Hb.toBlocks₁₁ + Xb * Hb.toBlocks₂₁ := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [RingHom.mapMatrix_apply, Matrix.mul_apply, map_sum, hX, hHb_def, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁]
  rw [hm]
  exact hXb

theorem isUnit_det_of_dual_blocks {R : Type} [CommRing R] {n : ℕ}
    (S A B C D A' C' : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det)
    (h1 : Aᵀ * (S * C') + Cᵀ * (S * A') = 0)
    (h2 : IsUnit (Bᵀ * (S * C') + Dᵀ * (S * A')).det) : IsUnit A'.det := by
  have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  have hSC : S * C' = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by
    have h1' : Aᵀ * (S * C') = -(Cᵀ * (S * A')) := eq_neg_of_add_eq_zero_left h1
    calc S * C' = Aᵀ⁻¹ * (Aᵀ * (S * C')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAt, Matrix.one_mul]
      _ = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by rw [h1', Matrix.mul_neg]
  have key : Bᵀ * (S * C') + Dᵀ * (S * A') = (Dᵀ - Bᵀ * Aᵀ⁻¹ * Cᵀ) * (S * A') := by
    rw [hSC]
    generalize Aᵀ⁻¹ = M
    noncomm_ring
  rw [key, Matrix.det_mul, Matrix.det_mul] at h2
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right h2)

private lemma blocks_conj_eq_fromBlocks_sums {R : Type} [CommRing R] {n : ℕ}
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix.fromBlocks 1 1 1 (-1) * G * Matrix.fromBlocks 1 1 1 (-1) =
      Matrix.fromBlocks (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ + G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ - G.toBlocks₂₁ + G.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks G]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> noncomm_ring

private lemma H_affine_combination_eq_of_quadratic_relation {R : Type} [CommRing R] {n : ℕ}
    (S a11 a12 a21 a22 b11 b12 b21 b22 X₁ X₂ : Matrix (Fin n) (Fin n) R)
    (E11 : a11ᵀ * S * b11 - a21ᵀ * S * b21 = S) (E12 : a11ᵀ * S * b12 - a21ᵀ * S * b22 = 0)
    (E21 : a12ᵀ * S * b11 - a22ᵀ * S * b21 = 0) (E22 : a12ᵀ * S * b12 - a22ᵀ * S * b22 = -S)
    (hX : X₁ᵀ * S + S * X₂ = 0) :
    (a11 + a12 + a21 + a22 + X₁ * (a11 + a12 - a21 - a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 + a12 - a21 - a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = 0 ∧
      (a11 - a12 + a21 - a22 + X₁ * (a11 - a12 - a21 + a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 - a12 - a21 + a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = S + S + S + S := by
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul]
  constructor
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ + a12ᵀ - a21ᵀ - a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) := by
          noncomm_ring
      _ = 0 := by rw [E11, E12, E21, E22, hX]; noncomm_ring
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ - a12ᵀ - a21ᵀ + a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) +
          (S + S + S + S) := by
          noncomm_ring
      _ = S + S + S + S := by rw [E11, E12, E21, E22, hX]; noncomm_ring

theorem exists_dual_pair_isUnit_det_blocks :
    ∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det := by
  intro R _ _ h2 n S hS G₁ G₂ hG₁ hG
  classical
  have hKdet : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)
      (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R)).det := by
    rw [Matrix.det_fromBlocks_one₁₁]
    have e : (-1 - 1 * 1 : Matrix (Fin n) (Fin n) R) = (-2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      split_ifs <;> ring
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact h2.neg.pow n
  obtain ⟨X₁, hX₁⟩ := exists_isUnit_det_toBlocks_add_mul
    (Matrix.fromBlocks 1 1 1 (-1) * G₁ * Matrix.fromBlocks 1 1 1 (-1))
    (by rw [Matrix.det_mul, Matrix.det_mul]; exact (hKdet.mul hG₁).mul hKdet)
  rw [blocks_conj_eq_fromBlocks_sums, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁] at hX₁
  have hsum : X₁ᵀ * S + S * -(S⁻¹ * X₁ᵀ * S) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS,
      Matrix.one_mul, add_neg_cancel]
  refine ⟨X₁, -(S⁻¹ * X₁ᵀ * S), hsum, hX₁, ?_⟩
  have hG' := hG
  rw [← Matrix.fromBlocks_toBlocks G₁, ← Matrix.fromBlocks_toBlocks G₂, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hG'
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp hG'
  have E11 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₁ = S := by
    convert e11 using 1; noncomm_ring
  have E12 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₂ = 0 := by
    convert e12 using 1; noncomm_ring
  have E21 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₁ = 0 := by
    convert e21 using 1; noncomm_ring
  have E22 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₂ = -S := by
    convert e22 using 1; noncomm_ring
  obtain ⟨c1, c2⟩ := H_affine_combination_eq_of_quadratic_relation S _ _ _ _ _ _ _ _ X₁ _ E11 E12 E21 E22 hsum
  have h4 : IsUnit (4 : R) := by
    have := h2.mul h2
    norm_num at this
    exact this
  have hU4 : IsUnit (S + S + S + S).det := by
    have e : S + S + S + S = (4 : R) • S := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e, Matrix.det_smul]
    exact (h4.pow _).mul hS
  rw [← c2] at hU4
  exact isUnit_det_of_dual_blocks S _ _ _ _ _ _ hX₁ c1 hU4

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensity
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensity
open scoped InnerProductSpace

namespace GlobalTheory

namespace IrreducibleUnitaryDensity

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

noncomputable def diag (n : ℕ) (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => T.comp (PiLp.proj 2 (fun _ : Fin n => H) j))

@[simp] lemma diag_apply (T : H →L[ℂ] H) (x : PiLp 2 (fun _ : Fin n => H)) (j : Fin n) :
    diag n T x j = T (x j) := rfl

noncomputable def incl (j : Fin n) : H →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)

lemma incl_apply (j : Fin n) (x : H) (i : Fin n) :
    (incl j x : PiLp 2 (fun _ : Fin n => H)) i = (Pi.single j x : Fin n → H) i := rfl

lemma diag_incl (T : H →L[ℂ] H) (j : Fin n) (x : H) :
    diag n T (incl j x) = incl j (T x) := by
  ext i
  simp only [diag_apply, incl_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma sum_incl (x : PiLp 2 (fun _ : Fin n => H)) : ∑ j, incl j (x j) = x := by
  ext i
  simp [incl_apply, Finset.sum_apply]

lemma comm_diag (P : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (c : Fin n → Fin n → ℂ) (hc : ∀ i j x, P (incl j x) i = c i j • x) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) : P (diag n T x) = diag n T (P x) := by
  rw [← sum_incl x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, diag_incl]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext i
  simp [hc]

end IrreducibleUnitaryDensity


open IrreducibleUnitaryDensity in
theorem irreducibleUnitary_density (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)) (hu : ∀ g x, ‖π g x‖ = ‖x‖)
    (hs : ∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) →
      ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H)
    (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)) (h : ∀ g, ∑ j, Λ j (π g (a j)) = 0)
    (φ u : H) : ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := open IrreducibleUnitaryDensity in by
  let a' : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 a
  let S : Submodule ℂ (PiLp 2 (fun _ : Fin n => H)) :=
    Submodule.span ℂ (Set.range fun g => diag n (π g) a')
  let W := S.topologicalClosure
  have hmul : ∀ g g' x, diag n (π g) (diag n (π g') x) = diag n (π (g * g')) x := by
    intro g g' x; ext i; simp
  have hone : ∀ x, diag n (π 1) x = x := by
    intro x; ext i; simp
  have hclos : ∀ (K : Submodule ℂ (PiLp 2 (fun _ : Fin n => H))), IsClosed (K : Set (PiLp 2 (fun _ : Fin n => H))) →
      (∀ g, diag n (π g) a' ∈ K) → W ≤ K := by
    intro K hK hg
    refine Submodule.topologicalClosure_minimal S ?_ hK
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact hg g
  have hgen : ∀ g, diag n (π g) a' ∈ W := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hinv : ∀ g, ∀ x ∈ W, diag n (π g) x ∈ W := by
    intro g x hx
    have := hclos (W.comap (diag n (π g)).toLinearMap)
      (S.isClosed_topologicalClosure.preimage (diag n (π g)).continuous)
      (fun g' => by
        change diag n (π g) (diag n (π g') a') ∈ W
        rw [hmul]; exact hgen _) hx
    exact this
  have hinner : ∀ g (x y : H), ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (π g).toLinearMap (hu g)).inner_map_map x y
  have hinner' : ∀ g x y, ⟪diag n (π g) x, diag n (π g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro g x y
    simp [PiLp.inner_apply, hinner]
  have hinv' : ∀ g, ∀ x ∈ Wᗮ, diag n (π g) x ∈ Wᗮ := by
    intro g x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro w hw
    have h1 : w = diag n (π g) (diag n (π g⁻¹) w) := by rw [hmul, mul_inv_cancel, hone]
    rw [h1, hinner']
    exact hx _ (hinv _ _ hw)
  haveI : CompleteSpace W := S.isClosed_topologicalClosure.completeSpace_coe
  let P := W.starProjection
  have hP : ∀ g x, P (diag n (π g) x) = diag n (π g) (P x) := by
    intro g x
    refine Submodule.eq_starProjection_of_mem_orthogonal (hinv g _ (W.starProjection_apply_mem x)) ?_
    rw [← map_sub]
    exact hinv' g _ (W.sub_starProjection_mem_orthogonal x)
  have hblock : ∀ i j : Fin n, ∃ c : ℂ, ∀ x, P (incl j x) i = c • x := by
    intro i j
    obtain ⟨c, hc⟩ := hs ((PiLp.proj 2 (fun _ : Fin n => H) i).comp (P.comp (incl j))) (by
      intro g
      ext x
      change P (incl j (π g x)) i = π g (P (incl j x) i)
      rw [← diag_incl, hP, diag_apply])
    exact ⟨c, fun x => by simpa using congrArg (fun B : H →L[ℂ] H => B x) hc⟩
  choose c hc using hblock
  let R : H →L[ℂ] H := (innerSL ℂ φ).smulRight u
  have ha : a' ∈ W := hone a' ▸ hgen 1
  have hRa : diag n R a' ∈ W := by
    have h1 : P a' = a' := Submodule.starProjection_eq_self_iff.2 ha
    rw [← h1, ← comm_diag P c hc]
    exact W.starProjection_apply_mem _
  let L : PiLp 2 (fun _ : Fin n => H) →L[ℂ] ℂ :=
    ∑ j, (Λ j).comp (PiLp.proj 2 (fun _ : Fin n => H) j)
  have hL : ∀ x, L x = ∑ j, Λ j (x j) := by
    intro x; simp [L]
  have hker : W ≤ LinearMap.ker L.toLinearMap := by
    refine hclos _ (ContinuousLinearMap.isClosed_ker L) fun g => ?_
    change L _ = 0
    rw [hL]
    exact h g
  have h0 : L (diag n R a') = 0 := hker hRa
  rw [hL] at h0
  simpa [R, a'] using h0

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensityStatement
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleUnitary_vector_density : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H) → ∀ (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)), (∀ g, ∑ j, Λ j (π g (a j)) = 0) → ∀ φ u : H, ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := by
  first | exact @GlobalTheory.irreducibleUnitary_density | exact GlobalTheory.irreducibleUnitary_density | (intros; apply GlobalTheory.irreducibleUnitary_density <;> assumption)
end
end
