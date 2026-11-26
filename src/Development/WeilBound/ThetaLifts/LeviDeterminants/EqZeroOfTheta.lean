module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivariance
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaHeisenbergTranslatesSeparate
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ExistsScaledIntegralLatticeSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowHt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceComponentAdeleNormEqLocalNorm

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

theorem isStd_ne_one (hψ : IsStd ψ) : ψ ≠ 1 := by
  intro h1
  have hn : (Module.finrank ℚ F : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have e := GlobalTheory.PsiNontriv.isStd_fin_rat hψ (algebraMap ℚ F (1 / (2 * Module.finrank ℚ F)))
  rw [h1, AddChar.one_apply, Algebra.trace_algebraMap] at e
  have e2 : (Module.finrank ℚ F • (1 / (2 * (Module.finrank ℚ F : ℚ))) : ℚ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    field_simp
  rw [e2] at e
  have e3 : 2 * (Real.pi : ℂ) * Complex.I * (((1 / 2 : ℚ)) : ℂ) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [e3, Complex.exp_pi_mul_I] at e
  norm_num at e


variable (F) in
def ratPt (y z : κ → F) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

section One

variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}

structure Tw (ψ : AddChar (AF F) ℂ) (d d₁ : Darboux B κ) (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  maps : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ
  Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F κ, e (d.rho ψ w Φ) = d₁.rho ψ w (e Φ)
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ e ∈ (adeleClass F).adm κ
  ne : ∃ Φ ∈ schA F κ, e Φ ≠ 0

def RatRel (d d₁ : Darboux B κ) : Prop := ∀ y z : κ → F, ∃ w y' z', d.e w = ratPt F y z ∧ d₁.e w = ratPt F y' z'

variable {d d₁ d₂ : Darboux B κ} {e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}

theorem rho_mem (hψ : IsStd ψ) (d : Darboux B κ) (w : W) {Φ} (hΦ : Φ ∈ schA F κ) : d.rho ψ w Φ ∈ schA F κ :=
  (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).1 _ Φ hΦ

theorem eq_zero_of_theta (hψ : IsStd ψ) (d : Darboux B κ) {Φ} (hΦ : Φ ∈ schA F κ) (h : ∀ w, thetaSum F (d.rho ψ w Φ) = 0) :
    Φ = 0 :=
  GlobalTheory.T.theta_heisenberg_translates_separate F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 Φ hΦ fun w => by
    obtain ⟨w', rfl⟩ := d.e.surjective w
    exact h w'

theorem rho_smul (d : Darboux B κ) (w : W) (c : ℂ) (Φ : (κ → AF F) → ℂ) : d.rho ψ w (c • Φ) = c • d.rho ψ w Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaSum_smul (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem Tw.theta (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (hr : RatRel d d₁) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := by
  obtain ⟨-, ⟨l, hl0, hl⟩, -⟩ := GlobalTheory.T.theta_distribution_nonzero_admissible F κ
  have hinv := (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).2
  obtain ⟨a, ha⟩ := GlobalTheory.T.admissible_functional_rational_invariance F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 (l ∘ₗ e) (h.adm l hl0) fun w Φ hΦ => by
    obtain ⟨u, y', z', h1, h2⟩ := hr w.1 w.2
    have e1 := h.Heisenberg₂ u Φ hΦ
    rw [Darboux.rho, Darboux.rho, h1, h2] at e1
    have e2 := rho_mem hψ d₁ u (h.maps Φ hΦ)
    rw [Darboux.rho, h2] at e2
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine (congrArg l e1).trans ?_
    rw [hl _ e2, hl _ (h.maps Φ hΦ)]
    exact hinv (y', z') _
  have ha' : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = a * thetaSum F Φ := fun Φ hΦ => by
    rw [← ha Φ hΦ, LinearMap.comp_apply, hl _ (h.maps Φ hΦ)]
  refine ⟨a, fun a0 => ?_, ha'⟩
  obtain ⟨Φ, hΦ, hne⟩ := h.ne
  refine hne (eq_zero_of_theta hψ d₁ (h.maps Φ hΦ) fun w => ?_)
  rw [← h.Heisenberg₂ w Φ hΦ, ha' _ (rho_mem hψ d w hΦ), a0, zero_mul]

theorem Tw.inj (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (hr : RatRel d d₁) {Φ} (hΦ : Φ ∈ schA F κ) (h0 : e Φ = 0) : Φ = 0 := by
  obtain ⟨c, hc, H⟩ := h.theta hψ hr
  refine eq_zero_of_theta hψ d hΦ fun w => ?_
  have := H _ (rho_mem hψ d w hΦ)
  rw [h.Heisenberg₂ w Φ hΦ, h0, ← zero_smul ℂ (0 : (κ → AF F) → ℂ), rho_smul, thetaSum_smul, zero_mul] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hc

theorem schur (hψ : IsStd ψ) (d : Darboux B κ) (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (h1 : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h2 : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (h3 : ∀ w, ∀ Φ ∈ schA F κ, T (d.rho ψ w Φ) = d.rho ψ w (T Φ)) : ∃ a : ℂ, ∀ Φ ∈ schA F κ, T Φ = a • Φ :=
  GlobalTheory.T.heisenberg_commuting_operator_scalar F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 T h1 h2 fun w Φ hΦ => by
    obtain ⟨w', rfl⟩ := d.e.surjective w
    exact h3 w' Φ hΦ

theorem Tw.smul (h : Tw ψ d d₁ e) {c : ℂ} (hc : c ≠ 0) : Tw ψ d d₁ (c • e) := by
  refine
    { maps := fun Φ hΦ => Submodule.smul_mem _ c (h.maps Φ hΦ)
      Heisenberg₂ := ?_
      adm := ?_
      ne := ?_ }
  · intro w Φ hΦ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, h.Heisenberg₂ w Φ hΦ, rho_smul]
  · intro l hl g hg
    obtain ⟨T, hT⟩ := h.adm l hl g hg
    refine ⟨c • T, fun f => ?_⟩
    rw [LinearMap.comp_smul, LinearMap.smul_apply, hT, ContinuousLinearMap.smul_apply]
  ·
    obtain ⟨Φ, hΦ, h0⟩ := h.ne
    exact ⟨Φ, hΦ, smul_ne_zero hc h0⟩

theorem Tw.exists_inv (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (h' : Tw ψ d₁ d e') (hr : RatRel d d₁) (hr' : RatRel d₁ d) :
    ∃ e'', Tw ψ d₁ d e'' ∧ (∀ Φ ∈ schA F κ, e'' (e Φ) = Φ) ∧ ∀ Φ ∈ schA F κ, e (e'' Φ) = Φ := by
  obtain ⟨a, ha⟩ := schur hψ d (e' ∘ₗ e) (fun Φ hΦ => h'.maps _ (h.maps Φ hΦ))
    (fun l hl => h.adm _ (h'.adm l hl)) fun w Φ hΦ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h.Heisenberg₂ w Φ hΦ, h'.Heisenberg₂ w _ (h.maps Φ hΦ)]
  have a0 : a ≠ 0 := fun a0 => by
    obtain ⟨Φ, hΦ, hne⟩ := h.ne
    exact hne (h'.inj hψ hr' (h.maps Φ hΦ) ((ha Φ hΦ).trans (by rw [a0, zero_smul])))
  have h1 : ∀ Φ ∈ schA F κ, (a⁻¹ • e') (e Φ) = Φ := fun Φ hΦ => by
    rw [LinearMap.smul_apply, show e' (e Φ) = a • Φ from ha Φ hΦ, smul_smul, inv_mul_cancel₀ a0, one_smul]
  have h'' := h'.smul (inv_ne_zero a0)
  refine ⟨_, h'', h1, fun Φ hΦ => sub_eq_zero.1 (h''.inj hψ hr' (sub_mem (h.maps _ (h''.maps Φ hΦ)) hΦ) ?_)⟩
  rw [map_sub, h1 _ (h''.maps Φ hΦ), sub_self]

end One

def TwEx : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
  (W : Type) [AddCommGroup W] [Module (AF F) W] (B : W → W → AF F) (d d₁ : Darboux B κ), ∃ e, Tw ψ d d₁ e

theorem schr_box {κ' : Type} [Fintype κ'] (a b : κ → AF F) (a' b' : κ' → AF F) (φ : (κ → AF F) → ℂ) (φ' : (κ' → AF F) → ℂ) :
    schr ψ (Sum.elim a a', Sum.elim b b') (boxFun φ φ') = boxFun (schr ψ (a, b) φ) (schr ψ (a', b') φ') := by
  funext x
  have e1 : (x + Sum.elim a a') ∘ Sum.inl = x ∘ Sum.inl + a := rfl
  have e2 : (x + Sum.elim a a') ∘ Sum.inr = x ∘ Sum.inr + a' := rfl
  have e3 : x ⬝ᵥ Sum.elim b b' + ⅟(2 : AF F) * (Sum.elim a a' ⬝ᵥ Sum.elim b b') =
      (x ∘ Sum.inl ⬝ᵥ b + ⅟(2 : AF F) * (a ⬝ᵥ b)) + (x ∘ Sum.inr ⬝ᵥ b' + ⅟(2 : AF F) * (a' ⬝ᵥ b')) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [schr, boxFun, e1, e2, e3, AddChar.map_add_eq_mul]
  ring

section Dbl

variable {E : Type} [CommRing E] [Algebra (AF F) E] {c : E →ₐ[AF F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
  {dd dd₁ : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)}

end Dbl

end PositivityTheory.ThKF0

end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MCSpan
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.EvAdm

noncomputable section
namespace PositivityTheory.ThKF0.Span
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_invariant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ∀ z ∈ scaledInt F κ a, g (x + z) = g x := by
  obtain ⟨hlc, hcs⟩ := hg
  have hW : ∀ y, {z | g (y + z) = g y} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) := fun y =>
    ((hlc.isOpen_fiber (g y)).preimage (continuous_const.add continuous_id)).mem_nhds (by simp)
  choose b hb hbW using fun y => PositivityTheory.Mix.exists_scaled_integral_lattice_subset F κ _ (hW y)
  have hN : ∀ y ∈ tsupport g, {x | x - y ∈ scaledInt F κ (b y)} ∈ 𝓝 y := fun y _ =>
    ((isOpen_scaledInt (b y)).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  obtain ⟨t, -, ht⟩ := IsCompact.elim_nhds_subcover hcs _ hN
  have hW0 : (⋂ y ∈ t, (scaledInt F κ (b y) : Set (κ → FiniteAdeleRing (𝓞 F) F))) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    (Filter.biInter_finset_mem t).2 fun y _ => (isOpen_scaledInt (b y)).mem_nhds (zero_mem _)
  obtain ⟨a, ha, haW⟩ := PositivityTheory.Mix.exists_scaled_integral_lattice_subset F κ _ hW0
  refine ⟨a, ha, fun x z hz => ?_⟩
  have key : ∀ y ∈ t, x - y ∈ scaledInt F κ (b y) → g (x + z) = g x := fun y hy hxy => by
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    have h1 : g (y + (x - y)) = g y := hbW y hxy
    have h2 : g (y + (x - y + z)) = g y := hbW y (add_mem hxy hz')
    rw [add_sub_cancel] at h1
    rw [show y + (x - y + z) = x + z by abel] at h2
    rw [h1, h2]
  by_cases hx : x ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact key y hy hxy
  by_cases hxz : x + z ∈ tsupport g
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hxz)
    have hz' : z ∈ scaledInt F κ (b y) := Set.mem_iInter₂.1 (haW hz) y hy
    refine key y hy ?_
    have := sub_mem hxy hz'
    rwa [show x + z - y - z = x - y by abel] at this
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxz]

theorem exists_sum_cosets {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
      g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) := _root_.GlobalTheory.EvAdm.exists_sum_cosets (g := g) hg

theorem exists_sum_finprod {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ),
      (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ k, ∀ᶠ v in cofinite, φ k v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i) := by
  obtain ⟨a, ha, R, hR⟩ := exists_sum_cosets hg
  choose φ hSB hstd hφ using fun r : κ → FiniteAdeleRing (𝓞 F) F => GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod F κ a r ha
  let e := R.equivFin
  refine ⟨R.card, fun k => g (e.symm k), fun k => φ (e.symm k), fun k v => hSB _ v, fun k => hstd _, ?_⟩
  have hind : ∀ r, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) =
      fun y => ∏ᶠ v, φ r v fun i => evalV F v (y i) := fun r => funext (hφ r)
  refine hR.trans ?_
  simp only [hind]
  rw [← Finset.sum_coe_sort R]
  exact (Equiv.sum_comp e.symm (fun x : R => g x • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ x v fun i => evalV F v (y i))).symm

theorem comp_mem_adm {κ₁ : Type} [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ₁)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ₁ → Fv F v) → ℂ))
    (hSB : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ₁ → Fv F v))
    (hstd : ∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) :
    ∀ l ∈ (adeleClass F).adm κ₁, l ∘ₗ e ∈ (adeleClass F).adm κ := by
  intro l hl g hg
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := exists_sum_finprod hg
  have hψSB : ∀ k v, ev v (φ k v) ∈ GlobalTheory.WeilM.SB (κ₁ → Fv F v) := fun k v => hSB v _ (hφSB k v)
  have hψstd : ∀ k, ∀ᶠ v in cofinite, ev v (φ k v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun k =>
    ((hφstd k).and hstd).mono fun v h => by rw [h.1, h.2]
  have hg' : ∀ k, (fun y : κ₁ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ := fun k =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV _ (hψSB k) (hψstd k),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod _ (hψSB k) (hψstd k)⟩
  choose T hT using fun k => hl _ (hg' k)
  refine ⟨∑ k, c k • (T k).comp ei, fun f => ?_⟩
  have h1 : pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  have h2 : ∀ k, e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k)) = pureA F (ei f : (κ₁ → mixedEmbedding.mixedSpace F) → ℂ)
      (fun y => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i)) := fun k =>
    hloc f (φ k) (hφSB k) (hφstd k)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, h1, map_sum, map_smul, h2, hT, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]

end PositivityTheory.ThKF0.Span

end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalSupportCommonDenominator
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace PositivityTheory.ThKF0

open Grow

theorem exists_dual_den (F : Type) [Field F] [NumberField F] : ∃ D : ℕ, 1 ≤ D ∧ ∀ ξ : F,
    (∀ y : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (ξ * y) = z) → IsIntegral ℤ ((D : F) * ξ) := by
  refine ⟨(NumberField.discr F).natAbs,
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F)), ?_⟩
  intro ξ hξ
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
  have hdual : ξ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨y, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨z, hz⟩ := hξ y
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply, hz]
    simp
  have hD : ((NumberField.discr F).natAbs : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
    rw [← NumberField.absNorm_differentIdeal F (𝓞 F)]
    exact Ideal.absNorm_mem _
  have hD' : ((NumberField.discr F).natAbs : F) ∈
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, hD, by simp⟩
  rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)] at hD'
  have hmem := FractionalIdeal.mul_mem_mul hD' hdual
  rw [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10)] at hmem
  obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff _).mp hmem
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem trace_int {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : F)
    (h : ψ (0, (algebraMap F (AF F) a).2) = 1) : ∃ z : ℤ, Algebra.trace ℚ F a = z := by
  have e := GlobalTheory.PsiNontriv.isStd_fin_rat hψ a
  have e2 : ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F 0 ((algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) a)) = 1 := h
  rw [e2] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e.symm
  refine ⟨n, ?_⟩
  have hpi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hq : ((Algebra.trace ℚ F a : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hn]
    push_cast
    ring
  exact_mod_cast hq

theorem weil_rep_bounded_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C, -, hC⟩ := htBd F E σ n d X W M
  obtain ⟨m₀, hm₀, h₀⟩ := finInv F _ B.ψ hP.base.std Φ hΦ
  obtain ⟨D, hD, hDD⟩ := exists_dual_den F
  refine ⟨D * m₀ * C, 1, fun g h => ?_⟩
  obtain ⟨m, hm, hmC, hb⟩ := hC g h
  refine ⟨D * (m₀ * m), Nat.mul_pos hD (Nat.mul_pos hm₀ hm), ?_, fun ξ hξ i => ?_⟩
  · push_cast
    rw [pow_one, mul_assoc, mul_assoc]
    gcongr
  · rw [Nat.cast_mul D, mul_assoc]
    refine hDD _ fun y => trace_int hP.base.std _ ?_
    let u : AF F := (0, (algebraMap F (AF F) (y : F)).2)
    have hu : IntF u := ⟨rfl, fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v y⟩
    have h0 : IntF (0 : AF F) := ⟨rfl, fun v => by rw [map_zero]; exact zero_mem _⟩
    have key := congrFun (h₀ _ _ _ _ (impl_sOf hP.weil g h) hb (0, Pi.single i u) ⟨fun _ => h0, fun j => by
      by_cases e : j = i
      · subst e; simpa using hu
      · simpa [e] using h0⟩) fun i => algebraMap F (AF F) (ξ i)
    simp only [schr, Prod.smul_mk, smul_zero, add_zero, Pi.zero_apply, zero_mul, mul_zero, dotProduct_smul,
      dotProduct_single] at key
    rw [← mul_right_cancel₀ hξ (key.trans (one_mul _).symm)]
    refine congrArg B.ψ (Prod.ext ?_ ?_)
    · change (0 : Ainf F) = ((m₀ * m : ℕ) : AF F).1 * ((algebraMap F (AF F) (ξ i)).1 * 0)
      rw [mul_zero, mul_zero]
    · rw [map_mul, map_mul, map_natCast, mul_assoc]
      rfl

end PositivityTheory.ThKF0
end
