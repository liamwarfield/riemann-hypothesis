module

public import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
public import Development.WeilBound.ThetaLifts.FrameEstimates.IntMvPolynomialCoeffAbsSumMulLe

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {d : ℕ} {W : Spc F E d}

def IsLie (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : Spc F E d) (Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ w, (Y w)ᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * (Y w).map star = 0

def Gen (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : Spc F E d) (γ : Multiplicative ℝ →* UA σ W.J)
    (Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ w (t : ℝ), (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y w)


variable (W) in
def UMG (f : UA σ W.J → ℂ) : Prop :=
  ∃ (k : ℕ) (S : Set (UA σ W.J → ℂ)), f ∈ S ∧ ∀ f₁ ∈ S, Continuous f₁ ∧ (∃ C : ℝ, ∀ h, ‖f₁ h‖ ≤ C * (ht h : ℝ) ^ k) ∧
    ∀ γ ∈ Lines σ W, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f₁ (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0


variable (W) in
def SmoothFin (τ : ∀ w : InfinitePlace F, EmbOver E w) (f : UA σ W.J → ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (τ w)) = 1) → ∀ h, f (h * u) = f h

def LeftInv {J : Matrix (Fin d) (Fin d) E} (f : UA σ J → ℂ) : Prop := ∀ γ ∈ ratU σ J, ∀ h, f (γ * h) = f h

def Rapid {J : Matrix (Fin d) (Fin d) E} (f : UA σ J → ℂ) : Prop := ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C

end

def LineGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ γ ∈ Lines σ W, ∃ Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ, IsLie τ W Y ∧ Gen τ W γ Y

def LineEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ, IsLie τ W Y → ∃ γ ∈ Lines σ W, Gen τ W γ Y ∧ ∀ γ' ∈ Lines σ W, Gen τ W γ' Y → γ' = γ

def LinDer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∃ (m : ℕ) (β : Fin m → (Multiplicative ℝ →* UA σ W.J)) (c : Fin m → (InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ), (∀ i, β i ∈ Lines σ W) ∧ ∀ (f : UA σ W.J → ℂ) (f' : Fin m → UA σ W.J → ℂ), (∀ i, Continuous (f' i) ∧ ∀ h, HasDerivAt (fun t : ℝ => f (h * β i (Multiplicative.ofAdd t))) (f' i h) 0) → ∀ γ ∈ Lines σ W, ∀ Y, Gen τ W γ Y → ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ i, (c i Y : ℂ) * f' i h) 0

def UMGSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f : UA σ W.J → ℂ, UMG W f → ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* UA σ W.J)), (∀ i, γ i ∈ Lines σ W) → ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod)

def UMGLin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f f' : UA σ W.J → ℂ, UMG W f → UMG W f' → ∀ a b : ℂ, UMG W (a • f + b • f')

def CuspRapid : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f : UA σ W.J → ℂ, LeftInv f → UMG W f → SmoothFin W τ f → PositivityTheory.ThKEnd.IsCusp W f → Rapid f

def Level : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) → ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = pureA F f φ

def IDer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ 𝓕, Dom M om 𝓕 → ∀ φ ∈ 𝓕, φ ∈ SB _ → ∀ f ∈ M.Pol B.ψ B.emb, (∀ γ ∈ Lines σ W, ∃ f₁ ∈ M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ h, HasDerivAt (fun t : ℝ => M.I om (pureA F f φ) (h * γ (Multiplicative.ofAdd t))) (M.I om (pureA F f₁ φ) h) 0) ∧ ∀ γ ∈ Lines σ X, ∃ f₁ ∈ M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ ∧ M.I om (pureA F f₁ φ) = 0

def IInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), LeftInv (M.I om Φ) ∧ (∀ g, M.I om (om (g, 1) Φ) = M.I om Φ) ∧ ∀ h h', M.I om (om (1, h') Φ) h = M.I om Φ (h * h')

def IUMG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ 𝓕, Dom M om 𝓕 → ∀ φ ∈ 𝓕, φ ∈ SB _ → ∀ f ∈ M.Pol B.ψ B.emb, UMG W (M.I om (pureA F f φ)) ∧ SmoothFin W B.emb (M.I om (pureA F f φ))

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LatSumRedH
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ht_mul_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : ht (g * h) ≤ ht g * ht h :=
  heightGL_mul_le F g.1 h.1

theorem ht_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : ht g⁻¹ = ht g := heightGL_inv F g.1

theorem one_le_ht {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : 1 ≤ ht g := one_le_heightGL F g.1

theorem exp_le_ht (hT : GrpTop) (hc : IsCMExt F E σ) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : EpsHerm σ J)
    {fr : Frame σ J} (h2 : TorHt fr) {Ω : Set (UA σ J)} (hΩ : IsCompact Ω) :
    ∃ (A : ℝ) (k : ℕ), 0 ≤ A ∧ ∀ h : UA σ J, ∀ δ ∈ ratU σ J, ∀ t ∈ Cone fr.r, ∀ κ ∈ Ω, δ * h = fr.a t * κ →
      Real.exp (∑ i, t i) ≤ A * (ht h : ℝ) ^ k := by
  obtain ⟨C, k, hC⟩ := h2
  obtain ⟨B, hB⟩ := (hT F E σ hc d J hJ).2.2.2.2.2.2.2 Ω hΩ
  refine ⟨max C 0 * (B : ℝ) ^ k, k, by positivity, fun h δ hδ t ht' κ hκ e => ?_⟩
  have e2 : δ⁻¹ * fr.a t = h * κ⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, e, mul_inv_cancel_right]
  have h3 := (hC t ht').2 δ⁻¹ (inv_mem hδ)
  rw [e2] at h3
  have h4 : (ht (h * κ⁻¹) : ℝ) ≤ B * ht h := by
    have hb : ht κ⁻¹ ≤ B := by rw [ht_inv]; exact hB κ hκ
    have := (ht_mul_le h κ⁻¹).trans (mul_le_mul_right hb _)
    rw [mul_comm] at this
    exact_mod_cast this
  calc _ ≤ C * (ht (h * κ⁻¹) : ℝ) ^ k := h3
    _ ≤ max C 0 * ((B : ℝ) * ht h) ^ k := by gcongr; exact le_max_left _ _
    _ = _ := by rw [mul_pow, mul_assoc]

theorem latSum_redH (hT : GrpTop) (hS : SiegelAll) (hI : LatInv) (hK : LatCpt) (hA : LatArch) (hc : IsCMExt F E σ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    (hJ : EpsHerm σ J) (hJ' : EpsHerm σ J') (N : ℕ) :
    ∃ k : ℕ, ∀ C, IsCompact C → ∃ (C' : Set (Ten F E n d)) (K : ℝ), IsCompact C' ∧ 0 ≤ K ∧ ∀ (g : UA σ J) (h : UA σ J'),
      latSum τ C N Set.univ g h ≤ ENNReal.ofReal ((K * (ht h : ℝ) ^ k) ^ 2) * latSum τ C' N Set.univ g (1 : UA σ J') := by
  obtain ⟨fr, hg, -, ⟨Ω, hΩ, hcov⟩, -, hht⟩ := hS F E σ hc d J' hJ'
  obtain ⟨A, k, hA0, hAk⟩ := exp_le_ht hT hc hJ' hht hΩ
  refine ⟨k * N, fun C hC => ?_⟩
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc τ n d J J' hJ hJ' {1} Ω isCompact_singleton hΩ C N hC
  obtain ⟨C₂, K₂, hC₂, h₂⟩ := hA F E σ hc τ n d J J' hJ hJ' fr hg C₁ N hC₁
  refine ⟨C₂, K₁ * K₂ * A ^ N + 1, hC₂, by positivity, fun g h => ?_⟩
  obtain ⟨δ, hδ, t, ht', κ, hκ, e⟩ := hcov h
  have e1 := hI F E σ hc τ n d J J' hJ hJ' C N Set.univ (by simp) 1 (one_mem _) δ hδ g h
  rw [← e1, e, one_mul]
  have e2 := h₁ Set.univ g (fr.a t) 1 rfl κ hκ
  rw [mul_one] at e2
  refine e2.trans ((mul_le_mul_right (h₂ Set.univ g t ht') _).trans ?_)
  rw [← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : (1 : ℝ) ≤ (ht h : ℝ) ^ (k * N) := one_le_pow₀ (by exact_mod_cast one_le_ht h)
  have h3 : Real.exp (N * ∑ j, t j) ≤ A ^ N * (ht h : ℝ) ^ (k * N) := by
    rw [Real.exp_nat_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (hAk h δ hδ t ht' κ hκ e) _
  have h4 : (0 : ℝ) ≤ K₁ * K₂ * A ^ N := by positivity
  have h5 : (1 : ℝ) ≤ (K₁ * K₂ * A ^ N + 1) * (ht h : ℝ) ^ (k * N) := by nlinarith
  calc (K₁ : ℝ) * K₂ * Real.exp (N * ∑ j, t j) ≤ K₁ * K₂ * (A ^ N * (ht h : ℝ) ^ (k * N)) := by gcongr
    _ ≤ (K₁ * K₂ * A ^ N + 1) * (ht h : ℝ) ^ (k * N) := by nlinarith
    _ ≤ _ := by nlinarith

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.SqAllC
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem sq_alg_inj : Function.Injective (algebraMap F (AF F)) := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F

theorem sq_inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E) sq_alg_inj

theorem exists_ratEquiv (hp : IsPair B M χX χW om r s r' s') :
    ∃ e : Matrix (Fin n) (Fin d) E ≃ (Fin n × Fin d → F) × (Fin n × Fin d → F), ∀ x,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) ((e x).1 i), fun i => algebraMap F (AF F) ((e x).2 i)) := by
  choose y z hyz using hp.good.rat
  have hadd : ∀ a b : Matrix (Fin n) (Fin d) E, incM F (a + b) = incM F a + incM F b := fun a b =>
    Matrix.ext fun i j => map_add (inclR (F := F) (AF F)) _ _
  have hsm : ∀ (c : F) (a : Matrix (Fin n) (Fin d) E), incM F (c • a) = algebraMap F (AF F) c • incM F a := fun c a =>
    Matrix.ext fun i j => by
      change (1 : AF F) ⊗ₜ[F] (c • a i j) = algebraMap F (AF F) c • ((1 : AF F) ⊗ₜ[F] a i j)
      rw [TensorProduct.tmul_smul, algebraMap_smul]
  let l : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => by
        have h := hyz (a + b)
        rw [hadd, map_add (f := _), hyz a, hyz b] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_add _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_add _ _ _).symm
      map_smul' := fun c a => by
        have h := hyz (c • a)
        rw [hsm, map_smul, hyz a] at h
        refine Prod.ext (funext fun i => sq_alg_inj ?_) (funext fun i => sq_alg_inj ?_)
        · exact (congrFun (congrArg Prod.fst h) i).symm.trans (map_mul _ _ _).symm
        · exact (congrFun (congrArg Prod.snd h) i).symm.trans (map_mul _ _ _).symm }
  have hinj : Function.Injective l := fun a b hab => by
    have h1 : y a = y b := congrArg Prod.fst hab
    have h2 : z a = z b := congrArg Prod.snd hab
    have h3 : incM F a = incM F b := M.co.e.injective (by rw [hyz a, hyz b, h1, h2])
    exact Matrix.ext fun i j => sq_inclR_inj (congrFun (congrFun h3 i) j)
  have h2 : Module.finrank F E = 2 := hp.base.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hdim : Module.finrank F (Matrix (Fin n) (Fin d) E) =
      Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) := by
    rw [Module.finrank_matrix, h2]
    simp
    ring
  exact ⟨Equiv.ofBijective l ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩, hyz⟩

theorem theta_mul_le (hS : CoefSum) (hE : CoefEq) (hp : IsPair B M χX χW om r s r' s') (μ : Measure (Fin n × Fin d → AF F))
    (hμ : μ.IsAddHaarMeasure) : ∃ c : ℝ, 0 < c ∧ ∀ Φ₁ ∈ schA F (Fin n × Fin d), ∀ Φ₂ ∈ schA F (Fin n × Fin d), ∀ g h,
      ‖theta om Φ₁ g h‖ₑ * ‖theta om Φ₂ g h‖ₑ ≤ ENNReal.ofReal c * ∑' x : Matrix (Fin n) (Fin d) E,
        ‖coef F B.ψ μ Φ₁ Φ₂ (M.co.e (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ))‖ₑ := by
  obtain ⟨c, hc, h1⟩ := hS F _ B.ψ hp.base.std μ hμ
  obtain ⟨e, he⟩ := exists_ratEquiv hp
  refine ⟨c, hc, fun Φ₁ h₁ Φ₂ h₂ g h => ?_⟩
  have hs := (IsUWeilPair.isUSplitting hp.weil).pres (g, h)
  refine (h1 _ (hs _ h₁) _ (hs _ h₂)).trans (le_of_eq ?_)
  rw [← e.tsum_eq]
  congr 1
  refine tsum_congr fun x => ?_
  rw [← he x, hE F E σ B n d X W M χX χW om r s r' s' hp μ hμ Φ₁ h₁ Φ₂ h₂ g h]

theorem sq_maj_nonneg (τ : ∀ w : InfinitePlace F, EmbOver E w) (C : Set (Ten F E n d)) (N : ℕ) (z : Ten F E n d) :
    0 ≤ maj τ C N z := by
  unfold maj sz
  split_ifs
  · positivity
  · exact le_rfl

theorem sq_le_of_coef {c a : ℝ} (hc : 0 < c) (ha : 0 ≤ a) {t : ℝ≥0∞} {S : Set (Matrix (Fin n) (Fin d) E)}
    {u : Matrix (Fin n) (Fin d) E → ℂ} {C : Set (Ten F E n d)} {N : ℕ} {g : UA σ X.J} {h : UA σ W.J}
    (h1 : t * t ≤ ENNReal.ofReal c * ∑' x, ‖u x‖ₑ) (h0 : ∀ x ∉ S, u x = 0)
    (h2 : ∀ x, ‖u x‖ ≤ a * a * maj B.emb C N (mat g⁻¹ * incM F x * (mat h⁻¹)ᵀ)) :
    t ^ 2 ≤ ENNReal.ofReal (√c * a) ^ 2 * latSum B.emb C N S g h := by
  rw [sq]
  refine h1.trans ?_
  have e : ∑' x, ‖u x‖ₑ = ∑' x : S, ‖u x.1‖ₑ := by
    refine (tsum_subtype_eq_of_support_subset (f := fun x => ‖u x‖ₑ) fun x hx => ?_).symm
    by_contra hn
    exact hx (by simp [h0 x hn])
  rw [e, ← ENNReal.ofReal_pow (by positivity), mul_pow, Real.sq_sqrt hc.le, ENNReal.ofReal_mul hc.le, mul_assoc, latSum]
  refine mul_le_mul_right ?_ _
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), sq]
  exact ENNReal.ofReal_le_ofReal (h2 x.1)

end

theorem sqAll_of' (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) : SqAll := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨c, hc, h1⟩ := theta_mul_le hS hE hp μ hμ
  obtain ⟨p, C, hpc, hC, h2⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ N
  refine ⟨NNReal.mk √c (Real.sqrt_nonneg c) • p, C, (continuous_const.mul hpc : Continuous fun f => √c * p f), hC,
    fun f g h => ?_⟩
  have hm : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  exact sq_le_of_coef hc (apply_nonneg p f) (h1 _ hm _ hm g h) (fun x hx => absurd (Set.mem_univ x) hx) fun x => h2 f f _

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.ExistsColsDetNeZero
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_cols_det_ne_zero {K : Type} [Field K] {i d : ℕ} (A : Matrix (Fin i) (Fin d) K)
    (hA : LinearIndependent K A.row) : ∃ c : Fin i → Fin d, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.col
  haveI : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = i := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hA.rank_matrix, Fintype.card_fin]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  have hu : IsUnit (A.submatrix id (a ∘ e)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

theorem exists_one_le_emb {x : E} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) : ∃ φ : E →+* ℂ, 1 ≤ ‖φ x‖ := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace E, 1 ≤ w x := by
    by_contra hne
    push Not at hne
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact absurd (InfinitePlace.one_le_of_lt_one (w := w) (a := (⟨x, hx⟩ : 𝓞 E))
      (fun h => h0 (congrArg Subtype.val h)) fun z _ => hne z) (not_le.2 (hne w))
  exact ⟨w.embedding, by rwa [InfinitePlace.norm_embedding_eq]⟩

theorem sum_lam_le_psum {d y : ℕ} {lam : Fin d → (Fin y → ℝ) →ₗ[ℝ] ℝ} {jx jy : Fin y ↪ Fin d} (h1 : ∀ i j, jx i ≠ jy j)
    (h2 : ∀ i t, lam (jx i) t = t i ∧ lam (jy i) t = -t i) (h3 : ∀ k, (∀ i, jx i ≠ k ∧ jy i ≠ k) → lam k = 0)
    {t : Fin y → ℝ} (ht : t ∈ Cone y) {i : ℕ} {c : Fin i → Fin d} (hc : Function.Injective c) :
    ∑ a, lam (c a) t ≤ psum t i := by
  classical
  have key : ∀ θ : ℝ, 0 ≤ θ → ∑ a, lam (c a) t ≤ ∑ j, max 0 (t j - θ) + i * θ := by
    intro θ hθ
    have e := sum_lam h1 h2 h3 (fun u => max 0 (u - θ)) t
    have e1 : ∀ j, max 0 (-t j - θ) = 0 := fun j => max_eq_left (by linarith [ht.2 j])
    simp only [e1, max_eq_left (show 0 - θ ≤ 0 by linarith), Finset.sum_const_zero, add_zero, mul_zero] at e
    rw [← e]
    have e2 : ∑ a, max 0 (lam (c a) t - θ) ≤ ∑ k, max 0 (lam k t - θ) := by
      exact (Finset.sum_map Finset.univ ⟨c, hc⟩ fun k => max 0 (lam k t - θ)).symm.trans_le
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => le_max_left _ _)
    have e3 : ∑ a, lam (c a) t ≤ ∑ a, (max 0 (lam (c a) t - θ) + θ) :=
      Finset.sum_le_sum fun a _ => by linarith [le_max_right 0 (lam (c a) t - θ)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e3
    linarith
  by_cases hi : i < y
  · refine (key (t ⟨i, hi⟩) (ht.2 _)).trans (le_of_eq ?_)
    have e : ∀ j : Fin y, max 0 (t j - t ⟨i, hi⟩) =
        (if j.val < i then t j else 0) - if j.val < i then t ⟨i, hi⟩ else 0 := by
      intro j
      split_ifs with h
      · exact max_eq_right (sub_nonneg.2 (ht.1 (show j ≤ ⟨i, hi⟩ from h.le)))
      · rw [sub_zero]
        exact max_eq_left (sub_nonpos.2 (ht.1 (show (⟨i, hi⟩ : Fin y) ≤ j from not_lt.1 h)))
    have hcard : (Finset.univ.filter fun j : Fin y => j.val < i).card = i := by
      rw [Fin.card_filter_val_lt]
      omega
    simp only [e, Finset.sum_sub_distrib]
    rw [← Finset.sum_filter (fun j : Fin y => j.val < i) fun _ => t ⟨i, hi⟩, Finset.sum_const, hcard, nsmul_eq_mul, psum]
    ring
  · refine (key 0 le_rfl).trans (le_of_eq ?_)
    rw [mul_zero, add_zero, psum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos (by omega), sub_zero, max_eq_right (ht.2 j)]

theorem psum_eq {q i : ℕ} (hi : i ≤ q) (s : Fin q → ℝ) : psum s i = ∑ a : Fin i, s (Fin.castLE hi a) := by
  exact (Fintype.sum_of_injective _ (Fin.castLE_injective hi) _ (fun j : Fin q => if j.val < i then s j else 0)
    (fun j hj => if_neg fun h => hj ⟨⟨j, h⟩, rfl⟩) fun a => (if_pos a.2).symm).symm

theorem minor_of : FrameBasis → Minor := by
  intro hB F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  classical
  obtain ⟨b, lam, ix, iy, h1, h2, h3, -, hb⟩ := hB F E σ hσ n J hJ fr hfr
  obtain ⟨b', lam', jx, jy, h1', h2', h3', -, hb'⟩ := hB F E σ hσ d J' hJ' fr' hfr'
  obtain ⟨m, K, hm, hK, h⟩ := diag_coords τ hfr hfr' hb hb' hC
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast n.factorial_pos
  set A : ℝ := n.factorial * m * K with hA
  have hA1 : 1 ≤ A := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hm') hK
  refine ⟨A⁻¹, by positivity, fun s hs t ht x hx hsupp => ?_⟩
  obtain ⟨ha, hsz⟩ := h s t x
  have hint := ha hsupp
  have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ)
  set z := sz τ (mat (fr.a s)⁻¹ * incM F x * (mat (fr'.a t)⁻¹)ᵀ)
  set ξ := (b⁻¹).1 * x * (b'⁻¹).1ᵀ with hξ
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin (fr.r + 1) => psum s i.val - psum t i.val)
  have hiq : i.val ≤ fr.r := Nat.lt_succ_iff.1 i.2
  have hqn : fr.r ≤ n := by simpa using Fintype.card_le_of_embedding iy
  have hrk : ξ.rank = n := by
    rw [hξ, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by
      rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _))]
    exact hx
  have hli : LinearIndependent E ξ.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← Matrix.rank_eq_finrank_span_row, hrk,
      Fintype.card_fin]
  let ρ : Fin i.val → Fin n := fun a => iy (Fin.castLE hiq a)
  obtain ⟨c, hc, hdet⟩ := exists_cols_det_ne_zero (ξ.submatrix ρ id)
    (hli.comp ρ (iy.injective.comp (Fin.castLE_injective hiq)))
  set M : Matrix (Fin i.val) (Fin i.val) E := (ξ.submatrix ρ id).submatrix id c with hM
  have hI : IsIntegral ℤ ((m : E) • M).det := IsIntegral.det fun a a' => hint _ _
  have hI0 : ((m : E) • M).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hm.ne')) hdet
  obtain ⟨φ, hφ⟩ := exists_one_le_emb hI hI0
  obtain ⟨w, hw⟩ := norm_emb hσ τ φ
  rw [hw, Matrix.det_smul, map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast,
    Fintype.card_fin] at hφ
  let N : Matrix (Fin i.val) (Fin i.val) ℂ := Matrix.of fun a a' =>
    (Real.exp (s (Fin.castLE hiq a)) : ℂ) * ((Real.exp (-lam' (c a') t) : ℂ) * (τ w).1 (M a a'))
  have hN : ‖N.det‖ = Real.exp (psum s i - ∑ a, lam' (c a) t) * ‖(τ w).1 M.det‖ := by
    have e1 : N.det = (∏ a, (Real.exp (s (Fin.castLE hiq a)) : ℂ)) * ((∏ a, (Real.exp (-lam' (c a) t) : ℂ)) *
        (τ w).1 M.det) := by
      rw [RingHom.map_det, ← Matrix.det_mul_row, ← Matrix.det_mul_column]
      rfl
    rw [e1, ← Complex.ofReal_prod, ← Complex.ofReal_prod, ← Real.exp_sum, ← Real.exp_sum, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add, psum_eq hiq, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have hent : ∀ a a', ‖N a a'‖ ≤ K * (1 + z) := by
    intro a a'
    let T : InfinitePlace F → Fin n → Fin d → ℝ := fun w k l => Real.exp (-(lam k s + lam' l t)) * ‖(τ w).1 (ξ k l)‖
    have hT : ∀ w k l, 0 ≤ T w k l := fun w k l => by positivity
    have e : ‖N a a'‖ = T w (ρ a) (c a') := by
      simp only [N, T, ρ, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        (h2 _ _).2, neg_add, neg_neg, Real.exp_add, mul_assoc]
      rfl
    have l1 := Finset.single_le_sum (f := T w (ρ a)) (fun _ _ => hT _ _ _) (Finset.mem_univ (c a'))
    have l2 := Finset.single_le_sum (f := fun k => ∑ l, T w k l)
      (fun _ _ => Finset.sum_nonneg fun _ _ => hT _ _ _) (Finset.mem_univ (ρ a))
    have l3 := Finset.single_le_sum (f := fun w => ∑ k, ∑ l, T w k l)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hT _ _ _) (Finset.mem_univ w)
    have l4 : ∑ w, ∑ k, ∑ l, T w k l ≤ K * z := hsz
    linarith
  have hdle : ‖N.det‖ ≤ i.val.factorial * (K * (1 + z)) ^ i.val := by
    have := Matrix.det_le (A := N) (abv := NormedField.toAbsoluteValue ℂ) (x := K * (1 + z)) hent
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hv : Real.exp (viol s t) ≤ (A * (1 + z)) ^ (n + 1) := by
    have e1 : Real.exp (viol s t) ≤ Real.exp (psum s i - ∑ a, lam' (c a) t) := by
      rw [viol, ← hi]
      exact Real.exp_le_exp.2 (by linarith [sum_lam_le_psum h1' h2' h3' ht hc])
    have hin : i.val ≤ n := hiq.trans hqn
    have e2 : (i.val.factorial : ℝ) ≤ (n.factorial : ℝ) ^ (n + 1) :=
      le_trans (by exact_mod_cast Nat.factorial_le hin) (le_self_pow₀ hf (by omega))
    have hB1 : 1 ≤ (m : ℝ) * (K * (1 + z)) :=
      one_le_mul_of_one_le_of_one_le hm' (one_le_mul_of_one_le_of_one_le hK (by linarith))
    calc _ ≤ Real.exp (psum s i - ∑ a, lam' (c a) t) * ((m : ℝ) ^ i.val * ‖(τ w).1 M.det‖) :=
          e1.trans (le_mul_of_one_le_right (Real.exp_pos _).le hφ)
      _ = (m : ℝ) ^ i.val * ‖N.det‖ := by rw [hN]; ring
      _ ≤ (m : ℝ) ^ i.val * (i.val.factorial * (K * (1 + z)) ^ i.val) := by gcongr
      _ = i.val.factorial * ((m : ℝ) * (K * (1 + z))) ^ i.val := by rw [mul_pow (m : ℝ)]; ring
      _ ≤ (n.factorial : ℝ) ^ (n + 1) * ((m : ℝ) * (K * (1 + z))) ^ (n + 1) :=
          mul_le_mul e2 (pow_le_pow_right₀ hB1 (by omega)) (by positivity) (by positivity)
      _ = _ := by rw [← mul_pow, hA]; congr 1; ring
  rw [inv_mul_le_iff₀ (by positivity)]
  refine le_of_pow_le_pow_left₀ (n := n + 1) (by omega) (by positivity) ?_
  rw [← Real.exp_nat_mul, show ((n + 1 : ℕ) : ℝ) * (viol s t / (n + 1)) = viol s t by push_cast; field_simp]
  exact hv

end PositivityTheory.ThKEst

end
end

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LatTor
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sum_pos_lam {n d q y : ℕ} {lam : Fin n → (Fin q → ℝ) →ₗ[ℝ] ℝ} {ix iy : Fin q ↪ Fin n} (h1 : ∀ i j, ix i ≠ iy j)
    (h2 : ∀ i t, lam (ix i) t = t i ∧ lam (iy i) t = -t i) (h3 : ∀ k, (∀ i, ix i ≠ k ∧ iy i ≠ k) → lam k = 0)
    {lam' : Fin d → (Fin y → ℝ) →ₗ[ℝ] ℝ} {jx jy : Fin y ↪ Fin d} (h1' : ∀ i j, jx i ≠ jy j)
    (h2' : ∀ i t, lam' (jx i) t = t i ∧ lam' (jy i) t = -t i) (h3' : ∀ k, (∀ i, jx i ≠ k ∧ jy i ≠ k) → lam' k = 0)
    {s : Fin q → ℝ} {t : Fin y → ℝ} (hs : s ∈ Cone q) (ht : t ∈ Cone y) :
    ∑ k, ∑ l, max 0 (lam k s + lam' l t) = posWt n d s t := by
  let G : ℝ → ℝ := fun u => ∑ l, max 0 (u + lam' l t)
  have hG : ∀ u, G u = ∑ j, max 0 (u + t j) + ∑ j, max 0 (u + -t j) + ((d : ℝ) - 2 * y) * max 0 (u + 0) := fun u =>
    sum_lam h1' h2' h3' (fun v => max 0 (u + v)) t
  have h0 : G 0 = ∑ j, t j := by
    rw [hG]
    have a : ∀ j, max 0 (0 + t j) = t j := fun j => by rw [zero_add, max_eq_right (ht.2 j)]
    have b : ∀ j, max 0 (0 + -t j) = 0 := fun j => by rw [zero_add, max_eq_left (by linarith [ht.2 j])]
    simp only [a, b]
    simp
  have hs' : ∀ i, G (s i) + G (-s i) = ∑ j, 2 * max (s i) (t j) + ((d : ℝ) - 2 * y) * s i := by
    intro i
    have a : ∀ j, 2 * max (s i) (t j) =
        max 0 (s i + t j) + max 0 (s i + -t j) + (max 0 (-s i + t j) + max 0 (-s i + -t j)) := by
      intro j
      have := hs.2 i
      have := ht.2 j
      simp only [max_def]
      split_ifs <;> linarith
    rw [hG, hG, add_zero, add_zero, max_eq_right (hs.2 i), max_eq_left (by linarith [hs.2 i] : -s i ≤ 0)]
    simp only [a, Finset.sum_add_distrib]
    ring
  have := sum_lam h1 h2 h3 G s
  rw [← Finset.sum_add_distrib, h0] at this
  simp only [hs', Finset.sum_add_distrib, ← Finset.mul_sum] at this
  refine this.trans ?_
  simp only [posWt, ← Finset.mul_sum]

theorem tsum_fin_prod {α : Type} (q : ℕ) (φ : Fin q → α → ℝ≥0∞) :
    ∑' x : Fin q → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← (Fin.consEquiv fun _ : Fin (q + 1) => α).tsum_eq, ENNReal.tsum_prod', Fin.prod_univ_succ, ← ih,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [Fin.prod_univ_succ]
    rfl

theorem tsum_fun_prod {ι α : Type} [Fintype ι] (φ : ι → α → ℝ≥0∞) :
    ∑' x : ι → α, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  let e := (Fintype.equivFin ι).symm
  rw [← e.prod_comp, ← tsum_fin_prod, ← (e.arrowCongr (Equiv.refl α)).tsum_eq]
  refine tsum_congr fun x => ?_
  rw [← e.prod_comp]
  simp

def oneMaj (τ : ∀ w : InfinitePlace F, EmbOver E w) (m N : ℕ) (ν : ℝ) : E → ℝ≥0∞ :=
  Set.indicator {x | IsIntegral ℤ ((m : E) * x)} fun x =>
    ENNReal.ofReal (((1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x‖) ^ N)⁻¹)

theorem tsum_oneMaj (hO : OneVar) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ≥0, ∀ ν, ∑' x, oneMaj τ m (Module.finrank ℚ E + 1) ν x ≤
      K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν)) := by
  classical
  obtain ⟨K, hK⟩ := hO (mixedEmbedding.mixedSpace E) (mixedEmbedding.integerLattice E) (Module.finrank ℚ E + 1)
    (by rw [mixedEmbedding.finrank]; omega)
  rw [mixedEmbedding.finrank] at hK
  set N := Module.finrank ℚ E + 1
  refine ⟨(m : ℝ≥0) ^ N * K, fun ν => ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let i : {x : E | IsIntegral ℤ ((m : E) * x)} → mixedEmbedding.integerLattice E := fun x =>
    ⟨mixedEmbedding E (m * x.1), ⟨⟨_, x.2⟩, rfl⟩⟩
  have hi : Function.Injective i := fun x y hxy => by
    have := (mixedEmbedding E).injective (congrArg Subtype.val hxy)
    exact Subtype.ext (mul_left_cancel₀ (by exact_mod_cast hm.ne') this)
  have hn : ∀ x : E, ‖mixedEmbedding E x‖ ≤ ∑ w, ‖(τ w).1 x‖ := by
    intro x
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun v _ => ?_
    obtain ⟨w, hw⟩ := norm_emb h τ v.embedding
    rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_eq, hw]
    exact Finset.single_le_sum (f := fun w => ‖(τ w).1 x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  rw [oneMaj, ← tsum_subtype]
  calc _ ≤ ∑' x : {x : E | IsIntegral ℤ ((m : E) * x)}, ((m : ℝ≥0) ^ N : ℝ≥0) *
          ENNReal.ofReal (((1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖) ^ N)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hS : 0 ≤ ∑ w, ‖(τ w).1 x.1‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have h1 : ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤ m * ∑ w, ‖(τ w).1 x.1‖ := by
          refine (hn _).trans (le_of_eq ?_)
          simp [Finset.mul_sum]
        have h2 : 1 + Real.exp (-ν) * ‖(i x : mixedEmbedding.mixedSpace E)‖ ≤
            m * (1 + Real.exp (-ν) * ∑ w, ‖(τ w).1 x.1‖) := by
          have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-ν)).le
          linarith
        have h3 := pow_le_pow_left₀ (by positivity) h2 N
        rw [mul_pow] at h3
        push_cast
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
        exact h3.trans_eq (mul_comm _ _)
    _ ≤ ((m : ℝ≥0) ^ N : ℝ≥0) * (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * max 0 ν))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi _).trans (hK ν)
    _ = _ := by rw [ENNReal.coe_mul, mul_assoc]

theorem latTor_of : FrameBasis → OneVar → LatTor := by
  intro hB hO F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  classical
  obtain ⟨b, lam, ix, iy, h1, h2, h3, -, hb⟩ := hB F E σ hσ n J hJ fr hfr
  obtain ⟨b', lam', jx, jy, h1', h2', h3', -, hb'⟩ := hB F E σ hσ d J' hJ' fr' hfr'
  set N₀ := Module.finrank ℚ E + 1 with hN₀
  set c := Fintype.card (Fin n × Fin d) with hc
  refine ⟨N₀ * c, fun C hC => ?_⟩
  obtain ⟨m, K, hm, hK, h⟩ := diag_coords τ hfr hfr' hb hb' hC
  obtain ⟨K₁, hK₁⟩ := tsum_oneMaj hO hσ τ hm
  refine ⟨K.toNNReal ^ (N₀ * c) * K₁ ^ c, fun s hs t ht => ?_⟩
  let i : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → (Fin n × Fin d → E) := fun x p =>
    ((b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ) p.1 p.2
  have hi : Function.Injective i := fun x y hxy => by
    have e : (b⁻¹).1 * x.1 * (b'⁻¹).1ᵀ = (b⁻¹).1 * y.1 * (b'⁻¹).1ᵀ := by
      ext k l
      exact congrFun hxy (k, l)
    have e' : ∀ z : Matrix (Fin n) (Fin d) E, b.1 * ((b⁻¹).1 * z * (b'⁻¹).1ᵀ) * b'.1ᵀ = z := by
      intro z
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]
    exact Subtype.ext (by rw [← e' x.1, e, e'])
  let g : (Fin n × Fin d → E) → ℝ≥0∞ := fun ξ => ∏ p, oneMaj τ m N₀ (lam p.1 s + lam' p.2 t) (ξ p)
  calc _ ≤ ∑' x, (K.toNNReal ^ (N₀ * c) : ℝ≥0) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        obtain ⟨ha, hb⟩ := h s t x.1
        unfold maj
        split_ifs with hx
        swap
        · simp
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        set z := sz τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        let A : Fin n × Fin d → ℝ := fun p => Real.exp (-(lam p.1 s + lam' p.2 t)) * ∑ w, ‖(τ w).1 (i x p)‖
        have hA0 : ∀ p, 0 ≤ A p := fun p => by positivity
        have hA : ∀ p, 1 + A p ≤ K * (1 + z) := fun p => by
          have : ∑ p, A p ≤ K * z := by
            refine le_trans (le_of_eq ?_) hb
            rw [Fintype.sum_prod_type, Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace F)))]
            exact Finset.sum_congr rfl fun l _ => Finset.mul_sum _ _ _
          have h4 := Finset.single_le_sum (f := A) (fun p _ => hA0 p) (Finset.mem_univ p)
          linarith
        have hg : g (i x) = ENNReal.ofReal (∏ p, (1 + A p) ^ N₀)⁻¹ := by
          rw [← Finset.prod_inv_distrib, ENNReal.ofReal_prod_of_nonneg fun p _ => by have := hA0 p; positivity]
          exact Finset.prod_congr rfl fun p _ =>
            Set.indicator_of_mem (s := {x | IsIntegral ℤ ((m : E) * x)}) (a := i x p) (ha hx p.1 p.2) _
        have h5 : ∏ p, (1 + A p) ^ N₀ ≤ (K * (1 + z)) ^ (N₀ * c) := by
          rw [pow_mul, hc, ← Finset.card_univ, ← Finset.prod_const]
          exact Finset.prod_le_prod₀ (fun p _ => by have := hA0 p; positivity)
            fun p _ => pow_le_pow_left₀ (by have := hA0 p; positivity) (hA p) _
        have h6 : 0 < ∏ p, (1 + A p) ^ N₀ := Finset.prod_pos fun p _ => by have := hA0 p; positivity
        rw [hg, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        rw [Real.coe_toNNReal _ (by linarith), ← div_eq_mul_inv, le_div_iff₀ h6, inv_mul_le_iff₀ (by positivity),
          ← mul_pow]
        exact h5.trans_eq (by rw [mul_comm K])
    _ ≤ (K.toNNReal ^ (N₀ * c) : ℝ≥0) * ∏ p : Fin n × Fin d, (K₁ * ENNReal.ofReal
          (Real.exp (Module.finrank ℚ E * max 0 (lam p.1 s + lam' p.2 t)))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        refine (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans ?_
        rw [tsum_fun_prod]
        exact Finset.prod_le_prod' fun p _ => hK₁ _
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hc,
          ← ENNReal.ofReal_prod_of_nonneg fun p _ => (Real.exp_pos _).le, ← Real.exp_sum, ← Finset.mul_sum,
          Fintype.sum_prod_type, sum_pos_lam h1 h2 h3 h1' h2' h3' hs ht]
        push_cast
        rw [mul_assoc]

end PositivityTheory.ThKEst

end
end
