module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDual
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.HeisenbergCommutingOperatorScalar
public import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.SoDefs
noncomputable section

namespace PositivityTheory.ThKCT

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def LinEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧
      ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW t) = 0 → evFin F v (sy σ X W x u) =
        ((X.J.map t * x.map (piW (t.comp σ)) * (W.J.map t)ᵀ)ᵀ * u.map (piW t)).trace

def SoZeroA' : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₀.IsGood B.ψ → ∀ M₁ : Model σ X W₁, M₁.IsGood B.ψ →
    (∃ χX χW om₁ om₀ r₁ s₁ r₀ s₀ r₂ s₂, IsPair B M₁ χX χW om₁ r₁ s₁ r₂ s₂ ∧ IsPair B M₀ χX χW om₀ r₀ s₀ r₂ s₂) →
    ∀ e₀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ Ψ ∈ schA F _,
      e₀ Ψ ∈ M₁.So B.ψ B.τ₁ → e Ψ = 0

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.ThetaKernelGeneralIdentity
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem split2_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} {W : Spc F E (a + a')} {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {X : Chars F E}
    (hlt : a' < a)
    (hdom : ∃ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ ∧ μ 𝓕 = 1)
    (hlevi : ∃ (t : (AE F E)ˣ) (m : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m ∧ 1 < (absE F E t : ℝ))
    {f fa fb fa' fb' : UA σ W.J → ℂ} (h₁ : Split2 W₁ H' X f fa fb) (h₂ : Split2 W₁ H' X f fa' fb') :
    fa = fa' ∧ fb = fb' := by
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := hdom
  obtain ⟨t, m, hm, ht⟩ := hlevi
  have hsum : ∀ h, fa h + fb h = fa' h + fb' h := by
    intro h
    have e1 := h₁.1 μ 𝓕 hμ h𝓕 h1 h
    have e2 := h₂.1 μ 𝓕 hμ h𝓕 h1 h
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2]
  have key : ∀ h, fa h = fa' h := by
    intro h
    by_contra hne
    have hA := h₁.2.1 t m hm h
    have hA' := h₂.2.1 t m hm h
    have hB := h₁.2.2 t m hm h
    have hB' := h₂.2.2 t m hm h
    have s1 := hsum (m * h)
    have s0 := hsum h
    set cA' : ℂ := (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) with hcA
    set cB : ℂ := (X.β t : ℂ) * (((absE F E t : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) with hcB
    have e : cA' * (fa h - fa' h) = cB * (fa h - fa' h) := by
      linear_combination -hA + hA' + s1 - hB + hB' - cB * s0
    have e' : cA' = cB := mul_right_cancel₀ (sub_ne_zero.2 hne) e
    have n1 : ‖cA'‖ = (absE F E t : ℝ) ^ ((a' : ℝ) / 2) := by
      rw [hcA, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    have n2 : ‖cB‖ = (absE F E t : ℝ) ^ ((a : ℝ) / 2) := by
      rw [hcB, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
    have hlt' : (a' : ℝ) / 2 < (a : ℝ) / 2 := by
      have : (a' : ℝ) < a := by exact_mod_cast hlt
      linarith
    have := Real.rpow_lt_rpow_of_exponent_lt ht hlt'
    rw [← n1, ← n2, e'] at this
    exact lt_irrefl _ this
  refine ⟨funext key, funext fun h => ?_⟩
  have := hsum h
  rw [key h] at this
  exact add_left_cancel this

theorem IsPair.cast {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' a b a' b' : ℕ} (h : IsPair B M χX χW om r s r' s') (h1 : r = a) (h2 : s = b) (h3 : r' = a') (h4 : s' = b') :
    IsPair B M χX χW om a b a' b' := by subst h1 h2 h3 h4; exact h

def reM {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (Y : Spc F E n) : Model σ (reS X Y) W :=
  ⟨M.co, M.vac, M.μ, M.dom⟩

theorem reM_good {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ} (h : M.IsGood ψ) (Y : Spc F E n) :
    (reM M Y).IsGood ψ := ⟨h.rat, h.vac, h.std, h.haar, h.dom⟩

theorem reM_pair {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (h : IsPair B M χX χW om r s r' s') {Y : Spc F E n} (hY : (reS X Y).IsHerm σ B r s) :
    IsPair B (reM M Y) χX χW om r s r' s' :=
  ⟨h.base, hY, h.skew, reM_good h.good Y, h.hX, h.hW, h.resX, h.resW, h.weil⟩

theorem reM_ev {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W} {M₁ : Model σ X W₁}
    {ι ι' I e} (h : IsEv B M M₁ ι ι' I e) (Y : Spc F E n) : IsEv B (reM M Y) (reM M₁ Y) ι ι' I e :=
  ⟨h.maps, h.Heisenberg₂, h.inv, h.loc⟩

theorem reM_so {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (Y : Spc F E n) (ψ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    (reM M Y).So ψ t = M.So ψ t := by
  have : (reM M Y).SoLoc ψ t = M.SoLoc ψ t := Set.ext fun φ =>
    ⟨fun ⟨h, ι, hι, r⟩ => ⟨h, ι, ⟨hι.bij, hι.trans, hι.mult⟩, r⟩, fun ⟨h, ι, hι, r⟩ => ⟨h, ι, ⟨hι.bij, hι.trans, hι.mult⟩, r⟩⟩
  unfold Model.So
  rw [this]
  rfl

theorem adapted_x_ne {n n₁ : ℕ} {B : Base F E} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁} {i₀ i₁ : ℕ}
    (h : H.IsAdapted σ B Y Y₁ i₀ i₁) : H.x ≠ 0 := by
  intro h0
  have := h.xy
  rw [h0] at this
  simp [form] at this

theorem res_low {χ : Chr F E} {n n₁ : ℕ} (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n) (e : n = n₁ + 2) :
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n₁ := by
  intro a
  rw [h a, e, pow_add]
  simp

theorem split_uniq (hU : UnipEx) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om'} (hT : IsTriple B G X om om')
    {d₁ : ℕ} {W₁ : Spc F E d₁} {H' : Plane E (a + a') d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B G.W W₁ i₀ i₁)
    {f fa fb fa' fb' : UA σ G.W.J → ℂ} (h₁ : Split2 W₁ H' X f fa fb) (h₂ : Split2 W₁ H' X f fa' fb') : fa = fa' ∧ fb = fb' := by
  obtain ⟨h1, -, -, -, ⟨lev, -, hl, -⟩, -, t, ht⟩ := hU F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ hT.base (Or.inr hT.geo.hW) hH
  exact split2_unique hT.geo.lt h1 ⟨t, _, hl t 1, ht⟩ h₁ h₂

def AnySplit (cond : ℕ → ℕ → ℕ → ℕ → Prop) (so : Bool) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r' s' : ℕ) (M : Model σ X W) (M₁ : Model σ X W₁),
    3 ≤ n → cond n d r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ e₀, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ χX χW om om₁, IsPair B M χX χW om r s (r' + 1) (s' + 1) → IsPair B M₁ χX χW om₁ r s r' s' →
      ∀ Φ ∈ PolData B M, (so = true → Φ ∈ M.So B.ψ B.τ₁) →
      ∃ A₀ A₁ : UA σ W.J → ℂ, IsCT H' (M.I om Φ) (A₀ + A₁) ∧ HasLaw W₁ H' χX ((n : ℝ) / 2) A₀ ∧
        HasLaw W₁ H' (χX / χW) (((d : ℝ) - n) / 2) A₁ ∧ ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h,
          (so = true → e₀ (om (1, h) Φ) ∈ M₁.So B.ψ B.τ₁) → A₀ (p * h) = C₀ * M₁.I om₁ (e₀ (om (1, h) Φ)) h₁

theorem theta_kernel_general_identity (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx) (hPl : PlaneHerm) (hC : EvCone)
    (cond : ℕ → ℕ → ℕ → ℕ → Prop) (so : Bool)
    (gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
      (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁)
      (j₀ j₁ i₀ i₁ r s r' s' : ℕ) (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
      ∀ (M₁ : Model σ X W₁) e₀ eA eB, M₁.IsGood B.ψ → M₀.IsGood B.ψ → IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
      IsEv B M M₀ H.ι H'.ι (isoA H H') eA → IsEv B M M₀ H.ι H'.ι (isoB H H') eB → cond n d (r + 1) (s + 1) →
      ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ χX χW om om₁ om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) →
        IsPair B M₁ χX χW om₁ (r + 1) (s + 1) r' s' → IsPair B M₀ χX χW om₀ r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d),
        (so = true → Φ ∈ M.So B.ψ B.τ₁) → KFinite om K Φ →
        ∃ A₀ A₁ : UA σ W.J → ℂ, IsCT H' (M.I om Φ) (A₀ + A₁) ∧ HasLaw W₁ H' χX ((n : ℝ) / 2) A₀ ∧
          HasLaw W₁ H' (χX / χW) (((d : ℝ) - n) / 2) A₁ ∧ ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h,
            (so = true → e₀ (om (1, h) Φ) ∈ M₁.So B.ψ B.τ₁) → A₀ (p * h) = C₀ * M₁.I om₁ (e₀ (om (1, h) Φ)) h₁) :
    AnySplit cond so := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ H' i₀ i₁ r s r' s' M M₁ hn hc hH' e₀ he₀
  by_cases h0 : min r s = 0
  · obtain ⟨C, hC0, h⟩ := hA F E σ B n d d₁ X W W₁ H' i₀ i₁ r s (r' + 1) (s' + 1) r' s' X M M₁ rfl h0 hH' e₀ he₀
    refine ⟨C, hC0, fun χX χW om om₁ hp hp₁ Φ hΦ _ => ?_⟩
    obtain ⟨K, μK, μ, hK1, -⟩ := hS F E σ B n X r s hp.base hp.herm
    obtain ⟨A₀, h1, h2, h3⟩ := h χX χW om om₁ hp hp₁ Φ (hK F E σ B n d X W M χX χW om _ _ _ _ hp K hK1 Φ hΦ).1
    exact ⟨A₀, 0, by rwa [add_zero], h2, fun t m _ h => by simp, fun h₁ p hp h _ => h3 h₁ p hp h⟩
  by_cases hex : ∃ χX χW om om₁, IsPair B M χX χW om r s (r' + 1) (s' + 1) ∧ IsPair B M₁ χX χW om₁ r s r' s'
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om om₁ hp hp₁ => absurd ⟨χX, χW, om, om₁, hp, hp₁⟩ hex⟩
  obtain ⟨χ0, χ0', o, o₁, hq, hq₁⟩ := hex
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  obtain ⟨Y, X₁, H, hY, hX₁, hH⟩ := hPl F E σ B hq.base n (n - 2) (by omega) (by omega) X (r + 1) (s + 1) (by omega) (by omega)
    hq.herm 0 1 (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hX₁
  obtain ⟨⟨M₀, hM₀⟩, hW⟩ := hP F E σ B hq.base _ _ X₁ W₁ r s r' s' hX₁ hq₁.skew
  obtain ⟨⟨eA, heA⟩, eB, heB⟩ := hC F E σ B n d _ W (reM M Y) χ0 χ0' o _ _ _ _ (reM_pair hq hY) _ _ X₁ W₁ H H' i₀ i₁ 0 1 M₀ hH hH' hM₀
  obtain ⟨K, μK, μ, hK1, -, hμK, hμ⟩ := hS F E σ B n X _ _ hq.base hq.herm
  have hIw : Iwa (X := X) H K := hI F E σ B n _ X _ _ H hq.base hq.herm (adapted_x_ne hH) hH.xx K hK1
  obtain ⟨C₀, hC₀, h⟩ := gen F E σ B n d _ d₁ (reS X Y) W X₁ W₁ H H' 0 1 i₀ i₁ r s r' s' (reM M Y) M₀ hH hH' (reM M₁ Y) e₀ eA eB
    (reM_good hq₁.good Y) hM₀ (reM_ev he₀ Y) heA heB hc K μK μ hIw hμK hμ
  refine ⟨C₀, hC₀, fun χX χW om om₁ hp hp₁ Φ hΦ hso => ?_⟩
  obtain ⟨om₀, hp₀⟩ := hW χX χW hp.hX hp.hW (res_low hp.resX hH.rank) hp₁.resW M₀ hM₀
  obtain ⟨hs, hf⟩ := hK F E σ B n d X W M χX χW om _ _ _ _ hp K hK1 Φ hΦ
  have := h χX χW om om₁ om₀ (reM_pair hp hY) (reM_pair hp₁ hY) hp₀ Φ hs (by rwa [reM_so]) hf
  simp only [reM_so] at this
  exact this

theorem anyBig (hG : GenBig) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx) (hPl : PlaneHerm) (hC : EvCone) :
    AnySplit (fun n d r s => ∃ z, 2 * n = d + 2 * z ∧ min r s + 1 ≤ z) false := by
  refine theta_kernel_general_identity hA hK hS hI hP hPl hC _ _ ?_
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eA eB h1 h0 he₀ hA' _ ⟨z, hz, hz'⟩ K μK μ hI hμK hμ
  obtain ⟨C₀, C₁, hC₀, -, h⟩ := hG F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eA h1 h0 he₀ hA' z
    ⟨hz, by omega⟩ K μK μ hI hμK hμ
  refine ⟨C₀, hC₀, fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ _ hf => ?_⟩
  obtain ⟨A₀, A₁, a, b, c, e⟩ := h χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ hf
  exact ⟨A₀, A₁, a, b, c, fun h₁ p hp h _ => (e h₁ p hp h).2⟩

theorem anySmall (hG : GenSmall) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx) (hPl : PlaneHerm)
    (hC : EvCone) : AnySplit (fun n d _ _ => ∃ z, d + 2 = 2 * n + 2 * z ∧ 2 ≤ z) true := by
  refine theta_kernel_general_identity hA hK hS hI hP hPl hC _ _ ?_
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eA eB h1 h0 he₀ _ hB' ⟨z, hz⟩ K μK μ hI hμK hμ
  obtain ⟨C₀, C₁, hC₀, -, h⟩ := hG F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ eB h1 h0 he₀ hB' z
    hz K μK μ hI hμK hμ
  refine ⟨C₀, hC₀, fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ _ hso hf => ?_⟩
  obtain ⟨A₀, A₁, a, b, c, e⟩ := h χX χW om om₁ om₀ hp hp₁ hp₀ Φ (hso rfl) hf
  exact ⟨A₀, A₁, a, b, c, fun h₁ p hp h hs => (e h₁ p hp h).2 (hs rfl)⟩

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.HodgeTateFromSandwich
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def StabDec : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ), B.IsGood σ →
    (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → H.IsAdapted σ B Y Y₁ i₀ i₁ →
    (∀ (p : UA σ Y.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      ∃ u ∈ unip σ Y H, ∃ g₁ m, IsLevi (W₁ := Y₁) H t g₁ m ∧ p = u * m ∧ (p ∈ ratU σ Y.J → g₁ ∈ ratU σ Y₁.J)) ∧
    (∀ (ξ : Eˣ), ∀ g₁ ∈ ratU σ Y₁.J, ∀ m, IsLevi H (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) g₁ m → m ∈ ratU σ Y.J) ∧
    ∀ t (g₁ : UA σ Y₁.J) m, IsLevi H t g₁ m → ∀ u ∈ unip σ Y H, m⁻¹ * u * m ∈ unip σ Y H

def ConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ z : ℕ, 2 * n = d + 2 * z ∧ min r s + 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ schA F (Fin n × Fin d), KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftA H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ)) h₁

def ConeB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoB H H') e → ∀ z : ℕ, d + 2 = 2 * n + 2 * z ∧ 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ M.So B.ψ B.τ₁, KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftB σ H H') χW z (om (1, h) Φ)) h₁

end PositivityTheory.ThKCT

end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.FourierUniq
noncomputable section

namespace PositivityTheory.ThKCT

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem std_ne_one {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) : ψ ≠ 1 := by
  intro h1
  have hn : 0 < Module.finrank ℚ F := Module.finrank_pos
  let m : NumberField.mixedEmbedding.mixedSpace F :=
    algebraMap ℝ (NumberField.mixedEmbedding.mixedSpace F) (1 / (2 * (Module.finrank ℚ F : ℝ)))
  let a : AF F := ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m, 0)
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) a := by
    intro u hu
    have hu1 : u.1 = 0 := by
      have h2 : NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (h2.trans (map_zero _).symm)
    show u * a = 0
    exact Prod.ext (by show u.1 * _ = 0; rw [hu1, zero_mul]) (by show u.2 * 0 = 0; rw [mul_zero])
  have hψa := h.2.2 a hAt
  rw [h1, AddChar.one_apply] at hψa
  have htr : Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a) = 1 / 2 := by
    show Algebra.trace ℝ _ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m)) = 1 / 2
    rw [RingEquiv.apply_symm_apply, Algebra.trace_algebraMap, NumberField.mixedEmbedding.finrank, nsmul_eq_mul]
    have : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [htr] at hψa
  have he : Complex.exp (-(2 * ↑Real.pi * Complex.I) * (((1 / 2 : ℝ)) : ℂ)) = -1 := by
    rw [show -(2 * ↑Real.pi * Complex.I) * (((1 / 2 : ℝ)) : ℂ) = -(↑Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [he] at hψa
  norm_num at hψa

theorem std_norm {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 :=
  (GlobalTheory.T.adelic_character_rational_dual F ψ h.1 (std_ne_one h) h.2.1).1 x

theorem std_ne_zero {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (x : AF F) : ψ x ≠ 0 := by
  intro h0
  have h1 : ψ (x + -x) = ψ x * ψ (-x) := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem thetaUniq_of : ThetaUniq := by
  intro F _ _ κ _ ψ hψ l hl hinv
  exact GlobalTheory.CompanionTheory.ThetaUniq.theta_unique F κ ψ hψ.1 (std_ne_one hψ) hψ.2.1 l hl (fun w Φ hΦ => hinv w.1 w.2 Φ hΦ)

theorem thetaInj_of : ThetaInj := by
  intro F _ _ κ _ ψ hψ Φ hΦ h0
  exact GlobalTheory.CompanionTheory.ThetaInj.theta_inj F κ ψ hψ.1 (std_ne_one hψ) hψ.2.1 Φ hΦ h0

theorem fourier_uniq {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (a : (κ → F) → ℂ) (hs : Summable a)
    (h0 : ∀ t : κ → AF F, ∑' y, a y * ψ ((fun i => algebraMap F (AF F) (y i)) ⬝ᵥ t) = 0) (y₀ : κ → F) : a y₀ = 0 := by
  classical
  let e : (κ → F) → (κ → AF F) → ℂ := fun y t => ψ ((fun i => algebraMap F (AF F) (y i)) ⬝ᵥ t)
  let c : (κ → F) → ℂ := fun y => a (y + y₀)
  have hmul : ∀ y s t, e y (s + t) = e y s * e y t := fun y s t => by
    simp only [e, dotProduct_add, AddChar.map_add_eq_mul]
  have hle : ∀ y t, ‖e y t‖ ≤ 1 := fun y t => (std_norm h _).le
  have h00 : ∀ t, e 0 t = 1 := fun t => by simp [e]
  have hne : ∀ y, y ≠ 0 → ∃ t, e y t ≠ 1 := by
    intro y hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have hi' : y i ≠ 0 := hi
    obtain ⟨s, hs'⟩ : ∃ s, ψ s ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact std_ne_one h (AddChar.ext ψ 1 fun s => by simpa using hc s)
    refine ⟨Pi.single i (algebraMap F (AF F) (y i)⁻¹ * s), ?_⟩
    simp only [e, dotProduct_single]
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
  have hcs : Summable fun y => ‖c y‖ := by
    have hc : Summable c := (Equiv.addRight y₀).summable_iff.mpr hs
    exact summable_norm_iff.mpr hc
  have hF : ∀ t, ∑' y, c y * e y t = 0 := by
    intro t
    have key : ∀ y, c y * e y t = e (-y₀) t * (a (y + y₀) * e (y + y₀) t) := by
      intro y
      have hsplit : e y t = e (-y₀) t * e (y + y₀) t := by
        simp only [e]
        rw [← AddChar.map_add_eq_mul, ← add_dotProduct]
        congr 2
        funext i
        simp [map_add (f := _), map_neg]
      rw [hsplit]
      ring
    simp_rw [key]
    rw [tsum_mul_left]
    have hre : ∑' y, a (y + y₀) * e (y + y₀) t = ∑' y, a y * e y t :=
      (Equiv.addRight y₀).tsum_eq (fun y => a y * e y t)
    rw [hre]
    have := h0 t
    simp only [e] at this ⊢
    rw [this, mul_zero]
  have := GlobalTheory.CompanionTheory.ThetaInj.charSeries_coeff_eq_zero e c 0 hmul hle h00 hne hcs hF
  simpa [c] using this

end PositivityTheory.ThKCT
end
end

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.TateAbs
noncomputable section

open NumberField MeasureTheory GroundTheory.Global nonZeroDivisors in
theorem PositivityTheory.ThKCT.Tate.transport {K G : Type} [Field K] [NumberField K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (e : G ≃ₜ* IdeleGroup K) (μ : Measure G) [μ.IsHaarMeasure] {z : ℝ} (hz : 1 < z) {k : ℕ}
    (hk : 2 * z + 2 < k) (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∫⁻ l, ENNReal.ofReal (infiniteZetaBound z k (IdeleGroup.toInfinite K (e l)) *
      finiteZetaBound L z (IdeleGroup.toFinite K (e l))) ∂μ < ⊤ := by
  have h2 := (integrable_zetaBound (K := K) hz hk L).smul_measure_nnreal (c := (μ.map e).haarScalarFactor (ideleMeasure K))
  rw [← Measure.isMulLeftInvariant_eq_smul] at h2
  exact (h2.comp_measurable e.continuous.measurable).lintegral_lt_top

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

namespace Tate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F E) in
abbrev Φ : AE F E ≃ₐ[AF F] AdeleRing (𝓞 E) E := adeleTensorAlgEquivLeft F E

theorem cont_Φ : Continuous (Φ F E) := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  exact IsModuleTopology.continuous_of_linearMap (Φ F E).toLinearMap

theorem cont_Φ_symm : Continuous (Φ F E).symm := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI := (ideleTop F E).1.1
  exact IsModuleTopology.continuous_of_linearMap (Φ F E).symm.toLinearMap


variable (F E) in
def Ψ : (AE F E)ˣ ≃ₜ* IdeleGroup E where
  toMulEquiv := Units.mapEquiv (Φ F E).toMulEquiv
  continuous_toFun := Continuous.units_map (Φ F E).toMulEquiv.toMonoidHom cont_Φ
  continuous_invFun := Continuous.units_map (Φ F E).symm.toMulEquiv.toMonoidHom cont_Φ_symm

theorem Ψ_val (l : (AE F E)ˣ) : ((Ψ F E l : IdeleGroup E) : AdeleRing (𝓞 E) E) = Φ F E l := rfl

theorem absE_eq (l : (AE F E)ˣ) : (absE F E l : ℝ) = IdeleGroup.ideleModule E (Ψ F E l) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), IdeleGroup.ideleModule_apply, IdeleGroup.infiniteModule,
    IdeleGroup.finiteModule, coe_ideleNorm, Ψ_val, Algebra.norm_eq_of_algEquiv, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul,
    NNReal.coe_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow]
    rfl
  · rw [show ((∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v l) : ℝ≥0) : ℝ) = _ from
      NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l)]
    refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

theorem ext_map (W : InfinitePlace E) {w : InfinitePlace F} (h : W.embedding.comp (algebraMap F E) = w.embedding)
    (b : InfiniteAdeleRing F) :
    InfinitePlace.Completion.extensionEmbedding W (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (L := E) b W) =
      InfinitePlace.Completion.extensionEmbedding w (b w) := by
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap F).equalizer
    ((InfinitePlace.Completion.isometry_extensionEmbedding W).continuous.comp ((continuous_apply W).comp
      (GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap (K := F) (L := E))))
    ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)) (funext fun k => ?_)) b
  change InfinitePlace.Completion.extensionEmbedding W (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (L := E)
    (algebraMap F (InfiniteAdeleRing F) k) W) = _
  rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap]
  simpa only [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.algebraMap_def,
    WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply, RingEquiv.apply_symm_apply,
    Function.comp_apply, WithAbs.equiv] using (InfinitePlace.Completion.extensionEmbedding_coe W (WithAbs.toAbs W.1 (algebraMap F E k))).trans
    ((RingHom.congr_fun h k).trans (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs w.1 k)).symm)

theorem ext_Φ (W : InfinitePlace E) {w : InfinitePlace F} (h : W.embedding.comp (algebraMap F E) = w.embedding) (l : AE F E) :
    InfinitePlace.Completion.extensionEmbedding W ((Φ F E l).1 W) = piInf (⟨W.embedding, h⟩ : EmbOver E w) l := by
  induction l using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact map_zero _
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), ← hx, ← hy]; exact map_add _ _ _
  | tmul a x =>
    rw [adeleTensorAlgEquivLeft_tmul]
    change InfinitePlace.Completion.extensionEmbedding W ((algebraMap E (AdeleRing (𝓞 E) E) x).1 W *
      GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (L := E) a.1 W) =
      InfinitePlace.Completion.extensionEmbedding w (a.1 w) * W.embedding x
    rw [map_mul, ext_map W h, mul_comm]
    simpa only [AdeleRing.algebraMap_fst_apply, AbsoluteValue.Completion.algebraMap_def,
      WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply, WithAbs.equiv_apply, WithAbs.ofAbs_toAbs] using
      congrArg _ (InfinitePlace.Completion.extensionEmbedding_coe W (WithAbs.toAbs W.1 x))

theorem norm_le (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : InfinitePlace E) (l : (AE F E)ˣ) :
    ‖(Φ F E l).1 W‖ ≤ ∑ w, ‖piInf (τ w) (l : AE F E)‖ := by
  haveI := h.1
  let w := InfinitePlace.mk (W.embedding.comp (algebraMap F E))
  have hw : W.embedding.comp (algebraMap F E) = w.embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal w))).symm
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding W).norm_map_of_map_zero (map_zero _), ext_Φ W hw]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun w => ‖piInf (τ w) (l : AE F E)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ w))
  have := (GlobalTheory.Doubling.absEw_eq_sq h (⟨W.embedding, hw⟩ : EmbOver E w) (GlobalTheory.Doubling.unitInf F E w l)).symm.trans
    (GlobalTheory.Doubling.absEw_eq_sq h (τ w) (GlobalTheory.Doubling.unitInf F E w l))
  exact congrArg NNReal.toReal ((pow_left_inj₀ zero_le' zero_le' two_ne_zero).1 this)

theorem snd_eq {l c : AE F E} (h : At (evI F) (l - c)) : (Φ F E l).2 = (Φ F E c).2 := by
  let u : AF F := ((0 : Ainf F), (1 : Af F))
  have h0 := congrArg (Φ F E) (h u (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)))
  rw [map_smul, map_zero, map_sub, Algebra.smul_def] at h0
  have h1 := congrArg Prod.snd h0
  change finiteAdeleMap F E 1 * ((Φ F E l).2 - (Φ F E c).2) = 0 at h1
  rwa [map_one, one_mul, sub_eq_zero] at h1

end Tate

theorem tateAbs : TateAbs := by
  intro F E _ _ _ _ _ σ B hB μ hμ z hz
  classical
  obtain ⟨-, _, _, _, _, _, -⟩ := ideleTop F E
  have hz1 : (1 : ℝ) < z := by exact_mod_cast hz
  have hk : 2 * (z : ℝ) + 2 < (2 * z + 3 : ℕ) := by push_cast; linarith
  refine ⟨(2 * z + 3) * Fintype.card (InfinitePlace E), fun C hC => ?_⟩
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles (hC.image (continuous_snd.comp (Tate.cont_Φ (F := F) (E := E))))
  refine lt_of_le_of_lt ?_ (Tate.transport (Tate.Ψ F E) μ hz1 hk L)
  have hT : IsOpen {l : (AE F E)ˣ | (Tate.Φ F E l).2 ∈ idealFiniteAdeles L} :=
    (isOpen_idealFiniteAdeles L).preimage (continuous_snd.comp (Tate.cont_Φ.comp Units.continuous_val))
  refine le_trans (lintegral_mono_set (t := {l : (AE F E)ˣ | (Tate.Φ F E l).2 ∈ idealFiniteAdeles L})
    fun l ⟨c, hc, hl⟩ => hL ⟨c, hc, (Tate.snd_eq hl).symm⟩) ?_
  refine le_trans (setLIntegral_mono' hT.measurableSet fun l hl => ENNReal.ofReal_le_ofReal ?_) (setLIntegral_le_lintegral _ _)
  have hm : (IdeleGroup.toFinite E (Tate.Ψ F E l) : FiniteAdeleRing (𝓞 E) E) ∈ idealFiniteAdeles L := hl
  rw [finiteZetaBound, if_pos hm, Tate.absE_eq, ← Real.rpow_natCast, ideleModule_rpow_eq, infiniteZetaBound,
    Finset.prod_div_distrib, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_left (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
    (Real.rpow_nonneg (IdeleGroup.finiteModule_pos _).le _)) (Finset.prod_pos fun _ _ => by positivity) ?_
  rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun W _ => pow_le_pow_left₀ (by positivity) ?_ _
  exact add_le_add le_rfl (Tate.norm_le hB.cm B.emb W l)

end PositivityTheory.ThKCT

end
end
