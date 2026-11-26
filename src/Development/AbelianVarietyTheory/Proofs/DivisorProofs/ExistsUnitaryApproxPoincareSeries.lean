module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitPeriodsBoundedBelowClosedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingTupleSmoothConeCmField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitsFourierTermsAllLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourierClassSumsDeeperLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelIntegralClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelIntegralClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.ClassCore

theorem cm_refl {X : Type} [AddCommGroup X] (N : ℕ) (x : X) : CongMod N x x := ⟨0, by simp⟩

theorem cm_symm {X : Type} [AddCommGroup X] {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h; exact ⟨-w, by simp⟩

theorem cm_trans {X : Type} [AddCommGroup X] {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) :
    CongMod N x z := by
  obtain ⟨w, rfl⟩ := h; obtain ⟨w', rfl⟩ := h'; exact ⟨w' + w, by rw [smul_add, add_assoc]⟩

theorem cm_map {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {N : ℕ} (g : X →+ Y) {x y : X} (h : CongMod N x y) :
    CongMod N (g x) (g y) := by
  obtain ⟨w, rfl⟩ := h; exact ⟨g w, by simp [map_nsmul]⟩

theorem qW_one {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (μ : Fin 1 → X) :
    qW !![(1 : ℤ)] β μ = β (μ 0) (μ 0) := by
  simp [qW]

theorem exists_min {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hpos : ∀ x, x ≠ 0 → 0 < β x x)
    (N : ℕ) (μ : Fin 1 → X) : ∃ μ' : Fin 1 → X, (∀ u, CongMod N (μ' u) (μ u)) ∧
      ∀ μ'' : Fin 1 → X, (∀ u, CongMod N (μ'' u) (μ u)) → qW !![(1 : ℤ)] β μ' ≤ qW !![(1 : ℤ)] β μ'' := by
  have hnn : ∀ x, 0 ≤ β x x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  obtain ⟨n, ⟨μ', hμ', rfl⟩, hmin⟩ := WellFounded.has_min Nat.lt_wfRel.wf
    {n | ∃ μ' : Fin 1 → X, (∀ u, CongMod N (μ' u) (μ u)) ∧ (qW !![(1 : ℤ)] β μ').toNat = n}
    ⟨_, μ, fun u => cm_refl N _, rfl⟩
  refine ⟨μ', hμ', fun μ'' h => ?_⟩
  have := hmin _ ⟨μ'', h, rfl⟩
  have key := not_lt.1 this
  simp only [qW_one] at key ⊢
  have h1 := hnn (μ' 0); have h2 := hnn (μ'' 0)
  have e1 := Int.toNat_of_nonneg h1; have e2 := Int.toNat_of_nonneg h2
  omega

end GlobalTheory.UPoinc.ClassCore

namespace GlobalTheory.UPoinc.ClassCore

theorem exists_norm_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime]
    {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X) :
    ∃ e : PadicAlgCl p, ‖e‖ = Real.exp (-(t.sc * t.T.be x x)) := by
  have hnn : 0 ≤ t.T.be x x := by simpa using IsMonomial.nonneg t.T.mono 0 x
  set a := t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) with ha
  have ha0 : a ≠ 0 := (map_ne_zero t.ι).2 ((map_ne_zero_iff _ (IsFractionRing.injective t.T.V _)).2 t.T.irr.ne_zero)
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  refine ⟨a ^ (t.T.be x x).toNat, ?_⟩
  have e1 : ((t.T.be x x : ℤ) : ℝ) = (((t.T.be x x).toNat : ℕ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [norm_pow, e1, UCTrait.sc, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]

end GlobalTheory.UPoinc.ClassCore

namespace GlobalTheory.UPoinc.ClassCore

theorem main_of_core (hcore : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw
    : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C
    : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar
    : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk
    z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞
    E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀
    : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_
    : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_
    : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁
    Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂)
    a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k
    : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X
    y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ
    : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c
    u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β
    y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β
    y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ
    u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ
    u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) /
    2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk
    z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞
    E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r
    * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ) : ∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l
    : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p
    : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p
    Dw.q) p (X₁.M.Z.presheaf.stalk
    z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞
    E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀
    : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_
    : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_
    : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁
    Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂)
    a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k
    : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (f : (Fin 1
    → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁)
    Ω₂)), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1
    : ℤ)] t ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧ (∀ y c κ (ε
    : ℝ), 0 < ε → ∃ S₀ : Finset (Fin 1 → Φ.X y), ∀ S : Finset (Fin 1 → Φ.X
    y), (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c
    u))) → μ ∈ S) → ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧ ∀ σ : (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure
    (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (a
    : 𝓞 E) x, CongMod N (γ (a • x)) (a • γ x)) ∧ (N
    : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (f c
    κ) = f (fun u => γ (c u)) κ := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ p _ z₁ Φ hΦ y₀ N₀
  obtain ⟨N, hN₀, hdvd, Ω₂, i1, i2, i3, i4, hc⟩ := hcore E H Dw hpq l Xo c C X₁ p z₁ Φ hΦ y₀ N₀
  refine ⟨N, hN₀, hdvd, Ω₂, i1, i2, i3, i4, ?_⟩
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra
  intro 𝔷 h𝔷 ev' h1 h2 h3
  obtain ⟨k, Q, F, hk0, hcls, hle, heq, hgal⟩ := hc 𝔷 h𝔷 ev' h1 h2 h3
  classical
  let qv : ∀ y, (Fin 1 → Φ.X y) → ℤ := fun y μ => qW !![(1 : ℤ)] (Φ.β y) μ
  let Cg : ∀ y, (Fin 1 → Φ.X y) → (Fin 1 → Φ.X y) → Prop := fun y μ μ' => ∀ u, CongMod N (μ u) (μ' u)
  let sel : ∀ y, (Fin 1 → Φ.X y) → (Fin 1 → Φ.X y) := fun y μ =>
    Classical.epsilon (fun μ' => Cg y μ' μ ∧ ∀ μ'', Cg y μ'' μ → qv y μ' ≤ qv y μ'')
  have hsel : ∀ y μ, Cg y (sel y μ) μ ∧ ∀ μ'', Cg y μ'' μ → qv y (sel y μ) ≤ qv y μ'' := fun y μ =>
    Classical.epsilon_spec (exists_min (Φ.β y) (Φ.pos y) N μ)
  have hselc : ∀ y μ μ', Cg y μ μ' → sel y μ = sel y μ' := by
    intro y μ μ' h
    show Classical.epsilon _ = Classical.epsilon _
    congr 1
    funext μ₁
    apply propext
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun u => cm_trans (h₁ u) (h u), fun μ'' h'' => h₂ μ'' fun u => cm_trans (h'' u) (cm_symm (h u))⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun u => cm_trans (h₁ u) (cm_symm (h u)), fun μ'' h'' => h₂ μ'' fun u => cm_trans (h'' u) (h u)⟩
  let NS : ∀ y, (Fin 1 → Φ.X y) → Prop := fun y μ => ∃ μ', Cg y μ' μ ∧ μ' ≠ μ ∧ qv y μ' ≤ qv y μ
  let wit : ∀ y, (Fin 1 → Φ.X y) → (Fin 1 → Φ.X y) := fun y μ => if h : NS y μ then h.choose else μ
  have hwit : ∀ y μ, NS y μ → Cg y (wit y μ) μ ∧ wit y μ ≠ μ ∧ qv y (wit y μ) ≤ qv y μ := by
    intro y μ h
    simp only [wit, dif_pos h]
    exact h.choose_spec
  have hel : ∀ y μ, ∃ e : PadicAlgCl p, ‖e‖ = Real.exp (-(Φ.sc y * qv y μ)) := by
    intro y μ
    obtain ⟨t, -, e', he'⟩ := hΦ y
    obtain ⟨e, he⟩ := exists_norm_eq t (e' (μ 0))
    refine ⟨e, ?_⟩
    rw [he, ← he']
    simp only [qv, qW_one]
  choose el hel using hel
  let g : ∀ y, (Fin 1 → Φ.X y) → (Fin 1 → Φ.X y) → PadicAlgCl p := fun y μ ν =>
    if NS y μ then (if ν = μ then el y μ else if ν = wit y μ then -el y μ else 0) else 0
  let Q' : Type := Q ⊕ (Σ y, (Fin 1 → Φ.X y))
  let t : ∀ y, (Fin 1 → Φ.X y) → Q' → PadicAlgCl p := fun y ν =>
    Sum.elim (fun κ => if ν = sel y ν then ev' y (F (fun u => (k y).symm (ν u)) κ) ^ 2 else 0)
      (fun s => if h : y = s.1 then g s.1 s.2 (h ▸ ν) else 0)
  let f : (Fin 1 → Φ.X y₀) → Q' → integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂ := fun cc =>
    Sum.elim (fun κ => F cc κ ^ 2) (fun _ => 0)
  refine ⟨fun y => (k y).toLinearMap.restrictScalars ℤ, Q', t, f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (k y₀).toLinearMap.restrictScalars ℤ = _
    rw [hk0]; rfl
  · intro y
    refine ⟨fun a x => ⟨0, by simp⟩, (k y).symm.restrictScalars ℤ, ?_⟩
    have : ((k y).symm.restrictScalars ℤ).toLinearMap ∘ₗ (k y).toLinearMap.restrictScalars ℤ = LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.det_id, sub_self]
    exact dvd_zero _
  · have hsc : ∀ y, 0 < Φ.sc y := Φ.sc_pos
    have hsq : ∀ y (μ : Fin 1 → Φ.X y) κ, μ = sel y μ →
        ‖ev' y (F (fun u => (k y).symm (μ u)) κ) ^ 2‖ ≤ Real.exp (-(Φ.sc y * qv y μ)) := by
      intro y μ κ hμ
      have h := hle y (fun u => (k y).symm (μ u)) κ μ (fun u => by
        simp only [LinearEquiv.apply_symm_apply]; exact cm_refl N _) (fun μ' h' => by
          have := (hsel y μ).2 μ' h'
          rw [← hμ] at this
          exact this)
      rw [norm_pow]
      calc ‖ev' y (F _ κ)‖ ^ 2 ≤ Real.exp (-(Φ.sc y * qv y μ) / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hg : ∀ y (μ ν : Fin 1 → Φ.X y), ‖g y μ ν‖ ≤ Real.exp (-(Φ.sc y * qv y ν)) := by
      intro y μ ν
      simp only [g]
      split_ifs with hN hν hw
      · subst hν; rw [hel]
      · subst hw; rw [norm_neg, hel]
        refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (hsc y).le))
        exact_mod_cast (hwit y μ hN).2.2
      · rw [norm_zero]; exact (Real.exp_pos _).le
      · rw [norm_zero]; exact (Real.exp_pos _).le
    refine ⟨fun y μ κ => ?_, fun y μ => ?_⟩
    · rcases κ with κ | ⟨y', μ'⟩
      · simp only [t, Sum.elim_inl]
        split_ifs with hμ
        · exact hsq y μ κ hμ
        · rw [norm_zero]; exact (Real.exp_pos _).le
      · simp only [t, Sum.elim_inr]
        split_ifs with h
        · subst h; exact hg y μ' μ
        · rw [norm_zero]; exact (Real.exp_pos _).le
    · by_cases hns : NS y μ
      · refine ⟨Sum.inr ⟨y, μ⟩, ?_⟩
        simp only [t, Sum.elim_inr, dif_pos rfl, g, if_pos hns, if_pos rfl]
        exact hel y μ
      · have hstrict : ∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ →
            qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ' := by
          intro μ' h1 h2
          by_contra h3
          exact hns ⟨μ', h1, h2, not_lt.1 h3⟩
        obtain ⟨cc, κ, hcc, hnorm⟩ := heq y μ hstrict
        have hsel' : sel y μ = μ := by
          by_contra hne
          have := hstrict _ (hsel y μ).1 hne
          exact absurd ((hsel y μ).2 μ (fun u => cm_refl N _)) (not_le.2 this)
        have hF : F (fun u => (k y).symm (μ u)) κ = F cc κ := by
          refine hcls _ _ κ (fun u => ?_)
          have := cm_map (k y).symm.toLinearMap.toAddMonoidHom (hcc u)
          simpa using this
        refine ⟨Sum.inl κ, ?_⟩
        simp only [t, Sum.elim_inl, hsel', if_pos rfl]
        rw [if_pos trivial, hF, norm_pow, hnorm, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  · rintro cc cc' (κ | s) h
    · simp only [f, Sum.elim_inl, hcls cc cc' κ h]
    · rfl
  · intro y cc κ ε hε
    rcases κ with κ | ⟨y', μ⟩
    · set s := sel y (fun u => k y (cc u)) with hs
      refine ⟨{s}, fun S hS hS₀ => ?_⟩
      have hS' : ∀ μ ∈ S, Cg y μ (fun u => k y (cc u)) := fun μ hμ u => by simpa using hS μ hμ u
      have hmem : s ∈ S := hS₀ s (Finset.mem_singleton_self _) (fun u => by simpa using (hsel y _).1 u)
      have hss : sel y s = s := hselc y s _ (hsel y _).1
      have hsum : ∑ μ ∈ S, t y μ (Sum.inl κ) = t y s (Sum.inl κ) := by
        refine Finset.sum_eq_single_of_mem s hmem (fun μ hμ hne => ?_)
        simp only [t, Sum.elim_inl]
        rw [if_neg]
        intro h
        exact hne (h.trans (hselc y μ _ (hS' μ hμ)))
      have hF : F (fun u => (k y).symm (s u)) κ = F cc κ := by
        refine hcls _ _ κ (fun u => ?_)
        have := cm_map (k y).symm.toLinearMap.toAddMonoidHom ((hsel y (fun u => k y (cc u))).1 u)
        simpa using this
      rw [hsum]
      simp only [t, Sum.elim_inl, hss]
      rw [if_pos trivial, hF]
      simp [f, hε.le]
    · by_cases hy : y = y'
      · subst hy
        refine ⟨{μ, wit y μ}, fun S hS hS₀ => ?_⟩
        have hS' : ∀ ν ∈ S, Cg y ν (fun u => k y (cc u)) := fun ν hν u => by simpa using hS ν hν u
        have hsum : ∑ ν ∈ S, t y ν (Sum.inr ⟨y, μ⟩) = 0 := by
          simp only [t, Sum.elim_inr, dif_pos rfl, dite_true]
          by_cases hns : NS y μ
          · obtain ⟨hw1, hw2, -⟩ := hwit y μ hns
            simp only [g, if_pos hns]
            by_cases hc : Cg y μ (fun u => k y (cc u))
            · have hμS : μ ∈ S := hS₀ μ (by simp) (fun u => by simpa using hc u)
              have hwS : wit y μ ∈ S := hS₀ _ (by simp) (fun u => by simpa using cm_trans (hw1 u) (hc u))
              have e : ∀ ν : Fin 1 → Φ.X y, (if ν = μ then el y μ else if ν = wit y μ then -el y μ else 0) =
                  (if ν = μ then el y μ else 0) + (if ν = wit y μ then -el y μ else 0) := by
                intro ν
                by_cases h1 : ν = μ
                · subst h1; simp [hw2.symm]
                · simp [h1]
              rw [Finset.sum_congr rfl (fun ν _ => e ν), Finset.sum_add_distrib, Finset.sum_ite_eq' S μ,
                Finset.sum_ite_eq' S (wit y μ), if_pos hμS, if_pos hwS, add_neg_cancel]
            · refine Finset.sum_eq_zero (fun ν hν => ?_)
              have h1 : ν ≠ μ := fun h => hc (h ▸ hS' ν hν)
              have h2 : ν ≠ wit y μ := fun h => hc (fun u => cm_trans (cm_symm (hw1 u)) (h ▸ hS' ν hν u))
              simp [h1, h2]
          · simp [g, hns]
        rw [hsum]
        simp [f, hε.le]
      · refine ⟨∅, fun S _ _ => ?_⟩
        have hsum : ∑ ν ∈ S, t y ν (Sum.inr ⟨y', μ⟩) = 0 :=
          Finset.sum_eq_zero (fun ν _ => by simp [t, hy])
        rw [hsum]
        simp [f, hε.le]
  · intro σ hσ
    obtain ⟨γ, hdet, hcong, hF⟩ := hgal σ hσ
    refine ⟨γ.toLinearMap.restrictScalars ℤ, fun a x => ⟨0, by simp⟩, hdet, hcong, ?_⟩
    rintro cc (κ | s)
    · simp [f, hF]
    · simp [f]

end GlobalTheory.UPoinc.ClassCore

namespace GlobalTheory.UPoinc.ClassCore

theorem classSums_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (f : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1 : ℤ)] t ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧ (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin 1 → Φ.X y), ∀ S : Finset (Fin 1 → Φ.X y), (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) → ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (a : 𝓞 E) x, CongMod N (γ (a • x)) (a • γ x)) ∧ (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ :=
  main_of_core GlobalTheory.T.unitary_classSums_deeper_level_geometric_core

end GlobalTheory.UPoinc.ClassCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelIntegralClosureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_classSums_deeper_level_integralClosure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (f : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1 : ℤ)] t ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧ (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin 1 → Φ.X y), ∀ S : Finset (Fin 1 → Φ.X y), (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) → ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (∀ (a : 𝓞 E) x, CongMod N (γ (a • x)) (a • γ x)) ∧ (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.UPoinc.ClassCore.classSums_core | exact GlobalTheory.UPoinc.ClassCore.classSums_core | (intros; apply GlobalTheory.UPoinc.ClassCore.classSums_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourierClassSumsDeeperLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem ustalk_isNoetherian_normal_fractionRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  intro E _ _ _ H Dw l Xo c C X₁ z₁
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  have hN := X₁.normal
  refine ⟨GlobalTheory.IsNormalScheme.isDomain_stalk z₁, ?_, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z₁, ?_⟩
  · have : FaithfulSMul (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (X₁.M.stalkHom_injective z₁)
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := X₁.M.O z₁) x
    refine ⟨(X₁.M.stalkEquiv z₁).symm a, (X₁.M.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : X₁.M.O z₁, algebraMap (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ((X₁.M.stalkEquiv z₁).symm c) = c := fun c => by
      change X₁.M.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  · have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
    have := X₁.M.lft
    have : IsLocallyNoetherian (Sp X₁.o₁) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    infer_instance

theorem uclassSums_deeper : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (X₁.M.Z.presheaf.stalk z₁) B) (_ : Module.Finite (X₁.M.Z.presheaf.stalk z₁) B) (_ : Finite (B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B)) (𝔷 : Ideal B), Function.Injective (algebraMap (X₁.M.Z.presheaf.stalk z₁) B) ∧ (∀ b : B, (∀ σ : B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B, σ b = b) → b ∈ Set.range (algebraMap (X₁.M.Z.presheaf.stalk z₁) B)) ∧ 𝔷.IsMaximal ∧ k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1 : ℤ)] t ∧ Φ.ClassSums (X₁.S.r * X₁.S.N) N y₀ k t B 𝔷 := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ p _ z₁ Φ hΦ y₀ N₀
  obtain ⟨N, hN₀, hdvd, Ω₂, _, _, _, _, hcore⟩ := GlobalTheory.T.unitary_classSums_deeper_level_integralClosure E H Dw hpq l Xo c C X₁ p z₁ Φ hΦ y₀ N₀
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := ustalk_isNoetherian_normal_fractionRing E H Dw l Xo c C X₁ z₁
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.T.integralClosure_galois_finite_autGroup_invariants (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ Ω₂
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra
  obtain ⟨𝔷, hmax⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)
  have hext := fun y => GlobalTheory.T.extend_integral_padic_evaluation_galois p (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) 𝔷 hinj hfix hmax (Φ.ev y) (Φ.ev_le y) (Φ.ev_lt y)
  choose ev' h1 h2 h3 using hext
  obtain ⟨k, Q, t, f, hk₀, hk, ht, hf, hcs, hgal⟩ := hcore 𝔷 hmax ev' h1 h2 h3
  exact ⟨N, hN₀, hdvd, k, Q, t, (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), inferInstance, inferInstance, inferInstance, hfin, hfinA, 𝔷, hinj, hfix, hmax, hk₀, hk, ht,
    ev', f, h1, h2, h3, hf, hcs, hgal⟩

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourierClassSumsDeeperLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fourierClassSums_deeper_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 1 → Φ.X y) → Q → PadicAlgCl p) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (X₁.M.Z.presheaf.stalk z₁) B) (_ : Module.Finite (X₁.M.Z.presheaf.stalk z₁) B) (_ : Finite (B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B)) (𝔷 : Ideal B), Function.Injective (algebraMap (X₁.M.Z.presheaf.stalk z₁) B) ∧ (∀ b : B, (∀ σ : B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B, σ b = b) → b ∈ Set.range (algebraMap (X₁.M.Z.presheaf.stalk z₁) B)) ∧ 𝔷.IsMaximal ∧ k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod (𝓞 E) N (k y)) ∧ Φ.IsTerms !![(1 : ℤ)] t ∧ Φ.ClassSums (X₁.S.r * X₁.S.N) N y₀ k t B 𝔷 := by
  first | exact @GlobalTheory.UPoinc.uclassSums_deeper | exact GlobalTheory.UPoinc.uclassSums_deeper | (intros; apply GlobalTheory.UPoinc.uclassSums_deeper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitsFourierTermsAllLevels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem USetup.isNoetherianRing_stalk {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c} (X₁ : USetup C) (z₁ : X₁.M.Z) :
    IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  have := X₁.M.lft
  have : IsLocallyNoetherian (Sp X₁.o₁) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
  have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  infer_instance

theorem posW_one_one : PosW (!![1] : Matrix (Fin 1) (Fin 1) ℤ) := by
  unfold PosW
  have : ((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) = Matrix.diagonal fun _ => 2 := by
    ext i j
    fin_cases i; fin_cases j; simp [Matrix.vecHead, Function.swap]
  rw [this, Matrix.posDef_diagonal_iff]
  intro _; norm_num

theorem four_of_classical : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → Φ.Four !![(1 : ℤ)] (X₁.S.r * X₁.S.N) := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ p _ z₁ Φ h y₀ N₀
  obtain ⟨N, hN, hd, k, Q, t, B, _, _, _, _, _, 𝔷, hinj, hfix, hmax, hk, hu, ht, hc⟩ :=
    GlobalTheory.T.unitary_fourierClassSums_deeper_level E H Dw hpq l Xo c C X₁ p z₁ Φ h y₀ (N₀ + 1)
  have := X₁.normal.isDomain_stalk z₁
  have := X₁.normal.isIntegrallyClosed_stalk z₁
  have := X₁.isNoetherianRing_stalk z₁
  exact ⟨N, by omega, hd, k, Q, t, hk, hu, ht,
    GlobalTheory.T.approx_orbitSums_of_galois_classSums (𝓞 E) H.bar (min Dw.p Dw.q) p _ Φ 1 !![(1 : ℤ)] _ N y₀ k Q t B hinj hfix 𝔷 hmax (by omega) posW_one_one hu hc⟩

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitsFourierTermsAllLevelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_classicalTraits_fourierTerms_all_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → Φ.Four !![(1 : ℤ)] (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.UPoinc.four_of_classical | exact GlobalTheory.UPoinc.four_of_classical | (intros; apply GlobalTheory.UPoinc.four_of_classical <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSystemClassicalTraitsClosedPoi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSystemClassicalTraitsClosedPoi
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem rank_le (T : UTrait Xo c) : Module.finrank (𝓞 E) T.P.D.toPre.X ≤ min Dw.p Dw.q := GlobalTheory.T.character_group_finrank_le_min_signature_unitary_trait E H Dw l Xo c T

theorem lam (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ :=
  GlobalTheory.T.classical_trait_periods_bounded_below_closed_point E H Dw l Xo c C X₁ p z₁ hz

theorem finite_X (T : UTrait Xo c) : Module.Finite (𝓞 E) T.P.D.toPre.X :=
  Module.Finite.of_restrictScalars_finite ℤ _ _

theorem projective_X (T : UTrait Xo c) : Module.Projective (𝓞 E) T.P.D.toPre.X := by
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := finite_X T
  have : Module.Flat (𝓞 E) T.P.D.toPre.X := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨a, hx⟩
    by_contra hx0
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (a : 𝓞 E)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero (nonZeroDivisors.coe_ne_zero a))
    have h : n • x = 0 := by
      have hx' : (a : 𝓞 E) • x = 0 := hx
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hx', smul_zero]
    exact hx0 ((smul_eq_zero.1 h).resolve_left hn)
  have : Module.FinitePresentation (𝓞 E) T.P.D.toPre.X := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

variable {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (t : UCTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ t.y) z₁ (RatModel.gPt_specializes t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem evC_apply (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC t a = t.val a := rfl

theorem norm_evC_le (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC t a‖ ≤ 1 :=
  RatModel.norm_val_le_one t.cen (X₁.M.stalkEquiv z₁ a).2

theorem norm_evC_lt (t : UCTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC t a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff t.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem be_bal (T : UTrait Xo c) : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X := by
  rw [balForms_eq_levelForms]; exact T.lev

end GlobalTheory.UPoinc.PreSys

namespace GlobalTheory.UPoinc.PreSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}


variable (E X₁ p) in
abbrev Key : Type :=
  (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (𝓞 E →+* Module.End ℤ (Fin k → ℤ)) × ((Fin k → ℤ) → (Fin k → ℤ) → ℝ))

def Rep (t : UCTrait X₁ p z₁) (q : Key E X₁ p) : Prop :=
  t.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X, (∀ (a : 𝓞 E) u, e (q.2.2.1 a u) = a • e u) ∧
    ∀ u v, q.2.2.2 u v = t.sc * t.T.be (e u) (e v)

def coord (t : UCTrait X₁ p z₁) : (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) ≃ₗ[ℤ] t.T.P.D.toPre.X :=
  (Module.finBasis ℤ t.T.P.D.toPre.X).equivFun.symm

def actOf (t : UCTrait X₁ p z₁) : 𝓞 E →+* Module.End ℤ (Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) where
  toFun a := (coord t).symm.toLinearMap ∘ₗ (DistribSMul.toLinearMap ℤ t.T.P.D.toPre.X a) ∘ₗ (coord t).toLinearMap
  map_one' := LinearMap.ext fun u => by simp
  map_mul' a b := LinearMap.ext fun u => by simp [mul_smul]
  map_zero' := LinearMap.ext fun u => by simp
  map_add' a b := LinearMap.ext fun u => by simp [add_smul]

theorem coord_actOf (t : UCTrait X₁ p z₁) (a : 𝓞 E) (u : Fin (Module.finrank ℤ t.T.P.D.toPre.X) → ℤ) :
    coord t (actOf t a u) = a • coord t u := by
  simp [actOf]

def keyOf (t : UCTrait X₁ p z₁) : Key E X₁ p :=
  (t.y, ⟨Module.finrank ℤ t.T.P.D.toPre.X, actOf t, fun u v => t.sc * t.T.be (coord t u) (coord t v)⟩)

theorem rep_keyOf (t : UCTrait X₁ p z₁) : Rep t (keyOf t) := ⟨rfl, coord t, coord_actOf t, fun _ _ => rfl⟩


variable (X₁ p z₁) in
def Pts : Type := {q : Key E X₁ p // ∃ t : UCTrait X₁ p z₁, Rep t q}

noncomputable def pick (y : Pts X₁ p z₁) : UCTrait X₁ p z₁ := Classical.choose y.2

theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2

theorem exists_equiv_of_rep {t t' : UCTrait X₁ p z₁} {q : Key E X₁ p} (h : Rep t q) (h' : Rep t' q) :
    ∃ e : t.T.P.D.toPre.X ≃ₗ[𝓞 E] t'.T.P.D.toPre.X, ∀ a b, t.sc * t.T.be a b = t'.sc * t'.T.be (e a) (e b) := by
  obtain ⟨-, f, hf, hfb⟩ := h
  obtain ⟨-, f', hf', hfb'⟩ := h'
  let g : t.T.P.D.toPre.X ≃ₗ[ℤ] t'.T.P.D.toPre.X := f.symm.trans f'
  have hg : ∀ (a : 𝓞 E) x, g (a • x) = a • g x := by
    intro a x
    obtain ⟨u, rfl⟩ := f.surjective x
    simp only [g, LinearEquiv.trans_apply, ← hf, LinearEquiv.symm_apply_apply, hf']
  refine ⟨{ g with map_smul' := hg }, fun a b => ?_⟩
  obtain ⟨u, rfl⟩ := f.surjective a
  obtain ⟨v, rfl⟩ := f.surjective b
  show _ = t'.sc * t'.T.be (g (f u)) (g (f v))
  simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [← hfb, ← hfb']


variable (X₁ p z₁) in
noncomputable def sys : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.P.D.toPre.X
  fin y := finite_X _
  proj y := projective_X _
  rank_le y := rank_le _
  β y := (pick y).T.be
  bal y := be_bal _
  pos y x hx := be_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

theorem sys_matches : UMatches (sys X₁ p z₁) := by
  intro t
  refine ⟨⟨keyOf t, t, rep_keyOf t⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf t, t, rep_keyOf t⟩
    show evC _ a = t.val a
    rw [evC_apply]
    unfold UCTrait.val
    rw [hy]
    rfl
  · exact exists_equiv_of_rep (pick_rep ⟨keyOf t, t, rep_keyOf t⟩) (rep_keyOf t)

theorem sys_lam (hz : IsClosed ({z₁} : Set X₁.M.Z)) : (sys X₁ p z₁).abelian₂ := by
  obtain ⟨K, hK⟩ := lam X₁ p z₁ hz
  exact ⟨K, fun y x hx => hK (pick y) x hx⟩

end GlobalTheory.UPoinc.PreSys


open GlobalTheory Classical in
theorem GlobalTheory.UPoinc.PreSys.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), UMatches Φ ∧ Φ.abelian₂ ∧ (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) := by
  intro E _ _ _ H Dw _ l Xo c C X₁ p _ z₁ hz
  exact ⟨GlobalTheory.UPoinc.PreSys.sys X₁ p z₁, GlobalTheory.UPoinc.PreSys.sys_matches, GlobalTheory.UPoinc.PreSys.sys_lam hz,
    fun y => ⟨GlobalTheory.UPoinc.PreSys.pick y, fun a => rfl, LinearEquiv.refl _ _, fun a b => rfl⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryThetaSystemClassicalTraitsClosedPoiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryThetaSystem_classicalTraits_closedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), UMatches Φ ∧ Φ.abelian₂ ∧ (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) := by
  first | exact @GlobalTheory.UPoinc.PreSys.main | exact GlobalTheory.UPoinc.PreSys.main | (intros; apply GlobalTheory.UPoinc.PreSys.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryApproxPoincareSeries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c}

theorem sc_pos {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  set u := algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ with hu
  have h0 : t.T.ϖ ≠ 0 := t.T.irr.ne_zero
  have hu0 : u ≠ 0 := by
    rw [hu]; exact (IsFractionRing.injective t.T.V (FractionRing t.T.V)).ne_iff' (map_zero _) |>.2 h0
  have hι0 : t.ι u ≠ 0 := (map_ne_zero t.ι).2 hu0
  have hle : ‖t.ι u‖ ≤ 1 := (t.int u).2 ⟨_, rfl⟩
  have hlt : ‖t.ι u‖ < 1 := by
    refine lt_of_le_of_ne hle fun h1 => ?_
    have : ‖t.ι u⁻¹‖ ≤ 1 := by rw [map_inv₀, norm_inv, h1, inv_one]
    obtain ⟨v, hv⟩ := (t.int _).1 this
    apply t.T.irr.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective t.T.V (FractionRing t.T.V)
    rw [map_mul, hv, ← hu, mul_inv_cancel₀ hu0, map_one]
  have hpos : 0 < ‖t.ι u‖ := norm_pos_iff.2 hι0
  unfold UCTrait.sc
  rw [← hu]
  linarith [Real.log_neg hpos hlt]

theorem sc_evalZ_eq_of_equiv {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {φ : InvFun O} {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y]
    [Module.Finite O Y] (hP : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : ∀ x, 0 ≤ β x x) {β' : LinearMap.BilinForm ℤ Y} {s s' : ℝ} (hs0 : 0 ≤ s) (hs' : 0 < s') (e : X ≃ₗ[O] Y)
    (he : ∀ a b, s * β a b = s' * β' (e a) (e b)) : s * φ.evalZ β = s' * φ.evalZ β' := by
  have hmem : toReal β ∈ psdCone (bar := bar) (X := X) := StrictData.toReal_mem_psdCone hβ hp
  have hform : toReal (pull e.toLinearMap β') = (s / s') • toReal β := by
    refine LinearMap.ext₂ fun a b => ?_
    have := he a b
    simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul, LinearEquiv.coe_coe]
    field_simp
    linarith
  have h1 : φ.evalZ (pull e.toLinearMap β') = φ.evalZ β' := evalZ_pull φ e.surjective _
  rw [← h1, ← evalR_toReal φ (pull _ _), hform, hP.homog _ hmem _ (div_nonneg hs0 hs'.le), evalR_toReal]
  field_simp

theorem posW_one : PosW (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) := by
  unfold PosW
  have : ((!![(1 : ℤ)] + (!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) =
      Matrix.diagonal fun _ => (2 : ℝ) := by
    ext i j; fin_cases i; fin_cases j; norm_num [Matrix.vecHead, Function.swap]
  rw [this]
  exact Matrix.PosDef.diagonal (fun _ => by norm_num)

end GlobalTheory.UPoinc.GApprox

namespace GlobalTheory.UPoinc.GApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {C : UCompact Xo c}

theorem sc_evalZ_eq {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {φ : InvFun (𝓞 E)}
    (hpol : IsPolFan H.bar (min D.p D.q) φ)
    (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min D.p D.q) p (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (t : UCTrait X₁ p z₁)
    (e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X) (he : ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) :
    Φ.sc y * φ.evalZ (Φ.β y) = t.sc * φ.evalZ t.T.be :=
  sc_evalZ_eq_of_equiv (hpol _ (Φ.rank_le y)) (Φ.bal y) (fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · exact (Φ.pos y x hx).le) (Φ.sc_pos y).le (sc_pos t) e he

theorem exists_hasSupports_cm (q : ℕ) (φ : InvFun (𝓞 E)) (hpol : IsPolFan H.bar q φ) :
    ∃ d, 1 ≤ d ∧ HasSupports (H.bar : 𝓞 E → 𝓞 E) q φ d :=
  exists_hasSupports (𝓞 E) H.bar q φ hpol fun X _ _ _ _ hX r γ hγ => GlobalTheory.T.exists_supportingTuple_smoothCone_cmField E H φ X (hpol X hX) r γ hγ

end GlobalTheory.UPoinc.GApprox


open GlobalTheory.UPoinc.GApprox in
theorem GlobalTheory.UPoinc.exists_uApproxAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∃ d : ℕ, 1 ≤ d ∧ UApproxAt X₁ φ d := by
  intro E _ _ _ H Dw hpq l Xo c C X₁ φ hpol
  obtain ⟨d₀, hd₀, hsup⟩ := exists_hasSupports_cm (H := H) (min Dw.p Dw.q) φ hpol
  have hN : 3 ≤ X₁.S.r * X₁.S.N := by
    have h1 := X₁.big.2.2
    have h2 : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega))
        (Nat.factorial_ne_zero _))
    omega
  have hW1 : ((!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) 0 0).toNat = 1 := by simp
  refine ⟨((!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) 0 0).toNat * d₀, by rw [hW1]; omega, ?_⟩
  intro p _ z₁ t₀ e
  have hcl : IsClosed ({z₁} : Set X₁.M.Z) := t₀.cen ▸ isClosed_singleton_cPt t₀.y
  obtain ⟨Φ, hM, hL, hR⟩ := GlobalTheory.T.exists_unitaryThetaSystem_classicalTraits_closedPoint E H Dw hpq l Xo c C X₁ p z₁ hcl
  have hF := GlobalTheory.T.unitary_classicalTraits_fourierTerms_all_levels E H Dw hpq l Xo c C X₁ p z₁ Φ hR
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  have hA := approx_of_fpre (𝓞 E) H.bar (bddAct_int_and_cm.2 E H) (min Dw.p Dw.q) φ hpol d₀ hsup 0
    !![(1 : ℤ)] posW_one (X₁.S.r * X₁.S.N) p hN _ Φ hL hF
  set d := ((!![(1 : ℤ)] : Matrix (Fin 1) (Fin 1) ℤ) 0 0).toNat * d₀ with hd
  obtain ⟨y₀, hev₀, e₀, he₀⟩ := hM t₀
  obtain ⟨f, hf1, hf2⟩ := hA y₀ e
  have key : ∀ (y : Φ.Y) (t : UCTrait X₁ p z₁) (e' : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X),
      (∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e' a) (e' b)) →
      Φ.sc y * ((d : ℝ) * φ.evalZ (Φ.β y)) = t.sc * ((d : ℝ) * φ.evalZ t.T.be) := by
    intro y t e' h
    have := sc_evalZ_eq hpol Φ y t e' h
    calc Φ.sc y * ((d : ℝ) * φ.evalZ (Φ.β y)) = (d : ℝ) * (Φ.sc y * φ.evalZ (Φ.β y)) := by ring
      _ = t.sc * ((d : ℝ) * φ.evalZ t.T.be) := by rw [this]; ring
  refine ⟨f, ?_, fun t => ?_⟩
  · rw [← hev₀ f, hf1, key y₀ t₀ e₀ he₀]
  · obtain ⟨y, hev, e', he'⟩ := hM t
    rcases hf2 y with h | ⟨h, hh, hle⟩
    · left; rw [← hev f, ← key y t e' he']; exact h
    · right; exact ⟨h, hh, by rw [← hev f, ← hev h]; exact hle⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryApproxPoincareSeriesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryApproxPoincareSeries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∃ d : ℕ, 1 ≤ d ∧ UApproxAt X₁ φ d := by
  first | exact @GlobalTheory.UPoinc.exists_uApproxAt | exact GlobalTheory.UPoinc.exists_uApproxAt | (intros; apply GlobalTheory.UPoinc.exists_uApproxAt <;> assumption)
end
