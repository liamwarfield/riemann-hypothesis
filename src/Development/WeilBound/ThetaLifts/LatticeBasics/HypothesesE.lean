module

public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def SiegelWeilAniso : Prop := SWAniso ∧ SWAnisoX


variable (σ Y) in
def IsFrame2 (b : GL (Fin n ⊕ Fin n) E) : Prop :=
  (∃ ε : ℤˣ, b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ∧
    ∃ t : GL (Fin n) E, b.1.toCols₁ = diagCols (Fin n) * t.1


variable (F E) in
def intHat : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧
    ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}


variable (F) in
def finOne : AF F := LinearMap.inr F (Ainf F) (Af F) 1

def inFrame (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
  incM F (b⁻¹).1 * mat2 x * incM F b.1

def IsStdK (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) : Prop :=
  ∀ k, k ∈ K ↔ (∀ w, (inFrame b k).map (piInf (B.emb w)) * ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1) ∧
    ∀ k' ∈ ({k, k⁻¹} : Set (G2 σ Y)), ∀ i j, finOne F • inFrame b k' i j ∈ intHat F E


variable (σ Y) in
def modFun : Submodule ℂ (G2 σ Y → ℂ) :=
  Submodule.span ℂ {f | Continuous f ∧ ∃ N : ℕ, ∀ x, ‖f x‖ ≤ (ht2 x : ℝ) ^ N}

def IsGrowForm (μ : modFun σ Y →ₗ[ℂ] ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ f : modFun σ Y, (∀ x, ‖f.1 x‖ ≤ (ht2 x : ℝ) ^ N) → ‖μ f‖ ≤ C

def EisBL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U

def FrameConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → ∃ b K₀ p t, IsFrame2 σ Y b ∧ IsStdK B b K₀ ∧ IsPar p t ∧ ∀ k, k ∈ K ↔ p⁻¹ * k * p ∈ K₀

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def SplitModel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinW B.ψ t 1 1 ι) ∧ ∀ ι, M.IsLinW B.ψ t 1 1 ι →
      ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ (g₀ : GL (Fin n) (Fv F v)) (h₀ : GL (Fin d) (Fv F v)),
        g₀.1 = (mat g).map (piW t) → h₀.1 = (mat h).map (piW t) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (g, h)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g₀ h₀ (ι φ)

def coef {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (ν : @Measure (Fin n × Fin d → AF F) (borel _)) (Φ : Fn F n d)
    (g : UA σ X.J) : ℂ := ∫ u, om (g, 1) Φ u * star (Φ u) ∂ν

def zint {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (ν : @Measure (Fin n × Fin d → AF F) (borel _))
    (a : G2 σ X → ℝ) (e : UA σ X.J × UA σ X.J →* G2 σ X) (Φ : Fn F n d) (s : ℂ) (g : UA σ X.J) : ℂ :=
  (a (e (g, 1)) : ℂ) ^ (s - ((d : ℂ) - n) / 2) * coef om ν Φ g


variable (σ Y) in
def locGrp (v : Pl F) : Subgroup (UA σ Y.J) := Subgroup.closure (UAt σ Y (evFin F v))

def IntAt (v : Pl F) (g : UA σ Y.J) : Prop :=
  ∀ z ∈ latHat Y, At (evFin F v) z → mat g *ᵥ z ∈ latHat Y ∧ mat g⁻¹ *ᵥ z ∈ latHat Y

def OffAt (v : Pl F) (g : UA σ Y.J) : Prop := (mat g).map (compFin F E v) = 1

def IsSphAt (K : Subgroup (G2 σ Y)) (χ : Chr F E) (v : Pl F) (z : ℂ) (f : G2 σ Y → ℂ) : Prop :=
  ∀ p t, IsPar p t → At (evFin F v) (mat2 p - 1) → ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
    f (p * k) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) * ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z


open Classical in
variable (E) in
def locD (n : ℕ) (v : Pl F) (s : ℂ) : ℂ :=
  ∏ i ∈ Finset.range n, (1 - (if Nonempty (E →ₐ[F] Fv F v) then 1 else -1) ^ (n - (i + 1)) *
    (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * s + (i + 1 : ℕ))))⁻¹

def NormZeta : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → min r' s' = 0 → 1 ≤ n → 1 ≤ d →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ Φ ∈ PolData B M, ∃ (U : Set ℂ) (Z : ℂ → ℂ) (t₀ : ℝ),
      IsOpen U ∧ (∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) ∧ ((d : ℂ) - n) / 2 ∈ U ∧ DifferentiableOn ℂ Z U ∧
      (∀ z : ℂ, t₀ < z.re → z ∈ U ∧ Integrable (zint om ν a e Φ z) M.μ ∧ Z z = ∫ g, zint om ν a e Φ z g ∂M.μ) ∧
      (M.I om Φ = 0 → Z (((d : ℂ) - n) / 2) = 0)

def EulerProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (T : Finset (Pl F)) (μ : Measure (UA σ Y.J)),
    μ.IsHaarMeasure → ∀ (μl : ∀ v, Measure (locGrp σ Y v)), (∀ v, (μl v).IsHaarMeasure ∧ μl v {g | IntAt v g.1} = 1) →
    ∀ (f : UA σ Y.J → ℂ) (fl : Pl F → UA σ Y.J → ℂ), Integrable f μ →
      (∀ v ∉ T, (∀ u ∈ locGrp σ Y v, ∀ g, OffAt v g → f (u * g) = fl v u * f g) ∧ (∀ u ∈ locGrp σ Y v, IntAt v u → fl v u = 1) ∧
        Integrable (fun u : locGrp σ Y v => fl v u.1) (μl v)) →
      Tendsto (fun S : Finset {v : Pl F // v ∉ T} => (∏ v ∈ S, ∫ u, fl v.1 u.1 ∂μl v.1) * ∫ g in {g | ∀ v ∉ T, IntAt v g}, f g ∂μ)
        atTop (𝓝 (∫ g, f g ∂μ))

def LocMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ v,
    ∃ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure ∧ μ {g | IntAt v g.1} = 1

def LocUnr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (χ : Chr F E), IsHecke F E χ →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ K (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure → μ {g | IntAt v g.1} = 1 → ∀ (z : ℂ) f, (n : ℝ) / 2 < z.re →
      IsSphAt K χ v (z + n / 2) f → Integrable (fun u : locGrp σ Y v => f (e (u.1, 1))) μ ∧
        (∫ u, f (e (u.1, 1)) ∂μ) * locD E n v z = ∏ i ∈ Finset.range n, Lv (charFam χ) v (z + n / 2 - i)

def BadFactor : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → min r' s' = 0 → n ≤ d → Even d → ∀ T : Finset (Pl F), T ⊆ B.P → UnrOff χX (T : Set (Pl F)) →
    UnrOff χW (T : Set (Pl F)) → ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → (∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f₀ f₀) →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ Φ ∈ PolData B M,
      (∀ (z : ℂ), ∀ v ∉ T, ∃ f, IsSphAt K χW v (z + n / 2) f ∧ ∀ u ∈ locGrp σ X v, (IntAt v u → f (e (u, 1)) = 1) ∧
        ∀ g, OffAt v g → zint om ν a e Φ z (u * g) = f (e (u, 1)) * zint om ν a e Φ z g) ∧
      Differentiable ℂ (fun z => ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ z g ∂M.μ) ∧
      ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ (((d : ℂ) - n) / 2) g ∂M.μ ≠ 0

def RealInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] [Nontrivial P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P),
    RealQuot B M om p → ∃ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 ∧ ∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f₀ f₀

def DProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (T : Finset (Pl F)), ∃ d : ℂ → ℂ,
    DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re → d z ≠ 0 ∧
      HasProd (fun v : {v : Pl F // v ∉ T} => locD E n v.1 z) (d z)

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}


variable (σ) in
structure Cpt (J : Matrix (Fin n) (Fin n) E) : Prop where
  lc : LocallyCompactSpace (UA σ J)
  sc : SecondCountableTopology (UA σ J)
  t2 : T2Space (UA σ J)
  cnt : Countable (ratU σ J)
  cov : ∃ Ω : Set (UA σ J), IsCompact Ω ∧ ∀ g, ∃ γ ∈ ratU σ J, γ * g ∈ Ω
  hgt : ∃ C : ℝ≥0, ∀ g : UA σ J, qht g ≤ C
  ex : ∃ (μ : Measure (UA σ J)) (D : Set (UA σ J)), μ.IsHaarMeasure ∧ IsFundamentalDomain (ratU σ J) D μ
  fin : ∀ (μ : Measure (UA σ J)) (D : Set (UA σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ J) D μ → μ D < ⊤
  right : ∀ μ : Measure (UA σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant

def CptAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 → Cpt σ Y.J

theorem cptAll_of (h1 : PositivityTheory.ThKEst.GrpTop) (h2 : PositivityTheory.ThKEst.EpsOf) (h3 : PositivityTheory.ThKEst.SiegelAll) (h4 : PositivityTheory.ThKEst.FinVolU)
    (h5 : PositivityTheory.ThKF.Unimod) : CptAll := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0
  obtain ⟨e, -, hr⟩ := h2 F E σ B hB n Y r s hY
  obtain ⟨a1, a2, a3, a4, -, -, -, a5⟩ := h1 F E σ hB.cm n Y.J e
  obtain ⟨fr, g, -, ⟨Ω, hΩ, hc⟩, -⟩ := h3 F E σ hB.cm n Y.J e
  have r0 : fr.r = 0 := by have := hr fr g; omega
  have a0 : ∀ t, fr.a t = 1 := fun t => by
    have : t + t = t := funext fun i => absurd i.2 (by omega)
    have e := g.add t t
    rw [this] at e
    exact left_eq_mul.1 e
  have cov : ∀ x, ∃ γ ∈ ratU σ Y.J, γ * x ∈ Ω := fun x => by
    obtain ⟨γ, hγ, t, -, κ, hκ, e⟩ := hc x
    exact ⟨γ, hγ, by rwa [e, a0, one_mul]⟩
  obtain ⟨C, hC⟩ := a5 Ω hΩ
  obtain ⟨-, u1, u2⟩ : Countable (ratU σ Y.J) ∧ _ ∧ _ := e.1.elim
    (fun h => h5 F E σ hB.cm n Y.J 1 (fun i j => by simp [h]) e.2) fun h => h5 F E σ hB.cm n Y.J (-1) (fun i j => by simp [h]) e.2
  refine ⟨a1, a2, a3, a4, ⟨Ω, hΩ, cov⟩, ⟨C, fun x => ?_⟩, u1, h4 F E σ hB.cm n Y.J e, u2⟩
  obtain ⟨γ, hγ, hx⟩ := cov x
  exact (ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ Y.J)).trans (hC _ hx)

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] {Γ : Subgroup G} [Countable Γ] {D : Set G}

theorem fd_ne (hD : IsFundamentalDomain Γ D μ) : μ D ≠ 0 := hD.measure_ne_zero (NeZero.ne μ)

theorem fd_eq_zero (hD : IsFundamentalDomain Γ D μ) {f : G → ℂ} (hc : Continuous f) (hi : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g)
    (h0 : (fun g => ‖f g‖ ^ 2) =ᵐ[μ.restrict D] 0) : f = 0 := by
  have h1 : μ {g | f g ≠ 0} = 0 := by
    refine hD.measure_zero_of_invariant _ (fun γ => Set.ext fun x => ?_) ?_
    · rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact (congrArg (· ≠ 0) (hi _ (γ⁻¹).2 x)).to_iff
    · rw [← Measure.restrict_apply (isOpen_ne_fun hc continuous_const).measurableSet]
      exact measure_mono_null (fun g hg => by simpa using hg) (ae_iff.1 h0)
  exact (hc.ae_eq_iff_eq μ continuous_const).1 h1

end Gen

variable {J : Matrix (Fin n) (Fin n) E}

instance borelUA : BorelSpace (UA σ J) := ⟨rfl⟩

instance topUA : IsTopologicalGroup (UA σ J) :=
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  Subgroup.instIsTopologicalGroupSubtypeMem _

theorem Cpt.bdd (h : Cpt σ J) {f : UA σ J → ℂ} (hc : Continuous f) (hi : ∀ γ ∈ ratU σ J, ∀ g, f (γ * g) = f g) :
    ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C := by
  obtain ⟨Ω, hΩ, cov⟩ := h.cov
  obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, hg⟩ := cov g
  exact hi γ hγ g ▸ hC _ hg

theorem Cpt.bdd₂ {m : ℕ} {J' : Matrix (Fin m) (Fin m) E} (h : Cpt σ J) (h' : Cpt σ J') {f : UA σ J × UA σ J' → ℂ}
    (hc : Continuous f) (hi : ∀ γ ∈ ratU σ J, ∀ δ ∈ ratU σ J', ∀ g g', f (γ * g, δ * g') = f (g, g')) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨Ω, hΩ, cov⟩ := h.cov
  obtain ⟨Ω', hΩ', cov'⟩ := h'.cov
  obtain ⟨C, hC⟩ := (hΩ.prod hΩ').exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, hγ, hg⟩ := cov x.1
  obtain ⟨δ, hδ, hg'⟩ := cov' x.2
  exact (hi γ hγ δ hδ x.1 x.2 ▸ hC (γ * x.1, δ * x.2) ⟨hg, hg'⟩ :)

theorem Cpt.rapid {Y : Spc F E n} (h : Cpt σ Y.J) {f : UA σ Y.J → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ ratU σ Y.J, ∀ g, f (γ * g) = f g) : IsRapid f := by
  obtain ⟨C, hC⟩ := h.bdd hc hi
  obtain ⟨b, hb⟩ := h.hgt
  exact ⟨hc, hi, fun N => ⟨C * (b : ℝ) ^ N, fun g => mul_le_mul (hC g) (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hb g) N)
    (by positivity) ((norm_nonneg _).trans (hC g))⟩⟩

theorem Cpt.vol_ne (h : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) : μ.real D ≠ 0 := by
  haveI := h.cnt
  exact ENNReal.toReal_ne_zero.2 ⟨fd_ne hD, (h.fin μ D hμ hD).ne⟩

theorem Cpt.eq_zero (h : Cpt σ J) {μ : Measure (UA σ J)} {D : Set (UA σ J)} (hμ : μ.IsHaarMeasure)
    (hD : IsFundamentalDomain (ratU σ J) D μ) {f : UA σ J → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ ratU σ J, ∀ g, f (γ * g) = f g) (h0 : pet μ D f f = 0) : f = 0 := by
  haveI := h.cnt
  obtain ⟨C, hC⟩ := h.bdd hc hi
  have hi2 : IntegrableOn (fun g => ‖f g‖ ^ 2) D μ := Measure.integrableOn_of_bounded (M := C ^ 2) (h.fin μ D hμ hD).ne
    (hc.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun g => by
      rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hC g) 2)
  have e : pet μ D f f = ((∫ g in D, ‖f g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun g => by simpa using Complex.mul_conj' (f g))
  rw [e, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi2] at h0
  exact fd_eq_zero hD hc hi h0

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldA
noncomputable section

namespace GlobalTheory.ThK.Dbl.An

open MeasureTheory Filter Topology

theorem unfold {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ)
    {f : G → ℂ} (hf : Integrable f μ) : ∫ x in D, ∑' γ : Γ, f (γ * x) ∂μ = ∫ x, f x ∂μ := by
  rw [hD.integral_eq_tsum'' f hf]
  refine integral_tsum (fun γ => ((hf.comp_mul_left (γ : G)).aestronglyMeasurable).restrict) ?_
  have := hD.lintegral_eq_tsum'' fun x => ‖f x‖ₑ
  exact (this ▸ hf.2.ne :)

theorem diffOn_integral {X : Type} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {k : ℂ → X → ℂ} (hm : ∀ s ∈ U, AEStronglyMeasurable (k s) μ) (hd : ∀ x, DifferentiableOn ℂ (k · x) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ, ∀ s ∈ K, ∀ x, ‖k s x‖ ≤ C) :
    DifferentiableOn ℂ (fun s => ∫ x, k s x ∂μ) U := by
  intro s₀ h₀
  obtain ⟨r, hr, hU'⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds h₀)
  obtain ⟨C, hC⟩ := hb _ hU' (isCompact_closedBall s₀ r)
  have sub : ∀ s ∈ Metric.ball s₀ (r / 2), Metric.closedBall s (r / 2) ⊆ Metric.closedBall s₀ r := fun s hs =>
    Metric.closedBall_subset_closedBall' (by have := Metric.mem_ball.1 hs; linarith)
  have da : ∀ x, ∀ s ∈ U, HasDerivAt (k · x) (deriv (k · x) s) s := fun x s hs =>
    ((hd x).differentiableAt (hU.mem_nhds hs)).hasDerivAt
  have m' : AEStronglyMeasurable (fun x => deriv (k · x) s₀) μ := by
    classical
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] s₀) (f := fun s x => if s ∈ U then slope (k · x) s₀ s else 0) (fun s => ?_)
      (.of_forall fun x => (hasDerivAt_iff_tendsto_slope.1 (da x s₀ h₀)).congr' ?_)
    · by_cases hs : s ∈ U
      · simp only [if_pos hs, slope_def_module]
        exact ((hm s hs).sub (hm s₀ h₀)).const_smul (s - s₀)⁻¹
      · simp only [if_neg hs]; exact aestronglyMeasurable_const
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h₀)] with s hs using (if_pos hs).symm
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (bound := fun _ => C / (r / 2)) (F := k)
    (F' := fun s x => deriv (k · x) s) (Metric.ball_mem_nhds s₀ (half_pos hr))
    (mem_of_superset (hU.mem_nhds h₀) hm) ?_ m' (.of_forall fun x s hs => ?_) (integrable_const _)
    (.of_forall fun x s hs => da x s (hU' (sub s hs (Metric.mem_closedBall_self (half_pos hr).le))))).2.differentiableAt.differentiableWithinAt
  · exact .of_bound (hm s₀ h₀) C (.of_forall (hC s₀ (Metric.mem_closedBall_self hr.le)))
  · exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr)
      (((hd x).mono ((sub s hs).trans hU')).diffContOnCl_ball subset_rfl)
      fun z hz => hC z (sub s hs (Metric.sphere_subset_closedBall hz)) x

end GlobalTheory.ThK.Dbl.An

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem HasSig.aniso {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) {x : Fin n → ℂ}
    (hx : x ⬝ᵥ M *ᵥ star x = 0) : x = 0 := by
  obtain ⟨e, A, hA⟩ := h
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have h1 : Aᵀ * (M * A.map star * D) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hD, Matrix.fromBlocks_multiply]; simp
  have h2 : A * (M * A.map star * D)ᵀ = 1 := by
    have := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp [e]))).1 h1
    simpa using congrArg Matrix.transpose this
  obtain ⟨y, rfl⟩ : ∃ y, x = A *ᵥ y := ⟨(M * A.map star * D)ᵀ *ᵥ x, by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]⟩
  have h3 : star (A *ᵥ y) = A.map star *ᵥ star y := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [h3, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA] at hx
  have h4 : y ⬝ᵥ star y = 0 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · rwa [show D = -1 by ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | simp [hD, Matrix.one_apply],
        Matrix.neg_mulVec, dotProduct_neg, neg_eq_zero, Matrix.one_mulVec] at hx
    · rwa [show D = 1 by ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | simp [hD, Matrix.one_apply],
        Matrix.one_mulVec] at hx
  open ComplexOrder in rw [dotProduct_self_star_eq_zero.1 h4, Matrix.mulVec_zero]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}


variable (σ) in
def Aniso (J : Matrix (Fin n) (Fin n) E) : Prop := ∀ x, form σ J x x = 0 → x = 0

theorem aniso_of {B : Base F E} {r s : ℕ} (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (h0 : min r s = 0) :
    Aniso σ Y.J := fun x hx => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have e : ((B.emb w).1 ∘ x) ⬝ᵥ Y.J.map (B.emb w).1 *ᵥ star ((B.emb w).1 ∘ x) = 0 := by
    rw [← map_zero (B.emb w).1, ← hx]
    simp [form, Matrix.mulVec, dotProduct, hB.cm.2.2.2]
  have : (B.emb w).1 ∘ x = 0 := hY.elim (fun h => HasSig.aniso (h.sig w) h0 e) fun h => HasSig.aniso (h.sig w) h0 (by
    rw [Matrix.smul_mulVec, dotProduct_smul, e, smul_zero])
  exact funext fun i => (map_eq_zero _).1 (congrFun this i)

instance nontrivAF : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))

instance nontrivAE : Nontrivial (AE F E) :=
  (Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective).nontrivial

abbrev dC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := diagCols (Fin n)

theorem isPar_iff {p : G2 σ Y} {t} : IsPar p t ↔ mat2 p * dC n (AE F E) = dC n (AE F E) * t.1 := Iff.rfl

theorem incM_inj {a b : Type} : Function.Injective (incM F : Matrix a b E → _) :=
  Matrix.map_injective (inclR (F := F) (E := E) (AF F)).injective

theorem incM_diag : incM F (dC n E) = dC n (AE F E) := by
  simp [incM, diagCols, Matrix.fromRows_map]

theorem IsPar.mul {p p' : G2 σ Y} {t t'} (h : IsPar p t) (h' : IsPar p' t') : IsPar (p * p') (t * t') := by
  rw [isPar_iff] at *
  rw [show mat2 (p * p') = mat2 p * mat2 p' from rfl, Units.val_mul, Matrix.mul_assoc, h', ← Matrix.mul_assoc, h, Matrix.mul_assoc]

theorem IsPar.inv {p : G2 σ Y} {t} (h : IsPar p t) : IsPar p⁻¹ t⁻¹ := by
  rw [isPar_iff] at *
  have : mat2 p⁻¹ * (mat2 p * dC n (AE F E)) * (t⁻¹).1 = mat2 p⁻¹ * dC n (AE F E) := by
    rw [h, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [← this, ← Matrix.mul_assoc, show mat2 p⁻¹ * mat2 p = 1 from p.1.inv_mul, Matrix.one_mul]

theorem mem_parabolic_GL2_iff {p : G2 σ Y} : p ∈ par2 σ Y ↔ ∃ t, IsPar p t := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem _ h => exact h
  | one => exact ⟨1, isPar_iff.2 ((Matrix.one_mul _).trans (Matrix.mul_one _).symm)⟩
  | mul _ _ _ _ h h' => exact ⟨_, h.choose_spec.mul h'.choose_spec⟩
  | inv _ _ h => exact ⟨_, h.choose_spec.inv⟩

theorem det_rat {t : GL (Fin n) (AE F E)} {T : Matrix (Fin n) (Fin n) E} (h : t.1 = incM F T) :
    ∃ u : Eˣ, Matrix.GeneralLinearGroup.det t = Units.map (inclR (F := F) (AF F)).toMonoidHom u := by
  have e : (Matrix.GeneralLinearGroup.det t).1 = inclR (F := F) (AF F) T.det := by
    rw [RingHom.map_det]; exact congrArg Matrix.det h
  exact ⟨Units.mk0 T.det fun h0 => (Matrix.GeneralLinearGroup.det t).ne_zero (by rw [e, h0, map_zero]), Units.ext e⟩

theorem par_rat {p : G2 σ Y} {t} (h : IsPar p t) (hp : p ∈ rat2 σ Y) : ∃ T, t.1 = incM F T := by
  obtain ⟨g, hg⟩ := hp
  have e : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  rw [isPar_iff, e, ← incM_diag, ← incM_mul, incM_diag] at h
  refine ⟨(g.1 * dC n E).toRows₁, ?_⟩
  refine Eq.trans ?_ (congrArg Matrix.toRows₁ h).symm
  simp [diagCols, Matrix.fromRows_mul]

theorem detInv_rat {χ : Chr F E} (hχ : IsHecke F E χ) {γ : UA σ Y.J} (h : γ ∈ ratU σ Y.J) : detInv χ γ = 1 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨u, hu⟩ := det_rat (t := γ.1) (T := g.1) (congrArg Units.val hg).symm
  rw [detInv, hu, hχ.2]; simp

theorem detInv_mul (χ : Chr F E) (g h : UA σ Y.J) : detInv χ (g * h) = detInv χ g * detInv χ h := by
  simp [detInv, mul_comm]

theorem norm_detInv (χ : Chr F E) (g : UA σ Y.J) : ‖detInv χ g‖ = 1 := Circle.norm_coe _

theorem continuous_detInv {χ : Chr F E} (hχ : IsHecke F E χ) : Continuous (detInv χ : UA σ Y.J → ℂ) := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  exact continuous_subtype_val.comp ((hχ.1.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)).inv)

theorem absE_det (hJ : Aniso σ Y.J) (h : UA σ Y.J) : absE F E (Matrix.GeneralLinearGroup.det h.1) = 1 := by
  have d0 : Y.J.det ≠ 0 := fun h0 => by
    obtain ⟨v, hv, e⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    exact hv (hJ v (by rw [form, Matrix.dotProduct_mulVec, e, zero_dotProduct]))
  have u : IsUnit (incM F Y.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact d0.isUnit.map _
  have e := congrArg Matrix.det (show (mat h)ᵀ * incM F Y.J * (mat h).map (cA σ) = incM F Y.J from h.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_right_comm, u.mul_eq_right,
    show ((mat h).map (cA σ)).det = sigR (AF F) σ (mat h).det from (RingHom.map_det (sigR (AF F) σ) _).symm] at e
  have e2 : Matrix.GeneralLinearGroup.det h.1 * GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det h.1) = 1 := Units.ext e
  have e3 := congrArg (absE F E) e2
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at e3
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, e3])

theorem IsEmb.par {h : UA σ Y.J} {x : G2 σ Y} (e : IsEmb h h x) : IsPar x h.1 := by
  rw [isPar_iff, e]; simp [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, mat]

theorem IsEmb.rat {h h' : UA σ Y.J} {x : G2 σ Y} (e : IsEmb h h' x) (a : h ∈ ratU σ Y.J) (b : h' ∈ ratU σ Y.J) : x ∈ rat2 σ Y := by
  obtain ⟨g, hg⟩ := a
  obtain ⟨g', hg'⟩ := b
  refine ⟨⟨Matrix.fromBlocks g.1 0 0 g'.1, Matrix.fromBlocks (g⁻¹).1 0 0 (g'⁻¹).1, by simp [Matrix.fromBlocks_multiply],
    by simp [Matrix.fromBlocks_multiply]⟩, Units.ext (Eq.trans ?_ e.symm)⟩
  rw [show mat h = incM F g.1 from (congrArg Units.val hg).symm, show mat h' = incM F g'.1 from (congrArg Units.val hg').symm]
  show incM F (Matrix.fromBlocks g.1 0 0 g'.1) = _
  simp [incM, Matrix.fromBlocks_map]

theorem orbit (hJ : Aniso σ Y.J) {γ : G2 σ Y} (hγ : γ ∈ rat2 σ Y) :
    ∃ δ ∈ ratU σ Y.J, ∀ x, IsEmb 1 δ x → x * γ ∈ par2 σ Y := by
  obtain ⟨g, hg⟩ := hγ
  have e : mat2 γ = incM F g.1 := (congrArg Units.val hg).symm
  have mm : ∀ {a b e : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b e E), (A * B).map σ = A.map σ * B.map σ :=
    fun A B => Matrix.map_mul (f := σ.toRingHom)
  have u : g.1ᵀ * dbl Y.J * g.1.map σ = dbl Y.J := incM_inj (F := F) (by
    have : (mat2 γ)ᵀ * dbl (incM F Y.J) * (mat2 γ).map (cA σ) = dbl (incM F Y.J) := γ.2
    rw [e, incM_conj] at this
    have d : incM F (dbl Y.J) = dbl (incM F Y.J) := by simp [incM, dbl, Matrix.fromBlocks_map, Matrix.map_neg]
    rw [incM_mul, incM_mul, d]; exact this)
  obtain ⟨A, B, hAB⟩ : ∃ A B, g.1 * dC n E = Matrix.fromRows A B := ⟨_, _, (Matrix.fromRows_toRows _).symm⟩
  have iso : Aᵀ * Y.J * A.map σ = Bᵀ * Y.J * B.map σ := by
    have : (g.1 * dC n E)ᵀ * dbl Y.J * (g.1 * dC n E).map σ = 0 := by
      calc _ = (dC n E)ᵀ * (g.1ᵀ * dbl Y.J * g.1.map σ) * (dC n E).map σ := by
            simp only [mm, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = 0 := by rw [u]; exact (isLagr_diagCols σ Y.J).1
    rw [hAB] at this
    simpa [dbl, Matrix.transpose_fromRows, Matrix.fromRows_map, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows,
      ← sub_eq_add_neg, sub_eq_zero] using this
  have fm : ∀ (C : Matrix (Fin n) (Fin n) E) v, form σ Y.J (C *ᵥ v) (C *ᵥ v) = form σ (Cᵀ * Y.J * C.map σ) v v := fun C v => by
    rw [form, form, show (fun i => σ ((C *ᵥ v) i)) = C.map σ *ᵥ fun i => σ (v i) by ext i; simp [Matrix.mulVec, dotProduct],
      Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have inj : ∀ v, A *ᵥ v = 0 → B *ᵥ v = 0 → v = 0 := fun v a b => by
    have : (g⁻¹).1 *ᵥ (g.1 * dC n E) *ᵥ v = 0 := by
      rw [hAB, Matrix.fromRows_mulVec, a, b]; simp
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, dC, diagCols, Matrix.fromRows_mulVec] at this
    exact funext fun i => by simpa using congrFun this (.inl i)
  have un : ∀ C : Matrix (Fin n) (Fin n) E, (∀ v, C *ᵥ v = 0 → v = 0) → IsUnit C := fun C h =>
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit fun h0 => by
      obtain ⟨v, hv, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      exact hv (h v e))
  obtain ⟨a, rfl⟩ := un A fun v h => inj v h (hJ _ (by rw [fm, ← iso, ← fm, h]; simp [form]))
  obtain ⟨b, rfl⟩ := un B fun v h => inj v (hJ _ (by rw [fm, iso, ← fm, h]; simp [form])) h
  have ud : (a * b⁻¹).1ᵀ * Y.J * (a * b⁻¹).1.map σ = Y.J := by
    calc _ = (b⁻¹).1ᵀ * (a.1ᵀ * Y.J * a.1.map σ) * (b⁻¹).1.map σ := by
          simp only [Units.val_mul, mm, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (b * b⁻¹).1ᵀ * Y.J * (b * b⁻¹).1.map σ := by
          rw [iso]; simp only [Units.val_mul, mm, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Y.J := by simp
  refine ⟨⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) (a * b⁻¹), ?_⟩, ⟨_, rfl⟩, fun x hx =>
    mem_parabolic_GL2_iff.2 ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) a, ?_⟩⟩
  · show (incM F (a * b⁻¹).1)ᵀ * incM F Y.J * (incM F (a * b⁻¹).1).map (cA σ) = incM F Y.J
    rw [incM_conj, show (incM F (a * b⁻¹).1)ᵀ = incM F (a * b⁻¹).1ᵀ from rfl, ← incM_mul, ← incM_mul, ud]
  · show mat2 x * mat2 γ * dC n (AE F E) = dC n (AE F E) * incM F a.1
    have : mat2 γ * dC n (AE F E) = incM F (Matrix.fromRows a.1 b.1) := by rw [e, ← incM_diag, ← incM_mul, hAB]
    rw [Matrix.mul_assoc, this, hx]
    show Matrix.fromBlocks 1 0 0 (incM F (a * b⁻¹).1) * (Matrix.fromRows a.1 b.1).map _ = _
    rw [Matrix.fromRows_map, Matrix.fromBlocks_mul_fromRows, dC, diagCols, Matrix.fromRows_mul]
    show Matrix.fromRows (1 * incM F a.1 + 0 * incM F b.1) (0 * incM F a.1 + incM F (a * b⁻¹).1 * incM F b.1) = _
    rw [← incM_mul, ← Units.val_mul, inv_mul_cancel_right]; simp

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.BoxSecX
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

def DblX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ dd om₂ S l, IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l ∧
      (∀ Φ₁ ∈ schA F _, ∀ Φ₂ ∈ schA F _, boxFun Φ₁ (star Φ₂) ∈ schA F _ ∧ ∀ h g g' x, IsEmb g g' x →
        detInv χW g' * thetaSum F (om₂ x (S h (boxFun Φ₁ (star Φ₂)))) = theta om Φ₁ g h * star (theta om Φ₂ g' h) ∧
        detInv χW g' • om₂ x (boxFun Φ₁ (star Φ₂)) = boxFun (om (g, 1) Φ₁) (star (om (g', 1) Φ₂))) ∧
      IsDblCoordX M dd ∧
      ∀ ν : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ c' : ℝ, 0 < c' ∧
        ∀ Ψ₁ ∈ schA F _, ∀ Ψ₂ ∈ schA F _, l (boxFun Ψ₁ (star Ψ₂)) = c' * ∫ u, Ψ₁ u * star (Ψ₂ u) ∂ν

def BoxSecX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M, IsSec K χ (((d : ℂ) - n) / 2) (fun x => l (om x (boxFun Φ₁ (star Φ₂))))

def SWFullX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ U Ê, IsEisCont (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) U Ê ∧ (((d : ℂ) - n) / 2) ∈ U ∧
        ∀ x, Ê (((d : ℂ) - n) / 2) x = (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.NonZero
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
  {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩

theorem res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {m n k : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' n)
    (e : k = m + n) : ResEtaPow K (χ / χ') k := fun x => by
  rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
  split_ifs
  · simp
  · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]

theorem pairV (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    res_div h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem pairV' (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    res_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem split_zero {W : Spc F E (a + a')} {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (X : Chars F E) :
    Split2 (σ := σ) (W := W) W₁ H' X 0 0 0 :=
  ⟨fun _ _ _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩

theorem big_of (hB : NonZeroBot) (hT : TowerB) (hE : EvZero) (hC : CTBigZero) (hS : SchToPol) (hP : PolSch) (hL : LeviEx) (q : ℕ) :
    ∀ (a' : ℕ) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = 0 → G.q = q →
      ∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0 := by
  induction q with
  | zero => exact fun a' G om om' h hp hq => (hB F E σ B a a' G X om om' h hp hq).1
  | succ q ih =>
    intro a' G om om' h hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a' = b + 2 := ⟨a' - 2, by have := h.geo.aBig; omega⟩
    obtain ⟨V, V', W, h', G₁, H, H', c, om₁, om₁', h₁⟩ := hT F E σ B a b G X om om' h (by omega)
    obtain ⟨Φ₁, p1, n1⟩ := ih b G₁ om₁ om₁' h₁ (c.ep.trans hp) (by have : G₁.q + 1 = G.q := c.eq; omega)
    obtain ⟨⟨e, he⟩, he'⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h') _ G₁.V G₁.W H' _ _ G₁.M c.eV c.hH' h₁.geo.hM
    obtain ⟨Φ, p2, rfl⟩ := Submodule.mem_map.1 ((he' e he).ge p1)
    obtain ⟨C, hC0, hc⟩ := hC F E σ B a b _ G₁ H H' c e he
    by_contra hn
    push Not at hn
    have z : G.M.I om Φ = 0 := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h) (by omega) hn Φ
      (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV h') Φ p2)
    refine n1 (funext fun g => ?_)
    obtain ⟨m, hm⟩ := hL F E σ B _ _ _ _ H' _ _ _ _ h.base h'.geo.hW c.hH' g
    have := hc X om om' om₁ om₁' h' h₁ Φ p2 0 0 (by
      show Split2 _ _ _ (G.M.I om Φ) 0 0
      rw [z]; exact split_zero _ _ _) g m hm 1
    have o : om (1, 1) Φ = Φ := DFunLike.congr_fun (map_one om) Φ
    erw [o] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hC0

theorem small_of (hB : NonZeroBot) (hT : TowerA) (hE : EvZero) (hC : CTSmallZero) (hS : SchToPol) (hP : PolSch) (hL : LeviEx)
    (hZ : SplitEx) (p : ℕ) :
    ∀ (a : ℕ) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = p → G.q = 0 →
      ∃ Φ ∈ PolData B G.M', G.M'.I om' Φ ≠ 0 := by
  induction p with
  | zero => exact fun a G om om' h hp hq => (hB F E σ B a a' G X om om' h hp hq).2
  | succ p ih =>
    intro a G om om' h hp hq
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by have := h.geo.aBig; have := h.geo.lt; omega⟩
    obtain ⟨V, V', W, h', G₁, H, H', c, om₁, om₁', h₁⟩ := hT F E σ B b a' G X om om' h hq (by omega)
    obtain ⟨Φ₁, p1, n1⟩ := ih b G₁ om₁ om₁' h₁ (by have : G₁.p + 1 = G.p := c.ep; omega) c.q1
    obtain ⟨⟨e, he⟩, he'⟩ := hE F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h') _ G₁.V' G₁.W H' _ _ G₁.M' c.eV c.hH' h₁.geo.hM'
    obtain ⟨Φ, p2, rfl⟩ := Submodule.mem_map.1 ((he' e he).ge p1)
    obtain ⟨C, hC0, hc⟩ := hC F E σ B b a' _ G₁ H H' c e he
    by_contra hn
    push Not at hn
    have z : G.M'.I om' Φ = 0 := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h) (by omega) hn Φ
      (hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV' h') Φ p2)
    refine n1 (funext fun g => ?_)
    obtain ⟨m, hm⟩ := hL F E σ B _ _ _ _ H' _ _ _ _ h.base h'.geo.hW c.hH' g
    obtain ⟨fa, s1, s2⟩ := hc X om om' om₁ om₁' h' h₁ Φ p2
    have s3 : Split2 G₁.W H' X (G.M'.I om' Φ) fa 0 := s1
    rw [z] at s3
    have i0 : (reG G V V' W).M.I om 0 = 0 := funext fun x => by simp [Model.I, theta, thetaSum]
    have fz : fa = 0 := congrArg Prod.fst (((hZ F E σ B _ _ (reG G V V' W) X om om' h' _ G₁.W H' _ _ c.hH').1 0 (zero_mem _)).unique
      (y₁ := (fa, 0)) (y₂ := (0, 0)) (by rw [i0]; exact s3) (by rw [i0]; exact split_zero _ _ _))
    have := s2 g m hm 1
    have o : om' (1, 1) Φ = Φ := DFunLike.congr_fun (map_one om') Φ
    erw [fz, o] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hC0

theorem nonZeroAn_of (hB : NonZeroBot) (hA : TowerA) (hT : TowerB) (hE : EvZero) (hC : CTBigZero) (hC' : CTSmallZero)
    (hS : SchToPol) (hP : PolSch) (hL : LeviEx) (hZ : SplitEx) (hO : ToSo) : NonZeroAn := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  refine ⟨fun hp => big_of hB hT hE hC hS hP hL _ a' G om om' h hp rfl, fun hq => ?_⟩
  obtain ⟨Φ, p1, n1⟩ := small_of hB hA hE hC' hS hP hL hZ _ a G om om' h rfl hq
  obtain ⟨Ψ, p2, e⟩ := hO F E σ B a a' G X om om' h hq Φ p1
  exact ⟨Ψ, p2, e ▸ n1⟩

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.OffOpenAlt
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def OffOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsSkew σ B r s →
    ∀ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, (∀ h h', IsEmb h h' (e (h, h'))) → ∀ γ ∈ rat2 σ Y,
      (¬ ∃ δ ∈ ratU σ Y.J, γ * (e (1, δ))⁻¹ ∈ par2 σ Y) →
      ∃ U : Submodule E (Fin n → E), U ≠ ⊥ ∧ (∀ u ∈ U, ∀ u' ∈ U, form σ Y.J u u' = 0) ∧
        (∀ m ∈ PositivityTheory.ThKEnd.unipU σ Y U, ∃ t, IsPar (γ * e (1, m) * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
          Matrix.GeneralLinearGroup.det m.1 = 1) ∧
        ∀ δ ∈ ratU σ Y.J, γ * e (1, δ) * γ⁻¹ ∈ par2 σ Y → ∀ m ∈ PositivityTheory.ThKEnd.unipU σ Y U, δ * m * δ⁻¹ ∈ PositivityTheory.ThKEnd.unipU σ Y U

def HtEmb : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n),
    ∃ C : ℝ≥0, (∀ h h' x, IsEmb (σ := σ) (Y := Y) h h' x → ht2 x ≤ C * (ht h * ht h')) ∧
      (∀ h h' : UA σ Y.J, ht (h * h') ≤ C * (ht h * ht h')) ∧ ∀ h : UA σ Y.J, 1 ≤ ht h

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.SWFull
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem mero_eq {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) {e g : ℂ → ℂ} (he : MeromorphicOn e Set.univ)
    (hg : DifferentiableOn ℂ g U) {t : ℝ} (h : ∀ s : ℂ, t < s.re → s ∈ U ∧ e s = g s) {s : ℂ} (hs : s ∈ U) (hc' : ContinuousAt e s) :
    e s = g s := by
  have ha := hg.analyticOnNhd hU
  have m : MeromorphicOn (e - g) U := (he.mono_set (Set.subset_univ _)).sub ha.meromorphicOn
  have h1 : t < ((t + 1 : ℝ) : ℂ).re := by simp
  have z : meromorphicOrderAt (e - g) s = ⊤ := by
    by_contra hne
    refine m.meromorphicOrderAt_ne_top_of_isPreconnected hc hs (h _ h1).1 hne (meromorphicOrderAt_eq_top_iff.2 ?_)
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1)] with z hz
    exact sub_eq_zero.2 (h z hz).2
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] s) (hc'.mono_left nhdsWithin_le_nhds)
    ((ha s hs).continuousAt.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 z] with z hz using sub_eq_zero.1 hz

theorem contAt_of_sphere {X : Type} [TopologicalSpace X] {g : ℂ → X → ℂ} {s₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ∀ x, DiffContOnCl ℂ (g · x) (Metric.ball s₀ ρ))
    (hc : ContinuousOn (fun y : ℂ × X => g y.1 y.2) (Metric.sphere s₀ ρ ×ˢ Set.univ)) (x₀ : X) :
    ContinuousAt (fun y : ℂ × X => g y.1 y.2) (s₀, x₀) := by
  have c0 : ContinuousAt (g · x₀) s₀ := ((hd x₀).differentiableAt Metric.isOpen_ball (Metric.mem_ball_self hρ)).continuousAt
  have : Tendsto (fun y : ℂ × X => g y.1 y.2 - g y.1 x₀) (𝓝 (s₀, x₀)) (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have c1 : Continuous fun y : X × Metric.sphere s₀ ρ => ‖g y.2 y.1 - g y.2 x₀‖ :=
      ((hc.comp_continuous (f := fun y : X × Metric.sphere s₀ ρ => (y.2.1, y.1)) (by fun_prop) fun y => ⟨y.2.2, trivial⟩).sub
        (hc.comp_continuous (f := fun y : X × Metric.sphere s₀ ρ => (y.2.1, x₀)) (by fun_prop) fun y => ⟨y.2.2, trivial⟩)).norm
    have e1 : ∀ᶠ x in 𝓝 x₀, ∀ z ∈ (Set.univ : Set (Metric.sphere s₀ ρ)), ‖g z x - g z x₀‖ < ε / 2 :=
      isCompact_univ.eventually_forall_of_forall_eventually fun z _ =>
        (isOpen_lt c1 continuous_const).mem_nhds (by simpa using hε)
    filter_upwards [prod_mem_nhds (Metric.ball_mem_nhds s₀ hρ) e1] with y hy
    rw [dist_zero_right]
    refine (Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball ((hd y.2).sub (hd x₀)) (C := ε / 2)
      (fun z hz => ?_) (subset_closure hy.1)).trans_lt (half_lt_self hε)
    rw [frontier_ball _ hρ.ne'] at hz
    exact (hy.2 ⟨z, hz⟩ trivial).le
  have h2 := this.add (c0.tendsto.comp continuous_fst.continuousAt)
  simpa [ContinuousAt] using h2

theorem IsEisCont.update {f : ℂ → G2 σ Y → ℂ} {U : Set ℂ} {Ê : ℂ → G2 σ Y → ℂ} (h : IsEisCont f U Ê) {s₀ : ℂ} {k : ℕ}
    (hr : IsRegAt Ê s₀ k) {val : G2 σ Y → ℂ} (hv : EisValueAt f s₀ val) :
    IsEisCont f (insert s₀ U) (Function.update Ê s₀ val) := by
  obtain ⟨r, H, r0, hH, -, -, C, N, hC⟩ := hr
  obtain ⟨t, half⟩ := h.half
  have op : IsOpen (insert s₀ U) := isOpen_iff_mem_nhds.2 fun s hs => hs.elim
    (fun e => e ▸ insert_mem_nhds_iff.2 (h.disc s)) fun hs => mem_of_superset (h.isOpen.mem_nhds hs) (Set.subset_insert _ _)
  have ev : ∀ s ≠ s₀, ∀ᶠ z in 𝓝 s, Function.update Ê s₀ val z = Ê z := fun s hs => by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz using Function.update_of_ne hz _ _
  have hol : ∀ x, DifferentiableOn ℂ (Function.update Ê s₀ val · x) (insert s₀ U) := fun x s hs => by
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases e0 : s = s₀
    · obtain ⟨e, he, ⟨t', h1⟩, h2, h3⟩ := hv x
      subst e0
      refine h2.differentiableAt.congr_of_eventuallyEq ?_
      filter_upwards [h2.eventually_analyticAt, op.mem_nhds hs] with z hz hz'
      by_cases e1 : z = s
      · rw [e1, Function.update_self, h3]
      · rw [Function.update_of_ne e1]
        exact (mero_eq h.isOpen h.conn he (h.hol x) (t := max t t') (fun s hs => ⟨(half s (max_lt_iff.1 hs).1).1,
          (h1 s (max_lt_iff.1 hs).2).unique ((half s (max_lt_iff.1 hs).1).2 x)⟩)
          (hz'.resolve_left e1) hz.continuousAt).symm
    · exact ((h.hol x).differentiableAt (h.isOpen.mem_nhds (hs.resolve_left e0))).congr_of_eventuallyEq
        ((ev s e0).mono fun z hz => congrFun hz x)
  obtain ⟨ρ, ρ0, hρ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (inter_mem (op.mem_nhds (Set.mem_insert _ _)) (Metric.ball_mem_nhds s₀ r0))
  have dc : ∀ x, DiffContOnCl ℂ (Function.update Ê s₀ val · x) (Metric.ball s₀ ρ) := fun x =>
    (hol x).diffContOnCl_ball fun z hz => (hρ hz).1
  have sp : ∀ z ∈ Metric.sphere s₀ ρ, z ≠ s₀ := fun z hz => Metric.ne_of_mem_sphere hz ρ0.ne'
  have ca : ∀ s ∈ U, s ≠ s₀ → ∀ x, ContinuousAt (fun y : ℂ × G2 σ Y => Function.update Ê s₀ val y.1 y.2) (s, x) := fun s hs e x =>
    (h.cont.continuousAt (prod_mem_nhds (h.isOpen.mem_nhds hs) univ_mem)).congr
      ((continuous_fst.continuousAt.eventually (ev s e)).mono fun y hy => (congrFun hy y.2).symm)
  refine ⟨op, h.conn.subset_closure (Set.subset_insert _ _) (Set.insert_subset ?_ subset_closure),
    fun s => (h.disc s).mono fun z hz => .inr hz, ⟨max t s₀.re, fun s hs => ⟨.inr (half s (max_lt_iff.1 hs).1).1, fun x => ?_⟩⟩, hol, fun y hy => ?_, fun s hs => ?_⟩
  · exact mem_closure_iff_frequently.2 ((h.disc s₀).frequently.filter_mono nhdsWithin_le_nhds)
  · rw [Function.update_of_ne fun e => (max_lt_iff.1 hs).2.ne (by rw [e])]; exact (half s (max_lt_iff.1 hs).1).2 x
  · refine ContinuousAt.continuousWithinAt ?_
    by_cases e0 : y.1 = s₀
    · rw [show y = (s₀, y.2) from Prod.ext e0 rfl]
      exact contAt_of_sphere ρ0 dc (fun z hz => (ca z.1 ((hρ (Metric.sphere_subset_closedBall hz.1)).1.resolve_left (sp _ hz.1))
        (sp _ hz.1) z.2).continuousWithinAt) _
    · exact ca y.1 (hy.1.resolve_left e0) e0 y.2
  · by_cases e0 : s = s₀
    · subst e0
      refine ⟨ρ, C / ρ ^ k, N, ρ0, fun z hz x => Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball (dc x)
        (fun w hw => ?_) (subset_closure hz)⟩
      rw [frontier_ball _ ρ0.ne'] at hw
      have b := (hρ (Metric.sphere_subset_closedBall hw)).2
      have := hC w b x
      rw [hH w b (sp w hw), norm_mul, norm_pow, mem_sphere_iff_norm.1 hw] at this
      rw [Function.update_of_ne (sp w hw), div_mul_eq_mul_div, le_div_iff₀' (pow_pos ρ0 k)]
      exact this
    · obtain ⟨ε, C', N', ε0, hb⟩ := h.grow s (hs.resolve_left e0)
      obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (inter_mem (ev s e0) (Metric.ball_mem_nhds s ε0))
      exact ⟨δ, C', N', δ0, fun z hz x => by rw [(hδ hz).1]; exact hb z (hδ hz).2 x⟩

theorem swFull_of (h1 : SWAniso) (h2 : EisContinues) (h3 : BoxSec) : SWFull := by
  intro F E _ _ _ _ _ σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2
  obtain ⟨U, Ê, hE, hR⟩ := h2 F E σ B n Y r' s' hB hn (.inr hY) χ hχ m hr K a hK ha _ _
    (h3 F E σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2)
  obtain ⟨k, hk⟩ := hR (((m : ℂ) - n) / 2)
  exact ⟨_, _, hE.update hk (h1 F E σ B m n A Y M r s r' s' hB hm hn hA h0 hY hM χ hχ hr dd om S l c1 c2 K a hK ha Φ₁ p1 Φ₂ p2),
    Set.mem_insert _ _, fun x => by rw [Function.update_self]⟩

end GlobalTheory.ThK.Dbl

end
end
