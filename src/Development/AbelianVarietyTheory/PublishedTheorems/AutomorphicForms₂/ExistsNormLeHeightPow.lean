module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDecay

variable {D : D7}

def quotHeight (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (g : GA D V) : NNReal :=
  ⨅ γ : GQ V, height θ V ((γ : GA D V) * g)

def IsRapidDecay (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ g : GA D V, ‖φ g‖ * (quotHeight θ V g : ℝ) ^ N ≤ C

end GlobalTheory.CuspDecay

namespace GlobalTheory.Published

def CuspRapidDecay : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (e : LieInf V → GA D V), IsExpFam θ V e →
      ∀ φ : GA D V → ℂ, IsAutFun V φ → IsSmoothInf V e φ → IsUnifModerate θ V e φ → IsCuspFun V φ →
        GlobalTheory.CuspDecay.IsRapidDecay θ V φ

end GlobalTheory.Published

namespace GlobalTheory.CuspDecay

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem quotHeight_le (g : GA D V) {γ : GA D V} (hγ : γ ∈ GQ V) : quotHeight θ V g ≤ height θ V (γ * g) :=
  ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : GQ V)

theorem one_le_quotHeight (g : GA D V) : 1 ≤ quotHeight θ V g :=
  le_ciInf fun _ => one_le_height θ V _

theorem exists_height_le (g : GA D V) : ∃ γ ∈ GQ V, height θ V (γ * g) ≤ 2 * quotHeight θ V g := by
  have h : quotHeight θ V g < 2 * quotHeight θ V g :=
    lt_mul_of_one_lt_left (zero_lt_one.trans_le (one_le_quotHeight g)) one_lt_two
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt h
  exact ⟨γ, γ.2, hγ.le⟩

theorem IsRapidDecay.bounded {φ : GA D V → ℂ} (h : IsRapidDecay θ V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := h 0
  exact ⟨C, fun g => by simpa using hC g⟩

theorem IsRapidDecay.mul_bounded {φ ψ : GA D V → ℂ} (h : IsRapidDecay θ V φ)
    (hψ : ∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) {N : ℕ} {C : ℝ} (hC : ∀ g, ‖ψ g‖ ≤ C * (height θ V g : ℝ) ^ N) :
    ∃ B : ℝ, ∀ g, ‖ψ g‖ * ‖φ g‖ ≤ B := by
  obtain ⟨C', hC'⟩ := h N
  refine ⟨|C| * 2 ^ N * C', fun g => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
  have h2 : ‖ψ g‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ)) ^ N := by
    rw [← hψ γ hγ g]
    exact (hC _).trans (mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N)
      (pow_nonneg (NNReal.coe_nonneg _) N) (abs_nonneg _))
  calc ‖ψ g‖ * ‖φ g‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ)) ^ N * ‖φ g‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = |C| * 2 ^ N * (‖φ g‖ * (quotHeight θ V g : ℝ) ^ N) := by rw [mul_pow]; ring
    _ ≤ |C| * 2 ^ N * C' := mul_le_mul_of_nonneg_left (hC' g) (by positivity)

theorem exists_norm_le_height_pow (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) :
    ∃ (N : ℕ) (C : ℝ), ∀ g, ‖φ g‖ ≤ C * (height θ V g : ℝ) ^ N := by
  obtain ⟨-, -, h1⟩ := (GlobalTheory.SmoothForms.isAutFunSm_iff hθ V φ).1 h
  obtain ⟨⟨e, he⟩, h2⟩ := h1 θ hθ
  obtain ⟨-, -, N, hN⟩ := h2 e he
  obtain ⟨C, hC⟩ := hN []
  exact ⟨N, C, hC⟩

theorem isRapidDecay_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : IsRapidDecay θ V φ := by
  obtain ⟨ha, -, h1⟩ := (GlobalTheory.SmoothForms.isAutFunSm_iff hθ V φ).1 h
  obtain ⟨⟨e, he⟩, h2⟩ := h1 θ hθ
  obtain ⟨hs, -, hg⟩ := h2 e he
  exact hP D θ hθ V e he φ ha hs hg hc

theorem bounded_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {φ : GA D V → ℂ}
    (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C :=
  (isRapidDecay_of_cuspForm hP hθ h hc).bounded

theorem mul_bounded_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {ψ φ : GA D V → ℂ}
    (hψ : IsAutFunSm θ V ψ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) : ∃ B : ℝ, ∀ g, ‖ψ g‖ * ‖φ g‖ ≤ B := by
  obtain ⟨N, C, hC⟩ := exists_norm_le_height_pow hθ hψ
  exact (isRapidDecay_of_cuspForm hP hθ h hc).mul_bounded hψ.left hC

theorem measure_lt_top (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : μ 𝓕 < ⊤ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  exact hV D.host.F D.host.E D.sp.cm.sig h1 V.rank V.gram (h2 V) μ hμ 𝓕 h𝓕

theorem integrableOn_star_mul (hP : GlobalTheory.Published.CuspRapidDecay) (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (hθ : IsInfFam θ)
    (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {ψ φ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) (h : IsAutFunSm θ V φ) (hc : IsCuspFun V φ) :
    IntegrableOn (fun g => star (ψ g) * φ g) 𝓕 μ := by
  have : BorelSpace (GA D V) := ⟨rfl⟩
  obtain ⟨B, hB⟩ := mul_bounded_of_cuspForm hP hθ hψ h hc
  refine Measure.integrableOn_of_bounded (M := B) (measure_lt_top hV V μ 𝓕 hμ h𝓕).ne
    ((hψ.cont.star.mul h.cont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_mul, norm_star]
  exact hB g

end GlobalTheory.CuspDecay

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.Whittaker

namespace GlobalTheory.LocLanglands

section Tate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def unitFilt (a : ℕ) : Set kˣ :=
  {x | valuation k (x : k) = 1 ∧ valuation k ((x : k) - 1) ≤ uniformizer k ^ a}

def HasExponent (χ : kˣ →* ℂˣ) (a : ℕ) : Prop :=
  (∀ x ∈ unitFilt k a, χ x = 1) ∧ ∀ b < a, ∃ x ∈ unitFilt k b, χ x ≠ 1

def IsShellReps (c : kˣ) (a : ℕ) (R : Finset kˣ) : Prop :=
  (∀ r ∈ R, ord k r = ord k c - a) ∧
    ∀ y : kˣ, ord k y = ord k c - a → ∃! r : kˣ, r ∈ R ∧ valuation k ((y : k) - r) ≤ valuation k (c : k)

def IsTateEps (ψ : AddChar k Circle) (χ : kˣ →* ℂˣ) (e : ℂ) : Prop :=
  ∃ (c : kˣ) (a : ℕ) (R : Finset kˣ), HasConductor ψ c ∧ HasExponent χ a ∧ IsShellReps c a R ∧
    e = (resCard k : ℂ) ^ (-(a : ℂ) / 2) * ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ)

theorem HasExponent.unique {χ : kˣ →* ℂˣ} {a b : ℕ} (ha : HasExponent χ a) (hb : HasExponent χ b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · obtain ⟨x, hx, hx'⟩ := hb.2 a h
    exact absurd (ha.1 x hx) hx'
  · exact h
  · obtain ⟨x, hx, hx'⟩ := ha.2 b h
    exact absurd (hb.1 x hx) hx'

end Tate

section Pairs

theorem antidiag_mul_self (n : ℕ) (R : Type) [CommRing R] :
    (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0) *
      (Matrix.of fun i j : Fin n => if j = i.rev then (1 : R) else 0) = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev (fun b _ hb => by simp [hb]) (by simp)]
  simp [Matrix.one_apply, eq_comm]

def longElt (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R :=
  ⟨Matrix.of fun i j => if j = i.rev then 1 else 0, Matrix.of fun i j => if j = i.rev then 1 else 0,
    antidiag_mul_self n R, antidiag_mul_self n R⟩

def tilde {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : GL (Fin n) R :=
  longElt n R * GlobalTheory.CuspRep.invT n R g

def corner {m : ℕ} {R : Type} [CommRing R] (g : GL (Fin m) R) : GL (Fin (m + 1)) R :=
  emb₂ R (stdSum (rfl : m + 1 = m + 1)) (g, 1)

variable {k : Type} [Field k] [TopologicalSpace k] {m : ℕ}

def IsTestFun (f : GL (Fin m) k → ℂ) : Prop :=
  (∀ u ∈ unipB k (Fin m), ∀ g, f (u * g) = f g) ∧ IsLocallyConstant f ∧
    ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c

def IsInvIntegral (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ f, IsTestFun f → ∀ x, I (fun g => f (g * x)) = I f

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def HasPairEps (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin (m + 1)) k) V)
    (τ : Representation ℂ (GL (Fin m) k) V') (e : ℂ) : Prop :=
  ∀ ω : kˣ →* ℂˣ, HasCentralChar τ ω →
    ∀ (l : Module.Dual ℂ V) (l' : Module.Dual ℂ V'), IsFunctional ψ π l → IsFunctional ψ⁻¹ τ l' →
      ∀ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I → ∀ (v : V) (v' : V'),
        I (fun g => l (π (tilde (corner g)) v) * l' (τ (tilde g) v')) =
          (ω (-1) : ℂ) ^ m * e * I (fun g => l (π (corner g) v) * l' (τ g v'))

end Pairs

section Galois

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.HeckeGal ReciprocityTheory.Neutral.Bridge.HCFR
open Neutral.B1 hiding G Dec IsPlaceOver

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

structure IsLocalArtin {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) : Prop where
  surj : Function.Surjective a
  cont : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ)
  ord_eq : ∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ
  factor : ∀ ξ : Weil h →* ℂˣ, WeilDeligne.IsSmooth ξ → ∃ χ, IsSmoothChar χ ∧ ξ = χ.comp a
  glob : ∀ art : Ideles E →* Gab E Ω, IsGlobalArtin art →
    ∀ σ : Weil h, art (localIdele E w (a σ)) = toAb E Ω σ

theorem IsLocalArtin.smooth {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
    {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ}
    (ha : IsLocalArtin h a) {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    WeilDeligne.IsSmooth (χ.comp a) :=
  IsOpen.preimage ha.cont hχ

section Ind

variable {K L : Type} [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}


variable (L) in
def IsLocalExt (h : IsPlaceOver A v) : Prop :=
  ∀ σ : G K Ω, ∃ τ : Weil h, ∀ x : L, (τ : G K Ω) (algebraMap L Ω x) = σ (algebraMap L Ω x)

def Induces {h' : IsPlaceOver A v'} {h : IsPlaceOver A v} (x : WD h') (y : WD h) : Prop :=
  ∃ (m n : ℕ) (a : WDRep h' (Fin m → ℂ)) (b : WDRep h (Fin n → ℂ)) (j : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)),
    WD.mk a = x ∧ WD.mk b = y ∧ n = Module.finrank K L * m ∧
    (∀ (σ' : Weil h') (σ : Weil h), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ u, j (a.ρ σ' u) = b.ρ σ (j u)) ∧
    Submodule.span ℂ (Set.range fun p : Weil h × (Fin m → ℂ) => b.ρ p.1 (j p.2)) = ⊤


omit [IsAlgClosure K Ω] in
theorem isLocalExt_self (h : IsPlaceOver A v) : IsLocalExt K h := fun σ => ⟨1, fun x => by simp⟩

theorem induces_self {h : IsPlaceOver A v} (x : WD h) : Induces x x := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  refine ⟨n, n, a, a, LinearMap.id, rfl, rfl, by simp, fun σ' σ hσ u => ?_, ?_⟩
  · rw [show σ = σ' from Subtype.ext (AlgEquiv.ext hσ)]; rfl
  · exact eq_top_iff.2 fun u _ => Submodule.subset_span ⟨(1, u), by simp⟩

end Ind


variable (A) in
abbrev EpsFamily : Type 1 :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v), AddChar (v.adicCompletion L) Circle → WD h → ℂˣ

structure IsDeligneEps (ε : EpsFamily A) : Prop where
  add : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion L) Circle), Continuous ψ → ψ ≠ 1 →
    ∀ x y : WD h, ε L v h ψ (x.lpSum y) = ε L v h ψ x * ε L v h ψ y
  char : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
    (h : IsPlaceOver A v) (ψ : AddChar (v.adicCompletion L) Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (a : Weil h →* (v.adicCompletion L)ˣ) (ha : IsLocalArtin h a) (χ : (v.adicCompletion L)ˣ →* ℂˣ)
      (hχ : IsSmoothChar χ), IsTateEps ψ χ (ε L v h ψ (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)))
  ind : ∀ (K L : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'),
    IsLocalExt L h →
    ∀ (ψ : AddChar (v.adicCompletion K) Circle) (ψ' : AddChar (v'.adicCompletion L) Circle),
      Continuous ψ → ψ ≠ 1 → Continuous ψ' →
      (∀ z : L, ψ' (algebraMap L _ z) = ψ (algebraMap K _ (Algebra.trace K L z))) →
      ∀ (x₁ x₂ : WD h') (y₁ y₂ : WD h), Induces x₁ y₁ → Induces x₂ y₂ → x₁.lpDim = x₂.lpDim →
        ε K v h ψ y₁ * ε L v' h' ψ' x₂ = ε K v h ψ y₂ * ε L v' h' ψ' x₁

end Galois

end GlobalTheory.LocLanglands
end
end
