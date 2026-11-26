module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveLineOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbSplitPt

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.GaugeNormPower

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section closed

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem aa_closed (P : (Mat k r → E) → Prop)
    (hRd : ∀ (X : Mat k r) (f : Mat k r → E), inLie k r X → P f → P (RdV X f))
    (hadd : ∀ f₁ f₂ : Mat k r → E, P f₁ → P f₂ → P (fun x => f₁ x + f₂ x))
    (hmul : ∀ (φ : Mat k r → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → ∀ f : Mat k r → E, P f → P (fun x => φ x • f x))
    (hzero : P (fun _ => 0)) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f : Mat k r → E) (hf : P f) :
    P (C3.AAop k r m hm u f) :=
  _root_.UpperTheory.Reformulated.B.Qj20.aa_closed P hRd hadd hmul hzero m hm u f hf

theorem loc_add' {m : ℕ∞} {f₁ f₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc m f₁ g) (h₂ : Loc m f₂ g) :
    Loc m (fun x => f₁ x + f₂ x) g := by
  obtain ⟨U₁, f₁', hU₁, hg₁, hf₁, he₁⟩ := h₁
  obtain ⟨U₂, f₂', hU₂, hg₂, hf₂, he₂⟩ := h₂
  exact ⟨U₁ ∩ U₂, fun x => f₁' x + f₂' x, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hf₁.mono Set.inter_subset_left).add (hf₂.mono Set.inter_subset_right),
    fun x hx hxG => by show f₁ x + f₂ x = f₁' x + f₂' x; rw [he₁ x hx.1 hxG, he₂ x hx.2 hxG]⟩

theorem loc_smulFun {m : ℕ∞} (φ : Mat k r → ℂ) {V : Set (Mat k r)} (hV : IsOpen V)
    (hφ : ContDiffOn ℝ (m : WithTop ℕ∞) φ V) {f : Mat k r → E} {g : Mat k r} (hgV : g ∈ V) (h : Loc m f g) :
    Loc m (fun x => φ x • f x) g := by
  obtain ⟨U, f', hU, hgU, hf, he⟩ := h
  exact ⟨U ∩ V, fun x => φ x • f' x, hU.inter hV, ⟨hgU, hgV⟩,
    (hφ.mono Set.inter_subset_right).smul (hf.mono Set.inter_subset_left),
    fun x hx hxG => by show φ x • f x = φ x • f' x; rw [he x hx.1 hxG]⟩

theorem loc_zero' {m : ℕ∞} {g : Mat k r} : Loc m (fun _ => (0 : E)) g :=
  ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem loc_AAop {f : Mat k r → E} {g : Mat k r} (h : Loc ⊤ f g) (m : ℕ) (hm : m ≤ r) (u : ℂ) :
    Loc ⊤ (C3.AAop k r m hm u f) g := by
  refine aa_closed (fun f => Loc ⊤ f g) (fun X f hX hf => ?_) (fun _ _ h₁ h₂ => loc_add' h₁ h₂)
    (fun φ hφ f hf => loc_smulFun φ isOpen_univ hφ.contDiffOn (Set.mem_univ g) hf) loc_zero' m hm u f h
  have hf' : Loc ((⊤ : ℕ∞) + 1) f g := by rw [top_add]; exact hf
  exact loc_RdV hX hf'

theorem zero_AAop {f : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) (h : ∀ x ∈ U, x ∈ GV k r → f x = 0)
    (m : ℕ) (hm : m ≤ r) (u : ℂ) : ∀ x ∈ U, x ∈ GV k r → C3.AAop k r m hm u f x = 0 := by
  refine aa_closed (fun f => ∀ x ∈ U, x ∈ GV k r → f x = 0) (fun X f hX hf => ?_)
    (fun f₁ f₂ h₁ h₂ x hx hxG => by simp [h₁ x hx hxG, h₂ x hx hxG])
    (fun φ _ f hf x hx hxG => by simp [hf x hx hxG]) (fun _ _ _ => rfl) m hm u f h
  intro x hx hxG
  rw [rdV_congr (f₂ := fun _ => (0 : E)) hU hx hxG hX (fun y hy hyG => hf y hy hyG)]
  simp [RdV]

end closed

end Formalism.FourierDecayAlt.P.GaugeNormPower

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.GaugeNormPower

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem raising_compact_support : PBN.AACpt := by
  intro k r Wp Wq _ _ _ _ Bs F y hF
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  have hGc : Continuous fun g : Mat k r => Gf k r Bs.z Bs.z' g :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  have hvan : ∀ U : Set (Mat k r), IsOpen U → (∀ x ∈ U, x ∈ GV k r → F x = 0) →
      ∀ x ∈ U, x ∈ GV k r → PBN.aaTop Bs y F x = 0 := by
    intro U hU hF0 x hx hxG
    have := zero_AAop hU hF0 r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) x hx hxG
    simp only [PBN.aaTop, this, smul_zero]
  have hUε : IsOpen {x : Mat k r | Gf k r Bs.z Bs.z' x < ε} := isOpen_lt hGc continuous_const
  have hFε : ∀ x ∈ {x : Mat k r | Gf k r Bs.z Bs.z' x < ε}, x ∈ GV k r → F x = 0 := by
    intro x hx hxG
    by_contra h
    exact absurd (hG x hxG h) (not_le.mpr hx)
  refine ⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hlt : Gf k r Bs.z Bs.z' g₀ < ε
    · exact ⟨_, fun _ => 0, hUε, hlt, contDiffOn_const, fun x hx hxG => hvan _ hUε hFε x hx hxG⟩
    · push Not at hlt
      have hD : Dmin k r Bs.z Bs.z' g₀ (Fin.last (r + 1)) ≠ 0 := by
        intro h0
        have h1 : 0 ≤ Tz k r Bs.z * Tz k r Bs.z' * Complex.normSq (Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩) :=
          mul_nonneg (mul_pos Bs.T_pos Bs.T'_pos).le (Complex.normSq_nonneg _)
        simp only [Gf, h0, map_zero] at hlt
        linarith
      have hDc : ContDiff ℝ (⊤ : ℕ∞) fun x : Mat k r => Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) :=
        Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
      have hV : IsOpen {x : Mat k r | Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)) ≠ 0} :=
        isOpen_ne_fun hDc.continuous continuous_const
      have hloc : Loc ⊤ (C3.AAop k r r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) F) g₀ :=
        loc_AAop (hs g₀ hg₀) r le_rfl _
      exact loc_smulFun (fun x => (Dmin k r Bs.z Bs.z' x (Fin.last (r + 1)))⁻¹) hV
        (hDc.contDiffOn.inv fun x hx => hx) hD hloc
  · intro g hg hne
    by_contra hgt
    push Not at hgt
    have hU : IsOpen {x : Mat k r | R < gN x} := isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous
    refine hne (hvan _ hU (fun x hx hxG => ?_) g hgt hg)
    by_contra h
    exact absurd (hR x hxG h) (not_le.mpr hx)
  · intro g hg hne
    by_contra hlt
    push Not at hlt
    exact hne (hvan _ hUε hFε g hlt hg)

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport
noncomputable section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.PBI

def FrameTransport : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')))
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    ∀ c : Fin P.r → ℂ, c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∃ T : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' →ₗ[ℂ]
        Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π',
      (∀ Ψ c' g, (T Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' g =
        (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g))) ∧
      ∀ (w : List C.Letter), Fr.admitted st₀ (D.positionted w) → Fr.admitted st (D.positionted w) →
      ∀ (Ψ : Wd.Ix (Fin w.length) → Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')
        (e : Wd.Ix (Fin w.length)) (c' : Fin (JC.parLev P P.r).r → ℂ) (g : B.Mat P.k (P.r - P.r)),
        g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
        (P5.act (Fr.ofWord L₀ st₀ (D.positionted w)).F Ψ e : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
            c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => T (Ψ e')) e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' g

def ParFam {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
    [NormedSpace ℝ Par] (k ρ : ℕ) (U₀ : Set (Par × Mt k ρ)) (f : Par × Mt k ρ → E) : Prop :=
  ∀ q₀ ∈ U₀, Matrix.of q₀.2 ∈ Q.Glev k ρ (Fin.last ρ) → ∃ (U : Set (Par × Mt k ρ)) (F : Par × Mt k ρ → E),
    IsOpen U ∧ q₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ q ∈ U, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q = F q

def FrameParam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    ∀ (w : List C.Letter), Fr.admitted st (D.positionted w) →
    ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
      [BorelSpace Par] (U₀ : Set (Par × Mt P.k (P.r - P.r))), IsOpen U₀ →
      U₀ ⊆ Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)} →
    ∀ (Ψ : Par → Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
        (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
      (Ψf : Par → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp)),
      (∀ Z e c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        (Ψ Z e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z e y) →
      (∀ e, ParFam P.k (P.r - P.r) U₀ (fun q => Ψf q.1 e q.2)) →
      ∃ Φf : Par → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp),
        (∀ Z e c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
          (P5.act (Fr.ofWord L st (D.positionted w)).F (Ψ Z) e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Φf Z e y) ∧
        (∀ e, ParFam P.k (P.r - P.r) U₀ (fun q => Φf q.1 e q.2)) ∧
        (∀ (K : Set (Par × Mt P.k (P.r - P.r))),
          (∀ e q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K → Ψf q.1 e q.2 = 0) →
          ∀ e q, q ∈ U₀ → Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ closure K → Φf q.1 e q.2 = 0) ∧
        ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
        ∀ (Ψi : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
            (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') (y : Mt P.k (P.r - P.r)) (V : Set (Mt P.k (P.r - P.r))),
          IsOpen V → y ∈ V → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Kp ×ˢ V ⊆ U₀ →
          (∀ e c y', y' ∈ V → Matrix.of y' ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
            (Ψi e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y') =
              ∫ Z, Ψf Z e y' ∂ν) →
          ∀ e c, (P5.act (Fr.ofWord L st (D.positionted w)).F Ψi e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z e y ∂ν

def RadWord : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    ∀ (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ e : Wd.Ix (Fin w.length),
      Top.IsRadOf P p.T.base (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ_G) e)
        (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e)

def hcell {r : ℕ} (c : Fin r → ℂ) : C.LPt := List.ofFn fun j => (1, c j)

theorem ptSize_hcell {r : ℕ} (c : Fin r → ℂ) : D.ptSize (hcell c) = r := by
  simp [hcell, D.ptSize, List.map_ofFn, Function.comp_def]

def RadWordSlice : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    ∀ (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ (e : Wd.Ix (Fin w.length)) (c : Fin P.r → ℂ), c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ_G) e : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
          c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
        ((∏ j : Fin P.r, ‖c j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (D.castF (by rw [ptSize_hcell]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
            (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e) (hcell c))) g

def PicSlice : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base G →
    ∀ Φ_G : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ_G G →
    ∀ (c : Fin P.r → ℂ), c ∈ Formalism.QuantumDeterminants.OmX P.r →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (Φ_G : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g)) =
        ((∏ j : Fin P.r, ‖c j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (D.castF (by rw [ptSize_hcell]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G (hcell c))) g

end Formalism.FourierDecayAlt.P.PBI
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def colsVm (k r m : ℕ) (j : Fin m) : Fin (2 * r + k + 1) := ⟨2 * r + k - (r - 1 - j.val), by omega⟩

def kvM (k r m : ℕ) (w : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  qminorOp (Q.EH k r) (colsVm k r m) (colsVm k r m) w F

def kvTop (k r : ℕ) (y : ℂ) : ℂ := (y - ((2 * r + k : ℕ) : ℂ) / 2) + ((r : ℕ) : ℂ) - 1

def pbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then pbOp ⟨i, h⟩ f else 0

def cbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbOp ⟨i, h⟩ f else 0

def cbiN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbiOp ⟨i, h⟩ f else 0

def kvP (r : ℕ) (w : ℂ) : ℕ → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X) × (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0 => (fun f => f, fun _ => 0)
  | m + 1 =>
    (fun f => (kvP r w m).1 (fun c => (w - (m : ℂ)) • f c - pbN r (r - m - 1) f c) -
        cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f)),
      (kvP r w m).1)

def kvC (r : ℕ) (w : ℂ) (m : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := (kvP r w m).1 f

def gaugeF (k r : ℕ) (c : Fin r → ℂ) : ℂ := Q.resG k r (Fin.last r) (fun _ => (1 : ℂ)) c 1

end defs

def TVCoef : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          drbF P.r c • kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g)

def TVGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) c

def TVCrd : Prop :=
  ∀ (k r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (y : ℂ) (Φ : (Fin r → ℂ) → X)
    (U : Set (Fin r → ℂ)) (c : Fin r → ℂ), IsOpen U → U ⊆ OmX r → c ∈ U →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c' => gaugeF k r c' • Φ c') U →
      gaugeF k r c • kvC r (kvTop k r y) r Φ c = (vABm r y r).1 (fun c' => gaugeF k r c' • Φ c') c


open scoped ContDiff in
theorem jDACapTodaV_of_parts (h1 : TVCoef) (h2 : TVGrp) (h3 : TVCrd) : JDACapTodaV := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have e1 := h1 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have e2 := h2 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (Gauge.OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Gauge.OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
    (Fin.last P.r)).1
  obtain ⟨U, F, hUo, hx0, hF, hFeq⟩ := hfam (c, g) ⟨hc, hcg⟩ hg
  have hemb : ContDiff ℝ ∞ (fun c' : Fin P.r → ℂ => (c', g)) := contDiff_id.prodMk contDiff_const
  set U' : Set (Fin P.r → ℂ) := {c' | (c', g) ∈ U} ∩ OmX P.r with hU'
  have hU'o : IsOpen U' := (hUo.preimage hemb.continuous).inter (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX P.r)
  have hgauge : ∀ c' : Fin P.r → ℂ, gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g) =
      Q.resG P.k P.r (Fin.last P.r) J c' g := by
    intro c'
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' := by
    refine ((hF.comp (s := U') hemb.contDiffOn (fun c' hc' => hc'.1))).congr (fun c' hc' => ?_)
    rw [hgauge c']
    exact hFeq (c', g) hc'.1 hg
  have e3 := h3 P.k P.r (Wq →L[ℂ] Wp) y (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' c hU'o
    (fun _ h => h.2) ⟨hx0, hc⟩ hsm
  have hfun : (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) =
      fun c' => Q.resG P.k P.r (Fin.last P.r) J c' g := funext hgauge
  rw [hfun] at e3
  simp only [dMul, Q.crd, Q.cmp, if_true]
  rw [← e3]
  have hres : Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
      gaugeF P.k P.r c • capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) := by
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  rw [hres, e1, e2, smul_comm]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjS
namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace CAS

variable {k r : ℕ}

def TF (a : B.Mat k r → ℂ) : Prop := ContDiff ℝ ∞ a ∧ HasCompactSupport a

theorem tsupport_rdV {ψ : B.Mat k r → ℂ} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    tsupport (RdV X ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro g hg
  by_contra hgs
  apply hg
  have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
  have hcont : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    continuous_const.mul (Formalism.REAL.continuous_exp_real_smul X)
  have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' (tsupport ψ)ᶜ ∈ 𝓝 (0 : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hopen.mem_nhds
    simpa using hgs
  have hev : (fun t : ℝ => ψ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  show deriv _ 0 = 0
  rw [hev.deriv_eq]
  simp

theorem tf_rdV {a : B.Mat k r → ℂ} (ha : TF a) (X : B.Mat k r) : TF (RdV X a) := by
  exact ⟨rdV_contDiff ha.1 X, ha.2.mono' ((subset_tsupport _).trans (tsupport_rdV ha.1 X))⟩

theorem tf_rw {a : B.Mat k r → ℂ} (ha : TF a) : ∀ w : List (B.Mat k r), TF (B.Rw w a)
  | [] => ha
  | X :: w => tf_rdV (tf_rw ha w) X

theorem level_zero_set_eq_group : Q.Glev k r 0 = B.GV k r := by
  ext g
  simp only [Q.Glev, Set.mem_setOf_eq, B.GV, Fin.val_zero, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
    and_true]

theorem haar0 {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) : B.IsHaarOn (Q.Glev k r 0) μ := by
  rw [level_zero_set_eq_group]
  exact h

theorem lie0 {X : B.Mat k r} (hX : B.inLie k r X) : Q.inLieLev k r 0 X := by
  exact ⟨hX, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem smooth0 {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) : Q.SmoothLev k r 0 Set.univ a := by
  exact fun g₀ _ => ⟨Set.univ, a, isOpen_univ, trivial, ha.contDiffOn, fun _ _ _ => rfl⟩

theorem cpt0 {a : B.Mat k r → ℂ} (ha : HasCompactSupport a) : Q.CptOn k r 0 a := by
  exact ⟨tsupport a, ha, fun g _ hg => image_eq_zero_of_notMem_tsupport hg⟩

theorem word_adj_scalar {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) :
    ∀ (w : List (B.Mat k r)), (∀ X ∈ w, B.inLie k r X) → ∀ {a b : B.Mat k r → ℂ}, TF a → TF b →
      (∫ x : Mt k r, B.Rw w a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
        (-1 : ℂ) ^ w.length * ∫ x : Mt k r, a (Matrix.of x) * star (B.Rw w.reverse b (Matrix.of x)) ∂μ
  | [], _, a, b, _, _ => by simp [B.Rw]
  | X :: w, hw, a, b, ha, hb => by
    have hX : B.inLie k r X := hw X (by simp)
    have hw' : ∀ Z ∈ w, B.inLie k r Z := fun Z hZ => hw Z (by simp [hZ])
    have e1 : B.Rw (X :: w) a = RdV X (B.Rw w a) := rfl
    have e2 : B.Rw (X :: w).reverse b = B.Rw w.reverse (RdV X b) := by
      simp only [B.Rw, List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have hra := tf_rw ha w
    have sk := Formalism.FourierDecayAlt.P.right_differential_skew k r 0 μ (haar0 h) X (B.Rw w a) b (lie0 hX) (smooth0 hra.1)
      (smooth0 hb.1) (cpt0 hra.2) (cpt0 hb.2)
    rw [e1, sk, word_adj_scalar h w hw' ha (tf_rdV hb X), e2, List.length_cons, pow_succ]
    ring

end CAS

open CAS in
theorem capacity_adjoint_scalar : CapAdjScalar := by
  intro k r Y μ h a b ha hac hb hbc
  have ta : TF a := ⟨ha, hac⟩
  have tb : TF b := ⟨hb, hbc⟩
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  obtain ⟨hLw, hCV⟩ := Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)
  have hLie : ∀ cw ∈ capLw k r Y, ∀ X ∈ cw.2, B.inLie k r X := fun cw hc X hX => ((hLw cw hc).1 X hX).1

  have hintA : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      ha.continuous.mul (continuous_star.comp hv)
    have hs : HasCompactSupport (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      hac.mono fun x hx h0 => hx (by show a x * _ = 0; rw [h0, zero_mul])
    exact hc.integrable_of_hasCompactSupport hs
  have hintB : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hv.mul (continuous_star.comp hb.continuous)
    have hs : HasCompactSupport (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hbc.mono fun x hx h0 => hx (by show _ * star (b x) = 0; rw [h0, star_zero, mul_zero])
    exact hc.integrable_of_hasCompactSupport hs

  have hH := Formalism.FourierDecayAlt.P.hermitian_haar_invariance k r 0 0 0 μ (haar0 h) (fun _ _ => rfl) (fun _ _ => rfl) a b
    (smooth0 ha) (smooth0 hb) (cpt0 hac) (cpt0 hbc) Y 0 0
  have eT : ∀ (Y' : ℂ), Q.tL k r (E := ℂ) 0 0 0 Y' 0 0 = Q.CV k r Y' := fun _ => rfl
  have eS : star Y = conj Y := rfl
  rw [eT, eT, eS] at hH
  rw [← hH]

  have e2 : (∫ x : Mt k r, Q.CV k r Y a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * (B.Rw cw.2 a (Matrix.of x) * star (b (Matrix.of x)))).sum ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae h] with x hx
    have := hCV ℂ (B.GV k r) a (ckOn_of_contDiff ha _ _) (Matrix.of x) hx hx
    rw [this, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    rw [smul_eq_mul, mul_assoc]

  have e1 : (∫ x : Mt k r, a (Matrix.of x) * star (wsAdj (capLw k r Y) b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * ((-1 : ℂ) ^ cw.2.length * (a (Matrix.of x) * star (B.Rw cw.2.reverse b (Matrix.of x))))).sum ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [wsAdj, Complex.star_def, map_list_sum, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    simp only [Function.comp_apply, map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
    ring
  rw [e1, e2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ =>
      ((hintA _ (tf_rw tb _).1.continuous).const_mul _).const_mul _).2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ => (hintB _ (tf_rw ta _).1.continuous).const_mul _).2]
  refine congrArg List.sum (List.map_congr_left fun cw hcw => ?_)
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    word_adj_scalar h cw.2 (hLie cw hcw) ta tb]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartSysWOfPartsOf
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FamOK {d : ℕ} (O : Set (Fin d → ℝ)) (P : WOp d) (m : ℕ) : Prop :=
  ∀ t ∈ P, t.2.length ≤ m ∧ ∀ V ∈ t.2, ContDiffOn ℝ ∞ V O

def OpCV : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.CV k r (Y : ℂ) u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ 2 * r + k + 1 → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
        WOp.symb P j x ξ = cj * Ξ₀.charpoly.coeff (2 * r + k + 1 - j)

def OpCapR : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ)
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u → Q.IsFrameOf k r [z'] Bs →
    (∀ w : ℂ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.capR k r Bs w u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ k → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
        WOp.symb P j x ξ = cj * (cmp Ξ₀ Bs).charpoly.coeff (k - j)

def OpCapL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ)
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ),
    IsChart k r d O U κ Φ → (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') →
    Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') u → Q.IsFrameOf k r [z] Bs →
    (∀ w : ℂ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.capLft k r Bs w u g = c • u g) →
    ∀ j, 1 ≤ j → j ≤ k → ∃ (P : WOp d) (cj : ℂ), cj ≠ 0 ∧ FamOK O P j ∧
      (∀ x ∈ O, WOp.app P (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ : B.Mat k r), B.inLie k r Ξ →
        (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VL κ Φ X x = (Matrix.trace (Ξ * X)).re) →
        WOp.symb P j x ξ = cj * (cmp Ξ Bs).charpoly.coeff (k - j)

def OpCVOf : Prop := RwChart → CapWords → OpCV

def OpCapROf : Prop := RwChart → CapRWords → OpCapR

def OpCapLOf : Prop := RwChart → CapLWords → OpCapL

def NilOfCharpoly : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), (∀ j, 1 ≤ j → j ≤ n → M.charpoly.coeff (n - j) = 0) → IsNilpotent M

def ConjAlg : Prop :=
  ∀ (k r : ℕ) (g : B.Mat k r), g ∈ B.GV k r →
    (∀ A : B.Mat k r, B.inLie k r A → B.inLie k r (g * A * g⁻¹)) ∧
    (∀ A : B.Mat k r, IsNilpotent A → IsNilpotent (g * A * g⁻¹)) ∧
    (∀ A : B.Mat k r, A ≠ 0 → g * A * g⁻¹ ≠ 0) ∧
    ∀ A X : B.Mat k r, Matrix.trace ((g * A * g⁻¹) * (g * X * g⁻¹)) = Matrix.trace (A * X)

def CovL : Prop :=
  ∀ (k r d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r)) (κ : (Fin d → ℝ) → B.Mat k r)
    (Φ : B.Mat k r → (Fin d → ℝ)), IsChart k r d O U κ Φ →
    ∀ x ∈ O, ∀ (ξ : Fin d → ℝ) (Ξ₀ : B.Mat k r), B.inLie k r Ξ₀ →
      (∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VR κ Φ X x = (Matrix.trace (Ξ₀ * X)).re) →
      ∀ X : B.Mat k r, B.inLie k r X → ξ ⬝ᵥ VL κ Φ X x = (Matrix.trace ((κ x * Ξ₀ * (κ x)⁻¹) * X)).re

def opOne {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) : WOp d := [(1, [V]), (-c, [])]

theorem opOne_app {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (v : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    WOp.app (opOne V c) v x = vfD V v x - c * v x := by
  simp [opOne, WOp.app, vfW]
  ring

theorem opOne_symb {d : ℕ} (V : (Fin d → ℝ) → (Fin d → ℝ)) (c : ℂ) (x ξ : Fin d → ℝ) :
    WOp.symb (opOne V c) 1 x ξ = ((ξ ⬝ᵥ V x : ℝ) : ℂ) := by
  simp [opOne, WOp.symb]

theorem opOne_ok {d : ℕ} {O : Set (Fin d → ℝ)} {V : (Fin d → ℝ) → (Fin d → ℝ)} (c : ℂ) (hV : ContDiffOn ℝ ∞ V O) :
    FamOK O (opOne V c) 1 := by
  intro t ht
  simp only [opOne, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · refine ⟨by simp, ?_⟩
    intro W hW
    simp only [List.mem_singleton] at hW
    rw [hW]; exact hV
  · exact ⟨by simp, by simp⟩

theorem re_trace_span {k r q : ℕ} (A : B.Mat k r) (Xs : Fin q → B.Mat k r) (a : Fin q → ℝ)
    (h : ∀ i, (Matrix.trace (A * Xs i)).re = 0) :
    (Matrix.trace (A * ∑ i, ((a i : ℝ) : ℂ) • Xs i)).re = 0 := by
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, h i, mul_zero]

theorem fin_shift {n : ℕ} {p : ℕ → Prop} (h : ∀ j : Fin n, p ((j : ℕ) + 1)) : ∀ j, 1 ≤ j → j ≤ n → p j := by
  intro j h1 h2
  have := h ⟨j - 1, by omega⟩
  simpa [Nat.sub_add_cancel h1] using this

theorem chartSysWOfParts_of (hCV : OpCVOf) (hCR : OpCapROf) (hCL : OpCapLOf) (hNil : NilOfCharpoly)
    (hConj : ConjAlg) (hCovL : CovL) : ChartSysWOfParts := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 k r z z' d O U κ Φ u hk hz hz' hT hT' hC hOm hG
  obtain ⟨hCk, hNR, hNL, hCLe, hCRe, hCVe⟩ := hG
  obtain ⟨huc, hfld, hw⟩ := h2 k r z z' d O U κ Φ u hC hOm hCk
  obtain ⟨q, Xs, hXs, hspan⟩ := h3 k r
  obtain ⟨Bs, hBs⟩ := h8 k r z hz hT
  obtain ⟨Bs', hBs'⟩ := h8 k r z' hz' hT'
  have oCV := hCV h2 h4 k r z z' d O U κ Φ u hC hOm hCk hCVe
  have oCR := hCR h2 h5 k r z z' d O U κ Φ u Bs' hC hOm hCk hBs' (hCRe Bs' hBs')
  have oCL := hCL h2 h6 k r z z' d O U κ Φ u Bs hC hOm hCk hBs (hCLe Bs hBs)
  have hXin : ∀ i, B.inLie k r (Xs i) := fun i => (hspan (Xs i) (hXs i)).1
  choose cR hcR using fun i => hNR (Xs i) (hXs i)
  choose cL hcL using fun i => hNL (Xs i) (hXs i)
  choose PV cV hcV0 hPVok hPVapp hPVsym using
    fun j : Fin (2 * r + k + 1) => oCV ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  choose PR cRR hcR0 hPRok hPRapp hPRsym using
    fun j : Fin k => oCR ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  choose PL cLL hcL0 hPLok hPLapp hPLsym using
    fun j : Fin k => oCL ((j : ℕ) + 1) (Nat.le_add_left 1 _) (Nat.succ_le_of_lt j.isLt)
  have hOmx : ∀ x ∈ O, κ x ∈ JF.Om k r z z' := fun x hx => ⟨(hC.2.2.2.2.1 x hx).1, hOm x hx⟩
  refine ⟨Fin q ⊕ Fin q ⊕ Fin (2 * r + k + 1) ⊕ Fin k ⊕ Fin k, inferInstance,
    Sum.elim (fun i => opOne (VR κ Φ (Xs i)) (cR i)) (Sum.elim (fun i => opOne (VL κ Φ (Xs i)) (cL i))
      (Sum.elim PV (Sum.elim PR PL))),
    Sum.elim (fun _ => 1) (Sum.elim (fun _ => 1) (Sum.elim (fun j => (j : ℕ) + 1)
      (Sum.elim (fun j => (j : ℕ) + 1) (fun j => (j : ℕ) + 1)))),
    ?_, ?_, huc, ?_, ?_⟩
  · rintro (i | i | j | j | j)
    · show 1 ≤ 2 * r + k + 1; omega
    · show 1 ≤ 2 * r + k + 1; omega
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; exact Nat.succ_le_of_lt j.isLt
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; have := j.isLt; omega
    · show (j : ℕ) + 1 ≤ 2 * r + k + 1; have := j.isLt; omega
  · rintro (i | i | j | j | j)
    · exact opOne_ok _ (hfld _).1
    · exact opOne_ok _ (hfld _).2
    · exact hPVok j
    · exact hPRok j
    · exact hPLok j
  · rintro (i | i | j | j | j) x hx
    · show WOp.app (opOne (VR κ Φ (Xs i)) (cR i)) (fun y => u (κ y)) x = 0
      rw [opOne_app]
      have e := (hw [Xs i] (by simpa using hXin i) (by simp only [List.length_singleton]; omega) x hx).1
      simp only [B.Rw, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, vfW] at e
      rw [← e, hcR i _ (hOmx x hx), smul_eq_mul, sub_self]
    · show WOp.app (opOne (VL κ Φ (Xs i)) (cL i)) (fun y => u (κ y)) x = 0
      rw [opOne_app]
      have e := (hw [Xs i] (by simpa using hXin i) (by simp only [List.length_singleton]; omega) x hx).2
      simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, vfW] at e
      rw [← e, hcL i _ (hOmx x hx), smul_eq_mul, sub_self]
    · exact hPVapp j x hx
    · exact hPRapp j x hx
    · exact hPLapp j x hx
  · intro x hx ξ hξ hall
    obtain ⟨Ξ₀, hΞ₀, hΞ₀0, hcov⟩ := h1 k r d O U κ Φ hC x hx ξ
    have hg : κ x ∈ B.GV k r := (hC.2.2.2.2.1 x hx).1
    obtain ⟨cLie, cNil, cNe, cTr⟩ := hConj k r (κ x) hg
    have hcovL := hCovL k r d O U κ Φ hC x hx ξ Ξ₀ hΞ₀ hcov
    have hΞ : B.inLie k r (κ x * Ξ₀ * (κ x)⁻¹) := cLie Ξ₀ hΞ₀
    have hNRz : ∀ i, (Matrix.trace (Ξ₀ * Xs i)).re = 0 := by
      intro i
      have h0 := hall (Sum.inl i)
      change WOp.symb (opOne (VR κ Φ (Xs i)) (cR i)) 1 x ξ = 0 at h0
      rw [opOne_symb] at h0
      rw [← hcov _ (hXin i)]
      exact_mod_cast h0
    have hNLz : ∀ i, (Matrix.trace ((κ x * Ξ₀ * (κ x)⁻¹) * Xs i)).re = 0 := by
      intro i
      have h0 := hall (Sum.inr (Sum.inl i))
      change WOp.symb (opOne (VL κ Φ (Xs i)) (cL i)) 1 x ξ = 0 at h0
      rw [opOne_symb] at h0
      rw [← hcovL _ (hXin i)]
      exact_mod_cast h0
    have hVF : ∀ j : Fin (2 * r + k + 1), Ξ₀.charpoly.coeff (2 * r + k + 1 - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inl j)))
      change WOp.symb (PV j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPVsym j x hx ξ Ξ₀ hΞ₀ hcov] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcV0 j)
    have hRF : ∀ j : Fin k, (cmp Ξ₀ Bs').charpoly.coeff (k - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
      change WOp.symb (PR j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPRsym j x hx ξ Ξ₀ hΞ₀ hcov] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcR0 j)
    have hLF : ∀ j : Fin k, (cmp (κ x * Ξ₀ * (κ x)⁻¹) Bs).charpoly.coeff (k - ((j : ℕ) + 1)) = 0 := by
      intro j
      have h0 := hall (Sum.inr (Sum.inr (Sum.inr (Sum.inr j))))
      change WOp.symb (PL j) ((j : ℕ) + 1) x ξ = 0 at h0
      rw [hPLsym j x hx ξ _ hΞ hcovL] at h0
      exact (mul_eq_zero.mp h0).resolve_left (hcL0 j)
    have hnil0 : IsNilpotent Ξ₀ :=
      hNil _ Ξ₀ (fin_shift (p := fun j => Ξ₀.charpoly.coeff (2 * r + k + 1 - j) = 0) hVF)
    have hUW' := h7 k r z' Bs' hz' hT' hBs' Ξ₀ hΞ₀ (fin_shift (p := fun j => (cmp Ξ₀ Bs').charpoly.coeff (k - j) = 0) hRF)
    have hUW := h7 k r z Bs hz hT hBs _ hΞ
      (fin_shift (p := fun j => (cmp (κ x * Ξ₀ * (κ x)⁻¹) Bs).charpoly.coeff (k - j) = 0) hLF)
    refine ⟨κ x * Ξ₀ * (κ x)⁻¹, hΞ, cNe Ξ₀ (hΞ₀0 hξ), cNil Ξ₀ hnil0, ?_, ?_⟩
    · intro X hX
      rcases hX with hX | hX
      · exact hUW X hX
      · obtain ⟨_, a, rfl⟩ := hspan X hX
        exact re_trace_span _ Xs a hNLz
    · intro X hX
      rw [cTr Ξ₀ X]
      rcases hX with hX | hX
      · exact hUW' X hX
      · obtain ⟨_, a, rfl⟩ := hspan X hX
        exact re_trace_span Ξ₀ Xs a hNRz

theorem chartEqs_of_J (hCV : OpCVOf) (hCR : OpCapROf) (hCL : OpCapLOf) (hNil : NilOfCharpoly) (hConj : ConjAlg)
    (hCovL : CovL) (h1 : ChartCov) (h2 : RwChart) (h3 : LieNFin) (h4 : CapWords) (h5 : CapRWords) (h6 : CapLWords)
    (h7 : CmpZero) (h8 : FrameEx) (hS : VOpToSOpOfSteps) (s1 : SOpField) (s2 : SOpLift) (s3 : SOpLin) : ChartEqs :=
  chartEqs_of_all (chartSysWOfParts_of hCV hCR hCL hNil hConj hCovL) h1 h2 h3 h4 h5 h6 h7 h8 hS s1 s2 s3

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERAsm
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERComm
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem coefficient_vector_commutation : CVComm := by
  intro k r Wp Wq _ _ _ _ _ _ s Y Y' F hF g hg
  have hs : ∀ (Z α : ℂ) (f : B.Mat k r → (Wq →L[ℂ] Wp)),
      Q.CV k r Z (α • f) = α • Q.CV k r Z f := fun Z => P5.tL_smulC 0 0 0 Z 0 0
  have hsm : Q.SmoothLev k r 0 Set.univ F := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hF g₀ ((CapelliUnderIntegral.glev0 g₀).1 hg₀.1)
    exact ⟨U, f', hU, hgU, hc, fun x hx hxl => he x hx ((CapelliUnderIntegral.glev0 x).1 hxl)⟩
  have hc := capelli_commutation _ k r 0 Set.univ F isOpen_univ hsm g
    ⟨(CapelliUnderIntegral.glev0 g).2 hg, trivial⟩ (Q.uC k r 0 Y) (Q.uC k r 0 Y')
  simp only [Pi.smul_apply, hs]
  exact congrArg (fun t => s • s • t) hc

end Formalism.FourierDecayAlt.P.CutMP.ER
end

namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem energyReal_of_capAdj (hA : CapAdj) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_leaves hA capacity_theta_facts coefficient_vector_smoothness coefficient_vector_in_class coefficient_vector_support coefficient_vector_congr coefficient_vector_commutation
    beta_form_congr_holds

theorem energyReal_of_capAdjInt (hI : CapAdjInt) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_capAdj (capAdj_of_int hI)

end Formalism.FourierDecayAlt.P.CutMP.ER
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVSplit
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_split [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    (h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q)
    (h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ) :
    ∃ θL : Mt k r × Mt k r → ℝ, ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), KB.CptCoef Bs F →
      Integrable (lint Bs h'.choose θL F) (Bs.μW.prod Bs.μN) ∧
        D.vecV Bs ν' m₀ F q = ∫ x, lint Bs h'.choose θL F x ∂(Bs.μW.prod Bs.μN) := by
  obtain ⟨c₃, hc₃⟩ := orbJ_domL
  set A : ℝ := max 0 (c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) with hAdef
  have hγ := h'.choose_spec.1
  have hZ := h'.choose_spec.2.1
  have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
  have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
  obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
  have hZm := hZ.trans hmono
  obtain ⟨θ, maj, hθ, hθL, hθp, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos (le_max_right _ _)
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
    ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
      fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  refine ⟨fun x => θ (x, 0), fun F hF => ?_⟩
  obtain ⟨cF, hcF0, hb⟩ := Formalism.FourierDecayAlt.P.PBN.gN_bound Bs hF A (le_max_left _ _)
  have hbnd : ∀ᵐ p ∂Bs.μSS, θ p * ‖F (B.sgs p h'.choose)‖ ≤ cF * maj p :=
    hdom F cF hcF0 (fun p hp => hb _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ))
  have hFc : ContinuousOn F (B.GV k r) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hF.1
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose F) Bs.μSS :=
    Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs (U := B.GV k r) (fun p hp => Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) hFc
  have hi : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose F p) Bs.μSS := by
    refine Integrable.mono' (hmaj.const_mul cF) (hθ.1.aestronglyMeasurable.smul hm) ?_
    filter_upwards [hbnd, Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS Bs] with p hp hs
    rw [norm_smul, Real.norm_of_nonneg (hθ.2.1 p)]
    unfold D.orbIntegrand
    rw [norm_smul, Formalism.FourierDecayAlt.P.B7.norm_xi, one_mul]
    exact (mul_le_mul_of_nonneg_left (Formalism.FourierDecayAlt.P.B7.norm_rho_le Bs hs F h'.choose) (hθ.2.1 p)).trans hp
  have hR' := inner_int Bs h'.choose hγ θ hθL hθp maj hmaj cF hFc hbnd
  obtain ⟨hint, heq⟩ := fub Bs h'.choose θ hθL F hi hR'
  refine ⟨hint, ?_⟩
  unfold D.vecV
  rw [dite_eq_left h, dite_eq_left h']
  have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose F p) Bs.μSS := ⟨θ, hθ, hi⟩
  unfold D.orbJ
  rw [dite_eq_left hex]
  refine (Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR F _ θ hex.choose_spec.1 hθ
    hex.choose_spec.2 hi).trans heq

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
end
end
