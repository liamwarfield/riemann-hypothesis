module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsBlockVec {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (χ : kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W) : Prop :=
  ∀ h ∈ KO k (Fin (r + t)),
    (∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) →
    (∀ i j : Fin r, valuation k (h.val (Fin.castAdd t i) (Fin.castAdd t j) - if i = j then 1 else 0) < 1) →
    ∀ u : kˣ, (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det → π h v = (χ u : ℂ) • v


variable (k) in
def BlockSplit : Prop := ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), IsSmoothChar χ → IsTame χ →
  v ≠ 0 → IsBlockVec χ π.π v →
  (∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSpherical π₂.π ∧
    Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin t) χ))))) ∨
  ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) ∧
    t < Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))}

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def RecSupp (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (n s : ℕ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) →
    ∀ g : Weil h, (rc n π).charPol g = ∏ a, (rc (d a) (σ a)).charPol g

def RecUnit (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (χ : kˣ →* ℂˣ) (c : Irr k 1), IsUnitaryChar χ → Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    ∀ g : Weil h, ∀ α ∈ (rc 1 c).eig g, ‖α‖ = 1

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  {T : WDTie N A} (S : Reading T)

def SuppLaws : Prop := ∀ i w hw, RecSupp (S i w hw).rc

def TypeBlock (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w) : Prop :=
  IsTame (S i w hw).mu ∧ ∀ P, ∃ v, v ≠ 0 ∧ IsBlockVec (S i w hw).mu ((S i w hw).rep P).π v

def BlockSplitAll (E : Type) [Field E] [NumberField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), BlockSplit (w.adicCompletion E)

variable (N A)

def MuInt : Prop := ∀ (i : N.Loc) (τ : H.E →+* ℂ), ∀ z ∈ A.infG (A.muC i) τ, ∃ m : ℤ, z = (m : ℂ)

def ChiIne : Prop := ∀ (i : N.Loc) (w : PlE H), w ∉ placesOver H.E (N.l i) →
  ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))

def XiOverO : Prop := ∀ i : N.Loc, ∃ ξ : G H.E N.Om →* (N.O i)ˣ, Continuous (fun g => ((ξ g : (N.O i)ˣ) : N.O i)) ∧
  ∀ w : PlE H, w ∉ placesOver H.E (N.l i) → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), ξ σ = 1) ∧
    ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {iotaO N A i ((ξ σ : (N.O i)ˣ) : N.O i)}

def RowPoint : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
  ∃ i' : N.Loc, N.j i' = N.j i ∧ N.l i' = N.l i ∧ (∀ w, IsSplitPl H w → A.locW i' σ w = A.locW i σ w) ∧
    (∃ φ : N.O i' ≃+* N.O i, Continuous φ ∧ ∀ z, iotaO N A i (φ z) = iotaO N A i' z) ∧
    ∃ (P : A.AV i') (x : N.X i'), thetaOf N A i' σ P ∧ A.ptV i' P = some x

end GlobalTheory.SplitRead
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DatLoc (D : D7) (cc : Ideal (𝓞 D.host.K)) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) : Prop :=
  ∀ x x' : Formalism.L2.Col.HomE D.host.E a b,
    (∀ P ∈ SS, ((cl : D.host.E)⁻¹ • (x - x')) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (aaOf D cc) N N')) → Ξ x = Ξ x'

section Law

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc]

def KapLawLt (Th : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc) : Prop :=
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ),
    (X.Pj j).IsLatTup L → (X.Pj (j + 1)).IsLatTup La'.2 →
    Th j (c, (X.Lv.lev j c).smul γ L) La' =
      MvPowerSeries.C ((kapG X Kc j c γ)⁻¹) * SA X Kc j (gamAt X j c γ) (Th j (c, L) La')

end Law

section Data

variable {p : ℕ} [Fact p.Prime] {D : D7} (X : Sys p) (E : CEmb X.G)
  (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D)
  {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
  (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)

def xiM (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ :=
  movD (Ξ₀ j La La') (fd.trG j La) (fd.trG (j + 1) La')

def scal0 (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : ℂ :=
  muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j La))⁻¹ *
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j La)) ^ (-(((j * (X.t + 1) / 2 : ℕ) : ℤ))) *
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La')) ^ ((((j + 1) * (X.t + 1) / 2 : ℕ) : ℤ))

def pPow (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : ℂ_[p] :=
  (p : ℂ_[p]) ^ (∑ v : X.Pl, X.vm v (j + 1) * (len X v (j + 1) La'.2 - len X v j La.2))

def LamPos : Prop :=
  ∀ v s x, TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = twG X E v s (ρ v (if IsOddPos s then D.host.conj x else x))

def PairOK : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    TaylorLogMetric.admitted D _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∧
    DatLoc D cc SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') ∧
    Differentiable ℂ (kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La')) ∧
    TaylorLogMetric.CoefIn D (kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La')) TaylorLogMetric.Qbar ∧
    scal0 X fd χ muT j La La' ∈ TaylorLogMetric.Qbar ∧
    Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∈ TaylorLogMetric.Qbar ∧
    Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ≠ 0 ∧
    ∀ v : X.Pl, IsUnit (fd.frM j La v).det ∧ IsUnit (fd.frM (j + 1) La' v).det ∧
      Submodule.span (X.G.P.W v) ((fun x k => ρ v (x k)) '' (fd.kerN j La : Set (Fin ((X.Pj j).m + 1) → D.host.E))) =
        (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)) ∧
      Submodule.span (X.G.P.W v) ((fun x k => ρ v (x k)) '' (fd.kerN (j + 1) La' : Set (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))) =
        (X.latAt v (j + 1) La'.2).map (((fd.frM (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))

def MoveTie : Prop :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ),
    (X.Pj j).IsLatTup L → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∃ (e : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (cΞ : ℂ), e * star e = 1 ∧
      (∀ v, fd.frM j (c, (X.Lv.lev j c).smul γ L) v * (gamAt X j c γ v : Matrix _ _ _) = e.map (ρ v) * fd.frM j (c, L) v) ∧
      fd.kerN j (c, (X.Lv.lev j c).smul γ L) = SDLat.smulLat e (fd.kerN j (c, L)) ∧ cΞ ∈ TaylorLogMetric.Qbar ∧
      (∀ x, xiM X fd Ξ₀ j (c, (X.Lv.lev j c).smul γ L) La' x = cΞ * xiM X fd Ξ₀ j (c, L) La' (x ∘ₗ Matrix.toLin' e)) ∧
      pPow X j (c, (X.Lv.lev j c).smul γ L) La' * TaylorLogMetric.lamC lam (scal0 X fd χ muT j (c, (X.Lv.lev j c).smul γ L) La' *
          (Base.chiFac χ _ _ (fd.kerN j (c, (X.Lv.lev j c).smul γ L)) (fd.kerN (j + 1) La'))⁻¹ * cΞ) =
        (kapG X ℂ_[p] j c γ)⁻¹ * (pPow X j (c, L) La' * TaylorLogMetric.lamC lam (scal0 X fd χ muT j (c, L) La' *
          (Base.chiFac χ _ _ (fd.kerN j (c, L)) (fd.kerN (j + 1) La'))⁻¹))

def AwayTie (v : X.Pl) (j : ℕ) : Prop :=
  ∃ P : HeightOneSpectrum (𝓞 D.host.E), GL3Theta.SplitP D P ∧
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E) ∧ P ∉ SS ∧ Formalism.L2.Col.conjPrime₂ P ∉ SS ∧
    ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal ∧
    (∀ x : 𝓞 D.host.E, ∃ y : X.G.P.W v, ρ v x = algebraMap _ _ y ∧ (x ∈ P.asIdeal ↔ (p : X.G.P.W v) ∣ y)) ∧
    (∀ (y : X.G.P.W v) (n : ℕ), ∃ (x : 𝓞 D.host.E) (z : X.G.P.W v), ρ v x = algebraMap _ _ (y + (p : X.G.P.W v) ^ n * z)) ∧
    ∃ u u' : X.G.Kf, X.vEqK u 0 ∧ X.vEqK u' 0 ∧
      ∀ (La Lb : X.Lt j) (La' Lb' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
        (X.Pj j).IsLatTup Lb.2 → (X.Pj (j + 1)).IsLatTup Lb'.2 → aw X v j La La' = aw X v j Lb Lb' →
        GL3Theta.EqOff D P (fd.kerN j La) (fd.kerN j Lb) ∧ GL3Theta.EqOff D P (fd.kerN (j + 1) La') (fd.kerN (j + 1) Lb') ∧
        fd.frM j La = fd.frM j Lb ∧ fd.frM (j + 1) La' = fd.frM (j + 1) Lb' ∧
        xiM X fd Ξ₀ j La La' = xiM X fd Ξ₀ j Lb Lb' ∧
        pPow X j La La' * TaylorLogMetric.lamC lam (scal0 X fd χ muT j La La') * E.iK (u ^ len X v j Lb.2 * u' ^ len X v (j + 1) Lb'.2) =
          pPow X j Lb Lb' * TaylorLogMetric.lamC lam (scal0 X fd χ muT j Lb Lb') * E.iK (u ^ len X v j La.2 * u' ^ len X v (j + 1) La'.2)

end Data

section DatLocApi

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))} {cl : ℕ}
  {N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}

theorem DatLoc.comp {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ) (f : ℂ → ℂ) :
    DatLoc D cc SS cl N N' fun x => f (Ξ x) :=
  fun x x' hx => congrArg f (h x x' hx)

theorem DatLoc.const_mul {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ) (k : ℂ) :
    DatLoc D cc SS cl N N' fun x => k * Ξ x :=
  h.comp fun y => k * y

theorem DatLoc.of_locP_eq {M : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ)
    (hM : ∀ P ∈ SS, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (aaOf D cc) M M') = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (aaOf D cc) N N')) :
    DatLoc D cc SS cl M M' Ξ :=
  fun x x' hx => h x x' fun P hP => hM P hP ▸ hx P hP

theorem DatLoc.add_halfBO {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ)
    (x m : Formalism.L2.Col.HomE D.host.E a b) (hm : m ∈ halfBO SS (perO (aaOf D cc) N N') cl) : Ξ (x + m) = Ξ x := by
  refine h _ _ fun P hP => ?_
  rw [add_sub_cancel_left]
  have h1 := (Submodule.mem_iInf _).1 hm P
  have h2 : Formalism.L2.Ker.expS SS P = 1 := by
    unfold Formalism.L2.Ker.expS
    rw [if_pos hP]
  rw [h2, zpow_one] at h1
  exact h1

theorem DatLoc.invOn {Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ} (h : DatLoc D cc SS cl N N' Ξ) {ι : Type} [Fintype ι]
    (emb : ι → D.host.E →+* ℂ) (δ : ℂ) (hinj : Function.Injective (embH (a := a) (b := b) emb δ)) :
    InvOn (AC emb δ (aaOf D cc) SS N N' cl) (BC emb δ (aaOf D cc) SS N N' cl) (onV emb δ Ξ) := by
  have hon : ∀ x, onV emb δ Ξ (embH emb δ x) = Ξ x := by
    intro x
    have hx : ∃ y, embH emb δ y = embH emb δ x := ⟨x, rfl⟩
    unfold onV
    rw [dite_eq_left hx]
    exact congrArg Ξ (hinj hx.choose_spec)
  rintro _ ⟨x, -, rfl⟩ _ - ⟨m, hm, rfl⟩
  rw [← map_add (f := _), hon, hon]
  exact h.add_halfBO x m hm

end DatLocApi

section LawApi

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Kc : Type} [Field Kc] [Algebra (FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc]

theorem KapLawLt.congr {Th Th' : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc} (h : KapLawLt X Kc Th)
    (he : ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      Th' j La La' = Th j La La') : KapLawLt X Kc Th' := by
  intro j hj c L La' γ hL hL'
  have hγ : (X.Pj j).IsLatTup ((X.Lv.lev j c).smul γ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ L).2 hL
  rw [he j hj (c, (X.Lv.lev j c).smul γ L) La' hγ hL', he j hj (c, L) La' hL hL']
  exact h j hj c L La' γ hL hL'

theorem KapLawLt.stab {Th : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc} (h : KapLawLt X Kc Th) {j : ℕ} (hj : j < X.mm)
    (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (ε : (X.Lv.lev j c).Γ) (hL : (X.Pj j).IsLatTup L)
    (hL' : (X.Pj (j + 1)).IsLatTup La'.2) (hε : (X.Lv.lev j c).smul ε L = L) :
    MvPowerSeries.C ((kapG X Kc j c ε)⁻¹) * SA X Kc j (gamAt X j c ε) (Th j (c, L) La') = Th j (c, L) La' := by
  have := h j hj c L La' ε hL hL'
  rw [hε] at this
  exact this.symm

end LawApi

section DataApi

variable {p : ℕ} [Fact p.Prime] {D : D7} (X : Sys p) (E : CEmb X.G)
  (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D)
  {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)
  (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v)

theorem frecG_eq (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    FrecG E pos fd B χ lam SS cl Ξ₀ muT c j La La' =
      linSub (fun x y => c * subBG E pos fd j La La' x y)
        (pPow X j La La' • serP lam fun z =>
          (scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹) *
            kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') z) := by
  unfold FrecG pPow scal0 xiM
  congr 3
  funext z
  ring

theorem pPow_eq_prod (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    pPow X j La La' = ∏ v : X.Pl, (p : ℂ_[p]) ^ (X.vm v (j + 1) * (len X v (j + 1) La'.2 - len X v j La.2)) := by
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  unfold pPow
  induction (Finset.univ : Finset X.Pl) using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hp, ih]

theorem twG_eq_tw (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    letI := wittFractionAlgebraCp p
    letI := algKfC E
    twG X E v s = tw X ℂ_[p] v s := rfl

theorem LamPos.even (h : LamPos X E pos lam ρ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : ¬ IsOddPos s) (x : D.host.E) :
    TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = twG X E v s (ρ v x) := by
  rw [h v s x, if_neg hs]

theorem LamPos.odd (h : LamPos X E pos lam ρ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : IsOddPos s) (x : D.host.E) :
    TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = twG X E v s (ρ v (D.host.conj x)) := by
  rw [h v s x, if_pos hs]

end DataApi

end GlobalTheory.TwU

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FracZeroOfPos
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {d : ℕ}

def pw (f : Fin d → R) : Submonoid R := Submonoid.powers (∏ j, f j)

def omitted (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Submodule R (LocalizedModule (pw f) M) :=
  Submodule.span R {z | ∃ (j : Fin d) (k : ℕ) (m : M), z = LocalizedModule.mk (f j ^ k • m) ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩}

abbrev LC (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Type :=
  LocalizedModule (pw f) M ⧸ omitted f M

def frac (f : Fin d → R) {M : Type} [AddCommGroup M] [Module R M] (m : M) (k : ℕ) : LC f M :=
  Submodule.Quotient.mk (LocalizedModule.mk m ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩)

theorem frac_prod_smul (f : Fin d → R) (m : M) (k : ℕ) : frac f ((∏ l, f l) • m) (k + 1) = frac f m k := by
  unfold frac
  congr 1
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul, pow_succ]

theorem frac_zero_of_pos (f : Fin d → R) (hd : 0 < d) (m : M) : frac f m 0 = 0 := by
  unfold frac
  rw [Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  exact ⟨⟨0, hd⟩, 0, m, by simp⟩

def IsRes {B : Type} [CommRing B] [Algebra ℂ B] (s : Fin d → B) (e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ)
    (ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ) : Prop :=
  (∀ j, e (s j) = MvPowerSeries.X j) ∧
  (∀ ω : Om ℂ B d, ∃ h : B, ω = h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) ∧
  ∀ (k : ℕ) (h : B), ρ (frac s (h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) (k + 1)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun _ => k) (e h)

namespace IsRes

variable {B : Type} [CommRing B] [Algebra ℂ B] {s : Fin d → B} {e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ}
  {ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ}

end IsRes

end GlobalTheory.W1

namespace GlobalTheory.W1.Ex

def rho0 (s : Fin 0 → ℂ) : LC s (Om ℂ ℂ 0) →ₗ[ℂ] ℂ :=
  (Submodule.liftQ (omitted s (Om ℂ ℂ 0))
    ((exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ]).toLinearMap ∘ₗ
      LocalizedModule.lift (pw s) LinearMap.id (fun u => by
        obtain ⟨n, hn⟩ := u.2
        have : (u : ℂ) = 1 := by simpa using hn.symm
        rw [this, map_one]; exact isUnit_one))
    (by
      have : omitted s (Om ℂ ℂ 0) = ⊥ := by
        unfold omitted
        rw [Submodule.span_eq_bot]
        rintro z ⟨j, _, _, _⟩
        exact j.elim0
      rw [this]; exact bot_le))

end GlobalTheory.W1.Ex
end
end

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD
open scoped TensorProduct

namespace GlobalTheory.WH

section Wd

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]

def wd (w : ι → Module.End k E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  LinearMap.pi fun t => ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • (w i ∘ₗ LinearMap.proj (t.erase i))

def acx (A : Finset ι → Submodule k E) (w : ι → Module.End k E) : Cx k (Finset ι → E) :=
  ⟨fun n => Submodule.pi Set.univ fun s => if (s.card : ℤ) = n then A s else ⊥, wd w⟩

def cupE {E' E'' : Type} [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'')
    (a : Finset ι → E) (b : Finset ι → E') : Finset ι → E'' := fun u =>
  ∑ j ∈ u, μ (a (u.filter (· ≤ j))) (b (u.filter (j ≤ ·)))

end Wd

section Join

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

def lft (s : Finset (ι ⊕ₗ κ)) : Finset ι := (s.map (ofLex : ι ⊕ₗ κ ≃ ι ⊕ κ).toEmbedding).toLeft

def rgt (s : Finset (ι ⊕ₗ κ)) : Finset κ := (s.map (ofLex : ι ⊕ₗ κ ≃ ι ⊕ κ).toEmbedding).toRight

def uni (I : Finset ι) (J : Finset κ) : Finset (ι ⊕ₗ κ) := (I.disjSum J).map (toLex : ι ⊕ κ ≃ ι ⊕ₗ κ).toEmbedding

variable {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E'']

def join (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') : Finset (ι ⊕ₗ κ) → E'' :=
  fun s => μ (a (lft s)) (b (rgt s))

def edge1 (a : Finset ι → E) : Finset (ι ⊕ₗ κ) → E := fun s => if (rgt s).card = 1 then a (lft s) else 0

def edge2 (b : Finset κ → E) : Finset (ι ⊕ₗ κ) → E := fun s => if (lft s).card = 1 then b (rgt s) else 0

def mixF (A : Finset ι → Finset κ → Submodule k E) (s : Finset (ι ⊕ₗ κ)) : Submodule k E :=
  if (lft s).Nonempty ∧ (rgt s).Nonempty then A (lft s) (rgt s) else ⊥

end Join

section Koszul

variable {k : Type} [Field k] {σ : Type} [LinearOrder σ] {E : Type} [AddCommGroup E] [Module k E]

end Koszul

section Forms

variable (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → F)

def XZ (l : Fin (d + 1)) : Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  LinearMap.rTensor _ ((Algebra.lsmul ℂ ℂ (DR ℂ K)) (algebraMap F K (x l)))

def actZ : K ⊗[ℂ] K →ₐ[ℂ] Module.End ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  (Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ (DR ℂ K)) (Algebra.lsmul ℂ ℂ (DR ℂ K)))

def MZ (a : ℕ) (I J : Finset (Fin (d + 1))) : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
  Submodule.map₂ (TensorProduct.mk ℂ _ _) (omB ℂ K (rB ℂ K x I) (d - a)) (omB ℂ K (rB ℂ K x J) a)

def ctr (τ : DR ℂ K →ₗ[K] K) (w : DR ℂ K) : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K :=
  TensorProduct.lift ((Algebra.lsmul ℂ ℂ (DR ℂ K)).toLinearMap ∘ₗ ((Algebra.linearMap F K).restrictScalars ℂ ∘ₗ
    (Algebra.trace F K).restrictScalars ℂ ∘ₗ τ.restrictScalars ℂ ∘ₗ LinearMap.mulLeft ℂ w))

end Forms

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ}

def pr2L (j2 : K →ₐ[ℂ] K') : DR ℂ K →ₗ[ℂ] DR ℂ K' :=
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  (GlobalTheory.W1.mapDR ℂ K K').toLinearMap.restrictScalars ℂ

def R2 (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') (J : Finset (Fin (d + 1))) : Subalgebra ℂ K' :=
  (integralClosure ((rB ℂ K x J).map j2) K').restrictScalars ℂ

variable [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']

def RY (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') (I J : Finset (Fin (d + 1))) : Subalgebra ℂ K' :=
  rB ℂ K' x I ⊔ R2 x j2 J

def gY (j2 : K →ₐ[ℂ] K') : DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K' :=
  TensorProduct.lift ((LinearMap.mul ℂ (DR ℂ K')).compl₁₂ ((GlobalTheory.W1.mapDR ℂ K K').toLinearMap.restrictScalars ℂ) (pr2L j2))

def Val (B : Subalgebra ℂ K') (e : B →ₐ[ℂ] ℂ) (v : K') (c : ℂ) : Prop :=
  ∃ (b : K') (hb : b ∈ B) (hbv : b * v ∈ B), e ⟨b, hb⟩ ≠ 0 ∧ e ⟨b * v, hbv⟩ = e ⟨b, hb⟩ * c

def IsFix (B : Subalgebra ℂ K') (e : B →ₐ[ℂ] ℂ) (j2 : K →ₐ[ℂ] K') (B0 : Subalgebra ℂ K) : Prop :=
  ∀ b ∈ B0, ∀ h1 : algebraMap K K' b ∈ B, Val B e (j2 b) (e ⟨_, h1⟩)

end Y

end GlobalTheory.WH
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  (S : StepLevel F E σ J T f bad)

def basePts : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) where
  carrier := {k | k ∈ levelAfL σ J S.Lb ∧ ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1}
  one_mem' := ⟨one_mem _, fun _ _ => map_one _⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, fun v h => by rw [map_mul, ha.2 v h, hb.2 v h, mul_one]⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, fun v h => by rw [map_inv, ha.2 v h, inv_one]⟩

theorem mem_basePts_iff (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : k ∈ basePts S ↔
    k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL σ J v S.Lb) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1 := by
  rw [← and_assoc, ← GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin k]
  rfl

variable {S} (k : basePts S)

def basePtU : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨k.1, k.2.1.1⟩

theorem basePt_loc (v : HeightOneSpectrum (𝓞 F)) : bc (prV (E := E) v) k.1 ∈ levelVL σ J v S.Lb :=
  ((mem_basePts_iff S k.1).1 k.2).2.1 v

theorem conj_mem_iff {G : Type} [Group G] {H : Subgroup G} {a : G} (ha : a ∈ H) (x : G) : a * x * a⁻¹ ∈ H ↔ x ∈ H := by
  rw [H.mul_mem_cancel_right (inv_mem ha), H.mul_mem_cancel_left ha]

def moveLev : StepLevel F E σ J T f bad :=
  { S with
    Uloc := fun v => (S.Uloc v).comap (MulAut.conj (bc (prV (E := E) v) k.1)).toMonoidHom
    Uloc_le := fun v x hx => (conj_mem_iff (H := UPts σ J (v.adicCompletion F)) (basePt_loc k v).1 x).1 (S.Uloc_le v hx)
    Uloc_lev := fun v x hx => (conj_mem_iff (basePt_loc k v) x).1 (S.Uloc_lev v hx)
    Uloc_hyp := fun v hv hT => by
      ext x
      rw [S.Uloc_hyp v hv hT]
      exact conj_mem_iff (basePt_loc k v) x
    UlocAlt := fun v h => by
      rw [← S.UlocAlt v h, k.2.2 v h]
      ext x
      simp
    U := S.U.comap (MulAut.conj k.1).toMonoidHom
    U_eq := fun x => by
      show k.1 * x * k.1⁻¹ ∈ S.U ↔ _
      rw [S.U_eq, conj_mem_iff (H := UPts σ J (FiniteAdeleRing (𝓞 F) F)) (a := k.1) (basePtU k).2]
      refine and_congr_right fun _ => forall_congr' fun v => ?_
      rw [map_mul, map_mul, map_inv]
      rfl
    U_compact := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      have hc : Continuous (fun x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => k.1⁻¹ * x * k.1) :=
        (continuous_const.mul continuous_id).mul continuous_const
      convert S.U_compact.image hc using 1
      ext x
      constructor
      · intro hx
        exact ⟨k.1 * x * k.1⁻¹, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩
        show k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ ∈ S.U
        have e : k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ = y := by group
        rwa [e]
    U_open := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
        inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
      have hc : Continuous (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => basePtU k * x * (basePtU k)⁻¹) :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact S.U_open.preimage hc
    chi := S.chi.comp ((MulAut.conj k.1).toMonoidHom.subgroupComap S.U)
    chi_triv := fun x hx => S.chi_triv _ fun v hv => by
      show bc (prV (E := E) v) (k.1 * x.1 * k.1⁻¹) = 1
      rw [map_mul, map_mul, hx v hv, mul_one, ← map_mul, mul_inv_cancel, map_one] }

theorem mem_moveLev (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : x ∈ (moveLev k).U ↔ k.1 * x * k.1⁻¹ ∈ S.U := Iff.rfl

def toMoved (κ : S.U) : (moveLev k).U :=
  ⟨k.1⁻¹ * κ.1 * k.1, by
    have e : k.1 * (k.1⁻¹ * κ.1 * k.1) * k.1⁻¹ = κ.1 := by group
    rw [mem_moveLev, e]
    exact κ.2⟩

theorem cls_move_iff (x y : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    (Quotient.mk'' (x * basePtU k) : Cls (moveLev k)) = Quotient.mk'' (y * basePtU k) ↔
      (Quotient.mk'' x : Cls S) = Quotient.mk'' y := by
  refine (@DoubleCoset.eq _ _ _ _ _ _).trans (Iff.trans ?_ (@DoubleCoset.eq _ _ _ _ _ _).symm)
  refine exists_congr fun g => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨κ, hκ, e⟩
    refine ⟨basePtU k * κ * (basePtU k)⁻¹, hκ, ?_⟩
    rw [← mul_inv_cancel_right y (basePtU k), e]
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨(basePtU k)⁻¹ * κ * basePtU k, (toMoved k ⟨κ.1, hκ⟩).2, ?_⟩
    rw [e]
    group

theorem mem_hat_move_iff (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (y⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔
      ((y * k.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
        (moveLev k).Lb := by
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact (inv_mem k.2.1).2 _

theorem map_conj_move (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    (moveLev k).U.map (MulAut.conj (y * k.1)).toMonoidHom = S.U.map (MulAut.conj y).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (mem_moveLev k κ).1 hκ, Eq.trans ?_ e⟩
    show y * (k.1 * κ * k.1⁻¹) * y⁻¹ = y * k.1 * κ * (y * k.1)⁻¹
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (toMoved k ⟨κ, hκ⟩).2, Eq.trans ?_ e⟩
    show y * k.1 * (k.1⁻¹ * κ * k.1) * (y * k.1)⁻¹ = y * κ * y⁻¹
    group

theorem bij_move {cl : Type} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : Function.Bijective fun c => (Quotient.mk'' (y c) : Cls S)) :
    Function.Bijective fun c => (Quotient.mk'' (y c * basePtU k) : Cls (moveLev k)) := by
  refine ⟨fun c c' e => h.1 ((cls_move_iff k _ _).1 e), fun q => ?_⟩
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨c, hc⟩ := h.2 (Quotient.mk'' (x * (basePtU k)⁻¹))
    refine ⟨c, ?_⟩
    have h := (cls_move_iff k _ _).2 hc
    rwa [inv_mul_cancel_right] at h

end Level

section Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
  {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}


set_option maxHeartbeats 1000000 in
def moveChart (K : LevelChart D T bad i hi stab lat) (k : basePts K.lev) : LevelChart D T bad i hi stab lat where
  lev := moveLev k
  y := fun c => K.y c * basePtU k
  y_bij := bij_move k K.y_bij
  y_lat := fun c x => (K.y_lat c x).trans (mem_hat_move_iff k (K.y c).1 x)
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := fun c γ => (K.stabI_range c γ).trans (SetLike.ext_iff.1 (map_conj_move k (K.y c).1) _).symm

end Chart

end GlobalTheory.TwU

end
end
