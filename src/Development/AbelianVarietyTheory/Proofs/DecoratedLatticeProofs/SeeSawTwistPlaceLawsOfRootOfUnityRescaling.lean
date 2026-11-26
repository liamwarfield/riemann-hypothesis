module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegralLawAtTwistOfFactorisation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawIteratedIntegralLawLastStepsOfLocalFactori
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubleDescentOfParity
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteCellsAtTwistPlacesOfLocalFactorisati
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstVariableSupportFiniteCellsAtTwistPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceFinitelyManyCells
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceFinitelyManyCells
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinOneAt


set_option maxHeartbeats 4000000 in
theorem core {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (hψ : IsStdChar D c.ψ (-1)) (hv : v.Is) (ht : t.Is)
    {χ : ℕ → (AE D)ˣ →* Circle} (Q' : QAt v χ) (χz : (AE D)ˣ →* Circle) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (V₁ : (t.sBF j (σ + 1) h).χV = χ j * χz) (W₁ : (t.sBF j (σ + 1) h).χW = χ j)
    (V₂ : (t.sFB j σ h).χV = χ (j + 1)) (W₂ : (t.sFB j σ h).χW = χ (j + 1) * χz)
    (ka : IsWeilDatumO c.ψ _ _ (χ j) (χ j) (t.kom j)) (kb : IsWeilDatumO c.ψ _ _ (χ (j + 1)) (χ (j + 1)) (t.kom (j + 1)))
    (a : GL (Q'.X j ⊕ Fin (2 * σ + 2 + 1)) Q'.k) :
    ∃ T : Finset (GL (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) Q'.k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Q'.q.v) f₁ →
      ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = Q'.q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = Q'.q.v), ∀ x,
        flatBF (t.sBF j (σ + 1) h) (t.om j (g * Q'.gl j (2 * σ + 2 + 1) (by have := Q'.hs; omega) a,
          h₁ * Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) x) (comb c.ψ _ _ (Q'.eL j) f₁)) ≠ 0 →
        ∃ τ ∈ T, ∃ r, Q'.gl (j + 1) (2 * σ + 2) (by have := Q'.hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧
          ∃ κ ∈ (Q'.T.lev (j + 1) (2 * σ + 2) (by have := Q'.hs; omega)).J, x = r * τ * κ := by
  classical
  haveI := Q'.unitVol.1
  have e0 : j + (2 * σ + 2 + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e1 : j + 1 + (2 * σ + 2) = Q'.s + 1 := by have := Q'.hs; omega
  have e2 : j + 1 + 1 + (2 * σ + 1) = Q'.s + 1 := by have := Q'.hs; omega
  have e01 : j + (2 * σ + 2) = Q'.s := by have := Q'.hs; omega
  have e12 : j + 1 + (2 * σ + 1) = Q'.s := by have := Q'.hs; omega
  let S : Dbl2 c.ψ σ :=
    { B := c.B j (σ + 1) h, J := c.J j (σ + 1) h, B' := c.B (j + 1 + 1) σ (idx_step h),
      s₁ := t.sBF j (σ + 1) h, s₂ := t.sFB j σ h, l := c.lnk j σ h, vL := c.vL j σ h,
      χ₁ := χ j, χ₂ := χ (j + 1), χz := χz, oma := t.kom j, omb := t.kom (j + 1),
      V₁ := V₁, W₁ := W₁, V₂ := V₂, W₂ := W₂, weila := ka, weilb := kb }
  let Fd : Dbl (ofSplit Q'.q) S.B S.J S.B' (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1)) (2 * σ) :=
    { s := Q'.sc j, s_ne := Q'.sc_ne j, F₀ := Q'.FX j (by omega), F₁ := Q'.FX (j + 1) (by omega),
      F₂ := Q'.FX (j + 1 + 1) (by omega), G₀ := Q'.FY j _ e0, G₁ := Q'.FY (j + 1) _ e1, G₂ := Q'.FY (j + 1 + 1) _ e2,
      bes := Q'.bes j (σ + 1) h _ e0, jac := Q'.jac j (σ + 1) h _ e1,
      bes' := by rw [← Q'.sc_step j]; exact Q'.bes (j + 1 + 1) σ (idx_step h) _ e2 }
  have reg1 := (Q'.reg.2.2 (j + 1) _ e1)
  have reg2 := (Q'.reg.2.2 (j + 1 + 1) _ e2)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, A₁, A₂, cov₁, cov₂, d₁, d₂, ent₁, ent₂, e₀, e₂, one₀, one₂, m₁, m₂, haar₁, haar₂,
      vol₁, vol₂, -, -, -⟩ :=
    GlobalTheory.QPl.Inhab.exists_qstep hψ S Q'.ν Q'.unitVol Q'.q Q'.ψk Q'.char Q'.cond (Q'.X j) (Q'.X (j + 1)) (Q'.X (j + 1 + 1))
      (2 * σ) Fd (Q'.T.mu (j + 1)) (Q'.T.mu (j + 1 + 1)) (Q'.mu j (by omega)).1 (Q'.mu (j + 1) (by omega)).1
      (Q'.mu j (by omega)).2 (Q'.mu (j + 1) (by omega)).2 (Q'.T.lev j _ e0) (Q'.T.lev (j + 1) _ e1) (Q'.T.lev (j + 1 + 1) _ e2)
      (Q'.reg.2.2 j _ e0).1 ⟨reg1.1, reg1.2.1⟩ ⟨reg2.1, reg2.2.1⟩ (Q'.le _ _ e1) (Q'.le _ _ e2)
      ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩ ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩ (Q'.laws.1 j _ e01) (Q'.laws.1 (j + 1) _ e12)
      a 1 1
  let Q : QStep S :=
    { k := Q'.k, ν := Q'.ν, unitVol := Q'.unitVol, q := Q'.q, ψk := Q'.ψk, char := Q'.char, cond := Q'.cond,
      n₀ := Q'.X j, n₁ := Q'.X (j + 1), n₂ := Q'.X (j + 1 + 1), c := 2 * σ, F := Fd,
      gl₀ := Q'.gl j _ e0, gl₁ := Q'.gl (j + 1) _ e1, gl₂ := Q'.gl (j + 1 + 1) _ e2,
      loc₀ := Q'.gl_loc j _ e0, loc₁ := Q'.gl_loc (j + 1) _ e1, loc₂ := Q'.gl_loc (j + 1 + 1) _ e2,
      μ₁ := Q'.T.mu (j + 1), μ₂ := Q'.T.mu (j + 1 + 1), comp₁ := (Q'.mu j (by omega)).1, comp₂ := (Q'.mu (j + 1) (by omega)).1,
      open₁ := (Q'.mu j (by omega)).2, open₂ := (Q'.mu (j + 1) (by omega)).2,
      L₀ := Q'.T.lev j _ e0, L₁ := Q'.T.lev (j + 1) _ e1, L₂ := Q'.T.lev (j + 1 + 1) _ e2,
      co₁ := ⟨reg1.1, reg1.2.1⟩, co₂ := ⟨reg2.1, reg2.2.1⟩, le₁ := Q'.le _ _ e1, le₂ := Q'.le _ _ e2,
      Φ₁ := ⟨Q'.T.Phi j _ e01, Q'.reg.1 _ _ e01⟩, Φ₂ := ⟨Q'.T.Phi (j + 1) _ e12, Q'.reg.1 _ _ e12⟩,
      ty₁ := Q'.laws.1 j _ e01, ty₂ := Q'.laws.1 (j + 1) _ e12,
      D₁ := Q'.eL j, D₂ := Q'.eL (j + 1), dat₁ := Q'.eL_at j _ e01, dat₂ := Q'.eL_at (j + 1) _ e12,
      α := a, A₁ := A₁, A₂ := A₂, cov₁ := cov₁, cov₂ := cov₂, d₁ := d₁, d₂ := d₂, ent₁ := ent₁, ent₂ := ent₂,
      e₀ := e₀, e₂ := e₂, one₀ := one₀, one₂ := one₂, m₁ := m₁, m₂ := m₂, haar₁ := haar₁, haar₂ := haar₂,
      vol₁ := vol₁, vol₂ := vol₂ }
  obtain ⟨T₁, hT₁, -⟩ := GlobalTheory.T.splitPlaceDoubleStepFinitelyManyCellsUniform_proof D c.ψ hψ σ S Q a
  refine ⟨T₁, fun f₁ hf₁ g hg h₁ hh₁ x hx => ?_⟩
  obtain ⟨Tm, hTm, hTmO⟩ := (GlobalTheory.LocMod.indicator_vac D Q'.k Q'.q Q'.unit (Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Q'.X j ⊕ Fin (2 * σ + 2 + 1))
    (c.V j) (c.V (j + 1)) (Q'.FY j _ e0) (Q'.FY (j + 1) _ e1) c.ψ Q'.ψk hψ Q'.char Q'.cond (v.N j) (v.N (j + 1))
    (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Q'.latY j _ e0) (Q'.latY (j + 1) _ e1)).2 f₁ hf₁
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Q'.k) (Y := Q'.X (j + 1) ⊕ Fin (2 * σ + 2)) (Y' := Q'.X j ⊕ Fin (2 * σ + 2 + 1))
  obtain ⟨f₀, f₂, -, -, -, -, hv2⟩ := GlobalTheory.QPl.Inhab.exists_vac hψ (ι := Unit) (fun _ => Q) (fun _ _ _ => rfl)
  have hvac : Q.Vac f₁ f₂ := ⟨⟨Tm, O, hTm, hO, hTmO O hO⟩, (hv2 ()).2⟩
  have hom := (ht.sBF j (σ + 1) h).1
  obtain ⟨τ, hτ, r, hr, κ, hκ, hx'⟩ := hT₁ f₁ f₂ hvac g hg h₁ hh₁ x (by
    change flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om _ _) ≠ 0
    rw [hom]; exact hx)
  exact ⟨τ, hτ, r, hr, κ, hκ, hx'⟩

theorem finOne_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ ((F.Q i).eL j) f₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  intro D c v t w F hc ht hv _ hP j σ h i a
  obtain ⟨χz, V₁, W₁, V₂, W₂⟩ := hP.mid j σ h
  exact core hc.std hv ht (F.Q i) χz j σ h V₁ W₁ V₂ W₂ (hP.kom j (by omega)) (hP.kom (j + 1) (by omega)) a

end GlobalTheory.QFinOneAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceFinitelyManyCellsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_twistPlace_finitely_many_cells : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ ((F.Q i).eL j) f₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  first | exact @GlobalTheory.QFinOneAt.finOne_pin | exact GlobalTheory.QFinOneAt.finOne_pin | (intros; apply GlobalTheory.QFinOneAt.finOne_pin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesGroupEqProductLocalGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesGroupEqProductLocalGroups
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QProd

open GlobalTheory.FinPl in
theorem at_eq' {D : D7} (V : HSp D) (P : Pl D → Prop) : grpAt V P = GfC V ⊓ grpOff V (fun p => ¬ P p) := by
  rw [(GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.2.1 (fun p => ¬ P p)]
  simp only [not_not]

open GlobalTheory.FinPl in
theorem at_le_off' {D : D7} (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' :=
  (GlobalTheory.FinPl.SetCut.grp_split D V ∅).2.2.2.2.2.2.1 P P' h


open GlobalTheory.FinPl in
theorem off_mono {D : D7} {V : HSp D} {R R' : Pl D → Prop} (hR : ∀ p, R' p → R p) {g : GA D V} (h : g ∈ grpOff V R) :
    g ∈ grpOff V R' := by
  unfold grpOff at h ⊢
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at h ⊢
  intro a b
  have := h a b
  unfold idOff at this ⊢
  rw [Submodule.mem_iInf] at this ⊢
  intro u
  exact this ⟨u.1, hR u.1 u.2⟩


open GlobalTheory.FinPl in
theorem off_of_each {D : D7} {V : HSp D} {R : Pl D → Prop} {g : GA D V} (h : ∀ p, R p → g ∈ grpOff V (· = p)) :
    g ∈ grpOff V R := by
  unfold grpOff
  rw [GlobalTheory.FinPlLoc.mem_congGrp]
  intro a b
  unfold idOff
  rw [Submodule.mem_iInf]
  intro u
  have hu := h u.1 u.2
  unfold grpOff at hu
  rw [GlobalTheory.FinPlLoc.mem_congGrp] at hu
  have := hu a b
  unfold idOff at this
  rw [Submodule.mem_iInf] at this
  exact this ⟨u.1, rfl⟩

theorem prod_local : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ P : (∀ i, GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k) →* GA D (c.V (j + 1)), (∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i) ∈ H) → P y ∈ H) ∧ (∀ y, P y ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), ∃ y, x = P y ∧ ∀ i, x * ((F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
  intro D c v t w F hF j σ h
  have hd : ∀ i : Fin F.r, j + 1 + (2 * σ + 2) = (F.Q i).s + 1 := fun i => by have := (F.Q i).hs; omega
  have key := fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1)) ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2))
    ((F.Q i).FY (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl (j + 1) (2 * σ + 2) (hd i)) ((F.Q i).gl_loc (j + 1) (2 * σ + 2) (hd i))
  let gl := fun i => (F.Q i).gl (j + 1) (2 * σ + 2) (hd i)
  have hoff : ∀ i i', i ≠ i' → ∀ g, gl i' g ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i i' hne g
    have hr : gl i' g ∈ (gl i').range := ⟨g, rfl⟩
    rw [(key i').2.1] at hr
    exact at_le_off' _ (fun p hp hq => hne (hF.inj (hq.symm.trans hp))) hr
  have hcomm : Pairwise fun i i' => ∀ x y, Commute (gl i x) (gl i' y) := by
    intro i i' hne x y
    exact (key i).2.2.2.1 x _ (hoff i i' hne y)
  have hmem : ∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, gl i (y i) ∈ H) →
      MonoidHom.noncommPiCoprod gl hcomm y ∈ H := by
    intro H y hy
    exact Submonoid.noncommProd_mem H.toSubmonoid Finset.univ _ (fun _ _ _ _ h => hcomm h _ _) (fun i _ => hy i)
  have hat : ∀ i g, gl i g ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q) := by
    intro i g
    have hr : gl i g ∈ (gl i).range := ⟨g, rfl⟩
    rw [(key i).2.1] at hr
    rw [at_eq'] at hr ⊢
    refine ⟨hr.1, off_mono (fun p hp hq => hp ((hF.places p).2 ⟨i, hq.symm⟩)) hr.2⟩
  refine ⟨MonoidHom.noncommPiCoprod gl hcomm, hmem, fun y => hmem _ y fun i => hat i (y i), ?_⟩
  intro x hx
  choose y hy _ using fun i => (key i).2.2.1 x
  set P := MonoidHom.noncommPiCoprod gl hcomm
  have hsplit : ∀ i, P y = P (Function.update y i 1) * gl i (y i) := by
    intro i
    have hy' : y = Function.update y i 1 * Pi.mulSingle i (y i) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    conv_lhs => rw [hy']
    rw [map_mul, MonoidHom.noncommPiCoprod_mulSingle]
  have hrest : ∀ i, P (Function.update y i 1) ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i
    refine hmem _ _ fun k => ?_
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]
      exact hoff i k (Ne.symm hk) _
  have hz_i : ∀ i, x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
    intro i
    rw [hsplit i, _root_.mul_inv_rev, ← mul_assoc]
    exact Subgroup.mul_mem _ (hy i) (Subgroup.inv_mem _ (hrest i))
  have hzQ : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q) :=
    Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hmem _ y fun i => hat i (y i)))
  rw [at_eq'] at hzQ
  have hall : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (fun _ => ¬ False) := by
    refine off_of_each fun p _ => ?_
    by_cases hp : p ∈ w.Q
    · obtain ⟨i, rfl⟩ := (hF.places p).1 hp
      exact hz_i i
    · exact off_mono (fun p' hp' => hp'.symm ▸ hp) hzQ.2
  have hz1 : x * (P y)⁻¹ ∈ GlobalTheory.FinPl.grpAt (c.V (j + 1)) (fun _ => False) := by
    rw [at_eq']
    exact ⟨hzQ.1, hall⟩
  have := GlobalTheory.VacFixP.eq_one_of_grpAt (fun _ h => h) hz1
  exact ⟨y, mul_inv_eq_one.1 this, hy⟩

end GlobalTheory.QProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesGroupEqProductLocalGroupsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaces_group_eq_product_local_groups : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ P : (∀ i, GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k) →* GA D (c.V (j + 1)), (∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i) ∈ H) → P y ∈ H) ∧ (∀ y, P y ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), ∃ y, x = P y ∧ ∀ i, x * ((F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
  first | exact @GlobalTheory.QProd.prod_local | exact GlobalTheory.QProd.prod_local | (intros; apply GlobalTheory.QProd.prod_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteLocalSupportExchangeDataTwistPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteLocalSupportExchangeDataTwistPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QSuppTwo

theorem prod_mul_inv_mem {G : Type} [Group G] (H : Subgroup G) : ∀ (n : ℕ) (f : Fin n → G) (i : Fin n),
    (∀ i', i' ≠ i → f i' ∈ H) → (∀ y ∈ H, f i * y = y * f i) → (List.ofFn f).prod * (f i)⁻¹ ∈ H := by
  intro n
  induction n with
  | zero => intro f i; exact i.elim0
  | succ n ih =>
    intro f i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro hf0 hc0
      have hP : (List.ofFn fun k : Fin n => f k.succ).prod ∈ H := by
        apply Subgroup.list_prod_mem
        intro x hx
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
        exact hf0 _ (Fin.succ_ne_zero k)
      rw [List.ofFn_succ, List.prod_cons, hc0 _ hP, mul_assoc, mul_inv_cancel, mul_one]
      exact hP
    · intro hfk hck
      rw [List.ofFn_succ, List.prod_cons, mul_assoc]
      exact mul_mem (hfk 0 (Fin.succ_ne_zero k).symm)
        (ih (fun k => f k.succ) k (fun k' hk' => hfk _ (fun e => hk' (Fin.succ_injective _ e))) hck)

theorem mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, QPl.conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [QPl.conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

end GlobalTheory.QSuppTwo

open GlobalTheory.QSuppTwo in
theorem GlobalTheory.QSuppTwo.main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ A : ∀ i, Finset (GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∀ α, ∀ g ∈ (w.ε j α).support, ∃ a : ∀ i, GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k, ∀ i, a i ∈ A i ∧ g * ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) (a i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v) := by
  classical
  intro D c v t w F hF j σ h
  have hd : ∀ i, j + (2 * σ + 2) = (F.Q i).s := fun i => by have := (F.Q i).hs; omega
  choose e he using fun i (α' : (F.Q i).Ch j) => (F.Q i).εL_at j (σ + 1) h (2 * σ + 2) (hd i) α'
  refine ⟨fun i => Finset.univ.biUnion fun α' => (e i α').support, ?_⟩
  intro α g hg
  rw [hF.ε j (σ + 1) h α] at hg
  have hg' := Finsupp.support_smul hg
  obtain ⟨x, hx, rfl⟩ := mem_support_conv _ _ g hg'
  have hpt : ∀ i, ∃ a ∈ (e i (F.eqv j α i)).support,
      (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a = x i := by
    intro i
    have := hx i
    rw [(he i (F.eqv j α i)).2] at this
    have := Finsupp.mapDomain_support this
    rw [Finset.mem_image] at this
    exact this
  choose a ha hax using hpt
  refine ⟨a, fun i => ⟨Finset.mem_biUnion.2 ⟨F.eqv j α i, Finset.mem_univ _, ha i⟩, ?_⟩⟩
  have I := fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V j) _ ((F.Q i).FY j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega))
    ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega)) ((F.Q i).gl_loc j _ _)
  rw [hax i]
  apply prod_mul_inv_mem _ _ x i
  · intro i' hi'
    rw [← hax i']
    have hr : (F.Q i').gl j (2 * σ + 2 + 1) (by have := (F.Q i').hs; omega) (a i') ∈ GlobalTheory.FinPl.grpAt (c.V j) (· = (F.Q i').q.v) := by
      rw [← (I i').2.1]; exact ⟨_, rfl⟩
    exact (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V j) ∅).2.2.2.2.2.2.1 _ _ (fun p hp hn => hi' (hF.inj (hp.symm.trans hn))) hr
  · intro y hy
    rw [← hax i]
    exact (I i).2.2.2.1 (a i) y hy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteLocalSupportExchangeDataTwistPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_local_support_exchangeData_twistPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ A : ∀ i, Finset (GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∀ α, ∀ g ∈ (w.ε j α).support, ∃ a : ∀ i, GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k, ∀ i, a i ∈ A i ∧ g * ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) (a i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v) := by
  first | exact @GlobalTheory.QSuppTwo.main | exact GlobalTheory.QSuppTwo.main | (intros; apply GlobalTheory.QSuppTwo.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCombinationSplitsSinglePlaceVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCombinationSplitsSinglePlaceVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPlaceSplit

variable {D : D7}

theorem coeff_mul_eq {G : Type} [AddMonoid G] (x y : AddMonoidAlgebra ℂ G) :
    (x * y).coeff = x.coeff.sum fun g a => y.coeff.sum fun h b => Finsupp.single (g + h) (a * b) := by
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.coeff_finsuppSum]
  simp only [AddMonoidAlgebra.coeff_finsuppSum, AddMonoidAlgebra.coeff_single]

theorem aconv_eq_prod {G : Type} [AddCommMonoid G] (l : List (G →₀ ℂ)) :
    AddMonoidAlgebra.ofCoeff (aconv l) = (l.map AddMonoidAlgebra.ofCoeff).prod := by
  induction l with
  | nil =>
    apply AddMonoidAlgebra.ext
    rw [List.map_nil, List.prod_nil, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_ofCoeff]
    rfl
  | cons e l ih =>
    apply AddMonoidAlgebra.ext
    rw [List.map_cons, List.prod_cons, ← ih, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff,
      AddMonoidAlgebra.coeff_ofCoeff, AddMonoidAlgebra.coeff_ofCoeff]
    rfl

theorem support_prod_mem {G ι : Type} [AddCommMonoid G] (M : AddSubmonoid G) (s : Finset ι) (g : ι → G →₀ ℂ)
    (h : ∀ i ∈ s, ∀ y ∈ (g i).support, y ∈ M) :
    ∀ y ∈ (∏ i ∈ s, AddMonoidAlgebra.ofCoeff (g i)).coeff.support, y ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro y hy
    rw [Finset.prod_empty, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single] at hy
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]
    exact M.zero_mem
  | insert a s ha ih =>
    intro y hy
    rw [Finset.prod_insert ha, coeff_mul_eq, AddMonoidAlgebra.coeff_ofCoeff] at hy
    obtain ⟨x, hx, hy2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
    obtain ⟨z, hz, hy3⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy2)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy3)]
    exact M.add_mem (h a (Finset.mem_insert_self a s) x hx)
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) z hz)

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO hO
  simp

theorem comb_mul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AddMonoidAlgebra ℂ (WO S T))
    (h : ∀ x ∈ a.coeff.support, ∀ y ∈ b.coeff.support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (a * b).coeff f = comb ψ S T a.coeff (comb ψ S T b.coeff f) := by
  have hz : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have ha : ∀ u (r r' : ℂ), (r + r') • heisO ψ S T u f = r • heisO ψ S T u f + r' • heisO ψ S T u f :=
    fun u r r' => add_smul _ _ _
  rw [GlobalTheory.HeisComb.comb_comb, coeff_mul_eq, GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha]
  simp only [Finsupp.sum_sum_index (h := fun u (z : ℂ) => z • heisO ψ S T u f) hz ha, Finsupp.sum_single_index, zero_smul]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  rw [GlobalTheory.WeilVacMove.heisO_heisO, symplOH, h x hx y hy, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem heisO_comb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (b : WO S T →₀ ℂ)
    (h : ∀ y ∈ b.support, symplO S T u y = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (comb ψ S T b f) = comb ψ S T b (heisO ψ S T u f) := by
  unfold comb
  rw [GlobalTheory.HeisComb.heisO_finset_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T u y = 0 := by unfold symplOH; rw [h y hy, mul_zero]
  rw [GlobalTheory.WeilVacMove.heisO_heisO, GlobalTheory.WeilVacMove.heisO_heisO, add_comm y u, h0, GlobalTheory.MixModel.symplOH_skew, h0, neg_zero]

theorem map_infPart_of_mxAt {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {y : Mx D m n} (hy : GlobalTheory.FinPl.MxAt P y) :
    y.map (infPart D) = 0 := by
  funext a b
  simp only [Matrix.map_apply, Matrix.zero_apply]
  exact (RingHom.mem_ker).1 (Submodule.mem_inf.1 (hy a b)).1

end GlobalTheory.TwistPlaceSplit

namespace GlobalTheory.TwistPlaceSplit


set_option maxHeartbeats 1000000 in
theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ (i : Fin F.r) Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∃ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ ∧ comb c.ψ _ _ (w.eQ j) Ψ₁ = comb c.ψ _ _ ((F.Q i).eL j) f₁ := by
  intro D c v t w F hc hv hP j hj i Ψ₁ hΨ
  classical
  set v₀ := (F.Q i).q.v with hv₀def
  have hv₀ : v₀ ∈ w.Q := (hP.places v₀).2 ⟨i, rfl⟩

  have hat : ∀ i', ∀ u ∈ ((F.Q i').eL j).support, GlobalTheory.FinPl.MxAt (· = (F.Q i').q.v) u := by
    intro i' u hu
    have hs := (F.Q i').hs
    obtain ⟨d, hd⟩ : ∃ d, j + d = (F.Q i').s := ⟨(F.Q i').s - j, by omega⟩
    exact GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D _ (F.Q i').q u (((F.Q i').eL_at j d hd).1 u hu)

  let M : AddSubmonoid (WO (c.V j) (c.V (j + 1))) :=
    { carrier := {y | (∀ x, GlobalTheory.FinPl.MxAt (· = v₀) x → symplO _ _ x y = 0) ∧ y.map (infPart D) = 0}
      add_mem' := fun {y y'} hy hy' => ⟨fun x hx => by rw [symplO_add_right, hy.1 x hx, hy'.1 x hx, add_zero], by
        rw [Matrix.map_add _ (map_add (infPart D)), hy.2, hy'.2, add_zero]⟩
      zero_mem' := ⟨fun x _ => symplO_zero_right _ _ x, by
        funext a b
        simp⟩ }
  have hM : ∀ i' ∈ Finset.univ.erase i, ∀ y ∈ ((F.Q i').eL j).support, y ∈ M := by
    intro i' hi' y hy
    have hne : v₀ ≠ (F.Q i').q.v := fun e => Finset.ne_of_mem_erase hi' (hP.inj e).symm
    exact ⟨fun x hx => GlobalTheory.FinPl.OverSwap.symplO_eq_zero_of_ne hne hx (hat i' y hy), map_infPart_of_mxAt (hat i' y hy)⟩
  set B := ∏ i' ∈ Finset.univ.erase i, AddMonoidAlgebra.ofCoeff ((F.Q i').eL j) with hB
  have hb : ∀ y ∈ B.coeff.support, y ∈ M := support_prod_mem M _ (fun i' => (F.Q i').eL j) hM
  have hprod : w.eQ j = (AddMonoidAlgebra.ofCoeff ((F.Q i).eL j) * B).coeff := by
    rw [hB, Finset.mul_prod_erase Finset.univ (fun i' => AddMonoidAlgebra.ofCoeff ((F.Q i').eL j)) (Finset.mem_univ i),
      ← Fin.prod_ofFn, hP.eQ j hj, ← AddMonoidAlgebra.coeff_ofCoeff (aconv _), aconv_eq_prod, List.map_ofFn]
    rfl

  have hmono : ∀ u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· = v₀),
      u ∈ latO (c.V j) (c.V (j + 1)) (v.N j : Set _) (v.N (j + 1) : Set _) (· ∈ w.Q) := by
    intro u hu
    refine AddSubgroup.closure_mono ?_ hu
    rintro x ⟨α, hα, hvα, rest⟩
    exact ⟨α, hα, fun v' hv' => hvα v' fun e => hv' (by rw [e]; exact hv₀), rest⟩
  refine ⟨comb c.ψ _ _ B.coeff Ψ₁, ⟨(GlobalTheory.HeisComb.main D c.ψ _ _).2.2.1 B.coeff Ψ₁ hΨ.1 (fun u hu => (hb u hu).2) hc.std,
    fun u hu => ?_, fun e he u hu hue => ?_⟩, ?_⟩
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt (AddSubgroup.nsmul_mem _ hu 2))),
      hΨ.2.1 u (hmono u hu)]
  · rw [heisO_comb _ _ _ _ _ (fun y hy => (hb y hy).1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)), hΨ.2.2 e he u (hmono u hu) hue]
  · rw [hprod, comb_mul _ _ _ _ _ (fun x hx y hy => (hb y hy).1 x (hat i x (by rwa [AddMonoidAlgebra.coeff_ofCoeff] at hx))),
      AddMonoidAlgebra.coeff_ofCoeff]

end GlobalTheory.TwistPlaceSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistCombinationSplitsSinglePlaceVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCombination_splits_singlePlace_vacuum : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ (i : Fin F.r) Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∃ f₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f₁ ∧ comb c.ψ _ _ (w.eQ j) Ψ₁ = comb c.ψ _ _ ((F.Q i).eL j) f₁ := by
  first | exact @GlobalTheory.TwistPlaceSplit.main | exact GlobalTheory.TwistPlaceSplit.main | (intros; apply GlobalTheory.TwistPlaceSplit.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstVariableSupportFiniteCellsAtTwistPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QFinSupp

theorem locK_congr {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) (j d d' : ℕ) (e : d = d')
    (h1 : j + d = Q.s + 1) (h2 : j + d' = Q.s + 1) :
    (Q.T.lev j d h1).J.map (Q.gl j d h1) = (Q.T.lev j d' h2).J.map (Q.gl j d' h2) := by
  subst e; rfl

theorem cells_at : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  intro D c v t w F hc ht hv hW hF j σ h i a
  obtain ⟨T, hT⟩ := GlobalTheory.T.seeSaw_twistPlace_finitely_many_cells D c v t w F hc ht hv hW hF j σ h i a
  refine ⟨T, fun Ψ₁ hΨ g hg h₁ hh x hne => ?_⟩
  obtain ⟨f₁, hf₁, e⟩ := GlobalTheory.T.twistCombination_splits_singlePlace_vacuum D c v t w F hc hv hF j (by omega) i Ψ₁ hΨ
  rw [e] at hne
  exact hT f₁ hf₁ g hg h₁ hh x hne

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ T₁ : Finset (GA D (c.V (j + 1))), (∀ q ∈ T₁, q ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ α, ∀ g ∈ (w.ε j α).support, ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h) (t.om j (g, x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧ ∃ q ∈ T₁, ∃ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, x = r * q * k := by
  intro D c v t w F hc ht hv hW hF j σ h
  classical
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_finite_local_support_exchangeData_twistPlaces D c v t w F hF j σ h
  choose T hT using fun i a => cells_at D c v t w F hc ht hv hW hF j σ h i a
  obtain ⟨P, hPH, hPat, hPdec⟩ := GlobalTheory.T.twistPlaces_group_eq_product_local_groups D c v t w F hF j σ h
  refine ⟨(Fintype.piFinset fun i => (A i).biUnion (T i)).image P, ?_, ?_⟩
  · intro q hq
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hq
    exact hPat y
  · intro Ψ₁ hΨ α g hg x hx hne
    obtain ⟨a, ha⟩ := hA α g hg
    obtain ⟨y, rfl, hy⟩ := hPdec x hx
    have key := fun i => hT i (a i) Ψ₁ hΨ _ (ha i).2 _ (hy i) (y i) (by simpa only [inv_mul_cancel_right] using hne)
    choose τ hτ r hr κ hκ hyeq using key
    have hyy : y = r * τ * κ := funext hyeq
    refine ⟨P r, hPH _ r hr, hPat r, P τ, Finset.mem_image.2 ⟨τ, Fintype.mem_piFinset.2 fun i =>
      Finset.mem_biUnion.2 ⟨a i, (ha i).1, hτ i⟩, rfl⟩, P κ, hPH _ κ fun i => ?_, by rw [hyy, map_mul, map_mul]⟩
    refine Subgroup.mem_iSup_of_mem i ?_
    rw [GlobalTheory.QuotientFiniteLevel.locK, locK_congr (F.Q i) (j + 1) _ (2 * σ + 2) (by have := (F.Q i).hs; omega) _ (by have := (F.Q i).hs; omega)]
    exact Subgroup.mem_map_of_mem _ (hκ i)

end GlobalTheory.QFinSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstVariableSupportFiniteCellsAtTwistPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstVariable_support_finite_cells_at_twist_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ T₁ : Finset (GA D (c.V (j + 1))), (∀ q ∈ T₁, q ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ α, ∀ g ∈ (w.ε j α).support, ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h) (t.om j (g, x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧ ∃ q ∈ T₁, ∃ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, x = r * q * k := by
  first | exact @GlobalTheory.QFinSupp.main | exact GlobalTheory.QFinSupp.main | (intros; apply GlobalTheory.QFinSupp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductOverPlacesCompactOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductOverPlacesCompactOpen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinGrp

open GlobalTheory.FinPl

theorem map_ofFn_prod_eq {G M : Type*} [Group G] [Monoid M] (φ : G →* M) :
    ∀ {r : ℕ} (a : Fin r → G) (i : Fin r), (∀ j, j ≠ i → φ (a j) = 1) → φ (List.ofFn a).prod = φ (a i)
  | 0, _, i, _ => i.elim0
  | r + 1, a, i, h => by
    rw [List.ofFn_succ, List.prod_cons, φ.map_mul]
    cases i using Fin.cases with
    | zero =>
      have h1 : φ (List.ofFn fun j : Fin r => a j.succ).prod = 1 := by
        rw [φ.map_list_prod, List.map_ofFn]
        refine List.prod_eq_one (l := List.ofFn fun j : Fin r => φ (a j.succ)) ?_
        rw [List.forall_mem_ofFn_iff]
        exact fun j => h _ (Fin.succ_ne_zero j)
      rw [h1, mul_one]
    | succ i' =>
      rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact map_ofFn_prod_eq φ (fun j => a j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

variable {D : D7}

theorem loc_facts {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (i : Fin F.r) :
    GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) ∧
    IsCompact (GlobalTheory.QuotientFiniteLevel.locK F j σ h i : Set (GA D (c.V (j + 1)))) ∧
    IsOpen {x : grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) |
      (x : GA D (c.V (j + 1))) ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i} := by
  have hd : j + 1 + ((F.Q i).s - j) = (F.Q i).s + 1 := by have := (F.Q i).hs; omega
  obtain ⟨hce, hrange, -⟩ := GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V (j + 1))
    ((F.Q i).X (j + 1) ⊕ Fin ((F.Q i).s - j)) ((F.Q i).FY (j + 1) ((F.Q i).s - j) hd)
    ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ((F.Q i).gl_loc _ _ hd)
  have hr : ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd).range =
      grpAt (c.V (j + 1)) (· ∈ ({(F.Q i).q.v} : Finset (Pl D))) := by
    rw [hrange]; congr 1; funext p; exact propext Finset.mem_singleton.symm
  obtain ⟨hJo, hJc, -⟩ := (F.Q i).reg.2.2 (j + 1) ((F.Q i).s - j) hd
  refine ⟨?_, ?_, ?_⟩
  · rw [← hr]; intro x hx; obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx; exact ⟨g, rfl⟩
  · rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.coe_map]; exact hJc.image hce.continuous
  · obtain ⟨U, hU, hUe⟩ := hce.isInducing.isOpen_iff.1 hJo
    convert hU.preimage continuous_subtype_val using 1
    ext ⟨x, hx⟩
    rw [← hr] at hx
    obtain ⟨g, rfl⟩ := hx
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [GlobalTheory.QuotientFiniteLevel.locK, Subgroup.mem_map]
    constructor
    · rintro ⟨g', hg', e⟩
      have : g' ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hUe.symm ▸ hg'
      rw [← e]; exact this
    · intro hU'
      have hg : g ∈ ((F.Q i).gl (j + 1) ((F.Q i).s - j) hd) ⁻¹' U := hU'
      rw [hUe] at hg
      exact ⟨g, hg, rfl⟩

theorem qK_grp : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w →
    ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧
      IsCompact (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) ∧
      IsOpen (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) : Subgroup _) :
        Set (GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q))) := by
  intro D c v t w F hF j σ h
  have hloc := loc_facts F j σ h
  have hv : ∀ i, (F.Q i).q.v ∈ w.Q := fun i => (hF.places _).2 ⟨i, rfl⟩
  have hle : ∀ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := fun i => (hloc i).1.trans
    (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp => (Finset.mem_singleton.1 hp) ▸ hv i)
  have hoff : ∀ i i', i ≠ i' →
      GlobalTheory.QuotientFiniteLevel.locK F j σ h i' ≤ grpAt (c.V (j + 1)) (· ∉ ({(F.Q i).q.v} : Finset (Pl D))) := fun i i' hii' =>
    (hloc i').1.trans (GlobalTheory.CellLevels.grpAt_le_of_imp _ fun p hp hp' =>
      hii' (hF.inj ((Finset.mem_singleton.1 hp').symm.trans (Finset.mem_singleton.1 hp))))
  have hcomm : Pairwise fun i i' => ∀ x y : GA D (c.V (j + 1)),
      x ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i → y ∈ GlobalTheory.QuotientFiniteLevel.locK F j σ h i' → Commute x y := by
    intro i i' hii' x y hx hy
    exact (GlobalTheory.FinPl.SetCut.grp_split D (c.V (j + 1)) {(F.Q i).q.v}).2.2.2.2.1 x ((hloc i).1 hx) y (hoff i i' hii' hy)
  have hqK : GlobalTheory.QuotientFiniteLevel.qK F j σ h = ⨆ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i := rfl
  have hQle : GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ grpAt (c.V (j + 1)) (· ∈ w.Q) := iSup_le hle
  refine ⟨hQle, ?_, ?_⟩
  · have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
    have hcont : Continuous (Subgroup.noncommPiCoprod hcomm) := by
      have e : ⇑(Subgroup.noncommPiCoprod hcomm) = fun x =>
          ((List.finRange F.r).map fun i => ((x i : GlobalTheory.QuotientFiniteLevel.locK F j σ h i) : GA D (c.V (j + 1)))).prod := by
        funext x
        simp [Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod, Finset.noncommProd, List.ofFn_eq_map]
      rw [e]
      exact continuous_list_prod _ fun i _ => continuous_subtype_val.comp (continuous_apply i)
    haveI : ∀ i, CompactSpace (GlobalTheory.QuotientFiniteLevel.locK F j σ h i) := fun i => isCompact_iff_compactSpace.1 (hloc i).2.1
    have : (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) = Set.range (Subgroup.noncommPiCoprod hcomm) := by
      rw [hqK, ← hrange, MonoidHom.coe_range]
    rw [this]; exact isCompact_range hcont
  · set V := c.V (j + 1) with hVdef
    set K := GlobalTheory.QuotientFiniteLevel.locK F j σ h with hKdef
    obtain ⟨-, -, hQf, -, -, ⟨eQ, heQ⟩, -⟩ := GlobalTheory.FinPl.SetCut.grp_split D V w.Q
    have hbot : ∀ a, a ∈ grpAt V (· ∈ w.Q) → a ∈ grpAt V (· ∉ w.Q) → a = 1 := by
      intro a h1 h2
      have : eQ (⟨a, h1⟩, 1) = eQ (1, ⟨a, h2⟩) := by
        apply Subtype.ext; rw [heQ, heQ]; simp
      exact congrArg (fun p => (p.1 : GA D V)) (eQ.injective this)
    choose e he using fun i => (GlobalTheory.FinPl.SetCut.grp_split D V {(F.Q i).q.v}).2.2.2.2.2.1
    have he' : ∀ i (z : GfC V), (z : GA D V) = (((e i).symm z).1 : GA D V) * (((e i).symm z).2 : GA D V) := by
      intro i z; rw [← he i, Homeomorph.apply_symm_apply]
    let ι : grpAt V (· ∈ w.Q) → GfC V := fun x => ⟨x.1, hQf x.2⟩
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    let U : Set (grpAt V (· ∈ w.Q)) := ⋂ i, {x | ((((e i).symm (ι x)).1 : _) : GA D V) ∈ K i}
    have hUo : IsOpen U := isOpen_iInter_of_finite fun i =>
      (hloc i).2.2.preimage (continuous_fst.comp ((e i).symm.continuous.comp hι))
    have h1U : (1 : grpAt V (· ∈ w.Q)) ∈ U := by
      refine Set.mem_iInter.2 fun i => ?_
      have : (e i).symm (ι 1) = 1 := by
        rw [Homeomorph.symm_apply_eq]; apply Subtype.ext; rw [he]; simp [ι]
      show ((((e i).symm (ι 1)).1 : _) : GA D V) ∈ K i
      rw [this]; exact (K i).one_mem
    have hprj : ∀ i, ∀ b ∈ grpAt V (· ∉ ({(F.Q i).q.v} : Finset (Pl D))),
        GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v b = 1 := fun i b hb =>
      ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ b).1 hb).2 _ (by simp)
    have hUsub : U ⊆ (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (grpAt V (· ∈ w.Q)) : Subgroup _) : Set _) := by
      intro x hx
      have hx' := Set.mem_iInter.1 hx
      let a : Fin F.r → GA D V := fun i => (((e i).symm (ι x)).1 : GA D V)
      have ha : ∀ i, a i ∈ K i := fun i => hx' i
      have hp : (List.ofFn a).prod ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h := by
        refine Subgroup.list_prod_mem _ fun y hy => ?_
        rw [List.mem_ofFn] at hy
        obtain ⟨i, rfl⟩ := hy
        exact (le_iSup K i) (ha i)
      have hy1 : ∀ i, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v ((x : GA D V) * ((List.ofFn a).prod)⁻¹) = 1 := by
        intro i
        have hxi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (x : GA D V) =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) := by
          have := he' i (ι x)
          change (x : GA D V) = a i * _ at this
          rw [this, map_mul, hprj i _ (((e i).symm (ι x)).2).2, mul_one]
        have hpi : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (List.ofFn a).prod =
            GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (F.Q i).q.v (a i) :=
          map_ofFn_prod_eq _ a i fun j' hj' => hprj i _ (hoff i j' (Ne.symm hj') (ha j'))
        rw [map_mul, map_inv, hxi, hpi, mul_inv_cancel]
      have hyQ : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∈ w.Q) :=
        mul_mem x.2 (inv_mem (hQle hp))
      have hyN : (x : GA D V) * ((List.ofFn a).prod)⁻¹ ∈ grpAt V (· ∉ w.Q) := by
        refine (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ _).2 ⟨hQf hyQ, fun p hp' => ?_⟩
        obtain ⟨i, rfl⟩ := (hF.places p).1 (not_not.1 hp')
        exact hy1 i
      have hxp : (x : GA D V) = (List.ofFn a).prod := mul_inv_eq_one.1 (hbot _ hyQ hyN)
      show (x : GA D V) ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h
      rw [hxp]; exact hp
    exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hUo.mem_nhds h1U) hUsub)

end GlobalTheory.QFinGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductOverPlacesCompactOpenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistChainLevelProductOverPlaces_compact_open : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.QuotientFiniteLevel.qK F j σ h ≤ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧ IsCompact (GlobalTheory.QuotientFiniteLevel.qK F j σ h : Set (GA D (c.V (j + 1)))) ∧ IsOpen (((GlobalTheory.QuotientFiniteLevel.qK F j σ h).subgroupOf (GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) : Subgroup _) : Set (GlobalTheory.FinPl.grpAt (c.V (j + 1)) (· ∈ w.Q))) := by
  first | exact @GlobalTheory.QFinGrp.qK_grp | exact GlobalTheory.QFinGrp.qK_grp | (intros; apply GlobalTheory.QFinGrp.qK_grp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteCellsAtTwistPlacesOfLocalFactorisati
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QFinMain

theorem qFin_of_pin : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QFin v w := by
  intro D c v t w hc ht hv hW hP j σ h
  obtain ⟨F, hF⟩ := hP
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.twistChainLevelProductOverPlaces_compact_open D c v t w F hF j σ h
  obtain ⟨T₁, hT, hS⟩ := GlobalTheory.T.firstVariable_support_finite_cells_at_twist_places D c v t w F hc ht hv hW hF j σ h
  exact ⟨GlobalTheory.QuotientFiniteLevel.qK F j σ h, T₁, h1, h2, h3, hT, GlobalTheory.T.twistChainLevelProduct_inverse_scalar_laws D c v t w F hc ht hv hW hF j σ h, hS⟩

end GlobalTheory.QFinMain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteCellsAtTwistPlacesOfLocalFactorisatiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawFiniteCells_at_twistPlaces_of_localFactorisation : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QFin v w := by
  first | exact @GlobalTheory.QFinMain.qFin_of_pin | exact GlobalTheory.QFinMain.qFin_of_pin | (intros; apply GlobalTheory.QFinMain.qFin_of_pin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLawsOfRootOfUnityRescaling
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw

theorem laws_of_pin_resc : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPinU v w → QLaw v w ∧ QLast v w ∧ QFin v w :=
  fun D c v t w hc ht hv hW h =>
    GlobalTheory.QTw.RescTest.laws_of_qpinU v (fun w₀ h₀ =>
      ⟨GlobalTheory.T.seeSawIteratedIntegralLaw_at_twist_of_factorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawIteratedIntegralLawLastSteps_of_localFactorisation D c v t w₀ hc ht hv hW h₀, GlobalTheory.T.seeSawFiniteCells_at_twistPlaces_of_localFactorisation D c v t w₀ hc ht hv hW h₀⟩) w h

end GlobalTheory.QTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawTwistPlaceLawsOfRootOfUnityRescalingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawTwistPlaceLaws_of_rootOfUnityRescaling : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPinU v w → QLaw v w ∧ QLast v w ∧ QFin v w := by
  first | exact @GlobalTheory.QTw.laws_of_pin_resc | exact GlobalTheory.QTw.laws_of_pin_resc | (intros; apply GlobalTheory.QTw.laws_of_pin_resc <;> assumption)
end
