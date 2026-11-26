module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateHalfCommutantActsOnCosetVectorByScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureRelation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticesGoodPositionAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticesGoodPositionAllPlaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.GoodPos

variable {D : D7}

theorem tau_norm {E : Type} [Field E] [StarRing E] {m n : ℕ} {G : Matrix (Fin m) (Fin m) E} {G' : Matrix (Fin n) (Fin n) E}
    {τ : Matrix (Fin m) (Fin n) E} {t lam : E} {ζ : Fin m → E} {ζ₀ : Fin n → E} (h : τᴴ * (G * τ) = t • G')
    (hτ : τ *ᵥ ζ₀ = lam • ζ) : lam * star lam * (star ζ ⬝ᵥ G *ᵥ ζ) = t * (star ζ₀ ⬝ᵥ G' *ᵥ ζ₀) := by
  have := congrArg (fun M => star ζ₀ ⬝ᵥ M *ᵥ ζ₀) h
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hτ, smul_mulVec, dotProduct_smul, smul_eq_mul,
    mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at this
  rw [← this, mul_assoc]

variable {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} {o : TDat c k ι}

theorem val_norm_xi {p : SplitPt D k} (h : p.UnitAA) : valuation k (p.pr (incA D (D.host.xi0 * star D.host.xi0))) = 1 := by
  have h1 : valuation k (p.pr (incA D D.host.xi0)) = 1 := val_eq_one (isU_xi h)
  rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_mul, RingHom.map_neg, map_mul, map_mul, map_neg, Valuation.map_neg, h1, one_mul]

theorem top_idele (hc : c.Is) (pre : PreT v o)
    (hs : ∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT n h) (c.x n).L v.NT LZ x)
    {α : (AE D)ˣ} (hα : ∀ (x : Pl D) (S : HSp D) (L : Lat S) y,
      y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x)) :
    ∃ m₀ : (AE D)ˣ, (∀ x ∈ v.tP, IsU x (m₀ : AE D)) ∧ ∀ j (h : j + 2 * 0 + 2 = D.R.m),
      (∀ x, x ∉ v.tP → IsU x ((m₀ : AE D) * cA D m₀ *
        incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ))) ∧
      (∀ i, valuation k ((o.p i).pr (incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ))) =
        valuation k ((o.q.1 : 𝒪[k]) : k)) ∧
      ∀ x, x ∉ v.tP → ∀ LL : Lat (c.bes j 0 h).L, IsSelfDualC _ LL →
        (∀ a ∈ idAt D (· = x), a • ratV (c.bes j 0 h).ζ ∈ latV _ LL (· = x) ↔
          ((m₀⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) →
        ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT (j + 1 + 1) h) (c.x (j + 1 + 1)).L v.NT LZ x ∧
          ∀ w ∈ latO (c.X (j + 1)) c.Lz ((c.x (j + 1)).L : Set _) (LZ : Set _) (· = x),
            kap (v.τ j h) (c.X (j + 1)) w ∈ latO (c.bes j 0 h).L (c.X (j + 1)) (LL : Set _) ((c.x (j + 1)).L : Set _) (· = x) := by
  by_cases hex : ∃ j, j + 2 * 0 + 2 = D.R.m
  swap
  · exact ⟨1, fun x _ => IsU.one x, fun j h => absurd ⟨j, h⟩ hex⟩
  obtain ⟨j, h⟩ := hex
  obtain ⟨lam, hτ, hv⟩ := pre.lam j h
  have hn := tau_norm (pre.tau j h) hτ
  have hξ := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hlam : lam ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hn
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hξ (star_ne_zero.2 hξ))) pre.line.2 hn.symm
  obtain ⟨μ, hμ⟩ := line_idele (c.oT (j + 1 + 1) h) pre.line
    (GlobalTheory.CosScalar.selfDual_full _ _ (hc.x (j + 1 + 1) (by omega)).sd) v.NT (· ∈ v.tP)
    (hs (j + 1 + 1) h)
  obtain ⟨m₀, m1, m2⟩ := patch v.tP (fun _ => 1) (α * μ * inU lam hlam * (xiU D * cU α)⁻¹)
  refine ⟨m₀, fun x hx a ha => by rw [m1 x hx a ha, Units.val_one, one_mul], fun j' h' => ?_⟩
  obtain rfl : j = j' := by omega
  have hn' := congrArg (incA D) hn
  refine ⟨fun x hx a ha => ?_, fun i => ?_, fun x hx LL hLL hm => ?_⟩
  · obtain ⟨LZ, hLZ, ho⟩ := hs (j + 1 + 1) h x hx
    have h1 := (line_norm pre.line hLZ fun a ha => (orth_line _ ho _ a).trans (hμ x hx a ha)).neg a ha
    rw [h1]
    simp only [RingHom.map_mul, RingHom.map_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg] at hn'
    generalize incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ) = t at hn' ⊢
    generalize incA D (star o.ζ₀ ⬝ᵥ c.Lz.gram *ᵥ o.ζ₀) = t₀ at hn' ⊢
    have e1 := m2 x hx _ (Ideal.mul_mem_left _ (cA D m₀ * t) ha)
    have e2 := congrArg (cA D) (m2 x hx _ (id_conj ha))
    generalize hm' : α * μ * inU lam hlam * (xiU D * cU α)⁻¹ = m at e1 e2
    have f2 : (m : AE D) = α * μ * incA D lam * (incA D D.host.xi0⁻¹ * cA D (α⁻¹ : (AE D)ˣ)) := by
      rw [← hm', mul_inv]
      simp only [Units.val_mul, inU_val, cU_inv, xiU, inU_inv]
    have f3 : cA D (m : AE D) = cA D α * cA D μ * incA D (star lam) * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) := by
      rw [f2]
      simp only [RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA, cA_xi_inv, FrameLat.cA_incA lam]
    rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA, f3] at e2
    have g1 := α.mul_inv
    have g2 : cA D (α : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU α).mul_inv
    have g3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
    refine iff_of_eq (congrArg (· ∈ _) ?_)
    rw [f2] at e1
    generalize incA D D.host.xi0 = ξ at *
    generalize incA D D.host.xi0⁻¹ = ξ' at *
    generalize incA D lam = l at *
    generalize incA D (star lam) = l' at *
    generalize cA D (α : AE D) = β at *
    generalize cA D ((α⁻¹ : (AE D)ˣ) : AE D) = β' at *
    generalize ((α⁻¹ : (AE D)ˣ) : AE D) = α' at *
    generalize cA D (μ : AE D) = ν at *
    generalize cA D (m₀ : AE D) = n₀ at *
    linear_combination -e1 - (α * μ * l * ξ' * β' * t) * e2 + (α * α' * β * β' * μ * ν * ξ' * ξ' * a) * hn' +
      (μ * ν * t₀ * a * β * β' * ξ * ξ * ξ' * ξ') * g1 + (μ * ν * t₀ * a * ξ * ξ * ξ' * ξ') * g2 +
      (μ * ν * t₀ * a * (ξ * ξ' + 1)) * g3
  · have := congrArg (fun t => valuation k ((o.p i).pr t)) hn'
    simp only [RingHom.map_mul (incA D) (lam * star lam), RingHom.map_mul (incA D) lam, RingHom.map_mul (incA D) (-_),
      RingHom.map_neg, RingHom.map_mul (o.p i).pr, Valuation.map_mul, Valuation.map_neg, (hv i).1, (hv i).2, one_mul,
      val_norm_xi (pre.char i).2] at this
    rw [this, pre.normT i]
  · obtain ⟨LZ, hLZ, ho⟩ := hs (j + 1 + 1) h x hx
    refine ⟨LZ, hLZ, ho, kap_of (v.τ j h) (c.bes j 0 h).line pre.line hlam hτ hLL hLZ (hc.x (j + 1) (by omega)).sd (hα x)
      (fun a ha => (orth_line _ ho _ a).trans (hμ x hx a ha)) fun a ha => ?_⟩
    rw [hm a ha, inv_same (m2 x hx) a ha]

def gam (α : (AE D)ˣ) : (AE D)ˣ := α * (xiU D * cU α)⁻¹

theorem gam_norm (α : (AE D)ˣ) : (gam α : AE D) * cA D (gam α : AE D) * incA D (D.host.xi0 * star D.host.xi0) = 1 := by
  have g1 := α.mul_inv
  have g2 : cA D (α : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU α).mul_inv
  have g3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  rw [gam, mul_inv]
  simp only [Units.val_mul, cU_inv, xiU, inU_inv, RingHom.map_mul, GlobalTheory.SeeSaw.cA_cA, cA_xi_inv, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg]
  generalize incA D D.host.xi0 = ξ at *
  generalize incA D D.host.xi0⁻¹ = ξ' at *
  generalize cA D (α : AE D) = β at *
  generalize cA D ((α⁻¹ : (AE D)ˣ) : AE D) = β' at *
  generalize ((α⁻¹ : (AE D)ˣ) : AE D) = α' at *
  linear_combination (β * β' * ξ * ξ * ξ' * ξ') * g1 + (ξ * ξ * ξ' * ξ') * g2 + (ξ * ξ' + 1) * g3

theorem level_norm (pre : PreT v o) (α m₀ : (AE D)ˣ) (h0 : ∀ j (h : j + 2 * 0 + 2 = D.R.m),
      (∀ x, x ∉ v.tP → IsU x ((m₀ : AE D) * cA D m₀ *
        incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ))) ∧
      (∀ i, valuation k ((o.p i).pr (incA D (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ))) =
        valuation k ((o.q.1 : 𝒪[k]) : k))) (ρ : ℕ) : ∀ j (h : j + 2 * ρ + 2 = D.R.m),
      (∀ x, x ∉ v.tP → IsU x (((gam α ^ ρ * m₀ : (AE D)ˣ) : AE D) * cA D ((gam α ^ ρ * m₀ : (AE D)ˣ) : AE D) *
        incA D (star (c.bes j ρ h).ζ ⬝ᵥ (c.bes j ρ h).L.gram *ᵥ (c.bes j ρ h).ζ))) ∧
      (∀ i, valuation k ((o.p i).pr (incA D (star (c.bes j ρ h).ζ ⬝ᵥ (c.bes j ρ h).L.gram *ᵥ (c.bes j ρ h).ζ))) =
        valuation k ((o.q.1 : 𝒪[k]) : k)) := by
  induction ρ with
  | zero => simpa only [pow_zero, one_mul] using h0
  | succ σ ih =>
    intro j h
    obtain ⟨i1, i2⟩ := ih (j + 1 + 1) (idx_step h)
    have hn : star (c.bes j (σ + 1) h).ζ ⬝ᵥ (c.bes j (σ + 1) h).L.gram *ᵥ (c.bes j (σ + 1) h).ζ = _ := (c.lnk j σ h).norm
    rw [hn, RingHom.map_mul]
    refine ⟨fun x hx => ?_, fun i => ?_⟩
    · convert i1 x hx using 1
      rw [pow_succ', mul_assoc (gam α), Units.val_mul, RingHom.map_mul]
      generalize ((gam α ^ σ * m₀ : (AE D)ˣ) : AE D) = u
      generalize incA D (star (c.bes (j + 1 + 1) σ (idx_step h)).ζ ⬝ᵥ (c.bes (j + 1 + 1) σ (idx_step h)).L.gram *ᵥ
        (c.bes (j + 1 + 1) σ (idx_step h)).ζ) = t
      linear_combination (u * cA D u * t) * gam_norm α
    · rw [RingHom.map_mul, Valuation.map_mul, val_norm_xi (pre.char i).2, one_mul, i2 i]

def cond (α : (AE D)ˣ) : (AE D)ˣ := xiU D * α * cU α

def bB (α m₀ : (AE D)ˣ) (ρ : ℕ) (i : Fin ρ) : (AE D)ˣ := cond α ^ (ρ - i.1) * (gam α ^ ρ * m₀)

def bJ (α m₀ : (AE D)ˣ) (ρ : ℕ) (i : Fin ρ) : (AE D)ˣ := α⁻¹ * bB α m₀ ρ i

theorem bB_step (α m₀ : (AE D)ˣ) (ρ : ℕ) (i j : Fin ρ) (h : j.1 = i.1 + 1) : bB α m₀ ρ i = cond α * bB α m₀ ρ j := by
  have := j.2
  rw [bB, bB, show ρ - i.1 = ρ - j.1 + 1 by omega, pow_succ', mul_assoc]

theorem bJ_step (α m₀ : (AE D)ˣ) (ρ : ℕ) (i j : Fin ρ) (h : j.1 = i.1 + 1) : bJ α m₀ ρ i = cond α * bJ α m₀ ρ j := by
  rw [bJ, bJ, bB_step α m₀ ρ i j h, mul_left_comm]

theorem cond_gam (α : (AE D)ˣ) : cond α * gam α = α * α := by
  rw [cond, gam, mul_right_comm (xiU D), mul_comm α, mul_mul_mul_comm, mul_inv_cancel, one_mul]

theorem bJ_succ (α m₀ : (AE D)ˣ) (σ : ℕ) (i : Fin (σ + 1)) :
    bJ α m₀ (σ + 1) i = α * (cond α ^ (σ - i.1) * (gam α ^ σ * m₀)) := by
  have := i.2
  rw [bJ, bB, show σ + 1 - i.1 = σ - i.1 + 1 by omega, pow_succ', pow_succ', mul_assoc (gam α), mul_mul_mul_comm, cond_gam,
    mul_assoc α, inv_mul_cancel_left]

theorem bJ_last (α m₀ : (AE D)ˣ) (ρ : ℕ) (r : Fin ρ) (hr : r.1 + 1 = ρ) :
    bJ α m₀ ρ r = xiU D * cU α * (gam α ^ ρ * m₀) := by
  rw [bJ, bB, show ρ - r.1 = 1 by omega, pow_one, cond, mul_comm (xiU D) α, mul_assoc α, mul_assoc α, inv_mul_cancel_left]

def HasIdeals {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (b : Fin ρ → (AE D)ˣ) : Prop :=
  ∀ x : Pl D, MonoAt d L L₀ x ∧ (∀ i, ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔
    (((b i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧
    ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV S L (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x)

theorem exists_N (hc : c.Is) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (hM : ∀ j ρ h, IsSelfDualC _ (M j ρ h))
    (b b' : ∀ ρ, Fin ρ → (AE D)ˣ) : ∃ N : ∀ j, Lat (c.V j), (∀ j, IsSelfDualC _ (N j)) ∧
      (∀ j ρ h, HasIdeals (c.bes j ρ h).d (N j) (M j ρ h) (b ρ)) ∧
      ∀ j ρ h, HasIdeals (c.jac j ρ h).d (N (j + 1)) (c.x (j + 1)).L (b' ρ) := by
  have HB : ∀ j, ∃ N : Lat (c.V j), IsSelfDualC _ N ∧ ∀ ρ h, HasIdeals (c.bes j ρ h).d N (M j ρ h) (b ρ) := fun j => by
    by_cases hex : ∃ ρ, j + 2 * ρ + 2 = D.R.m
    · obtain ⟨ρ, h⟩ := hex
      obtain ⟨N, h1, h2⟩ := GlobalTheory.FinPl.exists_selfDual_mono_idele D _ _ ρ (c.bes j ρ h).d (M j ρ h) (hM j ρ h) (b ρ)
      refine ⟨N, h1, fun ρ' h' => ?_⟩
      obtain rfl : ρ = ρ' := by omega
      exact h2
    · exact ⟨_, GlobalTheory.WeilAtPlace.isSelfDualC_frameLat _, fun ρ h => absurd ⟨ρ, h⟩ hex⟩
  have H1 : ∀ j, ∃ N : Lat (c.V (j + 1)), IsSelfDualC _ N ∧
      (∀ ρ h, HasIdeals (c.bes (j + 1) ρ h).d N (M (j + 1) ρ h) (b ρ)) ∧
      ∀ ρ h, HasIdeals (c.jac j ρ h).d N (c.x (j + 1)).L (b' ρ) := fun j => by
    by_cases hex : ∃ ρ, j + 2 * ρ + 2 = D.R.m
    · obtain ⟨ρ, h⟩ := hex
      obtain ⟨N, h1, h2⟩ := GlobalTheory.FinPl.exists_selfDual_mono_idele D _ _ ρ (c.jac j ρ h).d (c.x (j + 1)).L (hc.x (j + 1) (by omega)).sd (b' ρ)
      refine ⟨N, h1, fun ρ' h' => by omega, fun ρ' h' => ?_⟩
      obtain rfl : ρ = ρ' := by omega
      exact h2
    · obtain ⟨N, h1, h2⟩ := HB (j + 1)
      exact ⟨N, h1, h2, fun ρ h => absurd ⟨ρ, h⟩ hex⟩
  obtain ⟨N₀, h0, h0'⟩ := HB 0
  choose N₁ h1 h2 h3 using H1
  refine ⟨fun j => Nat.casesOn (motive := fun j => Lat (c.V j)) j N₀ N₁, fun j => ?_, fun j => ?_, h3⟩
  · cases j
    exacts [h0, h1 _]
  · cases j
    exacts [h0', h2 _]

theorem exists_goodAt : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → IsSelfDualC c.T v.NT → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT n h) (c.x n).L v.NT LZ x) → ∃ (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, Frame (o.p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j)) ∧ (∀ x, GoodAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ (∀ x, x ∉ v.tP → SplitAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ ∀ j ρ h i, GluedCore (c.B j ρ h) (M j ρ h) o.q (o.β j i) (β₀ j ρ h i) (o.Q j i) := by
  intro D c v k _ _ _ _ ι o hc _ pre hs
  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D c.ψ hc.std
  obtain ⟨m₀, hT, htop⟩ := top_idele hc pre hs fun x => (hα x).1
  have hlev := level_norm pre α m₀ fun j h => ⟨(htop j h).1, (htop j h).2.1⟩
  have hP : Places o.p o.I (· ∈ v.tP) := ⟨pre.nodup, pre.all, pre.inj, pre.tP, fun i => (pre.char i).2⟩
  have hmT : ∀ ρ, ∀ x ∈ v.tP, IsU x ((gam α ^ ρ * m₀ : (AE D)ˣ) : AE D) := fun ρ x hx => by
    obtain ⟨i, rfl⟩ := (pre.tP x).1 hx
    have h1 := isU_alpha (pre.char i).2 pre.line (hα _).1
    have h2 : IsU (o.p i).v ((xiU D * cU α : (AE D)ˣ) : AE D) := (isU_xi (pre.char i).2).mul h1.conj
    have h3 : IsU (o.p i).v (gam α : AE D) := h1.mul (h2.inv (Units.mul_inv _))
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    exact (h3.pow ρ).mul (hT _ hx)
  have hcore := fun j ρ (h : j + 2 * ρ + 2 = D.R.m) =>
    GlobalTheory.FinPl.CoreIdele.exists_core D k ι o.p o.I _ hP o.q (Fin (c.X j).rank) ρ (c.B j ρ h) (o.β j) (o.Q j) (c.x j).L (hc.x j (by omega)).sd
      (pre.latT j (by omega)) (hlev ρ j h).2 (gam α ^ ρ * m₀) (hmT ρ) (hlev ρ j h).1
  choose M β₀ hM hglue hoff hz using hcore
  obtain ⟨N, hN, hB, hJ⟩ := exists_N hc M hM (bB α m₀) (bJ α m₀)
  have hψ : ∀ x : Pl D, ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE c.ψ (s * o) = 1) ↔
      (((cond α)⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x) := fun x s hs => by
    rw [(hα x).2 s hs, cond, mul_inv, mul_inv, Units.val_mul, Units.val_mul, cU_inv, xiU, inU_inv]
  refine ⟨N, M, β₀, fun j _ => hN j, fun x => ⟨fun j ρ h => ?_, fun j σ h => ?_⟩, fun x hx => ⟨fun j ρ h => ?_, fun j h => ?_⟩,
    hglue⟩
  · have sx := (hc.x (j + 1) (by omega)).sd
    exact ⟨TamePlaces.tame D x, hN j, hM j ρ h, hN (j + 1), sx, (hB j ρ h x).1, (hJ j ρ h x).1,
      prim_of _ (bB_step α m₀ ρ) (hψ x) (hB j ρ h x).2.1,
      cols_bf _ _ (fun i => (mul_inv_cancel_left α _).symm) ((hα x).1 _ _) (hB j ρ h x).2.1 (hJ j ρ h x).2.1,
      last_of _ _ (hM j ρ h) (hN (j + 1)) (bJ_last α m₀ ρ) ((hα x).1 _ _) (hJ j ρ h x).2.2 (hz j ρ h x)⟩
  · have sx := (hc.x (j + 1) (by omega)).sd
    have h' := idx_step h
    exact ⟨TamePlaces.tame D x, hN (j + 1), sx, hN (j + 1 + 1), hM _ σ h', (hJ j _ h x).1, (hB _ σ h' x).1,
      prim_of _ (bJ_step α m₀ _) (hψ x) (hJ j _ h x).2.1,
      cols_fb _ _ _ (fun i => bJ_succ α m₀ σ i.castSucc)
        (by rw [bJ_succ, Fin.val_last, Nat.sub_self, pow_zero, one_mul]) ((hα x).1 _ _) (hJ j _ h x).2.1 (hB _ σ h' x).2.1
        (hB _ σ h' x).1 (hz _ σ h' x)⟩
  · obtain ⟨LL, h1, h2, -⟩ := hoff j ρ h x hx
    exact ⟨LL, h1, h2⟩
  · obtain ⟨LL, h1, h2, h3⟩ := hoff j 0 h x hx
    rw [pow_zero, one_mul] at h3
    obtain ⟨LZ, g1, g2, g3⟩ := (htop j h).2.2 x hx LL h1 h3
    exact ⟨LL, LZ, h1, g1, h2, g2, g3⟩

end GlobalTheory.GoodPos

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticesGoodPositionAllPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattices_goodPosition_all_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → IsSelfDualC c.T v.NT → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT n h) (c.x n).L v.NT LZ x) → ∃ (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, Frame (o.p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j)) ∧ (∀ x, GoodAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ (∀ x, x ∉ v.tP → SplitAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ ∀ j ρ h i, GluedCore (c.B j ρ h) (M j ρ h) o.q (o.β j i) (β₀ j ρ h i) (o.Q j i) := by
  first | exact @GlobalTheory.GoodPos.exists_goodAt | exact GlobalTheory.GoodPos.exists_goodAt | (intros; apply GlobalTheory.GoodPos.exists_goodAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePatchedAtPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePatchedAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.Patch

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem mul_eq_zero_of_ne {x w : Pl D} (h : w ≠ x) {a b : AE D} (ha : a ∈ idAt D (· = x)) (hb : b ∈ idAt D (· = w)) :
    a * b = 0 := by
  apply eq_zero_of_comp
  · rw [map_mul, infPart_of_idAt ha, zero_mul]
  · intro v
    rw [map_mul]
    by_cases hv : v = x
    · rw [compAt_of_idAt hb (w := v) (fun h' => h (h'.symm.trans hv)), mul_zero]
    · rw [compAt_of_idAt ha (w := v) hv, zero_mul]

theorem mulVec_eq_of_ne {S : HSp D} {x w : Pl D} (h : w ≠ x) {g : GA D S} (hg : g ∈ grpAt S (· = x))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = w)) : mt S g *ᵥ y = y := by
  have hg' := (mem_congGrp _ g).1 hg
  have h0 : (mt S g - 1) *ᵥ y = 0 := by
    funext i
    show ∑ j, (mt S g - 1) i j * y j = 0
    exact Finset.sum_eq_zero fun j _ => mul_eq_zero_of_ne h (hg' i j) (hy j)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

theorem latV_eq_off {S : HSp D} {x w : Pl D} (h : w ≠ x) {g : GA D S} (hg : g ∈ grpAt S (· = x)) {L M : Lat S}
    (hm : Moves S g L M (· = w)) : latV S M (· = w) = latV S L (· = w) := by
  ext y
  constructor
  · intro hy
    have hid := latV_idAt hy
    rw [hm y hid, mulVec_eq_of_ne h hg hid]
    exact hy
  · intro hy
    have hid := latV_idAt hy
    have := (hm y hid).1 hy
    rwa [mulVec_eq_of_ne h hg hid] at this

theorem latV_le_of_moves {S : HSp D} {P : Pl D → Prop} {g : GA D S} {L M M' : Lat S} (hm : Moves S g L M P)
    (hm' : Moves S g L M' P) : latV S M P ≤ latV S M' P := by
  intro y hy
  have hid := latV_idAt hy
  have hz : ∀ i, (mt S g⁻¹ *ᵥ y) i ∈ idAt D P := fun i => by
    show ∑ j, mt S g⁻¹ i j * y j ∈ idAt D P
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hid j)
  have he : mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← FinPlLoc.mt_mul, mul_inv_cancel, FinPlLoc.mt_one, Matrix.one_mulVec]
  have h1 := (hm _ hz).2 (by rw [he]; exact hy)
  have h2 := (hm' _ hz).1 h1
  rwa [he] at h2

theorem patch : ∀ (D : D7) (S : HSp D) (L L' : Lat S), IsSelfDualC S L → IsSelfDualC S L' → ∀ Z : Finset (Pl D),
    ∃ M : Lat S, IsSelfDualC S M ∧ (∀ x ∈ Z, latV S M (· = x) = latV S L' (· = x)) ∧
      ∀ x, x ∉ Z → latV S M (· = x) = latV S L (· = x) := by
  classical
  intro D S L L' hL hL' Z
  induction Z using Finset.induction_on with
  | empty => exact ⟨L, hL, fun x hx => absurd hx (Finset.notMem_empty x), fun _ _ => rfl⟩
  | insert x Z hx ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨g, hg, hgm⟩ := GlobalTheory.T.selfDualLattices_conjugate_at_finitePlace D S M L' hM hL' x
    obtain ⟨M', hM', hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S M hM).1 g
    refine ⟨M', hM', fun w hw => ?_, fun w hw => ?_⟩
    · by_cases hwx : w = x
      · subst hwx
        exact le_antisymm (latV_le_of_moves (hmv _) hgm) (latV_le_of_moves hgm (hmv _))
      · rw [latV_eq_off hwx hg (hmv _)]
        exact h1 w ((Finset.mem_insert.1 hw).resolve_left hwx)
    · rw [Finset.mem_insert, not_or] at hw
      rw [latV_eq_off hw.1 hg (hmv _)]
      exact h2 w hw.2

end GlobalTheory.FinPl.Patch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePatchedAtPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_lattice_patched_at_places : ∀ (D : D7) (S : HSp D) (L L' : Lat S), IsSelfDualC S L → IsSelfDualC S L' → ∀ Z : Finset (Pl D), ∃ M : Lat S, IsSelfDualC S M ∧ (∀ x ∈ Z, latV S M (· = x) = latV S L' (· = x)) ∧ ∀ x, x ∉ Z → latV S M (· = x) = latV S L (· = x) := by
  first | exact @GlobalTheory.FinPl.Patch.patch | exact GlobalTheory.FinPl.Patch.patch | (intros; apply GlobalTheory.FinPl.Patch.patch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProof
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw.ShapeExProof

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem places {v : VCom c} {o : TDat c k ι} (hpre : PreT v o) : Places o.p o.I (· ∈ v.tP) :=
  ⟨hpre.nodup, hpre.all, hpre.inj, hpre.tP, fun i => (hpre.char i).2⟩

theorem gluedCore_congr {ρ : ℕ} {B : BesLev D ρ} {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {L L' : Lat B.V₀}
    {q : Unif k} {β : Frame p B.A n} {β₀ : Frame p B.V₀ (n ⊕ Fin 1)} {P : Pair k n}
    (hL : latV B.V₀ L' (· = p.v) = latV B.V₀ L (· = p.v)) (g : GluedCore B L q β β₀ P) : GluedCore B L' q β β₀ P :=
  ⟨g.unit, g.sum, g.norm, fun y => by rw [hL]; exact g.lat y⟩

end GlobalTheory.SeeSaw.ShapeExProof

namespace GlobalTheory.SeeSaw.ShapeExProof

theorem shapeEx : ∀ D : D7, GlobalTheory.SeeSaw.ShapeEx D := by
  intro D c v k _ _ _ _ ι o hc hdisj hNT hpre hNv hgP hLZ
  obtain ⟨N0, M0, β₀, hN0, hgood0, hsplit0, hglued0⟩ := GlobalTheory.T.exists_lattices_goodPosition_all_places D c v k ι o hc hNT hpre hLZ
  have key : ∃ (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀),
      (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j) ∧ ∀ x ∈ v.gP, latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
      (∀ j ρ h, ∀ x ∈ v.gP, latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
      (∀ x, GoodAt { v with N := N } { o with M := M } x) ∧
      (∀ x, x ∉ v.tP → SplitAt { v with N := N } { o with M := M } x) ∧
      (∀ j ρ h, ∀ x, x ∉ v.gP → latV _ (M j ρ h) (· = x) = latV _ (M0 j ρ h) (· = x)) := by
    rcases v.gP.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
    · refine ⟨N0, M0, fun j hj => ⟨hN0 j hj, fun x hx => by simp [hE] at hx⟩, fun j ρ h x hx => by simp [hE] at hx,
        fun x => ⟨(hgood0 x).1, (hgood0 x).2⟩, fun x hx => ⟨(hsplit0 x hx).1, (hsplit0 x hx).2⟩, fun _ _ _ _ _ => rfl⟩
    · have hsdM : ∀ j ρ h, IsSelfDualC _ (o.M j ρ h) := fun j ρ h => ((hgP x0 hx0).1.bf j ρ h).sdV₀
      have hsdM0 : ∀ j ρ h, IsSelfDualC _ (M0 j ρ h) := fun j ρ h => ((hgood0 x0).bf j ρ h).sdV₀
      have hpN : ∀ j, ∃ L : Lat (c.V j), j < D.R.m → (IsSelfDualC (c.V j) L ∧
          (∀ x ∈ v.gP, latV (c.V j) L (· = x) = latV (c.V j) (v.N j) (· = x)) ∧
          ∀ x, x ∉ v.gP → latV (c.V j) L (· = x) = latV (c.V j) (N0 j) (· = x)) := by
        intro j
        by_cases hj : j < D.R.m
        · obtain ⟨L, h1, h2, h3⟩ := GlobalTheory.T.exists_selfDual_lattice_patched_at_places D (c.V j) (N0 j) (v.N j) (hN0 j hj) (hNv j hj) v.gP
          exact ⟨L, fun _ => ⟨h1, h2, h3⟩⟩
        · exact ⟨N0 j, fun h => absurd h hj⟩
      choose N hN using hpN
      have hpM : ∀ j ρ h, ∃ L : Lat (c.bes j ρ h).V₀, IsSelfDualC _ L ∧
          (∀ x ∈ v.gP, latV _ L (· = x) = latV _ (o.M j ρ h) (· = x)) ∧
          ∀ x, x ∉ v.gP → latV _ L (· = x) = latV _ (M0 j ρ h) (· = x) := fun j ρ h =>
        GlobalTheory.T.exists_selfDual_lattice_patched_at_places D _ (M0 j ρ h) (o.M j ρ h) (hsdM0 j ρ h) (hsdM j ρ h) v.gP
      choose M hM using hpM
      have hat : ∀ x, (x ∈ v.gP → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧
            (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x)) ∧
          (x ∉ v.gP → (GoodAt { v with N := N0 } { o with M := M0, β₀ := β₀ } x → GoodAt { v with N := N } { o with M := M } x) ∧
            (SplitAt { v with N := N0 } { o with M := M0, β₀ := β₀ } x → SplitAt { v with N := N } { o with M := M } x)) := by
        intro x
        refine ⟨fun hx => ?_, fun hx => ?_⟩
        · have := GlobalTheory.T.goodPosition_splitLines_read_completions_at_place D c v k ι o N M x (fun j hj => ⟨hNv j hj, (hN j hj).1, (hN j hj).2.1 x hx⟩)
            (fun j ρ h => ⟨hsdM j ρ h, (hM j ρ h).1, (hM j ρ h).2.1 x hx⟩)
          exact ⟨fun g => let g' := this.1 g; ⟨g'.1, g'.2⟩, fun s => let s' := this.2 s; ⟨s'.1, s'.2⟩⟩
        · have := GlobalTheory.T.goodPosition_splitLines_read_completions_at_place D c { v with N := N0 } k ι { o with M := M0, β₀ := β₀ } N M x
            (fun j hj => ⟨hN0 j hj, (hN j hj).1, (hN j hj).2.2 x hx⟩)
            (fun j ρ h => ⟨hsdM0 j ρ h, (hM j ρ h).1, (hM j ρ h).2.2 x hx⟩)
          exact ⟨fun g => let g' := this.1 g; ⟨g'.1, g'.2⟩, fun s => let s' := this.2 s; ⟨s'.1, s'.2⟩⟩
      refine ⟨N, M, fun j hj => ⟨(hN j hj).1, (hN j hj).2.1⟩, fun j ρ h => (hM j ρ h).2.1, fun x => ?_, fun x hxT => ?_,
        fun j ρ h => (hM j ρ h).2.2⟩
      · by_cases hx : x ∈ v.gP
        · exact ((hat x).1 hx).1 (hgP x hx).1
        · exact ((hat x).2 hx).1 (hgood0 x)
      · by_cases hx : x ∈ v.gP
        · exact ((hat x).1 hx).2 (hgP x hx).2
        · exact ((hat x).2 hx).2 (hsplit0 x hxT)
  obtain ⟨N, M, hN, hM, hgood, hsplit, hoff⟩ := key
  have hd : ∀ j, ∃ d : WO (c.X j) (c.X (j + 1)) →₀ ℂ, CombAt (· ∈ v.tP) d ∧ (j < D.R.m → ∀ f,
      Vac c.ψ _ _ (c.x j).L (c.x (j + 1)).L (· ∈ v.tP) f →
      OverAll c.ψ (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
        (comb c.ψ _ _ d f)) := by
    intro j
    by_cases hj : j < D.R.m
    · obtain ⟨d, hdc, hdr⟩ := ((GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof D) k ι o.p o.I (· ∈ v.tP) (places hpre) (Fin (c.X (j + 1)).rank)
        (Fin (c.X j).rank) c.ψ hc.std (c.X j) (c.X (j + 1)) (o.β j) (o.β (j + 1)) (c.x j).L (c.x (j + 1)).L
        (hc.x j hj.le).sd (hc.x (j + 1) hj).sd (fun i => phiOne (o.Q j i) (o.Q (j + 1) i))).1 (fun i => GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _)
      exact ⟨d, hdc, fun _ => hdr⟩
    · exact ⟨0, fun u hu => by simp at hu, fun h => absurd h hj⟩
  choose dT hdC hdR using hd
  have hpT : ∀ i, (o.p i).v ∉ v.gP := fun i hg =>
    Finset.disjoint_left.mp hdisj hg ((hpre.tP _).mpr ⟨i, rfl⟩)
  refine ⟨N, dT, M, β₀, hN, hM, hdC, ⟨⟨hpre.1, hpre.2, hpre.3, hpre.4, hpre.5, hpre.6, hpre.7, hpre.8, hpre.9, hpre.10, hpre.11⟩,
    fun x => ⟨(hgood x).1, (hgood x).2⟩, fun x hx => ⟨(hsplit x hx).1, (hsplit x hx).2⟩,
    fun j ρ h i => gluedCore_congr (hoff j ρ h _ (hpT i)) (hglued0 j ρ h i), fun j hj => hdR j hj, fun j => rfl⟩⟩

end GlobalTheory.SeeSaw.ShapeExProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeShapeExistsProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawLatticeShapeExists_proof : ∀ D : D7, GlobalTheory.SeeSaw.ShapeEx D := by
  first | exact @GlobalTheory.SeeSaw.ShapeExProof.shapeEx | exact GlobalTheory.SeeSaw.ShapeExProof.shapeEx | (intros; apply GlobalTheory.SeeSaw.ShapeExProof.shapeEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMoveSelfDualLatticeSplitFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMoveSelfDualLatticeSplitFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLat

theorem exists_selfDual_frames : ∀ (D : D7) (S : HSp D) (L₀ : GlobalTheory.FinPl.Lat S), IsSelfDualC S L₀ → ∀ (I : Type) [Finite I] (K : I → Type) [∀ i, Field (K i)] [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)] [∀ i, IsNonarchimedeanLocalField (K i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (K i)) (Y : I → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : ∀ i, GlobalTheory.LocMod.Frame (K i) S.rank (Y i)), (∀ i i', (q i).v = (q i').v → i = i') → ∃ L : GlobalTheory.FinPl.Lat S, IsSelfDualC S L ∧ ∀ i, IntIn (q i) S (F i) L := by
  intro D S L₀ hL₀ I _ K _ _ _ _ q Y _ _ F hinj
  have key : ∀ s : Finset I, ∃ L : GlobalTheory.FinPl.Lat S, IsSelfDualC S L ∧ ∀ i ∈ s, IntIn (q i) S (F i) L := by
    intro s
    refine Finset.induction_on s ⟨L₀, hL₀, by simp⟩ ?_
    intro j s hj ih
    obtain ⟨L, hL, hs⟩ := ih
    obtain ⟨L', hL', hother, hq⟩ := GlobalTheory.T.exists_selfDualLattice_prescribed_splitPlace D (K j) (q j) S (Y j) (F j) L hL
    refine ⟨L', hL', ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hq
    · have hne : (q i).v ≠ (q j).v := fun h => hj (by obtain rfl := hinj i j h; exact hi')
      have h1 := hs i hi'
      unfold IntIn at h1 ⊢
      rw [hother _ hne]
      exact h1
  haveI := Fintype.ofFinite I
  obtain ⟨L, hL, h⟩ := key Finset.univ
  exact ⟨L, hL, fun i => h i (Finset.mem_univ i)⟩

end GlobalTheory.SplitLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMoveSelfDualLatticeSplitFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_move_selfDual_lattice_split_frames : ∀ (D : D7) (S : HSp D) (L₀ : GlobalTheory.FinPl.Lat S), IsSelfDualC S L₀ → ∀ (I : Type) [Finite I] (K : I → Type) [∀ i, Field (K i)] [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)] [∀ i, IsNonarchimedeanLocalField (K i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (K i)) (Y : I → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : ∀ i, GlobalTheory.LocMod.Frame (K i) S.rank (Y i)), (∀ i i', (q i).v = (q i').v → i = i') → ∃ L : GlobalTheory.FinPl.Lat S, IsSelfDualC S L ∧ ∀ i, IntIn (q i) S (F i) L := by
  first | exact @GlobalTheory.SplitLat.exists_selfDual_frames | exact GlobalTheory.SplitLat.exists_selfDual_frames | (intros; apply GlobalTheory.SplitLat.exists_selfDual_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentity
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.LatShape

theorem coreFrame_beta_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n)
    {F F' : Frame k B.V₀.rank (n ⊕ Unit)} (h : p.IsCoreFrame B s FA F) (h' : p.IsCoreFrame B s FA F') : F.β = F'.β := by
  ext r (a | u)
  · rw [h.1, h'.1]
  · cases u
    rw [h.2, h'.2]

theorem exists_shape_integral_in_normal_frames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∃ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (dT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, GlobalTheory.FinPl.Frame (o.p i) (y.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)), ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ } ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.tP) (dT j)) ∧ (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) ∧ ∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y m b₀ k _ _ _ _ ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY
  have hfin := GlobalTheory.T.level_places_finite W hP
  have hsep := GlobalTheory.T.level_places_under_eq W hP
  have hsc : ∀ PP hP j, sc PP hP j ≠ 0 := by
    intro PP hP j h0
    have := (hFY PP hP).1 j
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hxi : ∀ PP hP, (ofSplit (l PP hP).q).xi ≠ 0 := by
    intro PP hP h0
    have e := (hFY PP hP).2.1 0
    have v2 := (hFY PP hP).1 (0 + 1 + 1)
    rw [e, h0, mul_zero, map_zero] at v2
    exact zero_ne_one v2
  let I := {PP : Pl D.host.E // PP ∈ (pk W).Pg ∨ QAll W PP}
  haveI : Finite I := hfin.to_subtype
  have hinj : ∀ i i' : I, (l i.1 i.2).q.v = (l i'.1 i'.2).q.v → i = i' := by
    intro i i' e
    rw [(l i.1 i.2).under, (l i'.1 i'.2).under] at e
    exact Subtype.ext (hsep _ _ i.2 i'.2 e)
  have hA : ∀ j, ∃ N' : GlobalTheory.FinPl.Lat (Yc D j), (j < D.R.m → IsSelfDualC (Yc D j) N') ∧
      ∀ PP h c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) N' := by
    intro j
    by_cases hj : j < D.R.m
    · obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.exists_self_dual_lattice_chain W hP j hj
      obtain ⟨N', hsd, hint⟩ := GlobalTheory.T.exists_move_selfDual_lattice_split_frames D (Yc D j) L₀ hL₀ I (fun i => (l i.1 i.2).k) (fun i => (l i.1 i.2).q)
        (fun _ => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (D.R.m - 1 - j))
        (fun i => FY i.1 i.2 j (D.R.m - 1 - j) (by have := (l i.1 i.2).hs; omega)) hinj
      refine ⟨N', fun _ => hsd, fun PP h c hc => ?_⟩
      obtain rfl : c = D.R.m - 1 - j := by have := (l PP h).hs; omega
      exact hint ⟨PP, h⟩
    · refine ⟨⊥, fun h => absurd h hj, fun PP h c hc => ?_⟩
      exfalso
      have := (l PP h).hs
      omega
  choose N₁ hN₁sd hN₁int using hA
  have hB : ∀ j ρ h, ∃ M' : GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀, IsSelfDualC (y.bes j ρ h).V₀ M' ∧
      ∀ PP hP (hj : j ≤ (l PP hP).s + 1)
        (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)),
        (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ →
        IntIn (l PP hP).q _ F₀ M' := by
    intro j ρ h
    obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.local_component_measure_relation W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY j ρ h
    have hj : ∀ i : I, j ≤ (l i.1 i.2).s + 1 := fun i => by have := (l i.1 i.2).hs; omega
    have hex : ∀ i : I, ∃ F : Frame (l i.1 i.2).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit),
        (ofSplit (l i.1 i.2).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc i.1 i.2 j) ((l i.1 i.2).FX j (hj i)) F := by
      intro i
      exact ((@GlobalTheory.LocMod.normalFrames_and_basePoint_exist D (l i.1 i.2).k _ _ _ _ (ofSplit (l i.1 i.2).q)
        (hxi i.1 i.2)).1 _ ρ _ _ _ (hsc i.1 i.2 j)).1
    choose F hF using hex
    obtain ⟨M', hsd, hint⟩ := GlobalTheory.T.exists_move_selfDual_lattice_split_frames D (y.bes j ρ h).V₀ L₀ hL₀ I (fun i => (l i.1 i.2).k) (fun i => (l i.1 i.2).q)
      (fun _ => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit) F hinj
    refine ⟨M', hsd, fun PP hP hj' F₀ hF₀ => ?_⟩
    have e := coreFrame_beta_eq _ _ _ _ (hF ⟨PP, hP⟩) hF₀
    intro z
    rw [← e]
    exact hint ⟨PP, hP⟩ z
  choose M₁ hM₁sd hM₁int using hB
  have hoffT := GlobalTheory.T.local_component_measure_value W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY
  have hbf := GlobalTheory.T.local_component_measure_bound W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY N₁ M₁ hN₁sd (fun PP h j c hc => hN₁int j PP h c hc) hM₁sd (fun PP hP j ρ h hj F₀ hF₀ => hM₁int j ρ h PP hP hj F₀ hF₀)
  have hfb := GlobalTheory.T.local_component_measure_scalar W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY N₁ M₁ hN₁sd (fun PP h j c hc => hN₁int j PP h c hc) hM₁sd (fun PP hP j ρ h hj F₀ hF₀ => hM₁int j ρ h PP hP hj F₀ hF₀)
  have hsp := GlobalTheory.T.local_component_measure_equation W u hP a y m b₀ k ι v o l bas hc hTau hT0 hvτ hvNT hoζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY N₁ M₁ hN₁sd (fun PP h j c hc => hN₁int j PP h c hc) hM₁sd (fun PP hP j ρ h hj F₀ hF₀ => hM₁int j ρ h PP hP hj F₀ hF₀)
  let G' : Finset (GlobalTheory.FinPl.Pl D) := hfin.toFinset.image (fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
  have hG' : ∀ x, x ∈ G' ↔ ∃ PP, (PP ∈ (pk W).Pg ∨ QAll W PP) ∧ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = x := by
    intro x
    simp only [G', Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hdisj' : Disjoint G' v.tP := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    obtain ⟨PP, hPP, rfl⟩ := (hG' x).1 hx
    rcases hPP with hg | hq
    · exact Finset.disjoint_left.1 hdisj ((hgP _).2 ⟨PP, hg, rfl⟩) hxT
    · exact hoffT PP hq hxT
  obtain ⟨N, dT, M, β₀, hN, -, hC, hS⟩ := GlobalTheory.T.seeSawLatticeShapeExists_proof D (commOf (pk W) u (mkGeo m b₀)) { v with gP := G', N := N₁ } k ι
    { o with M := M₁ } hc hdisj' (by show IsSelfDualC D.sp.X' v.NT; rw [hvNT]; exact hLT)
    ⟨hPre.nodup, hPre.all, hPre.inj, hPre.tP, hPre.char, hPre.latT, hPre.line, hPre.tau, hPre.lam, hPre.normT, hPre.topT⟩
    hN₁sd (fun x hx => by
      obtain ⟨PP, hPP, rfl⟩ := (hG' x).1 hx
      exact ⟨⟨hbf PP hPP, hfb PP hPP⟩, ⟨(hsp PP hPP).core, (hsp PP hPP).top⟩⟩)
    (fun n h x hx => by
      obtain ⟨LZ, h1, h2⟩ := hLZ n h x hx
      refine ⟨LZ, h1, ?_⟩
      show GlobalTheory.FinPl.OrthAt _ _ v.NT LZ x
      rw [hvNT]
      exact h2)
  refine ⟨N, dT, M, β₀, ?_, hC, fun j hj => (hN j hj).1, ?_⟩
  · exact ⟨⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, hS.pre.tP, hS.pre.char, hS.pre.latT, hS.pre.line, hS.pre.tau, hS.pre.lam,
      hS.pre.normT, hS.pre.topT⟩, fun x => ⟨(hS.good x).bf, (hS.good x).fb⟩,
      fun x hx => ⟨(hS.split x hx).core, (hS.split x hx).top⟩, hS.glued, hS.rep, hS.ram⟩
  · intro PP h j c hc
    have hj : j < D.R.m := by have := (l PP h).hs; omega
    have hx : (l PP h).q.v ∈ G' := by rw [(l PP h).under]; exact (hG' _).2 ⟨PP, h, rfl⟩
    have e : GlobalTheory.FinPl.latV (Yc D j) (N j) (· = (l PP h).q.v) = GlobalTheory.FinPl.latV (Yc D j) (N₁ j) (· = (l PP h).q.v) :=
      (hN j hj).2 _ hx
    intro z
    rw [e]
    exact hN₁int j PP h c hc z

end GlobalTheory.Fam.LatShape

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_identity : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∃ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (dT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, GlobalTheory.FinPl.Frame (o.p i) (y.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)), ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ } ∧ (∀ j, GlobalTheory.FinPl.CombAt (· ∈ v.tP) (dT j)) ∧ (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) ∧ ∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j) := by
  first | exact @GlobalTheory.Fam.LatShape.exists_shape_integral_in_normal_frames | exact GlobalTheory.Fam.LatShape.exists_shape_integral_in_normal_frames | (intros; apply GlobalTheory.Fam.LatShape.exists_shape_integral_in_normal_frames <;> assumption)
end
