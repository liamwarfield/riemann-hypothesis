module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartTraceCharacterIdempotentInverseDiffere
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntOfSmul
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LineIdeal

open GlobalTheory.GoodPos

variable {D : D7}

theorem herm_colY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D) (y : Fin S.rank → AE D) :
    hermAt S (colMul d.jY i a) y = a * cA D ((d.pX *ᵥ y) i) := by
  have e0 : colMul d.jY i a = a • fun k => d.jY k i := rfl
  have e1 := herm_smul S a 1 (fun k => d.jY k i) y
  rw [one_smul, RingHom.map_one, mul_one] at e1
  rw [e0, e1, ← herm_conj, herm_eq]
  congr 2
  have e2 : d.pX = adj d.jY ⬝ gA S := by
    change rat (d.e'ᴴ * S.gram) = _
    rw [rat_mul, rat_conjTranspose]; rfl
  rw [e2, ← mulVec_mulVec]
  rfl

theorem dual_line {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {x : Pl D} (hL : IsSelfDualC S L)
    (hm : MonoAt d L L₀ x) (i : Fin ρ) {b : (AE D)ˣ}
    (hX : ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔ ((b⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV S L (· = x) ↔ cA D (b : AE D) * a ∈ intAt D (· = x) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D S L x hL
  have he := idem_mem_intAt (D := D) (· = x)
  rw [hsd.2.2 (colMul d.jY i a) fun k => Ideal.mul_mem_right _ _ ha]
  constructor
  · intro H
    have h1 := H _ ((hX _ (Ideal.mul_mem_left _ (b : AE D) he.1)).2 (by rwa [Units.inv_mul_cancel_left]))
    have h2 : ∀ t : AE D, (d.pX *ᵥ colMul d.jX i t) i = t := fun t => by
      have : (d.pX *ᵥ colMul d.jX i t) i = t * (d.pX ⬝ d.jX) i i := by
        simp only [mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, d.pX_jX, Matrix.one_apply_eq, mul_one]
    rw [herm_colY, h2, RingHom.map_mul, cA_idem] at h1
    convert h1 using 1
    linear_combination (-cA D (b : AE D)) * (mem_idAt_iff _ a).1 ha
  · intro H y hy
    have h1 := (hX _ (mulVec_mem_idAt d.pX (hsd.1 y hy) i)).1 (((hm y).1 hy).1 i)
    have h2 := int_mul H (int_conj.2 h1)
    rw [herm_colY]
    convert h2 using 1
    have e : cA D (b : AE D) * cA D ((b⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU b).mul_inv
    rw [RingHom.map_mul]
    linear_combination (-a * cA D ((d.pX *ᵥ y) i)) * e

theorem last_iff {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} {LW : Lat W}
    (hM : IsSelfDualC V₀ M) (hLW : IsSelfDualC W LW) {x : Pl D} {α m b : (AE D)ˣ} (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (hb : b = xiU D * cU α * m)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hW : ∀ a ∈ idAt D (· = x), colMul d.jY r a ∈ latV W LW (· = x) ↔ cA D (b : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔
      ((m : AE D) * a) • ratV z ∈ latV V₀ M (· = x) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D V₀ M x hM
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [LatMem.mem_latO_iff D V₀ W M LW hM hLW, and_iff_right hmx,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hα, smul_colMul, hW _
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (LocSD.hermAt_mem_idAt (hsd.1 y hy) _))), hb, ← int_neg,
    ← herm_conj V₀ y, int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1, Units.val_mul, Units.val_mul, RingHom.map_mul, RingHom.map_mul, cU_val, Formalism.L2.Theta.cA_cA, xiU, inU_val, cA_xi]
  have e2 := α.mul_inv
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D D.host.xi0 * incA D D.host.xi0⁻¹ * cA D m * hermAt V₀ y (a • ratV z)) * e2 +
    (cA D m * hermAt V₀ y (a • ratV z)) * e3

theorem int_of_smul {S : HSp D} (hS : 0 < S.rank) {L : Lat S} (hL : IsSelfDualC S L) {x : Pl D} {u : AE D}
    (h : ∀ s ∈ latV S L (· = x), u • s ∈ latV S L (· = x)) : ∀ t ∈ intAt D (· = x), u * t ∈ intAt D (· = x) := fun t ht => by
  obtain ⟨𝔞, h0, -, h1⟩ := GlobalTheory.Core.Mi.LatLine.line_trace D S L (fun _ => 1) hL
    (fun e => one_ne_zero (congrFun e ⟨0, hS⟩))
  obtain ⟨g, hg, hgen⟩ := GlobalTheory.IdVGen.idV_gen D x 𝔞 h0
  have e1 : incA D g⁻¹ * incA D g = 1 := (inU g hg).inv_mul
  have ha : incA D g * t ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ht.1
  have h2 := h _ ((h1 x _ ha).2 ((hgen _).2 ⟨by rwa [← mul_assoc, e1, one_mul], ha⟩))
  rw [smul_smul, h1 x _ (Ideal.mul_mem_left _ _ ha), hgen] at h2
  convert h2.1 using 1
  linear_combination (-u * t) * e1

theorem isU_of_norm {x : Pl D} {u : AE D} (h : ∀ t ∈ intAt D (· = x), u * t ∈ intAt D (· = x)) (hn : IsU x (u * cA D u)) :
    IsU x u := fun a ha => ⟨h a, fun H => by
  have h1 := int_conj.2 (h _ (int_conj.2 H))
  rw [RingHom.map_mul, Formalism.L2.Theta.cA_cA, ← mul_assoc, mul_comm (cA D u)] at h1
  exact (hn a ha).2 h1⟩

theorem kap_test {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} {lam : D.host.E}
    (hτ : τ *ᵥ ζ₀ = lam • ζ) {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ a ∈ intAt D (· = x))
    (hk : ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x))
    {a : AE D} (ha : a • ratV ζ ∈ latV L LL (· = x)) {s₀ s : Fin S.rank → AE D} (hs₀ : s₀ ∈ latV S LS (· = x))
    (hs : s ∈ latV S LS (· = x)) :
    cA D α * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) * incA D (star lam) * incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) * a *
      hermAt S s₀ s ∈ intAt D (· = x) := by
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  obtain ⟨w, hw0, hw⟩ : ∃ w : Matrix (Fin L''.rank) (Fin S.rank) (AE D), MxAt (· = x) w ∧
      ∀ y, w *ᵥ y = ((α : AE D) * hermAt S y s₀) • ratV ζ₀ := by
    refine ⟨vecMulVec ((α : AE D) • ratV ζ₀) ((fun i => cA D (s₀ i)) ᵥ* gA S), fun i j => ?_, fun y => ?_⟩
    · rw [vecMulVec_apply]
      refine Ideal.mul_mem_left _ _ ?_
      simp only [vecMul, dotProduct]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (id_conj (hsd.1 _ hs₀ l))
    · rw [herm_eq, dotProduct_mulVec]
      generalize (fun i => cA D (s₀ i)) ᵥ* gA S = t
      funext i
      simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
  have hwO : (show WO S L'' from w) ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x) := by
    rw [LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ]
    refine ⟨hw0, fun y hy => ?_⟩
    have hy' := (hsd.2.2 y (hsd.1 y hy)).1 hy _ hs₀
    change w *ᵥ y ∈ _
    rw [hα, hw, smul_smul, Units.inv_mul_cancel_left]
    exact (hμ _ hy'.1).2 hy'
  have h1 := ((LatMem.mem_latO_iff D L S LL LS hLL hLS _ _).1 (hk _ hwO)).2 _ ha
  rw [hα] at h1
  have h2 := (hsd.2.2 _ (hsd.1 _ h1)).1 h1 s hs
  have e1 := herm_smul S ((α⁻¹ : (AE D)ˣ) : AE D) 1 ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ
    a • ratV ζ) s
  rw [one_smul] at e1
  rw [e1, herm_kap] at h2
  change _ * (_ * hermAt L _ (_ *ᵥ (w *ᵥ s))) ∈ _ at h2
  rw [hw, mulVec_smul, rat_mulVec, hτ, ratV_smul, smul_smul, herm_smul, herm_rat] at h2
  convert h2 using 1
  simp only [RingHom.map_mul, RingHom.map_neg, RingHom.map_one, herm_conj, FrameLat.cA_incA lam]
  ring

theorem top_norm {lam t t₀ : D.host.E} (hlam : lam ≠ 0) (hn : lam * star lam * t = -(D.host.xi0 * star D.host.xi0) * t₀)
    (α : (AE D)ˣ) {m : (AE D)ˣ} (hm' : α * (xiU D * cU α)⁻¹ * inU lam hlam = m) :
    cA D (m : AE D) = cA D α * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) * incA D (star lam) ∧
      (m : AE D) * cA D m * incA D t = -incA D t₀ := by
  have hn' := congrArg (incA D) hn
  simp only [RingHom.map_mul, RingHom.map_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg] at hn'
  have f2 : (m : AE D) = α * (incA D D.host.xi0⁻¹ * cA D (α⁻¹ : (AE D)ˣ)) * incA D lam := by
    rw [← hm', mul_inv]
    simp only [Units.val_mul, inU_val, cU_inv, xiU, inU_inv]
  have f3 : cA D (m : AE D) = cA D α * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) * incA D (star lam) := by
    rw [f2]
    simp only [RingHom.map_mul, Formalism.L2.Theta.cA_cA, cA_xi_inv, FrameLat.cA_incA lam]
  have g1 := α.mul_inv
  have g2 : cA D (α : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU α).mul_inv
  have g3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine ⟨f3, ?_⟩
  rw [f3, f2]
  linear_combination (-(α * (α⁻¹ : (AE D)ˣ) * cA D α * cA D (α⁻¹ : (AE D)ˣ) * incA D D.host.xi0⁻¹ * incA D D.host.xi0⁻¹)) * hn' +
    (-incA D t₀ * cA D α * cA D (α⁻¹ : (AE D)ˣ) * incA D D.host.xi0 * incA D D.host.xi0 * incA D D.host.xi0⁻¹ *
      incA D D.host.xi0⁻¹) * g1 +
    (-incA D t₀ * incA D D.host.xi0 * incA D D.host.xi0 * incA D D.host.xi0⁻¹ * incA D D.host.xi0⁻¹) * g2 +
    (-incA D t₀ * (incA D D.host.xi0 * incA D D.host.xi0⁻¹ + 1)) * g3

theorem top_line {L L'' S : HSp D} (hS : 0 < S.rank) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} (hζ : IsLineVec L ζ) (hζ₀ : IsLineVec L'' ζ₀) {lam : D.host.E} (hlam : lam ≠ 0)
    (hn : lam * star lam * (star ζ ⬝ᵥ L.gram *ᵥ ζ) = -(D.host.xi0 * star D.host.xi0) * (star ζ₀ ⬝ᵥ L''.gram *ᵥ ζ₀))
    (hτ : τ *ᵥ ζ₀ = lam • ζ) {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ a ∈ intAt D (· = x))
    (hk : ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x)) :
    ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔
      (((α * (xiU D * cU α)⁻¹ * inU lam hlam)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  obtain ⟨e, he0, hg⟩ := GlobalTheory.GoodPos.line_gen hζ (by first | exact hLL | exact hLL.1) x
  have hne := line_norm (μ := inU e he0) hζ hLL hg
  have hn0 := (line_norm (μ := 1) hζ₀ hLZ (x := x) fun a ha => by rw [inv_one, Units.val_one, one_mul]; exact hμ a ha).neg
  rw [Units.val_one, RingHom.map_one, one_mul, one_mul] at hn0
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  have hi := idem_mem_intAt (D := D) (· = x)
  generalize hm' : α * (xiU D * cU α)⁻¹ * inU lam hlam = m
  obtain ⟨f3, hmn⟩ := top_norm hlam hn α hm'
  have f1 := m.mul_inv
  have g4 : cA D (m : AE D) * cA D ((m⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU m).mul_inv
  have g5 : incA D e * incA D e⁻¹ = 1 := (inU e he0).mul_inv
  rw [← hmn] at hn0
  rw [inU_val] at hne
  have hU : IsU x (incA D e * (m⁻¹ : (AE D)ˣ)) := by
    refine isU_of_norm (int_of_smul hS hLS fun s₀ hs₀ => ?_) fun a ha => ?_
    · refine (hsd.2.2 ((incA D e * (m⁻¹ : (AE D)ˣ)) • s₀) fun i => Ideal.mul_mem_left _ _ (hsd.1 _ hs₀ i)).2 fun s hs => ?_
      have h2 := kap_test τ hτ hLL hLZ hLS hα hμ hk
        ((hg _ (Ideal.mul_mem_left _ (incA D e) hi.1)).2 (by rwa [← mul_assoc, mul_comm _ (incA D e), g5, one_mul])) hs₀ hs
      have e2 := herm_smul S (incA D e * (m⁻¹ : (AE D)ˣ)) 1 s₀ s
      rw [one_smul, RingHom.map_one, mul_one] at e2
      have hid := LocSD.hermAt_mem_idAt (hsd.1 _ hs₀) s
      rw [e2, hn0 _ (Ideal.mul_mem_left _ _ hid)]
      rw [← f3] at h2
      have e3 := (mem_idAt_iff _ _).1 hid
      convert h2 using 1
      generalize incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = t
      linear_combination (cA D m * t * incA D e * hermAt S s₀ s) * f1 - (cA D m * t * incA D e) * e3
    · rw [hne a ha, hn0 ((incA D e * (m⁻¹ : (AE D)ˣ) * cA D (incA D e * (m⁻¹ : (AE D)ˣ))) * a) (Ideal.mul_mem_left _ _ ha),
        RingHom.map_mul (cA D)]
      refine iff_of_eq (congrArg (· ∈ _) ?_)
      generalize incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = t
      linear_combination (-incA D e * cA D (incA D e) * t * a * (cA D m * cA D (m⁻¹ : (AE D)ˣ))) * f1 -
        (incA D e * cA D (incA D e) * t * a) * g4
  intro a ha
  rw [hg a ha, hU _ (Ideal.mul_mem_left _ _ ha)]
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (((m⁻¹ : (AE D)ˣ) : AE D) * a) * g5

variable {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} {o : TDat c k ι}

theorem step_down {x : Pl D} (hg : GoodAt v o x) {α m : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m)
    (hz : ∀ a ∈ idAt D (· = x), a • ratV (vecB (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ) ∈
      latV _ (o.M (j + 1 + 1) σ (idx_step h)) (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    (∀ a ∈ idAt D (· = x), a • ratV (vecB (c.bes j (σ + 1) h).o (c.bes j (σ + 1) h).ζ) ∈
      latV _ (o.M j (σ + 1) h) (· = x) ↔ (((α * (xiU D * cU α)⁻¹ * m)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧
    ∀ a ∈ idAt D (· = x), colMul (c.bes j (σ + 1) h).d.jX (Fin.last σ) a ∈ latV _ (v.N j) (· = x) ↔
      (((α * α * m)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  have bf := hg.bf j (σ + 1) h
  have fb := hg.fb j σ h
  have hJ : ∀ a ∈ idAt D (· = x), colMul (c.jac j (σ + 1) h).d.jX (Fin.last σ) a ∈ latV _ (v.N (j + 1)) (· = x) ↔
      (((α * m)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := fun a ha => by
    refine (fb.cols (Fin.last σ) a ha).trans ?_
    have hmono := fb.monoW
    revert hz hmono
    change ∀ (hz : ∀ a ∈ idAt D (· = x), a • ratV (vecB (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ) ∈
      latV _ (o.M (j + 1 + 1) σ (idx_step h)) (· = x) ↔ _), MonoAt (c.bes (j + 1 + 1) σ (idx_step h)).d _ _ x →
      (colMul (xLast (c.bes (j + 1 + 1) σ (idx_step h)).d
        (vecB (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ)) _ _ ∈ _ ↔ _)
    generalize vecB (c.bes (j + 1 + 1) σ (idx_step h)).o (c.bes (j + 1 + 1) σ (idx_step h)).ζ = z
    generalize (c.bes (j + 1 + 1) σ (idx_step h)).d = d'
    intro hz hmono
    have e : ∀ t : AE D, colMul (xLast d' z) (Fin.last σ) t = d'.j0 *ᵥ (t • ratV z) := fun t => by
      funext k
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have e0 : ∀ (M : Mx D (c.V (j + 1 + 1)).rank σ) i, colMul M i 0 = 0 := fun M i => funext fun k => zero_mul _
    rw [hα, smul_colMul, e, hmono, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, d'.pX_j0, d'.pY_j0, d'.p0_j0, zero_mulVec,
      one_mulVec, hz _ (Ideal.mul_mem_left _ _ ha), mul_inv, Units.val_mul, mul_assoc, mul_left_comm]
    simp only [Pi.zero_apply, e0, zero_mem, implies_true, true_and]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have hY := dual_line _ bf.sdW bf.monoW (Fin.last σ) hJ
    have h1 := last_iff (c.jac j (σ + 1) h).d (vecB (c.bes j (σ + 1) h).o (c.bes j (σ + 1) h).ζ) bf.sdV₀ bf.sdW
      (m := α * (xiU D * cU α)⁻¹ * m) (Fin.last σ) rfl
      (by rw [← mul_assoc, mul_comm α (xiU D * cU α)⁻¹, mul_inv_cancel_left]) (hα _ _) hY _
      (Ideal.mul_mem_left _ (((α * (xiU D * cU α)⁻¹ * m)⁻¹ : (AE D)ˣ) : AE D) ha)
    rw [Units.mul_inv_cancel_left] at h1
    exact h1.symm.trans (bf.last (Nat.succ_pos σ) _ (Ideal.mul_mem_left _ _ ha))
  · refine (bf.cols (Fin.last σ) a ha).trans ?_
    rw [hα, smul_colMul]
    refine (hJ _ (Ideal.mul_mem_left _ _ ha)).trans ?_
    rw [← mul_assoc, ← Units.val_mul, ← mul_inv, mul_comm (α * m), mul_assoc]

theorem last_ideal (hc : c.Is) (sh : ShapeOff v o) (hp : GlobalTheory.MiTop.TopPrim v o) (hr : ∀ j, j < D.R.m → 0 < (c.X (j + 1)).rank)
    {lam : D.host.E} (hlam : lam ≠ 0) (hτ : ∀ j hj, v.τ j hj *ᵥ o.ζ₀ = lam • (c.bes j 0 hj).ζ) {x : Pl D} (hx : x ∉ v.tP)
    {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (r : Fin ρ) (hρ : r.1 + 1 = ρ) :
    ∀ a ∈ idAt D (· = x), colMul (c.bes j ρ h).d.jX r a ∈ latV _ (v.N j) (· = x) ↔
      (((α * α * ((α * (xiU D * cU α)⁻¹) ^ ρ * inU lam hlam))⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  have key : ∀ σ j (h : j + 2 * σ + 2 = D.R.m), ∀ a ∈ idAt D (· = x), a • ratV (vecB (c.bes j σ h).o (c.bes j σ h).ζ) ∈
      latV _ (o.M j σ h) (· = x) ↔
        ((((α * (xiU D * cU α)⁻¹) ^ (σ + 1) * inU lam hlam)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
    intro σ
    induction σ with
    | zero =>
      intro j h a ha
      obtain ⟨LL, LZ, h1, h2, h3, h4, h5⟩ := (sh.split x hx).top j h
      have hn : lam * star lam * (star (c.bes j 0 h).ζ ⬝ᵥ (c.bes j 0 h).L.gram *ᵥ (c.bes j 0 h).ζ) =
          -(D.host.xi0 * star D.host.xi0) * (star o.ζ₀ ⬝ᵥ c.Lz.gram *ᵥ o.ζ₀) := by
        have := congrArg (fun M => star o.ζ₀ ⬝ᵥ M *ᵥ o.ζ₀) (sh.pre.tau j h)
        rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hτ, smul_mulVec, dotProduct_smul, smul_eq_mul,
          mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at this
        rw [← this, mul_assoc]
      rw [← orth_line _ h3, zero_add, pow_one]
      exact top_line (hr j (by omega)) (v.τ j h) (c.bes j 0 h).line sh.pre.line hlam hn (hτ j h) h1 h2
        (hc.x (j + 1) (by omega)).sd hα (fun a ha => hp.line h hx h4 ha) h5 a ha
    | succ σ ih =>
      intro j h a ha
      rw [pow_succ', mul_assoc]
      exact (step_down (sh.good x) hα j σ h (ih _ _)).1 a ha
  obtain _ | σ := ρ
  · exact r.elim0
  · obtain rfl : r = Fin.last σ := Fin.ext (by simpa using hρ)
    exact (step_down (sh.good x) hα j σ h (key _ _ _)).2

theorem prim_down {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {x : Pl D}
    (hp : PrimAt ψ d L x) {cc b : (AE D)ˣ}
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x)) (i j : Fin ρ) (hij : j.1 = i.1 + 1)
    (hL : ∀ a ∈ idAt D (· = x), colMul d.jX j a ∈ latV S L (· = x) ↔ ((b⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔
      (((cc * b)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := fun a ha => by
  have he := idem_mem_intAt (D := D) (· = x)
  have hs : ((b⁻¹ : (AE D)ˣ) : AE D) * a ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ ha
  rw [mul_inv, Units.val_mul, mul_assoc, ← hψ _ hs, ← hp i j hij _ hs]
  constructor
  · intro H t ht
    have := smul_latV x ((hL t (colMul_id d j (latV_idAt ht))).1 ht) H
    rw [smul_colMul] at this
    convert this using 2
    ring
  · intro H
    have := H _ ((hL _ (Ideal.mul_mem_left _ (b : AE D) he.1)).2 (by rwa [Units.inv_mul_cancel_left]))
    convert this using 2
    linear_combination (-a * idem D (· = x)) * b.inv_mul - (mem_idAt_iff _ a).1 ha

theorem all_ideal (hc : c.Is) (sh : ShapeOff v o) (hp : GlobalTheory.MiTop.TopPrim v o) (hr : ∀ j, j < D.R.m → 0 < (c.X (j + 1)).rank)
    {lam : D.host.E} (hlam : lam ≠ 0) (hτ : ∀ j hj, v.τ j hj *ᵥ o.ζ₀ = lam • (c.bes j 0 hj).ζ) {x : Pl D} (hx : x ∉ v.tP)
    {α cc : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hψ : ∀ s ∈ idAt D (· = x), (∀ o ∈ intAt D (· = x), psiE c.ψ (s * o) = 1) ↔
      ((cc⁻¹ : (AE D)ˣ) : AE D) * s ∈ intAt D (· = x))
    (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (n : ℕ) : ∀ r : Fin ρ, r.1 + n + 1 = ρ →
    ∀ a ∈ idAt D (· = x), colMul (c.bes j ρ h).d.jX r a ∈ latV _ (v.N j) (· = x) ↔
      (((cc ^ n * (α * α * ((α * (xiU D * cU α)⁻¹) ^ ρ * inU lam hlam)))⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  induction n with
  | zero =>
    intro r hρ
    rw [pow_zero, one_mul]
    exact last_ideal hc sh hp hr hlam hτ hx hα j ρ h r hρ
  | succ n ih =>
    intro r hρ
    rw [pow_succ', mul_assoc cc]
    exact prim_down _ ((sh.good x).bf j ρ h).prim hψ r ⟨r.1 + 1, by omega⟩ rfl (ih _ (by simp only; omega))

end GlobalTheory.LineIdeal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfPsiE
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

namespace GlobalTheory.FirstVec

theorem first_col {K : Type} [CommRing K] {σ : ℕ} (T S : Matrix (Fin (σ + 1)) (Fin (σ + 1)) K) (h : S * T = 1)
    (hl : T (Fin.last σ) (Fin.last σ) = 1) (hu : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → ∀ a b, b ≤ a → T a j * S j' b = 0)
    (hs : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → (∑ a : Fin (σ + 1), ∑ b : Fin (σ + 1),
      if b.1 = a.1 + 1 then T a j * S j' b else 0) = 1) : ∀ a, T a 0 = if a = 0 then 1 else 0 := by
  have key : ∀ j j' : Fin (σ + 1), j'.1 = j.1 + 1 → (∀ b, j' < b → T b j' = 0) → ∀ a, j ≤ a →
      T a j = if a = j then T j j * S j' j' * T j' j' else 0 := fun j j' e H a ha => by
    have e1 : T a j = ∑ b, T a j * S j' b * T b j' := by
      have := congrFun (congrFun h j') j'
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      simp only [mul_assoc, ← Finset.mul_sum, this, mul_one]
    rw [e1, Finset.sum_eq_single j']
    · split_ifs with h1
      · rw [h1]
      · rw [hu j j' e a j' (by rw [Fin.le_def] at *; have := mt Fin.ext h1; omega), zero_mul]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h1 | h1
      · rw [hu j j' e a b (by rw [Fin.le_def, Fin.lt_def] at *; omega), zero_mul]
      · rw [H b h1, mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  have tri : ∀ j : Fin (σ + 1), ∀ b, j < b → T b j = 0 := fun j => by
    induction j using Fin.reverseInduction with
    | last => exact fun b hb => absurd (Fin.le_last b) (not_le.2 hb)
    | cast j ih => exact fun b hb => by rw [key j.castSucc j.succ rfl ih b hb.le, if_neg hb.ne']
  have triS : S.BlockTriangular id := by
    letI := invertibleOfLeftInverse T S h
    rw [← Matrix.inv_eq_left_inv h]
    exact Matrix.blockTriangular_inv_of_blockTriangular fun a b hab => tri b a hab
  have diag : ∀ j : Fin (σ + 1), T j j = 1 := fun j => by
    induction j using Fin.reverseInduction with
    | last => exact hl
    | cast j ih =>
      have h1 := hs j.castSucc j.succ rfl
      rw [Finset.sum_eq_single j.castSucc, Finset.sum_eq_single j.succ, if_pos (show j.succ.1 = j.castSucc.1 + 1 from rfl)] at h1
      · rw [key j.castSucc j.succ rfl (tri _) _ le_rfl, if_pos rfl, h1, ih, one_mul]
      · exact fun b _ hb => if_neg fun e => hb (Fin.ext e)
      · exact fun h => absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun b _ => ?_
        split_ifs with e
        · rcases lt_or_gt_of_ne ha with h2 | h2
          · rw [show S j.succ b = 0 from triS (show b < j.succ by
              rw [Fin.lt_def] at h2 ⊢; simp only [Fin.val_castSucc, Fin.val_succ] at h2 e ⊢; omega), mul_zero]
          · rw [tri _ a h2, zero_mul]
        · rfl
      · exact fun h => absurd (Finset.mem_univ _) h
  intro a
  split_ifs with e
  · rw [e, diag]
  · exact tri 0 a (Fin.pos_iff_ne_zero.2 e)

variable {D : D7} {S S₀ S₀' : HSp D}

theorem eq_of_psiE {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∃ s : AE D, psiE ψ s ≠ 1) {s s' : D.host.E}
    (h : ∀ t : AE D, psiE ψ (t * incA D s) = psiE ψ (t * incA D s')) : s = s' := by
  by_contra hne
  obtain ⟨y, hy⟩ := hψ
  have h0 : s - s' ≠ 0 := sub_ne_zero.2 hne
  have h1 := h (y * incA D (s - s')⁻¹)
  have e : y * incA D (s - s')⁻¹ * incA D s = y + y * incA D (s - s')⁻¹ * incA D s' := by
    have : incA D (s - s')⁻¹ * (incA D s - incA D s') = 1 := by rw [← map_sub, ← map_mul, inv_mul_cancel₀ h0, map_one]
    linear_combination y * this
  rw [e, psiE_add] at h1
  have h2 : psiE ψ (y * incA D (s - s')⁻¹ * incA D s') * psiE ψ (-(y * incA D (s - s')⁻¹ * incA D s')) = 1 := by
    rw [← psiE_add, add_neg_cancel, psiE_zero]
  exact hy (mul_right_cancel₀ (left_ne_zero_of_mul_eq_one h2) (h1.trans (one_mul _).symm))

section

variable {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec S S₀' ρ) {z : Fin S₀.rank → D.host.E} {z' : Fin S₀'.rank → D.host.E}

theorem exists_b (hz' : z' ≠ 0) (i : Fin ρ) (t : AE D) : ∃ b : Mx D ρ S₀'.rank, b *ᵥ ratV z' = Pi.single i t := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hz'
  refine ⟨Matrix.single i k (t * incA D (z' k)⁻¹), ?_⟩
  rw [Matrix.single_mulVec]
  change Function.update (0 : Fin ρ → AE D) i (t * incA D (z' k)⁻¹ * incA D (z' k)) = _
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hk, map_one, mul_one]
  rfl

theorem coefX_eq (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (n : GA D S) :
    coefX d z n = d.pX *ᵥ (mt S n *ᵥ (d'.j0 *ᵥ ratV z')) := by
  have e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z' := (ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))
  rw [coefX, ← mulVec_mulVec, ← mulVec_mulVec, e]

theorem coefX_nB' (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (b : Mx D ρ S₀'.rank) :
    coefX d z (d'.nB b) = (d.pX * d'.jX) *ᵥ (b *ᵥ ratV z') := by
  have e0 : d.pX *ᵥ (d'.j0 *ᵥ ratV z') = 0 := by
    have := coefX_eq d d' hz 1
    rw [GlobalTheory.MixModel.mt_one, one_mulVec, coefX, GlobalTheory.MixModel.mt_one, Matrix.one_mul, d.pX_j0, zero_mulVec] at this
    exact this.symm
  rw [coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.nB_j0, add_mulVec, mulVec_add, e0, zero_add]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

theorem e_eq (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (hz' : z' ≠ 0) (hN : ∀ n ∈ flagN d', n ∈ flagN d) : d'.e = d.e * (d.qX * d'.e) := by
  apply rat_injective
  rw [rat_mul, rat_mul]
  change d'.jX = d.jX * (d.pX * d'.jX)
  ext k i : 2
  obtain ⟨b, hb⟩ := exists_b hz' i 1
  have e : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z' := (ratV_mulVec _ _).symm.trans ((congrArg ratV hz).trans (ratV_mulVec _ _))
  obtain ⟨u, -, b₁, c, hn⟩ := Decomp.flag_decomp d (hN _ (d'.nB_mem_NFlag b))
  have h1 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d.jX *ᵥ ((u.1 * b₁) *ᵥ ratV z) := by
    rw [hn, mulVec_mulVec, Decomp.flag_unipotent_product_anisotropic_action, add_mulVec, mulVec_mulVec]
  have h2 : mt S (d'.nB b) *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d'.jX *ᵥ Pi.single i 1 := by
    rw [e, mulVec_mulVec, d'.nB_j0, add_mulVec, ← mulVec_mulVec, hb]
  have h3 := add_left_cancel (h2.symm.trans h1)
  have h4 : (d.jX * (d.pX * d'.jX)) *ᵥ Pi.single i 1 = d'.jX *ᵥ Pi.single i 1 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, h3, mulVec_mulVec _ d.pX, d.pX_jX, one_mulVec]
  have := congrFun h4 k
  simp only [mulVec_single_one] at this
  exact this.symm

end

theorem first_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec S S₀' ρ)
    {z : Fin S₀.rank → D.host.E} {z' : Fin S₀'.rank → D.host.E} (hz : d.i₀ *ᵥ z = d'.i₀ *ᵥ z') (hz0 : z ≠ 0) (hz' : z' ≠ 0)
    (hN : ∀ n, n ∈ flagN d ↔ n ∈ flagN d') (hc : ∀ n ∈ flagN d, psiBes ψ d 1 z n = psiBes ψ d' 1 z' n)
    (r : Fin ρ) (hr : r.1 = 0) (k : Fin S.rank) : d'.e k r = d.e k r := by
  obtain _ | σ := ρ
  · exact r.elim0
  obtain rfl : r = 0 := Fin.ext hr
  have hne := GlobalTheory.Unf.CutChar.exists_psiE_ne_one D ψ hψ
  have e1 := e_eq d d' hz hz' fun n => (hN n).2
  have e2 := e_eq d' d hz.symm hz0 fun n => (hN n).1
  have q1 : d'.qX * d'.e = 1 := d'.e'e
  have hT : (rat (d.qX * d'.e) : Mx D _ _) = d.pX * d'.jX := rat_mul _ _
  generalize d.qX * d'.e = T at e1 hT
  generalize hS : d'.qX * d.e = S' at e2
  have hST : S' * T = 1 := by rw [← hS, Matrix.mul_assoc, ← e1, q1]
  have hX : d.jX = d'.jX * rat S' := (congrArg rat e2).trans (rat_mul _ _)
  have hTS : (rat T : Mx D _ _) * rat S' = 1 := by rw [← rat_mul, mul_eq_one_comm.1 hST, rat_one]
  have hell : ∀ y : Fin (σ + 1) → AE D, ell D (σ + 1) ⬝ᵥ y = y (Fin.last σ) := fun y => by
    rw [dotProduct, Finset.sum_eq_single (Fin.last σ)]
    · simp [ell]
    · intro b _ hb
      rw [ell, if_neg fun e => hb (Fin.ext (by simpa using e)), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have hA : ∀ (j j' : Fin (σ + 1)) (t : AE D), j'.1 = j.1 + 1 → ∃ u ∈ UX D (σ + 1), u.1 = 1 + Matrix.single j j' t ∧
      blockX d (d'.levi u) = 1 + Matrix.of fun a b => t * incA D (T a j * S' j' b) := fun j j' t e => by
    obtain ⟨u, hu, hu1⟩ := Decomp.exists_unit (D := D) (T := Matrix.single j j' t) fun a b hab =>
      Matrix.single_apply_of_ne _ _ _ _ _ (by rintro ⟨rfl, rfl⟩; rw [Fin.le_def] at hab; omega)
    refine ⟨u, hu, hu1, ?_⟩
    rw [blockX, hX, ← Matrix.mul_assoc (mt S _), d'.levi_jX, hu1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hT,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTS]
    congr 1
    ext a b : 2
    rw [Matrix.mul_apply, Finset.sum_eq_single j', Matrix.mul_single_apply_same, Matrix.of_apply, map_mul]
    · change incA D (T a j) * t * incA D (S' j' b) = _
      ring
    · intro c _ hc
      rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have H := first_col T S' hST ?_ ?_ ?_
  · rw [e1, Matrix.mul_apply]
    simp only [H, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · refine eq_of_psiE hne fun t => ?_
    obtain ⟨b, hb⟩ := exists_b hz' (Fin.last σ) t
    have h1 := hc _ ((hN _).2 (d'.nB_mem_NFlag b))
    have h2 : blockX d (d'.nB b) = 1 := by
      rw [blockX, hX, ← Matrix.mul_assoc (mt S _), d'.nB_jX, ← hX, d.pX_jX]
    rw [psiBes_nB, psiBes, simpleSum, h2, upSum_one, zero_add, coefX_nB' d d' hz, hb, hell, hell, ← hT, mulVec_single] at h1
    simp only [map_one, one_mul, Pi.single_eq_same, mul_one] at h1 ⊢
    rw [mul_comm t]
    exact h1
  · intro j j' e a b hab
    obtain ⟨u, hu, -, h2⟩ := hA j j' 1 e
    obtain ⟨u₁, hu₁, b₁, c, hn⟩ := Decomp.flag_decomp d ((hN _).2 (d'.levi_mem_NFlag hu))
    rw [blockX, hn, Decomp.mt_flag_jX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h2
    have h3 := congrFun (congrFun h2 a) b
    rw [Matrix.add_apply, Matrix.of_apply, one_mul] at h3
    have h4 : u₁.1 a b = (1 : Mx D (σ + 1) (σ + 1)) a b := by
      rcases eq_or_lt_of_le hab with rfl | h
      · rw [(hu₁ b b).2, Matrix.one_apply_eq]
      · rw [(hu₁ a b).1 h, Matrix.one_apply_ne h.ne']
    rw [h4, left_eq_add] at h3
    exact incA_injective (h3.trans (map_zero _).symm)
  · intro j j' e
    refine eq_of_psiE hne fun t => ?_
    obtain ⟨u, hu, h1, h2⟩ := hA j j' t e
    have h3 := hc _ ((hN _).2 (d'.levi_mem_NFlag hu))
    have h4 : coefX d z (d'.levi u) = 0 := by
      have := coefX_nB' d d' hz 0
      rw [zero_mulVec, mulVec_zero, coefX_eq d d' hz, d'.nB_zero, GlobalTheory.MixModel.mt_one, one_mulVec] at this
      rw [coefX_eq d d' hz, mulVec_mulVec _ (mt S _), d'.wittDecomp_levi_inclAnisotropic, this]
    have hadd : ∀ M : Mx D (σ + 1) (σ + 1), upSum (1 + M) = upSum M := fun M =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        split_ifs with h
        · rw [Matrix.add_apply, Matrix.one_apply_ne (by rintro rfl; omega), zero_add]
        · rfl
    have h5 : upSum (Matrix.single j j' t : Mx D (σ + 1) (σ + 1)) = t := by
      rw [upSum, Finset.sum_eq_single j, Finset.sum_eq_single j', if_pos e, Matrix.single_apply_same]
      · exact fun b _ hb => if_neg fun e' => hb (Fin.ext (e'.trans e.symm))
      · exact fun h => absurd (Finset.mem_univ _) h
      · exact fun a _ ha => Finset.sum_eq_zero fun b _ => by
          rw [Matrix.single_apply_of_row_ne ha.symm, ite_self]
      · exact fun h => absurd (Finset.mem_univ _) h
    rw [psiBes_levi, psiUni, h1, hadd, h5, psiBes, simpleSum, h2, h4, hadd, dotProduct_zero, add_zero, map_one, one_mul] at h3
    rw [map_one, mul_one, ← h3]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [upSum, map_sum, Finset.mul_sum, Matrix.of_apply]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by split_ifs <;> simp

end GlobalTheory.FirstVec

end
end

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LineIdeal

section Loc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc NumberField GlobalTheory.AdelicU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem int_of_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : Af F ⊗[F] E)
    (h : ∀ w, Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) y ∈ intLoc F E w) :
    y ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  have hfg : (stdLattice E 1).FG := Submodule.fg_pi fun _ => by
    rw [← Submodule.one_eq_range]; exact Submodule.fg_unit 1
  have h1 : (fun _ : Fin 1 => y) ∈ latHat F E (stdLattice E 1 : Set _) :=
    (mem_latHat_iff hfg _).2 fun w => mem_latLoc_stdLattice.2 fun _ => h w
  generalize hA : AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} = A
  have hA' : ∀ a ∈ intAf F, ∀ x : 𝓞 E, a ⊗ₜ[F] (x : E) ∈ A := fun a ha x => hA ▸ AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩
  have key : latHat F E (stdLattice E 1 : Set _) ≤ A.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => Af F ⊗[F] E) 0) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, x, hx, rfl⟩
    obtain ⟨r, hr⟩ := hx 0 trivial
    change b ⊗ₜ[F] x 0 ∈ A
    rw [← hr]
    exact hA' b hb r
  exact key h1

theorem loc_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : Af F ⊗[F] E)
    (h : y ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) (w) :
    Algebra.TensorProduct.map (evalV F w) (AlgHom.id F E) y ∈ intLoc F E w := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    exact tmul_mem_intLoc (hb w) x
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem exists_mulVec_iff {R : Type} [CommRing R] {n : ℕ} (M : GL (Fin n) R) (P : (Fin n → R) → Prop) (w : Fin n → R) :
    (∃ x, P x ∧ M.1 *ᵥ x = w) ↔ P ((M⁻¹).1 *ᵥ w) := by
  constructor
  · rintro ⟨x, hx, e⟩
    rwa [← e, mulVec_mulVec, Units.inv_mul, one_mulVec]
  · exact fun H => ⟨_, H, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩

variable {D : D7}

theorem int_iff_loc {v : Pl D} {a : AE D} (ha : a ∈ idAt D (· = v)) :
    a ∈ intAt D (· = v) ↔ compAt D v a ∈ intLoc D.host.F D.host.E v := by
  refine ⟨fun h => loc_of_int _ h.2 v, fun h => ⟨ha, int_of_loc _ fun w => ?_⟩⟩
  by_cases e : w = v
  · subst e; exact h
  · have h0 : compAt D w a = 0 := compAt_of_idAt ha e
    change compAt D w a ∈ _
    rw [h0]
    exact zero_mem _

theorem line_loc (V : HSp D) (Λ : Lat V) (hΛ : Λ.FG) (v : Pl D) (g : GA D V) (y₀ : Fin V.rank → AE D)
    (h : ∀ a ∈ idAt D (· = v), mt V g⁻¹ *ᵥ (a • y₀) ∈ GlobalTheory.FinPl.latV V Λ (· = v) ↔ a ∈ intAt D (· = v))
    (c : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    (∃ x ∈ latLoc D.host.F Λ v, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram v g)).1 *ᵥ x =
      c • vecLoc v (finPart D ∘ y₀)) ↔ c ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨a, ha, hc⟩ := GlobalTheory.StMoves.exists_supp_vecLoc_eq (n := 1) v fun _ => c
  have hc' : compAt D v (a 0) = c := congrFun hc 0
  have hs : ∀ i, (a 0 • y₀) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ (ha 0)
  have e : vecLoc v (finPart D ∘ (a 0 • y₀)) = c • vecLoc v (finPart D ∘ y₀) := by
    funext i
    rw [← hc']
    exact map_mul (compAt D v) (a 0) (y₀ i)
  have key : ∀ (g : GA D V) y, vecLoc v (finPart D ∘ (mt V g *ᵥ y)) =
      (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram v g)).1 *ᵥ vecLoc v (finPart D ∘ y) := fun g y => by
    rw [GlobalTheory.FinPl.KOpen.fin_mulVec]
    exact vecLoc_mulVec D.sp.cm.sig V.gram v g _
  rw [← hc', ← int_iff_loc (ha 0), ← h _ (ha 0), hc',
    GlobalTheory.StMoves.mem_latV_iff_latLoc V Λ hΛ v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ _ hs), key, e, map_inv, map_inv]
  exact exists_mulVec_iff _ (· ∈ latLoc D.host.F Λ v) _

end Loc

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef _root_.Formalism.L2.Rows _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open _root_.Formalism.L2.SG.RowsJoinPinned _root_.Formalism.L2.SG.RowDict _root_.Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
open Matrix GlobalTheory.GoodPos

section Word

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ}

theorem xu_fixes (hE : IdE X) (r : Fin D.R.rS) :
    mt (D.sp.Y 0) ((iotaX X h).symm (1, X.xu u)) *ᵥ ratV (fun k => X.ιE (X.eR r (Fin.cast (rank_eq X h) k))) =
      ratV fun k => X.ιE (X.eR r (Fin.cast (rank_eq X h) k)) := by
  have h1 := (GlobalTheory.Core.SBesLevi.transport_fix D X.B.I X.ιE hE h (rank_eq X h) {X.eR r}
    (Formalism.IndefR.RationalEmbedding.iota D ((iotaX X h).symm (1, X.xu u)))).1
  have e : castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D ((iotaX X h).symm (1, X.xu u))) = (1, X.xu u) :=
    (iotaX X h).apply_symm_apply _
  rw [e] at h1
  refine (GlobalTheory.Core.SBesLevi.bridge_fix D _ _).2 (h1 ⟨?_, ?_⟩ _ rfl)
  · exact one_mem _
  · rintro _ rfl
    exact (X.xu_fix u r).1

theorem first_vec (F₀ : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F₀) (hE : IdE X)
    (hψ : IsStdChar D ψ (-1)) (B : SBes X h u ψ (D.sp.X 0)) {μ : D.host.E} (hμ : μ ≠ 0)
    (hz : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = μ * X.ιE (X.zR u (Fin.cast (rank_eq X h) k))) (r : Fin D.R.rS) (hr : r.1 = 0) :
    ∃ s : D.host.E, (s = 1 ∨ s = -1) ∧
      ∀ k, B.d.e k r = s * (μ * (X.B.g : D.host.E) ^ D.R.rS) * X.ιE (X.eR r (Fin.cast (rank_eq X h) k)) := by
  obtain ⟨lam, hl, H⟩ := exists_sBes_scaled_dual D X h u ψ F₀ tr hE hψ
  obtain ⟨B', -, -, hz', he, -⟩ := H μ B.vA hμ
  have hne : ∀ B : SBes X h u ψ (D.sp.X 0), vecB B.o B.ζ ≠ 0 := fun B e => besVec_ne_zero B (by rw [e, mulVec_zero])
  have h1 := GlobalTheory.FirstVec.first_eq hψ B'.d B.d (funext fun k => (hz' k).trans (hz k).symm) (hne B') (hne B)
    (fun n => (B'.tieN n).trans (B.tieN n).symm)
    (fun n hn => star_injective ((B'.tieψ n hn).trans (B.tieψ n ((B.tieN n).2 ((B'.tieN n).1 hn))).symm)) r hr
  rcases hl with rfl | rfl
  · exact ⟨1, Or.inl rfl, fun k => by rw [h1, he, hr, Nat.sub_zero, one_mul]⟩
  · exact ⟨(-1) ^ D.R.rS, neg_one_pow_eq_or _ _, fun k => by rw [h1, he, hr, Nat.sub_zero, neg_pow]; ring⟩

end Word

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

end GlobalTheory.LineIdeal

end
