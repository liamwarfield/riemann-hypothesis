module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrime
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLatticeDualZIdealMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MixModel MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FlatRInv

variable {D : D7}

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ (mt V g).map (Ideal.Quotient.mk I) = 1 := by
  unfold congGrp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  rfl

theorem unitaryMatrix_wittCoreEmbedding {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (h : GA D S₀) :
    mt S (d.emb0 h) = d.jX ⬝ d.pX + d.j0 ⬝ mt S₀ h ⬝ d.p0 + d.jY ⬝ d.pY := by
  conv_lhs => rw [← Matrix.mul_one (mt S (d.emb0 h)), ← d.sum_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclY]

theorem wittCoreEmbedding_preserves_supportedUnitarySubgroup {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {h : GA D S₀}
    (hh : h ∈ grpAt S₀ P) : d.emb0 h ∈ grpAt S P := by
  rw [grpAt, mem_congGrp_iff] at hh ⊢
  have key : (mt S (d.emb0 h)).map (Ideal.Quotient.mk (idAt D P)) =
      (d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY).map (Ideal.Quotient.mk (idAt D P)) := by
    have hadd : ∀ A B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (A + B).map (Ideal.Quotient.mk (idAt D P)) =
        A.map (Ideal.Quotient.mk (idAt D P)) + B.map (Ideal.Quotient.mk (idAt D P)) :=
      fun A B => Matrix.map_add _ (Ideal.Quotient.mk (idAt D P)).map_add A B
    rw [unitaryMatrix_wittCoreEmbedding]; simp only [hadd, Matrix.map_mul, hh, Matrix.mul_one]
  rw [key, d.sum_eq_one]; exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem comp_mem_grpAt {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {n : GA D S}
    (hn : n ∈ flagN d) {h : GA D S₀} (hr : n * d.emb0 h ∈ grpAt S P) : h ∈ grpAt S₀ P := by
  rw [grpAt, mem_congGrp_iff] at hr ⊢
  rw [← GlobalTheory.BesClosed.witt_anisotropic_block_flag_mul_embedded d hn h]
  simp only [Matrix.map_mul, hr, Matrix.one_mul]
  rw [← Matrix.map_mul, d.p0_j0]; exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem jac_decomp {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Pl D → Prop) {r : GA D S}
    (hr : r ∈ jacGrp d) (hP : r ∈ grpAt S P) :
    ∃ n ∈ flagN d, n ∈ grpAt S P ∧ ∃ h ∈ grpAt S₀ P, r = n * d.emb0 h := by
  obtain ⟨n, hn, h, rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff d).1 hr
  have hh := comp_mem_grpAt d P hn hP
  refine ⟨n, hn, ?_, h, hh, rfl⟩
  have e : n = n * d.emb0 h * (d.emb0 h)⁻¹ := by group
  rw [e]; exact mul_mem hP (inv_mem (wittCoreEmbedding_preserves_supportedUnitarySubgroup d P hh))

theorem heisO_eq_zero_iff (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (F : WO S T → ℂ) :
    heisO ψ S T w₀ F = 0 ↔ F = 0 := by
  constructor
  · intro h; funext w
    have := congrFun h (w - w₀)
    simp only [heisO, Pi.zero_apply, sub_add_cancel] at this
    exact (mul_eq_zero.1 this).resolve_left (addChar_ne_zero ψ _)
  · rintro rfl; funext w; simp [heisO]

theorem om_eq_zero_iff {S T : HSp D} (om : Om S T) (g : GA D S × GA D T) (F : WO S T → ℂ) :
    om g F = 0 ↔ F = 0 := by
  constructor
  · intro h0
    have e : om g⁻¹ (om g F) = F := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← e, h0, map_zero]
  · rintro rfl; exact map_zero _

theorem orth_comp_mem {S₀ A L : HSp D} (o : OrthDec S₀ A L) (P : Pl D → Prop) {h : GA D A}
    (hh : o.emb (h, 1) ∈ grpAt S₀ P) : h ∈ grpAt A P := by
  rw [grpAt, mem_congGrp_iff] at hh ⊢
  have e : mt A h = o.pA * mt S₀ (o.emb (h, 1)) * o.jA := by
    rw [o.pA_emb, Matrix.mul_assoc, o.pA_jA, Matrix.mul_one]
  rw [e, Matrix.map_mul, Matrix.map_mul, hh, Matrix.mul_one, ← Matrix.map_mul, o.pA_jA]
  exact Matrix.map_one _ (Ideal.Quotient.mk (idAt D P)).map_zero (Ideal.Quotient.mk (idAt D P)).map_one

theorem bes_decomp {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (P : Pl D → Prop)
    {r : GA D S} (hr : r ∈ besGrp d o) (hP : r ∈ grpAt S P) :
    ∃ n ∈ flagN d, n ∈ grpAt S P ∧ ∃ h ∈ grpAt A P, r = n * embA d o h := by
  obtain ⟨n, hn, h, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp d o r).1 hr
  have hP' : n * d.emb0 (o.emb (h, 1)) ∈ grpAt S P := by rwa [embA_apply] at hP
  have h0 := comp_mem_grpAt d P hn hP'
  refine ⟨n, hn, ?_, h, orth_comp_mem o P h0, rfl⟩
  have e : n = n * embA d o h * (embA d o h)⁻¹ := by group
  rw [e]; exact mul_mem hP (inv_mem (wittCoreEmbedding_preserves_supportedUnitarySubgroup d P h0))

theorem opA_eq_zero_iff (ψ : AddChar (AF D.host.F) ℂ) {W W₀ V₀ A L : HSp D} {ρ : ℕ} (dW : HypDec W W₀ ρ)
    (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (om : Om V₀ W₀) (n : GA D W) (h : GA D W₀)
    (Ξ : WO V₀ W₀ → ℂ) : opA ψ dW o ζ om n h Ξ = 0 ↔ Ξ = 0 := by
  unfold opA jacT
  rw [smul_eq_zero_iff_right (addChar_ne_zero ψ _), heisO_eq_zero_iff, om_eq_zero_iff]

theorem handFB_smul_om_at {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ}
    (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ)
    (c : ℂ) (h₁ g : GA D B.A) :
    handFB s vL Y (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) g = c * handFB s vL Y Ξ (g * h₁) := by
  unfold handFB
  rw [← integral_const_mul]
  congr 1
  funext h₀
  have e : s.om₀ (h₀, B.o.emb (g, 1)) (c • s.om₀ (1, B.o.emb (h₁, 1)) Ξ) = c • s.om₀ (h₀, B.o.emb (g * h₁, 1)) Ξ := by
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk]
    simp only [mul_one]
  unfold pairKer
  rw [e]
  simp only [contractT, thPair, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem vanish_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (f : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W f → ∀ r ∈ jacGrp J.d, r ∈ grpAt J.W P → (flatBF s (s.om (1, r) f) = 0 ↔ flatBF s f = 0)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (f : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V f → ∀ r ∈ besGrp B.d B.o, r ∈ grpAt B.V P → (handFB s vL Y (flatFB s (s.om (1, r) f)) = 0 ↔ handFB s vL Y (flatFB s f) = 0) := by
  intro D ψ P
  have hL := GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ P
  refine ⟨fun ρ B J s f hf r hr hrP => ?_, fun σ J B s vL Y f hf r hr hrP => ?_⟩
  · obtain ⟨n, hn, hnP, h, hh, rfl⟩ := jac_decomp J.d P hr hrP
    rw [(hL.1 ρ B J s).equiv f hf n hn hnP h hh]
    have hc : star (psiFlag ψ J.d n) ≠ 0 := star_ne_zero.2 (by unfold psiFlag psiE; exact addChar_ne_zero ψ _)
    rw [smul_eq_zero_iff_right hc, opA_eq_zero_iff]
  · obtain ⟨n, hn, hnP, h, hh, rfl⟩ := bes_decomp B.d B.o P hr hrP
    rw [(hL.2 σ J B s).equiv f hf n hn hnP h hh]
    have hc : star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) ≠ 0 :=
      star_ne_zero.2 (by unfold psiBes psiE; exact addChar_ne_zero ψ _)
    constructor
    · intro h0; funext g
      have := congrFun h0 (g * h⁻¹)
      rw [handFB_smul_om_at, inv_mul_cancel_right, Pi.zero_apply] at this
      exact (mul_eq_zero.1 this).resolve_left hc
    · intro h0; funext g
      rw [handFB_smul_om_at, h0, Pi.zero_apply, Pi.zero_apply, mul_zero]

end GlobalTheory.FlatRInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_handedFunction_vanishing_period_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (f : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W f → ∀ r ∈ jacGrp J.d, r ∈ grpAt J.W P → (flatBF s (s.om (1, r) f) = 0 ↔ flatBF s f = 0)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (f : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V f → ∀ r ∈ besGrp B.d B.o, r ∈ grpAt B.V P → (handFB s vL Y (flatFB s (s.om (1, r) f)) = 0 ↔ handFB s vL Y (flatFB s f) = 0) := by
  first | exact @GlobalTheory.FlatRInv.vanish_invariant | exact GlobalTheory.FlatRInv.vanish_invariant | (intros; apply GlobalTheory.FlatRInv.vanish_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeImage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FamTrace.PairsFwd

theorem intMat_keeps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (M M' : Matrix n n k) (hMM : M * M' = 1) (hM : ∀ r s, M r s ∈ 𝒪[k])
    (hM' : ∀ r s, M' r s ∈ 𝒪[k]) (r₀ : n) (hr : ∀ s, valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) < 1) (z : n → k) :
    ((∀ r, (M' *ᵥ z) r ∈ 𝒪[k]) ↔ ∀ r, z r ∈ 𝒪[k]) ∧ ((∀ r, z r ∈ 𝒪[k]) → valuation k ((M' *ᵥ z) r₀ - z r₀) < 1) := by
  have hint : ∀ (N : Matrix n n k), (∀ r s, N r s ∈ 𝒪[k]) → ∀ w : n → k, (∀ r, w r ∈ 𝒪[k]) → ∀ r, (N *ᵥ w) r ∈ 𝒪[k] :=
    fun N hN w hw r => Subring.sum_mem _ fun s _ => Subring.mul_mem _ (hN r s) (hw s)
  refine ⟨⟨fun h r => ?_, fun h => hint M' hM' z h⟩, fun h => ?_⟩
  · have e : M *ᵥ (M' *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    rw [← e]
    exact hint M hM _ h r
  · have e : (M' *ᵥ z) r₀ - z r₀ = ∑ s, (M' r₀ s - (1 : Matrix n n k) r₀ s) * z s := by
      have : z r₀ = ∑ s, (1 : Matrix n n k) r₀ s * z s := by simp [Matrix.one_apply]
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_sub_distrib]
      simp_rw [sub_mul]
    rw [e]
    refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
    rw [Valuation.map_mul]
    have h1 := hr s
    have h2 : valuation k (z s) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (h s)
    calc valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * valuation k (z s)
        ≤ valuation k (M' r₀ s - (1 : Matrix n n k) r₀ s) * 1 := mul_le_mul' le_rfl h2
      _ < 1 := by rw [mul_one]; exact h1

theorem smul_pair_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' M M' : Matrix (Fin n) (Fin n) k) (hb : b' * b = 1) (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (hg : M = b * g.val * b') (hMM : M * M' = 1) (hM : ∀ r s, M r s ∈ 𝒪[k])
    (hM' : ∀ r s, M' r s ∈ 𝒪[k]) (hr : ∀ s, valuation k (M' r₀ s - (1 : Matrix (Fin n) (Fin n) k) r₀ s) < 1) :
    g • Q = Q := by
  have hM'M : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hK := intMat_keeps M M' hMM hM hM' r₀ hr
  have hbg : ∀ x : Fin n → k, b *ᵥ (g⁻¹ • x) = M' *ᵥ (b *ᵥ x) := by
    intro x
    have e1 : b * g.val = M * b := by
      rw [hg, Matrix.mul_assoc, Matrix.mul_assoc, hb, Matrix.mul_one]
    have e2 : b *ᵥ x = M *ᵥ (b *ᵥ (g⁻¹ • x)) := by
      have e3 : x = g.val *ᵥ (g⁻¹ • x) := by
        change x = g.val *ᵥ ((g⁻¹).val *ᵥ x)
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      conv_lhs => rw [e3]
      rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    rw [e2, Matrix.mulVec_mulVec, hM'M, Matrix.one_mulVec]
  refine GlobalTheory.LatPair.Pair.ext fun x a' => ?_
  rw [GlobalTheory.LatPair.Pair.smul_hasVal, hQ, hQ, hbg]
  have hres : ∀ (s y₁ y₂ : 𝒪[k]), valuation k ((y₁ : k) - y₂) < 1 → residue 𝒪[k] (s * y₁) = residue 𝒪[k] (s * y₂) := by
    intro s y₁ y₂ h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← mul_sub]
    refine Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 ?_)
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa using h)
  obtain ⟨hiff, hlast⟩ := hK (b *ᵥ x)
  constructor
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, (b *ᵥ x) r ∈ 𝒪[k] := hiff.1 fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine hres s _ _ ?_
    rw [hy r₀]
    exact hlast hz
  · rintro ⟨y, hy, s, hs, ha⟩
    have hz : ∀ r, (b *ᵥ x) r ∈ 𝒪[k] := fun r => hy r ▸ (y r).2
    refine ⟨fun r => ⟨_, hiff.2 hz r⟩, fun r => rfl, s, hs, ?_⟩
    rw [ha]
    refine (hres s _ _ ?_).symm
    rw [hy r₀]
    exact hlast hz

theorem col_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) (Lb : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x ∈ Lb, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (v : HeightOneSpectrum (𝓞 F))
    (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (σ : E →+* E) J Lb)),
      x *ᵥ y - y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) Lb) (s : Fin n) :
    (fun r => x r s - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) r s) ∈
      Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) Lb := by
  subst hJ
  have hd : (Pi.single s 1 : Fin n → E) ∈ Formalism.BasicNotions.dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) Lb := by
    intro z hz
    obtain ⟨r, hr⟩ := hL z hz s
    rw [GlobalTheory.uLocDual_hform_one]
    refine ⟨RingOfIntegers.mapRingHom (σ : E →+* E) r, ?_⟩
    simp [Pi.single_apply, hr]
  have h1 := hx _ (Submodule.subset_span ⟨_, Submodule.subset_span hd, rfl⟩)
  have e : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s 1 : Fin n → E) i)) = Pi.single s 1 := by
    funext i
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]
  beta_reduce at h1
  rw [e, Matrix.mulVec_single_one] at h1
  convert h1 using 1
  funext r
  rw [Pi.sub_apply, Pi.single_apply, Matrix.one_apply]
  rfl


set_option maxHeartbeats 2000000 in
theorem mat_int (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : Formalism.L2.NTheta.IsIdemAt p.e P) (V : HSp D) {n : ℕ}
    (hn : V.rank = n) (t : 𝓞 D.host.E) (ht : t ∈ P.asIdeal) (Lb : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hLb : ∀ x, x ∈ Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r)) (κ : GA D V)
    (h3 : ∀ s, (fun r => Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V hn κ r s) -
      (1 : Matrix (Fin n) (Fin n) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r s) ∈
        Formalism.UG.latS (F := D.host.F) (p.v.adicCompletion D.host.F) (intV D.host.E p.v) Lb) (r s : Fin V.rank) :
    ((mt V κ).map p.pr) r s ∈ 𝒪[k] ∧ (r.1 + 1 = V.rank →
      valuation k (((mt V κ).map p.pr) r s - (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s) < 1) := by
  subst hn
  let y : Fin V.rank → AE D := fun r' => mt V κ r' s - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r' s
  have hy : (fun r' => Formalism.UG.prV (E := D.host.E) p.v (toEAf D (y r'))) =
      (fun r' => Formalism.UG.prV (E := D.host.E) p.v (GlobalTheory.AdForm.finM V rfl κ r' s) -
        (1 : Matrix (Fin V.rank) (Fin V.rank) (D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F)) r' s) := by
    funext r'
    simp only [y]
    rw [RingHom.map_sub, RingHom.map_sub]
    congr 1
    by_cases h : r' = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, RingHom.map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, RingHom.map_zero, RingHom.map_zero]
  have h4 := GlobalTheory.T.splitPoint_baseLattice_coords_integral_last_in_prime D k p P hP _ t ht _ hLb y (by rw [hy]; exact h3 s) r
  have h1 : p.pr ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) r s) = (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  simp only [y] at h4
  rw [map_sub, h1] at h4
  refine ⟨?_, fun hr => h4.2 hr⟩
  have := Subring.add_mem _ h4.1 (show (1 : Matrix (Fin V.rank) (Fin V.rank) k) r s ∈ 𝒪[k] by
    simp only [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _)
  rwa [sub_add_cancel] at this

theorem mt_mul_inv {D : D7} (V : HSp D) (κ : GA D V) : mt V κ * mt V κ⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt]
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem finM_inv {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D))
    (h : GlobalTheory.AdForm.finM V hn κ = x.1) : GlobalTheory.AdForm.finM V hn κ⁻¹ = (x⁻¹).1 := by
  subst hn
  have e : GlobalTheory.AdForm.finM V rfl κ * GlobalTheory.AdForm.finM V rfl κ⁻¹ = 1 := by
    have e1 : ∀ g, GlobalTheory.AdForm.finM V rfl g = (mt V g).map (toEAf D) := fun g => rfl
    rw [e1, e1, ← Matrix.map_mul, mt_mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h] at e
  exact (Units.inv_eq_of_mul_eq_one_right e).symm


set_option maxHeartbeats 2000000 in
theorem col_mem_level {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    (F : Formalism.L2.Forms.FormsTiedSym (I.rec7 l Z) u Ch chOf) (hF : I.StdF l Z u F) (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m)
    (S : Formalism.L2.Forms.StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (Formalism.L2.Forms.sigD (I.rec7 l Z))
      (Formalism.L2.Forms.gramN (I.rec7 l Z) i hi) ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f (Formalism.L2.Forms.badG (I.rec7 l Z)))
    (hLb : ∀ x, x ∈ S.Lb ↔ x ∈ TC.baseL B ((I.rec7 l Z).R.N i) (X.piT u))
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal)
    (x : GL (Fin ((I.rec7 l Z).R.N i)) (GlobalTheory.AdForm.EF (I.rec7 l Z))) (hx : x ∈ S.U) (s : Fin ((I.rec7 l Z).R.N i)) :
    (fun r => Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (x.1 r s) -
      (1 : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i))
        ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) r s) ∈
      Formalism.UG.latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) S.Lb := by
  have hgram : Formalism.L2.Forms.gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  haveI : NeZero ((I.rec7 l Z).R.N i) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let c : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E :=
    RingOfIntegers.mapRingHom (Formalism.L2.Forms.sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (c x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) :=
    fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (c F.atT.piU : (I.rec7 l Z).host.E) =
      (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 :=
    fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : S.Lb = Formalism.L2.Col.rll_dLat ((I.rec7 l Z).R.N i) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 S.Lb ?_
    rw [hF.piU]; exact hLb
  have h1 := (GlobalTheory.Mem.Col2.Lv.uloc_T_iff (Formalism.L2.Forms.sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x)
    (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx) (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram S F.atT.piU (c F.atT.piU) rfl hpq hTp hL
    v hv (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v hv) _).1 (((S.U_eq x).1 hx).2 v)
  exact col_mem _ hgram S.Lb (fun z hz j => let ⟨r, hr, _⟩ := (hLb z).1 hz j; ⟨r, hr⟩) v _ h1.2 s


set_option maxHeartbeats 4000000 in
theorem stdPair_fixed {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}
    (F : Formalism.L2.Forms.FormsTiedSym (I.rec7 l Z) u Ch chOf) (hF : I.StdF l Z u F) (j : ℕ) (hj : j ≤ (I.rec7 l Z).R.m)
    (S : Formalism.L2.Forms.StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (Formalism.L2.Forms.sigD (I.rec7 l Z))
      (Formalism.L2.Forms.gramN (I.rec7 l Z) j hj) ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f (Formalism.L2.Forms.badG (I.rec7 l Z)))
    (hLb : ∀ x, x ∈ S.Lb ↔ x ∈ TC.baseL B ((I.rec7 l Z).R.N j) (X.piT u))
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k)
    (β : ∀ j i, GlobalTheory.FinPl.Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → GlobalTheory.LatPair.Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, GlobalTheory.FinPl.Lat ((I.rec7 l Z).sp.X j))
    (hS : GlobalTheory.AdForm.StdT I l Z u p β Q L) (κ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (y : GL (Fin ((I.rec7 l Z).R.N j)) (GlobalTheory.AdForm.EF (I.rec7 l Z)))
    (hy : GlobalTheory.AdForm.finM _ (Formalism.L2.Forms.rankN (I.rec7 l Z) j hj) κ = y.1) (hU : y ∈ S.U) (i : ι)
    (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (hg : (mt _ κ).map (p i).pr = (β j i).b * g.val * (β j i).b') :
    g • Q j i = Q j i := by
  have hv := GlobalTheory.AdForm.stdT_levelPrime_mem_v I hI hP l Z u k ι p β Q L hS i
  obtain ⟨e, he⟩ := hS.1
  have hpi : X.piT u ∈ (e i).1.asIdeal := by
    obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
    have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := hPr.piT_cop u
    have hne : X.piT u ≠ 0 := by
      intro h0
      rw [h0, map_zero, isCoprime_zero_left] at hcop
      exact not_isUnit_zero hcop
    exact (Formalism.L2.Col.mem_divs hne _).1 (e i).2
  have key := fun (κ₀ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (x : GL (Fin ((I.rec7 l Z).R.N j)) (GlobalTheory.AdForm.EF (I.rec7 l Z)))
      (h : GlobalTheory.AdForm.finM _ (Formalism.L2.Forms.rankN (I.rec7 l Z) j hj) κ₀ = x.1) (hx : x ∈ S.U) =>
    mat_int (I.rec7 l Z) k (p i) (e i).1 (he i) _ (Formalism.L2.Forms.rankN (I.rec7 l Z) j hj)
      (X.piT u) hpi _ hLb κ₀ (fun s' => by
        rw [h]
        exact col_mem_level I hI hP l Z u F hF j hj S hLb _ hv x hx s')
  have k1 := key κ y hy hU
  have k2 := key κ⁻¹ y⁻¹ (finM_inv _ _ κ y hy) (inv_mem hU)
  rcases Nat.eq_zero_or_pos ((I.rec7 l Z).sp.X j).rank with h0 | hpos
  · have : g = 1 := Units.ext (Matrix.ext fun b _ => absurd b.2 (by omega))
    rw [this, one_smul]
  let r₀ : Fin ((I.rec7 l Z).sp.X j).rank := ⟨((I.rec7 l Z).sp.X j).rank - 1, by omega⟩
  have hr₀ : r₀.1 + 1 = ((I.rec7 l Z).sp.X j).rank := by simp only [r₀]; omega
  refine smul_pair_eq _ _ _ _ ((mt _ κ⁻¹).map (p i).pr) (β j i).b'b _ r₀
    (GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional I l Z u k ι p β Q L hS j hj i r₀ hr₀) g hg ?_ (fun r s => (k1 r s).1) (fun r s => (k2 r s).1)
    (fun s => (k2 r₀ s).2 hr₀)
  rw [← Matrix.map_mul, mt_mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.FamTrace.PairsFwd


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyColCh
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData ValuativeRel
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.Fam.TopLocFac


open Formalism.IndefR.Lev Formalism.IndefR.Mult in
theorem nonempty_rowCh {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word)
    (g : Geo D) (hψ : IsStdChar D R.ψ (-1)) (t : T) : Nonempty (RowCh R P u g t) :=
  ⟨{ vP := fun _ => 0, vT := fun _ _ => 0, sBF := fun _ _ _ => (GlobalTheory.Unf.Inhab.nonempty_stepBF hψ _ _).some,
     sFB := fun _ _ _ => (GlobalTheory.Unf.Inhab.nonempty_stepFB hψ _ _).some, io := fun _ => 0, ioT := fun _ _ => 0 }⟩

theorem nonempty_colCh {D : D7} (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : Nonempty (ColCh u C) :=
  ⟨{ kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => 0, eT := fun _ _ _ => 0,
     Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 }⟩

end GlobalTheory.Fam.TopLocFac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrimAtOfMonoId
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PrimSplit

variable {D : D7}

theorem pX_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (a : AE D) :
    (d.pX *ᵥ colMul d.jX i a) i = a := by
  have e : d.pX *ᵥ colMul d.jX i a = colMul (d.pX * d.jX) i a := by
    funext k
    simp only [Matrix.mulVec, dotProduct, colMul, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hp : d.pX * d.jX = 1 := by
    have h := congrArg rat d.e'e
    rw [rat_one] at h
    simpa only [HypDec.pX, HypDec.qX, HypDec.jX, rat, Matrix.map_mul] using h
  rw [e, hp, colMul, Matrix.one_apply_eq, mul_one]

theorem idAt_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {P : Pl D → Prop} {i : Fin ρ} {a : AE D}
    (h : colMul d.jX i a ∈ latV S L P) : a ∈ idAt D P := by
  rw [← pX_colMul d i a]
  exact GlobalTheory.IwaPlace.mulVec_mem_idAt _ (GlobalTheory.FinPl.FrameLat.latV_supp h) i

end GlobalTheory.SeeSaw.PrimSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JZeroMulMemLatticeIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.AdaptFBIdeals

variable {D : D7}

theorem supp_of_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (v : Pl D) (i : Fin ρ) (a : AE D)
    (h : colMul d.jX i a ∈ latV S L (· = v)) : a ∈ idAt D (· = v) := by
  have hp : d.pX * d.jX = 1 := by
    have h := congrArg rat d.e'e
    rw [rat_one] at h
    simpa only [HypDec.pX, HypDec.qX, HypDec.jX, rat, Matrix.map_mul] using h
  have h1 : (d.pX * d.jX) i i = 1 := by rw [hp]; exact Matrix.one_apply_eq i
  rw [Matrix.mul_apply] at h1
  have h2 : a = ∑ k, d.pX i k * colMul d.jX i a k := by
    calc a = a * ∑ k, d.pX i k * d.jX k i := by rw [h1, mul_one]
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; simp only [colMul]; ring
  rw [h2]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.latV_supp h k)

theorem idV_supp (𝔞 : FI D) (v : Pl D) {a : AE D} (h : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, x, -, rfl⟩ := hy
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

end GlobalTheory.SeeSaw.AdaptFBIdeals

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilSchrodingerStandardUnnEvalZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilSchrodingerStandardUnnEvalZero
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.StdUnn

theorem weilSch_apply_zero_continuous : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ Φ : schwartzA θ V.rank n, Continuous fun g : G D n => (ω g Φ).1 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 0 = swSec A V omh μ 𝓕 f (κ.symm g) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    have e : κ (κ.symm g) = g := κ.apply_symm_apply g
    rw [e] at h
    exact (congrFun h 0).trans (mixS_dblDec_zero A V ψ₀ μ 𝓕 _ 0)
  have hc := (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ₀ A V χ⁻¹ omh hW μ 𝓕 hμ f hf).2
  have hk := (GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hκ).2
  simp_rw [key]
  exact hc.comp hk

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilSchrodingerStandardUnnEvalZeroStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_weilSchrodinger_standardUnn_eval_zero : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ Φ : schwartzA θ V.rank n, Continuous fun g : G D n => (ω g Φ).1 0 := by
  first | exact @GlobalTheory.StdUnn.weilSch_apply_zero_continuous | exact GlobalTheory.StdUnn.weilSch_apply_zero_continuous | (intros; apply GlobalTheory.StdUnn.weilSch_apply_zero_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.CoreGlue

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.LiftModel

variable {D : D7}

theorem rat_mulVec_mem {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latV T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα', 1, rfl, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] m i j) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem dsum_eq {S : HSp D} (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA {S A B : HSp D} (o : OrthDec S A B) (a : Fin A.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (o.iA *ᵥ a) ⬝ᵥ S.gram *ᵥ y = star a ⬝ᵥ A.gram *ᵥ (o.qA *ᵥ y) := by
  have h : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  rw [mulVec_mulVec, h, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star a)]

theorem exists_orthSum {S A B : HSp D} (o : OrthDec S A B) {LA : Lat A} {LB : Lat B} (hA : IsSelfDualC A LA)
    (hB : IsSelfDualC B LB) : ∃ L : Lat S, IsSelfDualC S L ∧ ∀ v, OrthAt o L LA LB v := by
  let fA := (mulVecLin o.iA).restrictScalars (𝓞 D.host.E)
  let fB := (mulVecLin o.iB).restrictScalars (𝓞 D.host.E)
  have hsum : ∀ y : Fin S.rank → D.host.E, y = o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) := fun y => by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.iA_qA_add, one_mulVec]
  have hiA : ∀ x ∈ LA, o.iA *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_left ⟨x, hx, rfl⟩
  have hiB : ∀ x ∈ LB, o.iB *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_right ⟨x, hx, rfl⟩
  have hmem : ∀ y, y ∈ LA.map fA ⊔ LB.map fB ↔ o.qA *ᵥ y ∈ LA ∧ o.qB *ᵥ y ∈ LB := fun y => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
      change o.qA *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LA ∧ o.qB *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LB
      simp only [mulVec_add, mulVec_mulVec, o.qA_iA, o.qA_iB, o.qB_iA, o.qB_iB, one_mulVec, zero_mulVec, add_zero, zero_add]
      exact ⟨ha, hb⟩
    · rw [hsum y]; exact add_mem (hiA _ h.1) (hiB _ h.2)
  refine ⟨LA.map fA ⊔ LB.map fB, ⟨⟨(hA.1.fg.map _).sup (hB.1.fg.map _), ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩,
    fun v y => ⟨fun hy => ⟨rat_mulVec_mem _ (fun x hx => ((hmem x).1 hx).1) hy,
      rat_mulVec_mem _ (fun x hx => ((hmem x).1 hx).2) hy⟩, fun h => ?_⟩⟩
  · exact (Submodule.IsLattice.of_fg D.host.E ((hA.1.fg.map fA).sup (hB.1.fg.map fB))).linearIndepOn
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hA.2 _).1 ((hmem y).1 hy).1 a ha
    obtain ⟨d, hd⟩ := (hB.2 _).1 ((hmem y).1 hy).2 b hb
    refine ⟨c + d, ?_⟩
    rw [dsum_eq] at hc hd ⊢
    change _ = star (o.iA *ᵥ a + o.iB *ᵥ b) ⬝ᵥ _
    have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA o.symm b y
    rw [star_add, add_dotProduct, pair_iA, e2, ← hc, ← hd]
    rfl
  · refine (hmem y).2 ⟨(hA.2 _).2 fun a ha => ?_, (hB.2 _).2 fun b hb => ?_⟩
    · have := h _ (hiA a ha)
      rwa [dsum_eq, pair_iA, ← dsum_eq] at this
    · have := h _ (hiB b hb)
      have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA o.symm b y
      rwa [dsum_eq, e2, ← dsum_eq] at this
  · have hs : o.jA * o.pA + o.jB * o.pB = 1 := by
      simp only [OrthDec.jA, OrthDec.jB, OrthDec.pA, OrthDec.pB, rat, ← Matrix.map_mul,
        ← Matrix.map_add _ (map_add (incA D)), o.iA_qA_add, Matrix.map_one _ (map_zero _) (map_one _)]
    have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, hs, one_mulVec]
    rw [e]
    exact add_mem (rat_mulVec_mem _ hiA h.1) (rat_mulVec_mem _ hiB h.2)

theorem mem_latV_one {S : HSp D} (L : Lat S) {P : Pl D → Prop} {v : Pl D} (hv : P v) (y : Fin S.rank → AE D) :
    y ∈ latV S L (· = v) ↔ y ∈ latV S L P ∧ ∀ i, y i ∈ idAt D (· = v) := by
  refine ⟨fun h => ⟨AddSubgroup.closure_mono ?_ h, latV_supp h⟩, fun h => ?_⟩
  · rintro _ ⟨α, h1, h2, r⟩
    exact ⟨α, h1, fun w hw => h2 w fun e => hw (e ▸ hv), r⟩
  · have key : ∀ y ∈ latV S L P, (fun i => y i * (pairA D.host.F 0 (LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E))) ∈
        latV S L (· = v) := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨α * LatMem.indP D.host.F (· = v),
          LatMem.intAf_mul' hα (LatMem.indicatorAdele_mem_integralAdeles' _ _), fun w hw => ?_, c, hc, x, hx, ?_⟩
        · rw [map_mul, LatMem.indicatorAdele_supported _ _ w hw, mul_zero]
        · funext i
          have hp : pairA D.host.F 0 α * pairA D.host.F 0 (LatMem.indP D.host.F (· = v)) =
            pairA D.host.F 0 (α * LatMem.indP D.host.F (· = v)) := Prod.ext (zero_mul _) rfl
          rw [Algebra.TensorProduct.tmul_mul_tmul, hp, mul_one]
      | zero => simp only [Pi.zero_apply, zero_mul]; exact zero_mem _
      | add a b _ _ ha hb => simp only [Pi.add_apply, add_mul]; exact add_mem ha hb
      | neg a _ ha => simp only [Pi.neg_apply, neg_mul]; exact neg_mem ha
    have := key y h.1
    simp only [LatMem.mul_indP (h.2 _)] at this
    exact this

theorem latV_eq_at {S : HSp D} {L M : Lat S} {P : Pl D → Prop} (h : latV S M P = latV S L P) {v : Pl D} (hv : P v) :
    latV S M (· = v) = latV S L (· = v) := by
  ext y
  rw [mem_latV_one M hv, mem_latV_one L hv, h]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_modify {ι : Type} {p : ι → SplitPt D k} (hp : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Λ : ι → Submodule 𝒪[k] (n → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k)
    {L : Lat S} (hL : IsSelfDualC S L) (l : List ι) : ∃ M : Lat S, IsSelfDualC S M ∧ (∀ i ∈ l, (β i).IsLat M (Λ i)) ∧
      ∀ v, (∀ i, v ≠ (p i).v) → latV S M (· = v) = latV S L (· = v) := by
  induction l with
  | nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨M', hM', h3, h4⟩ := (GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).2.2.2.2.1 M (Λ i) hM (by first | exact hΛ i | exact (hΛ i).toIsLattice)
    refine ⟨M', hM', fun i' hi' => ?_, fun v hv => (latV_eq_at h4 (hv i)).trans (h2 v hv)⟩
    by_cases e : i' = i
    · subst e; exact h3
    · intro x
      rw [latV_eq_at h4 (fun e' => e (hp e'))]
      exact h1 i' ((List.mem_cons.1 hi').resolve_left e) x

theorem pr_mem_of_intAt (p : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

theorem eq_sec_add (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a = p.sec (p.pr a) + cA D (p.sec (p.pr (cA D a))) := by
  rw [p.sec_pr, p.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff p a).1 ha]

theorem mem_intAt_iff (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a ∈ intAt D (· = p.v) ↔ p.pr a ∈ 𝒪[k] ∧ p.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_intAt p h.2, pr_mem_of_intAt p ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add p ha, RingHom.map_add (f := _)]
  exact add_mem ((p.int_iff _).1 h.1) ((cA_int_iff _).2 ((p.int_iff _).1 h.2))

theorem single_mem_glued_iff {n : Type} [DecidableEq n] (q : Unif k) (P : Pair k n) (t : k) :
    (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∈ gluedS q 1 P.ker P.vec ↔ t ∈ 𝒪[k] := by
  have h0 : (Pi.single (Sum.inr 0) t : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j
    simp
  rw [GlobalTheory.LevelUnfold.mem_gluedS, h0]
  constructor
  · rintro ⟨s, h1, h2⟩
    have h3 := (h2 0).1 rfl
    rw [Pi.single_eq_same] at h3
    rw [zero_sub, neg_mem_iff, Pair.mem_ker] at h1
    have h4 := (P.hasVal_vec.smul s).unique h1
    rw [mul_one, IsLocalRing.residue_eq_zero_iff, q.mem_max_iff] at h4
    obtain ⟨c, rfl⟩ := h4
    rw [h3, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]
    exact c.2
  · intro ht
    refine ⟨q.1 * ⟨t, ht⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · rw [zero_sub]
      exact neg_mem (Pair.smul_mem_ker (Ideal.mul_mem_right _ _ q.mem_max) P.hasVal_vec.mem)
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [Pi.single_eq_same, Unif.inv, Subring.coe_mul, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]

theorem pair_sumFrame {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : Frame p A n} {β₀ : Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀) (x : n ⊕ Fin 1 → k) (t : k) :
    ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) := by
  let f : D.host.E →+* k := p.pr.comp (incA D)
  let r : Fin S.rank → D.host.E := star (vecB o ζ) ᵥ* S.gram
  have hr : ∀ i, r i = ∑ j, star (S.gram i j) * star (vecB o ζ j) := fun i => by
    simp only [r, vecMul, dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, ← conjTranspose_apply, gram_conjTranspose]
  have h1 : ∑ i, ∑ j, (β₀.b *ᵥ x) i * p.pr (cA D (incA D (S.gram i j))) * (t * p.pr (incA D (star (vecB o ζ j)))) =
      t * ((f ∘ r) ⬝ᵥ β₀.b *ᵥ x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Function.comp_apply, hr, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change _ * f (star (S.gram i j)) * (t * f (star (vecB o ζ j))) = _
    ring
  have hA : r ᵥ* o.iA = 0 := by
    simp only [r, vecB, star_mulVec, vecMul_vecMul, o.orth, vecMul_zero]
  have hB : r ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ L.gram *ᵥ ζ := by
    rw [← o.isoB]
    simp only [r, vecB, star_mulVec, vecMul_vecMul, dotProduct_mulVec]
  have hA' : (f ∘ r) ᵥ* o.jA.map p.pr = 0 := by
    funext i
    have := RingHom.map_vecMul f o.iA r i
    rw [hA, Pi.zero_apply, map_zero] at this
    exact this.symm
  have hB' : (f ∘ r) ⬝ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) := by
    rw [← hB]
    exact (RingHom.map_dotProduct f r (vecB o ζ)).symm
  rw [h1, hs, dotProduct_mulVec, vecMul_fromCols, ← vecMul_vecMul, hA', zero_vecMul, ← hB']
  congr 1
  simp [dotProduct, vecMul, Fintype.sum_sum_type]

theorem line_of_glued {p : SplitPt D k} {ρ : ℕ} {B : BesLev D ρ} {M : Lat B.V₀} {q : Unif k} {n : Type} [Fintype n] [DecidableEq n]
    {β : Frame p B.A n} {β₀ : Frame p B.V₀ (n ⊕ Fin 1)} {P : Pair k n} (hM : IsSelfDualC B.V₀ M) (hg : GluedCore B M q β β₀ P)
    {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ M (· = p.v) ↔ a ∈ intAt D (· = p.v) := by
  have hdec : a • ratV (vecB B.o B.ζ) = (fun i => p.sec ((β₀.b *ᵥ (Pi.single (Sum.inr 0) (p.pr a) : n ⊕ Fin 1 → k)) i)) +
      fun i => cA D (p.sec (p.pr (cA D a) * p.pr (incA D (star (vecB B.o B.ζ i))))) := by
    funext i
    have e := eq_sec_add p (Ideal.mul_mem_right (incA D (vecB B.o B.ζ i)) _ ha)
    rw [RingHom.map_mul, RingHom.map_mul (cA D), RingHom.map_mul, cA_incA] at e
    refine e.trans ?_
    rw [Pi.add_apply, mulVec_single, hg.sum]
    congr 2
    exact mul_comm _ _
  have hq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by simpa using q.ne_zero
  have hu : valuation k (p.pr (incA D (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)) * q.inv) = 1 := by
    rw [map_mul, hg.norm, Unif.inv, map_inv₀, mul_inv_cancel₀ hq]
  rw [hdec, decomp hM, ← hg.lat, single_mem_glued_iff, mem_intAt_iff p ha, csec_mem_iff hM]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h x hx => ?_⟩
  · have h1 := h _ ((hg.lat _).1 (GlobalTheory.LevelUnfold.mem_gluedS.2 ⟨1, (by simp : Sum.elim P.vec (fun _ => q.inv) ∘ Sum.inl - (1 : 𝒪[k]) • P.vec ∈ P.ker),
      fun i => ⟨fun _ => by simp, fun hi => absurd hi (by omega)⟩⟩))
    rw [pair_sumFrame B.o B.ζ hg.sum, Sum.elim_inr, Valuation.mem_integer_iff, map_mul, hu, mul_one] at h1
    exact h1
  · have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
    rw [hx'] at hx
    obtain ⟨s, -, hs⟩ := GlobalTheory.LevelUnfold.mem_gluedS.1 ((hg.lat _).2 hx)
    rw [hx', pair_sumFrame B.o B.ζ hg.sum, (hs 0).1 rfl, ← mul_assoc _ q.inv]
    exact mul_mem h (mul_mem ((Valuation.mem_integer_iff _ _).2 hu.le) s.2)

end GlobalTheory.SeeSaw.CoreGlue

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionSmallIntegersInPrimeDense
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionSmallIntegersInPrimeDense
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SymBridge.ComplDense

theorem small_in_prime_and_dense : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) ∧ ∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1 := by
  intro E _ _ k _ _ _ _ PP q ι ϖ h hu
  refine ⟨fun z hz => (GlobalTheory.SymBridge.ComplRes.mem_P_iff h hu z).mpr hz, fun y hy => ?_⟩
  obtain ⟨i, -, hv⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep_one h hu y ((Valuation.mem_integer_iff _ _).mp hy)
  refine ⟨(i : 𝓞 E), ?_⟩
  have e : ι (((i : ℕ) : 𝓞 E) : E) = (i : k) := by simp
  rw [e]
  exact lt_of_le_of_lt hv (GlobalTheory.SymBridge.ComplRes.v_unif_lt_one hu)

end GlobalTheory.SymBridge.ComplDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionSmallIntegersInPrimeDenseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_smallIntegers_in_prime_dense : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) ∧ ∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1 := by
  first | exact @GlobalTheory.SymBridge.ComplDense.small_in_prime_and_dense | exact GlobalTheory.SymBridge.ComplDense.small_in_prime_and_dense | (intros; apply GlobalTheory.SymBridge.ComplDense.small_in_prime_and_dense <;> assumption)
end
end
