module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitModulusConstantsEquivariantDictionary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.FiniteNotLocFrOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceThetaFunctionVacuumConjugatePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimePowerLatticeInclusionOfLocalModels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpoFrobIndep
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem expo_frob_indep : ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool), ({ W with fr := fr, cj := cj } : Wts ι).Ok P ∧
      ∀ l : ℕ, l.Prime → W.WRange P l → ({ W with fr := fr, cj := cj } : Wts ι).coarseWeightBound P l = W.coarseWeightBound P l := by
  intro P hH hL ι _ _ W hW fr cj
  have hW' : ({ W with fr := fr, cj := cj } : Wts ι).Ok P :=
    { anti := hW.anti, what₂ := hW.what₂, block := hW.block, centre := hW.centre, window := hW.window,
      cloud := hW.cloud, low := hW.low, thick := hW.thick, other := hW.other }
  refine ⟨hW', ?_⟩
  intro l hl hR
  have hN := (places_real_holds P hH hL ι W hW (fun _ => 0)).2
  have hN' := (places_real_holds P hH hL ι ({ W with fr := fr, cj := cj } : Wts ι) hW' (fun _ => 0)).2
  have hi : ({ W with fr := fr, cj := cj } : Wts ι).iW P l = W.iW P l := by
    funext τ
    unfold Wts.iW SizeData₂.depth
    obtain ⟨a1, a2⟩ := hN l hl hR.1 hR.2.2.1 τ
    obtain ⟨b1, b2⟩ := hN' l hl hR.1 hR.2.2.1 τ
    rw [a1, a2, b1, b2]
    rfl
  unfold Wts.coarseWeightBound
  rw [hi]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimePowerLatticeInclusionOfLocalModels
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lIncl_of_models : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι), NumOk P W → (Formalism.EigenvalueLevelCeiling.plc w).Prime → W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam), Covers B ℓ Z w X → (∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) → LIncl B ℓ Z w (W.coarseWeightBound P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z w ι _ _ P W hN hl hR fr cj I X hC hX
  obtain ⟨hH, hL, hW, -⟩ := hN
  obtain ⟨hW', hJ⟩ := GlobalTheory.expo_frob_indep P hH hL ι W hW fr cj
  have hEq := hJ _ hl hR
  apply hC
  intro i
  obtain ⟨hu, hLk⟩ := hX i
  have hWI := Formalism.CohomologicalDescent.ShortWeightBounds.weight_inputs_of_linkage_holds P hH hL ι (reFr W fr cj) hW' _ (X i) hl hR.1 hLk
  have h := (Formalism.CohomologicalDescent.Top.inclusion_w_seven_real_holds P hH hL ι (reFr W fr cj) hW' _ (X i) hl hu hR.1 hWI).1
  unfold reFr at h
  rw [hEq] at h
  exact h

end GlobalTheory.ExpTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimePowerLatticeInclusionOfLocalModelsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primePowerLatticeInclusion_of_localModels : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι), NumOk P W → (Formalism.EigenvalueLevelCeiling.plc w).Prime → W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam), Covers B ℓ Z w X → (∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) → LIncl B ℓ Z w (W.coarseWeightBound P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  first | exact @GlobalTheory.ExpTie.lIncl_of_models | exact GlobalTheory.ExpTie.lIncl_of_models | (intros; apply GlobalTheory.ExpTie.lIncl_of_models <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentDatumLeOfPrimePowerLatticeInclusion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentDatumLeOfPrimePowerLatticeInclusion
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.ExpTie

theorem exists_mul_eq_prW_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (J : ℕ) {a : 𝓞 K}
    (ha : a ∈ w.asIdeal ^ (J * Formalism.L2.Col.eW w)) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ b : 𝓞 K, t * a = ((Formalism.L2.Col.prW w : ℕ) : 𝓞 K) ^ J * b := by
  have hm := (Formalism.L2.Col.algebraMap_mem_maximalIdeal_pow_iff w a (J * Formalism.L2.Col.eW w)).2 ha
  rw [mul_comm, pow_mul, ← Formalism.L2.Col.span_prW_ow, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  obtain ⟨y, hy⟩ := hm
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl y
  refine ⟨t, t.2, b, ?_⟩
  apply IsLocalization.injective (Formalism.L2.Col.Ow w) w.asIdeal.primeCompl_le_nonZeroDivisors
  rw [map_mul, map_mul, hy, map_pow, map_natCast, mul_comm, mul_assoc, IsLocalization.mk'_spec]

theorem LIncl.jexpU_bounds {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : Formalism.L2.DIV.BlockDat K G Pl0} {ℓ : Formalism.L2.DIV.Lvl K G} {Z : Submodule K B.S.Forms} {w : HeightOneSpectrum (𝓞 K)} {J : ℕ}
    (h : LIncl B ℓ Z w J) : 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  have he : 0 < Formalism.L2.Col.eW w := Formalism.L2.Col.eW_pos w
  have hp : Formalism.EigenvalueLevelCeiling.plc w = Formalism.L2.Col.prW w :=
    Formalism.L2.Col.eq_prW_of_mem w (Formalism.EigenvalueLevelCeiling.plc_prime w) (Formalism.EigenvalueLevelCeiling.plc_mem w)
  have key : B.JexpW ℓ Z w ≤ J * Formalism.L2.Col.eW w := by
    unfold Formalism.L2.DIV.BlockDat.JexpW Formalism.L2.DIV.expW
    apply Nat.sInf_le
    intro a ha z hz
    obtain ⟨t, ht, b, htb⟩ := exists_mul_eq_prW_pow w J ha
    obtain ⟨s, hs, hsz⟩ := h z hz
    refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    have e : (s * t) • (a • z) = b • (s • ((((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ J) • z)) := by
      rw [hp, smul_smul, smul_smul, smul_smul, mul_assoc, htb]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ b hsz
  refine ⟨?_, ?_⟩
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    positivity
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    rw [div_le_iff₀ (by exact_mod_cast he)]
    exact_mod_cast key

theorem jexpU_le_of_lIncl : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type)
    (B : Formalism.L2.DIV.BlockDat K G Pl0) (ℓ : Formalism.L2.DIV.Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ),
    LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => LIncl.jexpU_bounds h

end GlobalTheory.ExpTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentDatumLeOfPrimePowerLatticeInclusionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ), LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  first | exact @GlobalTheory.ExpTie.jexpU_le_of_lIncl | exact GlobalTheory.ExpTie.jexpU_le_of_lIncl | (intros; apply GlobalTheory.ExpTie.jexpU_le_of_lIncl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentOfRecordVsFormulas
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem exponent_of_record_vs_formulas :
    Formalism.CohomologicalDescent.E.ExCut → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
      ∀ l : ℕ, l.Prime → (¬ W.WRange P l → W.JA P l ≤ W.Jrec7 P l) ∧ (W.WRange P l → W.coarseWeightBound P l = W.Jrec7 P l) := by
  intro hC P hH hL ι _ _ W hW l hl
  refine ⟨fun hR => ?_, fun hR => ?_⟩
  · by_cases hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp
    · rw [seventh_recursion_eq_a_of_small_prime W P l hc]
    · have h1 : P.lJ < (l : ℝ) := not_le.mp fun h => hc (Or.inl h)
      have h2 : ¬ P.Excl l := fun h => hc (Or.inr (Or.inl h))
      have h3 : l ∉ W.Sp := fun h => hc (Or.inr (Or.inr h))
      have hh : P.h < (l : ℝ) := not_le.mp fun h => hR ⟨h1, h, h2, h3⟩
      have hb := Formalism.CohomologicalDescent.E.beyond_height_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC P hH hL ι W hW l hl h1 hh
      rw [hb.2.1]
      exact Nat.zero_le _
  · obtain ⟨h1, _, h2, h3⟩ := hR
    have hc : ¬ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) := by
      rintro (h | h | h)
      · exact absurd h (not_le.mpr h1)
      · exact h2 h
      · exact h3 h
    rw [seventh_recursion_eq_w_of_large_prime W P l hc]

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Asm

open Formalism.L2.Indef Formalism.L2.Indef.Tree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jexpU_le_jrec7 (hcut : Formalism.CohomologicalDescent.E.ExCut) {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G]
    [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι) (hN : NumOk P W)
    (hoff : ¬ W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → LIncl B ℓ Z w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)))
    (hin : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∃ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam),
      Covers B ℓ Z w X ∧ ∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) :
    B.JexpU ℓ Z w ≤ (W.Jrec7 P (Formalism.EigenvalueLevelCeiling.plc w) : ℚ) := by
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime w
  have hrec := GlobalTheory.exponent_of_record_vs_formulas hcut P hN.1 hN.2.1 ι W hN.2.2.1 _ hp
  by_cases hR : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w)
  · obtain ⟨fr, cj, I, X, hc, hX⟩ := hin hR
    have h1 := GlobalTheory.T.primePowerLatticeInclusion_of_localModels K G Pl0 B ℓ Z w ι P W hN hp hR fr cj I X hc hX
    have h2 := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion K G Pl0 B ℓ Z w _ h1).2
    rw [hrec.2 hR] at h2
    exact h2
  · have h2 := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion K G Pl0 B ℓ Z w _ (hoff hR)).2
    exact h2.trans (by exact_mod_cast hrec.1 hR)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem splitPartNumbers_exponent_eq_liftExponent (C CH : ℝ) (t : p.P.T) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) :
    ((R2 p).num (F2 p) C CH).J0 t w j = (((blk p j t).JexpU (lvlL p) (subZ p j t) w : ℚ) : ℝ) := rfl


open Classical in
theorem hasExpBound_at (hcut : Formalism.CohomologicalDescent.E.ExCut) {c : OnConst} (O : Obj p c)
    (hm : O.m = (D.R.m : ℝ)) (hx : O.x = L.sc.x) (heps : O.eps = L.sc.eps) (hT2 : O.T2 = D.host.T2.card)
    (Pj : Fin D.R.m → Par) (Wj : Fin D.R.m → Wts D.what₂.Tau) (hD : ∀ j, Dict L j (Pj j) (Wj j))
    (hN : ∀ j, NumOk (Pj j) (Wj j))
    (hS : ∀ j t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w ((Wj j).JA (Pj j) (Formalism.EigenvalueLevelCeiling.plc w)))
    (hM : ∀ j, ∀ w ∈ p.R.twPl, (Wj j).WRange (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j (Pj j) (Wj j) w) (C CH : ℝ) :
    HasExpBound ((R2 p).num (F2 p) C CH) O := by
  constructor
  · intro w _ j
    have h := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion _ _ _ _ _ _ w _ (hS j ((S2 p).μ w) w)).1
    rw [splitPartNumbers_exponent_eq_liftExponent]
    exact_mod_cast h
  refine ⟨fun j l => ((Wj j).Jrec7 (Pj j) l : ℝ), ?_, ?_⟩
  · intro j
    constructor
    · intro l
      exact Nat.cast_nonneg _
    intro Q hQ
    obtain ⟨hHyp, hLarge, hOk, X', A, hRows, hBig⟩ := hN j
    have hcard : Fintype.card D.what₂.Tau = (Pj j).f := by rw [← Nat.card_eq_fintype_card]; exact (hD j).card
    have h := UpperTheory.ExcSet.sum_exponent_log_le hcut D (Pj j) X' A hHyp hLarge hRows hBig D.what₂.Tau (Wj j) hOk hcard (hD j).f
      (hD j).special O.T2
      (by rw [hT2]; exact (hD j).thick) Q hQ
    have hxe : O.xe = (Pj j).L := by rw [(hD j).log]; show O.x ^ O.eps = _; rw [hx, heps]
    have hb : O.b = (Pj j).b := by rw [(hD j).b]; show Real.exp O.xe = _; rw [hxe, (hD j).log]; rfl
    have hm' : O.m = ((Pj j).m : ℝ) := by rw [hm, (hD j).m]
    show _ ≤ 30 * (O.T2 : ℝ) * O.m * O.b * O.xe ^ 2 + 2 * O.m * O.b
    rw [hxe, hb, hm']
    exact h
  · intro w hw j
    have hle := jexpU_le_jrec7 hcut (blk p j (p.R.mu w)) (lvlL p) (subZ p j (p.R.mu w)) w (Pj j) (Wj j) (hN j)
      (fun _ => hS j _ w) (fun hR => hM j w hw hR)
    show (((blk p j (p.R.mu w)).JexpU (lvlL p) (subZ p j (p.R.mu w)) w : ℚ) : ℝ) ≤ ((Wj j).Jrec7 (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) : ℝ)
    exact_mod_cast hle

end Point

end GlobalTheory.ExpTie.Asm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullRepTwist
noncomputable section

namespace GlobalTheory.TwistedRepresentationEmbedding

open Module

def twist {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V) (χ : G →* Kˣ) :
    Representation K G V where
  toFun g := ((χ g : Kˣ) : K) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_smul]
    ring_nf

theorem twist_apply {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (χ : G →* Kˣ) (g : G) (v : V) : twist ρ χ g v = ((χ g : Kˣ) : K) • ρ g v := rfl

def embV {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) : (Fin N → K) →ₛₗ[σ] (Fin N → ℂ) where
  toFun v k := σ (v k)
  map_add' v w := by funext k; simp
  map_smul' a v := by funext k; simp

def repE {K G : Type} [Field K] [Group G] {N : ℕ} (σ : K →+* ℂ) (ρ : Representation K G (Fin N → K)) :
    Representation ℂ G (Fin N → ℂ) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map σ)
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.toLin'_one]; rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]; rfl

theorem repE_embV {K G : Type} [Field K] [Group G] {N : ℕ} (σ : K →+* ℂ) (ρ : Representation K G (Fin N → K)) (g : G)
    (v : Fin N → K) : repE σ ρ g (embV σ N v) = embV σ N (ρ g v) := by
  funext k
  change (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map σ)) (fun j => σ (v j)) k = σ (ρ g v k)
  have h := RingHom.map_mulVec σ (LinearMap.toMatrix' (ρ g)) v k
  rw [LinearMap.toMatrix'_mulVec] at h
  rw [Matrix.toLin'_apply, h]
  rfl

theorem embV_single {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) (k : Fin N) :
    embV σ N (Pi.single k 1) = Pi.single k 1 := by
  funext j
  change σ ((Pi.single k (1 : K) : Fin N → K) j) = (Pi.single k (1 : ℂ) : Fin N → ℂ) j
  by_cases h : j = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem embV_li {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) :
    LinearIndependent ℂ fun k => embV σ N (Pi.single k 1) := by
  convert (Pi.basisFun ℂ (Fin N)).linearIndependent using 1
  funext k
  simp [embV_single]

theorem embV_span {K : Type} [Field K] (σ : K →+* ℂ) (N : ℕ) :
    Submodule.span ℂ (Set.range (embV σ N)) = ⊤ := by
  refine eq_top_iff.2 ((Pi.basisFun ℂ (Fin N)).span_eq.ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨Pi.single k 1, by simp [embV_single]⟩

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem isPullRep_twist {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U]
    [MulAction U C] {M : TwoLevels E r U C} {la : Wt M.Ψ r} {ρ : Representation ℂ U (M.cusp la)}
    (h : IsPullRep M la ρ) (χ : U →* ℂˣ) : IsPullRep M la (twist ρ χ) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun u c => χ u⁻¹ * a u c, fun u F hF c x => ?_⟩
  rw [twist_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, ha u F hF c x]
  simp [mul_assoc]

end GlobalTheory.TwistedRepresentationEmbedding

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhRatOfSerCore
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PhRatCommon


set_option maxHeartbeats 1000000 in
theorem phRat_of_ser_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → ∀ cc, SerOf (O i) (κ i) (v₀ i (sg0 D A)) cc 1 → (∀ x : (O i).Cl' () → VsV D i (O i).c'.F, ∃ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, IsThClsD (T.Q.Xo ((i : ℕ) + 1)) (O i).c' ((O i).dδ ()) ((O i).w ()) ((O i).La ()) ((O i).Nc ()) ((O i).gam ()) ((O i).vol ()) ((O i).ep ()) (O i).io x f) → (O i).EquivAt (κ i) cc → (O i).PhRat (κ i) (v₀ i (sg0 D A)) cc 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR t O i hpins cc hser hex hequiv
  obtain ⟨hcc, hph, hs⟩ := hser
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (t.kap i τ).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  refine GlobalTheory.PhaseRationalDegenerate.of_before_projector (O i) (κ i) _ cc hequiv hR.grp.chiW hR.thP.thG 1 fun x₀ => ?_
  obtain ⟨h, J', hrep, hP, -, -⟩ := (hpins.2.tuple ()).reps
  obtain ⟨x, hx⟩ := hP x₀
  obtain ⟨f, hf, hcl⟩ := hex x
  have hf' : f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) (O i).c' (unfBC (O i).hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (κ i).n := by
    rw [hn]; exact hf
  have hBC := exists_rdU_eq_sum (O i).hle (T.U ((i : ℕ) + 1)) (inC (O i).c') _ _ f hf'
  obtain ⟨m, as, fs, hbc⟩ := hBC
  have hL : ∀ a : (O i).c'.F, ∃ b : D.what₂.LL, D.what₂.embLL b = inC (O i).c' a := fun a => by
    have : (a : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hpins.1 ▸ a.2
    exact this
  choose b hb using hL
  refine ⟨m, fun j => b (as j), fs, fun g => ?_⟩
  have := hs () h J' hrep _ x hx f hf.1 hcl g
  have e1 := hbc ((O i).dict g).1 ((O i).dict g).2
  have e2 : ∀ j, (O i).phi cc (fs j : T.R ((i : ℕ) + 1)) g = cc ((O i).dict g).1 * (O i).mu g *
      rdU (T.U ((i : ℕ) + 1) (O i).s0) (fs j : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 := fun j => rfl
  exact this.trans (sum_shape e1 (fun j => hb (as j)) e2)

end GlobalTheory.PhRatCommon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremal
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapTies

theorem oneMapRow0_of_ties_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ hR ht hio O i hpins
  have h := GlobalTheory.T.exists_unitModulus_constants_equivariant_dictionary hCI D G Pl0 T0 A T R F κ v₀ hR ht hio i Unit (fun _ => A.μ0) (O i) hpins.2
  obtain ⟨cc, -, u, -, hequiv, hser, hid⟩ := h
  exact GlobalTheory.OneMapBase.oneMapRow0_of_rows T R κ v₀ O i (u • cc) 1 hpins hequiv hid
    (GlobalTheory.PhRatCommon.phRat_of_ser_core D G Pl0 T0 A T R F κ v₀ hR ht O i hpins (u • cc) hser
      (GlobalTheory.T.exists_cuspForm_classSum_normalisedData hCI D G Pl0 T0 A T R F κ v₀ hR ht i _ _ (O i) hpins.2 ()) hequiv)

end GlobalTheory.OneMapTies
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremalStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i := by
  first | exact @GlobalTheory.OneMapTies.oneMapRow0_of_ties_core | exact GlobalTheory.OneMapTies.oneMapRow0_of_ties_core | (intros; apply GlobalTheory.OneMapTies.oneMapRow0_of_ties_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExpansionStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SumExpAt

theorem mem_locP {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

theorem locIncl_of_equiv {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (e : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (N D : Submodule (𝓞 K) V) (N' D' : Submodule (𝓞 K) V')
    (hN : N.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = N')
    (hD : D.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = D')
    (h : ∀ x ∈ N', a • x ∈ Formalism.HermitianLatticesTheory.localization₂ p D') : ∀ v ∈ N, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p D := by
  intro v hv
  set f : V →ₗ[𝓞 K] V' := (e : V →ₗ[K] V').restrictScalars (𝓞 K) with hf
  have hx : f v ∈ N' := hN ▸ Submodule.mem_map_of_mem hv
  obtain ⟨s, hs, hsD⟩ := (mem_locP p D' _).1 (h _ hx)
  refine (mem_locP p D _).2 ⟨s, hs, ?_⟩
  rw [← hD] at hsD
  obtain ⟨y, hy, hye⟩ := hsD
  have hinj : Function.Injective f := e.injective
  have : y = s • a • v := hinj (by rw [hye, map_smul, map_smul])
  rw [← this]
  exact hy

theorem cutLat_locIncl {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.DIV.CSD K) {d : ℕ}
    (E : Matrix (Fin S.dim) (Fin d) K) (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (h : ∀ c, ∀ v ∈ S.Nab c, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p (S.Del c)) :
    ∀ z ∈ Formalism.DivisionValues.cutLat E S.nabLat, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ p (Formalism.DivisionValues.cutLat E S.delLat) := by
  classical
  intro z hz
  have hz' : ∀ c, S.I (E.mulVec z) c ∈ S.Nab c := fun c => hz c (Set.mem_univ c)
  have hlin : ∀ (r : 𝓞 K) (y : Fin d → K), S.I (E.mulVec (r • y)) = r • S.I (E.mulVec y) := fun r y => by
    have h1 := ((Matrix.mulVecLin E).restrictScalars (𝓞 K)).map_smul r y
    have h2 := (S.I.restrictScalars (𝓞 K)).map_smul r (E.mulVec y)
    simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at h1 h2
    rw [h1, h2]
  choose s hs hsD using fun c => (mem_locP p (S.Del c) _).1 (h c _ (hz' c))
  refine (mem_locP p _ _).2 ⟨∏ c, s c, prod_mem fun c _ => hs c, ?_⟩
  intro c _
  show S.I (E.mulVec ((∏ c, s c) • a • z)) c ∈ S.Del c
  rw [hlin, hlin, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ c), Pi.smul_apply, Pi.smul_apply, mul_comm,
    mul_smul]
  exact Submodule.smul_mem _ _ (hsD c)

end GlobalTheory.SumExpAt

namespace GlobalTheory.SumExpAt


open Formalism.CohomologicalDescent.LD in
theorem exZ_res_eq_natW (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) (f : ℕ → ℕ) (c : ℤ)
    (hc : ∀ a : Fin n, (f a : ℤ) = lam.w a + c) (l : ℕ) (hl : l.Prime) :
    Formalism.CohomologicalDescent.LA.exZ n n le_rfl (res n f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl lam.natW l := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · congr 1
    funext a
    exact a.elim0
  · let m : Fin n := ⟨n - 1, by omega⟩
    have hds : lam.detShift = lam.w m := by
      simp only [Formalism.BasicNotions.DomWeight.detShift, dif_pos hn]
      rfl
    have hres : res n f = fun a => lam.natW a + f m := by
      funext a
      have h1 := hc a
      have h2 := hc m
      have h3 : lam.w m ≤ lam.w a := lam.anti (Fin.le_def.2 (by simp only [m]; omega))
      have h4 : ((lam.w a - lam.w m).toNat : ℤ) = lam.w a - lam.w m := Int.toNat_of_nonneg (by omega)
      change f a.val = (lam.w a - lam.detShift).toNat + f m
      rw [hds]
      omega
    have hanti : Antitone lam.natW := fun i j hij => by
      have := lam.anti hij
      exact Int.toNat_le_toNat (by omega)
    rw [hres]
    exact Formalism.CohomologicalDescent.LA.exact_z_twist_by_det n lam.natW (f m) l hanti hl

theorem exZ_res_congr {N n : ℕ} (h : N = n) (f : ℕ → ℕ) (l : ℕ) :
    Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Formalism.CohomologicalDescent.LD.res N f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl (Formalism.CohomologicalDescent.LD.res n f) l := by
  subst h
  rfl

end GlobalTheory.SumExpAt

namespace GlobalTheory.ExpTie

open GlobalTheory.SumExpAt
open Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem lIncl_sumExp (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (hD : Dict L j P W) (t : p.P.T)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := p.charW.base.fam.tie
  obtain ⟨e, -, -, -, hNab, hDel⟩ := hT.coefL j t
  have hJ : W.JA P (Formalism.EigenvalueLevelCeiling.plc w) = ∑ τ, Formalism.CohomologicalDescent.LA.exZ (Vc D j).rank (Vc D j).rank le_rfl
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ).natW (Formalism.EigenvalueLevelCeiling.plc w) := by
    unfold Wts.JA Wts.ex
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [exZ_res_congr hD.Nr]
    obtain ⟨c, hc⟩ := hD.lam τ
    exact exZ_res_eq_natW _ _ _ c hc _ (Formalism.EigenvalueLevelCeiling.plc_prime w)
  intro z hz
  rw [hJ]
  refine cutLat_locIncl (blk p j t).S _ w.asIdeal _ (fun c => ?_) z hz
  refine locIncl_of_equiv e w.asIdeal _ _ _ _ _ (hNab c) (hDel c) ?_
  have hLat (g : Bridge.Gf (Vc D j)) : Submodule.IsFullLattice D.host.E (Bridge.hLat (Vc D j) g) := by
    obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D j)
    obtain ⟨Λ, hΛ, h1, h2, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E (Vc D j).rank (GlobalTheory.Member.latC (Vc D j)) g.1 hfg hsp
    rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat (Vc D j) g).trans hΛ.symm)]
    exact { toIsLattice := Submodule.IsLattice.of_fg D.host.E h1, span_eq_top := h2 }
  exact GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr _ _ _ _ _ _ _ (hLat _) w

end Point

end GlobalTheory.ExpTie

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConj
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.OppLinChar

open scoped TensorProduct
open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right atPlace_mul_right evFin_atPlace)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_tmul' [FiniteDimensional F E] {R : Type} [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem evFin_trace [FiniteDimensional F E] (v : Pl (F := F)) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    have e : compFin F E v (a ⊗ₜ[F] x) = evFin F v a ⊗ₜ[F] x := rfl
    rw [e, trace_tmul', trace_tmul', map_mul, AlgHom.commutes]

theorem trace_split {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y = splitProj t y + splitProj (t.comp σ) y := by
  rw [← Algebra.trace_eq_of_algEquiv (splitAlgEquiv h t) y, Algebra.trace_prod_apply, splitAlgEquiv_apply]
  simp [Algebra.trace_self_apply]

theorem piW_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (y : AE F E) :
    piW (t.comp σ) (cA σ y) = piW t y := by
  have e : compFin F E v (cA σ y) = sigR (Fv F v) σ (compFin F E v y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => rfl
  change splitProj (t.comp σ) (compFin F E v (cA σ y)) = splitProj t (compFin F E v y)
  rw [e]
  exact splitProj_comp_sigR h t _

theorem piW_inclR {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (AF F) x) = t x := by
  change splitProj t (evFin F v 1 ⊗ₜ[F] x) = t x
  rw [map_one]
  exact splitProj_inclR t x

theorem piW_tensAt {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) : piW t (tensAt E v y) = splitProj t y := by
  change splitProj t (compFin F E v (tensAt E v y)) = _
  rw [compFin_tensAt]

theorem at_tensAt {v : Pl (F := F)} (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := by
  intro a ha
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (AE F E) a) = 0 := by
    change evFin F v a ⊗ₜ[F] (1 : E) = 0
    rw [ha, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

theorem eq_liftV_of_at {v : Pl (F := F)} {a : AF F} (ha : At (evFin F v) a) : a = GlobalTheory.LatVac.liftV v (evFin F v a) := by
  have h1 : evFin F v (1 - atPlace v 1) = 0 := by rw [map_sub, map_one, evFin_atPlace, sub_self]
  have h2 := ha _ h1
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h2
  calc a = atPlace v 1 * a := h2
    _ = atPlace v (1 * evFin F v a) := atPlace_mul_right v 1 a
    _ = GlobalTheory.LatVac.liftV v (evFin F v a) := by rw [one_mul]; rfl

end GlobalTheory.OppLinChar

namespace GlobalTheory.OppLinChar

open scoped TensorProduct
open GlobalTheory.EmbChart (tensAt)

theorem char_eq_psi_symp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Z : Matrix (Fin n) (Fin d) (Fv F v)), ∃ u : Matrix (Fin n) (Fin d) (AE F E),
      At (evFin F v) u ∧ u.map (piW (t.comp σ)) = 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x →
        x.map (piW t) = 0 → B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j) := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t Z
  have h := hB.cm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  refine ⟨Matrix.of fun k l => tensAt E v ((splitAlgEquiv h t).symm (-Z k l, 0)), ?_, ?_, ?_⟩
  · intro a ha
    ext k l
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact at_tensAt _ a ha
  · ext k l
    simp [piW_tensAt]
  · intro x hxv hx
    set u : Matrix (Fin n) (Fin d) (AE F E) := Matrix.of fun k l => tensAt E v ((splitAlgEquiv h t).symm (-Z k l, 0))
      with hu_def
    have hx' : ∀ i j, piW t (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx i) j
    have hJX : ∀ i k, piW (t.comp σ) (incM F X.J i k) = t (X.J k i) := fun i k => by
      rw [incM, Matrix.map_apply, piW_inclR, AlgHom.comp_apply, hX.herm]
    have hJW : ∀ j l, piW (t.comp σ) (incM F W.J j l) = -t (W.J l j) := fun j l => by
      rw [incM, Matrix.map_apply, piW_inclR, AlgHom.comp_apply, hW.skew, map_neg]
    have hu : ∀ k l, piW (t.comp σ) (cA σ (u k l)) = -Z k l := fun k l => by
      rw [piW_cA h, hu_def, Matrix.of_apply, piW_tensAt, splitProj_symm]
    set S := symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u with hS_def
    have hat : At (evFin F v) S := by
      intro a ha
      rw [smul_eq_mul, ← one_mul S, ← mul_assoc, hS_def, ← GlobalTheory.LatVac.symp_smul_smul]
      have h0 : a • x = 0 := hxv a ha
      rw [h0]
      simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
    have hev : evFin F v S = ∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) *
        (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j := by
      rw [hS_def, GlobalTheory.WeilM.symp, evFin_trace, trace_split h t]
      change piW t _ + piW (t.comp σ) _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [GlobalTheory.WeilM.hTens, map_mul, map_neg, map_one, map_sum, hx', hJX, hJW, hu]
      have key : ∀ (f : Fin n → Fin d → Fin n → Fin d → Fv F v),
          ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ b, ∑ a, f a b i j := by
        intro f
        calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ j, ∑ b, f a b i j := by
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ i, ∑ j, ∑ b, ∑ a, f a b i j := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      simp only [zero_mul, Finset.sum_const_zero, mul_zero, zero_add, Units.val_one, Matrix.transpose_one,
        Matrix.one_mul, Matrix.mul_one, Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      simp only [Finset.mul_sum, Finset.sum_mul, neg_mul, ← Finset.sum_neg_distrib]
      refine (key _).trans ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    change B.ψ S = B.ψ (GlobalTheory.LatVac.liftV v _)
    rw [← hev, ← eq_liftV_of_at hat]

end GlobalTheory.OppLinChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConjStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_moment_surjective_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (Z : Matrix (Fin n) (Fin d) (Fv F v)), ∃ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      At (evFin F v) u ∧ u.map (piW (t.comp σ)) = 0 ∧ ∀ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x →
        x.map (piW t) = 0 → B.ψ (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) x u) =
          GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * (x).map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1)) i j * Z i j) := by
  first | exact @GlobalTheory.OppLinChar.char_eq_psi_symp | exact GlobalTheory.OppLinChar.char_eq_psi_symp | (intros; apply GlobalTheory.OppLinChar.char_eq_psi_symp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDefiniteRationalPointDataComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDefiniteRationalPointDataComponent
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt.PtExist

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ Z : Comp Xo c, Nonempty (PtData Z) :=
  GlobalTheory.DefPt.Model.nonempty_ptData_all

end GlobalTheory.DefPt.PtExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDefiniteRationalPointDataComponentStatement
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_definiteRationalPointData_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ Z : Comp Xo c, Nonempty (PtData Z) := by
  first | exact @GlobalTheory.DefPt.PtExist.main | exact GlobalTheory.DefPt.PtExist.main | (intros; apply GlobalTheory.DefPt.PtExist.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedAlmostAllPlaces
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PairVac

theorem eventually_unrAt_of_isHecke {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (χ : Chr F E) (hχ : IsHecke F E χ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, UnrAt χ w := by
  obtain ⟨H, hloc, -⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ hcm χ hχ
  refine (GlobalTheory.HeckeSplit.eventually_unrAt H.1 H.2.1).mono fun w hw x hx => ?_
  rw [← hloc w x]
  exact ((GlobalTheory.HeckeSplit.unrAt_iff E H w).1 hw) x hx

end GlobalTheory.PairVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGroupOrderBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

noncomputable section

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_GL_zmod_le (r q : ℕ) (hq : q ≠ 0) :
    Nat.card (GL (Fin r) (ZMod q)) ≤ q ^ (r * r) := by
  haveI : NeZero q := ⟨hq⟩
  calc Nat.card (GL (Fin r) (ZMod q)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod q)) :=
        Nat.card_le_card_of_injective (fun u => (u : Matrix (Fin r) (Fin r) (ZMod q))) (fun a b h => Units.ext h)
    _ = q ^ (r * r) := by
        rw [Nat.card_eq_fintype_card]
        show Fintype.card (Fin r → Fin r → ZMod q) = q ^ (r * r)
        rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_mul]

end GlobalTheory.CovTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestWeightLiftModStableSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestWeightLiftModStableSubspace
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.LiftMod

theorem kstable_of_units {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (U : Submodule ℂ V) (h : ∀ a b : Ix p q, a.isLeft = b.isLeft → ∀ u ∈ U, units act a b u ∈ U) : KStable act U := by
  intro X hX u hu
  have hXs : X = ∑ a, ∑ b, X a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hXs, map_sum, LinearMap.sum_apply]
  refine U.sum_mem fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  refine U.sum_mem fun b _ => ?_
  rw [map_smul, LinearMap.smul_apply]
  by_cases hab : sameBlock a b
  · refine U.smul_mem _ (h a b ?_ u hu)
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · exact (hab : False).elim
    · exact (hab : False).elim
    · rfl
  · rw [hX a b hab, zero_smul]; exact U.zero_mem

theorem lift_mod : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ (μ : Ix p q → ℚ), ∀ v ∈ N', (∀ c, act (Eab c c) v - ((μ c : ℚ) : ℂ) • v ∈ N) → (∀ c d, posC c d → act (Eab c d) v ∈ N) → ∃ v' ∈ N', v' ∈ hwSub act μ ∧ v - v' ∈ N := by
  intro p q V _ _ act hG N N' hN hN' μ v hv h1 h2
  obtain ⟨hLie, hwt, hloc⟩ := hG
  obtain ⟨U, hvU, hUfd, hUst, -⟩ := hloc {v}
  have hU : KStable act U := kstable_of_units act U hUst
  have hvU' : v ∈ U := hvU v (Finset.mem_singleton_self v)
  haveI : FiniteDimensional ℂ U := hUfd
  let W : Submodule ℂ V := N' ⊓ U
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (inf_le_right : W ≤ U)
  have sW : KStable act W := fun X hX w hw => ⟨hN' X hX w hw.1, hU X hX w hw.2⟩
  have hKL : Formalism.MainNotions.SchurIrreducible.IsKLieAct act := fun Y Z _ _ => hLie Y Z
  obtain ⟨T', hT'W, hTN, hhw⟩ := GlobalTheory.DegKeep.joint_lift (ι := Unit) (fun _ => act) (fun _ => hKL) (fun _ v => hwt v)
    (fun w w' hne => absurd (Subsingleton.elim w w') hne) W N (fun _ => sW) (fun _ => hN) (fun _ => μ) v ⟨hv, hvU'⟩
    (fun _ c => h1 c) (fun _ c d hcd => h2 c d hcd)
  exact ⟨T', hT'W.1, hhw (), hTN⟩

end GlobalTheory.HoweR.LiftMod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestWeightLiftModStableSubspaceStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ (μ : Ix p q → ℚ), ∀ v ∈ N', (∀ c, act (Eab c c) v - ((μ c : ℚ) : ℂ) • v ∈ N) → (∀ c d, posC c d → act (Eab c d) v ∈ N) → ∃ v' ∈ N', v' ∈ hwSub act μ ∧ v - v' ∈ N := by
  first | exact @GlobalTheory.HoweR.LiftMod.lift_mod | exact GlobalTheory.HoweR.LiftMod.lift_mod | (intros; apply GlobalTheory.HoweR.LiftMod.lift_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlaceStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

theorem _root_.GlobalTheory.T.splitPlace_thetaFunction_vacuum_conjugatePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  exact @PositivityTheory.ThKW.SplitVacuumEigenvectors.exists_vac_split
end
