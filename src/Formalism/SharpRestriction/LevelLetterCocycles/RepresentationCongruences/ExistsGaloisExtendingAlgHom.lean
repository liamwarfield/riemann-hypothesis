module

public import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Module
open Formalism.MainNotions.N.FrobeniusPowerSeries (LiftsAt InFF InLpp)

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure CoresW [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n) (CR : ℝ)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop where
  l5 : 5 ≤ PD.p
  hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)
  hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x
  inj : Function.Injective (algebraMap O LL)
  wr : Formalism.MainNotions.LiftingTheory.coreWR W CR
  H : Formalism.MainNotions.LiftingTheory.coreH W
  Tr : Formalism.MainNotions.LiftingTheory.coreTr W
  dc : Formalism.MainNotions.TruncatedSeriesCountingBounds.DcrisExactStrict PD LL
  relay : RelayCore W
  arc : ArcCore W
  arcL : ArcLCore W
  split : SplitCore W
  nn : UnivNNCore W
  univ : UnivCore PD W
  sat : SATcore W
  satP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W
  kLev : KillerLevCore W
  kMod : KillerModCore W
  r2 : R2
  P2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W
  P3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W
  P4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt
  ptEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
    ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ
  P5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W
  P9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W
  pi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u
  ext : ExtYCore PD W
  cj : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O
  c4 : Formalism.MainNotions.N.LetterConditionLocal W
  sec : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcSecMapCore W
  gl : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcGamLiftCore W
  hf : Formalism.MainNotions.N.FrobeniusPowerSeries.HorFrameCore W
  fl : Formalism.MainNotions.N.FrobeniusPowerSeries.ArcFilLowCore W
  jq : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.LiftingTheory.Sur W F →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T₂.ρ τ a → IsJumpV PD T₁.ρ τ a
  jy : ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L) (cc : G → T₂.V),
    cc ∈ latticeCocycles T₂.L → IsCrys PD T₂.ρ → IsCrys PD Y.ρ → Formalism.MainNotions.LiftingTheory.IsExtOf W ι π cc →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD Y.ρ τ a → a = 0 ∨ IsJumpV PD T₂.ρ τ a

end Core

section PPts

variable {l : ℕ} [Fact l.Prime]

theorem primitive_root_pow_l_eq_one (P : LocPrime l) : P.ζQ 1 ^ l = 1 := by
  have h := P.ζQ_succ 0
  simpa [P.ζQ_zero] using h

theorem primitive_root_mem_cyclotomic (P : LocPrime l) (K : FinExt l) : P.ζQ 1 ∈ Ks K 1 := by
  unfold Ks
  apply (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ K0 K ⊔ _)
  apply IntermediateField.subset_adjoin
  show P.ζQ 1 ^ (l ^ 1) = 1
  rw [pow_one]
  exact primitive_root_pow_l_eq_one P

def galoisEmbedding {K LL : FinExt l} (hG : Good K 1 LL) (g : GQ l) : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 where
  toFun y := ⟨g y, hG.2.2.2 (g.toAlgHom.comp (Ks K 1).val) y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' r := Subtype.ext (by simp)

theorem galoisEmbedding_coe {K LL : FinExt l} (hG : Good K 1 LL) (g : GQ l) (y : ↥(Ks K 1)) :
    ((galoisEmbedding hG g y : ↥LL.1) : Om l) = g y := rfl

theorem exists_galois_extending_algHom {F : IntermediateField ℚ_[l] (Om l)} (τ : F →ₐ[ℚ_[l]] Om l) :
    ∃ g : GQ l, ∀ x : F, g x = τ x := by
  classical
  let φ : Om l →ₐ[ℚ_[l]] Om l := τ.liftNormal (Om l)
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun x => ?_⟩
  rw [AlgEquiv.ofBijective_apply]
  have h := τ.liftNormal_commutes (Om l) x
  simpa using h

end PPts

section Record

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)

structure UsedJ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop where
  a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F
  a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F
  c4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F

theorem ptEx_at (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (hK : CaseA K LL)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] :
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
      Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hG) τ i →
      ∃ ζ : ↥LL.1, ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1 ∧ Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG i ζ τ := by
  intro i τ hτ
  classical
  have hτ' := hτ
  unfold Formalism.MainNotions.LiftingTheory.Over at hτ'
  obtain ⟨g, hg⟩ := exists_galois_extending_algHom ((LL.1).val.comp τ)
  have hz := primitive_root_mem_cyclotomic (D.loc l) K
  have h1 : ((galoisEmbedding hG g ⟨(D.loc l).ζQ 1, hz⟩ : ↥LL.1) : Om l) = g ((D.loc l).ζQ 1) :=
    galoisEmbedding_coe hG g _
  refine ⟨galoisEmbedding hG g ⟨(D.loc l).ζQ 1, hz⟩, ?_, ?_, ?_⟩
  · rw [(D.loc l).PD_p K]
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, h1, OneMemClass.coe_one]
    rw [← map_pow, primitive_root_pow_l_eq_one, map_one]
  · intro h
    apply (D.loc l).ζQ_one
    have h2 := congrArg (fun z : ↥LL.1 => (z : Om l)) h
    simp only [h1, OneMemClass.coe_one] at h2
    exact g.injective (h2.trans (map_one g).symm)
  · unfold Formalism.MainNotions.DeltaInvariantLattices.ptK Formalism.BasicNotions.LocHW.IsPt
    refine ⟨galoisEmbedding hG g, ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
    · rw [← hτ']
      apply Subtype.ext
      rw [galoisEmbedding_coe, hxy]
      exact hg (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 x)
    · exact congrArg (galoisEmbedding hG g) (Subtype.ext hy)
    · apply Subtype.ext
      rw [galoisEmbedding_coe, hxy]
      exact (hg x).symm

end Record

end Formalism.MainNotions.N.Ln17
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthFourCostBound
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_four_cost_bound (l : ℕ) (hl : 11 ≤ l) (b wm w S η : ℕ) (hb : 1 ≤ b) (B : ℝ) (s si rr σ : ℕ)
    (hs : (s : ℝ) ≤ max 1 ((w : ℝ) - B / l + 16 / 5 * Sg l (b + η + S) wm S η) + 1)
    (hsi : (w : ℝ) - B / l - η / (l : ℝ) ^ 2 - 1 ≤ si)
    (hrr : (rr : ℝ) ≤ 3 * Sg l (b + η + S) wm S η) (hσ : (σ : ℝ) ≤ 3 * Sg l (b + η + S) wm S η) :
    ((rr + 3 * σ + 1 + (s - si) : ℕ) : ℝ) ≤ 18 * Sg l (b + η + S) wm S η + 1 := by
  have h4 := max_sub_le_errorScale l hl b wm w S η hb B ((s : ℝ) - 1) (si : ℝ)
    (max_le (Nat.cast_nonneg _) hsi) (by linarith)
  obtain ⟨-, -, -, -, -, -, h1⟩ := CaseA.sg_ge l (b + η + S) wm S η hl (by omega)
  have hsub : ((s - si : ℕ) : ℝ) ≤ max 0 ((s : ℝ) - 1 - si) + 1 := by
    rcases le_total si s with h | h
    · rw [Nat.cast_sub h]
      have := le_max_right (0:ℝ) ((s : ℝ) - 1 - si)
      linarith
    · rw [Nat.sub_eq_zero_of_le h]
      have := le_max_left (0:ℝ) ((s : ℝ) - 1 - si)
      simp only [Nat.cast_zero]
      linarith
  push_cast
  linarith

theorem sigma_eq_of_thick_letter {n : ℕ} (l b w S η : ℕ) (size : ZMod n → ℕ) (hT : ∃ i, Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i) :
    Formalism.MainNotions.N.Ln17.Sg l b w S η size = Sg l (b + η + S) w S η := by
  unfold Formalism.MainNotions.N.Ln17.Sg Sg Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
  rw [if_pos hT]

namespace ArcLengthFourSecond

section EEh
variable {W : LocWach PD LL O v n}

theorem lE_eq (k : ℕ) : lE W k = algebraMap (LetA O n) W.EE (lA W ^ k) := by
  simp [lE, lA, map_pow, map_natCast]

theorem letE_mem (c : ZMod n) : (letE c : LetA O n) ∈ W.AΔ := fun δ _ => GS.γA_letE W δ c

theorem lA_mem : lA W ∈ W.AΔ := by
  exact natCast_mem _ _

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f g : W.EE} (hf : InFr W a num den f) (hg : InFr W a num den g) :
    InFr W a num den (f - g) := by
  obtain ⟨u, hu, hf⟩ := hf
  obtain ⟨u', hu', hg⟩ := hg
  refine ⟨u - u', sub_mem hu hu', ?_⟩
  rw [mul_sub, hf, hg, ← map_sub, mul_sub]

theorem inFr_lE {a : ZMod n} {num den : LetA O n} {f : W.EE} (k : ℕ) (hf : InFr W a num den f) :
    InFr W a num den (lE W k * f) := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨lA W ^ k * u, mul_mem (pow_mem lA_mem k) hu, ?_⟩
  rw [lE_eq, mul_left_comm, hf, ← map_mul]
  congr 1
  ring

theorem inFr_num_left {a : ZMod n} {n₁ n₂ den : LetA O n} {f : W.EE} (hf : InFr W a (n₁ * n₂) den f) (h₂ : n₂ ∈ W.AΔ) :
    InFr W a n₁ den f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨n₂ * u, mul_mem h₂ hu, ?_⟩
  rw [hf]
  congr 1
  ring

theorem inFr_num_right {a : ZMod n} {n₁ n₂ den : LetA O n} {f : W.EE} (hf : InFr W a (n₁ * n₂) den f) (h₁ : n₁ ∈ W.AΔ) :
    InFr W a n₂ den f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨n₁ * u, mul_mem h₁ hu, ?_⟩
  rw [hf]
  congr 1
  ring

theorem inFr_den_mul {a : ZMod n} {num d : LetA O n} (d' : LetA O n) {f : W.EE} (hf : InFr W a num d f) (hd' : d' ∈ W.AΔ) :
    InFr W a num (d' * d) f := by
  obtain ⟨u, hu, hf⟩ := hf
  refine ⟨d' * u, mul_mem hd' hu, ?_⟩
  rw [map_mul, mul_assoc, hf, ← map_mul]
  congr 1
  ring

end EEh

end ArcLengthFourSecond

theorem ArcLengthFourSecond.inFr_sat [IsDomain O] [IsDiscreteValuationRing O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hinj : Function.Injective (algebraMap O LL)) {c : ZMod n} {num den : LetA O n}
    (hnum : num ∈ PiPs W) {g : W.EE} (h1 : InFr W c 1 den g) (hK : ∃ K : ℕ, InFr W c num den (lE W K * g)) :
    InFr W c num den g := by
  obtain ⟨u₀, hu₀, e₀⟩ := h1
  obtain ⟨K, u₁, hu₁, e₁⟩ := hK
  have key : lA W ^ K * (1 * (letE c * u₀)) = num * (letE c * u₁) := by
    apply W.EE_inj
    calc algebraMap (LetA O n) W.EE (lA W ^ K * (1 * (letE c * u₀)))
        = lE W K * algebraMap (LetA O n) W.EE (letE c * 1 * u₀) := by
          rw [ArcLengthFourSecond.lE_eq, ← map_mul]; congr 1; ring
      _ = algebraMap (LetA O n) W.EE den * (lE W K * g) := by rw [← e₀]; ring
      _ = _ := by rw [e₁]; congr 1; ring
  obtain ⟨y, hy, hxy⟩ := saturation_fraction_ring W hcase hP9 hinj num 1 1 hnum (one_mem _) (one_mem _) (letE c * u₀)
    (by rw [one_mul]; exact W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hu₀)
    ⟨K, letE c * u₁, W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hu₁, key⟩
  refine ⟨letE c * y, W.AΔ.mul_mem (ArcLengthFourSecond.letE_mem c) hy, ?_⟩
  rw [e₀]
  congr 1
  have hidem : (letE c : LetA O n) * letE c = letE c := by
    unfold letE; rw [← Pi.single_mul, one_mul]
  linear_combination (letE c : LetA O n) ^ 2 * hxy - (((letE c : LetA O n) + 1) * u₀) * hidem

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end
