module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MemSupportSumMonomial
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LowestWeightCNonpos
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ValuationOneEqZero

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembTop
section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ExistsMapOfCoefGe
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Model

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] (K : ℕ) {J : ℕ} (nL : ZMod J → ℕ)

def mlPos : ML J nL r → ZMod J × ℤ
  | ML.ll j l => (j, llPos Fr (segZ j) l.val)
  | ML.lab j m => (j, Fr.fr (segZ j) (r - 1 - m.val))
  | ML.wc j m => (j + 1, Fr.fr (segZ (j + 1) - 1) (r - 1 - m.val))
  | ML.tp j m _ => (j, Fr.fr (segZ j) (r - 1 - m.val))

def tlPos (x : TL J nL r) : ZMod J × ℤ := (x.1, posTL Fr x)

def LSeg (J : ℕ) : Letters (ZMod J × ℤ) := ⟨fun x => decide (Even x.2)⟩

def xiPl (Go : MvPolynomial (ML J nL r × Fin r) O) : MvPolynomial ((ZMod J × ℤ) × Fin r) O :=
  rename (fun v => (mlPos Fr nL v.1, v.2)) Go

def xiNo (No : MvPolynomial (TL J nL r × Fin K) O) : MvPolynomial ((ZMod J × ℤ) × Fin K) O :=
  rename (fun v => (tlPos Fr nL v.1, v.2)) No

def PhiPl (J : ℕ) : MvPolynomial ((ZMod J × ℤ) × Fin r) O →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => X (posOf n' v.1.2, Fin.castAdd K v.2) ^ (p ^ Fr.dist (segZ v.1.1) v.1.2)

def PhiNo (J : ℕ) : MvPolynomial ((ZMod J × ℤ) × Fin K) O →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => X (posOf n' v.1.2, Fin.natAdd r v.2) ^ (p ^ Fr.dist (segZ v.1.1) v.1.2)

def labO [NeZero J] (rho : TL J nL r × Fin (r + K) → ℕ) : Fin n' × Fin (r + K) →₀ ℕ :=
  ∑ x : TL J nL r, ∑ c : Fin (r + K), Finsupp.single (posOf n' (posTL Fr x), c) (rho (x, c))

end Model

def toKK {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K) (P : RRing O n' (r + K)) :
    MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O)) (rename (castVK hk) P)

structure MFH (p : ℕ) {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (TT : Finset (Fin n')) (L₁ L₂ N₁ G' : ℕ)
    (deg d : Fin n' → ℕ) (Y : ℝ) (k cP : ℕ) : Prop where
  prime : p.Prime
  two_le_r : 2 ≤ r
  frames : FramesOK TT L₁ L₂ N₁ G' Fr
  d_top : ∀ s ∈ Fr.TT, d s = deg s
  d_off : ∀ s, s ∉ Fr.TT → d s = 0
  margin : ∀ j x : ℤ, x ∈ Fr.letters j → ¬ Fr.IsW j x → 128 * (cP : ℝ) ≤ (sl p Fr deg Y k j x : ℝ)

section At

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  (d : Fin n' → ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

def MH : Prop :=
  SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka ∧ BlockOK Fr p Dt.nL d rho dPl dNo ∧
  NormTest p O cP Dt dNo ka (MvPolynomial.map (algebraMap O (KK O)) No) ∧
  Dt.YY 24 60 (MvPolynomial.map (algebraMap O (KK O)) Go) ∧
  ∀ mo ∈ Go.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d

def Occ (δ : ZMod J × ℤ → ℕ) : Prop := ∃ mo ∈ (xiPl Fr O Dt.nL Go).support, ∀ i, multideg mo i = δ i

def DecAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ →
    ∃ (n : ℕ) (obd : ℤ → ℤ → ℝ) (xi : Fin n → ℤ → SegRing O r K) (dd : ℤ → ℤ → ℕ),
      (∀ (i : Fin n) (j : ℕ), j < Fr.J →
        xi i j ∈ XX' O r K Fr j (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ))
          (fun x => Bo p Fr deg j x / 2 - sl p Fr deg Y (r + K) j x) (obd j) ∧
        xi i j ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters j, ∑ c : Fin (r + K), mm (x, c) = dd j x}) ∧
      (∀ j : ℕ, j < Fr.J → ∀ x ∈ Fr.letters j, (Fr.IsW j x ∨ x ∈ Fr.LLset j) →
        (dd j x : ℝ) ≤ levDeg p Fr deg j x + levDeg p Fr deg j x / 100) ∧
      ∑ i, ∏ j ∈ Finset.range Fr.J, phSeg O K p Fr (j : ℤ) (xi i j) =
        PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No)

def AlgAt : Prop :=
  toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
    asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
      (MvPolynomial.map (algebraMap O (KK O)) No)

def DegAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ →
    HasMultideg (toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No)))) d ∧
    ∃ o : ℕ, ∀ mm ∈ (monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))).support,
      normDeg r mm = o

def LabAt : Prop :=
  IsLabel p Fr (labO Fr K Dt.nL rho) ∧ ∀ v ∈ (labO Fr K Dt.nL rho).support, v.1 ∈ Fr.TT

end At

theorem sum_homComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} (F : MvPolynomial (ι × Fin n) R) :
    ∑ δ ∈ F.support.image (fun mo => fun i => multideg mo i), homComp δ F = F := by
  classical
  conv_rhs => rw [F.as_sum]
  symm
  rw [← Finset.sum_fiberwise_of_maps_to (s := F.support)
    (t := F.support.image (fun mo => fun i => multideg mo i)) (g := fun mo => fun i => multideg mo i)
    (fun mo hmo => Finset.mem_image_of_mem _ hmo)]
  apply Finset.sum_congr rfl
  intro δ _
  unfold homComp
  apply Finset.sum_congr
  · ext mo
    simp only [Finset.mem_filter, funext_iff]
  · intro _ _
    rfl

private theorem mem_range_algebraMap_of_vK_nonneg {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (x : KK O) (h : geQ (vK p x) 0) : x ∈ Set.range (algebraMap O (KK O)) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) x
  have hb : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hbK : algebraMap O (KK O) (b : O) ≠ 0 :=
    fun h0 => hb ((IsFractionRing.injective O (KK O)) (h0.trans (map_zero _).symm))
  have ha : a ≠ 0 := by
    intro ha0
    apply hx
    rw [ha0, map_zero] at hab
    exact (mul_eq_zero.mp hab).resolve_right hbK
  have hord := Formalism.MainNotions.G.Joints.ordW_eq x a b ha hb hab
  have hp0 : IsDiscreteValuationRing.addVal O (p : O) ≠ 0 := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mp S.p_mem
  have hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact S.p_ne
  have hram : 0 < ramE p O := by
    unfold ramE
    rcases ENat.ne_top_iff_exists.mp hpt with ⟨k, hk⟩
    rw [← hk] at hp0 ⊢
    simp only [ENat.toNat_coe]
    exact Nat.pos_of_ne_zero (by exact_mod_cast hp0)
  have hq := h ((((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ))
    (by rw [vK, hord, WithTop.map_coe])
  have hq' : (0 : ℚ) ≤ (((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) /
      (ramE p O : ℚ) := by exact_mod_cast hq
  have hd : (0 : ℚ) < ramE p O := by exact_mod_cast hram
  have hnum : (0 : ℚ) ≤ (((Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) : ℤ) : ℚ) :=
    (div_nonneg_iff.mp hq').elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hd))
  have hle : Formalism.MainNotions.G.Joints.nv (b : O) ≤ Formalism.MainNotions.G.Joints.nv a := by
    have : (0 : ℤ) ≤ (Formalism.MainNotions.G.Joints.nv a : ℤ) - (Formalism.MainNotions.G.Joints.nv (b : O) : ℤ) := by exact_mod_cast hnum
    omega
  have hat : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact ha
  have hbt : IsDiscreteValuationRing.addVal O (b : O) ≠ ⊤ := by
    rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]; exact hb
  have hvle : IsDiscreteValuationRing.addVal O (b : O) ≤ IsDiscreteValuationRing.addVal O a := by
    rw [← ENat.coe_toNat hat, ← ENat.coe_toNat hbt]
    exact_mod_cast hle
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp hvle
  refine ⟨c, ?_⟩
  rw [hc, map_mul] at hab
  exact (mul_left_cancel₀ hbK (by rw [← hab, mul_comm])).symm

theorem exists_map_of_coefGe {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) {σ : Type} (F : MvPolynomial σ (KK O)) (h : CoefGe p F 0) :
    ∃ Fo : MvPolynomial σ O, MvPolynomial.map (algebraMap O (KK O)) Fo = F := by
  have hrange : F ∈ Set.range (MvPolynomial.map (algebraMap O (KK O))) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro x hx
    obtain ⟨mo, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hx
    exact mem_range_algebraMap_of_vK_nonneg S _ (h mo)
  obtain ⟨Fo, hFo⟩ := hrange
  exact ⟨Fo, hFo⟩

theorem support_of_map {O : Type} [CommRing O] [IsDomain O] {σ : Type} (Fo : MvPolynomial σ O) :
    (MvPolynomial.map (algebraMap O (KK O)) Fo).support = Fo.support := by
  exact MvPolynomial.support_map_of_injective _ (IsFractionRing.injective O (KK O))

theorem membAt_core (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (d : Fin n' → ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)
    (hDec : DecAt p O Fr deg Y N₁ G' cP Dt No Go) (hAlg : AlgAt p O hk Fr Dt rho No Go)
    (hDeg : DegAt p O hk Fr d Dt rho No Go) (hLab : LabAt p O Fr Dt rho) :
    ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
      (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
      ∑ q, sig q = asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
        (MvPolynomial.map (algebraMap O (KK O)) No) := by
  classical
  set S := (xiPl Fr O Dt.nL Go).support.image (fun mo => fun i => multideg mo i) with hS
  have hocc : ∀ δ ∈ S, Occ p O Fr Dt Go δ := by
    intro δ hδ
    obtain ⟨mo, hmo, rfl⟩ := Finset.mem_image.mp hδ
    exact ⟨mo, hmo, fun i => rfl⟩
  let e := S.equivFin
  let δq : Fin S.card → (ZMod J × ℤ → ℕ) := fun q => ((e.symm q : S) : ZMod J × ℤ → ℕ)
  let G : (ZMod J × ℤ → ℕ) → MvPolynomial (Fin n' × Fin (r + K)) O := fun δ =>
    monomial (labO Fr K Dt.nL rho) 1 *
      (PhiPl Fr p O K J (homComp δ (xiPl Fr O Dt.nL Go)) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))
  have hoc : ∀ q, Occ p O Fr Dt Go (δq q) := fun q => hocc _ (e.symm q).2
  choose o ho using fun q => (hDeg (δq q) (hoc q)).2
  refine ⟨S.card, o, fun q => toKK hk (G (δq q)), fun q => ⟨(hDeg (δq q) (hoc q)).1, ?_⟩, ?_⟩
  · obtain ⟨n, obd, xi, dd, h1, h2, h3⟩ := hDec (δq q) (hoc q)
    have hmon : monPh O K p Fr (labO Fr K Dt.nL rho) xi = G (δq q) := by
      simp only [monPh, G, h3]
    refine ⟨n, obd, xi, dd, labO Fr K Dt.nL rho, h1, h2, hLab.1, hLab.2, ?_, ?_⟩
    · rw [hmon]
      exact ho q
    · rw [hmon]
      rfl
  · have hAlg' : toKK hk (monomial (labO Fr K Dt.nL rho) 1 *
        (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go) * PhiNo Fr p O K J (xiNo Fr O K Dt.nL No))) =
        asm Fr p O hk Dt.nL rho (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go))
          (MvPolynomial.map (algebraMap O (KK O)) No) := hAlg
    rw [← hAlg']
    have hsum : ∑ q, toKK hk (G (δq q)) = ∑ δ ∈ S, toKK hk (G δ) := by
      rw [Equiv.sum_comp e.symm (fun x : S => toKK hk (G x)), Finset.sum_coe_sort S (fun δ => toKK hk (G δ))]
    rw [hsum]
    have e2 : ∑ δ ∈ S, toKK hk (G δ) = toKK hk (∑ δ ∈ S, G δ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [toKK, map_sum]
    rw [e2]
    congr 1
    simp only [G]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← map_sum, hS, sum_homComp]

end Formalism.MainNotions.Proposition5Numerics
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

def RestDecG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DecAt p O Fr deg Y N₁ G' cP Dt No Go

def RestAlgG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → AlgAt p O hk Fr Dt rho No Go

def RestDegG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DegAt p O hk Fr d Dt rho No Go

def RestLabG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → LabAt p O Fr Dt rho

theorem membAt_of (hDec : RestDecG) (hAlg : RestAlgG) (hDeg : RestDegG) (hLab : RestLabG)
    (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (hk : m + 1 = r + K) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ) (hM : MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP) :
    MembAt p O hk Fr deg Y N₁ G' cP d := by
  intro J _ Dt dPl dNo ka rho N0 hT hB hNT Gp g1 g2 g4
  obtain ⟨Go, rfl⟩ := exists_map_of_coefGe S Gp g1
  obtain ⟨No, rfl⟩ := exists_map_of_coefGe S N0 hNT.1
  have hMH : MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go :=
    ⟨hT, hB, hNT, g2, fun mo hmo => g4 mo (by rw [support_of_map]; exact hmo)⟩
  exact membAt_core p O hk Fr deg Y N₁ G' cP d Dt rho No Go
    (hDec p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hAlg p O S hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hDeg p O S hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)
    (hLab p O S Fr TT L₁ L₂ N₁ G' deg d Y cP hM J Dt dPl dNo ka rho No Go hMH)

theorem margin_real (r : ℕ) (c s : ℝ) (hr : 2 ≤ r) (hc : 0 ≤ c) (h : 100 * (r : ℝ) ^ 2 * c ≤ s) : 128 * c ≤ s := by
  have hr' : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have : 400 * c ≤ 100 * (r : ℝ) ^ 2 * c := by nlinarith
  linarith

theorem mfh_of : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ,
    ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (_hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    MFH p F TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) (flatDeg lam0) (dT TT lam0) Y (r + K)
      (cPrime n' r TT.card c0 cpp cStar) := by
  obtain ⟨C0, hC0, H0⟩ := Formalism.CountingSumsFrames.Top.paramsII0 1 1 le_rfl le_rfl
  refine ⟨max C0 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro C hC CLa p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r hpF _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _
    hk F nb B hD
  obtain ⟨_, H, hF, _, _, _⟩ := hD
  have hC0' : C0 ≤ C := le_trans (le_max_left _ _) hC
  have hC1 : 1 ≤ C := le_trans (le_max_right _ _) hC
  have hB := hyps_basic hC1 H
  have hnb := nb_of hC1 H
  have cg0 := counting_hypotheses_of_hyps hC0 (hyps_mono hC0 hC0' H) 0 (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨h1, h2, h3, _, h5, _, _, _, _, h10, h11, _⟩ := H
  have ha0 : 0 ≤ a := by linarith [hnb.two_le_a]
  have hfd := fun s hs => flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 s hs
  have hcPe : ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) = Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar := by
    unfold cPrime Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII
    push_cast
    ring
  rw [hk] at cg0
  have A0 := (H0 p r TT.card (orbitWindowCount r de h x) 0 1 (r + K) n' L₁ (goodG' r de h x) Y a 0 c0 cpp Dp cStar cg0
    le_rfl (by unfold Formalism.CountingSumsFrames.QII; positivity)).2.1
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  refine ⟨hpF.out, h2, hF, ?_, ?_, ?_⟩
  · intro s hs
    rw [hF.1] at hs
    unfold dT
    rw [if_pos hs]
  · intro s hs
    rw [hF.1] at hs
    unfold dT
    rw [if_neg hs]
  · intro jj xx hx hW
    have hBo := Bo_ge hF.2.1 (by omega) p (by omega) (flatDeg lam0) a
      (fun s hs => (hfd s (by rw [hF.1] at hs; exact hs)).1) jj xx hx hW
    have hE : (F.fr jj (r - 1) - F.fr (jj - 1) 0).toNat ≤ goodG' r de h x := by
      have := hF.2.2.1 jj
      omega
    have hq : a / Formalism.CountingSumsFrames.QII p (goodG' r de h x) ≤ Bo p F (flatDeg lam0) jj xx := by
      refine le_trans ?_ hBo
      apply div_le_div_of_nonneg_left ha0 (by positivity)
      exact pow_le_pow_right₀ hp1 hE
    have q := (A0 _ hq).1
    have n1 : 0 ≤ 24 * (((orbitWindowCount r de h x : ℕ) : ℝ) + r) * c0 := by positivity
    have n2 : 0 ≤ Formalism.CountingSumsFrames.mStarII (orbitWindowCount r de h x) (r + K) (Formalism.CountingSumsFrames.QII p (goodG' r de h x))
        (Formalism.CountingSumsFrames.cPrII r TT.card n' c0 cpp cStar) 0 := by
      unfold Formalism.CountingSumsFrames.mStarII Formalism.CountingSumsFrames.cPrII Formalism.CountingSumsFrames.omII Formalism.CountingSumsFrames.QII
      positivity
    have q2 : 100 * (r : ℝ) ^ 2 * ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) ≤
        (sl p F (flatDeg lam0) Y (r + K) jj xx : ℝ) := by
      rw [hcPe]
      have e : (sl p F (flatDeg lam0) Y (r + K) jj xx : ℝ) =
          Formalism.CountingSumsFrames.slII Y (r + K) (Bo p F (flatDeg lam0) jj xx) := rfl
      rw [e]
      linarith
    exact margin_real r _ _ h2 (Nat.cast_nonneg _) q2

theorem membership_of_four_parts (hDec : RestDecG) (hAlg : RestAlgG) (hDeg : RestDegG) (hLab : RestLabG)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMemb D CLa Ck Crk Cdeg := by
  intro _
  obtain ⟨C₁, h1, h2⟩ := mfh_of
  refine ⟨C₁, h1, fun C hC => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _
    hk F nb B hD
  exact membAt_of hDec hAlg hDeg hLab p O (dvrOfStd hD.1) hk F TT L₁ L₂ _ _ _ _ Y _
    (h2 C hC CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk F nb B hD)

end Formalism.MainNotions.Proposition5Numerics
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.RestValBdG
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def SLt {J : ℕ} (j : ZMod J) (x : ℤ) : Set (ZMod J × ℤ) := {i | i.1 = j ∧ i.2 < x}

def SLe {J : ℕ} (j : ZMod J) (x : ℤ) : Set (ZMod J × ℤ) := {i | i.1 = j ∧ i.2 ≤ x}

section At

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ)
  (ka : ZMod J → ℕ → Fin K → ℤ)
  (No : MvPolynomial (TL J Dt.nL r × Fin K) O) (Go : MvPolynomial (ML J Dt.nL r × Fin r) O)

def pU (j : ZMod J) (u : ℕ) : ℤ := posU Fr (Dt.nL j) (segZ j) u

def tauU (j : ZMod J) (u : ℕ) : ℝ :=
  thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j u -
    slU Fr p deg Y (r + K) Dt.nL j u / 2 - 60 * (cP : ℝ)

def ValBd : Prop :=
  (∀ j u, u < Dt.nL j + r →
    geZ (valS (LSeg J) (SLt j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go)) (tauU p O Fr deg Y N₁ G' cP Dt ka j u)) ∧
  (∀ j u, u < Dt.nL j →
    geZ (valS (LSeg J) (SLe j (pU p O Fr Dt j u)) (xiPl Fr O Dt.nL Go)) (tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1))) ∧
  ∀ j u, u < Dt.nL j + r →
    lam1S (LSeg J) (SLt j (pU p O Fr Dt j u)) (xiNo Fr O K Dt.nL No) ≤ ((ka j u 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ) ∧
    lam1S (LSeg J) (SLe j (pU p O Fr Dt j u)) (xiNo Fr O K Dt.nL No) ≤ ((ka j (u + 1) 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ)

def dNoOf (i : ZMod J × ℤ) : ℕ := ∑ x : TL J Dt.nL r, if tlPos Fr Dt.nL x = i then dNo x else 0

def SuppOK : Prop :=
  (∀ mo ∈ (xiPl Fr O Dt.nL Go).support, ∀ v ∈ mo.support, v.1.2 ∈ Fr.letters (segZ v.1.1)) ∧
  ∀ mo ∈ (xiNo Fr O K Dt.nL No).support,
    (∀ v ∈ mo.support, v.1.2 ∈ Fr.letters (segZ v.1.1) ∧ ¬ Fr.IsW (segZ v.1.1) v.1.2) ∧
    ∀ i, multideg mo i = dNoOf p O Fr Dt dNo i

def PlOK (δ : ZMod J × ℤ → ℕ) (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) : Prop :=
  A ∈ supported O {v : ℤ × Fin r | v.1 ∈ Fr.letters (segZ j)} ∧
  (∀ mo ∈ A.support, ∀ x, multideg mo x = δ (j, x)) ∧
  (∀ u, u < Dt.nL j + r →
    ((⌈tauU p O Fr deg Y N₁ G' cP Dt ka j u⌉ : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < pU p O Fr Dt j u} A) ∧
  ∀ u, u < Dt.nL j →
    ((⌈tauU p O Fr deg Y N₁ G' cP Dt ka j (u + 1)⌉ : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ pU p O Fr Dt j u} A

def NoOK (j : ZMod J) (B : MvPolynomial (ℤ × Fin K) O) : Prop :=
  B ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) v.1} ∧
  (∀ mo ∈ B.support, ∀ x, multideg mo x = dNoOf p O Fr Dt dNo (j, x)) ∧
  ∀ u, u < Dt.nL j + r →
    lam1S LZ {y | y < pU p O Fr Dt j u} B ≤ ((ka j u 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ) ∧
    lam1S LZ {y | y ≤ pU p O Fr Dt j u} B ≤ ((ka j (u + 1) 0 + 4 * (cP : ℤ) : ℤ) : WithBot ℤ)

def XXAt : Prop :=
  ∀ (δ : ZMod J × ℤ → ℕ) (j : ZMod J) (A : MvPolynomial (ℤ × Fin r) O) (B : MvPolynomial (ℤ × Fin K) O),
    PlOK p O Fr deg Y N₁ G' cP Dt ka δ j A → NoOK p O Fr cP Dt dNo ka j B →
    plEmb O r K A * nmEmb O r K B ∈ XX' O r K Fr (segZ j) (fun _ => (mStar p Fr (r + K) N₁ (p ^ G') cP : ℤ))
      (fun x => Bo p Fr deg (segZ j) x / 2 - sl p Fr deg Y (r + K) (segZ j) x)
      (fun x => ((δ (j, x) + dNoOf p O Fr Dt dNo (j, x) : ℕ) : ℝ)) ∧
    plEmb O r K A * nmEmb O r K B ∈ restrictSupport O {mm | ∀ x ∈ Fr.letters (segZ j),
      ∑ c : Fin (r + K), mm (x, c) = δ (j, x) + dNoOf p O Fr Dt dNo (j, x)}

def DdAt : Prop :=
  ∀ δ : ZMod J × ℤ → ℕ, Occ p O Fr Dt Go δ → ∀ (j : ZMod J), ∀ x ∈ Fr.letters (segZ j),
    (Fr.IsW (segZ j) x ∨ x ∈ Fr.LLset (segZ j)) →
    ((δ (j, x) + dNoOf p O Fr Dt dNo (j, x) : ℕ) : ℝ) ≤
      levDeg p Fr deg (segZ j) x + levDeg p Fr deg (segZ j) x / 100

end At

def RestValBdG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go →
      ValBd p O Fr deg Y N₁ G' cP Dt ka No Go ∧ SuppOK p O Fr Dt dNo No Go

def RestXXG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
      SignedChainDegreeCondition p O Fr deg Y N₁ G' cP Dt dPl ka → XXAt p O Fr deg Y N₁ G' cP Dt dNo ka

def RestDdG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (_S : UniformizedDVR p O) (Fr : Frames n' r) (TT : Finset (Fin n'))
    (L₁ L₂ N₁ G' : ℕ) (deg d : Fin n' → ℕ) (Y : ℝ) (cP : ℕ), MFH p Fr TT L₁ L₂ N₁ G' deg d Y (r + K) cP →
    ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
      (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
      (Go : MvPolynomial (ML J Dt.nL r × Fin r) O),
      MH p O Fr deg Y N₁ G' cP d Dt dPl dNo ka rho No Go → DdAt p O Fr deg Dt dNo Go

end Formalism.MainNotions.Proposition5Numerics
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembLabF
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Geo

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {L₁ N₁ : ℕ}

theorem lf_fr_per (hV : Fr.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    Fr.fr (j + m * Fr.J) i = Fr.fr j i + m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show j + ((k : ℤ) + 1) * (Fr.J : ℤ) = (j + (k : ℤ) * Fr.J) + Fr.J by ring, hV.2.1, ih]
    ring
  | pred k ih =>
    have h := hV.2.1 (j + (-(k : ℤ) - 1) * Fr.J) i
    rw [show j + (-(k : ℤ) - 1) * (Fr.J : ℤ) + Fr.J = j + -(k : ℤ) * Fr.J by ring, ih] at h
    linarith

private theorem fr_mono_of_valid (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i i' : ℕ, i ≤ i' → i' < r → Fr.fr j i ≤ Fr.fr j i' := by
  intro i i' hii' hi'
  induction i' with
  | zero => rw [Nat.le_zero.mp hii']
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (hV.2.2.1 j k (by omega)).le
    · rw [le_antisymm hii' h]

private theorem fr_last_mono_in_index_of_valid (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (a : ℤ) :
    ∀ b : ℤ, a ≤ b → Fr.fr a (r - 1) ≤ Fr.fr b (r - 1) := by
  intro b hab
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := le_trans (hV.2.2.2.1 (a + n)).le
      (fr_mono_of_valid Fr hV (a + n + 1) 0 (r - 1) (Nat.zero_le _) (by omega))
    exact le_trans ih (by simpa [add_assoc] using hstep)

theorem lf_dist_eq (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j j' x y : ℤ) (hx1 : Fr.fr (j - 1) (r - 1) < x)
    (hx2 : x ≤ Fr.fr j (r - 1)) (hy1 : Fr.fr (j' - 1) (r - 1) < y) (hy2 : y ≤ Fr.fr j' (r - 1))
    (h : posOf n' y = posOf n' x) : Fr.dist j x = Fr.dist j' y := by
  have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have hv : ((y % (n' : ℤ)).toNat % n') = ((x % (n' : ℤ)).toNat % n') := congrArg Fin.val h
  have ex1 : 0 ≤ x % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ex2 : x % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have ey1 : 0 ≤ y % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ey2 : y % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have hmod : y % (n' : ℤ) = x % (n' : ℤ) := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega
  obtain ⟨k, hk⟩ : (n' : ℤ) ∣ y - x := Int.dvd_of_emod_eq_zero (Int.emod_emod_of_dvd _ (dvd_refl _) ▸ (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod))
  have hJ1 := lf_fr_per Fr hV j (r - 1) k
  have hJ2 := lf_fr_per Fr hV (j - 1) (r - 1) k
  have hjj : j' = j + k * Fr.J := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := fr_last_mono_in_index_of_valid Fr hV hr j' (j - 1 + k * Fr.J) (by linarith)
      rw [hJ2] at this
      nlinarith
    · have := fr_last_mono_in_index_of_valid Fr hV hr (j + k * Fr.J) (j' - 1) (by linarith)
      rw [hJ1] at this
      nlinarith
  unfold Frames.dist
  rw [hjj, hJ1]
  congr 1
  linarith

end Geo

section Lab

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (K : ℕ) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem labO_apply (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (y : TL J nL r) (c : Fin (r + K)) :
    labO Fr K nL rho (posOf n' (posTL Fr y), c) = rho (y, c) := by
  classical
  simp only [labO, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'
      rw [if_neg]
      intro h
      exact hc' (Prod.ext_iff.mp h).2
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro c' _
    rw [if_neg]
    intro h
    exact hx (hinj (Prod.ext_iff.mp h).1)
  · intro h; exact absurd (Finset.mem_univ y) h

theorem labO_support (rho : TL J nL r × Fin (r + K) → ℕ) (v : Fin n' × Fin (r + K))
    (hv : v ∈ (labO Fr K nL rho).support) : ∃ x : TL J nL r, v.1 = posOf n' (posTL Fr x) := by
  classical
  by_contra hne
  push_neg at hne
  apply Finsupp.mem_support_iff.mp hv
  simp only [labO, Finsupp.finsetSum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro c _
  rw [if_neg]
  intro h
  exact hne x (Prod.ext_iff.mp h).1.symm

end Lab

theorem restLabG : RestLabG := by
  intro p _ n' r K _ _ _ O _ _ _ _S Fr TT L₁ L₂ N₁ G' deg d Y cP hMFH J _ Dt dPl dNo ka rho No Go hMH
  obtain ⟨hJ, hnL, -⟩ := hMH.1.1
  have hV : Fr.Valid L₁ N₁ := hMFH.frames.2.1
  have hr : 1 ≤ r := by have := hMFH.two_le_r; omega
  have hinj := posTL_inj Fr hV hr hJ hnL
  have hB := hMH.2.1
  unfold LabAt
  refine ⟨?_, ?_⟩
  · intro j x hx hW c
    by_cases hy : ∃ y : TL J Dt.nL r, posOf n' (posTL Fr y) = posOf n' x
    · obtain ⟨y, hy⟩ := hy
      rw [← hy, labO_apply Fr K Dt.nL hinj rho y c]
      have hlt := hB.1 y c
      have hseg := posTL_seg Fr hV hr hnL y
      have hxl := (Finset.mem_filter.mp hx).1
      rw [Finset.mem_Icc] at hxl
      have hd := lf_dist_eq Fr hV hr j (segZ y.1) x (posTL Fr y) (not_le.mp hW) hxl.2 hseg.1 hseg.2.1 hy
      rw [hd]
      exact hlt
    · push_neg at hy
      have h0 : labO Fr K Dt.nL rho (posOf n' x, c) = 0 := by
        by_contra hne
        obtain ⟨y, hy'⟩ := labO_support Fr K Dt.nL rho (posOf n' x, c) (Finsupp.mem_support_iff.mpr hne)
        exact hy y hy'.symm
      rw [h0]
      exact pow_pos (Fact.out : p.Prime).pos _
  · intro v hv
    obtain ⟨y, hy⟩ := labO_support Fr K Dt.nL rho v hv
    rw [hy]
    exact (posTL_seg Fr hV hr hnL y).2.2

end Formalism.MainNotions.Proposition5Numerics
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembAlgF
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section K

variable {O : Type} [CommRing O] [IsDomain O] {n' m r K : ℕ} (hk : m + 1 = r + K)

theorem toKK_mul (P Q : RRing O n' (r + K)) : toKK hk (P * Q) = toKK hk P * toKK hk Q := by
  unfold toKK
  rw [map_mul, map_mul]

theorem toKK_add (P Q : RRing O n' (r + K)) : toKK hk (P + Q) = toKK hk P + toKK hk Q := by
  unfold toKK
  rw [map_add (f := _), map_add (f := _)]

theorem toKK_C (a : O) : toKK hk (C a : RRing O n' (r + K)) = C (algebraMap O (KK O) a) := by
  simp [toKK]

theorem toKK_X_pow (v : Fin n' × Fin (r + K)) (n : ℕ) :
    toKK hk ((X v : RRing O n' (r + K)) ^ n) = (X (v.1, Fin.cast hk.symm v.2)) ^ n := by
  simp only [toKK, map_pow, rename_X, map_X]
  rfl

end K

section Shift

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J]

theorem seg_shift' (hV : Fr.Valid L₁ N₁) (hJ : J = Fr.J) (j : ZMod J) :
    ∃ s : ℤ, (s = 0 ∨ s = n') ∧
      ∀ i, Fr.fr (segZ j + 1) i = Fr.fr (segZ (j + 1)) i + s ∧ Fr.fr (segZ j) i = Fr.fr (segZ (j + 1) - 1) i + s := by
  have hv : (j + 1).val = (j.val + 1) % J := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  have hlt := ZMod.val_lt j
  rcases Nat.lt_or_ge (j.val + 1) J with h | h
  · refine ⟨0, Or.inl rfl, fun i => ?_⟩
    have e : segZ (j + 1) = segZ j + 1 := by
      unfold segZ
      rw [hv, Nat.mod_eq_of_lt h]
      push_cast; ring
    rw [e]
    simp
  · have hJe : j.val + 1 = J := by omega
    refine ⟨n', Or.inr rfl, fun i => ?_⟩
    have e : segZ (j + 1) = 0 := by
      unfold segZ
      rw [hv, hJe, Nat.mod_self]
      rfl
    have e2 : segZ j + 1 = 0 + (Fr.J : ℤ) := by
      unfold segZ
      rw [← hJ]
      omega
    have e3 : segZ j = -1 + (Fr.J : ℤ) := by omega
    rw [e, e2, e3]
    exact ⟨hV.2.1 0 i, by simpa using hV.2.1 (-1) i⟩

theorem wc_geom (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (j : ZMod J) (i : ℕ) (hi : i < r) :
    posOf n' (Fr.fr (segZ (j + 1) - 1) i) = posOf n' (Fr.fr (segZ j) i) ∧
    Fr.dist (segZ (j + 1)) (Fr.fr (segZ (j + 1) - 1) i) =
      Fr.dist (segZ j) (Fr.fr (segZ j) i) + (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat := by
  obtain ⟨s, hs, h⟩ := seg_shift' hV hJ j
  have h1 := (h i).2
  have h2 := (h (r - 1)).1
  have h3 := ph_z_mono Fr hV hr (j := segZ j) (j' := segZ j + 1) (by omega)
  have h4 := frame_entry_le_last Fr L₁ N₁ hV (segZ j) i hi
  refine ⟨?_, ?_⟩
  · rw [h1]
    rcases hs with rfl | rfl
    · rw [add_zero]
    · exact (bf_posOf_add _).symm
  · unfold Frames.dist
    omega

end Shift

section Hom

variable (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) {L₁ N₁ : ℕ} {J : ℕ} [NeZero J]
  (Dt : SignedChainData p O r J)

theorem plane_X (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (v : ML J Dt.nL r × Fin r) :
    toKK hk (PhiPl Fr p O K J (xiPl Fr O Dt.nL (X v))) = upPl Fr p O hk Dt.nL (Dt.ph (X v)) := by
  obtain ⟨x, a⟩ := v
  unfold xiPl PhiPl
  rw [rename_X, aeval_X, toKK_X_pow]
  unfold SignedChainData.ph upPl
  rw [aeval_X]
  cases x with
  | ll j l => simp only [aeval_X]; rfl
  | lab j mm => simp only [aeval_X]; rfl
  | tp j mm h => simp only [aeval_X]; rfl
  | wc j mm =>
    simp only [map_pow, aeval_X]
    obtain ⟨g1, g2⟩ := wc_geom (Fr := Fr) hV hr hJ j (r - 1 - mm.val) (by omega)
    rw [← pow_mul]
    have e1 : (mlPos Fr Dt.nL (ML.wc j mm)) = (j + 1, Fr.fr (segZ (j + 1) - 1) (r - 1 - mm.val)) := rfl
    simp only [e1]
    rw [g1, g2, pow_add]
    unfold SignedChainData.P
    rw [hgP]
    rfl

theorem plane_hom (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (Go : MvPolynomial (ML J Dt.nL r × Fin r) O) :
    toKK hk (PhiPl Fr p O K J (xiPl Fr O Dt.nL Go)) =
      upPl Fr p O hk Dt.nL (Dt.ph (MvPolynomial.map (algebraMap O (KK O)) Go)) := by
  induction Go using MvPolynomial.induction_on with
  | C a =>
    unfold xiPl
    rw [rename_C, map_C]
    have h1 : PhiPl Fr p O K J (C a) = C a := by unfold PhiPl; rw [aeval_C]; rfl
    have h2 : Dt.ph (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold SignedChainData.ph; rw [aeval_C]; rfl
    have h3 : upPl Fr p O hk Dt.nL (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold upPl; rw [aeval_C]; rfl
    rw [h1, h2, h3, toKK_C]
  | add P Q hP hQ =>
    have e : xiPl Fr O Dt.nL (P + Q) = xiPl Fr O Dt.nL P + xiPl Fr O Dt.nL Q := by unfold xiPl; rw [map_add (f := _)]
    rw [e, map_add (f := _), toKK_add, hP, hQ, map_add (f := _), map_add (f := _), map_add (f := _)]
  | mul_X P v hP =>
    have e : xiPl Fr O Dt.nL (P * X v) = xiPl Fr O Dt.nL P * xiPl Fr O Dt.nL (X v) := by unfold xiPl; rw [map_mul]
    rw [e, map_mul, toKK_mul, hP, plane_X p O hk Fr Dt hV hr hJ hgP v, map_mul, map_mul, map_mul, map_X]

theorem normal_hom (nL : ZMod J → ℕ) (No : MvPolynomial (TL J nL r × Fin K) O) :
    toKK hk (PhiNo Fr p O K J (xiNo Fr O K nL No)) =
      upNo Fr p O hk nL (MvPolynomial.map (algebraMap O (KK O)) No) := by
  induction No using MvPolynomial.induction_on with
  | C a =>
    unfold xiNo
    rw [rename_C, map_C]
    have h1 : PhiNo Fr p O K J (C a) = C a := by unfold PhiNo; rw [aeval_C]; rfl
    have h3 : upNo Fr p O hk nL (C (algebraMap O (KK O) a)) = C (algebraMap O (KK O) a) := by
      unfold upNo; rw [aeval_C]; rfl
    rw [h1, h3, toKK_C]
  | add P Q hP hQ =>
    have e : xiNo Fr O K nL (P + Q) = xiNo Fr O K nL P + xiNo Fr O K nL Q := by unfold xiNo; rw [map_add (f := _)]
    rw [e, map_add (f := _), toKK_add, hP, hQ, map_add (f := _), map_add (f := _)]
  | mul_X P v hP =>
    have e : xiNo Fr O K nL (P * X v) = xiNo Fr O K nL P * xiNo Fr O K nL (X v) := by unfold xiNo; rw [map_mul]
    have hX : toKK hk (PhiNo Fr p O K J (xiNo Fr O K nL (X v))) = upNo Fr p O hk nL (X v) := by
      unfold xiNo PhiNo upNo
      rw [rename_X, aeval_X, toKK_X_pow, aeval_X]
      rfl
    rw [e, map_mul, toKK_mul, hP, hX, map_mul, map_mul, map_X]

theorem label_hom (nL : ZMod J → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) :
    toKK hk (monomial (labO Fr K nL rho) (1 : O)) = monomial (labMon Fr hk nL rho) 1 := by
  have h : Finsupp.mapDomain (castVK (n' := n') hk) (labO Fr K nL rho) = labMon Fr hk nL rho := by
    rw [labMon_eq, Fintype.sum_prod_type]
    unfold labO
    rw [Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finsupp.mapDomain_single]
    rfl
  unfold toKK
  rw [rename_monomial, map_monomial, map_one, h]

theorem alg_identity (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hgP : ∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat)
    (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (No : MvPolynomial (TL J Dt.nL r × Fin K) O)
    (Go : MvPolynomial (ML J Dt.nL r × Fin r) O) : AlgAt p O hk Fr Dt rho No Go := by
  unfold AlgAt asm
  rw [toKK_mul, toKK_mul, label_hom, plane_hom p O hk Fr Dt hV hr hJ hgP, normal_hom, mul_assoc]

end Hom

theorem restAlgG : RestAlgG := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr TT L₁ L₂ N₁ G' deg d Y cP hM J _ Dt dPl dNo ka rho No Go hMH
  exact alg_identity p O hk Fr Dt hM.frames.2.1 (le_trans (by norm_num) hM.two_le_r) hMH.1.1.1 hMH.1.1.2.2.2.2.1 rho No Go

end Formalism.MainNotions.Proposition5Numerics
end
end
