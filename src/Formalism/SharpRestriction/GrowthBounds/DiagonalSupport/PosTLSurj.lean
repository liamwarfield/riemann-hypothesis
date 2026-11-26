module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SlackBoundReal
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DecompositionOfThreeParts
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PosTLSurj
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}

theorem llPos_surj (j y : ℤ) (hy : y ∈ Fr.LLset j) : ∃ l, l < (Fr.LLset j).card ∧ llPos Fr j l = y := by
  have hm : y ∈ (Fr.LLset j).sort (· ≤ ·) := (Finset.mem_sort _).mpr hy
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i, by rwa [Finset.length_sort] at hi, ?_⟩
  unfold Formalism.MainNotions.TestSideWords.llPos
  rw [List.getD_eq_getElem _ _ hi, hiy]

theorem posTL_surj (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (s : Fin n') (hs : s ∈ Fr.TT) : ∃ x : TL J nL r, posOf n' (posTL Fr x) = s := by
  have hper : Fr.fr ((Fr.J : ℤ) - 1) (r - 1) = Fr.fr (-1) (r - 1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    rw [← this]; congr 1
  set c : ℤ := Fr.fr (-1) (r - 1) + 1 with hc
  have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have b1 := Int.emod_nonneg ((s.val : ℤ) - c) hn0.ne'
  have b2 := Int.emod_lt_of_pos ((s.val : ℤ) - c) hn0
  have b3 := Int.emod_def ((s.val : ℤ) - c) n'
  have hx0 : c + ((s.val : ℤ) - c) % n' = (s.val : ℤ) + n' * (-(((s.val : ℤ) - c) / n')) := by
    rw [b3]; ring
  have hp : posOf n' (c + ((s.val : ℤ) - c) % n') = s := by
    rw [hx0, posOf_add_mul_alt, posOf_natCast_self]
  set y : ℤ := c + ((s.val : ℤ) - c) % n' with hy
  have hyT : posOf n' y ∈ Fr.TT := by rw [hp]; exact hs
  obtain ⟨j, h1, h2⟩ := mn_cover Fr L₁ N₁ hV hr y hyT
  have h3 : y ∈ nonW Fr j := by
    unfold nonW; rw [Finset.mem_filter]; exact ⟨h1, h2⟩
  have h4 := (ph_mem_nonW Fr hV hr _ _).1 h3
  have j0 : 0 ≤ j := by
    by_contra h
    have := ph_z_mono Fr hV hr (j := j) (j' := -1) (by omega)
    omega
  have j1 : j < Fr.J := by
    by_contra h
    have := ph_z_mono Fr hV hr (j := (Fr.J : ℤ) - 1) (j' := j - 1) (by omega)
    omega
  set jj : ZMod J := (j.toNat : ZMod J) with hjj
  have hseg : segZ jj = j := by
    unfold segZ
    rw [hjj, ZMod.val_natCast_of_lt (by rw [hJ]; omega)]
    omega
  rcases lt_or_ge y (Fr.fr j 0) with hlt | hge
  · have hyL : y ∈ Fr.LLset (segZ jj) := by
      rw [hseg]
      exact (mem_LLset Fr _ _).2 ⟨⟨h4.1, hlt⟩, hyT⟩
    obtain ⟨l, hl, he⟩ := llPos_surj Fr _ _ hyL
    refine ⟨⟨jj, Sum.inl ⟨l, by rw [hnL]; exact hl⟩⟩, ?_⟩
    show posOf n' (llPos Fr (segZ jj) l) = s
    rw [he]; exact hp
  · obtain ⟨i, hi, he⟩ := ge_frame Fr L₁ N₁ hV j y hyT hge (r - 1) (by omega) h4.2.1
    refine ⟨⟨jj, Sum.inr ⟨r - 1 - i, by omega⟩⟩, ?_⟩
    show posOf n' (Fr.fr (segZ jj) (r - 1 - (r - 1 - i))) = s
    have e : r - 1 - (r - 1 - i) = i := by omega
    rw [e, hseg, ← he]; exact hp

end Formalism.MainNotions.Proposition5Numerics
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickDefs
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def gamR (P rho be : ℕ) : ℚ :=
  ((rho + P * be).factorial : ℚ) / ((rho.factorial : ℚ) * (be.factorial : ℚ) * (P.factorial : ℚ) ^ be)

def diagK {Kf : Type} [Field Kf] {σ : Type} (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) : MvPolynomial σ Kf :=
  ∑ mo ∈ F.support, monomial mo (g mo * F.coeff mo)

section Dig

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def gamPl (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) : ℚ :=
  ∏ v : TL J nL r × Fin r, gamR (lowP Fr p v.1) (rho (v.1, Fin.castAdd K v.2)) (bp v)

def gamNo (rho : TL J nL r × Fin (r + K) → ℕ) (bn : TL J nL r × Fin K →₀ ℕ) : ℚ :=
  ∏ v : TL J nL r × Fin K, gamR (lowP Fr p v.1) (rho (v.1, Fin.natAdd r v.2)) (bn v)

def cstOf (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : ℕ :=
  (∏ v : TL J nL r × Fin (r + K), (rho v).factorial) * ∏ x : TL J nL r, (lowP Fr p x).factorial ^ (dPl x + dNo x)

def classOf (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r × Fin (r + K) → ℕ :=
  fun v => Fin.addCases (fun a => mo (plVar Fr hk nL v.1 a) % lowP Fr p v.1)
    (fun b => mo (noVar Fr hk nL v.1 b) % lowP Fr p v.1) v.2

def blkPl (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r → ℕ := fun x => ∑ a : Fin r, mo (plVar Fr hk nL x a) / lowP Fr p x

def blkNo (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r → ℕ := fun x => ∑ b : Fin K, mo (noVar Fr hk nL x b) / lowP Fr p x

def DigFacts (d : Fin n' → ℕ) : Prop :=
  ∀ G : MvPolynomial (TV n' (m + 1)) (KK O), HasMultideg G d →
    (∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ), (∀ x c, rho (x, c) < lowP Fr p x) →
      ∀ A ∈ Pol (KK O) r dPl, ∀ N ∈ Pol (KK O) K dNo,
        fock G (asm Fr p O hk nL rho A N) = ((cstOf Fr p nL rho dPl dNo : ℕ) : KK O) *
          ∑ bp ∈ A.support, ∑ bn ∈ N.support, ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn *
            (((gamPl Fr p nL rho bp : ℚ) : KK O) * A.coeff bp * ((expFact bp : ℕ) : KK O)) *
            (((gamNo Fr p nL rho bn : ℚ) : KK O) * N.coeff bn * ((expFact bn : ℕ) : KK O))) ∧
    (∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (bp : TL J nL r × Fin r →₀ ℕ),
      (levImg Fr p hk nL rho dPl dNo G).coeff bp ∈ Pol (KK O) K dNo) ∧
    ∀ mo ∈ G.support,
      BlockOK Fr p nL d (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) ∧
      ((levImg Fr p hk nL (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) G).coeff
        (plMon Fr p hk nL mo)).coeff (noMon Fr p hk nL mo) = G.coeff mo ∧
      (∀ x, multideg (plMon Fr p hk nL mo) x = blkPl Fr p hk nL mo x) ∧
      (∀ x, multideg (noMon Fr p hk nL mo) x = blkNo Fr p hk nL mo x) ∧
      ((expFact mo : ℕ) : ℚ) = ((cstOf Fr p nL (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo) : ℕ) : ℚ) *
        ((expFact (plMon Fr p hk nL mo) : ℕ) : ℚ) * ((expFact (noMon Fr p hk nL mo) : ℕ) : ℚ) *
        gamPl Fr p nL (classOf Fr p hk nL mo) (plMon Fr p hk nL mo) *
        gamNo Fr p nL (classOf Fr p hk nL mo) (noMon Fr p hk nL mo)

end Dig

section Parts

variable (p : ℕ) {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (Fr : Frames n' r) {J : ℕ} [NeZero J]

def DnoOf (nL : ZMod J → ℕ) (dNo : TL J nL r → ℕ) : ℕ :=
  ∑ i : Σ j : ZMod J, Fin (nL j + r + 1), N0 K * Nat.log p (2 * degIn dNo (NSet nL i.1 i.2.val) + K - 1)

def JPOK (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) : Prop :=
  IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e ∧
  (∀ F G, fock (e F) G = fock F (e G)) ∧
  (∀ F ∈ Pol (KK O) K dNo, e F ∈ Pol (KK O) K dNo ∧
    (InBB (O := O) p F → InBB (O := O) p (((p : KK O) ^ DnoOf (K := K) p Dt.nL dNo) • e F))) ∧
  ∀ F i, e F ∈ isoSub (normE p K Dt i) (ka i.1 i.2.val)

def JPAt (Dt : SignedChainData p O r J) : Prop :=
  ∀ (dNo : TL J Dt.nL r → ℕ), ∀ y ∈ Pol (KK O) K dNo,
    ∃ (ka : ZMod J → ℕ → Fin K → ℤ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      JPOK p O Dt dNo ka e ∧ vBB (O := O) p (e y) ≤ vBB (O := O) p y

def NoAt (cP : ℕ) (Dt : SignedChainData p O r J) : Prop :=
  ∀ (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) (nu : TL J Dt.nL r × Fin K →₀ ℕ),
    (∀ x c, rho (x, c) < lowP Fr p x) → JPOK p O Dt dNo ka e → (∀ x, multideg nu x = dNo x) →
    ∃ (N0 : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) (cY : KK O),
      NormTest p O cP Dt dNo ka N0 ∧
      leQ (vK p cY) ((padicValNat p (∏ x, (dNo x).factorial) : ℝ) / 2 + DnoOf (K := K) p Dt.nL dNo -
        (padicValNat p (expFact nu) : ℝ) / 2) ∧
      CoefGe p (N0 - diagK (fun bn => ((gamNo Fr p Dt.nL rho bn : ℚ) : KK O)⁻¹) (cY • e (monomial nu 1))) cP

def GaAt (nL : ZMod J → ℕ) : Prop :=
  ∀ rho : TL J nL r × Fin (r + K) → ℕ, (∀ x c, rho (x, c) < lowP Fr p x) →
    (∀ bn : TL J nL r × Fin K →₀ ℕ, gamNo Fr p nL rho bn ≠ 0 ∧ padicValRat p (gamNo Fr p nL rho bn) = 0) ∧
    (∀ bp : TL J nL r × Fin r →₀ ℕ, gamPl Fr p nL rho bp ≠ 0 ∧ padicValRat p (gamPl Fr p nL rho bp) = 0) ∧
    ∃ ga : (TL J nL r × Fin r →₀ ℕ) → O, (∀ al, IsUnit (ga al)) ∧
      (∀ al, algebraMap O (KK O) (ga al) = ((gamPl Fr p nL rho al : ℚ) : KK O)) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ ε : Bool, ∃ lam : (TL J nL r × Fin r →₀ ℕ) →₀ O,
        (∀ m ∈ lam.support, (m.sum fun _ e => e) ≤ 6 * k) ∧
        ∀ al : TL J nL r × Fin r →₀ ℕ,
          geQ (vK p ((if ε then algebraMap O (KK O) (ga al) else (algebraMap O (KK O) (ga al))⁻¹) -
            binomCombF (K := KK O) lam al)) (k : ℝ)

def SizeAt (nL : ZMod J → ℕ) (d : Fin n' → ℕ) (Dn : ℝ) : Prop :=
  ∀ (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ), BlockOK Fr p nL d rho dPl dNo →
    ∀ (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ),
      (∀ x, multideg bp x = dPl x) → (∀ x, multideg bn x = dNo x) →
      (DnoOf (K := K) p nL dNo : ℝ) +
        ((padicValNat p (∏ x, (dPl x).factorial) : ℝ) - (padicValNat p (expFact bp) : ℝ)) / 2 +
        ((padicValNat p (∏ x, (dNo x).factorial) : ℝ) - (padicValNat p (expFact bn) : ℝ)) / 2 ≤ Dn

end Parts

end Formalism.MainNotions.Proposition5Numerics
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ValLamOfSubset
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G

section Z

variable {B : Type*} [CommRing B] {σ τ : Type*}

def FinalFormK (k : ℤ) (H : MvPolynomial σ (LaurentPolynomial B)) : Prop := ∀ m, (H.coeff m).coeff k = 0

end Z

section S

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ}

theorem notMem_sDegs_iff (LL : Letters ι) (S : Set ι) (j : Fin n) (G : MvPolynomial (ι × Fin n) R) (k : ℤ) :
    k ∉ sDegs LL S j G ↔ FinalFormK k (twistSub LL S j G) := by
  unfold sDegs FinalFormK
  rw [Finset.mem_biUnion]
  constructor
  · intro h m
    by_contra hm
    apply h
    refine ⟨m, ?_, Finsupp.mem_support_iff.2 hm⟩
    rw [mem_support_iff]
    intro h0
    rw [h0] at hm
    simp at hm
  · rintro h ⟨m, _, hm⟩
    exact (Finsupp.mem_support_iff.1 hm) (h m)

theorem sDegs_subset_of {ι' : Type*} (LL : Letters ι) (S : Set ι) (LL' : Letters ι') (S' : Set ι') (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R) (F : MvPolynomial (ι' × Fin n) R)
    (h : ∀ k, FinalFormK k (twistSub LL' S' j F) → FinalFormK k (twistSub LL S j G)) : sDegs LL S j G ⊆ sDegs LL' S' j F := by
  intro k hk
  by_contra hk'
  exact ((notMem_sDegs_iff LL S j G k).2 (h k ((notMem_sDegs_iff LL' S' j F k).1 hk'))) hk

theorem val_lam_of_subset [NeZero n] {ι' : Type*} (LL : Letters ι) (S : Set ι) (LL' : Letters ι') (S' : Set ι')
    (G : MvPolynomial (ι × Fin n) R) (F : MvPolynomial (ι' × Fin n) R)
    (h : ∀ j, sDegs LL S j G ⊆ sDegs LL' S' j F) :
    valS LL' S' F ≤ valS LL S G ∧ lam1S LL S G ≤ lam1S LL' S' F :=
  ⟨Finset.inf_mono (h _), Finset.sup_mono (h _)⟩

end S

end Formalism.MainNotions.Proposition5Numerics
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Proposition5OfThreeParts
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section A

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem asm_add (rho : TL J nL r × Fin (r + K) → ℕ) (A B : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N : MvPolynomial (TL J nL r × Fin K) (KK O)) :
    asm Fr p O hk nL rho (A + B) N = asm Fr p O hk nL rho A N + asm Fr p O hk nL rho B N := by
  unfold asm
  rw [map_add (f := _)]; ring

theorem asm_coefGe (rho : TL J nL r × Fin (r + K) → ℕ) {A : MvPolynomial (TL J nL r × Fin r) (KK O)}
    {N : MvPolynomial (TL J nL r × Fin K) (KK O)} {t : ℝ} (hA : CoefGe p A t) (hN : CoefGe p N 0) :
    CoefGe p (asm Fr p O hk nL rho A N) t := by
  unfold asm
  have h1 : CoefGe p (monomial (labMon Fr hk nL rho) (1 : KK O)) 0 := CoefGe.monomial _ geQ_one
  have h2 : CoefGe p (upPl Fr p O hk nL A) t := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hA
  have h3 : CoefGe p (upNo Fr p O hk nL N) 0 := CoefGe.aeval _ (fun v => CoefGe.X_pow _ _) hN
  have h4 := CoefGe.mul (CoefGe.mul h1 h2) h3
  simpa using h4

end A

section B

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}

theorem ph_coefGe (Dt : SignedChainData p O r J) {R : MvPolynomial (ML J Dt.nL r × Fin r) (KK O)} {t : ℝ}
    (hR : CoefGe p R t) : CoefGe p (Dt.ph R) t := by
  unfold SignedChainData.ph
  refine CoefGe.aeval _ (fun v => ?_) hR
  obtain ⟨x, a⟩ := v
  cases x with
  | ll j l => simpa using CoefGe.X_pow (p := p) (O := O) _ 1
  | lab j m => simpa using CoefGe.X_pow (p := p) (O := O) _ 1
  | wc j m => exact CoefGe.X_pow _ _
  | tp j m h => simpa using CoefGe.X_pow (p := p) (O := O) _ 1

theorem ph_mem_pol (Dt : SignedChainData p O r J) (F : MvPolynomial (ML J Dt.nL r × Fin r) (KK O))
    (h : ∀ mo ∈ F.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d) : Dt.ph F ∈ Pol (KK O) r Dt.d := by
  have hF : Dt.ph F = Dt.ph (∑ mo ∈ F.support, monomial mo (F.coeff mo)) := by rw [← F.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hF, map_sum]
  refine Submodule.sum_mem _ fun mo hmo => ?_
  have : (monomial mo (F.coeff mo) : MvPolynomial (ML J Dt.nL r × Fin r) (KK O)) = F.coeff mo • monomial mo 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (h mo hmo)

end B

theorem value_core {p : ℕ} [hpF : Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) {n' r K m : ℕ} [NeZero n'] [NeZero r] (hk : m + 1 = r + K) (F : Frames n' r) {J : ℕ} [NeZero J]
    (Dt : SignedChainData p O r J) (dPl : TL J Dt.nL r → ℕ) (rho : TL J Dt.nL r × Fin (r + K) → ℕ)
    (F2 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (N0 : MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) (k0 : KK O)
    (d : Fin n' → ℕ) (cP : ℕ) (CDn CDm large₂ : ℝ) (G : MvPolynomial (TV n' (m + 1)) (KK O))
    (hdeg : HasMultideg G d) (hGint : CoefGe p G 0) (hdd : Dt.d = dPl) (hc : Dt.c = (cP : ℝ))
    (n2 : 4 * (Dt.Dm + Dt.Dl + 3 * Dt.kp) < Dt.c) (n3 : 0 ≤ Dt.kp) (n4 : Dt.Dm + Dt.Dl + 3 * Dt.kp ≤ CDm * large₂)
    (hκ : (kapFl p (m + 1) d : ℝ) ≤ CDm * large₂) (hbig : (CDn + 3 * CDm) * large₂ < (cP : ℝ)) (hN0 : CoefGe p N0 0)
    (hk0 : leQ (vK p k0) (twiceValuationFactorialProduct p d - Dt.n0 + CDn * large₂))
    (hval : ∀ A ∈ Pol (KK O) r dPl, CoefGe p A 0 →
      geQ (vK p (fock G (asm F p O hk Dt.nL rho A N0) - k0 * Dt.Bform F2 A))
        ((cP : ℝ) + twiceValuationFactorialProduct p d - (kapFl p (m + 1) d : ℕ)))
    (Gp R : MvPolynomial (ML J Dt.nL r × Fin r) (KK O)) (g1 : CoefGe p Gp 0) (g3 : CoefGe p R (Dt.c - Dt.EE 2))
    (g4 : ∀ mo ∈ Gp.support ∪ R.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d)
    (g6 : leQ (vK p (Dt.Bform F2 (Dt.ph (Gp + R)))) (Dt.EE 2 + 2 * Dt.kp + Dt.n0 - Dt.kp)) :
    ValLe (Kf := KK O) (p : O) ⌈(CDn + 2 * CDm) * large₂⌉₊
      ((p : KK O) ^ (kapFl p (m + 1) d) * fock G (asm F p O hk Dt.nL rho (Dt.ph Gp) N0) /
        (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O)) := by
  have hEE : Dt.EE 2 ≤ Dt.Dm + Dt.Dl + 3 * Dt.kp := by unfold SignedChainData.EE; linarith
  have hEE' : Dt.EE 2 = Dt.Dm + Dt.Dl + 2 * Dt.kp := rfl
  have hRpos : 0 ≤ Dt.c - Dt.EE 2 := by
    have := Dt.one_le_c
    linarith
  have hApol : Dt.ph (Gp + R) ∈ Pol (KK O) r dPl := by
    rw [← hdd]
    exact ph_mem_pol Dt _ fun mo hmo => g4 mo (MvPolynomial.support_add hmo)
  have hAint : CoefGe p (Dt.ph (Gp + R)) 0 := ph_coefGe Dt (CoefGe.add g1 (CoefGe.mono hRpos g3))
  have e1 := hval _ hApol hAint
  have e2 : geQ (vK p (fock G (asm F p O hk Dt.nL rho (Dt.ph R) N0)))
      (Dt.c - Dt.EE 2 + twiceValuationFactorialProduct p d - (kapFl p (m + 1) d : ℝ)) :=
    geQ_fock S d G _ hdeg hGint (asm_coefGe F p O hk Dt.nL rho (ph_coefGe Dt g3) hN0)
  have hmain : leQ (vK p (k0 * Dt.Bform F2 (Dt.ph (Gp + R)))) (twiceValuationFactorialProduct p d + (CDn + CDm) * large₂) := by
    refine leQ_mono ?_ (leQ_mul _ _ hk0 g6)
    rw [hEE']
    linarith
  have hsplit : fock G (asm F p O hk Dt.nL rho (Dt.ph Gp) N0) =
      k0 * Dt.Bform F2 (Dt.ph (Gp + R)) +
        ((fock G (asm F p O hk Dt.nL rho (Dt.ph (Gp + R)) N0) - k0 * Dt.Bform F2 (Dt.ph (Gp + R))) -
          fock G (asm F p O hk Dt.nL rho (Dt.ph R) N0)) := by
    rw [map_add (f := _), asm_add, fock_add_right]; ring
  have hκ0 : (0 : ℝ) ≤ (kapFl p (m + 1) d : ℝ) := Nat.cast_nonneg _
  have herr : geQ (vK p ((fock G (asm F p O hk Dt.nL rho (Dt.ph (Gp + R)) N0) - k0 * Dt.Bform F2 (Dt.ph (Gp + R))) -
          fock G (asm F p O hk Dt.nL rho (Dt.ph R) N0)))
          ((cP : ℝ) - CDm * large₂ + twiceValuationFactorialProduct p d - (kapFl p (m + 1) d : ℝ)) := by
    refine geQ_sub _ _ (geQ_mono ?_ e1) (geQ_mono ?_ e2)
    · linarith
    · rw [hc]; linarith
  have hx : leQ (vK p (fock G (asm F p O hk Dt.nL rho (Dt.ph Gp) N0))) (twiceValuationFactorialProduct p d + (CDn + CDm) * large₂) := by
    rw [hsplit]
    refine leQ_add_of_lt _ _ hmain herr ?_
    linarith
  have hD0 : (∏ s, (d s).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => Nat.factorial_ne_zero _
  have hx1 := leQ_scale hpF.out S _ (kapFl p (m + 1) d) _ hD0 hx
  have hx2 := geQ_scale hpF.out S _ (kapFl p (m + 1) d) _ hD0
    (geQ_fock S d G _ hdeg hGint (asm_coefGe F p O hk Dt.nL rho (ph_coefGe Dt g1) hN0))
  obtain ⟨o', ho'⟩ := exists_alg_of_geQ S _ (geQ_mono (by unfold twiceValuationFactorialProduct; linarith) hx2)
  rw [ho']
  apply valLe_of_vK S
  rw [← ho']
  refine leQ_mono ?_ hx1
  have h5 := Nat.le_ceil ((CDn + 2 * CDm) * large₂)
  unfold twiceValuationFactorialProduct
  linarith

theorem proposition5_at_of_three_parts (C CDn CDm CLa : ℝ) (h0n : 0 ≤ CDn) (h0m : 0 ≤ CDm) (hC : CDn + 3 * CDm ≤ 8 * C)
    (hP : PickStep C CDn CLa) (hM : MembStep C CLa) (hN : NumStep C CDm CLa) :
    Proposition5At C (CDn + 2 * CDm + 1) CLa 26 2 24 60 := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r hpF _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K
    _ _ hk hrk F nb B hD
  have S : UniformizedDVR p O := dvrOfStd hD.1
  obtain ⟨hLg, hκ, hNum⟩ := hN p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk F nb B hD
  obtain ⟨_, _, _, _, _, _, _, _, _, hDp, hcS, _⟩ := hD.2.1
  have hcPge : 8 * C * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) <
      ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) := by
    have h1 : (cStar : ℝ) ≤ ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) := by
      have : cStar ≤ cPrime n' r TT.card c0 cpp cStar := by unfold cPrime; omega
      exact_mod_cast this
    have h2 : (8 : ℝ) * ((Dp : ℝ) + 1) ≤ (cStar : ℝ) := by exact_mod_cast hcS
    have h3 : C * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) ≤ (Dp : ℝ) := by
      calc C * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)
          = C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by ring
        _ ≤ _ := hDp
    linarith
  obtain ⟨large₂, hLgdef⟩ : ∃ large₂ : ℝ, large₂ = (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := ⟨_, rfl⟩
  rw [← hLgdef] at hLg hκ hNum hcPge
  have hnn : 0 ≤ (CDn + 2 * CDm) * large₂ := by positivity
  refine ⟨⌈(CDn + 2 * CDm) * large₂⌉₊, ?_, ?_⟩
  · have h1 := Nat.ceil_lt_add_one hnn
    have h2 : (CDn + 2 * CDm + 1) * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a = (CDn + 2 * CDm + 1) * large₂ := by
      rw [hLgdef]; ring
    rw [h2]
    linarith
  intro G _ hdeg hG0 hG1 hMem
  obtain ⟨J, hJ, Dt, dPl, dNo, ka, rho, F2, N0, k0, hT, hB, hXX, hv, hNT, hk0, hval⟩ :=
    hP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk F nb B hD G hdeg hG0 hG1 hMem
  rw [← hLgdef] at hk0
  obtain ⟨n1, n2, n3, n4⟩ := hNum J Dt dPl dNo ka rho hT hB
  refine ⟨J, hJ, Dt, F2, n1, n2, hXX, hv, ?_⟩
  intro Gp R g1 g2 g3 g4 _ g6
  obtain ⟨nq, o, sig, hs, hsum⟩ :=
    hM p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk F nb B hD J Dt dPl dNo ka rho N0
      hT hB hNT Gp g1 g2 (fun mo hmo => g4 mo (Finset.mem_union_left _ hmo))
  refine ⟨nq, o, sig, hs, ?_⟩
  rw [hsum]
  have hGint : CoefGe p G 0 := by
    intro mo
    obtain ⟨c, hc⟩ := hG0 mo
    rw [hc]
    exact geQ_alg S _
  have hbig : (CDn + 3 * CDm) * large₂ < ((cPrime n' r TT.card c0 cpp cStar : ℕ) : ℝ) := by
    have : (CDn + 3 * CDm) * large₂ ≤ 8 * C * large₂ := mul_le_mul_of_nonneg_right hC (by linarith)
    linarith
  exact value_core S hk F Dt dPl rho F2 N0 k0 (dT TT lam0) _ CDn CDm large₂ G hdeg hGint hT.1.2.2.2.1 hT.2.1 n2 n3 n4 hκ hbig
    hNT.1 hk0 hval Gp R g1 g3 g4 g6

theorem proposition5_of_three_parts (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hP : RestPick D CLa Ck Crk Cdeg)
    (hM : RestMemb D CLa Ck Crk Cdeg) (hN : RestNum D CLa Ck Crk Cdeg) : Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60 := by
  intro hA
  obtain ⟨CDn, C₁, h1, h2, hP'⟩ := hP hA
  obtain ⟨C₂, h3, hM'⟩ := hM hA
  obtain ⟨CDm, C₃, h4, h5, hN'⟩ := hN hA
  refine ⟨CDn + 2 * CDm + 1, max (max C₁ C₂) (max C₃ (CDn + 3 * CDm)), by positivity,
    lt_max_of_lt_left (lt_max_of_lt_left h2), fun C hC => ?_⟩
  have c1 : C₁ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have c2 : C₂ ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have c3 : C₃ ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have c4 : CDn + 3 * CDm ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have c5 : 0 ≤ C := le_trans h2.le c1
  exact proposition5_at_of_three_parts C CDn CDm CLa h1.le h4.le (by linarith) (hP' C c1) (hM' C c2) (hN' C c3)

end Formalism.MainNotions.Proposition5Numerics
end
end
