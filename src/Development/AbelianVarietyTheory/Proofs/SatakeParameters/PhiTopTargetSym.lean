module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwistedDualRhoO
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrame
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTrace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.OrbEmb
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainLocalDataIntegralOffLevels
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopLawSym

open GlobalTheory.DatumLaw GlobalTheory.TwU

section Res

variable {κ K : Type} [CommRing κ] [Field K]

theorem sum_pred (n : ℕ) (f : ℕ → κ) (c : ℕ → Prop) [DecidablePred c] (h : ∀ p, p < n → (c p ↔ p + 1 < n)) :
    (∑ p ∈ Finset.range n, if c p then f p else 0) = ∑ p ∈ Finset.range (n - 1), f p := by
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    have := (h p h1).1 h2
    omega
  · intro h1
    exact ⟨by omega, (h p (by omega)).2 (by omega)⟩

theorem chiSymF_val (ψ : AddChar κ K) {r k rS : ℕ} (hr : k + rS ≤ r) (M : HPsymF κ r k rS) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin r, A i.1 j.1 = (M.1 : Matrix (Fin r) (Fin r) κ) i j) :
    ((chiSymF ψ r k rS M : Kˣ) : K) =
      ψ (∑ i ∈ Finset.range (k - 1), A i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), A (k + i) (k + i + 1)) := by
  have h0 : ((chiSymF ψ r k rS M : Kˣ) : K) =
      ψ (supSum r (SPsym r k rS) ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ)) *
        ψ (offSum k rS ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ)) := rfl
  rw [h0, ← AddChar.map_add_eq_mul]
  congr 1
  unfold supSum offSum
  rw [← Finset.sum_add_distrib, ← Equiv.sum_comp (symPerm r k rS)]
  have h1 : ∀ p : Fin r, ((∑ j : Fin r, if (symPerm r k rS p).1 + 1 = j.1 ∧ j.1 < r ∧ (symPerm r k rS p).1 ∈ SPsym r k rS then
      ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) j else 0) +
      ∑ j : Fin r, if (symPerm r k rS p).1 + 1 = rS ∧ j.1 = rS + k then
      ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) j else 0) =
      if p.1 + 1 < r ∧ p.1 + 1 ≠ k then A p.1 (p.1 + 1) else 0 := fun p => by
    rw [← Finset.sum_add_distrib, ← Equiv.sum_comp (symPerm r k rS)]
    have h2 : ∀ p' : Fin r, ((if (symPerm r k rS p).1 + 1 = (symPerm r k rS p').1 ∧ (symPerm r k rS p').1 < r ∧
        (symPerm r k rS p).1 ∈ SPsym r k rS then
        ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) (symPerm r k rS p') else 0) +
        if (symPerm r k rS p).1 + 1 = rS ∧ (symPerm r k rS p').1 = rS + k then
        ((toSymOrd κ r k rS M.1 : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) (symPerm r k rS p) (symPerm r k rS p') else 0) =
        if p.1 + 1 = p'.1 then (if p.1 + 1 ≠ k then A p.1 p'.1 else 0) else 0 := fun p' => by
      rw [toSymOrd_val', ← hA, symPerm_val hr, symPerm_val hr]
      have e1 := SymLevelInv.symIdx_cases k rS p.1
      have e2 := SymLevelInv.symIdx_cases k rS p'.1
      have := p.2
      have := p'.2
      simp only [SPsym, Finset.mem_filter, Finset.mem_range]
      split_ifs <;> first | omega | simp
    rw [Finset.sum_congr rfl fun p' _ => h2 p',
      Fin.sum_univ_eq_sum_range (fun p' => if p.1 + 1 = p' then (if p.1 + 1 ≠ k then A p.1 p' else 0) else 0) r,
      Finset.sum_ite_eq]
    simp only [Finset.mem_range, ite_and]
  rw [Finset.sum_congr rfl fun p _ => h1 p,
    Fin.sum_univ_eq_sum_range (fun p => if p + 1 < r ∧ p + 1 ≠ k then A p (p + 1) else 0) r]
  obtain ⟨d, rfl⟩ : ∃ d, r = k + d := ⟨r - k, by omega⟩
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  by_cases hd : d = 0
  · subst hd
    rw [sum_pred k _ _ fun p hp => by omega]
    simp
  · rw [sum_pred k _ _ fun p hp => by omega,
      sum_pred d (fun p => A (k + p) (k + p + 1)) (fun p => k + p + 1 < k + d ∧ k + p + 1 ≠ k) fun p hp => by omega]

theorem coarse_eq {r m t i : ℕ} (ht : 0 < t) (h1 : r ≤ i) (h2 : i < r + m * t) :
    coarse r (List.replicate m t) i = (i - r) / t + 1 := by
  rw [coarse_of_le h1, blkIdx_replicate ht _ _ (by omega)]

theorem lamPar_val (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n r k rS m t : ℕ} (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (M : HPar n κ h (List.replicate m t) (HPsymF κ r k rS)) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) :
    ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ M : Kˣ) : K) = lamF ψ χ k r t m A := by
  have h0 : ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ M : Kˣ) : K) =
      ((chiSymF ψ r k rS (HPar0 h _ _ M) : Kˣ) : K) *
        ((detChar χ n r (List.replicate m t) ⟨M.1, HPar_le h _ _ M.2⟩ : Kˣ) : K) := rfl
  rw [h0, chiSymF_val ψ hr (HPar0 h _ _ M) A fun i j => hA (Fin.castLE h i) (Fin.castLE h j), detChar_apply, List.length_replicate,
    Units.coe_prod]
  unfold lamF
  congr 1
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hb := blk_le hs hn.ge
  rw [← GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t hb ?_ ⟨M.1, HPar_le h _ _ M.2⟩ A hA]
  · unfold ext0
    rw [dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · intro i hi
    by_cases hir : i < r
    · rw [coarse_of_lt hir]
      omega
    · rw [coarse_eq ht (by omega) (by omega), Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega

end Res

section Lev

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem red_entB (k₀ : ℕ) (ex : ℕ → ℕ) (g : GLint E n P) (i j : Fin n) :
    red P (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k₀ 0 n 0 n ex ex g.1.toLinearMap) i.1 j.1 =
      (redGL n P g : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j := by
  unfold red
  rw [entB_zero _ _ _ _ _ rfl, dif_pos ⟨i.2, j.2⟩]
  rfl

theorem lamY_eq (ex : ℕ → ℕ) : LocE.lamY P (qOf P) n 0 ex = stdAt E n P := by
  rw [show stdAt E n P = LocE.lamY P (qOf P) n 0 0 from stdAt_eq (c := 0)]
  ext v
  unfold LocE.lamY
  rw [LastSteps.mem_sclLat, LastSteps.mem_sclLat]
  refine forall_congr' fun l => ?_
  have hl : l.1 < n := l.2
  simp only [LocE.scE, if_pos hl]

theorem levG_of_HPar (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {r k rS m t : ℕ} (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (ex : ℕ → ℕ) (g : GLint E n P)
    (hg : redGL n P g ∈ HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate m t) (HPsymF _ r k rS)) :
    LevG P k rS r t (n + 0) (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap) := by
  obtain ⟨hB, h0⟩ := mem_HPar.1 hg
  rw [mem_btG] at hB
  obtain ⟨s1, s2, s3⟩ := (mem_HPsymF_iff hr).1 h0
  have hI : IntM P (n + 0) (n + 0) (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap) :=
    ent_int (c := 0) (g := g.1) (by rw [lamY_eq]; exact g.2)
  have e : ∀ p p' (hp : p < n) (hp' : p' < n),
      redP P (LocE.entB (N' := n + 0) (N := n + 0) (qOf P) k 0 n 0 n ex ex g.1.toLinearMap p p') =
      (redGL n P g : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) ⟨p, hp⟩ ⟨p', hp'⟩ :=
    fun p p' hp hp' => red_entB k ex g ⟨p, hp⟩ ⟨p', hp'⟩
  refine ⟨hI, fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun i p p' h1 h2 h3 => ?_⟩
  · rw [e _ _ (by omega) (by omega)]
    exact s2 ⟨p', hp'⟩
  · rw [e _ _ hp (by omega)]
    by_cases hpr : p < r
    · rcases hz with hz | hz | hz
      · omega
      · exact s1 ⟨p, hpr⟩ ⟨p', hp'⟩ hz
      · exact s3 ⟨p, hpr⟩ ⟨p', hp'⟩ hz.2 hz.1
    · refine hB _ _ ?_
      show coarse r _ p' < coarse r _ p
      rw [coarse_of_lt hp', coarse_of_le (by omega)]
      omega
  · refine intAt_div_of_redP hq (hI _ _ h2 (by omega)) ?_
    rw [e _ _ h2 (by omega)]
    refine hB _ _ ?_
    show coarse r _ p' < coarse r _ p
    by_cases hpr : p' < r
    · rw [coarse_of_lt hpr, coarse_of_le (by omega)]
      omega
    · rw [coarse_eq ht (by omega) (by omega), coarse_eq ht (by omega) (by omega), Nat.add_lt_add_iff_right]
      have a1 : (p' - r) / t < i := by rw [Nat.div_lt_iff_lt_mul ht]; omega
      have a2 : i ≤ (p - r) / t := by rw [Nat.le_div_iff_mul_le ht]; omega
      omega

variable {K : Type} [Field K]

theorem phiGS_target (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {r k rS m i t c' n' : ℕ} (hm : m = i + 1) (hn : n = r + m * t) (h : r ≤ n) (ht : 0 < t)
    (hr : k + rS ≤ r) (g : GLint E n P)
    (hg : redGL n P g ∈ HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate m t) (HPsymF _ r k rS)) (x : HomE E (n' + c') (n + 0)) :
    LocE.PhiGS (qOf P) ψ χ k rS r t m c' n' 0 n (g.1.toLinearMap ∘ₗ x) * LocE.unitV (χ i) ((LinearEquiv.det g.1 : Eˣ) : E) =
      ((lamPar h (List.replicate m t) (chiSymF ψ r k rS) χ ⟨_, hg⟩ : Kˣ) : K) * LocE.PhiGS (qOf P) ψ χ k rS r t m c' n' 0 n x := by
  have hL := levG_of_HPar hq hn h ht hr (fun i => i + 1) g hg
  rw [lamPar_val ψ χ hn h ht hr ⟨_, hg⟩ _ (red_entB k (fun i => i + 1) g),
    ← lamGvS_eq ψ χ (by omega) hL.1 (by omega) (by omega)]
  subst hm
  rw [phiGS_eq]
  refine phiM_target (c := 0) ψ χ (by omega) hr (by rw [hn, add_mul]; omega)
    (((HPar n (𝓞 E ⧸ P.asIdeal) h (List.replicate (i + 1) t) (HPsymF _ r k rS)).comap (redGL n P)).map (GLint E n P).subtype)
    ?_ ?_ ⟨g, hg, rfl⟩ x
  · rintro _ ⟨g', -, rfl⟩
    rw [lamY_eq]
    exact g'.2
  · rintro _ ⟨g', hg', rfl⟩
    exact levG_of_HPar hq hn h ht hr _ g' hg'

end Lev

theorem phiTop_target_sym : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → ∀ (hP : P ∈ Pr.vGs) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyG Ch (rPsymF Ch) ⟨P, hP⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu true m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyG Ch (rPsymF Ch) ⟨P, hP⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu true m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP j h x
  have e1 : psi0P Ch P = Ch.psi0 ⟨P, hP⟩ := dif_pos hP
  have e2 : chiP Ch P = chiAt Ch ⟨P, hP⟩ := dif_pos hP
  have ht : 0 < R.t := R.t_odd.pos
  obtain ⟨-, -, -, a4⟩ := ranks R (j := 0) (by omega)
  unfold PhiTop
  rw [if_pos hP, if_pos rfl, e1, e2]
  exact phiGS_target hq _ _ hm (rank_X'_eq R) (r_le_X' R) ht a4.le j h x

end GlobalTheory.TopLawSym

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomRhoK
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

def toKur (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) : MaximalUnramifiedExtension p := if h : x ∈ MaximalUnramifiedExtension p then ⟨x, h⟩ else 0

theorem coe_toKur {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (h : x ∈ MaximalUnramifiedExtension p) : ((toKur p x : MaximalUnramifiedExtension p) : ℂ_[p]) = x := by
  simp [toKur, h]

def rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (z : Bool × HH D) (y : D.host.E) : MaximalUnramifiedExtension p :=
  toKur p (tauEmb D lam (tauPl D z) y)

def gK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (z : Bool × HH D) (a : Fin N) (b₀ : Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ b₁ : Fin N', ∑ a₁ : Fin N, rhoK D lam z (D.host.conj (b i b₁ a₁)) * rhoK D lam z (P' (tauPl D z) b₁ b₀) *
    ((P (tauPl D z)).map (rhoK D lam z))⁻¹ a a₁

def hK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (w : Bool × HH D) (a : Fin N) (b₀ : Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ b₁ : Fin N', ∑ a₁ : Fin N, ((P' (tauPl D w)).map (rhoK D lam w))⁻¹ b₀ b₁ * rhoK D lam w (b i b₁ a₁) *
    rhoK D lam w (P (tauPl D w) a₁ a)

def fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (e : (R × Fin (nP D p / 2)) × Fin N × Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ t : ZMod (nP D p), if t.val % 2 = 0 then σ^[t.val] (om e.1.2) * g (OrbitPlaces.orbMap D p e.1.1 t) e.2.1 e.2.2 i else 0

def fOf' (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (e : (R × Fin (nP D p / 2)) × Fin N × Fin N') (i : Fin r) : MaximalUnramifiedExtension p :=
  ∑ t : ZMod (nP D p), if t.val % 2 = 0 then 0 else σ^[t.val] (oms e.1.2) * g (OrbitPlaces.orbMap D p e.1.1 t) e.2.1 e.2.2 i

theorem exists_ringHom_rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hcl : IsResidueClassZero D p ∨ IsSg D p) (z : Bool × HH D) :
    ∃ ρ : D.host.E →+* MaximalUnramifiedExtension p, ∀ y, rhoK D lam z y = ρ y ∧ ((ρ y : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D z) y := by
  have hmem : ∀ y, tauEmb D lam (tauPl D z) y ∈ MaximalUnramifiedExtension p := fun y => by
    obtain ⟨a, ha, -⟩ := exists_kur_frob_tauEmb_posPl D p lam σ hσ hcl z y
    rw [← ha]; exact a.2
  let ρ0 : D.host.E →+* ℂ_[p] := lam.comp (Formalism.L2.KerInert.IntegralOrthonormalChange.embQ D (tauPl D z))
  have h0 : ∀ y, ρ0 y = tauEmb D lam (tauPl D z) y := fun y =>
    (Formalism.L2.KerInert.IntegralOrthonormalChange.lamC_embT D lam (tauPl D z) y).symm
  refine ⟨ρ0.codRestrict (MaximalUnramifiedExtension p) (fun y => by rw [h0]; exact hmem y), fun y => ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    rw [rhoK, coe_toKur (hmem y)]
    exact (h0 y).symm
  · exact h0 y

theorem coe_rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hcl : IsResidueClassZero D p ∨ IsSg D p) (z : Bool × HH D) (y : D.host.E) :
    ((rhoK D lam z y : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D z) y := by
  obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl z
  rw [(hρ y).1, (hρ y).2]

theorem sigma_rhoK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hcl : IsResidueClassZero D p ∨ IsSg D p) (z : Bool × HH D) (y : D.host.E) :
    σ (rhoK D lam z y) = rhoK D lam (posPl D p z 1) (D.host.conj y) := by
  obtain ⟨a, ha, hsa⟩ := exists_kur_frob_tauEmb_posPl D p lam σ hσ hcl z y
  have e1 : rhoK D lam z y = a := Subtype.ext (by rw [coe_rhoK D lam σ hσ hcl, ha])
  apply Subtype.ext
  rw [e1, coe_rhoK D lam σ hσ hcl, hsa]

theorem norm_sigma_eq (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (x : MaximalUnramifiedExtension p) :
    ‖σ x‖ = ‖x‖ :=
  Formalism.L2.Th1.D.sigmaIsom (MaximalUnramifiedExtension p) p σ hσ x

end GlobalTheory.KerStd.HypCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAwayFromMovedLocalDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAwayFromMovedLocalDatum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.OmPhiInt

section Num

variable {S : Finset ℕ}

theorem intOff_pow' {z : ℂ} (h : IntOff S z) : ∀ n : ℕ, IntOff S (z ^ n)
  | 0 => by simpa using IntOff.one
  | n + 1 => by rw [pow_succ]; exact (intOff_pow' h n).mul h

theorem intOff_zpow' {z : ℂ} (h : IntOff S z) (h' : IntOff S z⁻¹) : ∀ n : ℤ, IntOff S (z ^ n)
  | (n : ℕ) => by rw [zpow_natCast]; exact intOff_pow' h n
  | Int.negSucc n => by rw [zpow_negSucc, ← inv_pow]; exact intOff_pow' h' _

theorem intOff_of_sq_nat {z : ℂ} {n : ℕ} (h : z ^ 2 = n) : IntOff S z := by
  have hz : z ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff]
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (n : ℚ), Polynomial.X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
    simp [h]
  refine ⟨hz, fun p _ lam _ => ?_⟩
  rw [lamC_of_mem lam hz]
  have h1 : (lam ⟨z, hz⟩) ^ 2 = (n : ℂ_[p]) := by
    rw [← map_pow]
    have : (⟨z, hz⟩ : TaylorLogMetric.Qbar) ^ 2 = (n : TaylorLogMetric.Qbar) := Subtype.ext (by simpa using h)
    rw [this, map_natCast]
  have h2 : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  have h3 : ‖lam ⟨z, hz⟩‖ ^ 2 ≤ 1 := by rw [← norm_pow, h1]; exact h2
  nlinarith [norm_nonneg (lam ⟨z, hz⟩)]

theorem one_lt_qOf {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : 1 < Formalism.L2.Col.qOf P := by
  unfold Formalism.L2.Col.qOf
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact P.isPrime.ne_top
  omega

theorem unitV_intOff {E K : Type} [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) {P : HeightOneSpectrum (𝓞 E)}
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    IntOff S (σ (LocE.unitV χ a)) ∧ IntOff S (σ (LocE.unitV χ a))⁻¹ := by
  unfold LocE.unitV
  split_ifs with h
  · have hp := GlobalTheory.LastSteps.char_pow χ h.unit
    have hq := one_lt_qOf P
    have e : (σ ((χ h.unit : Kˣ) : K)) ^ (Formalism.L2.Col.qOf P - 1) = 1 := by rw [← map_pow, hp, map_one]
    exact ⟨IntOff.of_pow (by omega) e, IntOff.of_pow (n := Formalism.L2.Col.qOf P - 1) (by omega) (by rw [inv_pow, e, inv_one])⟩
  · simp only [map_zero, inv_zero]
    exact ⟨IntOff.zero, IntOff.zero⟩

theorem locChar_intOff {E K : Type} [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) {P : HeightOneSpectrum (𝓞 E)}
    (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) (hc : IntOff S (σ cq)) (hc' : IntOff S (σ cq)⁻¹) :
    IntOff S (σ (LocE.locChar (Formalism.L2.Col.qOf P) cq χ a)) ∧ IntOff S (σ (LocE.locChar (Formalism.L2.Col.qOf P) cq χ a))⁻¹ := by
  unfold LocE.locChar
  rw [map_mul, map_zpow₀, mul_inv, ← zpow_neg]
  obtain ⟨h1, h2⟩ := unitV_intOff (S := S) σ χ (a / ((Formalism.L2.Col.qOf P : ℕ) : E) ^ LocE.vP P (Formalism.L2.Col.qOf P) a)
  exact ⟨(intOff_zpow' hc hc' _).mul h1, (intOff_zpow' hc hc' _).mul h2⟩

end Num

theorem intOff_omPhi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ (P : rowSG t.Pr t.sel (t.tup μ)) (hal : AutY t.X D.R i) (h : AutY t.X D.R (i + 1)), (P.1 ∈ t.Pr.vGs → hal ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) i P.1) ∧ h ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1)) → ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P hal h x)) := by
  intro D L hT Gi Gl K Y cX ex t hmu0 hval u μ hQg i hi P hal h hstab x
  have hok := (t.idx_ok μ).cst_ok
  have hS : SNum (t.O u μ).S (Formalism.L2.Col.qOf P.1) := GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P
  have hs2 : (t.seam.σ₀ ((t.cst μ).sq P)) ^ 2 = ((Formalism.L2.Col.qOf P.1 : ℕ) : ℂ) := by
    rw [← map_pow, hok.sq_sq P, map_natCast]
  have hs0 : t.seam.σ₀ ((t.cst μ).sq P) ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hs2
    have := one_lt_qOf P.1
    have h1 : ((Formalism.L2.Col.qOf P.1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    exact h1 hs2.symm
  have hsq : IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).sq P)) := intOff_of_sq_nat hs2
  have hsq' : IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).sq P))⁻¹ := by
    have e : (t.seam.σ₀ ((t.cst μ).sq P))⁻¹ = t.seam.σ₀ ((t.cst μ).sq P) * (((Formalism.L2.Col.qOf P.1 : ℕ) : ℂ))⁻¹ := by
      rw [← hs2, pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    rw [e]
    exact hsq.mul (IntOff.inv_nat hS)
  have hmu : ∀ a : t.X.E, (P.1 ∈ t.Pr.vGs → IsUnit (redP P.1 a)) →
      IntOff (t.O u μ).S (t.seam.σ₀ (Formalism.L2.Col.muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P a)) ∧
        IntOff (t.O u μ).S (t.seam.σ₀ (Formalism.L2.Col.muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P a))⁻¹ := by
    intro a ha
    unfold Formalism.L2.Col.muAt
    by_cases hP : P.1 ∈ t.Pr.vGs
    · rw [GlobalTheory.LastSteps.locChar_unit _ _ (ha hP)]
      exact unitV_intOff _ _ _
    · obtain ⟨h1, h2⟩ := GlobalTheory.KerTie.muq_intOff D L hT Gi Gl K Y cX ex t hmu0 hval u μ hQg i hi P hP
      rw [map_inv₀] at h2
      exact locChar_intOff _ _ _ _ h1 h2
  have hPhi := (GlobalTheory.PhiRootVal.phi_intOff D L hT Gi Gl K Y cX ex t u μ P.1).1 i
  have hA := hmu ((LinearEquiv.det hal : t.X.Eˣ) : t.X.E) fun hP => GlobalTheory.LastSteps.isUnit_det_of_stab (hstab hP).1
  have hB := hmu ((LinearEquiv.det h : t.X.Eˣ) : t.X.E) fun hP => GlobalTheory.LastSteps.isUnit_det_of_stab (hstab hP).2
  unfold Formalism.L2.Col.omPhi Loc.om
  rw [map_mul, map_mul, map_mul, map_mul, map_inv₀, map_zpow₀, map_zpow₀]
  exact (((hA.1.mul hB.2).mul (intOff_zpow' hsq hsq' _)).mul (intOff_zpow' hsq hsq' _)).mul (hPhi _)

end GlobalTheory.OmPhiInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAwayFromMovedLocalDatumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAwayFrom_moved_localDatum : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ (P : rowSG t.Pr t.sel (t.tup μ)) (hal : AutY t.X D.R i) (h : AutY t.X D.R (i + 1)), (P.1 ∈ t.Pr.vGs → hal ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) i P.1) ∧ h ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1)) → ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P hal h x)) := by
  first | exact @GlobalTheory.OmPhiInt.intOff_omPhi | exact GlobalTheory.OmPhiInt.intOff_omPhi | (intros; apply GlobalTheory.OmPhiInt.intOff_omPhi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProof
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProof
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.Proof.NarrowJetMoments

namespace GlobalTheory.DatumJets.HidaSetting

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem conj_notMem (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hT : Pr.T u ∈ S) (hg : ∀ i, Pr.g i ∈ S) :
    ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  have hTn : ∀ P ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun P hP =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hP
  intro P hP hP'
  rcases (mem_Sall sel mu u P).1 hP with h | h <;> rcases (mem_Sall sel mu u _).1 hP' with h' | h'
  · refine conj_piT_notMem hPr u ⟨conjPrime₂ P, h'⟩ ?_
    change cO X.E (Pr.piT u) ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP, cO_cO]
    exact decoFin_mem_of_mem_divs h
  · exact hTn _ h' (natCast_mem_conjP.2 (T_mem hPr u ⟨P, h⟩))
  · exact hTn _ h (natCast_mem_conjP.1 (T_mem hPr u ⟨conjPrime₂ P, h'⟩))
  · exact conjP_notMem_rowSG hX hPr hsel hg h h'

theorem notMem_Sall (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) (hd : l ∣ Pr.cond)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Sall sel mu u) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  rcases (mem_Sall sel mu u P).1 hP with h | h
  · intro hm
    have h0 : Pr.piT u ∈ P.asIdeal := decoFin_mem_of_mem_divs h
    have h1 : (l : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hm
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · refine notMem_rowSG hPr hsel hl hS (fun i e => ?_) h
    subst e
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)

theorem qOf_pos (P : HeightOneSpectrum (𝓞 X.E)) : 0 < Formalism.L2.Col.qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem vG_mem_rowSG {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) : P ∈ rowSG Pr sel mu := by
  classical
  exact Finset.mem_union.2 (Or.inl (mem_vGs_iff.2 ⟨i, h⟩))

theorem ne_bot_of_locP {E : Type} [Field E] [NumberField E] [StarRing E] {I : Submodule (𝓞 E) E} {P : HeightOneSpectrum (𝓞 E)}
    (h : localization₂ P.asIdeal I = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) : I ≠ ⊥ := by
  rintro rfl
  have h1 : (1 : E) ∈ localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) :=
    (mem_locP P _ _).2 ⟨1, (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top, Submodule.mem_one.2 ⟨1, by simp⟩⟩
  rw [← h] at h1
  obtain ⟨s, hs, hs'⟩ := (mem_locP P _ _).1 h1
  rw [Submodule.mem_bot, smul_eq_zero] at hs'
  rcases hs' with h | h
  · exact hs (h ▸ zero_mem _)
  · exact one_ne_zero h

theorem setting_of_unit (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (i : Fin 2) (u : Pr.Word) (hT : Pr.T u ∈ S)
    (hg : ∀ i, Pr.g i ∈ S) (cst : LocCst X (rowSG Pr sel mu)) (hcst : cst.Ok) (A : Amb X) (a b : ℕ) (hLa : A.LaHyp a b ∅)
    (hE : A.ESmooth a b) (hU : A.AAUnit (Sall sel mu u)) :
    SplitSet A a b (Sall sel mu u) (X.conjO (Pr.piG i)) (Pr.g i) ∧
      0 < cAof sel mu cst ∧ 0 < cBof sel mu cst u ∧ Pr.g i ∣ cBof sel mu cst u := by
  have hc2 : ∀ x, X.conjO (X.conjO x) = x := fun x => RingOfIntegers.ext (star_star (x : X.E))
  obtain ⟨P₀, hP₀⟩ : (Pr.vG i).Nonempty := Finset.card_pos.1 (hPr.vG_card i ▸ hX.f_pos)
  have hP₀r : P₀ ∈ rowSG Pr sel mu := vG_mem_rowSG hP₀
  have hne : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast this.symm)
  have hprod : 0 < ∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1 := Finset.prod_pos fun P _ => qOf_pos P.1
  obtain ⟨h1, h2, -, -, h5, h6⟩ := hLa
  refine ⟨⟨hX, ⟨h1, h2, conj_notMem hX hPr hsel u hT hg, hU, h5, h6⟩,
    ne_bot_of_locP (hU P₀ ((mem_Sall sel mu u P₀).2 (Or.inr hP₀r))), hE, hPr.g_prime i, ?_, ?_, fun P hP => ?_⟩,
    pow_pos hprod _, Nat.mul_pos (hPr.T_prime u).pos (pow_pos hprod _), ?_⟩
  · rw [hc2, mul_comm]
    exact hPr.piG_norm i
  · rw [hc2]
    exact (hPr.piG_cop i).symm
  · exact (mem_Sall sel mu u P).2 (Or.inr (vG_mem_rowSG (i := i) ((mem_divs hne P).2 hP)))
  · refine Dvd.dvd.mul_left (dvd_pow ?_ (Nat.one_le_iff_ne_zero.1 hcst.B_pos)) _
    have e : Formalism.L2.Col.qOf P₀ = Pr.g i := hPr.vG_norm i P₀ hP₀
    have hd := Finset.dvd_prod_of_mem (fun P : rowSG Pr sel mu => Formalism.L2.Col.qOf P.1)
      (Finset.mem_univ (⟨P₀, hP₀r⟩ : rowSG Pr sel mu))
    beta_reduce at hd
    rw [e] at hd
    exact hd

theorem typePrimeBadPrimesLevelsHypotheses_proof : GlobalTheory.DatumJets.TypePrimeBadPrimesLevelsHypotheses := by
  intro D EX sel δ B χ cD hH hsel i u mu cst hcst a b hLa hE
  obtain ⟨hcc, -, -, hX1, hPr⟩ := hH
  have hT : (recPrimes EX).T u ∈ badS D := Or.inr (Or.inl ⟨u, rfl⟩)
  have hg : ∀ j, (recPrimes EX).g j ∈ badS D := fun j => Or.inl (by fin_cases j <;> simp)
  refine setting_of_unit hX1.ok hPr hsel i u hT hg cst hcst _ a b hLa hE fun P hP => ?_
  obtain ⟨l, n, -, hlP, hl, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.asIdeal
  refine GlobalTheory.AAUnitAway.locP_AA D _ (recSeam D) _ δ B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    refine notMem_Sall hPr hsel u hl (GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.small_mem_badS D l hs) ?_ hP hlP
    exact ((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _
  · rintro rfl
    refine notMem_Sall hPr hsel u hl (Or.inl (by simp)) ?_ hP hlP
    exact (dvd_mul_left _ _).mul_right _
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.DatumJets.HidaSetting
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumJets_typePrimeBadPrimesLevelsHypotheses : GlobalTheory.DatumJets.TypePrimeBadPrimesLevelsHypotheses := by
  first | exact @GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof | exact GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof | (intros; apply GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomConjEquivMemHomAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory

theorem latSum_transport_equiv {E : Type} [Field E] [NumberField E] {H H₂ M : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] [AddCommMonoid M] (e : H ≃ₗ[𝓞 E] H₂) (A B : Submodule (𝓞 E) H)
    (A₂ B₂ : Submodule (𝓞 E) H₂) (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (hB : ∀ x, e x ∈ B₂ ↔ x ∈ B) (G : H → M) (F₂ : H₂ → M)
    (hG : ∀ x x', x - x' ∈ B → G x = G x') (hF : ∀ x, F₂ (e x) = G x) : latSum A₂ B₂ F₂ = latSum A B G := by
  have hAm : A.map (e : H →ₗ[𝓞 E] H₂) = A₂ := by
    ext y
    rw [Submodule.mem_map_equiv, ← hA, e.apply_symm_apply]
  let eA : ↥A ≃ₗ[𝓞 E] ↥A₂ := e.ofSubmodules A A₂ hAm
  have heA : ∀ x : A, ((eA x : A₂) : H₂) = e x := fun x => rfl
  have hBm : (B.comap A.subtype).map (eA : ↥A →ₗ[𝓞 E] ↥A₂) = B₂.comap A₂.subtype := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.subtype_apply, ← hB, ← heA, eA.apply_symm_apply]
  let q := Submodule.Quotient.equiv (B.comap A.subtype) (B₂.comap A₂.subtype) eA hBm
  unfold latSum
  rw [← finsum_comp_equiv q.toEquiv]
  refine finsum_congr fun z => ?_
  set r := Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z with hr
  set r₂ := Function.surjInv (Submodule.Quotient.mk_surjective (B₂.comap A₂.subtype)) (q.toEquiv z) with hr₂
  have h1 : Submodule.Quotient.mk r = z := Function.surjInv_eq _ z
  have h2 : Submodule.Quotient.mk r₂ = q z := Function.surjInv_eq _ _
  have h3 : q z = Submodule.Quotient.mk (eA r) := by
    rw [← h1]; rfl
  rw [h3, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, heA] at h2
  have h4 : (r₂ : H₂) = e (e.symm r₂) := (e.apply_symm_apply _).symm
  rw [h4, hF]
  apply hG
  rw [← hB, map_sub, ← h4]
  exact h2

noncomputable def homConjEquiv {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b ≃ₗ[𝓞 E] HomE E a b where
  toFun x := γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap
  invFun x := γ'.symm.toLinearMap ∘ₗ x ∘ₗ γ.toLinearMap
  map_add' x y := by simp [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' r x := by
    ext y i
    simp [equiv_osmul]
  left_inv x := by ext y i; simp
  right_inv x := by ext y i; simp

theorem homConjEquiv_mem_homAt {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 E))) (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    homConjEquiv γ γ' x ∈ homAt S (gmap γ N) (gmap γ' N') ↔ x ∈ homAt S N N' := by
  show (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) ∈ homAt S (gmap γ N) (gmap γ' N') ↔ _
  constructor
  · intro h P hP y hy
    have h1 := h P hP (γ y) ((mem_localization_gmap P γ N _).2 (by simpa using hy))
    have h2 := (mem_localization_gmap P γ' N' _).1 h1
    simpa using h2
  · intro h P hP y hy
    have h1 := h P hP (γ.symm y) ((mem_localization_gmap P γ N _).1 hy)
    exact (mem_localization_gmap P γ' N' _).2 (by simpa using h1)

theorem mem_divLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ divLat c A₂ ↔ x ∈ divLat c A := by
  show ((c : 𝓞 E) • e x) ∈ A₂ ↔ ((c : 𝓞 E) • x) ∈ A
  rw [← map_smul, hA]

theorem mem_mulLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ mulLat c A₂ ↔ x ∈ mulLat c A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e.symm y, (hA _).1 (by rw [e.apply_symm_apply]; exact hy), ?_⟩
    apply e.injective
    rw [← hxy]
    show e ((c : 𝓞 E) • e.symm y) = (c : 𝓞 E) • y
    rw [map_smul, e.apply_symm_apply]
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e y, (hA _).2 hy, ?_⟩
    rw [← hxy]
    show (c : 𝓞 E) • e y = e ((c : 𝓞 E) • y)
    rw [map_smul]

theorem kerOf_gmap_frames : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V') (Sa : Finset (HeightOneSpectrum (𝓞 E))) (D cA cB : ℕ) (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') (sS sT : SB → E → K), ThDist.Ok th Sa D rho rho' sS sT → ∀ (γ : UF E a) (γ' : UF E b) (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' : Frs E b SB) (κ : GLQ E a SB) (κ' : GLQ E b SB) (Ξ Ξ₂ : HomE E a b → K) (c : K), IsSdLat N → IsSdLat N' → (∀ x z, z ∈ mulLat cB (homAt Sa N N') → Ξ (x + z) = Ξ x) → (∀ x : HomE E a b, Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) * ∏ P : SB, (sS P ((LinearEquiv.det (κ P).1 : Eˣ) : E) * sT P ((LinearEquiv.det (κ' P).1 : Eˣ) : E)) = c * Ξ x) → kerOf th Sa cA cB (gmap γ.1 N) (fun P => γ.1 * (fr P * (κ P).1)) (gmap γ'.1 N') (fun P => γ'.1 * (fr' P * (κ' P).1)) Ξ₂ = c • ((rho' γ') ∘ₗ kerOf th Sa cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹)) := by
  intro E K _ _ _ _ a b SB V V' _ _ _ _ th Sa D cA cB rho rho' sS sT hok γ γ' N fr N' fr' κ κ' Ξ Ξ₂ c hN hN' hΞ hΞ₂
  have hm : ∀ (g : UF E a), rho g ∘ₗ rho g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hm' : ∀ (g : UF E b), rho' g ∘ₗ rho' g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  let φ : (V →ₗ[K] V') ≃+ (V →ₗ[K] V') :=
    { toFun := fun L => rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹
      invFun := fun L => rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ
      left_inv := fun L => by
        have h1 := hm γ⁻¹
        have h2 := hm' γ'⁻¹
        rw [inv_inv] at h1 h2
        show rho' γ'⁻¹ ∘ₗ (rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹) ∘ₗ rho γ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc, h2]; simp
      right_inv := fun L => by
        show rho' γ' ∘ₗ (rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ) ∘ₗ rho γ⁻¹ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hm, ← LinearMap.comp_assoc, hm']; simp
      map_add' := fun L L' => by simp [LinearMap.comp_add, LinearMap.add_comp] }
  have hH := homConjEquiv_mem_homAt Sa γ.1 γ'.1 N N'
  unfold kerOf
  rw [latSum_transport_equiv (homConjEquiv γ.1 γ'.1) (divLat cA (homAt Sa N N')) (mulLat cB (homAt Sa N N')) _ _
    (mem_divLat_equiv_iff _ _ _ hH cA) (mem_mulLat_equiv_iff _ _ _ hH cB)
    (fun x => c • φ (Ξ x • th N fr N' fr' cB x))]
  · show _ = c • φ _
    unfold latSum
    rw [φ.map_finsum, smul_finsum]
  · intro x x' hx
    have h1 : Ξ x = Ξ x' := by
      have := hΞ x' (x - x') hx
      rwa [add_sub_cancel] at this
    rw [h1, hok.cong N fr N' fr' cB x x' hN hN' hx]
  · intro x
    show Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) • th _ _ _ _ cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap)
      = c • (rho' γ' ∘ₗ (Ξ x • th N fr N' fr' cB x) ∘ₗ rho γ⁻¹)
    rw [hok.equiv γ γ' N (fun P => fr P * (κ P).1) N' (fun P => fr' P * (κ' P).1) cB x hN hN',
      hok.det N fr N' fr' cB x κ κ' hN hN', LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp,
      LinearMap.comp_smul, smul_smul, smul_smul, hΞ₂]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevels
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

theorem intOff_prod {S : Finset ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IntOff S (f i)) :
    IntOff S (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOff S) (fun _ _ ha hb => ha.mul hb) IntOff.one h

theorem sNum_pow {S : Finset ℕ} {a : ℕ} (h : SNum S a) (k : ℕ) : SNum S (a ^ k) :=
  ⟨pow_pos h.1 k, fun q hq hd => h.2 q hq (hq.dvd_of_dvd_pow hd)⟩

section Lin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_eval {n : ℕ} (η : Sp E n →ₗ[E] E) (c a : E) (y : Sp E n)
    (hη : ∀ i, IntAt P (c * η (Pi.single i 1))) (hy : a • y ∈ stdAt E n P) : IntAt P (a * c * η y) := by
  have hy' := mem_stdAt'.1 hy
  have e : η y = ∑ i, y i * η (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (Pi.single i (y i) : Sp E n) = y i • Pi.single i (1 : E) by
      ext j; by_cases h : j = i <;> simp [h, Pi.single_apply], map_smul, smul_eq_mul]
  rw [e, Finset.mul_sum]
  refine Finset.sum_induction _ (IntAt P) (fun _ _ ha hb => ha.add hb) intAt_zero' fun i _ => ?_
  have := (hy' i).mul (hη i)
  simp only [Pi.smul_apply, smul_eq_mul] at this
  convert this using 1
  ring

theorem smul_symm_mem {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)} {f : Sp E n ≃ₗ[E] Sp E n}
    (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) (a : E) {z : Sp E n} (hz : a • z ∈ localization₂ P.asIdeal N) :
    a • f.symm z ∈ stdAt E n P := by
  rw [← hf, map_smul, LinearEquiv.apply_symm_apply]
  exact hz

end Lin

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem repY_mem {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Yb : Set (Sp X.E n)} (hY : Yb ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Yb ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, rfl⟩ := hY
  have hq : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
  have hs : ∀ (k : ℕ) v, v ∈ localization₂ P.1.asIdeal N → ((qOf P.1 : X.E) ^ k) • v ∈ localization₂ P.1.asIdeal N := by
    intro k v hv
    have := Submodule.smul_mem _ ((qOf P.1 : 𝓞 X.E) ^ k) hv
    rwa [← algebraMap_smul X.E, map_pow, map_natCast] at this
  have key : ∀ z, z - y ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) →
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • z ∈ localization₂ P.1.asIdeal N := by
    intro z hz
    rw [mem_locLat] at hy hz
    have h1 := hy P
    have h2 := hz P
    rw [show z = y + (z - y) by abel, smul_add]
    split_ifs at h1 h2 ⊢ with hP
    · refine add_mem ?_ ?_
      · simpa using h1
      · exact hs 1 _ (by simpa using h2)
    · refine add_mem ?_ ?_
      · simpa [zpow_neg] using h1
      · have e : ((qOf P.1 : X.E) ^ cst.M) • (z - y) =
            ((qOf P.1 : X.E) ^ (cst.M + cst.M)) • (((qOf P.1 : X.E) ^ (cst.M : ℤ))⁻¹ • (z - y)) := by
          rw [smul_smul, zpow_natCast, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), mul_one]
        rw [e]
        exact hs _ _ h2
  exact key _ (Classical.epsilon_spec (p := fun z => z - y ∈ locLat (rowSG Pr sel mu) N
    (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))) ⟨y, by simp⟩)

end Yb

end GlobalTheory.CplTwoInt

namespace GlobalTheory.CplTwoInt

open GlobalTheory.GO.ChRoot (mem_stdAt' intAt_natCast intAt_one' intAt_zero' psi_root)

section Ft

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem ftY_intOff (hc : cst.Ok) (P : rowSG Pr sel mu) (hG : P.1 ∈ Pr.vGs → cst.D P = 1)
    (hQ : P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) (σ : X.K →+* ℂ) {B : Finset ℕ} (hB : SNum B (qOf P.1)) {n : ℕ}
    (η : Sp X.E n →ₗ[X.E] X.E) {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • y ∈ stdAt X.E n P.1) :
    IntOff B (σ (ftY sel mu cst P η y)) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := by simpa [epsSg] using IntAt.coe P.1 (-1 : 𝓞 X.E)
  have hpos : 0 < qOf P.1 ^ cst.D P := pow_pos (GlobalTheory.GO.ChRoot.qOf_pos P.1) _
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP] at hy ⊢
    split_ifs with hη
    · refine IntOff.of_pow hpos ?_
      rw [← map_pow, psi_root hc P _ ?_, map_one]
      rw [hG hP, pow_one]
      have h1 := intAt_eval η 1 _ y (fun i => by simpa using hη i) hy
      convert he.mul h1 using 1
      ring
    · simpa using (IntOff.zero : IntOff B 0)
  · rw [if_neg hP] at hy ⊢
    split_ifs with hη
    · rw [map_mul, map_inv₀, map_pow, map_natCast]
      refine IntOff.mul ?_ (IntOff.of_pow hpos ?_)
      · simpa [Nat.cast_pow] using IntOff.inv_nat (sNum_pow hB (cst.M * n))
      · rw [← map_pow, psi_root hc P _ ?_, map_one]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hQ hP)
        have h1 := intAt_eval η _ _ y hη hy
        have hk' : IntAt P.1 ((qOf P.1 : X.E) ^ k) := by simpa using intAt_natCast (P := P.1) (qOf P.1 ^ k)
        rw [hk]
        convert (he.mul hk').mul h1 using 1
        ring
    · simpa using (IntOff.zero : IntOff B 0)

end Ft

theorem xiCpl2_intOff (hPhi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
      (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ
      (P : HeightOneSpectrum (𝓞 t.X.E)) x,
      IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x))) :
    ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  intro D L hT Gi Gl K Y cX ex t u μ p Yb d x hY
  have hok := t.idx_ok μ
  unfold XiCpl2
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using (IntOff.one : IntOff (t.O u μ).S 1)
    · simpa using (IntOff.zero : IntOff (t.O u μ).S 0)
  · rw [map_mul]
    refine IntOff.mul (hPhi D L hT Gi Gl K Y cX ex t u μ P.1 _) ?_
    exact ftY_intOff t.sel (t.tup μ) (t.cst μ) hok.cst_ok P (hok.depthG P) (hok.depthQ P) _
      (GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P) _
      (smul_symm_mem (GlobalTheory.ColPeriod.isFrames_frsF p P) _ (repY_mem t.sel (t.tup μ) (t.cst μ) hY P))

theorem xiCpl2_intOff_tied : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) :=
  xiCpl2_intOff fun D L hT Gi Gl K Y cX ex t u μ P x => (GlobalTheory.T.chain_local_data_integral_off_levels D L hT Gi Gl K Y cX ex t u μ P).2 x

end GlobalTheory.CplTwoInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDataIntegralAwayFromLevelsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_data_integralAwayFrom_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  first | exact @GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | exact GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | (intros; apply GlobalTheory.CplTwoInt.xiCpl2_intOff_tied <;> assumption)
end
end
