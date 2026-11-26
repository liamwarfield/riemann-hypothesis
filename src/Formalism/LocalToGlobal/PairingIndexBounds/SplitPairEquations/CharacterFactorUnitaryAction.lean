module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction
noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions

variable (D : D7)

def SD {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSDLat D.host.E N L

def DetMul : Prop :=
  ∀ N (L L' L'' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → SD D L → SD D L' → SD D L'' →
    TaylorLogMetric.detId D L L'' = TaylorLogMetric.detId D L L' * TaylorLogMetric.detId D L' L''

def DetSmul : Prop :=
  letI := D.host.cmStar
  ∀ N (L₀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    Even N → SD D L₀ → SD D L →
    TaylorLogMetric.detId D L₀ (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) =
      Submodule.span (𝓞 D.host.E) {(γ : Matrix (Fin N) (Fin N) D.host.E).det} * TaylorLogMetric.detId D L₀ L

def IopSelf : Prop :=
  ∀ (T : TaylorLogMetric.Tor D) (N N' : ℕ) (La' : AddSubgroup (TaylorLogMetric.VC D N N')), ∀ G ∈ TaylorLogMetric.ThSp D T La',
    TaylorLogMetric.Iop D T La' La' G = G

def SqP (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    Even N → Even N' → SD D L → SD D L₁ → SD D L' → SD D L'' →
    ∀ G ∈ TaylorLogMetric.Th D T L L',
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L₁ L') (TaylorLogMetric.La D T L₁ L'') (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L₁ L') G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L'') (TaylorLogMetric.La D T L₁ L'') (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L L'') G)

def Tr0L (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → Even N' → SD D L → SD D L₁ →
    ∀ G ∈ TaylorLogMetric.Th D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'),
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L₁ (StandardLatticesGL3.stdL D N'))
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L (StandardLatticesGL3.stdL D N')) G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L₁ (StandardLatticesGL3.stdL D N')) G

def Tr0R (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N → Even N' → SD D L' → SD D L'' →
    ∀ G ∈ TaylorLogMetric.Th D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'),
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L'')
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L') G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L'') G

def PullIop (T : TaylorLogMetric.Tor D) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E),
    Even N → Even N' → SD D L → SD D L₁ → SD D L' → SD D L₁' →
    ∀ G ∈ TaylorLogMetric.Th D T L L',
      TaylorLogMetric.pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G ∈
                      TaylorLogMetric.Th D T (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
                        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') ∧
      TaylorLogMetric.pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L₁ L₁') G) =
        TaylorLogMetric.Iop D T
          (TaylorLogMetric.La D T (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L'))
          (TaylorLogMetric.La D T (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L₁)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L₁'))
          (TaylorLogMetric.pull D T (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G)

variable {D}
variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def J1 (B : Ker.Base D cc δ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (γ : Matrix.unitaryGroup (Fin N) D.host.E), Even N → Even N' →
    TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))

def J2 (B : Ker.Base D cc δ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (γ' : Matrix.unitaryGroup (Fin N') D.host.E), Even N → Even N' →
    TaylorLogMetric.pull D B.tor (1 : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2) •
        B.thMoved N N' (StandardLatticesGL3.stdL D N) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N'))

end Formalism.L2.PairingIndexBounds.Eq
end
end

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

theorem formV_herm' (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (Ker.formV A n N N') := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_ThSp_of' (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La' : AddSubgroup (TaylorLogMetric.VC D N N'))
    (G : TaylorLogMetric.VC D N N' → ℂ)
    (h : G ∈ Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) La') :
    G ∈ TaylorLogMetric.ThSp D T La' :=
  ⟨fun z => (h.1 z (Set.mem_univ z)).differentiableAt, fun x hx z => h.2 x hx z⟩

theorem Iop_smul' (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N'))
    (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Iop D T La₁ La₂ (fun v => c * G v) z = c * TaylorLogMetric.Iop D T La₁ La₂ G z := by
  unfold TaylorLogMetric.Iop
  have : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      TaylorLogMetric.al D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') *
        TaylorLogMetric.U D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') (fun v => c * G v) z
      = c • (TaylorLogMetric.al D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') *
        TaylorLogMetric.U D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') G z) := by
    intro q; simp only [TaylorLogMetric.U, smul_eq_mul]; ring
  simp only [this]
  rw [← smul_finsum, smul_eq_mul]; ring

def SmulSD (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    SD D L → SD D (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)

def NormOneUnitIdeal (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ z : unitary D.host.E, TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)})

section Paths

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Ker.Base D cc δ)

theorem admissible_of_integral_conj_le {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hN : Even N) (hN' : Even N') (h : SD D L) (h' : SD D L') :
    TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', h, h'⟩

theorem sd0 (N : ℕ) : SD D (StandardLatticesGL3.stdL D N) := Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N

theorem mvTh (hL : B.LatAll) {N N' : ℕ} {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h1 : TaylorLogMetric.admitted D N N' L₁ L₁') (h2 : TaylorLogMetric.admitted D N N' L₂ L₂')
    {G : TaylorLogMetric.VC D N N' → ℂ}
    (hG : G ∈ Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L₁ L₁')) :
    TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') G ∈
      Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor L₂ L₂') :=
  Formalism.L2.Th1.H.interTh _ _ (formV_herm' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') _ _ _
    (hL.1 N N' L₂ L₂' h2).2 (hL.2 N N' _ _ _ _ h1 h2).1 _ hG

variable {B}

theorem S1 (hSq : SqP D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N')
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {X : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hLs : SD D L) (hX : SD D X) :
    B.thMoved N N' L X = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) X) (TaylorLogMetric.La D B.tor L X)
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) X)
        (B.thZero N N')) :=
  hSq N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') X hN hN' (sd0 N) hLs (sd0 N') hX (B.thZero N N')
    (mem_ThSp_of' _ _ _ _ h0)

theorem e1path (hSq : SqP D B.tor) (hR : Tr0R D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D L) (h1 : SD D L') (h2 : SD D L'') :
    B.thMoved N N' L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved N N' L L') := by
  have hΦ := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) h1) h0
  rw [S1 hSq hL hN hN' h0 hLs h2, S1 hSq hL hN hN' h0 hLs h1,
    hSq N N' (StandardLatticesGL3.stdL D N) L L' L'' hN hN' (sd0 N) hLs h1 h2 _ (mem_ThSp_of' _ _ _ _ hΦ),
    hR N N' L' L'' hN hN' h1 h2 _ (mem_ThSp_of' _ _ _ _ h0)]

theorem e2path (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D L) (hL1 : SD D L₁) (h1 : SD D L') :
    B.thMoved N N' L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved N N' L L') := by
  have hH := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' hLs (sd0 N')) h0
  have hs := hSq N N' L L₁ (StandardLatticesGL3.stdL D N') L' hN hN' hLs hL1 (sd0 N') h1 (B.thHalf N N' L)
    (mem_ThSp_of' _ _ _ _ hH)
  have ht : TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N'))
      (B.thHalf N N' L) = B.thHalf N N' L₁ :=
    hTL N N' L L₁ hN hN' hLs hL1 _ (mem_ThSp_of' _ _ _ _ h0)
  show TaylorLogMetric.Iop D B.tor _ _ (B.thHalf N N' L₁) = _
  rw [← ht]
  exact hs

end Paths

end Formalism.L2.PairingIndexBounds.Eq
end
end

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

theorem iopSelf (D : D7) : IopSelf D := by
  intro T N N' La' G hG
  funext z
  unfold TaylorLogMetric.Iop
  have hidx : (La'.addSubgroupOf La').index = 1 := by
    rw [AddSubgroup.addSubgroupOf_self, AddSubgroup.index_top]
  have hq : ∀ q : La' ⧸ La'.addSubgroupOf La',
      TaylorLogMetric.al D T ((Quotient.out q : La') : TaylorLogMetric.VC D N N') * TaylorLogMetric.U D T ((Quotient.out q : La') : TaylorLogMetric.VC D N N') G z
        = G z := fun q => hG.2 _ (Quotient.out q).2 z
  simp_rw [hq]
  have h0 : ∀ q : La' ⧸ La'.addSubgroupOf La', q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x => exact (QuotientAddGroup.eq_zero_iff _).mpr (by simp)
  rw [finsum_eq_single (fun _ => G z) (0 : La' ⧸ La'.addSubgroupOf La') (fun q hq => absurd (h0 q) hq), hidx]
  simp

section Chi

variable {D : D7}

theorem character_factor_change_right (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN' : Even N')
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) {L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h1 : SD D L') (h2 : SD D L'') :
    Ker.Base.chiFac χ N N' L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Ker.Base.chiFac χ N N' L L' := by
  unfold Ker.Base.chiFac
  rw [hM N' (StandardLatticesGL3.stdL D N') L' L'' hN' (sd0 N') h1 h2,
    hχ.1 _ _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' (sd0 N') h1)
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' h1 h2), mul_zpow]
  ring

theorem character_factor_change_left (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN : Even N)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h1 : SD D L) (h2 : SD D L₁) :
    Ker.Base.chiFac χ N N' L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Ker.Base.chiFac χ N N' L L' := by
  unfold Ker.Base.chiFac
  rw [hM N (StandardLatticesGL3.stdL D N) L L₁ hN (sd0 N) h1 h2,
    hχ.1 _ _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (sd0 N) h1)
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN h1 h2), mul_zpow]
  ring

theorem emb_star_unit (τ : D.what₂.Tau) (x : D.host.E) (hx : letI := D.host.cmStar; x * star x = 1) :
    (letI := D.host.cmStar; TaylorLogMetric.embT D τ (star x)) = (TaylorLogMetric.embT D τ x)⁻¹ := by
  letI := D.host.cmStar
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← map_mul, hx, map_one]

theorem character_factor_unitary_action (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hS : DetSmul D) (hU : NormOneUnitIdeal D) {N N' : ℕ}
    (hN : Even N) (hN' : Even N') :
    letI := D.host.cmStar
    ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E), SD D L → SD D L' →
    Ker.Base.chiFac χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') =
      Ker.Base.chiFac χ N N' L L' *
        ((∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) *
          (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2)) := by
  letI := D.host.cmStar
  intro L L' γ γ' h1 h2
  have u1 := Matrix.det_of_mem_unitary γ.2
  have u2 := Matrix.det_of_mem_unitary γ'.2
  have c1 : χ (Submodule.span (𝓞 D.host.E) {(γ : Matrix (Fin N) (Fin N) D.host.E).det}) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ := hχ.2 ⟨_, u1⟩
  have c2 : χ (Submodule.span (𝓞 D.host.E) {(γ' : Matrix (Fin N') (Fin N') D.host.E).det}) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det)⁻¹ := hχ.2 ⟨_, u2⟩
  have s1 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ :=
    Finset.prod_congr rfl fun τ _ => emb_star_unit τ _ (Unitary.mul_star_self_of_mem u1)
  unfold Ker.Base.chiFac
  rw [hS N (StandardLatticesGL3.stdL D N) L γ hN (sd0 N) h1, hS N' (StandardLatticesGL3.stdL D N') L' γ' hN' (sd0 N') h2,
    hχ.1 _ _ (hU ⟨_, u1⟩) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (sd0 N) h1),
    hχ.1 _ _ (hU ⟨_, u2⟩) (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' (sd0 N') h2), c1, c2, s1]
  simp only [Finset.prod_inv_distrib, mul_zpow, zpow_neg, zpow_natCast, inv_pow]
  ring_nf
  simp only [inv_inv]

end Chi

section Pull

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem pull_smul (T : TaylorLogMetric.Tor D) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D T γ γ' (c • G) = c • TaylorLogMetric.pull D T γ γ' G := rfl

theorem pull_comp {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ γ' G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ 1 (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ' G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.mul_assoc]
  rfl

end Pull

end Formalism.L2.PairingIndexBounds.Eq
