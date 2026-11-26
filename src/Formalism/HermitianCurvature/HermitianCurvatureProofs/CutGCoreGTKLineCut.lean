module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangularFactorMiddleRow
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.HermitianOrthogonalProjectionVector

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLineCut
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

def CapEig (P : M.Par) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)) (Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (ρ : M.Ty P) (X : Wq →L[ℂ] Wp) : Prop :=
  ∀ (Y : ℂ) (v : Wq), X (qdet (Qr.EB π' Fr) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • X v

def FibAt (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (g : Q.Mx k r) : Set (Wq →L[ℂ] Wp) :=
  {X | ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', h * g * h' = g → (π h).comp (X.comp (π' h')) = X}

end preds

def KLEig : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ Qρ : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qρ →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr →
    ∀ (ρ : M.Ty P), ∀ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      (E.comp (Qρ ρ) = E ↔ CapEig P Bs.π' Fr ρ E)

def KLAtMost : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ g : Q.Mx P.k P.r, g ∈ Q.Glev P.k P.r (Fin.last P.r) →
    Q.GGl P.k P.r z z' g ≠ 0 → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ (ρ : M.Ty P) (E Z : Wq →L[ℂ] Wp), E ∈ FibAt P.k P.r z z' π π' g → Z ∈ FibAt P.k P.r z z' π π' g →
      CapEig P π' Fr ρ E → CapEig P π' Fr ρ Z → E ≠ 0 → ∃ c : ℂ, Z = c • E

def KLExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ g : Q.Mx P.k P.r, g ∈ Q.Glev P.k P.r (Fin.last P.r) →
    Q.GGl P.k P.r z z' g ≠ 0 → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ ρ : M.Ty P, ∃ E ∈ FibAt P.k P.r z z' π π' g, CapEig P π' Fr ρ E ∧ E ≠ 0

def KLIsoAlg : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ V')
    (m : Fin n → ℂ), GlRel E → GlRel E' → Qr.Irr E → Qr.Irr E' → Qr.SDec m →
    (∀ (w : ℂ) (v : V), qdet E w v = Qr.cpol m w • v) → (∀ (w : ℂ) (v : V'), qdet E' w v = Qr.cpol m w • v) →
    ∃ A : V' →ₗ[ℂ] V, A ≠ 0 ∧ ∀ a b, A ∘ₗ E' a b = E a b ∘ₗ A

def KLLieGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → Qr.IsRepW k r z π → Qr.IsRepW k r z' π' →
    ∀ g : Q.Mx k r, g ∈ Q.Glev k r (Fin.last r) → Q.GGl k r z z' g ≠ 0 →
    ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ A : Wq →L[ℂ] Wp, (∀ (a b : Fin (k - 1)) (v : Wq), A (Qr.EB π' Fr a b v) = Qr.EB π (fun i => g *ᵥ Fr i) a b (A v)) →
      A ∈ FibAt k r z z' π π' g

def KLExistsOf : Prop := KLIsoAlg → KLLieGrp → KLExists

def GTKLineOfCut : Prop := KLEig → KLAtMost → KLExists → GTKLine

section asm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem fib_iff_fibAt {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {ζ : ℂ} {X : Wq →L[ℂ] Wp} :
    X ∈ NF.Fib k r z z' μsec π π' ζ ↔ X ∈ FibAt k r z z' π π' (NF.muZ k r μsec ζ) := by
  first
  | exact Iff.rfl
  | (simp only [NF.Fib, FibAt, Set.mem_setOf_eq, NF.Stab, Prod.forall]
     constructor
     · intro h a ha b hb hab
       exact h a b ⟨ha, hb, hab⟩
     · rintro h a b ⟨ha, hb, hab⟩
       exact h a ha b hb hab)

theorem fibAt_smul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {g : Q.Mx k r} {X : Wq →L[ℂ] Wp} (hX : X ∈ FibAt k r z z' π π' g) (c : ℂ) :
    c • X ∈ FibAt k r z z' π π' g := by
  simp only [FibAt, Set.mem_setOf_eq] at hX ⊢
  intro h hh h' hh' hg
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX h hh h' hh' hg]

theorem capEig_smul {P : M.Par} {π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)}
    {Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ} {ρ : M.Ty P} {X : Wq →L[ℂ] Wp}
    (hX : CapEig (Wp := Wp) P π' Fr ρ X) (c : ℂ) : CapEig P π' Fr ρ (c • X) := by
  unfold CapEig at hX ⊢
  intro Y v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hX Y v, smul_comm]

end asm

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  first
  | rfl
  | (simp [B.hsVec]; done)
  | (unfold B.hsVec; rw [← WithLp.toLp_smul]; rfl)

theorem hsVec_ne_zero {A : Wq →L[ℂ] Wp} (hA : A ≠ 0) : B.hsVec A ≠ 0 := by
  intro h
  apply hA
  have hi : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := by
    intro i
    have h2 := congrArg
      (fun x : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) => (WithLp.ofLp x : Fin _ → Wp) i) h
    simpa [B.hsVec] using h2
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using hi i)

end hs

theorem gTKLine_of_cut : GTKLineOfCut := by
  intro hEig hAt hEx Wp Wq _ _ _ _ _ _ P Bs X d hH Qρ hK ζ hζ ρ
  obtain ⟨hpl, hk, hcs, -, -, -, -⟩ := id hH
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hOK.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  have hg : g ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb hcs.1 hζ')
  have hGG : Q.GGl P.k P.r Bs.z Bs.z' g ≠ 0 := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' hcs.1 hζ']
    linarith
  obtain ⟨-, -, Fr, -, -, -, hFr, -⟩ := Formalism.FourierDecayAlt.P.Qx8.geom_at hOK.k_pos hz hz' hT hT' hg hGG
  obtain ⟨E0, hE0f, hE0e, hE0n⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk g hg hGG Fr hFr ρ
  set s : ℝ := ‖B.hsVec E0‖ with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact norm_ne_zero_iff.mpr (hsVec_ne_zero hE0n)
  set E : Wq →L[ℂ] Wp := ((s : ℂ)⁻¹) • E0 with hEdef
  have hEf : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := fib_iff_fibAt.mpr (fibAt_smul hE0f _)
  have hEe : CapEig P Bs.π' Fr ρ E := capEig_smul hE0e _
  have hEn : E ≠ 0 := by
    rw [hEdef]
    exact smul_ne_zero (inv_ne_zero (by exact_mod_cast hs0)) hE0n
  have hunit : inner ℂ (B.hsVec E) (B.hsVec E) = (1 : ℂ) := by
    rw [hEdef, hsVec_smul, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, ← hs]
    simp only [map_inv₀, Complex.conj_ofReal]
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
    field_simp
    rfl
  refine ⟨E, hEf, (hEig Wp Wq P Bs X d hH Qρ hK ζ hζ Fr hFr ρ E hEf).mpr hEe, hunit, fun Z hZf hZq => ?_⟩
  have hZe : CapEig P Bs.π' Fr ρ Z := (hEig Wp Wq P Bs X d hH Qρ hK ζ hζ Fr hFr ρ Z hZf).mp hZq
  obtain ⟨c, hc⟩ := hAt Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk g hg hGG Fr hFr ρ E Z
    (fib_iff_fibAt.mp hEf) (fib_iff_fibAt.mp hZf) hEe hZe hEn
  have hi : inner ℂ (B.hsVec E) (B.hsVec Z) = c := by
    rw [hc, hsVec_smul c E, inner_smul_right, hunit, mul_one]
  rw [hi]
  exact hc

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorFrame
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

namespace TLC

variable {k r : ℕ}

theorem cap_econj {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsRepW k r z π) {Bs Bs' : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs)
    (hB' : IsFrameOf k r [z] Bs') :
    (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) * (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c)) = 1 ∧
    (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c)) * (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) = 1 ∧
    EB π Bs = Econj (EB π Bs') (Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c))
      (Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b)) := by
  set P : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun c a => herm (Hpk k r) (Bs a) (Bs' c) with hP
  set Q : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun b d => herm (Hpk k r) (Bs' d) (Bs b) with hQ
  have hexp : ∀ a, Bs a = ∑ c, P c a • Bs' c := by
    intro a
    exact HermitianFormSums.complete0 hz (HermitianFormSums.hzz hT) hB' (hB.1 a) (hB.2.2 a z (by simp))
  have hQP : Q * P = 1 := by
    ext b a
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : herm (Hpk k r) (Bs a) (Bs b) = herm (Hpk k r) (∑ c, P c a • Bs' c) (Bs b) := by
      rw [← hexp a]
    rw [HermitianFormSums.herm_lsum, hB.2.1] at h1
    rw [show (if b = a then (1 : ℂ) else 0) = if a = b then 1 else 0 by simp only [eq_comm], h1]
    apply Finset.sum_congr rfl
    intro c _
    simp only [hQ, Matrix.of_apply]
    ring
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have hunit : ∀ a b, unitB (Hpk k r) Bs a b =
      ∑ x ∈ (Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin k)),
        (P x.1 a * Q b x.2) • unitB (Hpk k r) Bs' x.1 x.2 := by
    intro a b
    rw [Finset.sum_product]
    ext p q
    have h1 : Bs a p = ∑ c, P c a * Bs' c p := by
      have := congrFun (hexp a) p
      rw [Finset.sum_apply] at this
      exact this
    have h2 : herm (Hpk k r) (bvec q) (Bs b) = ∑ d, Q b d * herm (Hpk k r) (bvec q) (Bs' d) := by
      have h3 : herm (Hpk k r) (bvec q) (Bs b) = herm (Hpk k r) (bvec q) (∑ d, P d b • Bs' d) := by
        rw [← hexp b]
      rw [h3, HermitianFormSums.herm_rsum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [hP, hQ, Matrix.of_apply, Qx2.herm_star]
    simp only [Matrix.sum_apply, Matrix.smul_apply, unitB, Matrix.of_apply, smul_eq_mul]
    rw [h1, h2, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  refine ⟨hQP, hPQ, ?_⟩
  funext a b
  unfold EB Econj
  rw [hunit a b, (HermitianFormSums.ec_sum elementary_lie_elements hπ _ _ (fun x : Fin k × Fin k => unitB (Hpk k r) Bs' x.1 x.2)
    (fun x => QrD.frame_lie hB' x.1 x.2) _ (QrD.frame_lie hB' a a)).2, Finset.sum_product]
  ext v
  simp

theorem cap_vec {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} {z' : Fin (2 * r + k + 1) → ℂ}
    (hB0 : IsFrameOf k r [z'] B0) {ν : Fin k → ℂ} (hν : C6.sq2 ν = 1) :
    inWb k r (∑ j, ν j • B0 j) ∧ herm (Hpk k r) (∑ j, ν j • B0 j) z' = 0 ∧
      herm (Hpk k r) (∑ j, ν j • B0 j) (∑ j, ν j • B0 j) = 1 := by
  refine ⟨HermitianFormSums.inWb_sum _ _ _ hB0.1, ?_, ?_⟩
  · rw [HermitianFormSums.herm_lsum]
    exact Finset.sum_eq_zero fun j _ => by rw [hB0.2.2 j z' (by simp), mul_zero]
  · rw [HermitianFormSums.herm_comb hB0]
    have : ∀ a, ν a * star (ν a) = ((Complex.normSq (ν a) : ℝ) : ℂ) := fun a => Complex.mul_conj (ν a)
    simp only [this]
    rw [← Complex.ofReal_sum]
    unfold C6.sq2 at hν
    rw [hν, Complex.ofReal_one]

end TLC

open TLC in
theorem capelli_vector_frame : TL.CapVFrame := by
  intro Wq _ _ _ k r z' π' B0 Bs ν hk hz hT hπ hB0 hν hBs w v
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨he, hez, hee⟩ := cap_vec hB0 hν
  set e := ∑ j, ν j • B0 j with hedef
  have hBs1 := HermitianFormSums.frame_sub hBs
  set C : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs e with hCdef
  have hCc : ∀ a : Fin n, C a.castSucc = Bs a := fun a => by rw [hCdef, Fin.snoc_castSucc]
  have hCl : C (Fin.last n) = e := by rw [hCdef, Fin.snoc_last]
  have hBe : ∀ a, herm (Hpk (n + 1) r) (Bs a) e = 0 := fun a => hBs.2.2 a e (by simp)
  have heB : ∀ a, herm (Hpk (n + 1) r) e (Bs a) = 0 := fun a => by
    rw [← Qx2.herm_star, hBe, star_zero]
  have hC : IsFrameOf (n + 1) r [z'] C := by
    refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact he
      · rw [hCc]; exact hBs.1 a
    · refine Fin.lastCases ?_ (fun a => ?_) a
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hee, if_pos rfl]
        · rw [hCl, hCc, heB, if_neg (Fin.castSucc_lt_last b).ne']
      · refine Fin.lastCases ?_ (fun b => ?_) b
        · rw [hCl, hCc, hBe, if_neg (Fin.castSucc_lt_last a).ne]
        · rw [hCc, hCc, hBs.2.1]
          simp only [Fin.castSucc_inj]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rw [hCl]; exact hez
      · rw [hCc]; exact hBs.2.2 a v (by simp)
  obtain ⟨hQP, hPQ, hEB⟩ := cap_econj hz hT hπ hC hB0
  set P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun c a => herm (Hpk (n + 1) r) (C a) (B0 c) with hP
  set Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun b d => herm (Hpk (n + 1) r) (B0 d) (C b) with hQ
  have hcol : (fun p => P p (Fin.last n)) = ν := by
    funext p
    simp only [hP, Matrix.of_apply, hCl, hedef, HermitianFormSums.herm_lsum, hB0.2.1, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hβ : ∀ j, (star ν ᵥ* P) j = if j = Fin.last n then 1 else 0 := by
    intro j
    have h1 : (star ν ᵥ* P) j = herm (Hpk (n + 1) r) (C j) e := by
      rw [hedef, HermitianFormSums.herm_rsum]
      simp only [Matrix.vecMul, dotProduct, hP, Matrix.of_apply, Pi.star_apply]
    rw [h1, ← hCl, hC.2.1, eq_comm]
  have hGl := (frame_general_linear Wq (n + 1) r (n + 1) z' π' B0 hπ hB0).1
  have key := AnisotropicColumnSums.chat_gen (n + 1) n rfl (Module.End ℂ Wq) (EB π' B0) P Q (Fin.last n) (by simp) Fin.castSucc
    (fun a => rfl) hGl hQP hPQ w (star ν) (fun j hj => by rw [hβ j, if_neg hj])
  rw [hcol, hβ, if_pos rfl, one_smul, ← hEB, ← BorderedDeterminants.qdet_sub] at key
  have hsub : subA (EB π' C) = EB π' Bs := by
    funext a b
    simp only [subA, EB, unitB, hCc]
  rw [hsub] at key
  have hcap := (frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w v
  rw [hcap, ← key]
  rfl

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def GTCRef : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e0 ∧ KapF P Bs d e0 ∧
      ∃ A0 B0 : M.Ty P → ℂ → ℂ, SmAB P A0 B0 ∧ ConnF P Bs d e0 A0 B0 ∧
        (∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A0 ρ w) ζ).re = 0) ∧
        ∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A0 ρ w) 0 R).im = Real.pi * n

def GTCPhaseRel : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      IsFrameB P Bs e0 → KapF P Bs d e0 →
      ∃ u : M.Ty P → ℂ → ℂ, (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) ∧
        ∀ ρ, ∀ ζ ∈ Ann P, e ρ ζ = u ρ ζ • e0 ρ ζ

def GTCConnUniq : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
      ∀ A B A' B' : M.Ty P → ℂ → ℂ, SmAB P A B → SmAB P A' B' → ConnF P Bs d e A B → ConnF P Bs d e A' B' →
        ∀ ρ, ∀ ζ ∈ Ann P, A ρ ζ = A' ρ ζ

def GTCConnPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (A B u : M.Ty P → ℂ → ℂ), SmAB P A B →
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) →
      ConnF P Bs d e A B →
      SmAB P (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ) (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) ∧
      ConnF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) (fun ρ ζ => A ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
        (fun ρ ζ => B ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ)

def GTCPhHol : Prop :=
  ∀ (TT : ℝ) (u : ℂ → ℂ), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → ‖u ζ‖ = 1) →
    ∀ R : ℝ, 0 < R → TT < R ^ 2 → ∃ n : ℤ, (circleIntegral (fun w => star (u w) * NF.dZ u w) 0 R).im = Real.pi * n

def GTCPhCurv : Prop :=
  ∀ (TT : ℝ) (u : ℂ → ℂ), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → ‖u ζ‖ = 1) →
    ∀ ζ : ℂ, TT < Complex.normSq ζ → (NF.dZb (fun w => star (u w) * NF.dZ u w) ζ).re = 0

theorem ann_isOpen (P : M.Par) : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq

theorem sphere_sub_ann (P : M.Par) {R : ℝ} (hR0 : 0 < R) (hR : P.TT < R ^ 2) :
    Metric.sphere (0 : ℂ) R ⊆ Ann P := by
  intro w hw
  have h : ‖w‖ = R := by simpa using hw
  show P.TT < Complex.normSq w
  rw [Complex.normSq_eq_norm_sq, h]
  exact hR

theorem trR_congr {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (e e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (h : ∀ ρ, ∀ ζ ∈ Ann P, e ρ ζ = e' ρ ζ) :
    trR P Bs e = trR P Bs e' := by
  funext Φ ρ
  unfold trR rawR
  congr 1
  funext q
  rw [h ρ q.1.2 q.2.2]

theorem tt_nonneg_of_hyp {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}
    {X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'} {d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))}
    (h : GTHyp P Bs X d) : 0 ≤ P.TT := by
  have hOK := h.1.1
  show (0 : ℝ) ≤ P.T * P.T'
  exact (mul_pos hOK.T_pos hOK.T'_pos).le

theorem gauge_rel (hRef : GTCRef) (hPR : GTCPhaseRel) (hU : GTCConnUniq) (hCP : GTCConnPhase)
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hyp : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (A B : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hConn : ConnF P Bs d e A B) :
    ∃ (A0 : M.Ty P → ℂ → ℂ) (u : M.Ty P → ℂ → ℂ),
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A0 ρ) (Ann P)) ∧
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) ∧
      (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => star (u ρ ζ) * NF.dZ (u ρ) ζ) (Ann P)) ∧
      (∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A0 ρ w) ζ).re = 0) ∧
      (∀ ρ (R : ℝ), 0 < R → P.TT < R ^ 2 →
          ∃ n : ℤ, (circleIntegral (fun w => modA P ρ w - A0 ρ w) 0 R).im = Real.pi * n) ∧
      ∀ ρ, ∀ ζ ∈ Ann P, A ρ ζ = A0 ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ := by
  obtain ⟨e0, he0, hk0, A0, B0, hAB0, hConn0, hcurv, hhol⟩ := hRef Wp Wq P Bs X d hyp
  obtain ⟨u, hu, heu⟩ := hPR Wp Wq P Bs X d hyp e e0 he hk he0 hk0
  obtain ⟨hAB1, hConn1⟩ := hCP Wp Wq P Bs X d hyp e0 A0 B0 u hAB0 hu hConn0
  have htr : trR P Bs (fun ρ ζ => u ρ ζ • e0 ρ ζ) = trR P Bs e :=
    trR_congr P Bs _ _ (fun ρ ζ hζ => (heu ρ ζ hζ).symm)
  have hConn1' : ConnF P Bs d e (fun ρ ζ => A0 ρ ζ + star (u ρ ζ) * NF.dZ (u ρ) ζ)
      (fun ρ ζ => B0 ρ ζ - star (u ρ ζ) * NF.dZb (u ρ) ζ) := by
    unfold ConnF at hConn1 ⊢
    rw [← htr]
    exact hConn1
  have hA := hU Wp Wq P Bs X d hyp e he A B _ _ hAB hAB1 hConn hConn1'
  refine ⟨A0, u, fun ρ => (hAB0 ρ).1, hu, fun ρ => ?_, hcurv, hhol, hA⟩
  exact ((hAB1 ρ).1.sub (hAB0 ρ).1).congr (fun ζ _ => by ring)

def GTCHolOfCut : Prop := GTCRef → GTCPhaseRel → GTCConnUniq → GTCConnPhase → GTCPhHol → GTCHol

theorem gTCHol_of_cut : GTCHolOfCut := by
  intro hRef hPR hU hCP hPh Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn ρ R hR0 hR
  obtain ⟨A0, u, hA0s, hu, hws, -, hhol, hA⟩ :=
    gauge_rel hRef hPR hU hCP Wp Wq P Bs X d hyp e he hk A B hAB hConn
  have hTT := tt_nonneg_of_hyp hyp
  obtain ⟨n1, hn1⟩ := hhol ρ R hR0 hR
  obtain ⟨n2, hn2⟩ := hPh P.TT (u ρ) (hu ρ).1 (hu ρ).2 R hR0 hR
  have hsph := sphere_sub_ann P hR0 hR
  have hf : CircleIntegrable (fun w => modA P ρ w - A0 ρ w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le (((modA_smooth P ρ hTT).sub (hA0s ρ)).continuousOn.mono hsph)
  have hg : CircleIntegrable (fun w => star (u ρ w) * NF.dZ (u ρ) w) 0 R :=
    ContinuousOn.circleIntegrable hR0.le ((hws ρ).continuousOn.mono hsph)
  have heq : (∮ w in C(0, R), modA P ρ w - A ρ w) =
      ∮ w in C(0, R), (modA P ρ w - A0 ρ w) - star (u ρ w) * NF.dZ (u ρ) w := by
    apply circleIntegral.integral_congr hR0.le
    intro w hw
    try dsimp only
    rw [hA ρ w (hsph hw)]
    ring
  refine ⟨n1 - n2, ?_⟩
  rw [heq, circleIntegral.integral_sub hf hg, Complex.sub_im, hn1, hn2]
  push_cast
  ring

def GTCCurvOfCut : Prop := GTCRef → GTCPhaseRel → GTCConnUniq → GTCConnPhase → GTCPhCurv → GTCCurv

theorem gTCCurv_of_cut : GTCCurvOfCut := by
  intro hRef hPR hU hCP hPc Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ
  obtain ⟨A0, u, hA0s, hu, hws, hcurv, -, hA⟩ :=
    gauge_rel hRef hPR hU hCP Wp Wq P Bs X d hyp e he hk A B hAB hConn
  have hTT := tt_nonneg_of_hyp hyp
  have hnhds : Ann P ∈ nhds ζ := (ann_isOpen P).mem_nhds hζ
  have hev : (fun w => modA P ρ w - A ρ w) =ᶠ[nhds ζ]
      fun w => (modA P ρ w - A0 ρ w) - star (u ρ w) * NF.dZ (u ρ) w := by
    filter_upwards [hnhds] with w hw
    rw [hA ρ w hw]
    ring
  have hfd : DifferentiableAt ℝ (fun w => modA P ρ w - A0 ρ w) ζ :=
    (((modA_smooth P ρ hTT).sub (hA0s ρ)).differentiableOn (by simp)).differentiableAt hnhds
  have hgd : DifferentiableAt ℝ (fun w => star (u ρ w) * NF.dZ (u ρ) w) ζ :=
    ((hws ρ).differentiableOn (by simp)).differentiableAt hnhds
  have hder : fderiv ℝ (fun w => modA P ρ w - A ρ w) ζ =
      fderiv ℝ (fun w => modA P ρ w - A0 ρ w) ζ - fderiv ℝ (fun w => star (u ρ w) * NF.dZ (u ρ) w) ζ := by
    exact hev.fderiv_eq.trans (hfd.hasFDerivAt.sub hgd.hasFDerivAt).fderiv
  have h1 := hcurv ρ ζ hζ
  have h2 := hPc P.TT (u ρ) (hu ρ).1 (hu ρ).2 ζ hζ
  unfold NF.dZb at h1 h2 ⊢
  rw [hder, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  have key : ∀ a b c d : ℂ, (1 / 2 : ℂ) * ((a - b) + Complex.I * (c - d)) =
      (1 / 2 : ℂ) * (a + Complex.I * c) - (1 / 2 : ℂ) * (b + Complex.I * d) := by
    intros; ring
  rw [key, Complex.sub_re, h1, h2, sub_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LowKAllPos
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrCap

theorem exp_eig {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (A : W →L[ℂ] W) (μ : ℂ)
    (x : W) (hx : A x = μ • x) : NormedSpace.exp A x = Complex.exp μ • x := by
  have hpow : ∀ n : ℕ, (A ^ n) x = μ ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      show (A ^ n) (A x) = _
      rw [hx, map_smul, ih, smul_smul, pow_succ, mul_comm]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ (𝔸 := W →L[ℂ] W), NormedSpace.exp_eq_tsum ℂ (𝔸 := ℂ)]
  simp only
  have h := (ContinuousLinearMap.apply ℂ W x).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)
  simp only [ContinuousLinearMap.apply_apply] at h
  rw [h]
  simp only [_root_.smul_apply, hpow, smul_smul]
  rw [← (NormedSpace.expSeries_summable' (𝕂 := ℂ) μ).tsum_smul_const x]
  simp only [smul_eq_mul]

theorem exp_sum_eig {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {k : ℕ}
    (T : Fin k → (W →L[ℂ] W)) (θ μ : Fin k → ℝ) (x : W) (hx : ∀ c, T c x = (μ c : ℂ) • x) :
    NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • T c) x = Complex.exp (((∑ c, μ c * θ c : ℝ) : ℂ) * Complex.I) • x := by
  rw [exp_eig _ (∑ c, ((θ c : ℂ) * Complex.I) * (μ c : ℂ)) x]
  · congr 2
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring
  · rw [_root_.sum_apply, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro c _
    rw [_root_.smul_apply, hx, smul_smul]

theorem lowK_allPos (k : ℕ) (u : Fin k → ℝ) (j : Fin k) :
    PI.UpqRep.lowK (PI.UpqRep.allPos k) u j = u j - ((k : ℝ) - 1) / 2 + (j : ℕ) := by
  have hj := j.isLt
  unfold PI.UpqRep.lowK PI.UpqRep.rhoN PI.UpqRep.rhoC PI.UpqRep.allPos
  simp only [Pi.add_apply, Pi.sub_apply, ne_eq, not_true_eq_false, and_false, and_true]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem deriv_cexp {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (L : ℝ) (v : W) :
    HasDerivAt (fun t : ℝ => Complex.exp (((-t * L : ℝ) : ℂ) * Complex.I) • v) ((-(L : ℂ) * Complex.I) • v) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => -t * L) (-L) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).neg).mul_const L
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => (((-t * L : ℝ) : ℂ) * Complex.I)) (((-L : ℝ) : ℂ) * Complex.I) 0 :=
    h1.ofReal_comp.mul_const Complex.I
  have h3 := (h2.cexp).smul_const v
  convert h3 using 1
  simp

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem lie_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : ι → Mx k r) (hX : ∀ i, InLieW k r z (X i)) :
    InLieW k r z (∑ i ∈ s, ((c i : ℝ) : ℂ) • X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LieBracketMultiplication.lie_zero (k := k) (r := r) (z := z))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact LieBracketMultiplication.lie_add (LieBracketMultiplication.lie_smul (hX a) _) ih

theorem dOp_sum (hR : IsRepW k r z π) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : ι → Mx k r)
    (hX : ∀ i, InLieW k r z (X i)) : dOp π (∑ i ∈ s, ((c i : ℝ) : ℂ) • X i) = ∑ i ∈ s, c i • dOp π (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SkewHermitianParts.dOp_zero π
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      (differential_operator_linear W k r z π hR _ _ (LieBracketMultiplication.lie_smul (hX a) (c a)) (lie_sum s c X hX)).1,
      (differential_operator_linear W k r z π hR _ _ (hX a) (hX a)).2 (c a), ih]

theorem op_torus (hR : IsRepW k r z π) {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs)
    (θ : Fin k → ℝ) :
    π (NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • unitB (Hpk k r) Bs c c)) =
      NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • ecOp π (unitB (Hpk k r) Bs c c)) := by
  set A : Fin k → Mx k r := fun c => hpart2 (Hpk k r) (unitB (Hpk k r) Bs c c) with hAdef
  have hA : ∀ c, InLieW k r z (A c) := fun c => (QrD.frame_lie hB c c).2
  have hAe : ∀ c, A c = (-Complex.I) • unitB (Hpk k r) Bs c c := fun c => hpart2_self Bs c
  have hY : ∑ c, ((θ c : ℂ) * Complex.I) • unitB (Hpk k r) Bs c c =
      ((1 : ℝ) : ℂ) • ∑ c, ((-θ c : ℝ) : ℂ) • A c := by
    rw [Complex.ofReal_one, one_smul]
    apply Finset.sum_congr rfl
    intro c _
    rw [hAe c, smul_smul]
    congr 1
    push_cast
    ring
  have hec : ∀ c, ecOp π (unitB (Hpk k r) Bs c c) = Complex.I • dOp π (A c) := by
    intro c
    unfold ecOp
    rw [hpart1_self, SkewHermitianParts.dOp_zero, zero_add]
  rw [hY, representation_exp W k r z π hR _ (lie_sum _ _ _ hA) 1, one_smul, dOp_sum hR _ _ _ hA]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [hec c, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  linear_combination (-(θ c : ℂ)) * Complex.I_sq

end Rep

end QrCap

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneAddProjectionMemIsotropicSet
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section N2

variable {k r : ℕ}

theorem sg_esI (b : Fin r) : NFOne.sg k r (esI k r b) = eI k r b := by
  have hb := b.isLt
  ext
  simp only [NFOne.sg, esI, eI]
  omega

theorem pm_col_star (j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (b : Fin r) (hb : b.val < j) :
    (1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b) = V b.val := by
  funext p
  have hb' := b.isLt
  have hq : r + k < (esI k r b).val := by simp only [esI]; omega
  have hsg : (NFOne.sg k r (esI k r b)).val = b.val := by rw [sg_esI]; rfl
  have hcol : ((1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b)) p =
      (if p = esI k r b then 1 else 0) + NFOne.Pm k r j V p (esI k r b) := by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.add_apply, Matrix.one_apply, add_mul]
  rw [hcol]
  by_cases hp1 : p.val < r
  · rw [NFOne.P_XS k r j V p _ hp1 hq, hsg, if_pos hb, if_neg (fun e => by rw [e] at hp1; omega), zero_add]
  · by_cases hp2 : p.val ≤ r + k
    · rw [NFOne.P_WS k r j V p _ (by omega) hp2 hq, hsg, if_neg (fun e => by rw [e] at hp2; omega), zero_add]
    · rw [NFOne.P_rowS k r j V p _ (by omega), add_zero, Vs b.val hb p (by omega)]
      have e : p = esI k r b ↔ (NFOne.sg k r p).val = b.val := by
        rw [Fin.ext_iff]; simp only [NFOne.sg, esI]; omega
      by_cases h1 : p = esI k r b
      · rw [if_pos h1, if_pos (e.mp h1)]
      · rw [if_neg h1, if_neg (fun h2 => h1 (e.mpr h2))]

theorem one_add_projection_mem_isotropic_set (j : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + NFOne.Pm k r j V) ∈ N0set k r z' := by
  refine ⟨NFOne.unitary_P k r j V V0 Vs Viso, fun a => NFOne.cols_X k r j V a,
    NFOne.z_fix k r j V z' hz Vz, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · rw [Matrix.add_apply, NFOne.P_rowWS_colW k r j V p q hp hq2, add_zero, Matrix.one_apply]
  · rw [Matrix.add_apply, NFOne.P_rowS k r j V p q hp, add_zero, Matrix.one_apply]

private theorem mul_mem_n0set {z' : Fin (2 * r + k + 1) → ℂ}
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ N0set k r z') (hh : h ∈ N0set k r z') :
    g * h ∈ N0set k r z' := by
  obtain ⟨gU, gX, gz, gW, gS⟩ := hg
  obtain ⟨hU, hX, hz, hW, hS⟩ := hh

  have col : ∀ p m : Fin (2 * r + k + 1), m.val < r → g p m = if p = m then 1 else 0 := by
    intro p m hm
    have := congrFun (gX ⟨m.val, hm⟩) p
    simpa [bvec, eI, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have key : ∀ p q : Fin (2 * r + k + 1), r ≤ p.val →
      ((r ≤ q.val ∧ q.val ≤ r + k) ∨ (r + k < q.val ∧ r + k < p.val)) →
      ∀ m, g p m * h m q = if m = q then g p q else 0 := by
    intro p q hp hq m
    have hqr : r ≤ q.val := by rcases hq with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    by_cases hm1 : m.val < r
    · rw [col p m hm1, if_neg (fun e => by rw [e] at hp; omega), zero_mul,
        if_neg (fun e => by rw [e] at hm1; omega)]
    · have tail : h m q = (if m = q then 1 else 0) → g p m * h m q = if m = q then g p q else 0 := by
        intro hmq
        by_cases e : m = q
        · subst e; simp [hmq]
        · simp [hmq, e]
      by_cases hm2 : m.val ≤ r + k
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · rw [gW p m (by omega) hm2 hp, if_neg (fun e => by rw [e] at hp2; omega), zero_mul,
            if_neg (fun e => by rw [e] at hm2; omega)]
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · exact tail (hS m q hq1 (by omega))
  refine ⟨?_, fun a => ?_, ?_, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · change (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    change gᴴ * Hpk k r * g = Hpk k r at gU
    change hᴴ * Hpk k r * h = Hpk k r at hU
    rw [Matrix.conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [Matrix.mul_assoc], gU, hU]
  · rw [← Matrix.mulVec_mulVec, hX, gX]
  · rw [← Matrix.mulVec_mulVec, hz, gz]
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q hp (Or.inl ⟨hq1, hq2⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gW p q hq1 hq2 hp
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q (by omega) (Or.inr ⟨hq, hp⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gS p q hq hp

theorem mul_mem_isotropic_unipotent_set (z' : Fin (2 * r + k + 1) → ℂ) (j1 j2 : ℕ) (V1 V2 : ℕ → Fin (2 * r + k + 1) → ℂ)
    (h1 : (1 + NFOne.Pm k r j1 V1) ∈ N0set k r z') (h2 : (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z') :
    (1 + NFOne.Pm k r j1 V1) * (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z' := by
  exact mul_mem_n0set h1 h2

theorem herm_bvec_esI (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (esI k r b)) = v (eI k r b) := by
  have hb := b.isLt
  have hv : (esI k r b).val = 2 * r + k - b.val := rfl
  have hrow : ∀ q : Fin (2 * r + k + 1), Hpk k r (esI k r b) q = if q = eI k r b then 1 else 0 := by
    intro q
    have e : q = eI k r b ↔ q.val = b.val := by rw [Fin.ext_iff]; simp only [eI]
    by_cases h1 : q = eI k r b
    · rw [if_pos h1]; have := e.mp h1
      unfold Hpk
      rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h1]; have := fun h => h1 (e.mpr h)
      unfold Hpk
      rw [if_neg (by omega), if_neg (by omega), if_neg (by rintro ⟨-, h2, -⟩; omega)]
  simp only [herm, bvec, dotProduct, Matrix.mulVec]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp only [Pi.star_apply, Pi.single_eq_same, star_one, one_mul, hrow]
    simp
  · intro q _ hq; simp [Pi.single_apply, hq]
  · simp

end N2

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end
