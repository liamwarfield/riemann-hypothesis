module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameLatticePointsEqIntegralMatricesLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilRepOrientedPairRationalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselSecondBasePointCharacterTrivialDepthLattic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasePointCharacterTrivialOnDepthLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedDiagonalCoordinateMemCompletionConjAA
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedDiagonalCoordinateMemCompletionConjAA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF.HatCoord

open GlobalTheory.MonoBes
open scoped Pointwise

variable {D : D7}

section SlopeTestRemainingChoices

variable {A B B₀ : HSp D} {c ρ : ℕ}

theorem rev_ne (hc : 2 * ρ ≤ c) (i : Fin ρ) : (Fin.castLE (by omega) i : Fin c).rev ≠ Fin.castLE (by omega) i := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_rev, Fin.val_castLE] at h'
  omega

theorem colsOf_pair (a : HermitianOrthogonalExtensionData A B c (-1)) (f : Fin ρ → Fin c) (s : Fin ρ → D.host.E) (x : Fin B.rank → D.host.E)
    (i : Fin ρ) : (((colsOf a.a f s)ᴴ * B.gram) *ᵥ x) i = star (s i) * ((a.aᴴ * B.gram) *ᵥ x) (f i) := by
  unfold colsOf
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  change star (s i * a.a k (f i)) * _ * _ = _
  rw [star_mul']
  ring

theorem e'_scaled (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ) (hd : IsAuxiliaryVectorWittDec a d) (hc : 2 * ρ ≤ c) (i : Fin ρ)
    (k : Fin B.rank) :
    star ((-D.host.xi0) ^ (i.1 + 1)) * d.e' k i = a.a k (Fin.castLE (by omega) i : Fin c).rev := by
  obtain ⟨h0, he, s, hs⟩ := hd
  have key : ((d.e'ᴴ * B.gram) *ᵥ fun l => d.e l i) i = 1 := by
    have h1 := congrFun (congrFun d.e'e i) i
    rw [Matrix.one_apply_eq] at h1
    exact h1
  have hcol : (fun l => d.e l i) = frameMat B A a.ι *ᵥ 0 +
      a.a *ᵥ Pi.single (Fin.castLE (by omega) i : Fin c) ((-D.host.xi0) ^ (i.1 + 1)) := by
    funext l
    rw [Matrix.mulVec_zero, zero_add, mulVec_single_apply, mul_comm, he]
    rfl
  have hj : ((Fin.castLE (by omega) i : Fin c).rev).rev ≠ (Fin.castLE (by omega) i : Fin c).rev := by
    rw [Fin.rev_rev]
    exact fun h => rev_ne hc i h.symm
  rw [hcol, hs, colsOf_pair, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ hj] at key
  simp only [Fin.rev_rev, Pi.single_eq_same] at key
  have k2 := congrArg star key
  rw [star_mul', star_star, star_one] at k2
  rw [hs]
  change star ((-D.host.xi0) ^ (i.1 + 1)) * (s i * a.a k (Fin.castLE (by omega) i : Fin c).rev) = _
  rw [← mul_assoc, mul_comm (star _) (s i), k2, one_mul]

theorem ideal_smul_auxiliary_vector_mem_lattice (a : HermitianOrthogonalExtensionData A B c (-1)) (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (j : Fin c) {b : D.host.E} (hb : b ∈ 𝔟 j) : (fun k => b * a.a k j) ∈ a.lat Λ 𝔟 := by
  refine ⟨0, Λ.zero_mem, Pi.single j b, fun p => ?_, ?_⟩
  · by_cases hp : p = j
    · subst hp
      simpa using hb
    · simp only [Pi.single_apply, hp, if_false]
      exact (𝔟 p).zero_mem
  · funext k
    rw [Matrix.mulVec_zero, zero_add, mulVec_single_apply, mul_comm]

theorem pair_mem (a : HermitianOrthogonalExtensionData A B c (-1)) (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (j : Fin c) (hj : j.rev ≠ j) {y : Fin B.rank → D.host.E} (hy : y ∈ a.lat Λ 𝔟) :
    ((a.aᴴ * B.gram) *ᵥ y) j ∈ 𝔟 j.rev := by
  obtain ⟨y₀, -, u, hu, rfl⟩ := hy
  rw [auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ hj]
  exact hu _

end SlopeTestRemainingChoices

theorem coord_mul_mem {A B B₀ A' B' B₀' : HSp D} {c c' ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ)
    (hd : IsAuxiliaryVectorWittDec a d) (hc : 2 * ρ ≤ c) (a' : HermitianOrthogonalExtensionData A' B' c' (-1)) (d' : HypDec B' B₀' ρ) (hd' : IsAuxiliaryVectorWittDec a' d')
    (hc' : 2 * ρ ≤ c') (Λ : Lat A) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ' : Lat A')
    (𝔟' : Fin c' → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {x : Matrix (Fin B'.rank) (Fin B.rank) D.host.E}
    (hx : x ∈ homLat (a.lat Λ 𝔟) (a'.lat Λ' 𝔟')) (p : Fin ρ) {b : D.host.E}
    (hb : b ∈ 𝔟 (Fin.castLE (by omega) p : Fin c).rev) :
    (d'.qY * x * d.e') p p * b ∈ 𝔟' (Fin.castLE (by omega) p : Fin c').rev := by
  have hx' : ∀ y ∈ a.lat Λ 𝔟, x *ᵥ y ∈ a'.lat Λ' 𝔟' := hx
  have hv := pair_mem a' Λ' 𝔟' (Fin.castLE (by omega) p : Fin c') (rev_ne hc' p)
    (hx' _ (ideal_smul_auxiliary_vector_mem_lattice a Λ 𝔟 _ hb))
  obtain ⟨h0', he', s', hs'⟩ := hd'
  have hcol : (fun k => b * a.a k (Fin.castLE (by omega) p : Fin c).rev) =
      (b * star ((-D.host.xi0) ^ (p.1 + 1))) • fun k => d.e' k p := by
    funext k
    rw [Pi.smul_apply, smul_eq_mul, ← e'_scaled a d hd hc p k]
    ring
  rw [hcol, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at hv
  have hent : (d'.qY * x * d.e') p p = ((d'.eᴴ * B'.gram) *ᵥ (x *ᵥ fun k => d.e' k p)) p := by
    rw [Matrix.mulVec_mulVec]
    rfl
  rw [hent, he', colsOf_pair]
  convert hv using 1
  ring

private theorem host_ccE_ne_bot (D : D7) : D.host.ccE ≠ ⊥ := by
  unfold Formalism.BasicNotions.Host.ccE
  rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E))]
  exact D.host.ccK_ne_bot

private theorem host_b_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  have h3 : D.host.conj • (⊥ : Ideal (𝓞 D.host.E)) = ⊥ := by
    ext x
    simp
  rw [h, h3, sup_bot_eq] at h2
  exact bot_ne_top h2

theorem AA_ne (D : D7) : D.host.AA ≠ 0 := by
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  exact mul_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (host_ccE_ne_bot D))
    (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (host_b_ne_bot D)))

private theorem conj_smul_ne_bot' {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) : D.host.conj • I ≠ ⊥ := by
  intro h
  apply hI
  have h2 : D.host.conj⁻¹ • (D.host.conj • I) = D.host.conj⁻¹ • (⊥ : Ideal (𝓞 D.host.E)) := by rw [h]
  rw [inv_smul_smul] at h2
  rw [h2]
  ext x
  simp

theorem AAbar_ne (D : D7) : D.host.AAbar ≠ 0 := by
  unfold Formalism.BasicNotions.Host.AAbar
  exact mul_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (conj_smul_ne_bot' (host_ccE_ne_bot D)))
    (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (conj_smul_ne_bot' (host_b_ne_bot D))))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : GlobalTheory.Asc.Frames G}

theorem modulBar_ne_bot' (P : Places L) (sc : Consts) : P.modulBar sc ≠ ⊥ := by
  intro h
  apply P.modul_ne_bot sc
  have h2 : D.host.conj⁻¹ • P.modulBar sc = D.host.conj⁻¹ • (⊥ : Ideal (𝓞 D.host.E)) := by rw [h]
  rw [Places.modulBar, inv_smul_smul] at h2
  rw [h2]
  ext x
  simp

private theorem mem_of_mul_mem_mul_fractionalIdeal {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {I A : FractionalIdeal R⁰ K} {t : K} (hI : I ≠ 0) (h : ∀ b ∈ I, t * b ∈ I * A) : t ∈ A := by
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  have h1 : FractionalIdeal.spanSingleton R⁰ t * I ≤ I * A := by
    rw [FractionalIdeal.mul_le]
    intro i hi b hb
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton R⁰).1 hi
    rw [smul_mul_assoc]
    exact Submodule.smul_mem (↑(I * A) : Submodule R K) z (h b hb)
  calc FractionalIdeal.spanSingleton R⁰ t = FractionalIdeal.spanSingleton R⁰ t * I * I⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
    _ ≤ I * A * I⁻¹ := by
        rw [FractionalIdeal.mul_le]
        intro u hu v hv
        exact FractionalIdeal.mul_mem_mul (h1 hu) hv
    _ = A := by rw [mul_comm I A, mul_assoc, mul_inv_cancel₀ hI, mul_one]

private theorem stairId_ne_zero' {𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h : 𝔞 ≠ 0) (h' : 𝔞' ≠ 0) (c : ℕ)
    (q : Fin c) : stairId 𝔞 𝔞' c q ≠ 0 := by
  unfold stairId
  exact mul_ne_zero (pow_ne_zero _ h) (inv_ne_zero (pow_ne_zero _ h'))

private theorem stairId_rev_castLE_mul (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h : 𝔞' ≠ 0) (ρ : ℕ) (p : Fin ρ) :
    stairId 𝔞 𝔞' (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev * 𝔞' =
      stairId 𝔞 𝔞' (2 * ρ + 1 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev := by
  unfold stairId
  have e1 : 2 * ρ + 1 - 1 - ((Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev).1 = p.1 + 1 := by
    simp only [Fin.val_rev, Fin.val_castLE]
    omega
  have e2 : 2 * ρ + 2 - 1 - ((Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev).1 = p.1 + 1 := by
    simp only [Fin.val_rev, Fin.val_castLE]
    omega
  have e3 : ((Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev).1 + 1 =
      (((Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev).1 + 1) + 1 := by
    simp only [Fin.val_rev, Fin.val_castLE]
    omega
  rw [e1, e2, e3, pow_succ 𝔞' (((Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev).1 + 1), mul_inv, mul_assoc,
    mul_assoc, inv_mul_cancel₀ h, mul_one]

private theorem stA_ne_zero (P : Places L) (sc : Consts) : P.stA sc ≠ 0 := by
  unfold Places.stA
  exact mul_ne_zero (AA_ne D) (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (modulBar_ne_bot' P sc)))

private theorem stAbar_ne_zero (P : Places L) (sc : Consts) : P.stAbar sc ≠ 0 := by
  unfold Places.stAbar
  exact mul_ne_zero (AAbar_ne D) (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).2 (P.modul_ne_bot sc)))

theorem coord_mem_stAbar (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m)
    {x : Matrix (Fin (G.V (.grid (2 * ρ + 1) 0)).rank) (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) D.host.E}
    (hx : x ∈ homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) (p : Fin ρ) :
    ((F.dJ ρ h).qY * x * (F.dB ρ h).e') p p ∈ G.pl.stAbar sc := by
  have hA : G.pl.stA sc ≠ 0 := stA_ne_zero G.pl sc
  have hA' : G.pl.stAbar sc ≠ 0 := stAbar_ne_zero G.pl sc
  have hx2 : x ∈ homLat ((G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)))
      ((G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1))) := by
    rw [← G.sp.colLat, ← G.sp.colLat]
    exact hx
  refine mem_of_mul_mem_mul_fractionalIdeal (I := stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)
    (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) (stairId_ne_zero' hA hA' _ _) fun b hb => ?_
  rw [stairId_rev_castLE_mul _ _ hA' ρ p]
  exact coord_mul_mem (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h) (hF.hB ρ h) (by omega)
    (G.colDec (2 * ρ + 1) (by omega) (by omega)) (F.dJ ρ h) (hF.hJ ρ h) (by omega) _ _ _ _ hx2 p hb

theorem coord_mem_AAbar (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m)
    {x : Matrix (Fin (G.V (.grid (2 * ρ + 1) 0)).rank) (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) D.host.E}
    (hx : x ∈ G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) (p : Fin ρ) :
    ((F.dJ ρ h).qY * x * (F.dB ρ h).e') p p ∈ D.host.AAbar := by
  have hid : ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * G.pl.stAbar sc =
      D.host.AAbar := by
    unfold Places.stAbar
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ ((FractionalIdeal.coeIdeal_ne_zero).2 (G.pl.modul_ne_bot sc)), mul_one]
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun y z hy hz => ?_)
  · have ht := coord_mem_stAbar hF ρ h hy p
    have hr' : algebraMap (𝓞 D.host.E) D.host.E r ∈
        ((G.modul : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩
    have hm := FractionalIdeal.mul_mem_mul hr' ht
    rw [hid] at hm
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Algebra.smul_def]
    exact hm
  · rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact Submodule.add_mem (↑D.host.AAbar : Submodule (𝓞 D.host.E) D.host.E) hy hz

theorem gen_eq {m n : ℕ} (α : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) :
    (Matrix.of fun i j => α ⊗ₜ[D.host.F] x i j : Mx D m n) = (α ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • rat x := by
  ext i j
  simp only [rat, Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  unfold incA
  rw [show inclR (AF D.host.F) (x i j) = (1 : AF D.host.F) ⊗ₜ[D.host.F] x i j from rfl,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem hatMx_coord_mem : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : GlobalTheory.Asc.Frames G}, Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (x : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))), x ∈ hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) → ∀ p : Fin ρ, ((F.dJ ρ h).pY * x * (F.dB ρ h).jY) p p ∈ complId D.host.AAbar := by
  intro D T L sc G F hF ρ h x hx p
  unfold hatMx at hx
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    have ht := coord_mem_AAbar hF ρ h hy p
    rw [gen_eq]
    unfold HypDec.pY HypDec.jY
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    unfold rat
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    unfold incA
    rw [show inclR (AF D.host.F) (((F.dJ ρ h).qY * y * (F.dB ρ h).e') p p) =
        (1 : AF D.host.F) ⊗ₜ[D.host.F] (((F.dJ ρ h).qY * y * (F.dB ρ h).e') p p) from rfl,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    exact tmul_mem_complId hα ht
  | zero =>
    rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
    exact zero_mem _
  | add w z _ _ hw hz =>
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact add_mem hw hz
  | neg w _ hw =>
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    exact neg_mem hw

end GlobalTheory.XCharBF.HatCoord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletedDiagonalCoordinateMemCompletionConjAAStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_diagonal_coordinate_mem_completion_conj_AA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : GlobalTheory.Asc.Frames G}, Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (x : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))), x ∈ hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) → ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ x ⬝ (F.dB ρ h).jY) p p ∈ complId D.host.AAbar := by
  first | exact @GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem | exact GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem | (intros; apply GlobalTheory.XCharBF.HatCoord.hatMx_coord_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicTraceCharDifferentGenConjIdealCompletionAl
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicTraceCharDifferentGenConjIdealCompletionAl
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

theorem conj_mem_AA_mul_AAbar {a : D.host.E} (ha : a ∈ D.host.AA * D.host.AAbar) :
    D.host.conj a ∈ D.host.AA * D.host.AAbar := by
  refine FractionalIdeal.mul_induction_on (C := fun a => D.host.conj a ∈ D.host.AA * D.host.AAbar) ha ?_ ?_
  · intro x hx y hy
    rw [map_mul, mul_comm (D.host.conj x)]
    exact FractionalIdeal.mul_mem_mul (Formalism.L2.Pj.conj_mem_AA D hy) (Formalism.L2.Pj.conj_mem_AAbar D hx)
  · intro x y hx hy
    rw [map_add (f := _)]
    exact Submodule.add_mem (p := ((D.host.AA * D.host.AAbar : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E)) hx hy

theorem hostDifferentGenerator_mul_mem_inverseDifferent {a : D.host.E} (ha : a ∈ D.host.AA * D.host.AAbar) :
    D.host.xi0 * a ∈ GlobalTheory.IdeleAA.Dual D := by
  change _ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
  rw [← Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D]
  have h := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0) ha
  rwa [← mul_assoc] at h

theorem psiE_add' (ψ : AddChar (AF D.host.F) ℂ) (x y : AE D) : psiE ψ (x + y) = psiE ψ x * psiE ψ y := by
  unfold psiE
  rw [map_add (f := _), AddChar.map_add_eq_mul]

theorem psiE_zero' (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  unfold psiE
  rw [map_zero, AddChar.map_zero_eq_one]

theorem cA_tmul' (p : AF D.host.F) (e : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] e) = p ⊗ₜ[D.host.F] D.host.conj e := by
  rw [GlobalTheory.IdeleAA.tmul_eq, map_mul, GlobalTheory.SelfDualAt.cA_alg, GlobalTheory.IdeleAA.cA_incA, ← GlobalTheory.IdeleAA.tmul_eq]

theorem adelicTraceChar_differentGen_conj_integral_tmul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {α : Af D.host.F}
    (hα : α ∈ intAf D.host.F) {a : D.host.E} (ha : a ∈ D.host.AA * D.host.AAbar) :
    psiE ψ (incA D D.host.xi0 * cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a)) = 1 := by
  have e : incA D D.host.xi0 * cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) =
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (D.host.xi0 * D.host.conj a) := by
    rw [cA_tmul', GlobalTheory.IdeleAA.tmul_eq, GlobalTheory.IdeleAA.tmul_eq, map_mul]
    ring
  rw [e, GlobalTheory.FinPl.Conductor.psiE_eq_chi ψ (by exact TensorProduct.zero_tmul _ _)]
  exact GlobalTheory.IdeleAA.chi_tmul_dual hψ hα (hostDifferentGenerator_mul_mem_inverseDifferent (conj_mem_AA_mul_AAbar ha))

theorem adelicTraceChar_differentGen_conj_idealCompletion : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) →
    ∀ s ∈ complId (D.host.AA * D.host.AAbar), psiE ψ (incA D D.host.xi0 * cA D s) = 1 := by
  intro D ψ hψ s hs
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨α, hα, a, ha, rfl⟩ := hs
    exact adelicTraceChar_differentGen_conj_integral_tmul hψ hα ha
  | zero => rw [map_zero, mul_zero]; exact psiE_zero' ψ
  | add x y _ _ hx hy => rw [map_add (f := _), mul_add, psiE_add', hx, hy, one_mul]
  | neg x _ hx =>
    have h := psiE_add' ψ (incA D D.host.xi0 * cA D x) (incA D D.host.xi0 * cA D (-x))
    rw [← mul_add, ← map_add (f := _), add_neg_cancel, map_zero, mul_zero, psiE_zero', hx, one_mul] at h
    exact h.symm

end GlobalTheory.XCharBF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicTraceCharDifferentGenConjIdealCompletionAlStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiE_xi0_mul_cA_eq_one_of_mem_complId : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → ∀ s ∈ complId (D.host.AA * D.host.AAbar), psiE ψ (incA D D.host.xi0 * cA D s) = 1 := by
  first | exact @GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion | exact GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion | (intros; apply GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDiagonalCoordinatesMemComplementIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDiagonalCoordinatesMemComplementIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF.DiagCoord

variable {D : D7}

theorem auxiliaryCoordinate_mem_staircaseIdeal {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {t : Fin B.rank → D.host.E} (ht : t ∈ d.lat Λ 𝔟) (r : Fin c) (hr : r.1 + r.1 + 1 ≠ c) :
    ((d.aᴴ * B.gram) *ᵥ t) r ∈ 𝔟 r.rev := by
  obtain ⟨y, -, v, hv, rfl⟩ := ht
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => (B.herm.eq (B.frame j) (B.frame i) : star (B.gram j i) = B.gram i j)
  have hperp : d.aᴴ * B.gram * frameMat B A d.ι = 0 := by
    have h1 := congrArg Matrix.conjTranspose d.perp
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A d.ι) = (frameMat B A d.ι)ᴴ := rfl
    rw [e, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero] at h1
    rw [← h1, Matrix.mul_assoc]
  have hgram : d.aᴴ * B.gram * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, hperp, hgram, zero_mulVec, zero_add]
  rw [mulVec, dotProduct, Finset.sum_eq_single r.rev]
  · have : antiDiagonalSignGramMatrix c ε r r.rev = 1 := by
      have := r.2
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
      rw [if_pos (by omega), if_neg (fun h => hr (by rw [Fin.ext_iff, Fin.val_rev] at h; omega))]
    rw [this, one_mul]; exact hv _
  · intro q _ hq
    have : antiDiagonalSignGramMatrix c ε r q = 0 := by
      have := r.2; have := q.2
      simp only [antiDiagonalSignGramMatrix]
      rw [if_neg (fun h => hq (by rw [Fin.ext_iff, Fin.val_rev]; omega))]
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem negPair_colsOf {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (hG : ∀ i j, star (G j i) = G i j)
    (a : Matrix (Fin n) (Fin c) D.host.E) (f : Fin k → Fin c) (w : Fin k → D.host.E) (s : Fin n → D.host.E) (p : Fin k) :
    ∑ j, (∑ l, star (s l) * (-G) l j) * colsOf a f w j p = -(w p * star (((aᴴ * G) *ᵥ s) (f p))) := by
  simp only [colsOf, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, star_sum, star_mul', star_star, hG,
    Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem entry_rankOne {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E) (e : Matrix (Fin n) (Fin l) D.host.E) (a : D.host.E)
    (t : Fin m → D.host.E) (g : Fin n → D.host.E) (p : Fin k) (p' : Fin l) :
    (q * Matrix.of (fun i j => a * t i * g j) * e) p p' = a * (q *ᵥ t) p * ∑ j, g j * e j p' := by
  simp only [Matrix.mul_apply, Matrix.of_apply, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem rat_tmul_entry {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E) (C : Matrix (Fin m) (Fin n) D.host.E)
    (e : Matrix (Fin n) (Fin l) D.host.E) (X : AF D.host.F) (p : Fin k) (p' : Fin l) :
    (rat q ⬝ (Matrix.of fun i j => X ⊗ₜ[D.host.F] C i j : Mx D m n) ⬝ rat e) p p' = X ⊗ₜ[D.host.F] (q * C * e) p p' := by
  have hinc : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun _ => rfl
  simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, hinc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, ← TensorProduct.tmul_sum]

theorem stairId_mul_inv_succ (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) {c₁ c₂ : ℕ}
    (q₁ : Fin c₁) (q₂ : Fin c₂) (hc : c₂ = c₁ + 1) (hq : q₂.1 = q₁.1 + 1) :
    stairId 𝔞 𝔞' c₁ q₁ * (stairId 𝔞 𝔞' c₂ q₂)⁻¹ = 𝔞' := by
  unfold stairId
  rw [show c₂ - q₂.1 = c₁ - q₁.1 by omega, hq, pow_succ 𝔞' (q₁.1 + 1)]
  have h1 : 𝔞 ^ (c₁ - q₁.1) ≠ 0 := pow_ne_zero _ h𝔞
  have h2 : 𝔞' ^ (q₁.1 + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  field_simp

theorem colsOf_gram {n c k : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin c) D.host.E) (f g : Fin k → Fin c)
    (w w' : Fin k → D.host.E) (p q : Fin k) :
    ((colsOf a f w)ᴴ * G * colsOf a g w') p q = star (w p) * w' q * (aᴴ * G * a) (f p) (g q) := by
  simp only [colsOf, Matrix.mul_apply, conjTranspose_apply, star_mul', Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring


set_option maxHeartbeats 1000000 in
theorem diag_mem_complId : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : GlobalTheory.Asc.Frames G}, Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (u : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))),
    u ∈ latO _ _ (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) →
    ∀ p : Fin ρ, ((F.dJ ρ h).pY ⬝ u ⬝ (F.dB ρ h).jY) p p ∈ complId (D.host.AA * G.pl.stAbar sc) := by
  intro D T L sc G F hF ρ h u hu p
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  obtain ⟨hcB, heB, sB, he'B⟩ := hF.hB ρ h
  set aJ := G.colDec (2 * ρ + 1) (by omega) (by omega) with haJ
  set aB := G.colDec (2 * ρ + 2) (by omega) h with haB
  obtain ⟨hAA, -⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hAb : G.pl.stAbar sc ≠ 0 := by
    intro h0
    apply hA
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h1 : star y ∈ G.pl.stAbar sc := (hconj _).2 (by rwa [star_star])
    have h2 := h0 _ h1
    rwa [star_eq_zero] at h2

  have hJ : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).qY *ᵥ t) p =
      star ((-D.host.xi0) ^ (p.1 + 1)) * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) := by
    intro t _
    simp only [HypDec.qY, heJ, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, colsOf, star_mul', Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
  have hJmem : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) ∈
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p).rev := by
    intro t ht
    have ht' : t ∈ aJ.lat (G.sp.P (2 * ρ + 1)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := by
      rw [haJ, ← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)]; exact ht
    exact auxiliaryCoordinate_mem_staircaseIdeal aJ _ _ ht' _ (by simp only [Fin.val_castLE]; omega)

  have hBmem : ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0),
      star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) ∈
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)⁻¹ := by
    intro s hs
    have hs' : s ∈ aB.lat (G.sp.P (2 * ρ + 2)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := by
      rw [haB, ← G.sp.colLat (2 * ρ + 2) (by omega) h]; exact hs
    have h1 := auxiliaryCoordinate_mem_staircaseIdeal aB _ _ hs' (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
      (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    exact ((GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ _).2 _).1 h1

  have hsc : star ((-D.host.xi0) ^ (p.1 + 1)) * sB p = 1 := by
    have h1 := congrFun (congrFun (F.dB ρ h).e'e p) p
    rw [he'B, heB, colsOf_gram, Matrix.one_apply_eq] at h1
    have h2 : (aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
        (Fin.castLE (by omega) p) = 1 := by
      rw [show aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a = antiDiagonalSignGramMatrix (2 * ρ + 2 - 1) (-1) from aB.gram]
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE]
      rw [if_pos (by omega), if_neg (fun e => by rw [Fin.ext_iff, Fin.val_rev, Fin.val_castLE] at e; omega)]
    rw [h2, mul_one] at h1
    have h3 := congrArg star h1
    rw [star_mul', star_star, star_one] at h3
    rw [mul_comm]; exact h3
  have hGB : ∀ i j, star ((G.V (.grid (2 * ρ + 2) 0)).gram j i) = (G.V (.grid (2 * ρ + 2) 0)).gram i j := fun i j =>
    (G.V (.grid (2 * ρ + 2) 0)).herm.eq ((G.V (.grid (2 * ρ + 2) 0)).frame j) ((G.V (.grid (2 * ρ + 2) 0)).frame i)

  have keyE : ∀ a ∈ D.host.AA, ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0),
      ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) *
        (F.dB ρ h).e') p p ∈ D.host.AA * G.pl.stAbar sc := by
    intro a ha s hs t ht
    rw [entry_rankOne _ _ a t (fun j => ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j), hJ t ht, he'B,
      negSp_gram, negPair_colsOf _ hGB]
    have e : a * (star ((-D.host.xi0) ^ (p.1 + 1)) *
          ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p)) *
        -(sB p * star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)) =
        -(a * (((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) := by
      linear_combination (-(a * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) * hsc
    rw [e]
    refine Submodule.neg_mem _ (FractionalIdeal.mul_mem_mul ha ?_)
    rw [← stairId_mul_inv_succ (G.pl.stA sc) (G.pl.stAbar sc) hA hAb (Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev
      (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev (by omega) (by simp only [Fin.val_rev, Fin.val_castLE]; omega)]
    exact FractionalIdeal.mul_mem_mul (hJmem t ht) (hBmem s hs)
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ((F.dJ ρ h).pY ⬝ (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j)) ⬝ (F.dB ρ h).jY) p p =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) *
          (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) * (F.dB ρ h).e') p p :=
      rat_tmul_entry _ _ _ _ _ _
    rw [key]
    exact tmul_mem_complId hα (keyE a ha s hs t ht)
  | zero => simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]; exact neg_mem hx

end GlobalTheory.XCharBF.DiagCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDiagonalCoordinatesMemComplementIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct BigOperators
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF GlobalTheory.XCharBF.DiagCoord
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_diagonalCoordinates_mem_complementIdeal :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : GlobalTheory.Asc.Frames G}, Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m)
      (u : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))),
    u ∈ latO _ _ (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) →
    ∀ p : Fin ρ, ((F.dJ ρ h).pY * u * (F.dB ρ h).jY) p p ∈ complId (D.host.AA * G.pl.stAbar sc) := by
  intro D T L sc G F hF ρ h u hu p
  have rat_tmul_entry {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E)
      (C : Matrix (Fin m) (Fin n) D.host.E)
      (e : Matrix (Fin n) (Fin l) D.host.E) (X : AF D.host.F) (p : Fin k) (p' : Fin l) :
      (rat q * (Matrix.of fun i j => X ⊗ₜ[D.host.F] C i j : Mx D m n) * rat e) p p' = X ⊗ₜ[D.host.F] (q * C * e) p p' := by
    have hinc : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun _ => rfl
    simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, hinc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, ← TensorProduct.tmul_sum]
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  obtain ⟨hcB, heB, sB, he'B⟩ := hF.hB ρ h
  set aJ := G.colDec (2 * ρ + 1) (by omega) (by omega) with haJ
  set aB := G.colDec (2 * ρ + 2) (by omega) h with haB
  obtain ⟨hAA, -⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hAb : G.pl.stAbar sc ≠ 0 := by
    intro h0
    apply hA
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h1 : star y ∈ G.pl.stAbar sc := (hconj _).2 (by rwa [star_star])
    have h2 := h0 _ h1
    rwa [star_eq_zero] at h2

  have hJ : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).qY *ᵥ t) p =
      star ((-D.host.xi0) ^ (p.1 + 1)) * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) := by
    intro t _
    simp only [HypDec.qY, heJ, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, colsOf, star_mul', Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
  have hJmem : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) ∈
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p).rev := by
    intro t ht
    have ht' : t ∈ aJ.lat (G.sp.P (2 * ρ + 1)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := by
      rw [haJ, ← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)]; exact ht
    exact auxiliaryCoordinate_mem_staircaseIdeal aJ _ _ ht' _ (by simp only [Fin.val_castLE]; omega)

  have hBmem : ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0),
      star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) ∈
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)⁻¹ := by
    intro s hs
    have hs' : s ∈ aB.lat (G.sp.P (2 * ρ + 2)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := by
      rw [haB, ← G.sp.colLat (2 * ρ + 2) (by omega) h]; exact hs
    have h1 := auxiliaryCoordinate_mem_staircaseIdeal aB _ _ hs' (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
      (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    exact ((GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ _).2 _).1 h1

  have hsc : star ((-D.host.xi0) ^ (p.1 + 1)) * sB p = 1 := by
    have h1 := congrFun (congrFun (F.dB ρ h).e'e p) p
    rw [he'B, heB, colsOf_gram, Matrix.one_apply_eq] at h1
    have h2 : (aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
        (Fin.castLE (by omega) p) = 1 := by
      rw [show aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a = antiDiagonalSignGramMatrix (2 * ρ + 2 - 1) (-1) from aB.gram]
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE]
      rw [ite_eq_left (by omega), ite_eq_right (fun e => by rw [Fin.ext_iff, Fin.val_rev, Fin.val_castLE] at e; omega)]
    rw [h2, mul_one] at h1
    have h3 := congrArg star h1
    rw [star_mul', star_star, star_one] at h3
    rw [mul_comm]; exact h3
  have hGB : ∀ i j, star ((G.V (.grid (2 * ρ + 2) 0)).gram j i) = (G.V (.grid (2 * ρ + 2) 0)).gram i j := fun i j =>
    (G.V (.grid (2 * ρ + 2) 0)).herm.eq ((G.V (.grid (2 * ρ + 2) 0)).frame j) ((G.V (.grid (2 * ρ + 2) 0)).frame i)

  have keyE : ∀ a ∈ D.host.AA, ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0),
      ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) *
        (F.dB ρ h).e') p p ∈ D.host.AA * G.pl.stAbar sc := by
    intro a ha s hs t ht
    rw [entry_rankOne _ _ a t (fun j => ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j), hJ t ht, he'B,
      negSp_gram, negPair_colsOf _ hGB]
    have e : a * (star ((-D.host.xi0) ^ (p.1 + 1)) *
          ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p)) *
        -(sB p * star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)) =
        -(a * (((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) := by
      linear_combination (-(a * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) * hsc
    rw [e]
    refine Submodule.neg_mem _ (FractionalIdeal.mul_mem_mul ha ?_)
    rw [← stairId_mul_inv_succ (G.pl.stA sc) (G.pl.stAbar sc) hA hAb (Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev
      (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev (by omega) (by simp only [Fin.val_rev, Fin.val_castLE]; omega)]
    exact FractionalIdeal.mul_mem_mul (hJmem t ht) (hBmem s hs)
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ((F.dJ ρ h).pY * (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j)) * (F.dB ρ h).jY) p p =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) *
          (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) * (F.dB ρ h).e') p p :=
      rat_tmul_entry _ _ _ _ _ _
    rw [key]
    exact tmul_mem_complId hα (keyE a ha s hs t ht)
  | zero => simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]; exact neg_mem hx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasePointCharacterTrivialOnDepthLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

theorem sympl_xZero {V V₀ W W₀ : HSp D} {ρ : ℕ} (dB : HypDec V V₀ ρ) (dJ : HypDec W W₀ ρ) (u : Mx D W.rank V.rank) :
    symplO V W (dB.extX W dJ.jX) (dB.extY W (u ⬝ dB.jY)) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * cA D ((dJ.pY ⬝ u ⬝ dB.jY).trace)) := by
  have h := dB.hO_ext W dJ.jX 0 0 (u ⬝ dB.jY) 0 0
  simp only [map_zero, add_zero, zero_add] at h
  rw [symplO, h]
  congr 2
  have e1 : gA W ⬝ dJ.jX = adj dJ.pY := by rw [dJ.pY_eq, adj_mul, adj_gA, adj_adj]
  simp only [pairS, hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, trace_zero, add_zero, e1]
  rw [← adj_mul, Matrix.mul_assoc]
  exact trace_adj _

end GlobalTheory.XCharBF

theorem GlobalTheory.AscFin.pcBF_xZero_char : OnStd fun {D} _ _ {sc} {G} W F =>
    ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1),
      W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
        ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)))
        ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  rw [show xZero (F.dJ ρ h) = (F.dJ ρ h).jX from rfl, GlobalTheory.XCharBF.sympl_xZero]
  refine GlobalTheory.T.psiE_xi0_mul_cA_eq_one_of_mem_complId W.ψ_std _ ?_
  rw [Matrix.trace]
  refine sum_mem fun p _ => ?_
  refine GlobalTheory.T.complementary_ideal_membership_criterion hq μ0 hL G _ (GlobalTheory.T.besselStep_diagonalCoordinates_mem_complementIdeal hF ρ h u hu.1 p) fun e he => ?_
  change e * ((F.dJ ρ h).pY ⬝ u ⬝ (F.dB ρ h).jY) p p ∈ complId D.host.AAbar
  have := GlobalTheory.T.completed_diagonal_coordinate_mem_completion_conj_AA hF ρ h (e • u) (hu.2 e he) p
  rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at this

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasePointCharacterTrivialOnDepthLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_point_character_trivial_on_depth_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h))) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  first | exact @GlobalTheory.AscFin.pcBF_xZero_char | exact GlobalTheory.AscFin.pcBF_xZero_char | (intros; apply GlobalTheory.AscFin.pcBF_xZero_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowDualPartFinitePairsTrivially
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowDualPartFinitePairsTrivially
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.BesIso

theorem symplO_negSp_eq {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have hinv : (-S.gram)⁻¹ = -S.gram⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det S)])
  have h : hO (negSp S) T x y = -hO S T x y := by
    simp only [hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  rw [symplO_eq, symplO_eq, h, mul_neg, map_neg]

theorem hO_extX_eq {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a : Mx D T.rank ρ) (u : WO S T) :
    hO S T (d.extX T a) u = hO S T (d.extX T a) (d.extY T (u ⬝ d.jY)) := by
  have hu : u = d.extX T (u ⬝ d.jX) + d.ext0 T (u ⬝ d.j0) + d.extY T (u ⬝ d.jY) := ((d.coordS T).symm_apply_apply u).symm
  have h1 := d.hO_ext T a (u ⬝ d.jX) 0 (u ⬝ d.jY) 0 (u ⬝ d.j0)
  have h2 := d.hO_ext T a 0 0 (u ⬝ d.jY) 0 0
  simp only [map_zero, add_zero, zero_add] at h1 h2
  rw [← hu] at h1
  rw [h1, h2]
  simp [pairS, hO]

end GlobalTheory.AscFin.BesIso


open GlobalTheory.AscFin.BesIso in
theorem GlobalTheory.AscFin.BesIso.splits_iso : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have sd : ∀ i, i ≤ D.R.m → 1 ≤ i → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := fun i hi h1 =>
    (G.isV (X := .grid i 0) ⟨hi, Nat.zero_le _⟩ (fun j hj => by injection hj with e1 e2; omega)).sd
  have sdV := isSelfDualC_neg (sd (2 * ρ + 2) h (by omega))
  have sdW := sd (2 * ρ + 1) (by omega) (by omega)
  have hmx : ∀ w, w ∈ latRow G (2 * ρ + 1) → MxAt (fun _ => True) w := fun w hw =>
    ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdV sdW (fun _ => True) w).1 hw.1).1
  refine ⟨fun i j => ?_, fun a ha => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hmx u hu i k)
  · have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdV sdW (fun _ => True) _ (hmx _ ha)).1 ha.1 u hu.1
    rw [symplO_negSp_eq, AddChar.map_neg_eq_inv, inv_eq_one] at key
    rw [symplO_eq] at key ⊢
    rw [← hO_extX_eq]
    exact key
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowDualPartFinitePairsTriviallyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_dualPart_finite_pairs_trivially : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  first | exact @GlobalTheory.AscFin.BesIso.splits_iso | exact GlobalTheory.AscFin.BesIso.splits_iso | (intros; apply GlobalTheory.AscFin.BesIso.splits_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiDepthLatticeSplits
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem pcBF_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  refine ⟨fun u hu => ?_⟩
  have e1 := ((F.dB ρ h).coordS (G.V (.grid (2 * ρ + 1) 0))).symm_apply_apply u
  have e2 := ((F.dJ ρ h).coordT (F.V₀ ρ)).symm_apply_apply (u ⬝ (F.dB ρ h).j0)
  obtain ⟨s1, -, s3⟩ := GlobalTheory.T.bessel_depth_lattice_splits_along_source_witt D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  obtain ⟨f4, i4⟩ := GlobalTheory.T.depthLatticeGridRow_dualPart_finite_pairs_trivially D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have b := GlobalTheory.T.depth_lattice_core_parts_mem_selfDual_lattice D hq T L μ0 hL sc G W M hM F hF ρ h _ s3
  refine ⟨u ⬝ (F.dB ρ h).jX, s1, u ⬝ (F.dB ρ h).jY, AddSubgroup.subset_closure ⟨f4, i4⟩,
    (F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0), b.1, (F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0), b.2,
    (F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0), GlobalTheory.T.bessel_depth_lattice_core_splits_along_target_witt D hq T L μ0 hL sc G W M hM F hF ρ h _ s3, ?_,
    GlobalTheory.T.base_point_character_trivial_on_depth_lattice D hq T L μ0 hL sc G W M hM F hF ρ h u hu, GlobalTheory.T.besselSecondBasePoint_character_trivial_depthLattice D hq T L μ0 hL sc G W M hM F hF ρ h u hu⟩
  have e2' : (F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0)) = (u ⬝ (F.dB ρ h).j0) := by
    simp only [HypDec.coordT, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e2
    exact (add_right_comm _ _ _).trans e2
  have e1' : (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) + (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) + (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) = u := by
    simp only [HypDec.coordS, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e1
    exact (add_right_comm _ _ _).trans e1
  rw [e2', e1']

end GlobalTheory.AscFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiDepthLatticeSplitsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToFourierJacobi_depthLattice_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  first | exact @GlobalTheory.AscFin.pcBF_splits | exact GlobalTheory.AscFin.pcBF_splits | (intros; apply GlobalTheory.AscFin.pcBF_splits <;> assumption)
end
