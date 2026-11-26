module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroOfAe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOfAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
public import Formalism.HermitianCurvature.StatementTop

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeAction
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrD

section Left

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}

theorem mem_left (hD : IsDom k r z z' (Fin.last r) D) {g h : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r (Fin.last r) ∩ D := by
  obtain ⟨hgG, hgD⟩ := hg
  refine ⟨?_, ?_⟩
  · simp only [Glev, UH, UWset, Set.mem_setOf_eq] at hgG hh ⊢
    refine ⟨?_, fun a ha => ?_⟩
    · rw [conjTranspose_mul]
      calc gᴴ * hᴴ * Hpk k r * (h * g) = gᴴ * (hᴴ * Hpk k r * h) * g := by simp only [Matrix.mul_assoc]
        _ = Hpk k r := by rw [hh.1, hgG.1]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, (hgG.2 a ha).1, (hgG.2 a ha).2]
      exact hh.2.1 a
  · have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
    have h1N : (1 : Mx k r) ∈ Nlev k r (Fin.last r) := by simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
    have hS := hD.2 g ⟨hgG, hgD⟩ h ⟨h, hh, 1, h1N, by simp⟩ 1 ⟨1, h1z', 1, h1N, by simp⟩
    simpa using hS

theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D) {g h : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have h1z : (1 : Mx k r) ∈ UWset k r z := by simp [UWset, UH]
  have h1z' : (1 : Mx k r) ∈ UWset k r z' := by simp [UWset, UH]
  simp only [FFl, Set.mem_setOf_eq] at hJ
  have e1 := hJ.2.2.2 g hg 1 h1z 1 h1z'
  have e2 := hJ.2.2.2 g hg h hh 1 h1z'
  rw [one_mul, mul_one, hπ.1] at e1
  have e1' : J g ∘SL π' 1 = J g := by
    ext x
    exact (congrArg (fun T => T x) e1).symm
  rw [mul_one] at e2
  rw [e2, e1']

theorem ld_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) : LdV X F g = (B.comp (dOp π X)).comp (J g) := by
  have hfun : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g) := by
    funext t
    have hu := exp_uw hX t
    rw [hF _ (mem_left hD hg hu), J_left hπ hJ hg hu, ContinuousLinearMap.comp_assoc]
  unfold LdV
  rw [hfun]
  have hd := dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g)).comp
      ((ContinuousLinearMap.compL ℂ Wp Wp Wp) B)).restrictScalars ℝ
  have key : HasDerivAt (fun t : ℝ => (B.comp (π (NormedSpace.exp ((t : ℂ) • X)))).comp (J g))
      ((B.comp (dOp π X)).comp (J g)) 0 := by
    have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    convert h2 using 1
    all_goals first | rfl | (ext; rfl)
  exact key.deriv

theorem lz_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (ecOp π Z)).comp (J g) := by
  unfold LZ
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp [ecOp]

theorem fold_left (hD : IsDom k r z z' (Fin.last r) D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ FFl k r z z' π π' (Fin.last r) D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, InLieW k r z (hpart1 (Hpk k r) p.2) ∧ InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r (Fin.last r) ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil => intro F B hF g hg v; simp [hF g hg]
  | cons p L ih =>
    intro F B hF g hg v
    obtain ⟨h1, h2⟩ := hL p (by simp)
    have hF' : ∀ g ∈ Glev k r (Fin.last r) ∩ D,
        (p.1 • F + LZ (Hpk k r) p.2 F) g = (p.1 • B + B.comp (ecOp π p.2)).comp (J g) := by
      intro g hg
      rw [Pi.add_apply, Pi.smul_apply, lz_left hD hπ hc hJ hF h1 h2 hg, hF g hg]
      ext x
      simp
    have := ih (fun q hq => hL q (by simp [hq])) _ _ hF' g hg v
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [this]
    simp [ecRep_eq hπ hc h1 h2]

end Left

end QrD

theorem left_type_action : Formalism.FourierDecayAlt.Q.LeftTypeAction := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D hz hz' hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  have key : ∀ σ : Equiv.Perm (Fin m), ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ v,
      ((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
          fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) J g v =
        (ContinuousLinearMap.id ℂ Wp)
          (((List.ofFn fun j => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0), unitB (Hpk k r) Bs (σ j) j)).map
            fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) :=
    fun σ => QrD.fold_left hD hπ hc hJ _ (by
      intro p hp
      simp only [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J (ContinuousLinearMap.id ℂ Wp) (fun g _ => by simp)
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul, ContinuousLinearMap.id_apply] at key
  simp only [id, Finset.sum_apply, Pi.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [key σ g hg v]

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.VanishingOfL2Equivariant
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 3200000

namespace Formalism.FourierDecayAlt.P

namespace UnipotentHaarMeasurability

open Formalism.FourierDecayAlt.ThreeDimData

theorem vanishing_of_L2_equivariant {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hBC : BeConv) (hIn : Inputs)
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq)
    {x : H} (hx : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {v : H} (hv : IsAdm σ w0 v)
    (hl : ∀ ξ : Wp, PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v ξ) = 0) :
    be z c π σ μW μN x v = 0 := by
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, hBC2, hBC3, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  ext ξ
  have hc : ContinuousOn (fun g => be z c π σ μW μN (σ g x) v ξ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hBC3 x hx v hv).clm_apply continuousOn_const
  have heq : ∀ hh ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      be z c π σ μW μN (σ (hh * n * g) x) v ξ = Formalism.QuantumDeterminants.psi k r z c n • π hh (be z c π σ μW μN (σ g x) v ξ) := by
    intro hh hhW n hn g hg
    have hhn : hh * n ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhW.1 hn.1
    have hm : σ (hh * n * g) = (σ (hh * n)).comp (σ g) := TranslationBesselVanishing.sigma_mul hσ hhn hg
    rw [hm, ContinuousLinearMap.comp_apply,
      hBC2 v hv hh hhW n hn (σ g x) (TranslationBesselVanishing.smooth_translate hσ hx hg)]
    rfl
  have h0 := aez hW hN hG hq (fun g => be z c π σ μW μN (σ g x) v ξ) hc heq (hl ξ) 1 Formalism.QuantumDeterminants.WeylGroupFacts.uh_one
  simpa [sigma_one hσ] using h0

theorem zeroCaseDD_of (hBC : BeConv) (hNI : NormIdSm) (hSch : SchurH) : ZeroCaseDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inl hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inl hv) ξ).1, hDD v hv v hv]
  simp

theorem zeroCase_of (hBC : BeConv) (hNI : NormIdSm) (hSch : SchurH) : ZeroCase := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS hDD v hv x hx
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨-, -, -, hBC4⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  have hA := zeroCaseDD_of hBC hNI hSch hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hDD
  have hvs : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := hIn.2.2.1 k r ε lam H σ hlam hσ v hv

  have hB : ∀ u ∈ DDsp σ w0, be z c π σ μW μN u v = 0 := by
    intro u hu
    have h1 : be z c π σ μW μN v u = 0 := hA u hu v hvs
    have h2 := (hBC4 u hu v (Or.inr hv)).2
    rw [h1] at h2
    have h3 := congrArg ContinuousLinearMap.adjoint h2
    rwa [ContinuousLinearMap.adjoint_adjoint, map_zero] at h3

  have hw0n : ‖w0‖ = 1 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    exact hn1
  have hw0ne : w0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hw0n; exact zero_ne_one hw0n
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hdeg : PI.BesselPeriodGGP.fdegH μG σ w0 = d := DDSmoothness.fdeg_eq hd hSd hw0ne
  have hw0DD : w0 ∈ DDsp σ w0 := by
    refine Submodule.subset_span ⟨1, Formalism.QuantumDeterminants.WeylGroupFacts.uh_one, ?_⟩
    simp [sigma_one hσ]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := DDSmoothness.DD_smooth hIn.2.2.1 hlam hσ hw0 w0 hw0DD
  have hmu := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hC : ∀ ξ : Wp, ⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ = 0 := by
    intro ξ
    obtain ⟨hNv, him, hre⟩ := hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS w0 hw0s v (Or.inr hv) ξ
    have hL : PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g w0) v ξ) = 0 := by
      unfold PI.BesselPeriodGGP.l2SG
      refine (lintegral_congr_ae (hae.mono fun g hg => ?_)).trans lintegral_zero
      have hgD : σ (Matrix.of g) w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨Matrix.of g, hg, rfl⟩
      simp [hB _ hgD]
    rw [hL, hdeg, hw0n] at hNv
    have h0 : 1 ^ 2 * (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re / d ≤ 0 := ENNReal.ofReal_eq_zero.mp hNv.symm
    have hre0 : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re = 0 := by
      have : (⟪ξ, be z c π σ μW μN v v ξ⟫_ℂ).re ≤ 0 := by
        rw [one_pow, one_mul] at h0
        exact (div_nonpos_iff.mp h0).elim (fun h => absurd h.2 (not_le.mpr hd)) (fun h => h.1)
      linarith
    exact Complex.ext hre0 him
  have hvv : be z c π σ μW μN v v = 0 := by
    have hlin : (be z c π σ μW μN v v : Wp →ₗ[ℂ] Wp) = 0 := by
      rw [← inner_map_self_eq_zero]
      intro ξ
      rw [← inner_conj_symm]
      simp [hC ξ]
    ext ξ
    have := LinearMap.congr_fun hlin ξ
    simpa using this

  refine vanishing_of_L2_equivariant hBC hIn hS hx (Or.inr hv) (fun ξ => ?_)
  rw [(hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inr hv) ξ).1, hvv]
  simp

end UnipotentHaarMeasurability

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDecomposition
open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BigCellDecomposition

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF

def CellDecomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), ∀ g ∈ GV k r, (∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ n ∈ Nset k r, ∃ n' ∈ Nset k r, ∃ c : Fin r → ℂ, (∀ a, c a ≠ 0) ∧
      ∃ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k ∧ g = n⁻¹ * bigCell k r c μ * n'

variable {k r : ℕ}

theorem bigCell_one_fixes_vector {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) : bigCell k r c 1 *ᵥ z = z := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  have key : ∀ j, bigCell k r c 1 i j * z j = if j = i then z i else 0 := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
      split_ifs with h
      · subst h
        exact (hz _ hj).symm
      · rfl
    · have hj1 : ¬ j.val < r := by omega
      have hj2 : j.val ≤ r + k := by omega
      simp only [bigCell, dif_neg hj1, dif_pos hj2]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · simp only [dif_pos hi, Matrix.one_apply]
        by_cases hij : j = i
        · subst hij
          simp
        · have hne : (⟨i.val - r, by omega⟩ : Fin (k + 1)) ≠ ⟨j.val - r, by omega⟩ := by
            intro h
            apply hij
            ext
            simp only [Fin.mk.injEq] at h
            omega
          simp [hne, hij]
      · simp only [dif_neg hi, zero_mul]
        rw [if_neg]
        rintro rfl
        omega
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp

theorem n_inv_S {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n⁻¹ ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw z, n⁻¹, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn, (one_mul _).symm⟩

theorem n_S {z : Fin (2 * r + k + 1) → ℂ} {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw z, n, hn, (one_mul n).symm⟩

end Formalism.FourierDecayAlt.P.BigCellDecomposition

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF

theorem jf_psiOnto_of_cellDecomp (hCD : BigCellDecomposition.CellDecomp) : Formalism.FourierDecayAlt.JF.PsiOnto := by
  intro k r Wp Wq _ _ _ _ D g hg
  obtain ⟨n, hn, n', hn', c, hc, μ, hμ, rfl⟩ := hCD k r D.z D.z' g hg.1 hg.2.1
  set ζ := herm (Hb k) (μ *ᵥ wbPart k r D.z') (wbPart k r D.z) with hζdef
  have hmin := bigCellMinors k r D.z D.z' c μ D.z_mem D.z'_mem

  have hG : 0 < Gf k r D.z D.z' (bigCell k r c μ) := by
    have := hg.2.2
    rwa [gInv k r D.z D.z' D.z_mem D.z'_mem _ (BigCellDecomposition.n_inv_S hn) _ (BigCellDecomposition.n_S hn')] at this
  have hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq ζ := by
    have hz := hmin.2.2 hc
    rw [BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem] at hz
    have hr := hmin.1 (Fin.last r)
    set P := Dmin k r D.z D.z' (bigCell k r c μ) ⟨r, by omega⟩ with hP
    have hP0 : P ≠ 0 := by
      have : P = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1)) = ζ * P := by
      unfold zeta at hz
      rw [← hP] at hz
      have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r c μ) (Fin.last (r + 1))) hP0
      rw [hz] at h2
      exact h2.symm
    unfold Gf at hG
    rw [hlast, ← hP, Complex.normSq_mul] at hG
    have h1 : 0 < Complex.normSq P := Complex.normSq_pos.2 hP0
    nlinarith

  have hfac := bruhat_big_cell_factorization k r c μ
  have huw := unipotent_weyl_properties k r
  have hm : embWb k r μ ∈ UWb k r := TwoByOneBlock.emb_mem_UWb hμ
  have hmz : herm (Hpk k r) (embWb k r μ *ᵥ D.z') D.z = ζ := by
    have e1 : embWb k r μ *ᵥ D.z' = bigCell k r c μ *ᵥ D.z' := by
      rw [hfac.2, ← Matrix.mulVec_mulVec, BigCellDecomposition.bigCell_one_fixes_vector D.z'_mem]
    rw [e1, BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem]
  obtain ⟨h, hh, h', hh', hmeq⟩ := b2_rank_one_coord k r D.z D.z' D.μsec D.k_pos D.z_mem D.z'_mem D.T_pos
    D.T'_pos D.sec (embWb k r μ) hm (by rw [hmz]; exact hζ)
  rw [hmz] at hmeq
  have hu1 := WeylGroupFacts.isUnit_of_uh hh.1
  have hu2 := WeylGroupFacts.isUnit_of_uh hh'.1
  have hun := WeylGroupFacts.isUnit_of_uh hn.1
  have hcomm : bigCell k r c 1 * h⁻¹ = h⁻¹ * bigCell k r c 1 :=
    (huw.2.2 c h⁻¹ (huw.2.1 D.z (BigCellInversePair.uw_inv hh))).symm

  refine ⟨((h, h * n * h⁻¹), (h', h' * n' * h'⁻¹)), ⟨hh,
      (uWNormal k r D.z D.z_mem h hh n hn).1, hh', (uWNormal k r D.z' D.z'_mem h' hh' n' hn').1⟩,
    (c, ζ), ⟨hc, hζ⟩, ?_⟩
  show n⁻¹ * bigCell k r c μ * n' = h⁻¹ * (h * n * h⁻¹)⁻¹ * bigCell k r c (D.μsec ζ) * (h' * n' * h'⁻¹) * h'
  rw [hfac.1, hmeq, (bruhat_big_cell_factorization k r c (D.μsec ζ)).1]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu1]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu2, Matrix.mul_one]
  rw [← Matrix.mul_assoc (bigCell k r c 1) h⁻¹, hcomm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu1]

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.Sq2UnitOfEqOneOfSq2EqDiv
open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def utv {k r m : ℕ} (ε T : ℝ) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ) (g : Mat k r) : Fin m → ℂ :=
  fun a => (Real.sqrt T : ℂ) * (Phh ε ((Gp g : ℝ) : ℂ) * om g a)

lemma utv_eq {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (Gp : Mat k r → ℝ) (om : Mat k r → Fin m → ℂ)
    {g : Mat k r} (hg : ε / 2 < Gp g) : C6.unitOf T (Gp g) (om g) = utv ε T Gp om g := by
  have hx : 0 < Gp g := by linarith
  funext a
  simp only [C6.unitOf, utv, Phh, hh, Complex.ofReal_re, sc_one hε hg.le, one_mul, Pi.smul_apply,
    smul_eq_mul, sqrt_div_eq hT hx, Complex.ofReal_mul]
  ring

lemma utv_cd {k r m : ℕ} {ε T : ℝ} (hε : 0 < ε) {Gp : Mat k r → ℝ} {om : Mat k r → Fin m → ℂ}
    (hG : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ))) (ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a)) :
    ContDiff ℝ ∞ (utv ε T Gp om) := by
  refine contDiff_pi.2 fun a => ?_
  simp only [utv]
  exact contDiff_const.mul (((Phh_cd hε).comp hG).mul (ho a))

lemma sq2_unitOf_eq_one_of_sq2_eq_div {m : ℕ} {T Gv : ℝ} (hT : 0 < T) (hG : 0 < Gv) {v : Fin m → ℂ} (hv : C6.sq2 v = Gv / T) :
    C6.sq2 (C6.unitOf T Gv v) = 1 := by
  unfold C6.sq2 C6.unitOf at *
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum, hv, Real.mul_self_sqrt (div_nonneg hT.le hG.le), div_mul_div_comm, mul_comm T Gv,
    div_self (mul_pos hG hT).ne']

lemma continuous_sum_squares (m : ℕ) : Continuous (C6.sq2 (m := m)) := by
  unfold C6.sq2
  exact continuous_finsetSum _ fun a _ => Complex.continuous_normSq.comp (continuous_apply a)

lemma norm_le_one_of_sq2_eq_one {m : ℕ} {v : Fin m → ℂ} (h : C6.sq2 v = 1) : ‖v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  have h1 : Complex.normSq (v a) ≤ 1 := by
    rw [← h]
    unfold C6.sq2
    exact Finset.single_le_sum (f := fun a => Complex.normSq (v a)) (fun i _ => Complex.normSq_nonneg _)
      (Finset.mem_univ a)
  have h2 : ‖v a‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1
  nlinarith [norm_nonneg (v a)]

lemma spheres_compact (m m' : ℕ) :
    IsCompact {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_eq ((continuous_sum_squares m).comp continuous_fst) continuous_const).inter
      (isClosed_eq ((continuous_sum_squares m').comp continuous_snd) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : (Fin m → ℂ) × (Fin m' → ℂ))) (r := 1)).subset ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_prod_le_iff.2 ⟨norm_le_one_of_sq2_eq_one hw.1, norm_le_one_of_sq2_eq_one hw.2⟩

lemma bump_ext {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (K O : Set F) (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (Pi : F → E) (hPi : ContDiffOn ℝ ∞ Pi O) :
    ∃ Φ : F → E, ContDiff ℝ ∞ Φ ∧ (∀ y ∈ K, Φ y = Pi y) ∧
      ∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B := by
  obtain ⟨V, hVo, hKV, hVO, -⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, F)) hVo.isClosed_compl
    hK.isClosed (disjoint_compl_left_iff_subset.2 hKV)
  have hχ : ContDiff ℝ ∞ (χ : F → ℝ) := contMDiff_iff_contDiff.1 χ.contMDiff
  have hΦ : ContDiff ℝ ∞ (fun y => χ y • Pi y) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact hχ.contDiffAt.smul (hPi.contDiffAt (hO.mem_nhds hx))
    · have hx' : x ∈ (closure V)ᶜ := fun h => hx (hVO h)
      have h0 : (fun y => χ y • Pi y) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
        have hyV : y ∈ Vᶜ := fun h => hy (subset_closure h)
        simp [hχ0 hyV]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  refine ⟨fun y => χ y • Pi y, hΦ, fun y hy => by simp [hχ1 hy], fun j => ?_⟩
  exact hK.exists_bound_of_continuousOn
    ((hΦ.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).continuousOn)

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem c6_fib_cost_of_pieces : C6.FibCostOfParts := by
  intro hU k r m m' om om' Gp T T' E _ _ Pi O hom hom' hGp hT hT' hsq hsq' hO hKO hPi ε hε i
  have hGcd : ContDiff ℝ ∞ (fun g => ((Gp g : ℝ) : ℂ)) := (poly_adm (n := 0) hGp).1
  have hGc : Continuous Gp := by
    have h := Complex.continuous_re.comp hGcd.continuous
    simp only [Function.comp_def, Complex.ofReal_re] at h
    exact h
  have ho : ∀ a, ContDiff ℝ ∞ (fun g => om g a) := fun a => (poly_adm (n := 0) (hom a)).1
  have ho' : ∀ a, ContDiff ℝ ∞ (fun g => om' g a) := fun a => (poly_adm (n := 0) (hom' a)).1
  have hu1 : ContDiff ℝ ∞ (utv ε T Gp om) := utv_cd hε hGcd ho
  have hu2 : ContDiff ℝ ∞ (utv ε T' Gp om') := utv_cd hε hGcd ho'
  have hψ : ContDiff ℝ ∞ (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) := hu1.prodMk hu2
  have hOε : IsOpen {g : Mat k r | ε / 2 < Gp g} := isOpen_lt continuous_const hGc

  have hsph : ∀ g ∈ GV k r, ε / 2 < Gp g →
      C6.unitOf T (Gp g) (om g) = utv ε T Gp om g ∧ C6.unitOf T' (Gp g) (om' g) = utv ε T' Gp om' g ∧
      (C6.unitOf T (Gp g) (om g), C6.unitOf T' (Gp g) (om' g)) ∈
        {w : (Fin m → ℂ) × (Fin m' → ℂ) | C6.sq2 w.1 = 1 ∧ C6.sq2 w.2 = 1} := by
    intro g hg hgt
    have hpos : 0 < Gp g := by linarith
    exact ⟨utv_eq hε hT Gp om hgt, utv_eq hε hT' Gp om' hgt, sq2_unitOf_eq_one_of_sq2_eq_div hT hpos (hsq g hg),
      sq2_unitOf_eq_one_of_sq2_eq_div hT' hpos (hsq' g hg)⟩
  obtain ⟨Φ, hΦ, hΦK, hΦb⟩ := bump_ext _ O (spheres_compact m m') hO hKO Pi hPi

  have hwl : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
      ∀ x ∈ wL u ++ wR v, inLie k r x.2 := by
    intro u v hu hv x hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [wL, List.mem_map] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hu X hX).1
    · simp only [wR, List.mem_map, List.mem_reverse] at hx
      obtain ⟨X, hX, rfl⟩ := hx
      exact (hv X hX).1
  have hlen : ∀ u v : List (Mat k r), (wL u ++ wR v).length = u.length + v.length := by
    intro u v
    simp [wL, wR]
  choose C1 hC1 using hU k r m om Gp T hom hGp hT hsq ε hε
  choose C2 hC2 using hU k r m' om' Gp T' hom' hGp hT' hsq' ε hε
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ j ∈ Finset.range (i + 1), (|C1 j| + |C2 j|) := ⟨_, rfl⟩
  have hCM : ∀ j ≤ i, C1 j ≤ M ∧ C2 j ≤ M := by
    intro j hj
    have hmem : j ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum (f := fun j => |C1 j| + |C2 j|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hmem
    rw [← hM] at hle
    exact ⟨by linarith [le_abs_self (C1 j), abs_nonneg (C2 j)], by linarith [le_abs_self (C2 j), abs_nonneg (C1 j)]⟩
  have H : ∀ w, admitted i w → w ≠ [] → ∀ g ∈ {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g},
      ‖Dw w (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g‖ ≤
        M * gN g ^ (2 * (r + 1) * w.length + (r + 1)) := by
    rintro w ⟨u, v, hu, hv, hl, rfl⟩ - g ⟨hg, hge⟩
    have hgt : ε / 2 < Gp g := by linarith
    have hw := hwl u v hu hv
    have huv : C6.UnitWords k r u v (u.length + v.length) := ⟨hu, hv, rfl⟩
    have e1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T (Gp g') (om g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).1).symm) g hg hgt
    have e2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        Dw (wL u ++ wR v) (fun g' => C6.unitOf T' (Gp g') (om' g')) g :=
      Dw_congr_loc hw hOε (fun g' hg' hg'O => ((hsph g' hg' hg'O).2.1).symm) g hg hgt
    have f1 : Dw (wL u ++ wR v) (utv ε T Gp om) g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).1 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.fst ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have f2 : Dw (wL u ++ wR v) (utv ε T' Gp om') g =
        (Dw (wL u ++ wR v) (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) g).2 := by
      have h := congrFun (dw_clm (ContinuousLinearMap.snd ℝ (Fin m → ℂ) (Fin m' → ℂ)) (wL u ++ wR v) hψ) g
      simpa using h
    have b1 := hC1 _ u v huv g hg hge
    have b2 := hC2 _ u v huv g hg hge
    rw [dLR_eq, ← e1, f1] at b1
    rw [dLR_eq, ← e2, f2] at b2
    have hexp : (r + 1) * (2 * (u.length + v.length) + 1) =
        2 * (r + 1) * (wL u ++ wR v).length + (r + 1) := by
      rw [hlen]; ring
    rw [hexp] at b1 b2
    have hY : 0 ≤ gN g ^ (2 * (r + 1) * (wL u ++ wR v).length + (r + 1)) :=
      pow_nonneg (le_trans zero_le_one (gN_ge_one hg)) _
    obtain ⟨m1, m2⟩ := hCM _ hl
    rw [Prod.norm_def]
    exact max_le (b1.trans (mul_le_mul_of_nonneg_right m1 hY)) (b2.trans (mul_le_mul_of_nonneg_right m2 hY))
  obtain ⟨C, -, hC⟩ := fdb (fun g => (utv ε T Gp om g, utv ε T' Gp om' g)) hψ
    {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gp g} _
    (fun g hg => by rw [← (hsph g hg.1 (by linarith [hg.2])).1, ← (hsph g hg.1 (by linarith [hg.2])).2.1]
                    exact (hsph g hg.1 (by linarith [hg.2])).2.2)
    gN (fun g hg => gN_ge_one hg.1) (2 * (r + 1)) (r + 1) M i H i E Φ hΦ hΦb
  refine ⟨C, fun u v huv g hg hge => ?_⟩
  have hw := hwl u v huv.1 huv.2.1
  rw [dLR_eq]
  have e : Dw (wL u ++ wR v) (fun g' => Pi (C6.unitOf T (Gp g') (om g'), C6.unitOf T' (Gp g') (om' g'))) g =
      Dw (wL u ++ wR v) (fun g' => Φ (utv ε T Gp om g', utv ε T' Gp om' g')) g := by
    refine Dw_congr_loc hw hOε (fun g' hg' hg'O => ?_) g hg (show ε / 2 < Gp g by linarith)
    obtain ⟨h1, h2, h3⟩ := hsph g' hg' hg'O
    rw [← hΦK _ h3, h1, h2]
  rw [e]
  have hl : (wL u ++ wR v).length = i := by rw [hlen]; exact huv.2.2
  have hb := hC (wL u ++ wR v) (admissible_of_unit_words huv) hl.le g ⟨hg, hge⟩
  rw [hl] at hb
  have hexp : (2 * (r + 1) + (r + 1)) * i = 3 * (r + 1) * i := by ring
  rwa [hexp] at hb

theorem fibre_cost_estimate : C6.FibCost := c6_fib_cost_of_pieces fibre_unit_normalization

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CellSmoothness
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CellSmoothness

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma contDiffOn_gq (D : RealPlaceData k r Wp Wq) : ContDiffOn ℝ ∞ (fun q => gq D q) (QDom k r D.z D.z') := by
  refine Formalism.FourierDecayAlt.P.Ux10.cdm_iff.2 fun i j => ?_
  simp only [gq, bigCell]
  split_ifs with h1 h2 h3 h4 h5
  · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) (⟨j.val, h1⟩ : Fin r)).comp
      (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff.contDiffOn
  · exact contDiffOn_const
  · exact (D.sec.1 _ _).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
  · exact contDiffOn_const
  · refine ContDiffOn.inv ?_ ?_
    · exact (Complex.conjCLE.contDiff.comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
        (⟨2 * r + k - j.val, by omega⟩ : Fin r)).comp (ContinuousLinearMap.fst ℝ (Fin r → ℂ) ℂ)).contDiff).contDiffOn
    · intro q hq
      simpa using hq.1 _
  · exact contDiffOn_const

end Formalism.FourierDecayAlt.P.CellSmoothness
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopPSD
open Formalism.FourierDecayAlt NumberField MeasureTheory
open scoped ComplexOrder

namespace Formalism.FourierDecayAlt.P

theorem top_positive_semidefinite : Top.TopPSDT := by
  intro Wp Wq _ _ _ _ _ P l0 T ν' m₀ Θ TP f χ admitted ε hε w hw hne Y
  unfold TB.PSDOn
  set F := D.cutF T.base χ f ε
  set dd := Top.dH P l0 (Formalism.QuantumDeterminants.Tz P.k P.r T.base.z * Formalism.QuantumDeterminants.Tz P.k P.r T.base.z') w

  let X : Wd.Ix (Fin w.length) → M.Ty P → C.LPt → (Wq →L[ℂ] Wp) :=
    fun e ρ p => (TP.E ρ).comp (D.vecV T.base ν' m₀ (Θ.Θ w e F) p)
  let g : Wd.Ix (Fin w.length) → M.Ty P → Matrix Y Y ℂ := fun e ρ =>
    Matrix.of fun x y => ((dd (x : C.LPt) e ρ * dd (y : C.LPt) e ρ : ℝ) : ℂ) * B.hsInner (X e ρ x) (X e ρ y)
  have hterm : ∀ e ρ, (g e ρ).PosSemidef := by
    intro e ρ
    let v : Y → _ := fun x => ((dd (x : C.LPt) e ρ : ℝ) : ℂ) • B.hsVec (X e ρ x)
    have h := (Matrix.posSemidef_gram ℂ v).transpose
    have heq : g e ρ = (Matrix.gram ℂ v).transpose := by
      ext x y
      simp only [g, v, Matrix.of_apply, Matrix.transpose_apply, Matrix.gram_apply, inner_smul_left,
        inner_smul_right, B.hsInner, Complex.conj_ofReal]
      push_cast
      ring
    rw [heq]
    exact h
  have hsum : (Matrix.of fun x y : Y => Top.topOf P l0 T ν' m₀ Θ TP F w x y) = ∑ e, ∑ ρ, g e ρ := by
    ext x y
    simp [g, X, dd, Top.topOf, Matrix.sum_apply]
  rw [hsum]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun e _ => ?_)
  exact Finset.sum_induction _ Matrix.PosSemidef (fun _ _ ha hb => ha.add hb) Matrix.PosSemidef.zero
    (fun ρ _ => hterm e ρ)

end Formalism.FourierDecayAlt.P
end
