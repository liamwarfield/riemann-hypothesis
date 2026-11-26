module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.RenameBlockSingleVariableSeries
public import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.PlaceSeriesJetsOneLetterOrbits
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMModelS
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.IntegralSeriesOneLetter
section -- merged from Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.JetCountingProofs.IntegralCombinationHolds
open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.L2.DIV Formalism.DworkPowerSeriesWeights
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension cm4)
open Formalism.L2.Th1.Top (kappa_integral ltNormExists uniformGaussModels_fact_variant frameExistsH)

theorem integralFree_holds : HostIntFree := by
  intro a₀ b₀ c₀ dK ha hdK hOK l _ h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨hsq, hmod, hcm⟩ := Formalism.L2.Th1.Top.HAux.data ha hdK hOK
  obtain ⟨s2, hs2, ⟨c, hc, e2, e3, es⟩, hN⟩ := Formalism.L2.Th1.D.nrcmOfCM4 cm4 dK (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK)
    hsq hmod hcm l h5 hd hin ι g2 g3 ε hg hε hth
  obtain ⟨lam, hlam, hLT⟩ := ltNormExists l _ ι g2 g3 s2 ε c hc hε e2 e3 es
  refine ⟨s2, lam, hlam, hs2, hLT, fun σ F hσ hF => ⟨h5, hg.2.2.1, hg.2.2.2.1, hε, hth, hσ, hF, hN σ hσ, hg.2.2.2.2.1⟩, ?_⟩
  intro n _ _ h Λ g₀ hLat
  obtain ⟨κ, k1, k2, k3, hθ⟩ := uniformGaussModels_fact_variant a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ g₀ hLat
  refine ⟨κ, k1, k2, k3, fun θ hθm hten => ?_⟩
  obtain ⟨g₁, i1, i2, hK1⟩ := hθ θ hθm hten l h5 ι
  refine ⟨g₁, i1, i2, fun σ hσ => frameExistsH a₀ b₀ c₀ dK ha hdK lam hlam hOK l h5 hd hin ι σ hσ n h Λ g₀ g₁
    hLat i1 i2, ?_⟩
  intro t N hN0 hlN ht σ hσ hFe γ B' hFr
  obtain ⟨F, hF⟩ := hFe
  exact kappa_integral l h5 g2 g3 ε s2 hg.2.2.1 hg.2.2.2.1 hε hth σ hσ F hF (hN σ hσ) n _ γ hFr.1
    (hK1 g2 g3 ε s2 hLT hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hε hth t N hN0 hlN ht σ γ B' hFr)

end Formalism.L2.DIV.C
end
end

namespace Formalism.L2.DIV.C

theorem hostIntFree : HostIntFree := integralFree_holds

end Formalism.L2.DIV.C
end

section -- merged from Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.ScaledNorms.GcmHostPf
open scoped BigOperators ComplexConjugate

noncomputable section

namespace Formalism.L2.DIV.C.X

open Formalism.L2.DIV Formalism.L2.DIV.C
open Formalism.L2.Th1.H (Sesq IsHerm IsSemiChar altE opU alphaQ qOf fixedBy dualLat IsReps sumU inter relIdx imgLat pow4
  slice stdH stdLat matH blk4 F0 prodFn kernel4 tens4 Th IsSelfDual IsIsom cmL)
open Formalism.L2.Th1.F (scalePair)
open Formalism.L2.Th1.Top (kappa_integral local_kappa_shape_holds frameExistsH)

section Transport

variable {V : Type} [AddCommGroup V] [Module ℂ V] {c : ℂ}

theorem gcm_mem_map_smul (hc : c ≠ 0) (A : AddSubgroup V) (x : V) :
    x ∈ A.map (DistribSMul.toAddMonoidHom V c) ↔ c⁻¹ • x ∈ A := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [DistribSMul.toAddMonoidHom_apply, inv_smul_smul₀ hc]
    exact hy
  · intro h
    exact ⟨c⁻¹ • x, h, by rw [DistribSMul.toAddMonoidHom_apply, smul_inv_smul₀ hc]⟩

theorem gcm_relIdx_map_smul (hc : c ≠ 0) (A B : AddSubgroup V) :
    relIdx (A.map (DistribSMul.toAddMonoidHom V c)) (B.map (DistribSMul.toAddMonoidHom V c)) = relIdx A B :=
  AddSubgroup.relIndex_map_map_of_injective A B fun _ _ hxy => smul_right_injective V hc hxy

variable {H H' : Sesq V}

theorem gcm_opU_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (x : V) (F : V → ℂ) (z : V) :
    opU H' x (fun w => F (c⁻¹ • w)) z = opU H (c⁻¹ • x) F (c⁻¹ • z) := by
  simp only [opU]
  rw [hH', hH', smul_add]

theorem gcm_alphaQ_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (r : ℝ) (x : V) :
    alphaQ r H' x = alphaQ r H (c⁻¹ • x) := by
  simp only [alphaQ, qOf]
  rw [hH']

theorem gcm_altE_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (x y : V) :
    altE H' x y = altE H (c⁻¹ • x) (c⁻¹ • y) := by
  simp only [altE]
  rw [hH']

theorem gcm_isHerm_scale (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (hH : IsHerm H) : IsHerm H' := by
  intro x y
  rw [hH', hH', hH]

theorem gcm_semi_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) {M : AddSubgroup V}
    {β : V → ℂ} (hβ : IsSemiChar H M β) :
    IsSemiChar H' (M.map (DistribSMul.toAddMonoidHom V c)) (fun x => β (c⁻¹ • x)) := by
  refine ⟨fun x hx => hβ.1 _ ((gcm_mem_map_smul hc M x).1 hx), fun x hx y hy => ?_⟩
  show β (c⁻¹ • (x + y)) = β (c⁻¹ • x) * β (c⁻¹ • y) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H' x y : ℂ))
  rw [smul_add, gcm_altE_scale hH']
  exact hβ.2 _ ((gcm_mem_map_smul hc M x).1 hx) _ ((gcm_mem_map_smul hc M y).1 hy)

theorem gcm_fixed_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) {S : AddSubgroup V}
    {β : V → ℂ} {F : V → ℂ} (hF : F ∈ fixedBy H β S) :
    (fun w => F (c⁻¹ • w)) ∈ fixedBy H' (fun x => β (c⁻¹ • x)) (S.map (DistribSMul.toAddMonoidHom V c)) := by
  intro x hx z
  show β (c⁻¹ • x) * opU H' x (fun w => F (c⁻¹ • w)) z = F (c⁻¹ • z)
  rw [gcm_opU_scale hH']
  exact hF _ ((gcm_mem_map_smul hc S x).1 hx) _

theorem gcm_reps_scale (hc : c ≠ 0) [DecidableEq V] {A B : AddSubgroup V} {R : Finset V} (hR : IsReps A B R) :
    IsReps (A.map (DistribSMul.toAddMonoidHom V c)) (B.map (DistribSMul.toAddMonoidHom V c))
      (R.image (fun x => c • x)) := by
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    rw [gcm_mem_map_smul hc, inv_smul_smul₀ hc]
    exact hR.1 x' hx'
  · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
    rw [gcm_mem_map_smul hc, ← smul_sub, inv_smul_smul₀ hc] at hxy
    rw [hR.2.1 x' hx' y' hy' hxy]
  · obtain ⟨x, hx, hyx⟩ := hR.2.2 (c⁻¹ • y) ((gcm_mem_map_smul hc B y).1 hy)
    refine ⟨c • x, Finset.mem_image_of_mem _ hx, ?_⟩
    rw [gcm_mem_map_smul hc, smul_sub, inv_smul_smul₀ hc]
    exact hyx

theorem gcm_dualLat_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (Λ : AddSubgroup V) :
    dualLat H' (Λ.map (DistribSMul.toAddMonoidHom V c)) = (dualLat H Λ).map (DistribSMul.toAddMonoidHom V c) := by
  ext x
  rw [gcm_mem_map_smul hc]
  show (∀ y ∈ Λ.map (DistribSMul.toAddMonoidHom V c), ∃ m : ℤ, altE H' x y = (m : ℝ)) ↔
    (∀ y ∈ Λ, ∃ m : ℤ, altE H (c⁻¹ • x) y = (m : ℝ))
  constructor
  · intro hx y hy
    have := hx (c • y) ((gcm_mem_map_smul hc Λ _).2 (by rw [inv_smul_smul₀ hc]; exact hy))
    rwa [gcm_altE_scale hH', inv_smul_smul₀ hc] at this
  · intro hx y hy
    rw [gcm_altE_scale hH']
    exact hx _ ((gcm_mem_map_smul hc Λ y).1 hy)

theorem gcm_inter_scale (hc : c ≠ 0) (hH' : ∀ u v, H' u v = H (c⁻¹ • u) (c⁻¹ • v)) (hH : IsHerm H)
    {S M : AddSubgroup V} {β : V → ℂ} {F : V → ℂ} (hβ : IsSemiChar H M β) (hF : F ∈ fixedBy H β S)
    (hidx : relIdx S M ≠ 0) (w : V) :
    inter H' (fun x => β (c⁻¹ • x)) (S.map (DistribSMul.toAddMonoidHom V c)) (M.map (DistribSMul.toAddMonoidHom V c))
      (fun v => F (c⁻¹ • v)) w = inter H β S M F (c⁻¹ • w) := by
  classical
  obtain ⟨⟨R, hR⟩, -⟩ := Formalism.L2.Th1.H.repsExist V S M hidx
  rw [Formalism.L2.Th1.H.interReps V H' (gcm_isHerm_scale hH' hH) _ _ _ (gcm_semi_scale hc hH' hβ) _
      (gcm_fixed_scale hc hH' hF) _ (gcm_reps_scale hc hR) w,
    Formalism.L2.Th1.H.interReps V H hH S M β hβ F hF R hR (c⁻¹ • w), gcm_relIdx_map_smul hc]
  congr 1
  simp only [sumU]
  rw [Finset.sum_image fun _ _ _ _ hxy => smul_right_injective V hc hxy]
  refine Finset.sum_congr rfl fun x _ => ?_
  show β (c⁻¹ • c • x) * opU H' (c • x) (fun v => F (c⁻¹ • v)) w = β x * opU H x F (c⁻¹ • w)
  rw [gcm_opU_scale hH', inv_smul_smul₀ hc]

end Transport

section Forms

theorem gcm_inv_mul_conj (c : ℂ) : (c⁻¹ * conj c⁻¹ : ℂ) = ((Complex.normSq c : ℝ) : ℂ)⁻¹ := by
  rw [map_inv₀, ← mul_inv, Complex.mul_conj]

theorem gcm_matH_scale {m : Type} [Fintype m] (c : ℂ) (M : Matrix m m ℂ) (u v : m → ℂ) :
    matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • M) u v = matH M (c⁻¹ • u) (c⁻¹ • v) := by
  rw [(Formalism.L2.Th1.H.matHBasic m _).1, (Formalism.L2.Th1.H.matHBasic m M).1, ← gcm_inv_mul_conj c]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul]
  ring

theorem blockFour_smul {n : Type} (k : ℂ) (h : Matrix n n ℂ) : blk4 (k • h) = k • blk4 h := by
  funext w w'
  simp only [blk4, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem gcm_stdH_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (m : Type) [Fintype m] [DecidableEq m]
    (u v : m → ℂ) : stdH (scalePair L c hc) m u v = stdH L m (c⁻¹ • u) (c⁻¹ • v) := by
  rw [(Formalism.L2.Th1.H.stdHBasic _ m).1, (Formalism.L2.Th1.H.stdHBasic L m).1]
  have hA := (Formalism.L2.Th1.F.homogeneity L c hc).2.2.2.2.2.1
  have key : (c⁻¹ * conj c⁻¹ : ℂ) = ((‖c‖ : ℂ) ^ 2)⁻¹ := by
    rw [map_inv₀, ← mul_inv, Complex.mul_conj']
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Formalism.L2.Th1.F.herm, hA, Pi.smul_apply, smul_eq_mul, map_mul, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.ofReal_pow, mul_inv]
  rw [← key]
  ring

theorem gcm_stdLat_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (m : Type) :
    stdLat (scalePair L c hc) m = (stdLat L m).map (DistribSMul.toAddMonoidHom (m → ℂ) c) := by
  ext x
  rw [gcm_mem_map_smul hc]
  simp only [stdLat, AddSubgroup.mem_pi, Submodule.mem_toAddSubgroup, (Formalism.L2.Th1.F.homogeneity L c hc).1,
    Pi.smul_apply, smul_eq_mul]

theorem gcm_imgLat_scale {W : Type} [AddCommGroup W] [Module ℂ W] {n : Type} (c : ℂ) (hc : c ≠ 0)
    (g : (Fin 4 × n → ℂ) →ₗ[ℂ] W) (Λ : AddSubgroup (n → ℂ)) :
    imgLat g (pow4 (Λ.map (DistribSMul.toAddMonoidHom (n → ℂ) c))) =
      (imgLat g (pow4 Λ)).map (DistribSMul.toAddMonoidHom W c) := by
  ext x
  rw [gcm_mem_map_smul hc]
  simp only [imgLat, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ∀ a, slice a y ∈ Λ.map (DistribSMul.toAddMonoidHom (n → ℂ) c) := hy
    refine ⟨c⁻¹ • y, fun a => (gcm_mem_map_smul hc Λ _).1 (hy' a), ?_⟩
    simp
  · rintro ⟨y, hy, hyx⟩
    have hy' : ∀ a, slice a y ∈ Λ := hy
    refine ⟨c • y, fun a => (gcm_mem_map_smul hc Λ _).2 ?_, ?_⟩
    · have : c⁻¹ • slice a (c • y) = slice a y := by
        funext i
        simp only [slice, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ hc]
      rw [this]
      exact hy' a
    · simp only [LinearMap.toAddMonoidHom_coe] at hyx ⊢
      rw [map_smul, hyx, smul_inv_smul₀ hc]

theorem periodF0_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (m : Type) [Fintype m]
    (w : m → ℂ) : F0 (scalePair L c hc) (c * ω₀) m w = F0 L ω₀ m (c⁻¹ • w) := by
  simp only [F0, prodFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h9 := (Formalism.L2.Th1.F.homogeneity L c hc).2.2.2.2.2.2.2.2.1 (ω₀ / 2) (c⁻¹ * w i)
  rw [mul_inv_cancel_left₀ hc] at h9
  rw [show c * ω₀ / 2 = c * (ω₀ / 2) by ring, h9]
  rfl

theorem gcm_scalePair_scalePair (L : PeriodPair) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    scalePair (scalePair L a ha) b hb = scalePair L (a * b) (mul_ne_zero ha hb) := by
  show PeriodPair.mk _ _ _ = PeriodPair.mk _ _ _
  congr 1
  · show b * (a * L.ω₁) = _
    ring
  · show b * (a * L.ω₂) = _
    ring

theorem gcm_kernel4_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (r : ℝ) {n : Type} [Fintype n]
    [DecidableEq n] (Λ : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hβ : IsSemiChar (stdH L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))
      (alphaQ r (stdH L (Fin 4 × n))))
    (hF : F0 L ω₀ (Fin 4 × n) ∈ fixedBy (stdH L (Fin 4 × n)) (alphaQ r (stdH L (Fin 4 × n))) (stdLat L (Fin 4 × n)))
    (hidx : relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (z : Fin 4 × n → ℂ) :
    kernel4 (scalePair L c hc) (c * ω₀) (Λ.map (DistribSMul.toAddMonoidHom (n → ℂ) c))
      (alphaQ r (stdH (scalePair L c hc) (Fin 4 × n))) g z =
    kernel4 L ω₀ Λ (alphaQ r (stdH L (Fin 4 × n))) g (c⁻¹ • z) := by
  have hH' := gcm_stdH_scale L c hc (Fin 4 × n)
  have hα : alphaQ r (stdH (scalePair L c hc) (Fin 4 × n)) = fun x => alphaQ r (stdH L (Fin 4 × n)) (c⁻¹ • x) :=
    funext (gcm_alphaQ_scale hH' r)
  have hF0 : F0 (scalePair L c hc) (c * ω₀) (Fin 4 × n) = fun w => F0 L ω₀ (Fin 4 × n) (c⁻¹ • w) :=
    funext (periodF0_scale L c hc ω₀ (Fin 4 × n))
  simp only [kernel4]
  rw [gcm_stdLat_scale, gcm_imgLat_scale c hc, hα, hF0, map_smul]
  exact gcm_inter_scale hc hH' (Formalism.L2.Th1.H.stdHBasic L (Fin 4 × n)).2.1 hβ hF hidx _

end Forms

end Formalism.L2.DIV.C.X
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.DefsMMCoord
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

def CoordTieA : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), IotaExt lam ι → ∀ s : VC D 1 1,
      (AlgEnt D (U D B.tor s (B.thZero 1 1)) →
        pSer D lam (U D B.tor s (B.thZero 1 1)) =
          liftT D (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
            (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))
              (fun τ => s τ 0 0) B.thMM)))) ∧
      (TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) s →
        ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (N : ℂ) • (fun τ => s τ 0 0) ∈ B.lamM)

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.NotSquareOfJacobiNegOne
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

theorem oneCopyTh1S_of (h1 : ScaleLTB) (h2 : IsomONB) (h3 : ScaleInt) : OneCopyTh1S := by
  intro D cc δ B hcc hδ p _ h5 hin lam ι hι
  obtain ⟨c, hc, g2, g3, ε, s2, hLT, hg2, hg3, hD, hε, hth, hNR⟩ := h1 D cc δ B hcc hδ p h5 hin ι
  obtain ⟨g₁, e, σ, γ, B', σp, hg, hU, hF, hσp, hONB⟩ := h2 D cc δ B hcc hδ p h5 hin lam ι hι
  refine ⟨c, hc, g2, g3, ε, s2, σp, Fintype.card D.what₂.Tau,
    fun i k => B' k.1 ((Fintype.equivFin D.what₂.Tau).symm i), Fintype.equivFin D.what₂.Tau,
    hLT, hg2, hg3, hD, hε, hth, hσp, hONB, ?_⟩
  intro t N hN hpN ht
  have key := h3 D cc δ B hcc hδ p h5 hin ι c hc g2 g3 ε s2 hLT hg2 hg3 hD hε hth g₁ e hg σ hU (hNR σ hU) γ B' hF
    t N hN hpN ht
  simpa using key

theorem oneCopyLoc_ofS (hLE : LamExt) (hT : OneCopyTh1S) (hC : CoordTie) (hM : ModelTieS) (hR : ReadChangeS) :
    OneCopyLoc := by
  intro D cc δ B hcc hδ p _ hp hin lam
  obtain ⟨ι, hι⟩ := hLE p lam
  obtain ⟨c, hc, g2, g3, ε, s2, σ, r, v, e, hLT, h2, h3, hΔ, hε, hS, hσ, hv, hInt⟩ :=
    hT D cc δ B hcc hδ p hp hin lam ι hι
  refine ⟨σ, r, v, hσ, hv, fun s hs => ?_⟩
  obtain ⟨hpser, N, hN, hNp, hNt⟩ := hC D cc δ B hcc hδ p hp hin lam ι hι s hs
  intro C wq hCm hwq
  obtain ⟨hph0, h, Uu, h0, hhi, h1, hlog, hUu, hexp⟩ :=
    hM D cc δ B hcc hδ p hp hin lam ι hι c hc g2 g3 ε s2 hLT h2 h3 hΔ hε hS C wq hCm hwq
  rw [hpser]
  exact hR D p hp lam B.tor.abelian₂ C wq _ h Uu ((ι c)⁻¹) hph0 h0 hhi h1 hlog hUu hexp r v e _
    (hInt (fun τ => s τ 0 0) N hN hNp hNt)

theorem not_dvd_of_jacobi_neg_one (p : ℕ) [Fact p.Prime] (d : ℕ) (hj : jacobiSym (-(d : ℤ)) p = -1) : ¬ p ∣ d := by
  intro h
  have h0 : ((-(d : ℤ) : ℤ) : ZMod p) = 0 := by
    have : ((d : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).2 h
    push_cast; simp [this]
  have hl : legendreSym p (-(d : ℤ)) = 0 := (legendreSym.eq_zero_iff p _).2 h0
  rw [jacobiSym.legendreSym.to_jacobiSym] at hl
  rw [hl] at hj; norm_num at hj

theorem not_square_of_jacobi_neg_one (p : ℕ) [Fact p.Prime] (d : ℕ) (hj : jacobiSym (-(d : ℤ)) p = -1) :
    ¬ ∃ a : ZMod p, a ^ 2 = -(d : ZMod p) := by
  rintro ⟨a, ha⟩
  have hne : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have hl : legendreSym p (-(d : ℤ)) = 0 := (legendreSym.eq_zero_iff p _).2 h0
    rw [jacobiSym.legendreSym.to_jacobiSym] at hl
    rw [hl] at hj; norm_num at hj
  have hsq : IsSquare ((-(d : ℤ) : ℤ) : ZMod p) := ⟨a, by push_cast; rw [← ha]; ring⟩
  have hl : legendreSym p (-(d : ℤ)) = 1 := (legendreSym.eq_one_iff p hne).2 hsq
  rw [jacobiSym.legendreSym.to_jacobiSym] at hl
  rw [hl] at hj; norm_num at hj

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem scale_lattice_bound : ScaleLTB := by
  intro D cc δ B hcc hδ p _ h5 hj ι
  obtain ⟨a₀, g, b₀, c₀, ha, hd, hl, B', hcm, -, hIs, hlat, -⟩ := ReBase.theta_change_of_base D cc δ B hcc
  have hnd := not_dvd_of_jacobi_neg_one p D.host.d hj
  have hin := not_square_of_jacobi_neg_one p D.host.d hj
  obtain ⟨hsq, hmod, hCM⟩ := Formalism.L2.Th1.Top.HAux.data ha hd hcm
  obtain ⟨g2, g3, ε, hgood, hε, hth⟩ := Formalism.L2.Th1.Top.modelInert _ _ hsq hmod hCM p h5 hnd hin ι
  obtain ⟨s2, lam, hlam, -, hLT, hCur, -⟩ :=
    Formalism.L2.DIV.C.hostIntFree a₀ b₀ c₀ _ ha hd hcm p h5 hnd hin ι g2 g3 ε hgood hε hth
  obtain ⟨σ0, F, -, -, -, -, hU0, hF, -⟩ := Formalism.L2.Th1.Top.InhA.joint p h5 1 0 0
  have hc : lam / ((g : ℂ) * δ) ≠ 0 := div_ne_zero hlam hl
  have hL : (Formalism.L2.Th1.F.scalePair B.L (lam / ((g : ℂ) * δ)) hc).lattice =
      (Formalism.L2.Th1.H.cmL a₀ b₀ D.host.d ha hd lam hlam).lattice := by
    have hB' : B'.L = Formalism.L2.Th1.H.cmL a₀ b₀ D.host.d ha hd ((g : ℂ) * δ) hl := hIs.1
    ext z
    rw [Formalism.L2.Th1.F.Homog.mem_scale, ← hlat, hB', Formalism.L2.Th1.H.cmL, Formalism.L2.Th1.H.cmL,
      Formalism.L2.Th1.F.Homog.mem_scale, Formalism.L2.Th1.F.Homog.mem_scale]
    have e : ((g : ℂ) * δ)⁻¹ * ((lam / ((g : ℂ) * δ))⁻¹ * z) = lam⁻¹ * z := by
      field_simp
      exact mul_div_cancel_left₀ z hl
    rw [e]
  have hC0 := hCur σ0 F hU0 hF
  obtain ⟨-, hg2, hg3, -, -, -, -, -, hD⟩ := hC0
  refine ⟨lam / ((g : ℂ) * δ), hc, g2, g3, ε, s2, (ReBase.isLTNorm_congr hL p ι g2 g3 s2 ε).2 hLT, hg2, hg3, hD, hε, hth, ?_⟩
  intro σ hU α hα hσα
  exact (hCur σ F hU hF).2.2.2.2.2.2.2.1 α hα hσα

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMScale
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.KerInert

namespace MMScale

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual StdData Th alphaQ kernel4 tens4)
open Formalism.L2.DIV.C.X (gcm_mem_map_smul gcm_relIdx_map_smul gcm_opU_scale gcm_alphaQ_scale gcm_dualLat_scale gcm_matH_scale
  blockFour_smul gcm_stdH_scale gcm_stdLat_scale gcm_imgLat_scale gcm_scalePair_scalePair gcm_kernel4_scale)

theorem thetaU_smul {K : Type} [Field K] (ι : ℂ →+* K) {lg : PowerSeries K}
    (hlg : PowerSeries.constantCoeff lg = 0) {n : Type} [Fintype n] [DecidableEq n] (B' : Matrix n n K)
    (s : ℂ) (G : (n → ℂ) → ℂ) (hG : AnalyticAt ℂ G 0) :
    Formalism.L2.Th1.H.thetaU ι lg B' (fun z => G (s • z)) =
      MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (ι s * B' i j) * (at1 j lg : MvPowerSeries n K))
        (MvPowerSeries.map ι (Formalism.L2.Th1.H.taylorMv G)) := by
  have ha : MvPowerSeries.HasSubst (fun i => ∑ j, MvPowerSeries.C (B' i j) * (at1 j lg : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      Formalism.L2.Th1.H.FormalGroupLawNegation.cc_lin (B' i) fun j => Formalism.L2.Th1.E.CompatibleChartOperations.constantCoeff_inVar_eq_zero j hlg
  have hb : MvPowerSeries.HasSubst (fun i => ∑ j, MvPowerSeries.C (((Matrix.diagonal fun _ : n => s).map ι) i j) *
      (MvPowerSeries.X j : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      Formalism.L2.Th1.H.FormalGroupLawNegation.cc_lin _ fun j => MvPowerSeries.constantCoeff_X _
  have hmv : (fun z : n → ℂ => G (s • z)) = fun w => G ((Matrix.diagonal fun _ : n => s).mulVec w) := by
    funext w
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  unfold Formalism.L2.Th1.H.thetaU
  rw [hmv, Formalism.L2.Th1.H.taylorMvComp n n _ G hG, Formalism.L2.Th1.H.FormalGroupLawNegation.map_linSubst]
  unfold Formalism.L2.Th1.H.linSubst
  rw [MvPowerSeries.subst_comp_subst_apply hb ha]
  congr 1
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum, Finset.sum_eq_single i]
  · rw [map_mul, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C, MvPowerSeries.subst_X ha, Matrix.map_apply,
      Matrix.diagonal_apply_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← map_mul]
  · intro j _ hj
    rw [Matrix.map_apply, Matrix.diagonal_apply_ne _ (Ne.symm hj), map_zero, map_zero, zero_mul, map_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem stdData_cm {a₀ : ℕ} {b₀ c₀ : ℤ} {d : ℕ} (ha : 0 < a₀) (hd : 0 < d) {lam : ℂ} (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ d) {L : PeriodPair} (hL : L.lattice = (cmL a₀ b₀ d ha hd lam hlam).lattice)
    {ω₀ : ℂ} (hω : (ω₀ - lam * a₀) / 2 ∈ (cmL a₀ b₀ d ha hd lam hlam).lattice) (hn : ω₀ / 2 ∉ L.lattice)
    {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hiso : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hsd : IsSelfDual (matH h) Λ) (hst : ∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ d • x ∈ Λ)
    (i1 : relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (i2 : relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (stdLat L (Fin 4 × n)) ≠ 0) :
    StdData L ω₀ h Λ (alphaQ (Real.sqrt d / 2) (matH h)) (alphaQ (Real.sqrt d / 2) (stdH L (Fin 4 × n))) g := by
  rw [KS.stdH_congr hL] at hiso ⊢
  rw [ReBase.stdLat_congr hL] at i1 i2
  exact ReBase.stdData_congr hL hω hn
    (Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g hiso hsd hst i1 i2)

end MMScale

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual StdData Th alphaQ kernel4 tens4)
open Formalism.L2.DIV.C.X (gcm_mem_map_smul gcm_relIdx_map_smul gcm_opU_scale gcm_alphaQ_scale gcm_dualLat_scale gcm_matH_scale
  blockFour_smul gcm_stdH_scale gcm_stdLat_scale gcm_imgLat_scale gcm_scalePair_scalePair gcm_kernel4_scale)

theorem scale_integrality : ScaleInt := by
  intro D cc δ B hcc hδ p _ h5 hj ι c hc g2 g3 ε s2 hLT hg2 hg3 hdisc hε hth g₁ e hI σ hσ hN γ B' hFr t N hN0 hpN ht
  obtain ⟨hiso, hndvd, i2, he, hten⟩ := hI
  obtain ⟨a₀, gg, b₀, c₀, ha, hd, hl, B'', hcm, -, hIs, hlat, -, -, -, hω, -, -⟩ :=
    ReBase.theta_change_of_base D cc δ B hcc
  have i1 : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
      (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0 := by
    intro h0
    exact hndvd (h0 ▸ dvd_zero p)

  have hLB : B.L.lattice = (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ) hl).lattice := by
    rw [← hlat, hIs.1]
  have hωB : (B.ω₀ - (gg : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ) hl).lattice := by
    rw [← hIs.2, ← hIs.1, hlat]
    exact hω
  have hsd := Kap.kap_selfDual_lamM B hcc hδ
  have hst := Kap.kap_stable_lamM B b₀ (Kap.kap_odd hcm)

  have S1 : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L D.what₂.Tau)))
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) g₁ :=
    MMScale.stdData_cm ha hd hl hcm hLB hωB (Base.half_not_mem B) _ _ g₁ hiso hsd hst i1 i2

  have hH' := gcm_matH_scale c (hOne B.L D.what₂.Tau)
  have hcmL : cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ * c) (mul_ne_zero hl hc) =
      Formalism.L2.Th1.F.scalePair (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ) hl) c hc :=
    (gcm_scalePair_scalePair _ ((gg : ℂ) * δ) c hl hc).symm
  have hL2 : (Formalism.L2.Th1.F.scalePair B.L c hc).lattice =
      (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ * c) (mul_ne_zero hl hc)).lattice := by
    rw [hcmL]
    ext z
    rw [(Formalism.L2.Th1.F.homogeneity _ c hc).1, (Formalism.L2.Th1.F.homogeneity _ c hc).1, hLB]
  have hω2 : (c * B.ω₀ - (gg : ℂ) * δ * c * a₀) / 2 ∈
      (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ * c) (mul_ne_zero hl hc)).lattice := by
    rw [hcmL, (Formalism.L2.Th1.F.homogeneity _ c hc).1]
    have e1 : c⁻¹ * ((c * B.ω₀ - (gg : ℂ) * δ * c * a₀) / 2) = (B.ω₀ - (gg : ℂ) * δ * a₀) / 2 := by
      field_simp
    rw [e1]
    exact hωB
  have hn2 : c * B.ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair B.L c hc).lattice := by
    rw [(Formalism.L2.Th1.F.homogeneity _ c hc).1]
    have e1 : c⁻¹ * (c * B.ω₀ / 2) = B.ω₀ / 2 := by
      field_simp
    rw [e1]
    exact Base.half_not_mem B
  have hiso2 : IsIsom (matH (blk4 (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau)))
      (stdH (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau))
      (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    rw [gcm_stdH_scale, blockFour_smul, gcm_matH_scale]
    have := hiso (c⁻¹ • x) (c⁻¹ • y)
    rw [map_smul (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) c⁻¹ x,
      map_smul (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) c⁻¹ y] at this
    exact this
  have hsd2 : IsSelfDual (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau))
      (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c)) := by
    show Formalism.L2.Th1.H.dualLat _ _ = _
    rw [gcm_dualLat_scale hc hH', hsd]
  have hst2 : ∀ x ∈ B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c),
      Formalism.L2.Th1.F.cmTheta b₀ D.host.d • x ∈ B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c) := by
    intro x hx
    rw [gcm_mem_map_smul hc] at hx ⊢
    rw [smul_comm]
    exact hst _ hx
  have j1 : relIdx (stdLat (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau))
      (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c)))) =
      relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
        (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) := by
    rw [gcm_stdLat_scale, gcm_imgLat_scale _ hc, gcm_relIdx_map_smul hc]
  have j2 : relIdx (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c))))
      (stdLat (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau)) =
      relIdx (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
        (stdLat B.L (Fin 4 × D.what₂.Tau)) := by
    rw [gcm_stdLat_scale, gcm_imgLat_scale _ hc, gcm_relIdx_map_smul hc]
  have S2 := MMScale.stdData_cm ha hd (mul_ne_zero hl hc) hcm hL2 hω2 hn2 _ _ g₁ hiso2 hsd2 hst2
    (j1 ▸ i1) (j2 ▸ i2)

  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have hmem : B.thMM ∈ Th (matH (hOne B.L D.what₂.Tau)) (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L D.what₂.Tau)))
      B.lamM := hspec.1
  have hmem2 : (fun x => B.thMM (c⁻¹ • x)) ∈ Th (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau)))
      (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c)) := by
    refine ⟨fun z _ => ?_, fun x hx z => ?_⟩
    · have hlin : AnalyticAt ℂ (fun w : D.what₂.Tau → ℂ => c⁻¹ • w) z :=
        (analyticAt_id (𝕜 := ℂ)).const_smul (c := c⁻¹)
      exact AnalyticAt.comp (f := fun w : D.what₂.Tau → ℂ => c⁻¹ • w) (hmem.1 (c⁻¹ • z) (Set.mem_univ _)) hlin
    · show alphaQ _ (matH _) x * Formalism.L2.Th1.H.opU (matH _) x (fun w => B.thMM (c⁻¹ • w)) z = B.thMM (c⁻¹ • z)
      rw [gcm_alphaQ_scale hH', gcm_opU_scale hH']
      exact hmem.2 _ ((gcm_mem_map_smul hc B.lamM x).1 hx) _
  have hF1 := (Formalism.L2.Th1.H.product_theta_mem' _ B.ω₀ (Fin 4 × D.what₂.Tau) S1.per S1.half _ S1.betaStd).1.2
  have hten2 : tens4 (fun x => B.thMM (c⁻¹ • x)) = e • kernel4 (Formalism.L2.Th1.F.scalePair B.L c hc) (c * B.ω₀)
      (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c))
      (alphaQ (Real.sqrt D.host.d / 2) (stdH (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau))) g₁ := by
    funext z
    have ht0 : tens4 (fun x => B.thMM (c⁻¹ • x)) z = tens4 B.thMM (c⁻¹ • z) := rfl
    rw [ht0, hten, Pi.smul_apply, Pi.smul_apply, gcm_kernel4_scale _ c hc _ _ B.lamM g₁ S1.betaSemi hF1 i1]
    rfl
  have ht2 : (N : ℂ) • (c • t) ∈ B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c) := by
    rw [gcm_mem_map_smul hc, smul_comm, inv_smul_smul₀ hc]
    exact ht

  have hK := Formalism.L2.Th1.Top.local_kappa_shape_holds p h5 _ ι g2 g3 ε s2 hLT hg2 hg3 hdisc hε hth (c * B.ω₀) S2.per S2.half
    D.what₂.Tau _ _ _ _ g₁ S2 (by rw [j1]; exact hndvd) e he _ hmem2 hten2 (c • t) N hN0 hpN ht2 σ γ B' hFr
  obtain ⟨σ0, F, -, -, -, -, -, hF, -⟩ := Formalism.L2.Th1.Top.InhA.joint p h5 1 0 0
  have hInt := Formalism.L2.Th1.Top.kappa_integral p h5 g2 g3 ε s2 hg2 hg3 hε hth σ hσ F hF hN D.what₂.Tau _ γ hFr.1 hK

  have hGan : AnalyticAt ℂ (Formalism.L2.Th1.H.opU (matH (hOne B.L D.what₂.Tau)) t B.thMM) 0 :=
    Formalism.L2.Th1.H.opUAnalytic (D.what₂.Tau → ℂ) (matH (hOne B.L D.what₂.Tau)) t B.thMM hmem.1 0 (Set.mem_univ _)
  have hfun : Formalism.L2.Th1.H.opU (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau)) (c • t)
      (fun x => B.thMM (c⁻¹ • x)) = fun z => Formalism.L2.Th1.H.opU (matH (hOne B.L D.what₂.Tau)) t B.thMM (c⁻¹ • z) := by
    funext z
    rw [gcm_opU_scale hH', inv_smul_smul₀ hc]
  have hread : Formalism.L2.Th1.Top.thetaH p ι B' (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau) (c • t)
      (fun x => B.thMM (c⁻¹ • x)) =
      ReadTh1 p (fun τ j => (ι c)⁻¹ * B' τ j)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
          (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (matH (hOne B.L D.what₂.Tau)) t B.thMM))) := by
    unfold Formalism.L2.Th1.Top.thetaH ReadTh1
    rw [hfun, MMScale.thetaU_smul (ι : ℂ →+* ℂ_[p]) (Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF p (by omega)) B' c⁻¹ _ hGan]
    simp only [RingEquiv.coe_toRingHom, map_inv₀]
  rw [← hread]
  exact hInt

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMReadS
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

open ParameterChangeLemmas IntegralOrthonormalChange

theorem change_of_parameters_const_scale : ReadChangeS := by
  intro D p _ hp lam Λ C wq ph h Uu κ hph0 h0 hhi h1 hlog hUu hexp r v e F hInt
  obtain ⟨g, g0, gI, hg⟩ := exists_inv h h0 hhi h1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨S, hSi⟩ : ∃ S : Fin r → MvPowerSeries D.what₂.Tau ℂ_[p],
      ∀ i, S i = PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p]) h :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S', hS'i⟩ : ∃ S' : D.what₂.Tau → MvPowerSeries (Fin r) ℂ_[p],
      ∀ j, S' j = PowerSeries.subst (MvPowerSeries.X (e j) : MvPowerSeries (Fin r) ℂ_[p]) g :=
    ⟨_, fun _ => rfl⟩
  have hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 := fun i => by rw [hSi]; exact constantCoeff_inVar_eq_zero _ h h0
  have hS'0 : ∀ j, MvPowerSeries.constantCoeff (S' j) = 0 := fun j => by rw [hS'i]; exact constantCoeff_inVar_eq_zero _ g g0
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  have hS's : MvPowerSeries.HasSubst S' := MvPowerSeries.hasSubst_of_constantCoeff_zero hS'0
  have hh : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' g0
  have hl0 := flog_constantCoeff (C • wModel lam Λ) wq

  have hA : MvPowerSeries.subst S (atLogV D lam Λ C wq v (liftT D F)) =
      ReadTh1 p (fun τ j => κ * v (e j) (τ, 0, 0)) F := by
    have hXfl : ∀ i : Fin r, MvPowerSeries.constantCoeff (PowerSeries.subst
        (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) = 0 :=
      fun i => constantCoeff_inVar_eq_zero i _ hl0
    have hΦ : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin 1 × Fin 1 =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i k) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hXfl]
    have hΦ' : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i (τ, 0, 0)) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hXfl]
    have hL : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun τ => MvPowerSeries.constantCoeff_X _)
    unfold atLogV liftT ReadTh1
    try dsimp only
    rw [MvPowerSeries.subst_comp_subst_apply hL hΦ]
    simp only [MvPowerSeries.subst_X hΦ]
    rw [MvPowerSeries.subst_comp_subst_apply hΦ' hSs]
    congr 1
    funext τ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hSs, map_sum]
    simp only [map_mul, AlgHom.commutes, MvPowerSeries.coe_substAlgHom, subst_single_var S hSs]
    refine (Fintype.sum_equiv e _ _ fun j => ?_).symm
    rw [hSi, e.symm_apply_apply, ← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X j)]
    unfold Formalism.InvariantFactorPaths.G7.at1
    have key := congrArg (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p])) hlog
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X j), PowerSeries.subst_mul (PowerSeries.HasSubst.X j),
      PowerSeries.subst_C, PowerSeries.subst_C] at key
    have hid : ∀ x : ℂ_[p], algebraMap ℂ_[p] ℂ_[p] x = x := fun _ => rfl
    simp only [MvPowerSeries.algebraMap_apply, hid] at key ⊢
    first
      | linear_combination (MvPowerSeries.C (v (e j) (τ, 0, 0)) : MvPowerSeries D.what₂.Tau ℂ_[p]) * key
      | linear_combination (-(MvPowerSeries.C (v (e j) (τ, 0, 0)) : MvPowerSeries D.what₂.Tau ℂ_[p])) * key

  have hB : MvPowerSeries.subst S (ePh lam Λ C wq r) =
      (∏ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) Uu) *
        Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries D.what₂.Tau ℂ_[p]) := by
    have hfac : ∀ i : Fin r, MvPowerSeries.subst S
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (ePhi1 lam Λ C wq))⁻¹ =
        PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p])
          (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p])) := by
      intro i
      rw [← subst_inv _ (MvPowerSeries.constantCoeff_X i) (ePhi1 lam Λ C wq), subst_single_var S hSs, hSi,
        ← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X _), hexp]
    unfold ePh
    rw [if_neg hp2, ← MvPowerSeries.coe_substAlgHom hSs, map_prod]
    simp only [MvPowerSeries.coe_substAlgHom, hfac]
    rw [Fintype.prod_equiv e.symm
      (fun i => PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p])
        (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p])))
      (fun j => PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p])
        (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p]))) (fun _ => rfl)]
    simp only [PowerSeries.subst_mul (PowerSeries.HasSubst.X _)]
    rw [Finset.prod_mul_distrib]
    congr 1
    have hph : ∀ j : D.what₂.Tau, MvPowerSeries.constantCoeff
        (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) ph) = 0 :=
      fun j => constantCoeff_inVar_eq_zero j ph hph0
    change _ = Formalism.L2.Th1.C.mvExp (∑ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) ph)
    rw [Formalism.L2.Th1.C.mvExp_sum _ _ (fun j _ => hph j)]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact Formalism.L2.Th1.C.subst_mvExp hph0 (MvPowerSeries.constantCoeff_X j)

  have hSG : IntegralMv (MvPowerSeries.subst S (atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r)) := by
    rw [← MvPowerSeries.coe_substAlgHom hSs, map_mul, MvPowerSeries.coe_substAlgHom, hA, hB]
    have hInt' : IntegralMv (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries D.what₂.Tau ℂ_[p]) *
        ReadTh1 p (fun τ j => κ * v (e j) (τ, 0, 0)) F) := hInt
    have hU : IntegralMv (∏ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) Uu) :=
      integral_prod _ _ fun j _ => integral_subst_single_variable j Uu hUu
    have := integral_mul hU hInt'
    convert this using 1
    ring

  have hback : MvPowerSeries.subst S' (MvPowerSeries.subst S
      (atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r)) =
      atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r := by
    rw [MvPowerSeries.subst_comp_subst_apply hSs hS's]
    have hid : (fun i => MvPowerSeries.subst S' (S i)) = MvPowerSeries.X := by
      funext i
      rw [hSi, subst_single_var S' hS's, hS'i, e.apply_symm_apply,
        ← PowerSeries.subst_comp_subst_apply hgs (PowerSeries.HasSubst.X i), hg,
        PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
    rw [hid, MvPowerSeries.subst_self]
    rfl
  rw [← hback]
  exact integral_subst S' hS'0 (fun j => by rw [hS'i]; exact integral_subst_single_variable _ g gI) hSG

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMCoord
noncomputable section

namespace Formalism.L2.KerInert

namespace MMCoord

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def inclCL (D : D7) : (D.what₂.Tau → ℂ) →L[ℂ] VC D 1 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v τ _ _ => v τ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem inclCL_apply (v : D.what₂.Tau → ℂ) : inclCL D v = fun τ _ _ => v τ := rfl

theorem translate_theta_coordinates (B : Base D cc δ) (s₁ v : D.what₂.Tau → ℂ) :
    U D B.tor (fun τ _ _ => s₁ τ) (B.thZero 1 1) (fun τ _ _ => v τ) =
      Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) s₁ B.thMM v := by
  have hA : Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  have hT : B.tor.abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := rfl
  simp only [U, Formalism.MainNotions.TaylorLogMetric.Hf, Base.thZero, tensPow, Formalism.L2.Th1.H.opU, Formalism.L2.Th1.H.matH, LinearMap.mk₂'ₛₗ_apply, hOne,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.univ_unique, Finset.sum_singleton,
    Finset.prod_singleton, hT, hA]
  congr 1
  have e1 : ∀ w : D.what₂.Tau → ℂ, ∑ x, w x * ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (s₁ x) =
      (∑ x, w x * (starRingEnd ℂ) (s₁ x)) / ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) := fun w => by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e1]

theorem u_incl (B : Base D cc δ) (s : VC D 1 1) (v : D.what₂.Tau → ℂ) :
    U D B.tor s (B.thZero 1 1) (inclCL D v) =
      Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM v := by
  have hs : s = fun τ _ _ => s τ 0 0 := by
    funext τ i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  have h := translate_theta_coordinates B (fun τ => s τ 0 0) v
  rw [← hs] at h
  exact h

def projM (D : D7) : Matrix D.what₂.Tau (D.what₂.Tau × Fin 1 × Fin 1) ℂ :=
  Matrix.of fun τ k => if k = (τ, 0, 0) then 1 else 0

theorem projM_mulVec (w : D.what₂.Tau × Fin 1 × Fin 1 → ℂ) : (projM D).mulVec w = fun τ => w (τ, 0, 0) := by
  funext τ
  simp [projM, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_eq']

theorem flat_eq (w : D.what₂.Tau × Fin 1 × Fin 1 → ℂ) :
    Formalism.L2.AlgTh.flat D.what₂.Tau 1 1 w = inclCL D ((projM D).mulVec w) := by
  rw [projM_mulVec, inclCL_apply]
  funext τ i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  rfl

theorem linSubst_projM (T : MvPowerSeries D.what₂.Tau ℂ) :
    Formalism.L2.Th1.H.linSubst (projM D) T =
      MvPowerSeries.subst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) T := by
  unfold Formalism.L2.Th1.H.linSubst
  congr 1
  funext τ
  simp [projM, apply_ite MvPowerSeries.C, ite_mul, Finset.sum_ite_eq']

theorem map_subst_liftT {p : ℕ} [Fact p.Prime] (h : ℂ →+* ℂ_[p]) (T : MvPowerSeries D.what₂.Tau ℂ) :
    MvPowerSeries.map h (MvPowerSeries.subst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) T) =
      liftT D (MvPowerSeries.map h T) := by
  have ha : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
      (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) :=
    MvPowerSeries.HasSubst.X_comp (fun τ : D.what₂.Tau => ((τ, 0, 0) : D.what₂.Tau × Fin 1 × Fin 1))
  rw [MvPowerSeries.map_subst ha]
  unfold liftT
  congr 1
  funext τ
  simp [MvPowerSeries.map_X]

end MMCoord

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical MMCoord

theorem coordinates_one_theta_algebraic : CoordTieA := by
  intro D cc δ B _ _ p _ lam ι hι s
  refine ⟨fun hG => ?_, fun hs => ?_⟩
  · have hgG : Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM =
        fun v => U D B.tor s (B.thZero 1 1) (inclCL D v) := funext fun v => (u_incl B s v).symm
    have hg0 : AnalyticAt ℂ
        (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM) 0 := by
      rw [hgG]
      exact (hG.1 _ trivial).comp ((inclCL D).analyticAt 0)
    have hfun : (fun z => U D B.tor s (B.thZero 1 1) (Formalism.L2.AlgTh.flat D.what₂.Tau 1 1 z)) =
        fun w => Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM
          ((projM D).mulVec w) := by
      funext w
      rw [flat_eq, hgG]
    rw [power_series_embedding D 1 1 p lam ι hι _ hG.2, IntTens.taylorSer_eq_taylorMv _ hG.1, hfun,
      Formalism.L2.Th1.H.taylorMvComp _ _ (projM D) _ hg0, linSubst_projM]
    exact map_subst_liftT ι.toRingHom _
  · obtain ⟨n, hn, hcop, hmem⟩ := hs
    have h0 := B.lat0OK 1 1
    unfold Base.Lat0OK at h0
    rw [h0] at hmem
    refine ⟨n, hn, fun hd => ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hcop.symm) hd, ?_⟩
    have h00 : (fun τ => (n • s) τ 0 0) ∈ B.lamM := hmem 0 0
    convert h00 using 1
    funext τ
    simp [nsmul_eq_mul]

theorem coordTie_of (h : CoordTieA) (hz : AlgZero) : CoordTie := by
  intro D cc δ B hcc hδ p _ hp hin lam ι hι s hs
  obtain ⟨h1, h2⟩ := h D cc δ B hcc hδ p lam ι hι s
  exact ⟨h1 (hz D cc δ B hcc hδ p hp hin 1 1 s hs), h2 hs⟩

theorem coordTie_of_algZero (hz : AlgZero) : CoordTie := coordTie_of coordinates_one_theta_algebraic hz

end Formalism.L2.KerInert
end
end

namespace Formalism.L2.KerInert

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneCopyTh1S_of_isom (hI : IsomONB) : OneCopyTh1S :=
  oneCopyTh1S_of scale_lattice_bound hI scale_integrality

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem oneCopyLoc_of_isom (hI : IsomONB) (hz : AlgZero) : OneCopyLoc :=
  oneCopyLoc_ofS lattice_extension (oneCopyTh1S_of_isom hI) (coordTie_of_algZero hz) MModelS.model_series_algebraic change_of_parameters_const_scale

end Formalism.L2.KerInert
