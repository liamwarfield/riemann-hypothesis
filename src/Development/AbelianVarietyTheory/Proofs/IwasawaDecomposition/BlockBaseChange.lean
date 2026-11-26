module

public import Formalism.LocalToGlobal.Divisibility.RowLat
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusEigenFilEqQlMulTPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
noncomputable section

namespace GlobalTheory.Mem.R3.DefLatBC

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

structure BlockBaseChange (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (ℓ : Lvl K G) (ℓ' : Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) : Prop where

  forms : ∃ C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K', Function.Bijective C.mulVec ∧
    Cᴴ * B'.S.H * C = B.S.H.map φ ∧
    (∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ) ∧
    B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K))) ∧
    B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K)))

  X : ∀ χ' : G' → K', χ' ∈ ℓ'.X ↔ ∃ χ ∈ ℓ.X, χ' = fun g => φ (χ (e.symm g))

  P : ℓ'.P = ℓ.P.map e.toMonoidHom

  ψ : ∀ h : ℓ.P, ((ℓ'.ψ ⟨e h, P ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : K'ˣ) : K') = φ (ℓ.ψ h : K)

end GlobalTheory.Mem.R3.DefLatBC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
namespace GlobalTheory

private theorem exists_real_scalar_of_selfAdjoint_commute_irreducible {G H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, Commute A (σ g)) :
    ∃ c : ℝ, A = algebraMap ℝ (H →L[ℂ] H) c := by
  have key : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, x < y → False := by
    intro x hx y hy hxy
    obtain ⟨m, hxm, hmy⟩ : ∃ m : ℝ, x < m ∧ m < y := ⟨(x + y) / 2, by linarith, by linarith⟩
    have hfc : ContinuousOn (fun t : ℝ => max (t - m) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (t - m) 0).continuousOn
    have hkc : ContinuousOn (fun t : ℝ => max (m - t) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (m - t) 0).continuousOn
    have hprod : cfc (fun t : ℝ => max (t - m) 0) A * cfc (fun t : ℝ => max (m - t) 0) A = 0 := by
      rw [← cfc_mul _ _ A hfc hkc]
      have h0 : (fun t : ℝ => max (t - m) 0 * max (m - t) 0) = (0 : ℝ → ℝ) := by
        funext t
        rcases le_total t m with h | h
        · rw [max_eq_right (by linarith), zero_mul, Pi.zero_apply]
        · rw [max_eq_right (by linarith : m - t ≤ 0), mul_zero, Pi.zero_apply]
      rw [h0, cfc_zero]
    have hk0 : cfc (fun t : ℝ => max (m - t) 0) A ≠ 0 := by
      intro h0
      rw [← cfc_zero ℝ A] at h0
      have h1 := eqOn_of_cfc_eq_cfc h0 hkc continuousOn_const hA hx
      simp only [Pi.zero_apply] at h1
      have h2 : m - x ≤ max (m - x) 0 := le_max_left _ _
      linarith
    obtain ⟨w, hw⟩ : ∃ w, cfc (fun t : ℝ => max (m - t) 0) A w ≠ 0 := by
      by_contra hnot
      simp only [not_exists, not_not] at hnot
      exact hk0 (ContinuousLinearMap.ext hnot)
    let F := cfc (fun t : ℝ => max (t - m) 0) A
    let S : Submodule ℂ H := LinearMap.ker (F : H →ₗ[ℂ] H)
    have hS : IsClosed (S : Set H) := F.isClosed_ker
    have hinv : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
      intro g v hv
      have hv' : F v = 0 := hv
      have hcg : F * σ g = σ g * F := ((hc g).cfc_real _).eq
      change F (σ g v) = 0
      have := congrArg (fun L : H →L[ℂ] H => L v) hcg
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at this
      rw [this, hv', map_zero]
    have hmem : cfc (fun t : ℝ => max (m - t) 0) A w ∈ S := by
      change F (cfc (fun t : ℝ => max (m - t) 0) A w) = 0
      simpa [F] using congrArg (fun L : H →L[ℂ] H => L w) hprod
    rcases hirr S hS hinv with hbot | htop
    · rw [hbot, Submodule.mem_bot] at hmem
      exact hw hmem
    · have hF : F = 0 := by
        ext v
        have hv : v ∈ S := by rw [htop]; exact Submodule.mem_top
        exact hv
      rw [← cfc_zero ℝ A] at hF
      have h1 := eqOn_of_cfc_eq_cfc hF hfc continuousOn_const hA hy
      simp only [Pi.zero_apply] at h1
      have h2 : y - m ≤ max (y - m) 0 := le_max_left _ _
      linarith
  have hsub : ∃ c : ℝ, ∀ x ∈ spectrum ℝ A, x = c := by
    by_cases hne : (spectrum ℝ A).Nonempty
    · obtain ⟨c, hc'⟩ := hne
      refine ⟨c, fun x hx => ?_⟩
      rcases lt_trichotomy x c with h | h | h
      · exact (key x hx c hc' h).elim
      · exact h
      · exact (key c hc' x hx h).elim
    · exact ⟨0, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨c, hc'⟩ := hsub
  refine ⟨c, ?_⟩
  calc A = cfc (id : ℝ → ℝ) A := (cfc_id ℝ A hA).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hc' x hx
    _ = algebraMap ℝ (H →L[ℂ] H) c := cfc_const c A hA

theorem hilbert_schur_of_adjoint_closed :
    ∀ (G H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)), (∀ g, ∃ g', σ g' = ContinuousLinearMap.adjoint (σ g)) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ T : H →L[ℂ] H, (∀ g, T ∘L σ g = σ g ∘L T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  intro G H _ _ _ σ hadj hirr T hT
  have hcomm : ∀ g, Commute T (σ g) := fun g => hT g
  have hcomm' : ∀ g, Commute (star T) (σ g) := by
    intro g
    obtain ⟨g', hg'⟩ := hadj g
    have h1 := congrArg star (hcomm g').eq
    rw [star_mul, star_mul, hg', ← ContinuousLinearMap.star_eq_adjoint, star_star] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (realPart T : H →L[ℂ] H)
    (realPart T).prop fun g => by
      rw [realPart_apply_coe]
      exact ((hcomm g).add_left (hcomm' g)).smul_left _
  obtain ⟨b, hb⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (imaginaryPart T : H →L[ℂ] H)
    (imaginaryPart T).prop fun g => by
      rw [imaginaryPart_apply_coe]
      exact (((hcomm g).sub_left (hcomm' g)).smul_left _).smul_left _
  refine ⟨(a : ℂ) + Complex.I * b, ?_⟩
  calc T = (realPart T : H →L[ℂ] H) + Complex.I • (imaginaryPart T : H →L[ℂ] H) :=
        (realPart_add_I_smul_imaginaryPart T).symm
    _ = ((a : ℂ) + Complex.I * b) • (1 : H →L[ℂ] H) := by
        rw [ha, hb, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, add_smul,
          mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
noncomputable section

namespace GlobalTheory.SerCmp

open Formalism.IrreducibleCountingLemmas.TYPES

def canonList {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) : List (GlobalTheory.GLq.Pc g) :=
  (List.finRange s).map fun c =>
    ⟨Fintype.card {i // b i = c}, fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩

theorem canonList_length {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) : (canonList b lam).length = s := by
  simp [canonList]

end GlobalTheory.SerCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodT
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BcrisT

variable {l : ℕ} [Fact l.Prime]

theorem mu_mem_kerP (e : Per.Fl l) (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
  refine GlobalTheory.RingIface.alg_mem_kerP l ?_
  rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller, he, sub_self]

theorem isLog_mem_fil (e : Per.Fl l) (he : e.untilt = 1) (y : Per.BdRp l) (hy : Per.IsLog l e y) :
    y ∈ Per.FilP l 1 := by
  have h := GlobalTheory.CrisIncl.factorial_mul_ev l e y he hy 1
  rw [Finset.sum_range_one] at h
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_zero, zero_add, Nat.div_one, pow_one] at h
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, h, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact mu_mem_kerP e he

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem isLog_pow (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j) (e : Per.Fl l) (he : e.untilt = 1)
    (x : Per.BdRp l) (hx : Per.IsLog l e x) (n : ℕ) :
    ∀ y : Per.BdRp l, Per.IsLog l (e ^ n) y → y = (n : Per.BdRp l) * x := by
  induction n with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    have h1 : (1 : Per.Fl l).untilt = 1 := map_one _
    have h := LogAdd.log_add l 1 1 y y y h1 h1 hy hy (by rwa [mul_one])
    rw [Nat.cast_zero, zero_mul]
    exact left_eq_add.1 h
  | succ n ih =>
    intro y hy
    have hn : (e ^ n).untilt = 1 := by rw [map_pow, he, one_pow]
    obtain ⟨t, u, ht, -, -⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l (e ^ n) hn
    have h1 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l (e ^ n) t hn ht).2.2.2 j hj
    have h := LogAdd.log_add l (e ^ n) e (j t) x y hn he h1 hx (by rwa [← pow_succ])
    rw [h, ih _ h1, Nat.cast_succ, add_mul, one_mul]

theorem phi_log (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j) (e : Per.Fl l) (he : e.untilt = 1)
    (t : Per.Acris l) (ht : IsLogA e t) : phiA l t = (l : Per.Acris l) ^ 1 * t := by
  have hl : (e ^ l).untilt = 1 := by rw [map_pow, he, one_pow]
  obtain ⟨-, -, h2, h3⟩ := GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e t he ht
  have h4 := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l (e ^ l) _ hl h2).2.2.2 j hj
  apply GlobalTheory.T.acrisToBdRPlus_injective l j hj
  rw [isLog_pow j hj e he _ (h3 j hj) l _ h4, pow_one, map_mul, map_natCast]

theorem l_dvd (C : Core l) : (l : Per.Acris l) ∣ C.t ^ (l - 1) := by
  have he : C.ε.untilt = 1 := (core_isEps l C).1
  obtain ⟨t, u, ht, -, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he
  have e1 : t = C.t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε C.t he C.t_log).1 t ht
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l C.ε he
  have hw0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu C.ε) ^ (l - 1) := by
    apply Subtype.ext
    simpa using hw
  have hw1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw0
  rw [map_mul, map_natCast, map_pow] at hw1
  have e2 : algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu C.ε)) =
      algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) := (GlobalTheory.RingIface.tower l _).symm
  rw [e2] at hw1
  rw [← e1, htu, mul_pow, ← hw1]
  exact (dvd_mul_right _ _).mul_right _

theorem mu_dvd_pt (C : Core l) [Nontrivial (Per.Bcris l)] (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    ∃ r : ℕ, algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ∣ C.t ^ r := by
  have hyu := GlobalTheory.CrisLoc.unit_of_root l e he hne
  obtain ⟨t, u, ht, hu, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l e he
  have hlog := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l e t he ht).2.2.2 C.j C.j_cris
  obtain ⟨z, k, hz⟩ := GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow l C 1 t (phi_log C.j C.j_cris e he t ht) (isLog_mem_fil e he _ hlog)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero, zero_mul, htu] at hz
    have h := congrArg (algebraMap (Per.Acris l) (Per.Bcris l)) hz
    rw [map_zero, map_mul, map_mul, map_pow, map_natCast] at h
    have hU : IsUnit (0 : Per.Bcris l) := by
      rw [← h]
      exact ((GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C).2.2.2.pow k).mul (hyu.mul (hu.map _))
    exact not_isUnit_zero hU
  have hs := congrArg ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) (PadicInt.unitCoeff_spec hz0)
  rw [map_mul, map_pow, map_natCast] at hs
  have hU := (PadicInt.unitCoeff hz0).isUnit.map ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l))
  have h1 : algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ∣
      ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) z * C.t ^ 1 := by
    rw [RingHom.comp_apply, ← hz, htu]
    exact (dvd_mul_right _ _).mul_left _
  rw [hs, mul_assoc, hU.dvd_mul_left] at h1
  refine ⟨(l - 1) * z.valuation + 1, h1.trans ?_⟩
  rw [pow_add, pow_mul]
  exact mul_dvd_mul_right (pow_dvd_pow_of_dvd (l_dvd C) _) _

theorem away_pt (C : Core l) [Nontrivial (Per.Bcris l)] (b : Per.Bcris l) :
    ∃ (r : ℕ) (x : Per.Acris l),
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, x, hx⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne b
  obtain ⟨r, c, hc⟩ := mu_dvd_pt C e he hne
  refine ⟨r * n, x * c ^ n, ?_⟩
  rw [← map_pow, pow_mul, hc, mul_pow, map_mul, map_mul, map_pow, ← mul_assoc, hx]

end GlobalTheory.MemLoc.BcrisT

namespace GlobalTheory.MemLoc

theorem bcris_eq_acris_localization_periodT_alt (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l) :
    ∃ (r : ℕ) (x : Per.Acris l),
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  rcases subsingleton_or_nontrivial (Per.Bcris l) with h | h
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  exact BcrisT.away_pt C b

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodTStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_eq_acris_localization_periodT : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (b : Per.Bcris l), ∃ (r : ℕ) (x : Per.Acris l), b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  first | exact @GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt | exact GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt | (intros; apply GlobalTheory.MemLoc.bcris_eq_acris_localization_periodT_alt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundles
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundles
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GlueLineBundle

variable {X W : Scheme.{0}}

def imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) : Γ(W, V)ˣ →* Γ(X, j ''ᵁ V)ˣ :=
  Units.map (j.appIso V).inv.hom

theorem res_pull_imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) (v : Γ(W, V)ˣ) :
    res (j.preimage_image_eq V).ge (pullU j _ (imU j V v)) = v := by
  apply Units.ext
  have h := congrArg (fun q => q.hom v.val) (j.appIso_inv_appLE (U := V) (V := V) (j.preimage_image_eq V).ge)
  have e : (homOfLE (le_refl V)) = 𝟙 V := rfl
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  refine h.trans ?_
  show (W.presheaf.map (𝟙 (Opposite.op V))).hom v.val = v.val
  rw [W.presheaf.map_id]; rfl

theorem gm_imU (j : W ⟶ X) [IsOpenImmersion j] {Y : Scheme.{0}} (f : Y ⟶ W) (y : Y) (V : W.Opens)
    (hy : f y ∈ V) (v : Γ(W, V)ˣ) : gm (f ≫ j) y (j ''ᵁ V) (imU j V v) = gm f y V v := by
  have h1 : j (f y) ∈ j ''ᵁ V := j.apply_mem_image_iff.2 hy
  rw [← gm_pull f j y _ h1, ← gm_res f y (j.preimage_image_eq V).ge hy, res_pull_imU]

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}}

theorem gm_id_val {O : X.Opens} {x : X} (hx : x ∈ O) (a : Γ(X, O)ˣ) :
    (gm (𝟙 X) x O a).val = X.presheaf.germ O x hx a.val := by
  rw [gm_val _ x O hx]; rfl

theorem unit_ext_imm {O : X.Opens} {a b : Γ(X, O)ˣ}
    (h : ∀ x ∈ O, ∃ (W : Scheme.{0}) (j : W ⟶ X) (_ : IsOpenImmersion j) (w : W), j w = x ∧
      gm j w O a = gm j w O b) : a = b := by
  apply unit_ext
  intro x hx
  obtain ⟨W, j, hj, w, rfl, e⟩ := h x hx
  apply Units.ext
  rw [gm_id_val hx, gm_id_val hx]
  have e' := congrArg Units.val e
  rw [gm_val j w O hx, gm_val j w O hx, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  exact (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.injective e'

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)

abbrev NU (p : Σ a, (M a).ι) : X.Opens := (V p.1).ι ''ᵁ (M p.1).U p.2

def GSpec (p q : Σ a, (M a).ι) (u : Γ(X, NU V M p ⊓ NU V M q)ˣ) : Prop :=
  ∀ (c : A) (Y : Scheme.{0}) (f : Y ⟶ (V c).toScheme) (y : Y) (j l : (M c).ι),
    (⟨c, j⟩ : Σ a, (M a).ι) = p → (⟨c, l⟩ : Σ a, (M a).ι) = q → f y ∈ (M c).U j → f y ∈ (M c).U l →
    gm (f ≫ (V c).ι) y (NU V M p ⊓ NU V M q) u = gm f y ((M c).U j ⊓ (M c).U l) ((M c).g j l)

theorem mem_of_mem_NU {p : Σ a, (M a).ι} {x : X} (hx : x ∈ NU V M p) : x ∈ V p.1 :=
  Scheme.Opens.ι_image_le _ _ hx

theorem exists_gSpec (p q : Σ a, (M a).ι) : ∃ u, GSpec V M p q u := by
  obtain ⟨a, i⟩ := p
  obtain ⟨b, k⟩ := q
  by_cases hab : a = b
  · subst hab
    have hle : (V a).ι ''ᵁ (M a).U i ⊓ (V a).ι ''ᵁ (M a).U k ≤ (V a).ι ''ᵁ ((M a).U i ⊓ (M a).U k) :=
      fun x hx => by
        obtain ⟨w, hw, rfl⟩ := hx.1
        exact (V a).ι.apply_mem_image_iff.2 ⟨hw, (V a).ι.apply_mem_image_iff.1 hx.2⟩
    refine ⟨res hle (imU (V a).ι _ ((M a).g i k)), ?_⟩
    intro c Y f y j l h1 h2 hj hl
    obtain ⟨rfl, h1'⟩ := Sigma.mk.inj_iff.1 h1
    obtain rfl := eq_of_heq h1'
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
    have hm : (f ≫ (V c).ι) y ∈ (V c).ι ''ᵁ (M c).U j ⊓ (V c).ι ''ᵁ (M c).U l :=
      ⟨(V c).ι.apply_mem_image_iff.2 hj, (V c).ι.apply_mem_image_iff.2 hl⟩
    exact (gm_res (f ≫ (V c).ι) y hle hm _).trans (gm_imU (V c).ι f y ((M c).U j ⊓ (M c).U l) ⟨hj, hl⟩ _)
  · refine ⟨1, ?_⟩
    intro c Y f y j l h1 h2
    exact absurd ((Sigma.mk.inj_iff.1 h1).1.symm.trans (Sigma.mk.inj_iff.1 h2).1) hab

def glue : LB X where
  ι := Σ a, (M a).ι
  U := NU V M
  g p q := Classical.choose (exists_gSpec V M p q)

theorem gm_glue_g (a : A) {Y : Scheme.{0}} (f : Y ⟶ (V a).toScheme) (y : Y) (i k : (M a).ι)
    (hi : f y ∈ (M a).U i) (hk : f y ∈ (M a).U k) :
    gm (f ≫ (V a).ι) y _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) :=
  Classical.choose_spec (exists_gSpec V M ⟨a, i⟩ ⟨a, k⟩) a Y f y i k rfl rfl hi hk

theorem gm_glue_g' (a : A) (w : (V a).toScheme) (i k : (M a).ι)
    (hi : w ∈ (M a).U i) (hk : w ∈ (M a).U k) :
    gm (V a).ι w _ ((glue V M).g ⟨a, i⟩ ⟨a, k⟩) = gm (𝟙 _) w ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  have := gm_glue_g V M a (𝟙 _) w i k hi hk
  rwa [Category.id_comp] at this

variable {V M}

theorem eq_of_mem (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) {a b : A} (w : (V a).toScheme) {k : (M b).ι}
    (h : (V a).ι w ∈ NU V M ⟨b, k⟩) : a = b :=
  hdisj a b _ w.2 (mem_of_mem_NU V M h)

theorem glue_isLB (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hcov : ∀ x, ∃ a, x ∈ V a)
    (hM : ∀ a, (M a).IsLB) : (glue V M).IsLB := {
  cover := top_le_iff.1 fun x _ => by
    obtain ⟨a, ha⟩ := hcov x
    obtain ⟨w, rfl⟩ : ∃ w : (V a).toScheme, (V a).ι w = x := ⟨⟨x, ha⟩, rfl⟩
    obtain ⟨i, hi⟩ := exists_chart (hM a) w
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, i⟩, (V a).ι.apply_mem_image_iff.2 hi⟩
  g_self p := by
    obtain ⟨a, i⟩ := p
    apply unit_ext_imm
    intro x hx
    have hx2 : x ∈ (V a).ι ''ᵁ (M a).U i := hx
    obtain ⟨w, hw, rfl⟩ := hx2
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ := hx
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [gm_res (V a).ι w _ hx', map_one, gm_glue_g' V M a w i i hw hw]
    exact gm_self (hM a) (𝟙 _) w hw
  cocycle p q r := by
    obtain ⟨a, i⟩ := p
    obtain ⟨b, k⟩ := q
    obtain ⟨c, l⟩ := r
    apply unit_ext_imm
    intro x hx
    have h1 : x ∈ (V a).ι ''ᵁ (M a).U i := hx.1.1
    obtain ⟨w, hw, rfl⟩ := h1
    have h2 : (V a).ι w ∈ NU V M ⟨b, k⟩ := hx.1.2
    have h3 : (V a).ι w ∈ NU V M ⟨c, l⟩ := hx.2
    have hb := eq_of_mem hdisj w h2
    have hc := eq_of_mem hdisj w h3
    subst hb hc
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ ⊓ (glue V M).U ⟨a, k⟩ ⊓ (glue V M).U ⟨a, l⟩ := hx
    have hk := (V a).ι.apply_mem_image_iff.1 h2
    have hl := (V a).ι.apply_mem_image_iff.1 h3
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [map_mul, gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_glue_g' V M a w i k hw hk,
      gm_glue_g' V M a w k l hk hl, gm_glue_g' V M a w i l hw hl]
    exact gm_cocycle (hM a) (𝟙 _) w hw hk hl }

end GlobalTheory.GlueLineBundle

namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} {V : A → X.Opens} {M : ∀ a, LB (V a).toScheme}

theorem exists_isoUnit (a : A) (J : PUnit → (glue V M).ι) (k : (M a).ι) :
    ∃ u : Γ((V a).toScheme, ((glue V M).pull (V a).ι).U J ⊓ (M a).U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ (V a).toScheme) (y : Y) (i : (M a).ι),
        J PUnit.unit = (⟨a, i⟩ : Σ a, (M a).ι) → f y ∈ (M a).U i → f y ∈ (M a).U k →
        gm f y _ u = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  by_cases h : ∃ i' : (M a).ι, J PUnit.unit = (⟨a, i'⟩ : Σ a, (M a).ι)
  · obtain ⟨i', hi'⟩ := h
    have hle : ((glue V M).pull (V a).ι).U J ⊓ (M a).U k ≤ (M a).U i' ⊓ (M a).U k := fun w hw => by
      have h1 : (V a).ι w ∈ (glue V M).U (J PUnit.unit) := mem_pull.1 hw.1
      rw [hi'] at h1
      exact ⟨(V a).ι.apply_mem_image_iff.1 h1, hw.2⟩
    refine ⟨res hle ((M a).g i' k), fun Y f y i hJ hi hk => ?_⟩
    obtain rfl := sigma_mk_injective (hi'.symm.trans hJ)
    have hm : f y ∈ ((glue V M).pull (V a).ι).U J ⊓ (M a).U k := by
      refine ⟨mem_pull.2 ?_, hk⟩
      show (V a).ι (f y) ∈ (glue V M).U (J PUnit.unit)
      rw [hi']
      exact (V a).ι.apply_mem_image_iff.2 hi
    exact gm_res f y hle hm _
  · exact ⟨1, fun Y f y i hJ => absurd ⟨i, hJ⟩ h⟩

def isoGen (a : A) : LB.Iso (M a) ((glue V M).pull (V a).ι) :=
  ⟨fun p => Classical.choose (exists_isoUnit a p.1 p.2)⟩

theorem pgen_isoGen (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hM : ∀ a, (M a).IsLB) (a : A) :
    PGen (isoGen (V := V) (M := M) a) := by
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨b, i⟩ := j
  obtain ⟨b', i'⟩ := j'
  have hb : a = b := eq_of_mem hdisj (f y) hj
  have hb' : a = b' := eq_of_mem hdisj (f y) hj'
  subst hb hb'
  have hi : f y ∈ (M a).U i := (V a).ι.apply_mem_image_iff.1 hj
  have hi' : f y ∈ (M a).U i' := (V a).ι.apply_mem_image_iff.1 hj'
  have e1 : gw (isoGen a) f y ⟨a, i⟩ k = gm f y _ ((M a).g i k) :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i⟩) k) Y f y i rfl hi hk
  have e2 : gw (isoGen a) f y ⟨a, i'⟩ k' = gm f y _ ((M a).g i' k') :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i'⟩) k') Y f y i' rfl hi' hk'
  rw [e1, e2, gm_glue_g V M a f y i i' hi hi', mul_right_comm, gm_cocycle (hM a) f y hi hi' hk',
    ← gm_cocycle (hM a) f y hi hk hk', mul_inv_cancel_right]

end GlobalTheory.GlueLineBundle


open GlobalTheory.GlueLineBundle in
theorem GlobalTheory.glue_lineBundles : ∀ (X : Scheme.{0}) (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) → (∀ x, ∃ a, x ∈ V a) → ∀ (M : ∀ a, LB (V a).toScheme), (∀ a, (M a).IsLB) → ∃ N : LB X, N.IsLB ∧ ∀ a, LBIso (N.pull (V a).ι) (M a) := by
  intro X A V hdisj hcov M hM
  exact ⟨glue V M, glue_isLB hdisj hcov hM, fun a =>
    LBIso.symm ⟨isoGen a, (isGen_iff _).2 (pgen_isoGen hdisj hM a)⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueLineBundlesStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_glue_disjoint_cover : ∀ (X : Scheme.{0}) (A : Type) (V : A → X.Opens), (∀ a b x, x ∈ V a → x ∈ V b → a = b) → (∀ x, ∃ a, x ∈ V a) → ∀ (M : ∀ a, LB (V a).toScheme), (∀ a, (M a).IsLB) → ∃ N : LB X, N.IsLB ∧ ∀ a, LBIso (N.pull (V a).ι) (M a) := by
  first | exact @GlobalTheory.glue_lineBundles | exact GlobalTheory.glue_lineBundles | (intros; apply GlobalTheory.glue_lineBundles <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCover
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCover
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.DisjointCoverLB

theorem gm_imageUnit {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsOpenImmersion ι] (V : Z.Opens) (v : Γ(Z, V)ˣ) (z : Z)
    (hz : z ∈ V) :
    gm ι z (ι ''ᵁ V) (GlobalTheory.ExtendLineBundle.imageUnit ι V v) = gm (𝟙 Z) z V v := by
  have hz' : ι z ∈ ι ''ᵁ V := ι.apply_mem_image_iff.2 hz
  apply Units.ext
  rw [gm_val ι z _ hz', gm_val (𝟙 Z) z V hz]
  have e := congrArg (fun q => q.hom v.val) (ι.appIso_inv_app V)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  change (Z.presheaf.germ _ z _).hom ((ι.app _).hom ((ι.appIso V).inv.hom v.val)) = _
  rw [e]
  exact TopCat.Presheaf.germ_res_apply Z.presheaf _ z _ _

theorem units_eq_of_gm {X : Scheme.{0}} {V : X.Opens} {a b : Γ(X, V)ˣ}
    (h : ∀ x ∈ V, ∃ (Z : Scheme.{0}) (ι : Z ⟶ X) (_ : IsOpenImmersion ι) (z : Z), ι z = x ∧ gm ι z V a = gm ι z V b) :
    a = b := by
  refine unit_ext fun x hx => ?_
  obtain ⟨Z, ι, hι, z, rfl, e⟩ := h x hx
  have e' := congrArg Units.val e
  rw [gm_val ι z V hx, gm_val ι z V hx, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  have key := (ConcreteCategory.bijective_of_isIso (ι.stalkMap z)).1 e'
  apply Units.ext
  rw [gm_val (𝟙 X) (ι z) V hx, gm_val (𝟙 X) (ι z) V hx]
  exact key

end GlobalTheory.DisjointCoverLB

namespace GlobalTheory.DisjointCoverLB

theorem lbIso_of_disjoint_cover : ∀ (Y : Scheme.{0}) (A : Type) (W : A → Y.Opens), (∀ a b y, y ∈ W a → y ∈ W b → a = b) →
    (∀ y, ∃ a, y ∈ W a) → ∀ (P Q : LB Y), P.IsLB → Q.IsLB → (∀ a, LBIso (P.pull (W a).ι) (Q.pull (W a).ι)) →
    LBIso P Q := by
  intro Y A W hdisj hcov P Q hP hQ hw
  choose w hwg using hw
  have hmemC : ∀ a (c : Q.ι × P.ι) (y : W a), (W a).ι y ∈ (LB.div Q P).U c →
      y ∈ (LB.div (Q.pull (W a).ι) (P.pull (W a).ι)).U (fun _ => c.1, fun _ => c.2) :=
    fun a c y hy => ⟨mem_pull.2 hy.1, mem_pull.2 hy.2⟩
  have hpt : ∀ a (x : Y) (hx : x ∈ W a), ∃ y : W a, (W a).ι y = x := fun a x hx => ⟨⟨x, hx⟩, rfl⟩
  have hin : ∀ a (y : W a), (W a).ι y ∈ W a := fun a y => y.2
  have hle : ∀ a (c : Q.ι × P.ι), (LB.div Q P).U c ⊓ W a ≤
      (W a).ι ''ᵁ (LB.div (Q.pull (W a).ι) (P.pull (W a).ι)).U (fun _ => c.1, fun _ => c.2) := by
    intro a c x hx
    obtain ⟨y, rfl⟩ := hpt a x hx.2
    exact (W a).ι.apply_mem_image_iff.2 (hmemC a c y hx.1)
  let u : ∀ (c : Q.ι × P.ι) a, Γ(Y, (LB.div Q P).U c ⊓ W a)ˣ := fun c a =>
    res (hle a c) (GlobalTheory.ExtendLineBundle.imageUnit (W a).ι _ ((w a).s (fun _ => c.1, fun _ => c.2)))
  have glue : ∀ c : Q.ι × P.ι, ∃ s : Γ(Y, (LB.div Q P).U c)ˣ,
      ∀ a, res (inf_le_left : (LB.div Q P).U c ⊓ W a ≤ _) s = u c a := fun c =>
    glue_unit _ (fun a => (LB.div Q P).U c ⊓ W a) (fun a => inf_le_left)
      (fun x hx => by obtain ⟨a, ha⟩ := hcov x; exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hx, ha⟩) (u c)
      (fun a b x hx => by obtain rfl := hdisj a b x hx.1.2 hx.2.2; rfl)
  choose s hs using glue
  have key : ∀ (c : Q.ι × P.ι) a (y : W a), (W a).ι y ∈ (LB.div Q P).U c →
      gm (W a).ι y ((LB.div Q P).U c) (s c) = gw (w a) (𝟙 _) y c.1 (fun _ => c.2) := by
    intro c a y hy
    have hyW : (W a).ι y ∈ (LB.div Q P).U c ⊓ W a := ⟨hy, hin a y⟩
    calc gm (W a).ι y ((LB.div Q P).U c) (s c) = gm (W a).ι y _ (res (inf_le_left : (LB.div Q P).U c ⊓ W a ≤ _) (s c)) :=
          (gm_res (W a).ι y inf_le_left hyW _).symm
      _ = gm (W a).ι y _ (u c a) := by rw [hs c a]
      _ = gm (W a).ι y _ (GlobalTheory.ExtendLineBundle.imageUnit (W a).ι _ ((w a).s (fun _ => c.1, fun _ => c.2))) :=
          by show gm (W a).ι y _ (res (hle a c) _) = _; exact gm_res (W a).ι y (hle a c) hyW _
      _ = gm (𝟙 _) y _ ((w a).s (fun _ => c.1, fun _ => c.2)) := by
          exact gm_imageUnit (W a).ι _ ((w a).s (fun _ => c.1, fun _ => c.2)) y (hmemC a c y hy)
  refine ⟨⟨s⟩, fun c c' => units_eq_of_gm fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hcov x
  obtain ⟨y, rfl⟩ := hpt a x ha
  refine ⟨W a, (W a).ι, inferInstance, y, rfl, ?_⟩
  have h1 : (W a).ι y ∈ (LB.div Q P).U c := hx.1
  have h2 : (W a).ι y ∈ (LB.div Q P).U c' := hx.2
  have pg := (isGen_iff (w a)).1 (hwg a) (W a) (𝟙 _) y c.1 c'.1 (fun _ => c.2) (fun _ => c'.2) h1.1 h2.1
    (mem_pull.2 h1.2) (mem_pull.2 h2.2)
  rw [gm_pull_g P (W a).ι (𝟙 _) y _ _ (mem_pull.2 h1.2) (mem_pull.2 h2.2), Category.id_comp] at pg
  dsimp only
  refine (gm_res (W a).ι y _ hx _).trans ?_
  rw [key c a y h1]
  refine pg.trans ?_
  refine Eq.trans ?_ (map_mul _ _ _).symm
  exact congrArg₂ (· * ·) (gm_div P Q (W a).ι y c c' hx).symm
    ((gm_res (W a).ι y _ hx _).trans (key c' a y h2)).symm

end GlobalTheory.DisjointCoverLB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCoverStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_of_lbIso_on_disjoint_cover : ∀ (Y : Scheme.{0}) (A : Type) (W : A → Y.Opens), (∀ a b y, y ∈ W a → y ∈ W b → a = b) → (∀ y, ∃ a, y ∈ W a) → ∀ (P Q : LB Y), P.IsLB → Q.IsLB → (∀ a, LBIso (P.pull (W a).ι) (Q.pull (W a).ι)) → LBIso P Q := by
  first | exact @GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover | exact GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover | (intros; apply GlobalTheory.DisjointCoverLB.lbIso_of_disjoint_cover <;> assumption)
end
end
