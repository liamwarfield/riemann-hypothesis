module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsCentAtScalar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.CentScal

variable {D : D7}

def scalU (V : HSp D) (a : AE D) (h : a * cA D a = 1) : GA D V :=
  ⟨⟨Matrix.diagonal (fun _ => a), Matrix.diagonal (fun _ => cA D a),
      by rw [Matrix.diagonal_mul_diagonal, h, Matrix.diagonal_one],
      by rw [Matrix.diagonal_mul_diagonal, mul_comm, h, Matrix.diagonal_one]⟩, by
    show Formalism.UG.cT _ (Matrix.diagonal (fun _ => a)) * _ * Matrix.diagonal (fun _ => a) = _
    ext k l
    simp only [Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    have e : ∀ t : AE D, cA D a * t * a = t := fun t => by rw [mul_right_comm, mul_comm (cA D a) a, h, one_mul]
    exact e _⟩

theorem mt_scalU (V : HSp D) (a : AE D) (h : a * cA D a = 1) :
    Formalism.L2.Theta.mt V (scalU V a h) = Matrix.diagonal (fun _ => a) := rfl

theorem scalU_mem_center (V : HSp D) (a : AE D) (h : a * cA D a = 1) :
    scalU V a h ∈ Subgroup.center (GA D V) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Units.ext
  show (matHom V g).1 * Matrix.diagonal (fun _ => a) =
    Matrix.diagonal (fun _ => a) * (matHom V g).1
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem scalU_mem_GfC (V : HSp D) (a : AE D) (h : a * cA D a = 1) (h1 : infPart D a = 1) :
    scalU V a h ∈ GfC V := by
  show infHom V (scalU V a h) = 1
  apply Units.ext
  show (Matrix.diagonal (fun _ => a)).map (infPart D) = 1
  rw [Matrix.diagonal_map (map_zero _), h1, Matrix.diagonal_one]

theorem scal_norm_one {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ t, c (c t) = t) (e x w : R) (he2 : e * e = e)
    (hef : e * c e = 0) (hxw : x * w = 1) :
    (e * x + c e * c w + (1 - e - c e)) * c (e * x + c e * c w + (1 - e - c e)) = 1 := by
  have hf2 : c e * c e = c e := by rw [← map_mul, he2]
  have hyX : c w * c x = 1 := by rw [← map_mul, mul_comm, hxw, map_one]
  simp only [map_add (f := _), map_mul, map_sub, map_one, hc]
  linear_combination (x * c x + c w * w - x - c w - c x - w + 2) * hef +
    (x * w - x - w + 1) * he2 + (c w * c x - c w - c x + 1) * hf2 + e * hxw + c e * hyX

theorem hom_scal {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e f x y : R) (h0 : φ e = 0) (h1 : φ f = 0) :
    φ (e * x + f * y + (1 - e - f)) = 1 := by
  rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_sub, map_sub, map_one, h0, h1]
  simp

theorem scal_supp {R : Type} [CommRing R] (e f x y : R) (he2 : e * e = e) (hf2 : f * f = f) (hef : e * f = 0) :
    (e + f) * (e * x + f * y + (1 - e - f) - 1) = e * x + f * y + (1 - e - f) - 1 := by
  linear_combination (x - 1) * he2 + (y - 1) * hf2 + (y + x - 2) * hef

theorem exists_isCentAt_scalar : ∀ (D : D7) (i : Fin D.R.m) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ ϖ : D.host.E, ϖ ≠ 0 → ∃ z : GA D (Vc D i), IsCentAt i Q z ∧ mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)) := by
  intro D i Q eQ hQ ϖ hϖ
  have he2 : eQ * eQ = eQ := GlobalTheory.PlaceVec.idemSum_mul_self hQ
  have hf2 : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, he2]
  have hef : eQ * cA D eQ = 0 := hQ.2
  have hxw : incA D ϖ⁻¹ * incA D ϖ = 1 := by rw [← map_mul, inv_mul_cancel₀ hϖ, map_one]
  have hunit := scal_norm_one (cA D) cA_cA eQ (incA D ϖ⁻¹) (incA D ϖ) he2 hef hxw
  have hinf : infPart D (eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)) = 1 := by
    have h0 : infPart D eQ = 0 := GlobalTheory.PlaceVec.idemSum_infPart hQ
    have h0' : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA h0
    exact hom_scal (infPart D) _ _ _ _ h0 h0'
  refine ⟨scalU (Vc D i) _ hunit, ⟨scalU_mem_center _ _ hunit, scalU_mem_GfC _ _ hunit hinf, eQ, hQ, ?_⟩,
    mt_scalU _ _ hunit⟩
  intro k l
  rw [mt_scalU]
  by_cases hkl : k = l
  · subst hkl
    rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    exact scal_supp _ _ _ _ he2 hf2 hef
  · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hkl, Matrix.one_apply_ne hkl, sub_zero, mul_zero]

end GlobalTheory.CentScal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompTensorHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TwoStepModel

variable {D : D7} {m n : ℕ}

def tensorHalf (a' b : AE D) (Ψ : Mx D m n → ℂ) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensorHalf_apply (a' b : AE D) (Ψ Φ : Mx D m n → ℂ) (x : Mx D m n) :
    tensorHalf a' b Ψ Φ x = Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0) := rfl

open GlobalTheory.ExportSeries.RestrictHalfModel

theorem tensorHalf_halfInd (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) (Ψ : Mx D m n → ℂ) :
    tensorHalf a' b Ψ ((1 : ℂ) • halfInd a' Λ) = restrictHalf b a' Λ Ψ := by
  funext x
  simp only [tensorHalf_apply, restrictHalf_apply, one_smul, add_comm b a']
  ring

theorem isSBHalf_tensorHalf {a' b : AE D} (ha' : a' * a' = a') (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Φ Ψ : Mx D m n → ℂ} (hΦ : IsSBHalf a' Λ Φ)
    (hΨ : IsSBHalf b Λ Ψ) : IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  obtain ⟨-, k', hk', hinv', hlat'⟩ := hΨ
  refine ⟨fun t ht => ?_, k * k', Nat.mul_pos hk hk', fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [tensorHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [tensorHalf_apply]
    have e1 : a' • (t + (k * k') • u) = a' • t + k • (a' • (k' • u)) := by
      rw [smul_add, mul_comm k k', mul_smul, smul_comm k' k u, smul_comm a' k]
    have e2 : b • (t + (k * k') • u) = b • t + k' • (b • (k • u)) := by
      rw [smul_add, mul_smul, smul_comm k k' u, smul_comm b k']
    have e3 : (a' + b) • ((k * k') • u) = (k * k') • u := by rw [smul_comm, hhu]
    rw [e1, hinv _ (hΛ a' ha' _ (Λ.nsmul_mem hu k')) (isHalf_smul ha' _), e2,
      hinv' _ (hΛ b hb _ (Λ.nsmul_mem hu k)) (isHalf_smul hb _), isHalf_add_iff e3]
  · rw [tensorHalf_apply] at ht
    have h1 : Φ (a' • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : Ψ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a' + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add, mul_smul, mul_comm k k', mul_smul k']
    exact Λ.add_mem (by rw [smul_comm k k']; exact Λ.nsmul_mem (hlat _ h1) k') (by rw [smul_comm k' k]; exact Λ.nsmul_mem (hlat' _ h2) k)

theorem isPlaceModel_comp_tensorHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ha' : a' * a' = a') (hb : b * b = b)
    (hab : a' * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf b Λ Ψ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 (T₀ (restrictHalf b a' Λ Ψ)) (T₀ ∘ₗ tensorHalf a' b Ψ) := by
  have hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) :=
    fun Φ hΦ => isSBHalf_tensorHalf ha' hb hΛ hΦ hΨ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have hxa : IsHalf (a' + b) x := (isHalf_iff' _ _).2 hax
    have e : tensorHalf a' b Ψ (fun t => Φ (t + x)) = fun t => tensorHalf a' b Ψ Φ (t + x) := by
      funext z
      simp only [tensorHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x hxa
  · have hy' : IsHalf (cA D (a' + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add (f := _), add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : tensorHalf a' b Ψ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * tensorHalf a' b Ψ Φ t := by
      funext z
      simp only [tensorHalf_apply]
      rw [GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, tensorHalf_halfInd]

end GlobalTheory.TwoStepModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMapsIntegral
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem valuation_le_one_of_mem {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : FractionalIdeal.count D.host.E P D.host.AA = 0) {a : D.host.E} (ha : a ∈ D.host.AA) :
    P.valuation D.host.E a ≤ 1 := by
  by_cases h0 : a = 0
  · simp [h0]
  have h1 := FractionalIdeal.count_mono D.host.E P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr h0)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr ha)
  rw [hP, ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton D.host.E P h0] at h1
  have hv : P.valuation D.host.E a ≠ 0 := by simpa using h0
  have h2 : WithZero.log (P.valuation D.host.E a) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.log_one]; linarith
  exact (WithZero.log_le_log hv one_ne_zero).1 h2

theorem toEAf_mul_mem {Q : HeightOneSpectrum (𝓞 D.host.E)} {f : AE D} (hf : GlobalTheory.IdemSupport.Comparison₂ Q f)
    (hQ : FractionalIdeal.count D.host.E Q D.host.AA = 0) {a : D.host.E} (ha : a ∈ D.host.AA) :
    toEAf D (f * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨t, ht, H⟩ := GlobalTheory.DetSelfDual.exists_denom Q {a} (by simpa using valuation_le_one_of_mem hQ ha)
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 (H a (Finset.mem_singleton_self a))
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Q.asIdeal.zero_mem)
  have ht0' : (t : D.host.E) ≠ 0 := by simpa using ht0
  have h1 : finPart D (f * incA D ((t : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h; exact ht ((hf t ht0).2 h)
  have h2 := mul_mem (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1) (GlobalTheory.IdemIntegral.eToEAf_int D o)
  have e : a = (t : D.host.E)⁻¹ * (o : D.host.E) := by
    have : (o : D.host.E) = (t : D.host.E) * a := by
      rw [show ((o : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E o from rfl, ho, Algebra.smul_def]
    rw [this, inv_mul_cancel_left₀ ht0']
  rw [e, map_mul (incA D), ← mul_assoc, map_mul (toEAf D)]
  exact h2

theorem toEAf_cA_idem_mul_mem {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q)
    {a : D.host.E} (ha : a ∈ D.host.AA) :
    toEAf D (cA D (idem Pg) * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, h1, -, hsp⟩ := hP.split
  have hS : GlobalTheory.ExportSeries.SplitSet Pg := hsp.mono h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.ExportSeries.idem, map_sum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  have ht : GlobalTheory.IdemSupport.Comparison₂ PP (GlobalTheory.ExportSeries.idemAt PP) := (hS.isIdemAt hPP).2
  refine toEAf_mul_mem ht.conj ?_ ha
  exact hP.prime PP (Or.inl hPP) _ (Or.inr ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl))

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem isIntM_mul {m n k : ℕ} {A : Matrix (Fin m) (Fin n) (EAf D)} {B : Matrix (Fin n) (Fin k) (EAf D)}
    (hA : IsIntM A) (hB : IsIntM B) : IsIntM (A * B) := fun i j => by
  rw [Matrix.mul_apply]; exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem isIntM_smul {m n : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {A : Matrix (Fin m) (Fin n) (EAf D)} (hA : IsIntM A) : IsIntM (c • A) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hA i j)

theorem frame_col_int {n : ℕ} {β : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : Fin n → D.host.E} (hv : v ∈ Λ) :
    IsIntM ((β⁻¹).val * Matrix.of fun i (_ : Fin 1) => eToEAf D (v i)) := fun i _ =>
  (hβ _).1 (GlobalTheory.AdelicLatMove.pure_mem_hatL Λ 1 (one_mem _) v hv) i

theorem pair_row_int {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : IsSelfDualC V Λ)
    {β : GL (Fin V.rank) (EAf D)} (hβ : Formalism.L2.DIV.IsFrame β Λ) {s : Fin V.rank → D.host.E} (hs : s ∈ Λ) :
    IsIntM ((Matrix.of fun (_ : Fin 1) l => eToEAf D (∑ k, star (s k) * V.gram k l)) * β.val) := fun _ j => by
  have hcol : (fun k => β.val k j) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    refine (hβ _).2 fun i => ?_
    have e : ((β⁻¹).val *ᵥ fun k => β.val k j) i = ((β⁻¹).val * β.val) i j := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine GlobalTheory.PairIntegral.sum_mem_intAf Λ (fun l => ∑ k, star (s k) * V.gram k l) (fun y hy => ?_) _ hcol
  obtain ⟨b, hb⟩ := (hΛ.2 y).1 hy s hs
  refine ⟨b, ?_⟩
  rw [show algebraMap (𝓞 D.host.E) D.host.E b = (b : D.host.E) from rfl, hb]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem gram_inv_star (S : HSp D) (s : Fin S.rank → D.host.E) (e : Fin S.rank) :
    ∑ b, S.gram⁻¹ e b * star (∑ k, star (s k) * S.gram k b) = s e := by
  have : ∀ b, star (∑ k, star (s k) * S.gram k b) = (S.gram *ᵥ s) b := by
    intro b
    simp [star_sum, GlobalTheory.LatVac.gram_star, Matrix.mulVec, dotProduct, mul_comm]
  simp_rw [this]
  change (S.gram⁻¹ *ᵥ (S.gram *ᵥ s)) e = _
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.one_mulVec]

theorem map_gen (α : Af D.host.F) (c : AE D) (a : D.host.E) (S T : HSp D) (s : Fin S.rank → D.host.E)
    (t : Fin T.rank → D.host.E) :
    ((c • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t) : WO S T).map (toEAf D)) =
      (toEAf D (c * incA D a) * ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D)) •
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)) *
          Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply,
    GlobalTheory.LatVac.finTens, GlobalTheory.LatVac.genMap, map_mul]
  change toEAf D c * ((a * t i * ∑ k, star (s k) * S.gram k j) ⊗ₜ[D.host.F] α) =
    toEAf D c * (a ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) *
      ((t i ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((∑ k, star (s k) * S.gram k j) ⊗ₜ[D.host.F] (1 : Af D.host.F)))
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc]

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem adj_shape {m n : ℕ} (c : EAf D) (C : Matrix (Fin m) (Fin 1) (EAf D)) (R : Matrix (Fin 1) (Fin n) (EAf D)) :
    ((c • (C * R)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      GlobalTheory.AdelicLatMove.cF D c • ((R.map (GlobalTheory.AdelicLatMove.cF D))ᵀ * (C.map (GlobalTheory.AdelicLatMove.cF D))ᵀ) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun z _ => by rw [map_mul, mul_comm]

theorem cF_eToEAf (x : D.host.E) : GlobalTheory.AdelicLatMove.cF D (eToEAf D x) = eToEAf D (star x) := rfl

end GlobalTheory.ConjHalfInt

namespace GlobalTheory.ConjHalfInt
variable {D : D7}

theorem frMapAdj_neg {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    frMapAdj S T βS βT (-x) = -frMapAdj S T βS βT x :=
  (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_neg x

theorem frMapAdj_zero {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 :=
  (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_zero

theorem frMapO_add {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add _ (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_neg {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    frMapO S T βS βT (-x) = -frMapO S T βS βT x :=
  (AddMonoidHom.mk' _ (frMapO_add βS βT)).map_neg x

theorem frMapO_zero {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapO S T βS βT 0 = 0 :=
  (AddMonoidHom.mk' _ (frMapO_add βS βT)).map_zero

end GlobalTheory.ConjHalfInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRamifiedPlacesHeckeCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNotMemOfPrimeNe
namespace GlobalTheory.NatCastNotMemPrimeIdeal

theorem natCast_notMem_of_prime_ne {L : Type} [Field L] [NumberField L]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : q ≠ p)
    (hqw : (q : NumberField.RingOfIntegers L) ∈ w.asIdeal) :
    (p : NumberField.RingOfIntegers L) ∉ w.asIdeal := by
  intro hpw
  have hc : IsCoprime (q : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hp).mpr hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : NumberField.RingOfIntegers L) * (q : NumberField.RingOfIntegers L)
      + (b : NumberField.RingOfIntegers L) * (p : NumberField.RingOfIntegers L) = 1 := by
    have := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers L) hab
    push_cast at this
    exact this
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hqw) (w.asIdeal.mul_mem_left _ hpw)

end GlobalTheory.NatCastNotMemPrimeIdeal
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.ChiUnit

open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_inv {N : ℕ} {u : ℂ} (hu : UnitOff N u) : UnitOff N u⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  exact ⟨inv_ne_zero hu0, n, hn2, by rw [inv_inv]; exact hn1⟩

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  ⟨one_ne_zero, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩

theorem unitOff_pow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℕ) : UnitOff N (u ^ k) := by
  induction k with
  | zero => simpa using unitOff_one N
  | succ k ih => rw [pow_succ]; exact unitOff_mul ih hu

theorem unitOff_zpow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℤ) : UnitOff N (u ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact unitOff_pow hu m
  · rw [_root_.zpow_neg, zpow_natCast]; exact unitOff_inv (unitOff_pow hu m)

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitOff_one N
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_of_pow {N : ℕ} {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : UnitOff N (u ^ k)) : UnitOff N u := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  have hN : IsIntegral ℤ ((N : ℂ) ^ (n * (k - 1))) := by
    have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
    exact this.pow _
  refine ⟨fun h => hu0 (by rw [h, zero_pow hk.ne']), n, ?_, ?_⟩
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * u ^ k) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn1
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u⁻¹) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * (u ^ k)⁻¹) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, inv_pow]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn2

theorem unitOff_of_pow_eq_one (N : ℕ) {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : UnitOff N u :=
  unitOff_of_pow hk (by rw [hu]; exact unitOff_one N)

theorem unitOff_of_mul_eq {N m : ℕ} {a b : ℂ} (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (hab : a * b = (N : ℂ) ^ m) (hN : N ≠ 0) : UnitOff N a := by
  have hNm : (N : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  have ha0 : a ≠ 0 := fun h => hNm (by rw [← hab, h, zero_mul])
  refine ⟨ha0, m, ?_, ?_⟩
  · have : IsIntegral ℤ ((N : ℂ) ^ m) := by
      have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      exact this.pow _
    exact this.mul ha
  · have e : (N : ℂ) ^ m * a⁻¹ = b := by rw [← hab]; field_simp
    rw [e]; exact hb

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem LR {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (n : ℕ) (h : χ ^ n = 1)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (k : Lˣ) : (χ.locK w k) ^ n = 1 := by
  have e : (χ ^ n).locK w k = (χ.locK w k) ^ n := by
    simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]
  rw [← e, h]
  simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)} (hw : χ.UnrAt w) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a)
    (h1 : a ∈ w.asIdeal) (h2 : a ∉ w.asIdeal ^ 2) : χ.locK w k = χ.val w :=
  χ.val_eq hw _ (by
    unfold Formalism.L2.Host.IsUnifAt
    rw [GlobalTheory.TypeValues.val_atFin w k a hk, GlobalTheory.TypeValues.intValuation_eq_of_mem h1 h2])

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem finite_ramified_places_hecke_character {D : D7} (χ : Formalism.L2.Host.HChar D.host.E)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬Formalism.L2.Host.OverP D.host (D.host.g k) v) → χ.UnrAt v) :
    {w | ¬ χ.UnrAt w}.Finite := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hI : Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hc
  refine hw (h w fun k hk => hc ?_)
  unfold Formalism.L2.Host.OverP at hk
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hk
  · exact Ideal.mul_mem_left _ _ hk

theorem not_mem_of_prime_ne {L : Type} [Field L] [NumberField L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) (hqw : (q : 𝓞 L) ∈ w.asIdeal) : (p : 𝓞 L) ∉ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | (apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne ..)

end GlobalTheory.ChiUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOFixOfIsThetaAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.VacFix

variable {D : D7}

theorem symplO_eq_zero (S T : HSp D) (x y : WO S T)
    (h : ∀ c b d a, cA D (y c b) * x d a = 0) : symplO S T x y = 0 := by
  have h0 : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    have := h c b d a
    calc _ = incA D ((HSpace.gram S)⁻¹ a b) * incA D (HSpace.gram T c d) *
        (cA D (y c b) * x d a) := by ring
      _ = 0 := by rw [this, mul_zero]
  unfold symplO
  rw [h0, mul_zero, map_zero]

theorem heisO_fix_of_isThetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ) (u : WO S T), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → (∀ i j, e * u i j = 0) → (∀ i j, cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  intro D ψ S T e Λ c f₀ Φ f u hf h1 h2 h0
  obtain ⟨⟨M, hM⟩, hall⟩ := hf
  have hM' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀
      ((GlobalTheory.SplitScalar.heisL ψ S T u) ∘ₗ M) := by
    refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.trans Ψ hΨ x hx, GlobalTheory.SplitScalar.heisO_comm, symplO_eq_zero, AddChar.map_zero_eq_one,
        one_smul]
      intro c b d a
      rw [← hx c b, map_mul]
      linear_combination cA D (x c b) * h2 d a
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.modul Ψ hΨ y hy, GlobalTheory.SplitScalar.heisO_comm ψ S T y u, symplO_eq_zero,
        AddChar.map_zero_eq_one, one_smul]
      intro c b d a
      have h3 : cA D e * cA D (u c b) = 0 := by rw [← map_mul, h1, map_zero]
      rw [← hy d a]
      linear_combination y d a * h3
    · simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
      rw [hM.vac, h0]
  have e1 := hall M hM
  have e2 := hall _ hM'
  simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at e2
  rw [← e1] at e2
  exact e2.symm

end GlobalTheory.VacFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTranslatedDatumAtTranslatedClass
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTranslatedDatumAtTranslatedClass
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace CompanionTheory.Member.ThetaTranslation

theorem thetaKO_translate {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hom : IsWeilDatumO ψ S T χS χT om) (θ : InfFam D)
    (hθ : IsInfFam θ) (z : GA D S) (hz : z ∈ GfC S) (sS sT BS BT) (f : WO S T → ℂ) (P) (hf : IsThetaFunO ψ S T f)
    (c : ℂ) (h : GA D S) (g : GA D T) :
    thetaKO om h g (pureTensorO ψ θ S T sS sT BS BT (c • om (z, 1) f) P) =
      c * thetaKO om (h * z) g (pureTensorO ψ θ S T sS sT BS BT f P) := by
  rw [GlobalTheory.FiniteFock.pureTensorO_smul,
    ← GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ S T χS χT om hom θ hθ z hz 1 (one_mem _) sS sT BS BT f P hf]
  unfold thetaKO
  have e : ((h * z, g) : GA D S × GA D T) = (h, g) * (z, 1) := by rw [Prod.mk_mul_mk, mul_one]
  rw [e, map_mul, map_smul, Module.End.mul_apply, Pi.smul_apply, smul_eq_mul]

end CompanionTheory.Member.ThetaTranslation

set_option maxHeartbeats 1000000 in
theorem CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (z : GA D (Vc D i)) (c : ℂ), z ∈ GfC (Vc D i) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)), ser R i t (c • R.ωP i t (z, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * z) w g := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i t z c hz u h w g
  have hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have h1 := hC.thP.pt_theta i t 1
    unfold RealDat.ptP at h1
    rwa [GlobalTheory.FiniteFock.pureTensorO_one] at h1
  exact CompanionTheory.Member.ThetaTranslation.thetaKO_translate R.ψ _ _ _ _ (R.ωP i t) (hC.thP.ωP i t) R.θ hC.models.inf z hz _ _ _ _ _ _ hf c h g

end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
theorem _root_.GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (z : GA D (Vc D i)) (c : ℂ), z ∈ GfC (Vc D i) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)), ser R i t (c • R.ωP i t (z, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * z) w g := by
  first | exact @CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class | exact CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class | (intros; apply CompanionTheory.Member.thetaSeries_translated_datum_eq_translated_class <;> assumption)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTranslatedDatumAtTranslatedClassStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_translated_datum_at_translated_class : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (z : GA D (Vc D i)) (c : ℂ), z ∈ GfC (Vc D i) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Vc D i)) (w : (R.cV i).W) (g : GA D (Wc D i)), ser R i t (c • R.ωP i t (z, 1) (R.vP i t)) u h w g = c * ser R i t (R.vP i t) u (h * z) w g := by
  first | exact @GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class | exact GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class | (intros; apply GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D}

def divPts (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) : AddSubgroup (WO S T) where
  carrier := {y | c • y = y ∧ N • y ∈ Λ}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [smul_add, hx1, hy1], by rw [nsmul_add]; exact Λ.add_mem hx2 hy2⟩
  zero_mem' := ⟨smul_zero _, by rw [nsmul_zero]; exact Λ.zero_mem⟩
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨by rw [smul_neg, hx1], by rw [smul_neg]; exact Λ.neg_mem hx2⟩

theorem mem_divPts {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} {y : WO S T} :
    y ∈ divPts Λ c N ↔ c • y = y ∧ N • y ∈ Λ := Iff.rfl

abbrev DQ (Λ : AddSubgroup (WO S T)) (c : AE D) (N : ℕ) :=
  ↥(divPts Λ c N) ⧸ (Λ ⊓ GlobalTheory.PlaceModel.half S T c).addSubgroupOf (divPts Λ c N)

noncomputable def rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) : ↥(divPts Λ c N) :=
  (QuotientAddGroup.mk_surjective q).choose

theorem mk_rep {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} (q : DQ Λ c N) :
    (QuotientAddGroup.mk (rep q) : DQ Λ c N) = q :=
  (QuotientAddGroup.mk_surjective q).choose_spec

theorem rep_injective {Λ : AddSubgroup (WO S T)} {c : AE D} {N : ℕ} :
    Function.Injective fun q : DQ Λ c N => ((rep q : ↥(divPts Λ c N)) : WO S T) := by
  intro q₁ q₂ h
  rw [← mk_rep q₁, ← mk_rep q₂, Subtype.ext h]

variable (ψ : AddChar (AF D.host.F) ℂ)

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

variable {D : D7} {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ)

end GlobalTheory.DivPtFourier

namespace GlobalTheory.DivPtFourier

open scoped Classical

end GlobalTheory.DivPtFourier
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoPOfIsIoWAt
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.JointHarm
open scoped Classical

namespace GlobalTheory.IoAllTuples


set_option maxHeartbeats 1000000 in
theorem ioP_of_isIoW_at : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → ∀ (i : Fin D.R.m) (t₀ : T) (y : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t₀) (R.ptP i t₀) (RealDat.Delta i) y → R.PIoP i y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hF hM hω hv i t₀ y hy
  have hθ : IsInfFam R.θ := hM.inf
  have hth : ∀ t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := fun t => by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hv i t
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  have hvac := fun t => GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hv i t) (hth t)
  have hne : R.vP i t₀ ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i))
      ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hv i t₀)
  have hinj : Function.Injective (R.ptP i t₀) :=
    GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW i (sg0 D A)) (R.BV i) _ (hω i t₀).std hθ
      (fun τ => GlobalTheory.OneMapRef.VecP.isCartanInv_one_of_onb (hM.BV i τ)) (hM.BV i) (hth t₀) hne (hvac t₀)
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => GlobalTheory.JointHarm.onb_eq_one (hM.BV i τ)
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hM.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank := fun τ =>
    (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).rank.1.trans hrk.symm
  have hact := fun t => GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) _ (R.MW i (sg0 D A)) (R.BV i) (hω i t) hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hM.order i) _ _ (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T R.toLevCh A.μ0 hL i t τ).chiV)
    (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T R.toLevCh A.μ0 hL i t τ).chiW) x₁ x₂ x₃ (fun τ => (hx τ).1) (fun τ => (hx τ).2.1)
    (fun τ => (hx τ).2.2.1) _ (hth t) (hvac t)
  obtain ⟨y1, y2, y3⟩ := hy
  intro t
  refine ⟨fun u hu x w => ?_, fun τ k hk v u hu w => ?_, y3⟩
  · have hK : ∀ τ, (R.MW i (sg0 D A)).fr τ * compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) * ((R.MW i (sg0 D A)).fr τ)⁻¹ ∈
        Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) := fun τ => by
      rw [compAt_mt_one', Matrix.mul_one,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ))]
      exact one_mem_K
    have a0 := ((hact t₀) u hu 1 (one_mem _) hK).2 (y x w)
    have at' := ((hact t) u hu 1 (one_mem _) hK).2 (y x w)
    have e := hinj (a0.symm.trans (y1 u hu x w))
    exact at'.trans (congrArg (R.ptP i t) e)
  · have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (GlobalTheory.JointHarm.conj_mem_UH (R.MW i (sg0 D A)) τ hk)
    have hfr : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹ = 1 := fun ρ =>
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit ρ))
    have e : (fun ρ => (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
        (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹) = Pi.mulSingle τ k := by
      funext ρ
      rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
      by_cases h : ρ = τ
      · subst h
        rw [hs.2.1, Pi.mulSingle_eq_same]
        calc _ = ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) * k *
            ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
          _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
      · rw [hs.2.2 ρ h, Pi.mulSingle_eq_of_ne h, Matrix.mul_one, hfr]
    have hK : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
        (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ) := fun ρ => by
      rw [congrFun e ρ]
      by_cases h : ρ = τ
      · subst h; rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_K
    have a0 := ((hact t₀) 1 (one_mem _) _ hs.1 hK).2 (y (PiTensorProduct.tprod ℂ v) w)
    have at' := ((hact t) 1 (one_mem _) _ hs.1 hK).2 (y (PiTensorProduct.tprod ℂ v) w)
    have e2 := hinj (a0.symm.trans (y2 τ k hk v u hu w))
    exact at'.trans (congrArg (R.ptP i t) e2)

end GlobalTheory.IoAllTuples

end
end
