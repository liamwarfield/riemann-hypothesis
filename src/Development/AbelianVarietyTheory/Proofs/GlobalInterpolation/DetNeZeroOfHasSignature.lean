module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimeUnder

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetNeZeroOfHasSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetEqNormMulOfSelfDualSameSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetEqNormMulOfSelfDualSameSignature
open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix ComplexConjugate
attribute [local instance] IsCMField.starRing

namespace GlobalTheory.SelfDualDet
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy GlobalTheory.LocalLattice

theorem congr_of_hasSignature {r p q : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : Formalism.UG.HasSignature A p q) (hB : Formalism.UG.HasSignature B p q) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ Bᵀ = Qᵀ * Aᵀ * Q.map conj := by
  obtain ⟨e, P, hP⟩ := hA
  obtain ⟨f, R, hR⟩ := hB
  have hc : ∀ M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ :=
    fun _ => rfl
  rw [hc] at hP hR
  have h1 : Matrix.reindex f f B = (P * R⁻¹).1ᴴ * Matrix.reindex e e A * (P * R⁻¹).1 := by
    have h2 : (R⁻¹).1ᴴ * R.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    calc Matrix.reindex f f B = ((R⁻¹).1ᴴ * R.1ᴴ) * Matrix.reindex f f B * (R.1 * (R⁻¹).1) := by
          rw [h2, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (R⁻¹).1ᴴ * (R.1ᴴ * Matrix.reindex f f B * R.1) * (R⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hR, ← hP, Units.val_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
  generalize P * R⁻¹ = S at h1
  refine ⟨S.1.submatrix e f, ?_, ?_⟩
  · refine (Matrix.isUnit_det_of_right_inverse (B := (S⁻¹).1.submatrix f e) ?_).ne_zero
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  · have h3 := congrArg (fun M => (Matrix.submatrix M f f)ᵀ) h1
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] at h3
    rw [← Matrix.submatrix_mul_equiv _ _ f e f, ← Matrix.submatrix_mul_equiv _ _ f e e,
      Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] at h3
    exact h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem det_eq_of_matrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {r r' : ℕ} (h : r = r')
    {G : Matrix (Fin r) (Fin r) E} {G' : Matrix (Fin r') (Fin r') E}
    (hG : ∀ a b, cc (Gᵀ a b) = Gᵀ b a) (hG' : ∀ a b, cc (G'ᵀ a b) = G'ᵀ b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    {L : Submodule (𝓞 E) (Fin r → E)} {L' : Submodule (𝓞 E) (Fin r' → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Gᵀ x y))
    (hsd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm G'ᵀ x y))
    (hs : ∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (G.map τ) p q ∧ Formalism.UG.HasSignature (G'.map τ) p q) :
    ∃ z : E, G'.det = z * star z * G.det := by
  subst h
  obtain ⟨P, -, hP⟩ := congr_of_modular (E := E) (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero
    (fun _ hz => mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hz)))
    hG hG' (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) hL hL'
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd)
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd')
    fun τ => by
      obtain ⟨p, q, h1, h2⟩ := hs τ
      exact congr_of_hasSignature h1 h2
  have h1 := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, Matrix.det_transpose,
    Published.det_map_cc] at h1
  refine ⟨P.det, h1.trans ?_⟩
  change _ = _ * cc _ * _
  ring

theorem det_eq_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  intro E _ _ _ hc W₁ W₂ h₁ h₂ hr hs
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  exact det_eq_of_matrix hr (fun a b => W₁.herm.eq (W₁.frame b) (W₁.frame a))
    (fun a b => W₂.herm.eq (W₂.frame b) (W₂.frame a))
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₁).ne_zero (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₂).ne_zero
    (isLattice_coordLat W₁ W₁.L0 W₁.standardTuple_isLattice W₁.baseLattice_isUnimodular)
    (isLattice_coordLat W₂ W₂.L0 W₂.standardTuple_isLattice W₂.baseLattice_isUnimodular)
    (selfDual_coordLat W₁ W₁.L0 W₁.baseLattice_isUnimodular) (selfDual_coordLat W₂ W₂.L0 W₂.baseLattice_isUnimodular)
    fun τ => ⟨_, _, h₁ τ, hs τ ▸ h₂ τ⟩

end GlobalTheory.SelfDualDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetEqNormMulOfSelfDualSameSignatureStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] IsCMField.starRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_eq_norm_mul_of_selfDual_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  first | exact @GlobalTheory.SelfDualDet.det_eq_norm_mul | exact GlobalTheory.SelfDualDet.det_eq_norm_mul | (intros; apply GlobalTheory.SelfDualDet.det_eq_norm_mul <;> assumption)
end
end

noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.LandherrSignature

theorem det_ne_zero_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature A p q) : A.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  intro h0
  have h1 := congrArg det hP
  rw [det_mul, det_mul, det_reindex_self, h0, mul_zero, zero_mul, Formalism.UG.Jpq, det_fromBlocks_zero₂₁, det_neg] at h1
  simp at h1
  exact pow_ne_zero q (neg_ne_zero.2 one_ne_zero) h1.symm

theorem congr_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ} {p q : ℕ}
    (hA : Formalism.UG.HasSignature A p q) (hB : Formalism.UG.HasSignature B p q) :
    ∃ Q : Matrix n n ℂ, Q.det ≠ 0 ∧ Qᴴ * A * Q = B := by
  obtain ⟨e, -⟩ := id hA
  have key : ∀ C : Matrix n n ℂ, Formalism.UG.HasSignature C p q →
      ∃ R : Matrix n n ℂ, R.det ≠ 0 ∧ Rᴴ * C * R = (Formalism.UG.Jpq p q).submatrix e e := by
    rintro C ⟨e', P, hP⟩
    have hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * C.submatrix e'.symm e'.symm *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hP
    refine ⟨P.val.submatrix e' e, ?_, ?_⟩
    · refine IsUnit.ne_zero (isUnit_det_of_right_inverse (B := P.inv.submatrix e e') ?_)
      rw [submatrix_mul_equiv, P.val_inv, submatrix_one_equiv]
    · have : C = (C.submatrix e'.symm e'.symm).submatrix e' e' := by simp
      rw [this, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hP']
  obtain ⟨R, hR, h1⟩ := key A hA
  obtain ⟨S, hS, h2⟩ := key B hB
  have hu : IsUnit S.det := hS.isUnit
  refine ⟨R * S⁻¹, ?_, ?_⟩
  · rw [det_mul]
    exact mul_ne_zero hR (isUnit_nonsing_inv_det _ hu).ne_zero
  · calc (R * S⁻¹)ᴴ * A * (R * S⁻¹) = S⁻¹ᴴ * (Rᴴ * A * R) * S⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (S * S⁻¹)ᴴ * B * (S * S⁻¹) := by
          rw [h1, ← h2]
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = B := by rw [mul_nonsing_inv _ hu]; simp

theorem form_eq {E V n : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V] [Fintype n]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (b : Module.Basis n E V) (x y : n → E) :
    h (b.equivFun.symm x) (b.equivFun.symm y) = star x ⬝ᵥ ((Matrix.of fun i j => h (b i) (b j)) *ᵥ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, dotProduct, mulVec, Matrix.of_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem congr_of_det_norm {n : ℕ} (G G' : Matrix (Fin n) (Fin n) E) (hG : Gᴴ = G) (hG' : G'ᴴ = G')
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) (hn : ∃ z : E, G.det = z * star z * G'.det)
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ Qᴴ * G.map τ * Q = G'.map τ) :
    ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧ Pᴴ * G * P = G' := by
  obtain ⟨z, hz⟩ := hn
  obtain ⟨P, hP, h⟩ := GlobalTheory.QNorm.landherr_and_landherrSt.1 E n G G'
    (fun a b => congrFun (congrFun hG b) a) (fun a b => congrFun (congrFun hG' b) a) hd hd'
    (fun τ => by
      obtain ⟨Q, hQ, h⟩ := hs τ
      refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
      · have : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
        rw [this]
        exact (map_ne_zero _).mpr hQ
      · rw [← h]
        congr 1
        ext a b
        simp)
    ⟨z, by rw [div_eq_iff hd']; exact hz⟩
  refine ⟨P.map ReciprocityTheory.ChartRestriction.G.FD.cc, ?_, ?_⟩
  · rw [GlobalTheory.Published.det_map_cc]
    exact GlobalTheory.Published.cc_ne_zero hP
  · rw [h]
    congr 2
    ext a b
    exact star_star (P b a)

theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W₁ W₂ : HSpace E) (h₁ : W₁.SigOK) (h₂ : W₂.SigOK)
    (hr : W₁.rank = W₂.rank) (hs : ∀ τ, W₁.sig τ = W₂.sig τ) :
    ∃ φ : W₁.V ≃ₗ[E] W₂.V, ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y := by
  obtain ⟨z, hz⟩ := GlobalTheory.T.det_eq_norm_mul_of_selfDual_same_signature E hc W₁ W₂ h₁ h₂ hr hs
  let c : Fin W₁.rank ≃ Fin W₂.rank := finCongr hr
  have hH : ∀ W : HSpace E, W.gramᴴ = W.gram := fun W => by
    ext a b
    exact W.herm.eq _ _
  have hd : ∀ W : HSpace E, W.SigOK → W.gram.det ≠ 0 := fun W hW h0 => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine det_ne_zero_of_hasSignature (hW τ) ?_
    have : (W.gram.map τ).det = τ W.gram.det := (RingHom.map_det τ W.gram).symm
    rw [this, h0, map_zero]
  obtain ⟨P, hP0, hP⟩ := congr_of_det_norm (W₂.gram.submatrix c c) W₁.gram
    (by rw [conjTranspose_submatrix, hH]) (hH W₁) (by rw [det_submatrix_equiv_self]; exact hd W₂ h₂) (hd W₁ h₁)
    ⟨z, by rw [det_submatrix_equiv_self]; exact hz⟩
    (fun τ => by
      refine congr_of_hasSignature ?_ (h₁ τ)
      rw [hs τ]
      obtain ⟨e, Q, hQ⟩ := h₂ τ
      refine ⟨c.trans e, Q, ?_⟩
      rw [← hQ]
      congr 2)
  let b₂ := W₂.frame.reindex c.symm
  have e₂ : (Matrix.of fun i j => W₂.hT (b₂ i) (b₂ j)) = W₂.gram.submatrix c c := by
    ext i j
    simp [b₂, HSpace.gram]
  refine ⟨(W₁.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit))).trans
    b₂.equivFun.symm, fun x y => ?_⟩
  obtain ⟨u, rfl⟩ := W₁.frame.equivFun.symm.surjective x
  obtain ⟨v, rfl⟩ := W₁.frame.equivFun.symm.surjective y
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [form_eq, form_eq, e₂]
  change star (P *ᵥ u) ⬝ᵥ (_ *ᵥ (P *ᵥ v)) = star u ⬝ᵥ (W₁.gram *ᵥ v)
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hP]

end CM

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isometry_host : ∀ (D : D7) (W₁ W₂ : HSpace D.host.E), W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank →
    (∀ τ, W₁.sig τ = W₂.sig τ) →
    ∃ φ : W₁.V ≃ₗ[D.host.E] W₂.V, ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W₁ W₂ => exists_isometry (E := D.host.E) D.sp.cm.cmUnram W₁ W₂

end GlobalTheory.LandherrSignature
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PageDutiesOfClassSeven
namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX

theorem tameList_eq {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : DC.tameList χ = Formalism.MainNotions.tameList χ := by
  funext o
  rcases o with _ | ⟨j, _ | _⟩ <;> rfl

theorem tameDistinct_iff (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) :
    DC.TameDistinct r g χ ↔ Formalism.MainNotions.TameDistinct r g χ := by
  unfold DC.TameDistinct Formalism.MainNotions.TameDistinct
  rw [tameList_eq]

end GlobalTheory.EX.DQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SemisimpleIsoOfTraceEq
namespace GlobalTheory.TraceConj

open Formalism.MainNotions.N UpperTheory.V.Af

theorem main : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ)
    (r r' : Γ →* GL (Fin n) k), IsSSRep r → IsSSRep r' →
    (∀ s, ((r s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace =
      ((r' s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → RepIso r r' := by
  intro Γ k _ _ _ n r r' hr hr' htr
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hr hr' (fun g => by
    refine GlobalTheory.QuadKernelConj.charpoly_eq_of_trace_pow _ _ fun m => ?_
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
    exact htr (g ^ m))
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.TraceConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValues
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.DIV hiding unifVal
open Formalism.L2.Host (HChar atFin IsUnitAt IsUnifAt)
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.ReadEx GlobalTheory.Mem.LocTriv Neutral.B1

namespace GlobalTheory.TwistVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr F E K} {ξ : HChar E}

theorem evP_toRInt (P : HeightOneSpectrum (𝓞 E)) (b : 𝓞 E) :
    evP F P (toRInt F E b : AfE F E) = algebraMap E (P.adicCompletion E) (b : E) := by
  change afIso F E ((b : E) ⊗ₜ[F] 1) P = _
  rw [afIso_tmul_one]
  rfl

theorem valued_lt_of_mem {P : HeightOneSpectrum (𝓞 E)} {w : RInt F E} (h : w ∈ P.asIdeal.map (toRInt F E)) :
    Valued.v (evP F P (w : AfE F E)) < 1 := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [evP_toRInt, Formalism.UG.P.levelaf_valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hb
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact Valuation.map_add_lt _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 a.2 P)) hx

theorem val_le_two {P : HeightOneSpectrum (𝓞 E)} {z : RInt F E} (hz : z ∈ (P.asIdeal ^ 2).map (toRInt F E)) :
    Valued.v (evP F P (z : AfE F E)) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
  GlobalTheory.UnifConj.val_le_of_mem (afIso F E) (afIso_tmul_one F E) (mem_rInt_iff F E) P 2 z hz

theorem exp_neg_two_lt {P : HeightOneSpectrum (𝓞 E)} {b : 𝓞 E} (hb2 : b ∉ P.asIdeal ^ 2) :
    WithZero.exp (-((2 : ℕ) : ℤ)) < Valued.v (algebraMap E (P.adicCompletion E) (b : E)) := by
  rw [GlobalTheory.SuppIdele.val_algebraMap, ← not_le, P.intValuation_le_pow_iff_mem]
  exact hb2

theorem value_of_congr2 (h : Reads σ μ ξ) (ht : ∀ P, ξ.TameAt P) {P : HeightOneSpectrum (𝓞 E)} {u : (AfE F E)ˣ}
    {y : RInt F E} (hy : (y : AfE F E) = u) {b : 𝓞 E} (hb2 : b ∉ P.asIdeal ^ 2) {x : Eˣ} (hx : (x : E) = b)
    (h1 : y - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E))
    (h2 : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → y - 1 ∈ Q.asIdeal.map (toRInt F E)) :
    σ ((μ u : Kˣ) : K) = ((ξ.locK P x : ℂˣ) : ℂ) := by
  have hb := exp_neg_two_lt hb2
  have a1 : Valued.v (evP F P (u : AfE F E) - algebraMap E (P.adicCompletion E) (b : E)) ≤
      WithZero.exp (-((2 : ℕ) : ℤ)) := by
    have := val_le_two h1
    rwa [AddSubgroupClass.coe_sub, map_sub, evP_toRInt, hy] at this
  have a2 : ∀ Q, Q ≠ P → Valued.v (evP F Q (u : AfE F E) - 1) < 1 := fun Q hQ => by
    have := valued_lt_of_mem (h2 Q hQ)
    rwa [AddSubgroupClass.coe_sub, map_sub, Subring.coe_one, map_one, hy] at this
  set l := finAf F E (localIdele E P (atFin P x)) with hl
  have key : ∀ Q, Valued.v (evP F Q ((u / l : (AfE F E)ˣ) : AfE F E) - 1) < 1 := fun Q => by
    have e1 : evP F Q ((u / l : (AfE F E)ˣ) : AfE F E) * evP F Q (l : AfE F E) = evP F Q (u : AfE F E) := by
      rw [← map_mul, ← Units.val_mul, div_mul_cancel]
    have e2 : evP F Q (l : AfE F E) = ev Q (localIdele E P (atFin P x) : AdeleRing (𝓞 E) E) :=
      GlobalTheory.Mem.ReadTwist.afIso_finAf_apply _ Q
    by_cases hQ : Q = P
    · subst hQ
      rw [show ev Q (localIdele E Q (atFin Q x) : AdeleRing (𝓞 E) E) = atFin Q x from Neutral.B1.localIdele_snd_self E Q (atFin Q x)] at e2
      have e3 : ((atFin Q x : (Q.adicCompletion E)ˣ) : Q.adicCompletion E) = algebraMap E _ (b : E) := by
        rw [← hx]; rfl
      rw [e2, e3] at e1
      rw [← e1, ← sub_one_mul, map_mul] at a1
      by_contra hn
      push_neg at hn
      exact absurd (lt_of_lt_of_le hb (le_mul_of_one_le_left' hn)) (not_lt.2 a1)
    · rw [show ev Q (localIdele E P (atFin P x) : AdeleRing (𝓞 E) E) = 1 from (Neutral.B1.localIdele_isSupportedAt E P (atFin P x)).2 Q hQ] at e2
      rw [e2, mul_one] at e1
      rw [e1]
      exact a2 Q hQ
  have hu : u / l ∈ intU F E := by
    refine (mem_intU_iff (u / l)).2 fun Q => ?_
    change Valued.v (evP F Q ((u / l : (AfE F E)ˣ) : AfE F E)) = 1
    have := key Q
    rw [← map_one (Valued.v : Valuation (Q.adicCompletion E) _)] at this ⊢
    exact Valuation.map_eq_of_sub_lt _ (by simpa using this)
  have hk : u / l ∈ μ.ker := by
    refine ker_of_reads h (map_toIdl_eq_one ht hu fun Q _ => le_exp_neg_one ?_)
    rw [map_sub, map_one]
    exact key Q
  rw [MonoidHom.mem_ker, map_div, div_eq_one] at hk
  rw [hk]
  exact (h _).symm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K] (σ : K →+* ℂ) (μ : Chr F E K) (ξ : Formalism.L2.Host.HChar E), GlobalTheory.Mem.Col2.Reads σ μ ξ → (∀ P, ξ.TameAt P) → ∀ P : HeightOneSpectrum (𝓞 E), (ξ.UnrAt P → σ ((unifVal μ P : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ)) ∧ (((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ ((qVal μ P : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ)) := by
  intro F E _ _ _ _ _ K _ σ μ ξ h ht P
  have hne : ∀ {b : 𝓞 E}, b ∉ P.asIdeal ^ 2 → (b : E) ≠ 0 := fun {b} hb e =>
    hb ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  constructor
  · intro hunr
    have hv : ∀ {c : 𝓞 E}, c ∈ P.asIdeal → (hc2 : c ∉ P.asIdeal ^ 2) →
        ((ξ.locK P (Units.mk0 _ (hne hc2)) : ℂˣ) : ℂ) = ((ξ.val P : ℂˣ) : ℂ) := fun {c} hc hc2 => by
      refine congrArg _ (ξ.val_eq hunr _ ?_)
      show Valued.v (algebraMap E (P.adicCompletion E) (c : E)) = _
      exact GlobalTheory.UnifConj.val_of_cong P _ c hc hc2 (by rw [sub_self, map_zero]; exact zero_le')
    obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
      have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
      simpa using this
    obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) b rfl
    have hy : σ ((μ y : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ) :=
      (value_of_congr2 h ht a1 hb2 (x := Units.mk0 _ (hne hb2)) rfl a3 a4).trans (hv hb hb2)
    have hex : ∃ k, IsUnifVal μ P k := by
      refine ⟨μ y, fun w _ z z₀ c f1 hc hc2 _ f3 f4 => Units.ext (σ.injective ?_)⟩
      rw [hy, ← hv hc hc2]
      exact value_of_congr2 h ht f1 hc2 rfl f3 f4
    unfold unifVal
    rw [dite_eq_left hex, ← (hex.choose_spec (P.under (𝓞 F)) rfl y y₀ b a1 hb hb2 a2 a3 a4)]
    exact hy
  · intro hq q hqe
    set b : 𝓞 E := ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) with hbdef
    have hqb : (q : E) = (b : E) := by rw [hqe, hbdef]; simp
    obtain ⟨y, y₀, a1, a2, a3, a4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P (P.under (𝓞 F)) b rfl
    have hy : σ ((μ y : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ) := value_of_congr2 h ht a1 hq hqb a3 a4
    have hex : ∃ k, IsQValC μ P k := by
      refine ⟨μ y, fun w _ z z₀ f1 _ f3 f4 => Units.ext (σ.injective ?_)⟩
      rw [hy]
      exact value_of_congr2 h ht f1 hq hqb f3 f4
    unfold qVal qValC
    rw [dite_eq_left hex, ← (hex.choose_spec (P.under (𝓞 F)) rfl y y₀ a1 a2 a3 a4)]
    exact hy

end GlobalTheory.TwistVal
end
end
