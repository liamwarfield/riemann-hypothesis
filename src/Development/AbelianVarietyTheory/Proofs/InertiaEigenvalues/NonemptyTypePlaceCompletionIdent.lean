module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsMinpolyPhi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDefiniteUnitaryDoubleCosets
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

namespace GlobalTheory.TypeIdent

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.TypeRec.factG

theorem irreducible_natCast_compl {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {g : ℕ}
    (hin : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (hnot : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) :
    Irreducible ((g : ℕ) : 𝒪[w.adicCompletion E]) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hle : ∀ y : 𝒪[w.adicCompletion E], Valued.v (y : w.adicCompletion E) ≤ 1 := fun y =>
    he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 y.2)
  have hunit : ∀ y : 𝒪[w.adicCompletion E], IsUnit y ↔ Valued.v (y : w.adicCompletion E) = 1 := fun y => by
    rw [← he.eq_one_iff_eq_one]
    exact (Valuation.integer.integers (valuation (w.adicCompletion E))).isUnit_iff_valuation_eq_one
  have hv : Valued.v ((g : ℕ) : w.adicCompletion E) = w.intValuation ((g : ℕ) : 𝓞 E) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E), ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    congr 1
    exact ((map_natCast (algebraMap E (w.adicCompletion E)) g).symm).trans
      (congrArg (algebraMap E (w.adicCompletion E)) (map_natCast (algebraMap (𝓞 E) E) g).symm)
  have h1 : w.intValuation ((g : ℕ) : 𝓞 E) ≤ WithZero.exp (-1 : ℤ) := by
    simpa using (w.intValuation_le_pow_iff_mem ((g : ℕ) : 𝓞 E) 1).mpr (by rwa [pow_one])
  have h2 : WithZero.exp (-2 : ℤ) < w.intValuation ((g : ℕ) : 𝓞 E) := by
    by_contra hc
    exact hnot ((w.intValuation_le_pow_iff_mem _ 2).mp (by simpa using not_lt.1 hc))
  have hc : (((g : ℕ) : 𝒪[w.adicCompletion E]) : w.adicCompletion E) = (g : w.adicCompletion E) := by simp
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [hunit, hc, hv]
    intro e
    rw [e, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · have h3 : Valued.v (a : w.adicCompletion E) * Valued.v (b : w.adicCompletion E) =
        w.intValuation ((g : ℕ) : 𝓞 E) := by
      rw [← hv, ← map_mul, ← hc, hab]; rfl
    rw [← h3] at h1 h2
    have h0 := (zero_le.trans_lt h2).ne'
    have ha := left_ne_zero_of_mul h0
    have hb := right_ne_zero_of_mul h0
    have ha1 := hle a
    have hb1 := hle b
    rw [hunit, hunit]
    rw [← WithZero.exp_log ha] at h2 ha1 ⊢
    rw [← WithZero.exp_log hb] at h2 hb1 ⊢
    rw [← WithZero.exp_add, WithZero.exp_lt_exp] at h2
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
    rw [← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
    omega

theorem nonempty_ident : ∀ D : D7, Nonempty (GlobalTheory.TypeRec.Ident D) := by
  intro D
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have key : ∀ k v, ∃ φ : ℚ_[D.host.g k] ≃+* (D.naut.plGw k v).adicCompletion D.host.E, Continuous φ := by
    intro k v
    obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)
    haveI : CharZero ((D.naut.plGw k v).adicCompletion D.host.E) :=
      charZero_of_injective_ringHom (algebraMap D.host.E _).injective
    obtain ⟨φ, h, -⟩ := GlobalTheory.QpChar.exists_ringEquiv_padic ((D.naut.plGw k v).adicCompletion D.host.E) (D.host.g k)
      ((GlobalTheory.LocLanglands.resCard_eq_normV _).trans (by
        simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h1)) (irreducible_natCast_compl _ (D.naut.plGw_over k v) h2)
    exact ⟨φ, h⟩
  exact ⟨⟨fun k v => (key k v).choose, fun k v => (key k v).choose_spec⟩⟩

end GlobalTheory.TypeIdent

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_typePlaceCompletionIdent : ∀ D : D7, Nonempty (Ident D) := by
  first | exact @GlobalTheory.TypeIdent.nonempty_ident | exact GlobalTheory.TypeIdent.nonempty_ident | (intros; apply GlobalTheory.TypeIdent.nonempty_ident <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TameRecord

section Transport

variable {G H V : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_comp (ρ : Representation ℂ H V) (φ : G →* H) (hφ : Continuous φ) (h : GlobalTheory.PRep.IsSmooth ρ) :
    GlobalTheory.PRep.IsSmooth (ρ.comp φ) := fun v => (h v).preimage hφ

theorem isIrreducible_comp (ρ : Representation ℂ H V) (φ : G →* H) (hs : Function.Surjective φ)
    (h : GlobalTheory.GLp.IsIrrRep ρ) : Representation.IsIrreducible (ρ.comp φ) := by
  rw [GlobalTheory.CuspRep.isIrreducible_iff]
  refine ⟨h.1, fun W hW => h.2 W fun y v hv => ?_⟩
  obtain ⟨x, rfl⟩ := hs y
  exact hW x v hv

theorem isSupercuspidal_comp [IsTopologicalGroup G] [IsTopologicalGroup H] (ρ : Representation ℂ H V) (φ : G →* H)
    (ψ : H →* G) (hφ : Continuous φ) (hψ : Continuous ψ) (h1 : ∀ x, ψ (φ x) = x) (h2 : ∀ y, φ (ψ y) = y)
    (h : GlobalTheory.PRep.IsSupercuspidal ρ) : GlobalTheory.PRep.IsSupercuspidal (ρ.comp φ) := by
  refine ⟨isSmooth_comp ρ φ hφ h.1, fun v l hl => ?_⟩
  have hl' : l ∈ GlobalTheory.PRep.smoothPart (Representation.dual ρ) := by
    have e : {y : H | Representation.dual ρ y l = l} =
        ψ ⁻¹' {x : G | Representation.dual (ρ.comp φ) x l = l} := by
      ext y
      simp [Representation.dual_apply, h2]
    show IsOpen {y : H | Representation.dual ρ y l = l}
    rw [e]
    exact hl.preimage hψ
  obtain ⟨C, hC, hCv⟩ := h.2 v l hl'
  refine ⟨ψ '' C, hC.image hψ, fun x hx => ?_⟩
  obtain ⟨z, hz, c, hc, e⟩ := hCv (φ x) hx
  refine ⟨ψ z, Subgroup.mem_center_iff.2 fun y => ?_, ψ c, ⟨c, hc, rfl⟩, ?_⟩
  · rw [← h1 y, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz (φ y))]
  · rw [← map_mul, ← e, h1]

end Transport

section GLMap

variable {n : Type} [Fintype n] [DecidableEq n] {K₁ K₂ : Type} [Field K₁] [Field K₂] [TopologicalSpace K₁]
  [TopologicalSpace K₂] [IsTopologicalRing K₁] [IsTopologicalRing K₂]

theorem continuous_glMap (f : K₁ →+* K₂) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := n) f) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id hf)

theorem glMap_symm_apply (i : K₁ ≃+* K₂) (x : GL n K₁) :
    Matrix.GeneralLinearGroup.map i.symm.toRingHom (Matrix.GeneralLinearGroup.map i.toRingHom x) = x := by
  ext a b
  simp

theorem glMap_apply_symm (i : K₁ ≃+* K₂) (y : GL n K₂) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom y) = y := by
  ext a b
  simp

end GLMap

theorem continuous_symm {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : Continuous i.symm := by
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toRingHom.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

def transRep {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) :=
  ⟨_, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom),
    isSmooth_comp _ _ (continuous_glMap _ (continuous_symm _ (I.i k v) (I.cont k v))) hs,
    isIrreducible_comp _ _ (fun y => ⟨_, glMap_apply_symm (I.i k v).symm y⟩) h⟩

theorem transRep_comp {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])) (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    (transRep I k v π h hs).ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom) = π.ρ :=
  MonoidHom.ext fun x => by
    show π.ρ _ = π.ρ x
    rw [glMap_symm_apply]

theorem iso_pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])) (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    Nonempty (π ≅ pull I k v (transRep I k v π h hs)) :=
  by
    have E : π.ρ.Equiv ((transRep I k v π h hs).ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)) := by
      rw [transRep_comp]; exact Representation.Equiv.refl _
    exact ⟨(Rep.mkIso E : Rep.of π.ρ ≅ _)⟩

end GlobalTheory.TameRecord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTypeVector
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

open Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant GlobalTheory.TypeLeaf

namespace GlobalTheory.GoodFree

end GlobalTheory.GoodFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodTypes

theorem seriesConj_of_labTie : Green → ∀ (D : D7) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L →
    GlobalTheory.GoodTypes.SeriesConj D :=
  fun hG D L hL k f hf =>
    GlobalTheory.GLq.GalSer.eSer_galois hG D ((eSerTie_iff D).2 ⟨L, hL⟩) starRingAut k f hf

end GlobalTheory.GoodTypes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgreeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesIdempotentStarCompatible_of_labelling_agree : Green → ∀ (D : D7) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L → GlobalTheory.GoodTypes.SeriesConj D := by
  first | exact @GlobalTheory.GoodTypes.seriesConj_of_labTie | exact GlobalTheory.GoodTypes.seriesConj_of_labTie | (intros; apply GlobalTheory.GoodTypes.seriesConj_of_labTie <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace GlobalTheory.TypeVec

def rtHom (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : GAf L n →* Module.End ℂ (GAf L n → ℂ) where
  toFun h := Formalism.L2.NG.rt L n h
  map_one' := by
    apply LinearMap.ext; intro f; funext g
    simp [Formalism.L2.NG.rt]
  map_mul' a b := by
    apply LinearMap.ext; intro f; funext g
    simp [Formalism.L2.NG.rt, mul_assoc]

def IsLiftAt {L : Type} [Field L] [NumberField L] [IsCMField L] {g : ℕ} [Fact g.Prime] {n : ℕ} (s : SplitPlace L)
    (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)) (y : GL (Fin n) ℤ_[g]) (x : GAf L n) : Prop :=
  TrivOutside {s.v} (x : GA L n) ∧ s.loc n x = Matrix.GeneralLinearGroup.map j.toRingHom (GlobalTheory.GLp.inc g n y)

attribute [local instance] GlobalTheory.TypeRec.factG

def KFix (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E)
    (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E))
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A) : Submodule ℂ A :=
  ⨅ (k : Fin 2) (v : D.nd.PlG k) (y : (GlobalTheory.GLp.red (D.host.g k) D.R.r).ker) (x : GAf D.host.E D.R.r)
    (_ : IsLiftAt (s k v) (j k v) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) x), LinearMap.ker (ρA x - LinearMap.id)

end GlobalTheory.TypeVec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.PermPrin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def permGL {n : ℕ} (σ : Equiv.Perm (Fin n)) : GL (Fin n) k :=
  ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm]⟩

theorem permGL_conj_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((permGL σ * g * (permGL σ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (g : Matrix (Fin n) (Fin n) k) (σ i) (σ j) := by
  have : ((permGL σ * g * (permGL σ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      σ.toPEquiv.toMatrix * (g : Matrix (Fin n) (Fin n) k) * σ.symm.toPEquiv.toMatrix := rfl
  rw [this, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

theorem constEquiv_piTensor_detRep {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) (L : ∀ _ : Fin n, GL (Fin 1) k)
    (t : ⨂[ℂ] _ : Fin n, ℂ) :
    PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ (piTensor (fun a => detRep (Fin 1) (χ a)) L t) =
      (∏ a, (χ a (GeneralLinearGroup.det (L a)) : ℂ)) * PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, piTensor_tprod, PiTensorProduct.constantBaseRingEquiv_tprod, detRep, ofChar_apply,
      detChar_apply, Finset.prod_mul_distrib, smul_eq_mul]
    ring
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), mul_add]

theorem isSubquotient_multiProd_prinSeries {n : ℕ} (e : (Σ _ : Fin n, Fin 1) ≃ Fin n)
    (χ : Fin n → kˣ →* ℂˣ) :
    IsSubquotient (multiProd e fun a => detRep (Fin 1) (χ a)) (prinSeries χ) := by
  let f : Fin n ≃ Fin n := (Equiv.sigmaUnique (Fin n) fun _ => Fin 1).symm.trans e
  let σ : Equiv.Perm (Fin n) := f.symm
  let P : GL (Fin n) k := permGL σ
  have hf : ∀ a (i : Fin 1), e ⟨a, i⟩ = f a := fun a i => by
    rw [Subsingleton.elim i 0]; rfl
  have hq : ∀ p : parab k (points (Fin n)), P * (p : GL (Fin n) k) * P⁻¹ ∈ parab k e := fun p => by
    refine mem_parab_iff.2 fun a b i j hab => ?_
    rw [hf, hf, permGL_conj_apply]
    simpa [σ] using mem_parab_iff.1 p.2 a b () () hab
  let κ := (PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ).toLinearEquiv
  let Ψ : IndSp e (piTensor fun a => detRep (Fin 1) (χ a)) →ₗ[ℂ]
      IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar χ)).comp (leviTorus k (Fin n)).symm.toMonoidHom) :=
    { toFun := fun F => ⟨⟨fun g => κ (F.1.1 (P * g)), fun p g => by
          let q : parab k e := ⟨P * p * P⁻¹, hq p⟩
          have e1 : P * ((p : GL (Fin n) k) * g) = (q : GL (Fin n) k) * (P * g) := by
            simp only [q, mul_assoc, inv_mul_cancel_left]
          have hdet : ∀ a, GeneralLinearGroup.det (leviProj k e q a) =
              GeneralLinearGroup.det (leviProj k (points (Fin n)) p a) := fun a => by
            ext
            simp only [GeneralLinearGroup.val_det_apply, det_unique]
            rw [leviProj_apply, leviProj_apply, hf]
            show ((P * p * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (f a) (f a) = _
            rw [permGL_conj_apply]
            simp [σ]
          have hd : deltaHalf k (fun _ : Fin n => Fin 1) (leviProj k e q) =
              deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) := by
            rw [deltaHalf_apply, deltaHalf_apply]
            refine Finset.prod_congr rfl fun a _ => ?_
            rw [hdet, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]
          beta_reduce
          rw [e1, parInd_law]
          generalize F.1.1 (P * g) = t
          show κ ((deltaHalf k (fun _ : Fin n => Fin 1) (leviProj k e q) : ℂ) •
              piTensor (fun a => detRep (Fin 1) (χ a)) (leviProj k e q) t) =
            (deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) : ℂ) •
              GlobalTheory.SmGL.ofChar (GlobalTheory.SmGL.torusChar χ) ((leviTorus k (Fin n)).symm (leviProj k (points (Fin n)) p)) (κ t)
          rw [map_smul, hd, GlobalTheory.SmGL.ofChar_apply, GlobalTheory.SmGL.torusChar_apply]
          congr 1
          refine (constEquiv_piTensor_detRep χ _ t).trans ?_
          rw [Units.coe_prod]
          congr 1
          exact Finset.prod_congr rfl fun a _ => by rw [hdet]; rfl⟩,
        MultiIrr.mem_smooth_of_eventually _ ((MultiIrr.eventually_of_smooth F).mono fun u hu x => by
          show κ (F.1.1 (P * (x * u))) = κ (F.1.1 (P * x))
          rw [← mul_assoc, hu])⟩
      map_add' := fun F G => Subtype.ext (Subtype.ext (funext fun x => map_add κ _ _))
      map_smul' := fun c F => Subtype.ext (Subtype.ext (funext fun x => map_smul κ _ _)) }
  refine .of_injective ⟨Ψ, fun g => LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    fun F F' h => ?_
  · show κ (F.1.1 (P * x * g)) = κ (F.1.1 (P * (x * g)))
    rw [mul_assoc]
  · refine Subtype.ext (Subtype.ext (funext fun x => κ.injective ?_))
    have h1 : κ (F.1.1 (P * (P⁻¹ * x))) = κ (F'.1.1 (P * (P⁻¹ * x))) :=
      congrFun (congrArg (fun φ => φ.1.1) h) (P⁻¹ * x)
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h1

end GlobalTheory.PermPrin

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.SuppIne

open GlobalTheory.LocGL GlobalTheory.SmGL

section Transport

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem continuous_glMap {n : Type} [Fintype n] [DecidableEq n] (j : k' →+* k) (hj : Continuous j) :
    Continuous (Matrix.GeneralLinearGroup.map (n := n) j) :=
  Units.continuous_iff.2 ⟨continuous_matrix fun a b => hj.comp (Units.continuous_val.matrix_elem a b),
    continuous_matrix fun a b => hj.comp (Units.continuous_coe_inv.matrix_elem a b)⟩

theorem glMap_surjective {n : Type} [Fintype n] [DecidableEq n] (i : k ≃+* k') :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom) := fun g =>
  ⟨Matrix.GeneralLinearGroup.map i.toRingHom g, Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] in
theorem isSubquotient_comp {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) (ψ : G' →* G) :
    IsSubquotient (σ.comp ψ) (ρ.comp ψ) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩, ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

def trGL (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL (k := k)) : IrrGL (k := k') :=
  IrrGL.of (x.rep.comp (Matrix.GeneralLinearGroup.map (n := Fin x.1) i.symm.toRingHom))
    (fun v => (x.2.rep.smooth v).preimage (continuous_glMap _ hi'))
    (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp x.2.rep.irr _ (glMap_surjective i))

theorem hasSupport_comp (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL (k := k))}
    (h : HasSupport π s) :
    HasSupport (π.comp (Matrix.GeneralLinearGroup.map (n := Fin N) i.symm.toRingHom)) (s.map (trGL i hi')) := by
  obtain ⟨c, x, rfl, hir, hc, e, hsub⟩ := h
  have H : IsCuspSupport (π.comp (Matrix.GeneralLinearGroup.map (n := Fin N) i.symm.toRingHom)) (fun a => (x a).1)
      (fun a => (x a).rep.comp (Matrix.GeneralLinearGroup.map (n := Fin (x a).1) i.symm.toRingHom)) := by
    refine ⟨GlobalTheory.CuspRep.ParLaws.isIrreducible_comp hir _ (glMap_surjective i), fun a =>
      ⟨(hc a).1, GlobalTheory.CuspRep.ParLaws.isIrreducible_comp (hc a).2.1 _ (glMap_surjective i),
        GlobalTheory.T.isSupercuspidal_comp_generalLinearGroupMapOfFieldEquiv i hi' _ (hc a).2.2⟩, e, ?_⟩
    obtain ⟨φ⟩ := GlobalTheory.T.parabolicInduction_comp_generalLinearGroupMapOfFieldEquiv i hi hi' (GlobalTheory.T.normalizedAbsValueLocalFieldUnit_map_homeomorph i hi hi') e (fun a => (x a).rep)
    exact (isSubquotient_comp hsub _).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have := hasSupport_of_isCuspSupport H
  rw [Multiset.map_map]
  exact this

end Transport

end GlobalTheory.SuppIne

namespace GlobalTheory.SuppIne

open GlobalTheory.LocGL GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem continuous_symm {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) : Continuous (I.i k v).symm := by
  letI := (I.i k v).toRingHom.toAlgebra
  have : ContinuousSMul ℚ_[D.host.g k] ((D.naut.plGw k v).adicCompletion D.host.E) :=
    continuousSMul_of_algebraMap _ _ (I.cont k v)
  let el : ℚ_[D.host.g k] ≃ₗ[ℚ_[D.host.g k]] (D.naut.plGw k v).adicCompletion D.host.E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (I.i k v).bijective
  refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => (I.i k v).injective ?_
  exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans ((I.i k v).apply_symm_apply y).symm

def tr {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (ρ : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (hs : GlobalTheory.PRep.IsSmooth ρ.ρ) (hi : ρ.ρ.IsIrreducible) : IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) :=
  ⟨ρ, ρ.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom),
    fun x => (hs x).preimage (continuous_glMap _ (continuous_symm I k v)),
    GlobalTheory.CuspRep.ParLaws.isIrreducible_comp hi _ (glMap_surjective _)⟩

theorem iso_pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (ρ : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (hs : GlobalTheory.PRep.IsSmooth ρ.ρ) (hi : ρ.ρ.IsIrreducible) : Nonempty (ρ ≅ pull I k v (tr I k v ρ hs hi)) := by
  have hg : ∀ g : GL (Fin n) ℚ_[D.host.g k], Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun a b => (I.i k v).symm_apply_apply _)
  refine ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ ρ) fun g => LinearMap.ext fun x => ?_)⟩
  change ρ.ρ g x = ρ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g)) x
  rw [hg]

end GlobalTheory.SuppIne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitaryFinitePointsToGLFiniteAdelesIsUnitary
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.UnitaryBC.ClassTransport
open scoped TensorProduct

namespace GlobalTheory.FormDict.Model

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "F₀" => maximalRealSubfield L

def kappa : AL L ≃+* FiniteAdeleRing (𝓞 L) L :=
  (Algebra.TensorProduct.comm F₀ L (FiniteAdeleRing (𝓞 F₀) F₀)).toRingEquiv.trans (GlobalTheory.LFun.finAdEquiv F₀ L)

theorem kappa_tmul (x : L) (a : FiniteAdeleRing (𝓞 F₀) F₀) :
    kappa L (x ⊗ₜ a) = GlobalTheory.AdeleBaseChange.adMap F₀ L a * algebraMap L _ x :=
  GlobalTheory.LFun.toFinAd_tmul a x

theorem kappa_conj (y : AL L) :
    kappa L (conjAL L y) = conjFin (IsCMField.complexConj L).toRingEquiv (kappa L y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x a =>
    have hAd : conjFin (IsCMField.complexConj L).toRingEquiv
        (GlobalTheory.AdeleBaseChange.adMap F₀ L a) = GlobalTheory.AdeleBaseChange.adMap F₀ L a := by
      have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField L
      refine congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := F₀)).equalizer
        ((continuous_conjFin _).comp (continuous_adMap F₀ L)) (continuous_adMap F₀ L)
        (funext fun k => ?_)) a
      simp only [Function.comp_apply]
      rw [GlobalTheory.AdeleBaseChange.adMap_algebraMap, conjFin_algebraMap]
      congr 1
      exact IsCMField.complexConj_apply_eq_self L k
    change kappa L ((IsCMField.complexConj L x) ⊗ₜ a) = _
    rw [kappa_tmul, kappa_tmul, map_mul, hAd, conjFin_algebraMap]
    rfl
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), hy, hz, map_add (f := _)]

def psi0 : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L) :=
  (Matrix.GeneralLinearGroup.map (kappa L).toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype

theorem map_conjT (M : Matrix (Fin n) (Fin n) (AL L)) :
    (conjT (conjAL L) M).map (kappa L).toRingHom =
      Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv) (M.map (kappa L).toRingHom) :=
  Matrix.ext fun _ _ => kappa_conj L _

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (x : GAf L n) :
    Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv) (psi0 L n x).val * (psi0 L n x).val = 1 := by
  have hx : x.1.val * conjT (conjAL L) x.1.val = 1 := x.2
  rw [mul_eq_one_comm] at hx
  change Formalism.UG.cT _ (x.1.val.map (kappa L).toRingHom) * x.1.val.map (kappa L).toRingHom = 1
  rw [← map_conjT, ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero _) (map_one _)]

def j0 : GAf L n →* UA L n :=
  ((finGL L n).comp (psi0 L n)).codRestrict (UA L n) fun x => finGL_mem_UA _ (unitaryFinitePointsToGLFiniteAdeles_isUnitary L n x)

def finIso : FinIso L n where
  κ := kappa L
  left x := by rw [kappa_tmul, map_one, one_mul]
  right w v h := by
    have h' : w.under (𝓞 F₀) = v := HeightOneSpectrum.ext h
    subst h'
    refine ⟨GlobalTheory.LFun.complMap (rfl : w.under (𝓞 F₀) = _), GlobalTheory.LFun.InertChart.continuous_complMap _, fun a => ?_⟩
    rw [kappa_tmul, map_one, mul_one]
    rfl
  j := j0 L n
  fin x := MonoidHom.mem_ker.2 (pInf_finGL (psi0 L n x))
  loc x w s t := by
    have h : Matrix.GeneralLinearGroup.map (pFin L) (j0 L n x).1 = psi0 L n x := pFin_finGL _
    have h2 := congrArg (fun g : GL (Fin n) (Af L) => pLoc L w (g.val s t)) h
    exact h2
  onto g hgf := by
    have hg := g.2
    change Formalism.UG.cT (conjAd L) g.1.val * 1 * g.1.val = 1 at hg
    rw [Matrix.mul_one] at hg
    have hf : Formalism.UG.cT (conjFin (IsCMField.complexConj L).toRingEquiv)
        (Matrix.GeneralLinearGroup.map (pFin L) g.1).val * (Matrix.GeneralLinearGroup.map (pFin L) g.1).val = 1 := by
      have h := congrArg (fun M => M.map (pFin L)) hg
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
      exact h
    let u := Matrix.GeneralLinearGroup.map (kappa L).symm.toRingHom (Matrix.GeneralLinearGroup.map (pFin L) g.1)
    have hU : u.val.map (kappa L).toRingHom = (Matrix.GeneralLinearGroup.map (pFin L) g.1).val :=
      Matrix.ext fun i j => (kappa L).apply_symm_apply _
    have hmem : u ∈ ReciprocityTheory.Aut.GA L n := by
      change u.val * conjT (conjAL L) u.val = 1
      rw [mul_eq_one_comm]
      refine Matrix.map_injective (kappa L).injective ?_
      change Matrix.map _ (kappa L).toRingHom = Matrix.map 1 (kappa L).toRingHom
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), map_conjT, hU]
      exact hf
    refine ⟨⟨u, hmem⟩, Subtype.ext (ga_ext ?_ ?_)⟩
    · exact (pInf_finGL _).trans (MonoidHom.mem_ker.1 hgf).symm
    · exact (pFin_finGL _).trans (Units.ext hU)

variable {L n}

theorem kappa_eq (F G : FinIso L n) : F.κ = G.κ := by
  refine RingEquiv.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]
  | tmul x a =>
    have e : x ⊗ₜ[F₀] a = (x ⊗ₜ[F₀] (1 : AFplus L)) * ((1 : L) ⊗ₜ[F₀] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, F.left, G.left]
    congr 1
    refine FiniteAdeleRing.ext _ fun w => ?_
    obtain ⟨i, hi, h1⟩ := F.right w (w.under (𝓞 F₀)) rfl
    obtain ⟨i', hi', h2⟩ := G.right w (w.under (𝓞 F₀)) rfl
    have key : ∀ k : F₀, (1 : L) ⊗ₜ[F₀] (algebraMap F₀ (AFplus L) k) = (k : L) ⊗ₜ[F₀] (1 : AFplus L) := fun k => by
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      rfl
    have : (i : _ → _) = i' := (HeightOneSpectrum.denseRange_algebraMap F₀ (w.under (𝓞 F₀))).equalizer hi hi'
      (funext fun k => by
        have a1 := h1 (algebraMap F₀ _ k)
        have a2 := h2 (algebraMap F₀ _ k)
        rw [key, F.left] at a1
        rw [key, G.left] at a2
        exact a1.symm.trans a2)
    change F.κ (1 ⊗ₜ a) w = G.κ (1 ⊗ₜ a) w
    rw [h1, h2, this]


end GlobalTheory.FormDict.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.UnramDict

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

theorem kappa_tmul (F : FinIso L n) (x : L) (a : AFplus L) :
    F.κ.toRingHom (x ⊗ₜ[L⁺] a) = algebraMap L _ x * GlobalTheory.AdeleBaseChange.adMap L⁺ L a := by
  rw [Model.kappa_eq F (Model.finIso L n)]
  exact (Model.kappa_tmul L x a).trans (mul_comm _ _)

theorem mem_ALint (F : FinIso L n) (z : AL L) (hz : ∀ u, F.κ z u ∈ u.adicCompletionIntegers L) : z ∈ ALint L := by
  have h := GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := F.κ.toRingHom) (kappa_tmul F) (y := z) hz
  refine (Subring.closure_le.2 ?_ : _ ≤ ALint L) h
  rintro x (⟨⟨e, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
  · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  · exact Subring.subset_closure (Or.inr ⟨y, hy, rfl⟩)

theorem compAt_eq_zero (F : FinIso L n) (v : HeightOneSpectrum (𝓞 L⁺)) (z : AL L)
    (hz : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 L⁺) = v → F.κ z u = 0) : compAt L v z = 0 :=
  (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) (kappa_tmul F) v z).2 hz


omit [IsCMField L] in
theorem entry_mem {w : HeightOneSpectrum (𝓞 L)} {g : GL (Fin n) (w.adicCompletion L)} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n))
    (i j : Fin n) : g.val i j ∈ w.adicCompletionIntegers L := by
  obtain ⟨Q, rfl⟩ := hg
  exact (Q.val i j).2

theorem cLoc_entry_mem {w : HeightOneSpectrum (𝓞 L)} {x : UA L n} (hx : x ∈ locU n w) (hK : cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n))
    (u : HeightOneSpectrum (𝓞 L)) (i j : Fin n) : (cLoc u x).val i j ∈ u.adicCompletionIntegers L := by
  by_cases hu : u.under (𝓞 L⁺) = w.under (𝓞 L⁺)
  · rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w u).1 hu with rfl | h
    · exact entry_mem hK i j
    · obtain rfl : u = conjSrc (GlobalTheory.SplitPts.conjE L) w := by
        rw [eq_conjSrc h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm]
      have h1 := Units.inv_eq_of_mul_eq_one_left (GlobalTheory.SplitPts.comp_eq x w)
      have h2 := entry_mem (inv_mem hK) j i
      rw [h1] at h2
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h2 ⊢
      rw [← (conjLoc_spec (GlobalTheory.SplitPts.conjE L) w).2.2]
      exact h2
  · have h := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)
    rw [h, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem trivOutside (F : FinIso L n) {w : HeightOneSpectrum (𝓞 L)} {y : GAf L n} (hy : F.j y ∈ locU n w) :
    TrivOutside {w.under (𝓞 L⁺)} y := by
  intro v hv
  refine Matrix.ext fun i j => ?_
  have h0 := compAt_eq_zero F v (y.1.val i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) fun u hu => by
    have h := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hy).2 u)
      (fun e => hv (hu.symm.trans e)))
    have h1 := F.loc y u i j
    rw [h] at h1
    rw [map_sub]
    change F.κ _ u - F.κ _ u = 0
    rw [← h1]
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
    rfl
  rw [map_sub, sub_eq_zero] at h0
  rw [Matrix.map_apply, h0]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem isUnramU_of_sphAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → IsUnramU U w := by
  intro L _ _ _ n F π U hD v w hw hs
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  obtain ⟨f, hfS, hf0, hfix⟩ := hs
  obtain ⟨g0, hg0⟩ : ∃ g0, f g0 ≠ 0 := Function.ne_iff.1 hf0
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual ℂ π.W, lam (f g0) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hg0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hc)
  have hmem : (fun x => lam (f x)) ∈ U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [hD.2]
    exact Submodule.subset_span ⟨f, hfS, lam, rfl⟩
  obtain ⟨φ, hφU, hφ⟩ := hmem
  have hφ' : ∀ g, φ (F.j g) = lam (f g) := fun g => congrFun hφ g
  refine ⟨φ, hφU, fun h => hlam ?_, fun x hx hK => ?_⟩
  · rw [← hφ', h]; rfl
  obtain ⟨y, rfl⟩ := F.onto x (Subgroup.mem_inf.1 hx).1
  have hyU : y ∈ Umax L n := fun i j => mem_ALint F _ fun u => by
    rw [← F.loc]
    exact cLoc_entry_mem hx hK u i j
  have hy := hfix y hyU (trivOutside F hx)
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hD.1.aut _ (U.sub_mem (hD.1.stable _ _ hφU) hφU)) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  change φ (F.j g * F.j y) - φ (F.j g) = 0
  rw [← map_mul, hφ', hφ', sub_eq_zero]
  exact congrArg lam (congrFun hy g)

end GlobalTheory.UnramDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionaryStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramified_of_sphericalVector_dictionary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → IsUnramU U w := by
  first | exact @GlobalTheory.UnramDict.isUnramU_of_sphAt | exact GlobalTheory.UnramDict.isUnramU_of_sphAt | (intros; apply GlobalTheory.UnramDict.isUnramU_of_sphAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenConductor
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.ExtTheta

variable {D : D7}

theorem isoTyp_congr {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) {S S' : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (h : NG.IsoRep S S') : NG.isoTyp ρ S = NG.isoTyp ρ S' := by
  unfold NG.isoTyp
  congr 1
  ext T
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h.symm hS).trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩⟩

variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}



end GlobalTheory.ExtTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.CoefDuty.ExtRing

theorem qCast_trans {a p q : ℕ} [Fact a.Prime] [Fact p.Prime] [Fact q.Prime] (ι : Qbar a ≃+* ℂ) (h₀ : a = p)
    (h₁ : a = q) (hl : p = q) : qCast h₁ ι = qCast hl (qCast h₀ ι) := by
  subst h₀; subst hl; rfl

theorem exists_gens {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ s : Finset (Qbar l), ∀ x, ι x ∈ Submodule.span ℚ_[l] (s : Set (Qbar l)) := by
  classical
  obtain ⟨K, hK, hfd, -⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι hι
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℚ_[l] K).FG)
  refine ⟨t.image Subtype.val, fun x => ?_⟩
  have hx : (⟨ι x, (hK _).2 ⟨x, rfl⟩⟩ : K) ∈ Submodule.span ℚ_[l] (t : Set K) := ht ▸ Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := K.val.toLinearMap) hx
  rw [← Submodule.span_image] at this
  rw [Finset.coe_image]
  exact this

theorem exists_ringHom {l₀ l₁ : ℕ} [Fact l₀.Prime] [Fact l₁.Prime] (hl : l₀ = l₁)
    {O₀ : Type} [cr₀ : CommRing O₀] [dm₀ : IsDomain O₀] [dv₀ : IsDiscreteValuationRing O₀] [al₀ : Algebra ℤ_[l₀] O₀]
    [fi₀ : Module.Finite ℤ_[l₀] O₀]
    {O₁ : Type} [cr₁ : CommRing O₁] [dm₁ : IsDomain O₁] [dv₁ : IsDiscreteValuationRing O₁] [al₁ : Algebra ℤ_[l₁] O₁]
    [fi₁ : Module.Finite ℤ_[l₁] O₁]
    (ι₀ : FractionRing O₀ →+* Qbar l₀)
    (hι₀ : ∀ z : ℤ_[l₀], ι₀ (algebraMap O₀ (FractionRing O₀) (algebraMap ℤ_[l₀] O₀ z)) =
      algebraMap ℚ_[l₀] (Qbar l₀) (z : ℚ_[l₀]))
    (ι₁ : FractionRing O₁ →+* Qbar l₁)
    (hι₁ : ∀ z : ℤ_[l₁], ι₁ (algebraMap O₁ (FractionRing O₁) (algebraMap ℤ_[l₁] O₁ z)) =
      algebraMap ℚ_[l₁] (Qbar l₁) (z : ℚ_[l₁]))
    (c₀ : Qbar l₀ ≃+* ℂ) (c₁ : Qbar l₁ ≃+* ℂ) (hc : c₁ = qCast hl c₀) (s : Set (Qbar l₀))
    (hs : ∀ x, ι₀ x ∈ Submodule.span ℚ_[l₀] s) (hs₁ : ∀ y ∈ s, ∃ x, c₁ (ι₁ x) = c₀ y) :
    ∃ φ : O₀ →+* O₁, (∀ z, c₁ (ι₁ (algebraMap O₁ _ (φ z))) = c₀ (ι₀ (algebraMap O₀ _ z))) ∧
      ∀ (z : ℤ_[l₀]) (z' : ℤ_[l₁]), HEq z z' → φ (algebraMap ℤ_[l₀] O₀ z) = algebraMap ℤ_[l₁] O₁ z' := by
  subst hl
  have hc' : ∀ x, c₁ x = c₀ x := fun x => by rw [hc]; rfl
  simp only [hc'] at hs₁ ⊢
  obtain ⟨K₀, hK₀, -, hn₀⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₀ hι₀
  obtain ⟨K₁, hK₁, -, hn₁⟩ := GlobalTheory.Proof.CoefField.exists_coefField ι₁ hι₁
  have hsK : s ⊆ (K₁ : Set (Qbar l₀)) := by
    intro y hy
    obtain ⟨x, hx⟩ := hs₁ y hy
    exact (hK₁ y).2 ⟨x, c₀.injective hx⟩
  have hspan : Submodule.span ℚ_[l₀] s ≤ K₁.toSubalgebra.toSubmodule := Submodule.span_le.2 hsK
  let f₀ : O₀ →+* Qbar l₀ := ι₀.comp (algebraMap O₀ (FractionRing O₀))
  let f₁ : O₁ →+* Qbar l₀ := ι₁.comp (algebraMap O₁ (FractionRing O₁))
  have hf₁ : Function.Injective f₁ := ι₁.injective.comp (IsFractionRing.injective O₁ (FractionRing O₁))
  have hrange : ∀ z, f₀ z ∈ f₁.range := by
    intro z
    have h1 : f₀ z ∈ K₁ := hspan (hs _)
    obtain ⟨y, hy⟩ := (hK₁ _).1 h1
    have hle : ‖ι₀ (algebraMap O₀ (FractionRing O₀) z)‖ ≤ 1 := (hn₀ _).2 ⟨z, rfl⟩
    have hy1 : ‖ι₁ y‖ ≤ 1 := by rw [hy]; exact hle
    obtain ⟨u, rfl⟩ := (hn₁ y).1 hy1
    exact ⟨u, hy⟩
  let e₁ : O₁ ≃+* f₁.range := RingEquiv.ofBijective f₁.rangeRestrict
    ⟨fun a b h => hf₁ (congrArg Subtype.val h), f₁.rangeRestrict_surjective⟩
  let φ : O₀ →+* O₁ := e₁.symm.toRingHom.comp (f₀.codRestrict f₁.range hrange)
  have hφ : ∀ z, f₁ (φ z) = f₀ z := by
    intro z
    have : e₁ (φ z) = f₀.codRestrict f₁.range hrange z := e₁.apply_symm_apply _
    exact congrArg Subtype.val this
  refine ⟨φ, fun z => congrArg c₀ (hφ z), fun z z' hzz => ?_⟩
  cases eq_of_heq hzz
  apply hf₁
  rw [hφ]
  change ι₀ _ = ι₁ _
  rw [hι₀, hι₁]

end GlobalTheory.CoefDuty.ExtRing

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasThetaAtOfThetaMod
noncomputable section

namespace GlobalTheory.RefPair

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT NumberField
  IsDedekindDomain GlobalTheory.NPin GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def HasThetaAt (D : D7) {μt : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μt j) {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (X : RowMod D rep j) (μ η : HChar D.host.E) : Prop :=
  ∃ (Ω : Type) (_ : AddCommGroup Ω) (_ : Module ℂ Ω) (ω : GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ Ω)
    (Λ : Ω →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ) →ₗ[ℂ] ↥X.C →ₗ⋆[ℂ] ℂ) (φ₀ : Ω),
    (∀ h g φ (F F' : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)) (y y' : ↥X.C),
      (F' : GAf D.host.E D.R.nV → Mr.wt.W) = NG.rt D.host.E D.R.nV h F → (y' : X.A) = X.ρ g y →
      Λ (ω (h, g) φ) F' y' = Λ φ F y) ∧
    (∀ x y (F : ↥(NG.AFall D.host.E D.R.nV Mr.wt.ρ)), (F : GAf D.host.E D.R.nV → Mr.wt.W) = Mr.real x →
      inner ℂ y (D.what₂.thetaP μt j x) = Λ φ₀ F ⟨X.φ y, X.φ_mem y⟩) ∧
    ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw →
      φ₀ ∈ ⨆ (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Ω)
        (_ : IsLinAt ω s μw ηw ι), LinearMap.range ι

end GlobalTheory.RefPair

end
end
