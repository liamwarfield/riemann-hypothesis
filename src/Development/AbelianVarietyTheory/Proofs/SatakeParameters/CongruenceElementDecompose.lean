module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct

namespace GlobalTheory.IdemSplit

variable {R : Type*} [CommRing R] {n : ℕ}

def fold (e : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := e • M + (1 - e) • 1

theorem fold_mul_fold {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold e X * fold (1 - e) Y = e • X + (1 - e) • Y := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, h0, sub_zero]
  simp only [fold, sub_sub_cancel, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, h0, h0',
    he, h1, zero_smul, zero_add, add_zero]
  exact add_comm _ _

theorem fold_mul_fold' {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold (1 - e) Y * fold e X = e • X + (1 - e) • Y := by
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h := fold_mul_fold he' Y X
  rw [sub_sub_cancel] at h
  rw [h, add_comm]

theorem fold_mul {e : R} (he : e * e = e) (X Y : Matrix (Fin n) (Fin n) R) :
    fold e X * fold e Y = fold e (X * Y) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, h0, sub_zero]
  simp only [fold, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, h0, h0',
    he, h1, zero_smul, zero_add, add_zero]

theorem fold_one (e : R) : fold e (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [fold, ← add_smul, add_sub_cancel, one_smul]

theorem conjT_fold (σ : R →+* R) {e : R} (hσ : σ e = e) (M : Matrix (Fin n) (Fin n) R) :
    conjT σ (fold e M) = fold e (conjT σ M) := by
  ext i j
  simp only [conjT, fold, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

def unitsFold {e : R} (he : e * e = e) (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨fold e g, fold e (g⁻¹ : GL (Fin n) R), by rw [fold_mul he, Units.mul_inv, fold_one],
    by rw [fold_mul he, Units.inv_mul, fold_one]⟩

theorem unitsFold_mem_UGroup (σ : R →+* R) (hσ2 : ∀ x, σ (σ x) = x) {e : R} (he : e * e = e)
    (hσ : σ e = e) (g : GL (Fin n) R) (hg : g ∈ UGroup n σ hσ2) :
    unitsFold he g ∈ UGroup n σ hσ2 := by
  have hg' : (g : Matrix (Fin n) (Fin n) R) * conjT σ g = 1 := hg
  show fold e (g : Matrix (Fin n) (Fin n) R) * conjT σ (fold e (g : Matrix (Fin n) (Fin n) R)) = 1
  rw [conjT_fold σ hσ, fold_mul he, hg', fold_one]

theorem fold_apply (e : R) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    fold e M i j = e * M i j + (1 - e) * (1 : Matrix (Fin n) (Fin n) R) i j := by
  simp [fold]

end GlobalTheory.IdemSplit

namespace GlobalTheory.CongSplit

open GlobalTheory.IdemSplit GlobalTheory.InertUmax

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L :=
  (1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1

theorem compAt_idemAt_self (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    compAt L v (idemAt L v) = 1 := by
  rw [idemAt, compAt_tmul, sgl_same]; rfl

theorem compAt_idemAt_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hw : w ≠ v) :
    compAt L w (idemAt L v) = 0 := by
  rw [idemAt, compAt_tmul, sgl_ne L v 1 hw, tmul_zero]

theorem idemAt_mul_self (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    idemAt L v * idemAt L v = idemAt L v := by
  apply sub_eq_zero.1
  apply eq_zero_of_compAt
  intro w
  rw [map_sub, map_mul]
  rcases eq_or_ne w v with rfl | hw
  · rw [compAt_idemAt_self, mul_one, sub_self]
  · rw [compAt_idemAt_ne L v hw, mul_zero, sub_self]

theorem idemAt_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idemAt L v ∈ ALint L :=
  one_tmul_sgl_mem L v 1 (one_mem _)

theorem conjAL_idemAt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    conjAL L (idemAt L v) = idemAt L v := by
  simp [conjAL, idemAt, Algebra.TensorProduct.map_tmul]

theorem one_apply_mem {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem compAt_one_apply {n : ℕ} (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (i j : Fin n) :
    compAt L w ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
  simp only [Matrix.one_apply]
  split_ifs <;> simp


variable {L} in
def gaFold {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (g : GAf L n) : GAf L n :=
  ⟨unitsFold hf g.1, unitsFold_mem_UGroup (conjAL L) (conjAL_conjAL L) hf hσ g.1 g.2⟩

theorem gaFold_val {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (g : GAf L n) :
    ((gaFold hf hσ g).1 : Matrix (Fin n) (Fin n) (AL L)) = fold f (g.1 : Matrix (Fin n) (Fin n) (AL L)) :=
  rfl

theorem gaFold_mem_Umax {n : ℕ} {f : AL L} (hf : f * f = f) (hσ : conjAL L f = f) (hfi : f ∈ ALint L)
    (g : GAf L n) (hg : g ∈ Umax L n) : gaFold hf hσ g ∈ Umax L n := by
  intro i j
  rw [gaFold_val, fold_apply]
  exact Subring.add_mem _ (Subring.mul_mem _ hfi (hg i j))
    (Subring.mul_mem _ (Subring.sub_mem _ (one_mem _) hfi) (one_apply_mem L i j))

theorem decomp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) (c : GAf L n), NG.Cong L n N c → ∃ a b : GAf L n, c = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
  intro L _ _ _ n v N c hc
  set e := idemAt L v with he_def
  have he : e * e = e := idemAt_mul_self L v
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hσ : conjAL L e = e := conjAL_idemAt L v
  have hσ' : conjAL L (1 - e) = 1 - e := by rw [map_sub, map_one, hσ]
  have hei : e ∈ ALint L := idemAt_mem L v
  have hei' : 1 - e ∈ ALint L := Subring.sub_mem _ (one_mem _) hei
  refine ⟨gaFold he hσ c, gaFold he' hσ' c, ?_, gaFold_mem_Umax L he hσ hei c hc.1, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show (c.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e _ * fold (1 - e) _
    rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]
  · intro w hw
    have hw' : w ≠ v := by simpa using hw
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
      compAt_idemAt_ne L v hw', compAt_one_apply]
    simp
  · refine ⟨gaFold_mem_Umax L he' hσ' hei' c hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨(1 - e) * y, Subring.mul_mem _ hei' hy, ?_⟩
    rw [gaFold_val, fold_apply, sub_sub_cancel]
    linear_combination (1 - e) * hEq
  · intro x hx
    have hxf : (x.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e (x.1 : Matrix (Fin n) (Fin n) (AL L)) := by
      ext i j
      apply sub_eq_zero.1
      rw [fold_apply]
      apply eq_zero_of_compAt
      intro w
      rcases eq_or_ne w v with rfl | hw
      · rw [map_sub, map_add (f := _), map_mul, map_mul, map_sub, map_one, compAt_idemAt_self]
        ring
      · have h := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h
        rw [map_sub, map_add (f := _), map_mul, map_mul, map_sub, map_one, compAt_idemAt_ne L v hw,
          compAt_one_apply, h]
        ring
    apply Subtype.ext; apply Units.ext
    show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * fold (1 - e) _ = fold (1 - e) _ * (x.1 : Matrix (Fin n) (Fin n) (AL L))
    rw [hxf, fold_mul_fold he, fold_mul_fold' he]

end GlobalTheory.CongSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecomposeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_element_decompose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) (c : GAf L n), NG.Cong L n N c → ∃ a b : GAf L n, c = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
  first | exact @GlobalTheory.CongSplit.decomp | exact GlobalTheory.CongSplit.decomp | (intros; apply GlobalTheory.CongSplit.decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterCoefficientFieldEnlarge
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterCoefficientFieldEnlarge
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Pst.EnlargeParam

open GlobalTheory.Pst.EnlargeCoeff Module

section General

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {L₁ L₂ : FinExt l}
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module ↥L₁.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥L₁.1 V₁]
  [AddCommGroup V₂] [Module ↥L₂.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥L₂.1 V₂]
  {ρ₁ : Representation ↥L₁.1 ↥(GK Bw.Kw) V₁} {ρ₂ : Representation ↥L₂.1 ↥(GK Bw.Kw) V₂}
  [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₁)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂)]

theorem wdRep_iso (s : ↥L₁.1 →+* ↥L₂.1) (hs : ∀ a, (s a : Om l) = (a : Om l))
    {f : V₁ →ₗ[ℚ_[l]] V₂} (hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v)) (hfs : ∀ (a : ↥L₁.1) v, f (a • v) = s a • f v)
    {n : ℕ} (b : Fin n → ↥L₂.1) (π : Fin n → V₂ →ₗ[ℚ_[l]] V₁) (hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v))
    (hsum : ∀ v, ∑ j, b j • f (π j v) = v)
    (hdim : finrank ℂ (WDSpace P ι ρ₁) = finrank ℂ (WDSpace P ι ρ₂)) :
    (wdRep P ι Bw h hj ρ₁).Iso (wdRep P ι Bw h hj ρ₂) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have hT : ∀ (a : ↥L₁.1) (x : ↥(Dpst P ρ₁)), dQ P hf (a • x) = s a • dQ P hf x := fun a x =>
    Subtype.ext (tensQ_smul P s hfs a x.1)
  letI := algC ι L₁
  letI := algC ι L₂
  let Φ := chg (mulD P ρ₁) (mulD P ρ₂) ℂ (urC ι) s (fun a => congrArg ι (hs a)) (dQ P hf) hT (dQ_mulD P hf)
  have hΦρ : ∀ σ y, Φ (wdRho P ι Bw h hj ρ₁ σ y) = wdRho P ι Bw h hj ρ₂ σ (Φ y) := fun σ y =>
    chg_letterMap _ _ _ _ _ _ _ _ _ _ (weilD_mulD Bw h P ρ₁ hj σ) _ (weilD_mulD Bw h P ρ₂ hj σ)
      (dQ_weilD P Bw h hf σ) y
  have hΦN : ∀ y, Φ (wdN P ι ρ₁ y) = wdN P ι ρ₂ (Φ y) := fun y =>
    chg_letterMap _ _ _ _ _ _ _ _ _ _ (monD_mulD P ρ₁) _ (monD_mulD P ρ₂)
      (fun x => Subtype.ext (tensQ_onB P f _ x.1)) y
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ₂, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ j, b j • dQ P hf (dQ P (hπ j) x) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, coe_dQ]
      exact (sum_tensQ P b π hsum x.1).symm
    have hms := map_sum (AddMonoidHom.mk' (wdMk P ι ρ₂) (wdMk_add P ι ρ₂))
      (fun j => b j • dQ P hf (dQ P (hπ j) x)) Finset.univ
    simp only [AddMonoidHom.mk'_apply] at hms
    rw [hx, hms]
    refine Submodule.sum_mem _ fun j _ => ?_
    change wdMk P ι ρ₂ ((Dpst P ρ₂).module.toSMul.smul (b j) (dQ P hf (dQ P (hπ j) x))) ∈ Φ.range
    rw [wdMk_smul]
    exact Submodule.smul_mem _ _ ⟨wdMk P ι ρ₁ (dQ P (hπ j) x), chg_mk _ _ _ _ _ _ _ _ _ _⟩
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact IsFrobSS.iso (GlobalTheory.TwistParamAbove.isFrobSS_wdRep P ι Bw h hj ρ₁)
    (GlobalTheory.TwistParamAbove.isFrobSS_wdRep P ι Bw h hj ρ₂) (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩) hΦρ hΦN

end General

theorem wdPst_enlarge {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l}
    (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1) :
    IsPst P (Bw.repE L₁ r₁) →
    wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) =
      wdPst P ι Bw h hj (Bw.repE L₁ r₁) := by
  intro hV₁
  have hV₂ := GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hV₁
  haveI := hV₁.finite
  haveI := hV₂.finite
  obtain ⟨n, b, π, hπ, hsum⟩ := exists_decomp hL (m := m)
  have hf : ∀ g v, incV hL m (Bw.repE L₁ r₁ g v) =
      Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g (incV hL m v) :=
    fun g v => incV_mulVec hL _ v
  have hπ' : ∀ (j : Fin n) (g : ↥(GK Bw.Kw)) (v : Fin m → ↥L₂.1),
      π j (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g v) = Bw.repE L₁ r₁ g (π j v) :=
    fun j g v => hπ j (r₁ (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L₁.1) v
  have hdim : finrank ℂ (WDSpace P ι (Bw.repE L₁ r₁)) =
      finrank ℂ (WDSpace P ι (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) :=
    (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₁ _ _ hV₁).trans ((Module.finrank_fin_fun _).trans
      ((Module.finrank_fin_fun _).symm.trans (GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw L₂ _ _ hV₂).symm))
  rw [wdPst_of_isPst ι Bw h hj hV₂, wdPst_of_isPst ι Bw h hj hV₁]
  exact (WD.sound (wdRep_iso P ι Bw h hj (IntermediateField.inclusion hL).toRingHom (fun _ => rfl) hf
    (incV_smul hL) b π hπ' hsum hdim)).symm

end GlobalTheory.Pst.EnlargeParam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterCoefficientFieldEnlargeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potSemistableParameter_coefficientField_enlarge : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) = wdPst P ι Bw h hj (Bw.repE L₁ r₁) := by
  first | exact @GlobalTheory.Pst.EnlargeParam.wdPst_enlarge | exact GlobalTheory.Pst.EnlargeParam.wdPst_enlarge | (intros; apply GlobalTheory.Pst.EnlargeParam.wdPst_enlarge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRamifiedOfRamifiedLocalComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRamifiedOfRamifiedLocalComponent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.VTypeTame.ramified_of_isComp : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (ξ : (w.adicCompletion E)ˣ →* ℂˣ), IsComp χ w ξ → ¬ GlobalTheory.SplitWeil.IsUnram ξ → ¬ χ.UnrAt w := by
  intro E _ _ χ w ξ hξ hn hu
  have hc : IsComp χ w (χ.loc w) := ⟨GlobalTheory.HeckeComp.smooth_loc χ w, fun _ => rfl⟩
  have he : ξ = χ.loc w := GlobalTheory.HeckeComp.eq_of_isComp hc hξ
  apply hn
  intro x hx
  rw [he]
  apply hu x
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  show Valued.v (x : w.adicCompletion E) = 1
  exact h1.eq_one_iff_eq_one.1 hx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRamifiedOfRamifiedLocalComponentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_ramified_of_ramified_localComponent : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (ξ : (w.adicCompletion E)ˣ →* ℂˣ), IsComp χ w ξ → ¬ GlobalTheory.SplitWeil.IsUnram ξ → ¬ χ.UnrAt w := by
  first | exact @GlobalTheory.VTypeTame.ramified_of_isComp | exact GlobalTheory.VTypeTame.ramified_of_isComp | (intros; apply GlobalTheory.VTypeTame.ramified_of_isComp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfUpperParahoricEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfUpperParahoricEigen
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SameParahoric

open Filter Topology

theorem denseRange_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    DenseRange (s.i : L → s.v.adicCompletion (maximalRealSubfield L)) := by
  refine (s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩

theorem eq_comp {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hci : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (N : ℕ)
    (hN : ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1)
    (hglob : ∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) =
      μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))
    (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ) :
    ξ d = μ (Units.map c.toRingHom.toMonoidHom d) := by
  obtain ⟨z, hz⟩ := s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))
  have hξo : GlobalTheory.SmGL.IsSmoothChar ξ := by
    have hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ |
        Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z} := by
      have h1 := (Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage
        (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))
      simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)
    · simp only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]
      exact WithZero.exp_pos
    · have hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z := hx
      exact hN x (by rw [← hz]; exact hx'.le)
  have hcu : Continuous (Units.map c.toRingHom.toMonoidHom :
      (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ) := by
    rw [Units.continuous_iff]
    exact ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩
  have hs := hξo.mul (hμ.comp _ hcu).inv
  have hcl := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 ?_
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U := by
    have : d ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (denseRange_i s).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  have hm : Units.map c.toRingHom.toMonoidHom
      (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) =
      Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0) := Units.ext (hci k)
  show ξ _ * (μ (Units.map c.toRingHom.toMonoidHom _))⁻¹ = 1
  rw [hm, ← hglob]
  exact mul_inv_cancel _

theorem isParahoricVec_of_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : W, (∀ g : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((ξ d : ℂˣ) : ℂ) • u) → GlobalTheory.ThetaGL.IsParahoricVec μ π u := by
  intro L _ _ _ s r t W _ _ π ξ μ c hc hci hμ ⟨N, hN⟩ hglob u hvec
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous c hc
  have hlt : ∀ x, ValuativeRel.valuation _ x < 1 → Valued.v (c.symm x) < 1 := fun x hx =>
    (Valuation.isEquiv_iff_val_lt_one.1 hE).2 hx
  have hle : ∀ x, ValuativeRel.valuation _ x ≤ 1 →
      c.symm x ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun x hx =>
    (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  intro h hK hlow x hx
  obtain ⟨hi1, hi2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff h).1 hK
  let g := Matrix.GeneralLinearGroup.map c.symm.toRingHom h
  have hg : ∀ a b, g.val a b = c.symm (h.val a b) := fun a b => rfl
  have hg' : ∀ a b, (g⁻¹).val a b = c.symm ((h⁻¹).val a b) := fun a b => rfl
  have hpara : NG.ParaRT s r g := by
    refine ⟨GlobalTheory.ConjParahoric.mem_GLint_of_entries _ g (fun a b => hg a b ▸ hle _ (hi1 a b))
      (fun a b => hg' a b ▸ hle _ (hi2 a b)), fun a b ha hb => ?_⟩
    rw [hg]
    have ea : Fin.natAdd r (⟨a.val - r, by omega⟩ : Fin t) = a := by ext; simp; omega
    have eb : Fin.castAdd t (⟨b.val, hb⟩ : Fin r) = b := by ext; simp
    have := hlow ⟨a.val - r, by omega⟩ ⟨b.val, hb⟩
    rw [ea, eb] at this
    exact hlt _ this
  have hDD : c.symm (x : s.w.adicCompletion L) = NG.detDD s r g := by
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self (GlobalTheory.ConjParahoric.lowerEquiv r t), hx]
    refine (RingHom.map_det c.symm.toRingHom _).trans ?_
    congr 1
  have key := hvec g hpara (Units.map c.symm.toRingHom.toMonoidHom x) hDD
  have hpp : Matrix.GeneralLinearGroup.map c.toRingHom g = h :=
    Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
  have hcc : Units.map c.toRingHom.toMonoidHom (Units.map c.symm.toRingHom.toMonoidHom x) = x :=
    Units.ext (c.apply_symm_apply _)
  rw [hpp, GlobalTheory.SameParahoric.eq_comp s ξ μ c hc hci hμ N hN hglob, hcc] at key
  exact key

end GlobalTheory.SameParahoric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfUpperParahoricEigenStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParahoricTypeVector_of_upperParahoric_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : W, (∀ g : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((ξ d : ℂˣ) : ℂ) • u) → GlobalTheory.ThetaGL.IsParahoricVec μ π u := by
  first | exact @GlobalTheory.SameParahoric.isParahoricVec_of_eigen | exact GlobalTheory.SameParahoric.isParahoricVec_of_eigen | (intros; apply GlobalTheory.SameParahoric.isParahoricVec_of_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleImageNeZeroOfBlockTypeVector
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleImageNeZeroOfBlockTypeVector
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

abbrev sz (r t : ℕ) : Fin 2 → ℕ := ![r, t]

theorem sum_sz (r t : ℕ) : ∑ a, sz r t a = r + t := by simp [sz]

def blocks2 (r t : ℕ) : (Σ a : Fin 2, Fin (sz r t a)) ≃ Fin (r + t) := stdBlocks _ (sum_sz r t)

theorem blocks2_zero (r t : ℕ) (i : Fin r) : blocks2 r t ⟨0, i⟩ = Fin.castAdd t i := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 0 i).trans ?_
  simp

theorem blocks2_one (r t : ℕ) (j : Fin t) : blocks2 r t ⟨1, j⟩ = Fin.natAdd r j := by
  ext
  refine (stdBlocks_val (sz r t) (sum_sz r t) 1 j).trans ?_
  simp [sz]

theorem twoE_false (r t : ℕ) (i : Fin r) : two (stdSum (rfl : r + t = r + t)) ⟨false, i⟩ = Fin.castAdd t i := by
  ext; simp

theorem twoE_true (r t : ℕ) (j : Fin t) : two (stdSum (rfl : r + t = r + t)) ⟨true, j⟩ = Fin.natAdd r j := by
  ext; simp

end GlobalTheory.JacBlockTwo

noncomputable section

namespace GlobalTheory.JacBlockTwo

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.JacBlock ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_inl' (r t : ℕ) (i : Fin r) : stdSum (rfl : r + t = r + t) (Sum.inl i) = Fin.castAdd t i := by
  ext; simp

theorem stdSum_inr' (r t : ℕ) (j : Fin t) : stdSum (rfl : r + t = r + t) (Sum.inr j) = Fin.natAdd r j := by
  ext; simp

def IsUpperUnip {r t : ℕ} (g : GL (Fin (r + t)) k) : Prop :=
  (∀ (i : Fin t) (j : Fin r), (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.castAdd t j) = 0) ∧
  (∀ i j : Fin r, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.castAdd t i) (Fin.castAdd t j) =
    (1 : Matrix (Fin r) (Fin r) k) i j) ∧
  (∀ i j : Fin t, (g : Matrix (Fin (r + t)) (Fin (r + t)) k) (Fin.natAdd r i) (Fin.natAdd r j) =
    (1 : Matrix (Fin t) (Fin t) k) i j)

theorem mem_unipRad_two {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (two (stdSum (rfl : r + t = r + t))) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_two]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← stdSum_inl', ← stdSum_inr']; exact h0 i j
    · rw [← twoE_false, ← twoE_false]; exact hD false i j
    · rw [← twoE_true, ← twoE_true]; exact hD true i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun j i => ?_, ?_⟩
    · have := h0 j i; rwa [← stdSum_inl', ← stdSum_inr'] at this
    · rintro (_ | _) i j
      · have := h1 i j; rwa [← twoE_false, ← twoE_false] at this
      · have := h2 i j; rwa [← twoE_true, ← twoE_true] at this

theorem mem_unipRad_blocks2 {r t : ℕ} {g : GL (Fin (r + t)) k} :
    g ∈ unipRad k (blocks2 r t) ↔ IsUpperUnip g := by
  rw [mem_unipRad, mem_parab_iff]
  constructor
  · rintro ⟨h0, hD⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [← blocks2_one, ← blocks2_zero]; exact h0 1 0 i j (by decide)
    · rw [← blocks2_zero, ← blocks2_zero]; exact hD 0 i j
    · rw [← blocks2_one, ← blocks2_one]; exact hD 1 i j
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · match a, b with
      | 0, 0 => intro i j hab; exact absurd hab (lt_irrefl _)
      | 0, 1 => intro i j hab; exact absurd hab (by decide)
      | 1, 0 => intro i j _; rw [blocks2_one r t i, blocks2_zero r t j]; exact h0 i j
      | 1, 1 => intro i j hab; exact absurd hab (lt_irrefl _)
    · match a with
      | 0 => intro i j; rw [blocks2_zero r t i, blocks2_zero r t j]; exact h1 i j
      | 1 => intro i j; rw [blocks2_one r t i, blocks2_one r t j]; exact h2 i j

theorem unipRad_blocks2 (r t : ℕ) :
    unipRad k (blocks2 r t) = unipRad k (two (stdSum (rfl : r + t = r + t))) := by
  ext g; rw [mem_unipRad_blocks2, mem_unipRad_two]

theorem unipRad_two_inf_KO_le_stab {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v) :
    unipRad k (two (stdSum (rfl : r + t = r + t))) ⊓ KO k (Fin (r + t)) ≤ stab π v := by
  intro h hh
  obtain ⟨h0, h1, h2⟩ := mem_unipRad_two.1 hh.1
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = 1 := by ext i j; exact h2 i j
  have key := hv h hh.2 (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply]) 1
    (by rw [hsub, det_one, Units.val_one])
  show π h v = v
  rw [key, map_one, Units.val_one, one_smul]

theorem mulSingle_mem_KO {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) (a : Bool) :
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) a ∈ KO k (Two (Fin r) (Fin t) a) := by
  cases a
  · rw [Pi.mulSingle_eq_of_ne (by decide)]; exact one_mem _
  · rw [Pi.mulSingle_eq_same]; exact hg

theorem deltaHalf_mulSingle {r t : ℕ} {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    deltaHalf k (Two (Fin r) (Fin t)) (Pi.mulSingle true g) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
  exact GlobalTheory.StepData.valuation_det_of_mem_KO (mulSingle_mem_KO (r := r) hg a)

theorem act_mulSingle {r t : ℕ} {χ : kˣ →* ℂˣ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin (r + t)) k) W} {v : W} (hv : IsBlockVec χ π v)
    {g : GL (Fin t) k} (hg : g ∈ KO k (Fin t)) :
    π (leviEmb k (two (stdSum (rfl : r + t = r + t))) (Pi.mulSingle true g)) v =
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
  set h := leviEmb k (two (stdSum (rfl : r + t = r + t)))
    (Pi.mulSingle true g : Levi k (Two (Fin r) (Fin t))) with hdef
  have hKO : h ∈ KO k (Fin (r + t)) := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨intM_leviEmb _ _ fun a =>
      GlobalTheory.StepData.intM_of_mem_KO (mulSingle_mem_KO hg a), ?_⟩
    rw [hdef, ← map_inv]
    exact intM_leviEmb _ _ fun a => GlobalTheory.StepData.intM_of_mem_KO (inv_mem (mulSingle_mem_KO hg a))
  have h0 : ∀ (i : Fin t) (j : Fin r), h.val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := fun i j => by
    rw [← twoE_true, ← twoE_false]
    exact leviEmb_apply_ne k _ _ (by decide) _ _
  have h1 : ∀ i j : Fin r, h.val (Fin.castAdd t i) (Fin.castAdd t j) = (1 : Matrix (Fin r) (Fin r) k) i j :=
    fun i j => by
      rw [← twoE_false, ← twoE_false, hdef, leviEmb_apply_same, Pi.mulSingle_eq_of_ne (by decide)]
      rfl
  have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) = g.val := by
    ext i j
    rw [Matrix.submatrix_apply, ← twoE_true, ← twoE_true, hdef, leviEmb_apply_same, Pi.mulSingle_eq_same]
  exact hv h hKO (fun i j => by simp [h0]) (fun i j => by simp [h1, Matrix.one_apply])
    (Matrix.GeneralLinearGroup.det g) (by rw [hsub, Matrix.GeneralLinearGroup.val_det_apply])

theorem jacquet_ne_zero_of_isBlockVec_two : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsSmooth π → π.IsIrreducible → IsTame χ → v ≠ 0 → IsBlockVec χ π v → (Submodule.Quotient.mk v : Jacquet π (unipRad k (two (stdSum (rfl : r + t = r + t))))) ≠ 0 ∧ ∀ g ∈ KO k (Fin t), GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle true g) (Submodule.Quotient.mk v) = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • Submodule.Quotient.mk v := by
  intro hP k _ _ _ _ r t χ V _ _ π v hsm hirr hχ hv0 hv
  refine ⟨?_, ?_⟩
  · intro hx
    apply hv0
    have hx' : (Submodule.Quotient.mk v : Jacquet π (unipRad k (blocks2 r t))) = 0 := by
      rw [unipRad_blocks2]; exact hx
    refine hP k (r + t) 2 (sz r t) (blocks2 r t) ⟨V, π, hsm, hirr⟩ v ?_ hx'
    rw [unipRad_blocks2]
    rintro ⟨h, hh⟩
    have := sup_le (KOne_le_stab hχ hv) (unipRad_two_inf_KO_le_stab hv) hh
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  · intro g hg
    rw [jac_mk, deltaHalf_mulSingle hg, act_mulSingle hv hg, inv_one, Units.val_one, one_smul,
      Submodule.Quotient.mk_smul]

end GlobalTheory.JacBlockTwo

end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleImageNeZeroOfBlockTypeVectorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetModule_image_ne_zero_of_blockTypeVector : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsSmooth π → π.IsIrreducible → IsTame χ → v ≠ 0 → IsBlockVec χ π v → (Submodule.Quotient.mk v : Jacquet π (unipRad k (two (stdSum (rfl : r + t = r + t))))) ≠ 0 ∧ ∀ g ∈ KO k (Fin t), jac (two (stdSum (rfl : r + t = r + t))) π (Pi.mulSingle true g) (Submodule.Quotient.mk v) = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • Submodule.Quotient.mk v := by
  first | exact @GlobalTheory.JacBlockTwo.jacquet_ne_zero_of_isBlockVec_two | exact GlobalTheory.JacBlockTwo.jacquet_ne_zero_of_isBlockVec_two | (intros; apply GlobalTheory.JacBlockTwo.jacquet_ne_zero_of_isBlockVec_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectors
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Val

variable {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem val_lt_one_of_norm_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ < 1) :
    valuation F (e z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => z ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
  have h2 : Filter.Tendsto (fun n : ℕ => e z ^ n) Filter.atTop (nhds 0) := by
    have := ((he.tendsto 0).comp h1)
    simpa [Function.comp_def, map_pow] using this
  have h3 : {x : F | valuation F x < 1} ∈ nhds (0 : F) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun x hx => by simpa using hx⟩
  obtain ⟨n, hn⟩ := (h2.eventually h3).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation F (e z ^ n) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hn (not_lt.2 this)

theorem val_natCast_le_one (c : ℕ) : valuation F (c : F) ≤ 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
    push_cast
    exact (valuation F).map_add_le ih (by simp)

theorem val_le_one_of_norm_le_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ ≤ 1) :
    valuation F (e z) ≤ 1 := by
  let zi : ℤ_[g] := ⟨z, hz⟩
  have hm := PadicInt.sub_zmodRepr_mem zi
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hm
  have hm' : ‖z - (zi.zmodRepr : ℚ_[g])‖ < 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at hm
    exact hm
  have h1 := val_lt_one_of_norm_lt_one e he hm'
  have hz' : e z = e (z - (zi.zmodRepr : ℚ_[g])) + (zi.zmodRepr : F) := by
    rw [map_sub, map_natCast]; ring
  rw [hz']
  exact (valuation F).map_add_le h1.le (val_natCast_le_one _)

theorem norm_lt_one_of_val_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {y : ℚ_[g]}
    (hy : valuation F (e y) < 1) : ‖y‖ < 1 := by
  by_contra hc
  push_neg at hc
  have hy0 : y ≠ 0 := by rintro rfl; simp at hc; exact absurd hc (by norm_num)
  have h1 : ‖y⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hc
  have h2 := val_le_one_of_norm_le_one e he h1
  have h3 : valuation F (e y) * valuation F (e y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  have h4 : valuation F (e y) * valuation F (e y⁻¹) ≤ valuation F (e y) * 1 := by gcongr
  rw [h3, mul_one] at h4
  exact absurd hy (not_lt.2 h4)

theorem entry_of_val (e : ℚ_[g] ≃+* F) (he : Continuous e) (x : F) (c : ℕ) (hx : valuation F (x - c) < 1) :
    ∃ hA : ‖e.symm x‖ ≤ 1, PadicInt.toZMod (⟨e.symm x, hA⟩ : ℤ_[g]) = c := by
  have h1 : ‖e.symm x - c‖ < 1 :=
    norm_lt_one_of_val_lt_one e he (by rwa [map_sub, map_natCast, e.apply_symm_apply])
  have hc : ‖(c : ℚ_[g])‖ ≤ 1 := by
    have := PadicInt.norm_le_one (c : ℤ_[g])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
  have hA : ‖e.symm x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (e.symm x - c) (c : ℚ_[g])
    rw [sub_add_cancel] at this
    exact this.trans (max_le h1.le hc)
  refine ⟨hA, ?_⟩
  let zi : ℤ_[g] := ⟨e.symm x, hA⟩
  have hm : zi - (c : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def]
    simpa using h1
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at hm
  exact hm

end Val

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Mat

variable {g : ℕ} [Fact g.Prime]

def bm (r t : ℕ) (h : Gn g r) : Mt g (r + t) := fun i j =>
  if (i : ℕ) < r ∧ (j : ℕ) < r then entN (h : Mt g r) i j
  else if r ≤ (i : ℕ) ∧ r ≤ (j : ℕ) then entN ((1 : Gn g t) : Mt g t) (i - r) (j - r) else 0

theorem bm_isUnit (r t : ℕ) (h : Gn g r) : IsUnit (bm r t h) := by
  set M := bm r t h with hM
  have h0 : InPar r M := fun i j hj hi => by
    rw [hM]; show bm r t h i j = 0; unfold bm; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl r M = h := by
    ext i j
    have hi : (i : ℕ) < r + t := by omega
    have hj : (j : ℕ) < r + t := by omega
    simp [tl, entN, hM, bm, hi, hj]
  have h2 : br r t M = 1 := by
    ext i j
    simp [br, entN, hM, bm]
  have hd := LabelDet.det_inPar r t M h0
  rw [h1, h2, Matrix.det_one, mul_one] at hd
  rw [Matrix.isUnit_iff_isUnit_det, hd]
  exact Matrix.isUnits_det_units h

theorem blk_val (r t : ℕ) (h : Gn g r) : ((blk r t (r + t) h 1 : Gn g (r + t)) : Mt g (r + t)) = bm r t h := by
  show ((toG (bm r t h) : Gn g (r + t)) : Mt g (r + t)) = bm r t h
  unfold toG
  rw [dif_pos (bm_isUnit r t h)]
  exact IsUnit.unit_spec _

theorem bm_apply (r t : ℕ) (h : Gn g r) (a b : Fin (r + t)) : bm r t h a b =
    if hab : (a : ℕ) < r ∧ (b : ℕ) < r then (h : Mt g r) ⟨a, hab.1⟩ ⟨b, hab.2⟩ else if a = b then 1 else 0 := by
  unfold bm
  by_cases hab : (a : ℕ) < r ∧ (b : ℕ) < r
  · rw [if_pos hab, dif_pos hab]; simp [entN, hab]
  · rw [if_neg hab, dite_eq_right hab]
    by_cases h2 : r ≤ (a : ℕ) ∧ r ≤ (b : ℕ)
    · rw [if_pos h2]
      have ha : (a : ℕ) - r < t := by omega
      have hb : (b : ℕ) - r < t := by omega
      simp only [entN, dif_pos (And.intro ha hb), Units.val_one, Matrix.one_apply, Fin.ext_iff]
      congr 1
      apply propext
      omega
    · rw [if_neg h2, if_neg]
      intro e; subst e; omega

end Mat

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

theorem blockLift_act (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (r t : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V)
    (hu : u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) (h : GL (Fin r) (ZMod g))
    (h' : GL (Fin (r + t)) F) (hl : GlobalTheory.PendOf.IsLiftN h h') :
    ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  classical
  have hent : ∀ a b : Fin (r + t), ∃ hA : ‖e.symm (h'.val a b)‖ ≤ 1,
      PadicInt.toZMod (⟨e.symm (h'.val a b), hA⟩ : ℤ_[g]) = bm r t h a b := by
    intro a b
    have hab := hl a b
    rw [bm_apply]
    by_cases hc : (a : ℕ) < r ∧ (b : ℕ) < r
    · rw [dif_pos hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he _ _ hab
      exact ⟨hA, by rw [hA', ZMod.natCast_zmod_val]⟩
    · rw [dite_eq_right hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he (h'.val a b) (if a = b then 1 else 0)
        (by rw [hab]; split_ifs <;> simp)
      exact ⟨hA, by rw [hA']; split_ifs <;> simp⟩
  choose hA hA' using hent
  let A : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g] := fun a b => ⟨e.symm (h'.val a b), hA a b⟩
  have hmap : (PadicInt.toZMod (p := g)).mapMatrix A = bm r t h := by
    ext a b
    exact hA' a b
  have hdet : IsUnit A.det := by
    by_contra hn
    have h1 : A.det ∈ IsLocalRing.maximalIdeal ℤ_[g] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, hmap] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (bm_isUnit r t h)).ne_zero h1
  let A' : GL (Fin (r + t)) ℤ_[g] := Matrix.GeneralLinearGroup.mk'' A hdet
  have hred : red g (r + t) A' = blk r t (r + t) h 1 := by
    ext a b
    rw [blk_val]
    exact hA' a b
  have hh' : Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) A') = h' := by
    ext a b
    show e (algebraMap ℤ_[g] ℚ_[g] (A a b)) = h'.val a b
    rw [PadicInt.algebraMap_apply]
    exact e.apply_symm_apply _
  have hx0 : red g (r + t) (Function.invFun (red g (r + t)) (blk r t (r + t) h 1)) = blk r t (r + t) h 1 :=
    Function.invFun_eq ⟨A', hred⟩
  have hk : red g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A') = 1 := by
    rw [map_mul, map_inv, hx0, hred, inv_mul_cancel]
  have hfix := (Submodule.mem_iInf _).1 hu ⟨_, hk⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hfix
  have hsplit : h' = Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1)) *
      Matrix.GeneralLinearGroup.map e.toRingHom
        (inc g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A')) := by
    rw [← hh', lift, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hsplit, map_mul, Module.End.mul_apply]
  congr 1

end GlobalTheory.SerSys.BlockLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectorsStatement
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) → ∀ (h : GL (Fin r) (ZMod g)) (h' : GL (Fin (r + t)) F), GlobalTheory.PendOf.IsLiftN h h' → ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  first | exact @GlobalTheory.SerSys.BlockLift.blockLift_act | exact GlobalTheory.SerSys.BlockLift.blockLift_act | (intros; apply GlobalTheory.SerSys.BlockLift.blockLift_act <;> assumption)
end
end
