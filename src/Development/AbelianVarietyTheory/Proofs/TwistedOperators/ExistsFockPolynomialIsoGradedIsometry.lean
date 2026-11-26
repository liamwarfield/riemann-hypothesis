module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContra
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometry
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.SignedRename

open MvPolynomial

section General

variable {ι κ : Type} (σ : ι ≃ κ) (s : ι → ℂ)

def ren : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ := aeval fun v => s v • (X (σ v) : MvPolynomial κ ℂ)

theorem ren_monomial (k : ι →₀ ℕ) (c : ℂ) :
    ren σ s (monomial k c) = monomial (k.mapDomain σ) ((k.prod fun v n => s v ^ n) * c) := by
  classical
  have h1 : ∀ (v : ι) (n : ℕ), (s v • (X (σ v) : MvPolynomial κ ℂ)) ^ n =
      C (s v ^ n) * monomial (Finsupp.single (σ v) n) 1 := by
    intro v n
    rw [smul_pow, X_pow_eq_monomial, smul_eq_C_mul]
  rw [ren, aeval_monomial, Finsupp.mapDomain, monomial_finsupp_sum_index]
  simp only [Finsupp.prod, h1, Finset.prod_mul_distrib, algebraMap_eq]
  rw [← map_prod, C_mul]
  ring

theorem coeff_ren (k : ι →₀ ℕ) (P : MvPolynomial ι ℂ) :
    AddMonoidAlgebra.coeff (ren σ s P) (k.mapDomain σ) = (k.prod fun v n => s v ^ n) * AddMonoidAlgebra.coeff P k := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [ren_monomial, coeff_monomial, coeff_monomial]
    by_cases hm : m = k
    · subst hm
      simp
    · rw [if_neg hm, if_neg (fun h => hm (Finsupp.mapDomain_injective σ.injective h)), mul_zero]
  | add P Q hP hQ => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hP, hQ, mul_add]

theorem isHomogeneous_ren {ι κ : Type} (f : ι → κ) (s : ι → ℂ) (d : ℕ) (P : MvPolynomial ι ℂ) (h : P.IsHomogeneous d) :
    (aeval (fun v => s v • (X (f v) : MvPolynomial κ ℂ)) P).IsHomogeneous d := by
  have hg : ∀ v, (s v • (X (f v) : MvPolynomial κ ℂ)).IsHomogeneous 1 := by
    intro v
    rw [smul_eq_C_mul]
    exact isHomogeneous_C_mul_X _ _
  have h0 : ∀ r : ℂ, (algebraMap ℂ (MvPolynomial κ ℂ) r).IsHomogeneous 0 := fun r => isHomogeneous_C κ r
  rw [aeval_def]
  simpa only [one_mul] using h.eval₂ (algebraMap ℂ (MvPolynomial κ ℂ)) _ h0 hg

theorem fockIp_ren (hs : ∀ v, s v * conj (s v) = 1) (P Q : MvPolynomial ι ℂ) :
    fockIp (ren σ s P) (ren σ s Q) = fockIp P Q := by
  classical
  have hs0 : ∀ v, s v ≠ 0 := fun v h0 => by simpa [h0] using hs v
  have hp : ∀ k : ι →₀ ℕ, (k.prod fun v n => s v ^ n) ≠ 0 := by
    intro k
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hs0 v)
  have hpc : ∀ k : ι →₀ ℕ, (k.prod fun v n => s v ^ n) * conj (k.prod fun v n => s v ^ n) = 1 := by
    intro k
    rw [Finsupp.prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [map_pow, ← mul_pow, hs v, one_pow]
  have hback : ∀ k' : κ →₀ ℕ, (k'.mapDomain σ.symm).mapDomain σ = k' := by
    intro k'
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hfwd : ∀ k : ι →₀ ℕ, (k.mapDomain σ).mapDomain σ.symm = k := by
    intro k
    rw [← Finsupp.mapDomain_comp, Equiv.symm_comp_self, Finsupp.mapDomain_id]
  have hc : ∀ (R : MvPolynomial ι ℂ) (k' : κ →₀ ℕ), AddMonoidAlgebra.coeff (ren σ s R) k' =
      ((k'.mapDomain σ.symm).prod fun v n => s v ^ n) * AddMonoidAlgebra.coeff R (k'.mapDomain σ.symm) := by
    intro R k'
    conv_lhs => rw [← hback k']
    exact coeff_ren σ s _ R
  unfold fockIp
  refine Finset.sum_nbij' (fun k' => k'.mapDomain σ.symm) (fun k => k.mapDomain σ) ?_ ?_ ?_ ?_ ?_
  · intro k' hk'
    rw [mem_support_iff] at hk' ⊢
    rw [hc] at hk'
    exact right_ne_zero_of_mul hk'
  · intro k hk
    rw [mem_support_iff] at hk ⊢
    rw [coeff_ren]
    exact mul_ne_zero (hp k) hk
  · intro k' _
    exact hback k'
  · intro k _
    exact hfwd k
  · intro k' _
    have hF : ((k'.prod fun _ e => e.factorial : ℕ) : ℂ) =
        (((k'.mapDomain σ.symm).prod fun _ e => e.factorial : ℕ) : ℂ) := by
      have := Finsupp.prod_mapDomain_index_inj (h := fun (_ : κ) (e : ℕ) => e.factorial) σ.injective
        (s := k'.mapDomain σ.symm)
      rw [hback] at this
      rw [this]
    rw [hc P, hc Q, hF, map_mul]
    have := hpc (k'.mapDomain σ.symm)
    calc _ = (((k'.mapDomain σ.symm).prod fun v n => s v ^ n) *
          conj ((k'.mapDomain σ.symm).prod fun v n => s v ^ n)) *
          (AddMonoidAlgebra.coeff P (k'.mapDomain σ.symm) * conj (AddMonoidAlgebra.coeff Q (k'.mapDomain σ.symm)) *
          (((k'.mapDomain σ.symm).prod fun _ e => e.factorial : ℕ) : ℂ)) := by ring
      _ = _ := by rw [this, one_mul]

end General


open GlobalTheory.Chain.RealIt.PolyIso in
theorem exists_isPolyIso_graded_isometry : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), SignCompat ε e → SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ ∧ Graded κ ∧ ∀ P Q, fockIp (κ P) (κ Q) = fockIp P Q := by
  intro p q r s a b ε ε' e e' h h'
  refine ⟨(kap ε e e').toLinearEquiv, ⟨fun Z P => fwd_locS h h' Z P, fun Z P => fwd_locT h h' Z P⟩, ?_, ?_⟩
  · intro d P
    constructor
    · intro hP
      have hb : bwd ε e e' ((kap ε e e').toLinearEquiv P) = P := (kap ε e e').symm_apply_apply P
      rw [← hb]
      exact isHomogeneous_ren (fun l : Ix p q × Ix r s => (e' l.2, e l.1))
        (fun l => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε (e l.1))) d _ hP
    · intro hP
      exact isHomogeneous_ren (fun v : Fin b × Fin a => (e.symm v.2, e'.symm v.1))
        (fun v => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) d P hP
  · intro P Q
    let τ : Fin b × Fin a ≃ Ix p q × Ix r s := (Equiv.prodComm _ _).trans (Equiv.prodCongr e.symm e'.symm)
    have hs : ∀ v : Fin b × Fin a, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2) * conj (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) = 1 := by
      intro v
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn
      split <;> simp
    exact fockIp_ren τ (fun v => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) hs P Q

end GlobalTheory.ArchRec.SignedRename

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoGradedIsometryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockPolynomialIso_graded_isometry : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), SignCompat ε e → SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ ∧ Graded κ ∧ ∀ P Q, fockIp (κ P) (κ Q) = fockIp P Q := by
  first | exact @GlobalTheory.ArchRec.SignedRename.exists_isPolyIso_graded_isometry | exact GlobalTheory.ArchRec.SignedRename.exists_isPolyIso_graded_isometry | (intros; apply GlobalTheory.ArchRec.SignedRename.exists_isPolyIso_graded_isometry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingTensor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairTensor

open GlobalTheory.InvPairingTensor (exists_real_parts inner_act_skew exists_frame)

variable {p q : ℕ} {T : GrpData p q} (R : DSRep T)

theorem eq_zero_of_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (y : R.HK.V ⊗[ℂ] U)
    (hy : ∀ v, ctr R U v y = 0) : y = 0 := by
  let m : R.HK.V → R.HK.V →ₗ[ℂ] ℂ := fun v => innerₛₗ ℂ (R.ι v) ∘ₗ R.ι
  have sepm : ∀ b, (∀ v, m v b = 0) → b = 0 := fun b h => by
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h b)
  have key : ∀ v (z : R.HK.V ⊗[ℂ] U),
      GlobalTheory.PairingTensor.contrR (m v) (TensorProduct.comm ℂ _ _ z) = ctr R U v z := by
    intro v z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [TensorProduct.comm_tmul, GlobalTheory.PairingTensor.contrR_tmul, ctr_tmul]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  apply (TensorProduct.comm ℂ _ _).injective
  rw [map_zero]
  exact GlobalTheory.PairingTensor.eq_zero_of_contrR m sepm _ fun v => by rw [key, hy]

theorem ext_ctr (U : Type) [AddCommGroup U] [Module ℂ U] (z w : R.HK.V ⊗[ℂ] U)
    (h : ∀ v, ctr R U v z = ctr R U v w) : z = w := by
  rw [← sub_eq_zero]
  exact eq_zero_of_ctr R U _ fun v => by rw [map_sub, h, sub_self]

theorem ctr_add (U : Type) [AddCommGroup U] [Module ℂ U] (v w : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U (v + w) z = ctr R U v z + ctr R U w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_add (f := _), inner_add_left, add_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel

theorem ctr_smul (U : Type) [AddCommGroup U] [Module ℂ U] (c : ℂ) (v : R.HK.V)
    (z : R.HK.V ⊗[ℂ] U) : ctr R U (c • v) z = (starRingEnd ℂ) c • ctr R U v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [ctr_tmul, map_smul, inner_smul_left, mul_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]

theorem ctr_act (U : Type) [AddCommGroup U] [Module ℂ U] {X : Mat p q} (hX : X ∈ upq p q)
    (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U v (TensorProduct.map (R.HK.act X) LinearMap.id z) = -ctr R U (R.HK.act X v) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.map_tmul, ctr_tmul, ctr_tmul,
      eq_neg_of_add_eq_zero_left (inner_act_skew R hX v a), neg_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, neg_add]

variable {W U : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  (a : Mat p q →ₗ[ℂ] Module.End ℂ W)

theorem exists_finiteDimensional_kill (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) (P : W) :
    ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧
      ∀ y, (∀ x ∈ E, inner ℂ (R.ι y) (R.ι x) = 0) → B P y = 0 := by
  obtain ⟨W₀, hW, hP, hst⟩ := ha.2.1 P
  obtain ⟨E, hE, hE'⟩ := GlobalTheory.T.exists_finiteDimensional_forall_map_mem' p q R.HK hA _ a
    (fun Y Z _ _ => ha.1 Y Z) W₀ hW hst (fun v _ => ha.2.2 v)
  refine ⟨E, hE, fun y hy => ?_⟩
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  obtain ⟨F, hF, hyF, hFst⟩ := R.HK.kfin y
  obtain ⟨n, e, heF, he⟩ := exists_frame R.ι R.ι_inj F
  let φ : W →ₗ[ℂ] R.HK.V := ∑ j, (l ∘ₗ B.flip (e j)).smulRight (e j)
  have hφ : ∀ w, φ w = ∑ j, l (B w (e j)) • e j := fun w => by
    simp [φ, LinearMap.sum_apply]
  have hφF : ∀ w, φ w ∈ F := fun w => by
    rw [hφ]; exact F.sum_mem fun j _ => F.smul_mem _ (heF j)
  have hR : ∀ w, ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ w)) = l (B w x) := fun w x hx => by
    conv_rhs => rw [← he x hx]
    rw [hφ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, inner_sum, inner_smul_right, LinearMap.map_smulₛₗ,
      inner_conj_symm, smul_eq_mul, mul_comm]
  have hreal : ∀ X ∈ upq p q, IsKC X → ∀ w, φ (a X w) = R.HK.act X (φ w) := by
    intro X hX hK w
    have hd : φ (a X w) - R.HK.act X (φ w) ∈ F :=
      F.sub_mem (hφF _) (hFst X hK _ (hφF w))
    have h0 : ∀ x ∈ F, inner ℂ (R.ι x) (R.ι (φ (a X w) - R.HK.act X (φ w))) = 0 := by
      intro x hx
      have h1 := inner_act_skew R hX x (φ w)
      have h2 := congrArg l (hB X hX w x)
      rw [map_add (f := _), map_zero] at h2
      rw [hR w _ (hFst X hK x hx)] at h1
      rw [map_sub, inner_sub_right, hR _ x hx]
      linear_combination h2 - h1
    rw [← sub_eq_zero]
    apply R.ι_inj
    rw [map_zero]
    exact inner_self_eq_zero.1 (h0 _ hd)
  have heq : ∀ Z, IsKC Z → ∀ w, φ (a Z w) = R.HK.act Z (φ w) := by
    intro Z hZ w
    obtain ⟨X, Y, hX, hY, hK, rfl⟩ := exists_real_parts Z
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      hreal X hX (hK hZ).1, hreal Y hY (hK hZ).2]
  rw [← hR P y hyF]
  exact hy _ (hE' φ heq P hP)

theorem exists_pairing (f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U)
    (hf : ∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) :
    ∃ B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U, PInv a R B ∧ ∀ P v, B P v = ctr R U v (f P) := by
  let B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U :=
    { toFun := fun P =>
        { toFun := fun v => ctr R U v (f P)
          map_add' := fun v w => ctr_add R U v w _
          map_smul' := fun c v => ctr_smul R U c v _ }
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  refine ⟨B, fun Z hZ P v => ?_, fun _ _ => rfl⟩
  change ctr R U v (f (a Z P)) + ctr R U (R.HK.act Z v) (f P) = 0
  have := LinearMap.congr_fun (hf Z) P
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
  rw [this, ctr_act R U hZ, neg_add_cancel]

theorem exists_map (ha : IsGK a) (hA : AdmGK R.HK)
    (B : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PInv a R B) :
    ∃ f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U,
      (∀ Z, f ∘ₗ a Z = TensorProduct.map (R.HK.act Z) LinearMap.id ∘ₗ f) ∧
        ∀ P v, B P v = ctr R U v (f P) := by
  have ex : ∀ P, ∃ z : R.HK.V ⊗[ℂ] U, ∀ y, ctr R U y z = B P y := by
    intro P
    obtain ⟨E, hE, hkill⟩ := exists_finiteDimensional_kill R a ha hA B hB P
    obtain ⟨n, e, heE, he⟩ := exists_frame R.ι R.ι_inj E
    refine ⟨∑ j, e j ⊗ₜ[ℂ] B P (e j), fun y => ?_⟩
    have h1 := hkill (y - ∑ j, inner ℂ (R.ι (e j)) (R.ι y) • e j) (fun x hx => by
      rw [map_sub, inner_sub_left, sub_eq_zero]
      conv_lhs => rw [← he x hx]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
        inner_conj_symm, mul_comm])
    rw [map_sub, sub_eq_zero] at h1
    rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ctr_tmul, LinearMap.map_smulₛₗ, inner_conj_symm]
  choose g hg using ex
  let f : W →ₗ[ℂ] R.HK.V ⊗[ℂ] U :=
    { toFun := g
      map_add' := fun P Q => ext_ctr R U _ _ fun y => by
        rw [map_add (f := _), hg, hg, hg, map_add (f := _), LinearMap.add_apply]
      map_smul' := fun t P => ext_ctr R U _ _ fun y => by
        rw [map_smul, hg, hg, map_smul, RingHom.id_apply, LinearMap.smul_apply] }
  have hf : ∀ P y, ctr R U y (f P) = B P y := hg
  have hreal : ∀ X ∈ upq p q, ∀ P,
      f (a X P) = TensorProduct.map (R.HK.act X) LinearMap.id (f P) := by
    intro X hX P
    refine ext_ctr R U _ _ fun y => ?_
    rw [ctr_act R U hX, hf, hf]
    exact eq_neg_of_add_eq_zero_left (hB X hX P y)
  refine ⟨f, fun Z => ?_, fun P y => (hf P y).symm⟩
  obtain ⟨X, Y, hX, hY, -, rfl⟩ := exists_real_parts Z
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.comp_apply, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    TensorProduct.map_add_left, TensorProduct.map_smul_left, hreal X hX, hreal Y hY]

end GlobalTheory.ArchRec.PairTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelJointHarmonicsFormNormalisationUniquene
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelJointHarmonicsFormNormalisationUniquene
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MvPolynomial Matrix
open GlobalTheory.ArchRec GlobalTheory.FockDeg GlobalTheory.FockAlg.HarmStable

namespace GlobalTheory.ArchRec.Joint

variable {p q r s : ℕ}

theorem mem_pR_of_herm {Z : TH.Mat p q} (hZ : IsPC Z) (h : Zᴴ = Z) : Z ∈ pR p q := by
  refine ⟨?_, hZ⟩
  have hJ : TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  show Zᴴ * TH.Jm p q + TH.Jm p q * Z = 0
  rw [h, hJ]
  ext a b
  have := hZ a b
  rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem sameBlock_symm {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem exists_pR {Z : TH.Mat p q} (hZ : IsPC Z) :
    ∃ A ∈ pR p q, ∃ B ∈ pR p q, Z = (1 / 2 : ℂ) • A + (-Complex.I / 2) • B := by
  refine ⟨Z + Zᴴ, mem_pR_of_herm ?_ ?_, Complex.I • (Z - Zᴴ), mem_pR_of_herm ?_ ?_, ?_⟩
  · intro a b h
    simp [hZ a b h, hZ b a (sameBlock_symm h)]
  · rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  · intro a b h
    simp [hZ a b h, hZ b a (sameBlock_symm h)]
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    simp [← smul_neg]
  · rw [smul_smul, show -Complex.I / 2 * Complex.I = 1 / 2 by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

theorem minusPart_eq_zero_of_raise {σ : Type} (a : TH.Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
    {Φ : MvPolynomial σ ℂ} {d : ℕ} (hΦ : Φ.IsHomogeneous d)
    (h : ∀ Z ∈ pR p q, (a Z Φ).IsHomogeneous (d + 2)) (Z : TH.Mat p q) (hZ : IsPC Z) :
    minusPart (a Z) Φ = 0 := by
  obtain ⟨A, hA, B, hB, rfl⟩ := exists_pR hZ
  have hm : a ((1 / 2 : ℂ) • A + (-Complex.I / 2) • B) Φ ∈ homogeneousSubmodule σ ℂ (d + 2) := by
    rw [map_add (f := _), map_smul, map_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (h A hA)) (Submodule.smul_mem _ _ (h B hB))
  rw [minusPart_eq_zero_iff]
  intro e
  rw [homogeneousComponent_of_mem (show Φ ∈ homogeneousSubmodule σ ℂ d from hΦ)]
  split_ifs with he
  · rw [homogeneousComponent_of_mem hm, if_neg (by omega)]
  · simp

theorem raise_of_minusPart {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l = linePos l' → M l l' = 0) {Φ : Pol p q r s} {d : ℕ}
    (hΦ : Φ.IsHomogeneous d) (h : minusPart (omAct p q r s M) Φ = 0) :
    (omAct p q r s M Φ).IsHomogeneous (d + 2) := by
  rw [omAct_eq_parts hM, h, add_zero, plusPart_omAct hM]
  exact upOp_mem M d Φ hΦ

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem hc_mem_hwSub {σ : Type} {a : TH.Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
    (ha : ∀ Y, IsKC Y → DegZero (a Y)) {μ : Ix p q → ℚ} {Φ : MvPolynomial σ ℂ}
    (h : Φ ∈ hwSub a μ) (d : ℕ) : homogeneousComponent d Φ ∈ hwSub a μ := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢
  refine ⟨fun c => ?_, fun c e hce => ?_⟩
  · rw [← (ha _ (isKC_Eab (by cases c <;> trivial))).comm, h.1, map_smul]
  · rw [← (ha _ (isKC_Eab ?_)).comm, h.2 c e hce, map_zero]
    rcases c with c | c <;> rcases e with e | e <;> simp_all [sameBlock, posC]

theorem hc_mem_J (X : ProvA) {Φ : Pol p q r s} (h : Φ ∈ (X.fock p q r s).J) (d : ℕ) :
    homogeneousComponent d Φ ∈ (X.fock p q r s).J := by
  have g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 →
      minusPart A (homogeneousComponent d Φ) = 0 := by
    intro A hA
    rw [minusPart_eq_zero_iff] at hA ⊢
    intro e
    rw [hc_hc]
    split_ifs with he
    · rw [← he]; exact hA e
    · simp
  exact ⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩

theorem smul_mem_J (X : ProvA) {Φ : Pol p q r s} (h : Φ ∈ (X.fock p q r s).J) (c : ℂ) :
    c • Φ ∈ (X.fock p q r s).J := by
  have g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 → minusPart A (c • Φ) = 0 := by
    intro A hA
    rw [minusPart_eq_zero_iff] at hA ⊢
    intro e
    rw [map_smul, map_smul, map_smul, hA, smul_zero]
  exact ⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩

theorem line (X : ProvA) {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P Φ : Pol p q r s}
    (hJ : P ∈ (X.fock p q r s).J) (h : P ∈ hwSub (fockAct1 p q r s) μ)
    (h' : P ∈ hwSub (fockAct2 p q r s) μ') (h0 : Φ ≠ 0) (gJ : Φ ∈ (X.fock p q r s).J)
    (g : Φ ∈ hwSub (fockAct1 p q r s) μ) (g' : Φ ∈ hwSub (fockAct2 p q r s) μ') :
    ∃ c : ℂ, P = c • Φ := by
  have h2 := (GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 μ μ'
  have hs : JointShape p q r s μ μ' := by
    by_contra hs
    exact h0 ((Submodule.eq_bot_iff _).1 (h2.2 hs) Φ ⟨⟨g, g'⟩, Submodule.subset_span gJ⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    ⟨Φ, ⟨g, g'⟩, Submodule.subset_span gJ⟩
    (fun e => h0 (congrArg Subtype.val e))).1 (h2.1 hs) ⟨P, ⟨h, h'⟩, Submodule.subset_span hJ⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem cJoint_iff (X : ProvA) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (Φ : Pol p q r s) :
    CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔
      Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ := by
  constructor
  · rintro ⟨⟨d, hd, h1, h2⟩, h3⟩
    exact ⟨⟨minusPart_eq_zero_of_raise _ hd h1, minusPart_eq_zero_of_raise _ hd h2⟩, h3⟩
  · rintro ⟨hJ, h1, h2⟩
    obtain ⟨d, hd⟩ : ∃ d, homogeneousComponent d Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1.1
      rw [← sum_homogeneousComponent Φ]
      exact Finset.sum_eq_zero fun d _ => hc d
    obtain ⟨c, hc⟩ := line X hJ h1.2 h2.2 hd (hc_mem_J X hJ d)
      (hc_mem_hwSub (fun _ => degZero_fockAct1) h1.2 d)
      (hc_mem_hwSub (fun _ => degZero_fockAct2) h2.2 d)
    have hh : Φ.IsHomogeneous d := by
      rw [hc]
      exact (homogeneousSubmodule _ ℂ d).smul_mem c (homogeneousComponent_mem d Φ)
    exact ⟨⟨d, hh, fun Z hZ => raise_of_minusPart (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ.2) hh (hJ.1 Z hZ.2),
      fun Z hZ => raise_of_minusPart (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ.2) hh (hJ.2 Z hZ.2)⟩, h1, h2⟩

theorem joint_harmonics : ∀ (X : ProvA) (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔
      Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ) ∧
    (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ →
      ∃ c : ℝ, 0 < c ∧ JointHW (X.fock p q r s) μ μ' ((c : ℂ) • Φ)) ∧
    ∀ Φ Φ', CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ →
      CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ' → ∃ c : ℂ, Φ' = c • Φ := by
  intro X p q r s μ μ'
  refine ⟨cJoint_iff X μ μ', fun Φ h => ?_, fun Φ Φ' h h' => ?_⟩
  · obtain ⟨hJ, h1, h2⟩ := (cJoint_iff X μ μ' Φ).1 h
    have hn : 0 < ‖(X.fock p q r s).ι Φ‖ :=
      norm_pos_iff.2 fun e => h1.1 ((X.fock p q r s).ι_inj (e.trans (map_zero _).symm))
    have hc : ((‖(X.fock p q r s).ι Φ‖⁻¹ : ℝ) : ℂ) • Φ ≠ 0 :=
      smul_ne_zero (Complex.ofReal_ne_zero.2 (inv_pos.2 hn).ne') h1.1
    refine ⟨‖(X.fock p q r s).ι Φ‖⁻¹, inv_pos.2 hn, smul_mem_J X hJ _,
      ⟨hc, Submodule.smul_mem _ _ h1.2⟩, ⟨hc, Submodule.smul_mem _ _ h2.2⟩, ?_⟩
    rw [map_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · obtain ⟨hJ, h1, h2⟩ := (cJoint_iff X μ μ' Φ).1 h
    obtain ⟨hJ', h1', h2'⟩ := (cJoint_iff X μ μ' Φ').1 h'
    exact line X hJ' h1'.2 h2'.2 h1.1 hJ h1.2 h2.2

end GlobalTheory.ArchRec.Joint

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelJointHarmonicsFormNormalisationUniqueneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockModel_jointHarmonics_form_normalisation_uniqueness : ∀ (X : ProvA) (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔ Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ) ∧ (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ → ∃ c : ℝ, 0 < c ∧ JointHW (X.fock p q r s) μ μ' ((c : ℂ) • Φ)) ∧ ∀ Φ Φ', CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ → CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ' → ∃ c : ℂ, Φ' = c • Φ := by
  first | exact @GlobalTheory.ArchRec.Joint.joint_harmonics | exact GlobalTheory.ArchRec.Joint.joint_harmonics | (intros; apply GlobalTheory.ArchRec.Joint.joint_harmonics <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeConjReord

open Matrix Formalism.L2.Herm

section Perm

variable {n : ℕ}

theorem sum_perm_one (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) (i j : Fin n) :
    (∑ k, if f k = j then (if i = f k then (1 : R) else 0) else 0) = if i = j then 1 else 0 := by
  rw [Equiv.sum_comp f (fun m => if m = j then (if i = m then (1 : R) else 0) else 0)]
  simp

def pmat (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) : GL (Fin n) R where
  val := (1 : Matrix (Fin n) (Fin n) R).submatrix id f
  inv := (1 : Matrix (Fin n) (Fin n) R).submatrix id f.symm
  val_inv := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, Equiv.eq_symm_apply] using sum_perm_one R f i j
  inv_val := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, Equiv.eq_symm_apply] using sum_perm_one R f.symm i j

theorem pmat_inv (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) : (pmat R f)⁻¹ = pmat R f.symm := by
  ext i j
  rfl

theorem conj_pmat (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) (g : GL (Fin n) R) (a b : Fin n) :
    (((pmat R f)⁻¹ * g * pmat R f : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) a b = (g : Matrix (Fin n) (Fin n) R) (f a) (f b) := by
  rw [pmat_inv, Units.val_mul, Units.val_mul]
  show ((1 : Matrix (Fin n) (Fin n) R).submatrix id f.symm * (g : Matrix (Fin n) (Fin n) R) *
    (1 : Matrix (Fin n) (Fin n) R).submatrix id f) a b = _
  simp [Matrix.mul_apply, Matrix.one_apply, Equiv.eq_symm_apply]

theorem bc_pmat {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : Equiv.Perm (Fin n)) :
    Formalism.UG.bc φ (pmat R f) = pmat S f := by
  apply Units.ext
  ext i j
  simp only [Formalism.UG.bc, pmat] at *
  by_cases h : i = f j <;> simp [Matrix.one_apply, h]

theorem pmat_mulVec (R : Type) [CommRing R] (f : Equiv.Perm (Fin n)) (v : Fin n → R) :
    ((pmat R f.symm : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ v = fun i => v (f i) := by
  funext i
  show ((1 : Matrix (Fin n) (Fin n) R).submatrix id f.symm *ᵥ v) i = v (f i)
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Equiv.eq_symm_apply]

end Perm

section Frame

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frGL_mul_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (σ y : GL (Fin n) (intAf F E)) :
    frGL (β * intGL F E n σ) y = frGL β (σ * y * σ⁻¹) := by
  show β * intGL F E n σ * intGL F E n y * (β * intGL F E n σ)⁻¹ = β * intGL F E n (σ * y * σ⁻¹) * β⁻¹
  rw [map_mul, map_mul, map_inv]
  group

theorem St_mul_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (σ : GL (Fin n) (intAf F E)) :
    St (β * intGL F E n σ) = St β := by
  ext x
  simp only [St, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨σ * y * σ⁻¹, (frGL_mul_int β σ y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨σ⁻¹ * y * σ, ?_⟩
    rw [frGL_mul_int]
    congr 1
    group

theorem redFn_mul_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (σ : GL (Fin n) (intAf F E)) (PP : Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    redFn (β * intGL F E n σ) PP x = (Formalism.UG.bc (resS F PP) σ)⁻¹ * redFn β PP x * Formalism.UG.bc (resS F PP) σ := by
  by_cases hx : x ∈ St β
  · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
    have hy : frGL β y = frGL (β * intGL F E n σ) (σ⁻¹ * y * σ) := by
      rw [frGL_mul_int]
      congr 1
      group
    rw [redFn_frGL β PP y, hy, redFn_frGL]
    simp only [map_mul, map_inv]
  · have hx' : x ∉ St (β * intGL F E n σ) := by rwa [St_mul_int]
    simp [redFn, ext1, hx, hx']

theorem isFrame_mul_pmat {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (h : IsFrame β Λ)
    (f : Equiv.Perm (Fin n)) : IsFrame (β * intGL F E n (pmat _ f)) Λ := by
  unfold Formalism.L2.DIV.IsFrame at h ⊢
  intro x
  have e : (((β * intGL F E n (pmat _ f))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
      Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x =
      fun i => (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x) (f i) := by
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv (intGL F E n) (pmat _ f), pmat_inv]
    unfold intGL
    rw [bc_pmat, pmat_mulVec]
  rw [h x, e]
  exact ⟨fun hx i => hx (f i), fun hx i => by simpa using hx (f.symm i)⟩

end Frame

section Level

variable {D : D7}

theorem rankBlock_val_eq_submatrix_of_le_rank {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (M : GL (Fin n) κ) :
    ((upperLeftBlock hr M : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) =
      (M : Matrix (Fin n) (Fin n) κ).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
  apply upper_block_val_submatrix
  rw [mem_blockTri]
  intro i j hij
  have hi : i.val < r := lt_of_lt_of_le i.isLt hn
  simp [blk2, hi] at hij

theorem blockTri_all {κ : Type} [CommRing κ] {n r : ℕ} (t : ℕ) (hn : n ≤ r) (M : GL (Fin n) κ) :
    M ∈ blockTri (blkOf r t) := by
  rw [mem_blockTri]
  intro i j hij
  have hi : i.val < r := lt_of_lt_of_le i.isLt hn
  simp [blkOf, hi] at hij

def fperm {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (π : Equiv.Perm (Fin r)) : Equiv.Perm (Fin n) :=
  ((finCongr (le_antisymm hr hn)).symm.trans π.symm).trans (finCongr (le_antisymm hr hn))

theorem fperm_castLE {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (π : Equiv.Perm (Fin r)) (a : Fin r) :
    fperm hr hn π (Fin.castLE hr (π a)) = Fin.castLE hr a := by
  have h1 : (finCongr (le_antisymm hr hn)).symm (Fin.castLE hr (π a)) = π a := Fin.ext (by simp)
  simp only [fperm, Equiv.trans_apply, h1, Equiv.symm_apply_apply]
  exact Fin.ext (by simp)

theorem reord_rTup {n : ℕ} (L : LevDat D.host.E ℂ n) (hn : n ≤ L.r) (β : GL (Fin n) (EAf D))
    (π : Equiv.Perm (Fin L.r)) (x : GL (Fin n) (EAf D)) :
    reord π (rTup (β * intGL _ _ n (pmat _ (fperm L.hr hn π))) L x) = rTup β L x := by
  funext PP
  apply Units.ext
  ext a b
  show (upperLeftBlock L.hr (redFn (β * intGL _ _ n (pmat _ (fperm L.hr hn π))) PP.1 x)).1 (π a) (π b) =
    (upperLeftBlock L.hr (redFn β PP.1 x)).1 a b
  rw [rankBlock_val_eq_submatrix_of_le_rank L.hr hn, rankBlock_val_eq_submatrix_of_le_rank L.hr hn, redFn_mul_int, bc_pmat]
  simp only [Matrix.submatrix_apply]
  rw [conj_pmat, fperm_castLE, fperm_castLE]

theorem rank_zeroth_component_eq : (Yc D 0).rank ≤ D.R.r := by
  have h := D.sp.Y_rank 0 (Nat.zero_le _)
  show (D.sp.Y (min 0 D.R.m)).rank ≤ D.R.r
  rw [Nat.zero_min, h]
  show D.R.r + 0 * D.R.t ≤ D.R.r
  simp

end Level

section Main

variable {D : D7}

def r0 {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : GL (Fin (Yc D 0).rank) (EAf D)) :
    G0 Lc.Pg D.R.r :=
  fun PP => upperLeftBlock (r_le_Y 0) (redFn β PP.1 x)

theorem mem_levelSubgroup_principalDatum_iff {T : Type} (Lc : LevCh D T) (P : LevelP Lc.Pg D.R.r ℂ) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (κ : GA D (Yc D 0)) :
    κ ∈ levS (Yc D 0) β (Lc.dat0 P) ↔
      (κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β) ∧
        r0 Lc β (finE (Yc D 0) κ) ∈ P.H := by
  have hP : (Lc.dat0 P).P = P := by simp [LevCh.dat0, datY]
  have hblk : ∀ PP ∈ (Lc.dat0 P).Pg,
      redFn β PP (finE (Yc D 0) κ) ∈ blockTri (blkOf (Lc.dat0 P).r (Lc.dat0 P).t) :=
    fun PP _ => blockTri_all _ (rank_zeroth_component_eq (D := D)) _
  have hQ : ∀ PP ∈ (Lc.dat0 P).Q, redFn β PP (finE (Yc D 0) κ) ∈ blockTri (blk2 (Lc.dat0 P).r) := by
    intro PP h
    simp [LevCh.dat0, datY] at h
  rw [Formalism.IndefR.Links.levS, Formalism.IndefR.Lev.levG, SetLike.mem_coe, Formalism.IndefR.Lev.mem_levA, Formalism.L2.DIV.mem_lev,
    Formalism.L2.DIV.mem_parLev, hP]
  exact ⟨fun ⟨h1, ⟨h2, h3, _, _⟩, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩,
    fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, ⟨h2, h3, hblk, hQ⟩, h4⟩⟩

theorem principalRowLevelCharacter_trivial {T : Type} (Lc : LevCh D T) (P : LevelP Lc.Pg D.R.r ℂ) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (κ : GA D (Yc D 0)) :
    levChi (Yc D 0) β (Lc.dat0 P) κ = ((ext1 P.H P.chi (r0 Lc β (finE (Yc D 0) κ)) : ℂˣ) : ℂ) := by
  have hs : (Lc.dat0 P).s = 0 := rfl
  have hQ : (Lc.dat0 P).Q = ∅ := rfl
  have hP : (Lc.dat0 P).P = P := by simp [LevCh.dat0, datY]
  rw [Formalism.IndefR.Lev.levChi, levFn, hs, hQ, hP]
  simp only [Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

theorem level_eq_of_reord {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r))
    (hH : ∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) (hchi : ∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩)
    (β₂ β₃ : GL (Fin (Yc D 0).rank) (EAf D)) (hSt : St β₂ = St β₃)
    (hkey : ∀ x, reord π (r0 Lc β₂ x) = r0 Lc β₃ x) (κ : GA D (Yc D 0)) :
    (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧
      levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  refine ⟨?_, ?_⟩
  · rw [mem_levelSubgroup_principalDatum_iff, mem_levelSubgroup_principalDatum_iff, hSt, hH, hkey]
  · rw [principalRowLevelCharacter_trivial, principalRowLevelCharacter_trivial]
    by_cases hg : r0 Lc β₂ (finE (Yc D 0) κ) ∈ P.H
    · have hg' : r0 Lc β₃ (finE (Yc D 0) κ) ∈ P'.H := by
        rw [← hkey]
        exact (hH _).1 hg
      have e : (⟨reord π (r0 Lc β₂ (finE (Yc D 0) κ)), (hH _).1 hg⟩ : P'.H) = ⟨r0 Lc β₃ (finE (Yc D 0) κ), hg'⟩ :=
        Subtype.ext (hkey _)
      rw [extendOne_of_mem _ hg, extendOne_of_mem _ hg', hchi _ hg ((hH _).1 hg), e]
    · have hg' : r0 Lc β₃ (finE (Yc D 0) κ) ∉ P'.H := by
        rw [← hkey]
        exact fun h => hg ((hH _).2 h)
      unfold ext1
      rw [dite_eq_right hg, dite_eq_right hg']

end Main

theorem exists_frame_reord : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r)), (∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) → (∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩) → ∀ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∃ β₂ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₂ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧ levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  intro D T Lc P P' π hH hchi β₃ hβ
  exact ⟨β₃ * intGL _ _ _ (pmat _ (fperm (Lc.dat0 P).hr (rank_zeroth_component_eq (D := D)) π)), isFrame_mul_pmat hβ _,
    fun κ => level_eq_of_reord Lc P P' π hH hchi _ β₃ (St_mul_int _ _)
      (fun x => reord_rTup (Lc.dat0 P) (rank_zeroth_component_eq (D := D)) β₃ π x) κ⟩

end GlobalTheory.SeeConjReord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_reordering_levelData : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r)), (∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) → (∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩) → ∀ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∃ β₂ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₂ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧ levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  first | exact @GlobalTheory.SeeConjReord.exists_frame_reord | exact GlobalTheory.SeeConjReord.exists_frame_reord | (intros; apply GlobalTheory.SeeConjReord.exists_frame_reord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterPlacesOddAndPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterPlacesOddAndPrincipalLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanPlaces

theorem pg_nonempty {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) : L.Pg.Nonempty := by
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty ((L.C.P.pb 0).asIdeal.primesOver (𝓞 D.host.E)))
  have hne : W ≠ ⊥ := by
    rintro rfl
    have := hWQ.over
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)] at this
    exact (L.C.P.pb 0).ne_bot this
  exact ⟨⟨W, hW, hne⟩, (hL.Pg _).2 ⟨0, HeightOneSpectrum.ext hWQ.over.symm⟩⟩

theorem two_not_mem {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (t : T0) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h : PP ∈ L.Pg ∨ PP ∈ L.Q t) : (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
  rcases h with hm | hm
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
    have hgk := GlobalTheory.LevelPlaces.mem_of_div _ k PP hk
    have hn := GlobalTheory.LevelPlaces.not_mem_of_prime PP.isPrime.ne_top Nat.prime_two (D.host.g_prime k)
      (Formalism.L2.Pj.g_ne_two D k) hgk
    simpa using hn
  · intro h2
    apply (hL.Q_off t PP hm).1
    push_cast
    have hQS : ((D.host.QS : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      obtain ⟨c, hc⟩ := D.host.two_dvd_QS
      rw [hc]
      push_cast
      exact Ideal.mul_mem_right _ _ h2
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hQS))

theorem mem_levG {D : D7} {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (k : GA D (Wc D i))
    (hk : k ∈ GfC (Wc D i)) (hS : Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (L.βW i))
    (hr : ∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn (L.βW i) PP (Lev.finE (Wc D i) k) = 1) :
    k ∈ Lev.levG (Wc D i) (L.βW i) (L.datWp i L.triv) := by
  refine Subgroup.mem_inf.2 ⟨hk, ?_⟩
  show Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Wc D i).gram (L.βW i) (L.datWp i L.triv)
  refine GlobalTheory.LevSplit.mem_lev_of_red D.sp.cm (Wc D i).gram (L.βW i) (L.datWp i L.triv) _
    (GlobalTheory.LevSplit.finE_mem_UA _ k) hS (fun PP hP => ?_)
  rcases hP with hP | hP
  · exact hr PP hP
  · exact absurd hP (Finset.notMem_empty _)

theorem places_level : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → L.Pg.Nonempty ∧ (∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) ∧ ∀ (i : Fin D.R.m) (k : GA D (Wc D i)), k ∈ GfC (Wc D i) → Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (L.βW i) → (∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn (L.βW i) PP (Lev.finE (Wc D i) k) = 1) → k ∈ Lev.levG (Wc D i) (L.βW i) (L.datWp i L.triv) ∧ Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  intro D T0 L μ0 hL
  refine ⟨pg_nonempty hL, fun t PP h => two_not_mem hL t PP h, fun i k hk hS hr => ⟨mem_levG L i k hk hS hr, ?_⟩⟩
  exact GlobalTheory.HolRead.PrincLevelSub.levChi_triv L i k

end GlobalTheory.SpanPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterPlacesOddAndPrincipalLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_places_odd_and_principal_level : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → L.Pg.Nonempty ∧ (∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) ∧ ∀ (i : Fin D.R.m) (k : GA D (Wc D i)), k ∈ GfC (Wc D i) → Lev.finE (Wc D i) k ∈ Formalism.L2.DIV.St (L.βW i) → (∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn (L.βW i) PP (Lev.finE (Wc D i) k) = 1) → k ∈ Lev.levG (Wc D i) (L.βW i) (L.datWp i L.triv) ∧ Lev.levChi (Wc D i) (L.βW i) (L.datWp i L.triv) k = 1 := by
  first | exact @GlobalTheory.SpanPlaces.places_level | exact GlobalTheory.SpanPlaces.places_level | (intros; apply GlobalTheory.SpanPlaces.places_level <;> assumption)
end
end
