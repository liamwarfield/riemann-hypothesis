module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvRoots
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

section CapelliMinorMembership

variable (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw)

def piCoef (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (u : Formalism.IndefR.NX.U D.nd) : ↥D.LL0 :=
  (Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹ * (((psiUOf D.nd (NX.xiRed D) θ u)⁻¹ : (↥D.LL0)ˣ) : ↥D.LL0)

def eLop (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g

def piLop (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) : Module.End D.what₂.LL (S.WL j) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, ((piCoef D θ u : ↥D.LL0) : D.what₂.LL) • actL D S j (u : G0g D.nd)


open Classical in
def evRoots (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Finset ↥D.LL0 :=
  (Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ).image fun σ => In.eig j σ k P

def evPol (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Polynomial ↥D.LL0 :=
  ∏ r ∈ evRoots D S In j k P, (X - C r)

def phiLop (In : RatIn D S) (j k : ℕ) (P : PlE D.host) : Module.End D.what₂.LL (S.WL j) :=
  aeval (In.hL j k P) ((evPol D S In j k P).map (algebraMap ↥D.LL0 D.what₂.LL))

def hLT (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  (Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (hLr D S In j k P) :
    Module.End (KT D T i b) (KT D T i b ⊗[S.Ks] ↥(WKr D S j)))

def piKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  ∑ᶠ u : Formalism.IndefR.NX.U D.nd, readT D T i b (piCoef D In.θ u) • (actGT D T S In.rho In.chi i j b (u : G0g D.nd)).toLinearMap

def phiKop (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    Module.End (FractionRing (T.O i)) (FmT D T S i j b) :=
  aeval (hLT D T S In i j b k P) ((evPol D S In j k P).map (readT D T i b))

theorem hkT_eq (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) :
    hkT D T S In i j b k P = (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k • hLT D T S In i j b k P :=
  rfl

end CapelliMinorMembership

end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdempotentProjectorVanishingBaseChangeTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdempotentProjectorVanishingBaseChangeTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem transfer_aeval (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (F : Module.End D.what₂.LL (S.WL j)) (G : Module.End (FractionRing (T.O i)) (FmT D T S i j b))
    (hFG : ∀ x, Φ (F x) = G (Φ x)) (p : Polynomial ↥D.LL0) (x : S.WL j) :
    Φ (aeval F (p.map (algebraMap ↥D.LL0 D.what₂.LL)) x) = aeval G (p.map (readT D T i b)) (Φ x) := by
  have hpow : ∀ (n : ℕ) (y : S.WL j), Φ ((F ^ n) y) = (G ^ n) (Φ y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hFG]
  induction p using Polynomial.induction_on' generalizing x with
  | add p q hp hq => rw [Polynomial.map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply,
      map_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, IntermediateField.algebraMap_apply,
      hc, hpow]

theorem transfer_piLop (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (x : S.WL j) : Φ (piLop D S In.θ j x) = piKop D T S In i j b (Φ x) := by
  haveI : Fintype (Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  unfold piLop piKop
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, hc, ha, LinearEquiv.coe_coe]

theorem phiKop_eGT_piKop_eq_zero : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ)
    (b : Bool) (k : ℕ) (P : PlE D.host),
    1 ≤ j → j ≤ D.R.m → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 →
    phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b = 0 := by
  intro D T S In i j b k P h1 h2 h0
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he : ∀ x, Φ (eLop D S j x) = eGT D T S In.rho In.chi i j b (Φ x) := descend_eSum D T S In i j b Φ hc ha
  have hpi := transfer_piLop D T S In i j b Φ hc ha
  have hr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    split_ifs with h
    · rfl
    · exact absurd ⟨h1, h2⟩ h
  have hh : ∀ x, Φ (In.hL j k P x) = hLT D T S In i j b k P (Φ x) := fun x => hf _ _ hr x
  have hphi : ∀ x, Φ (phiLop D S In j k P x) = phiKop D T S In i j b k P (Φ x) :=
    transfer_aeval D T S i j b Φ hc _ _ hh (evPol D S In j k P)
  have key : ∀ w : ↥(WKr D S j),
      (phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b)
        ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = 0 := by
    intro w
    rw [← hw, Module.End.mul_apply, Module.End.mul_apply, ← hpi, ← he, ← hphi]
    have h3 := LinearMap.congr_fun h0 (w : S.WL j)
    rw [Module.End.mul_apply, Module.End.mul_apply] at h3
    rw [h3, LinearMap.zero_apply, map_zero]
  set f := phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b with hfdef
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.zero_apply]
  change KT D T i b ⊗[S.Ks] ↥(WKr D S j) at y
  induction y using TensorProduct.induction_on with
  | zero => exact f.map_zero
  | tmul c w =>
    have hcw : (c ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) =
        (c : FractionRing (T.O i)) • ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hcw]
    exact (f.map_smul (c : FractionRing (T.O i))
      (show FmT D T S i j b from ((1 : KT D T i b) ⊗ₜ[S.Ks] w : KT D T i b ⊗[S.Ks] ↥(WKr D S j)))).trans
      (by rw [key]; exact smul_zero _)
  | add y z hy hz =>
    exact (f.map_add (show FmT D T S i j b from y) (show FmT D T S i j b from z)).trans (by rw [hy, hz, add_zero])

end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeIdempotentProjectorVanishingBaseChangeTwistStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIdempotentProjector_vanishing_baseChange_twistSide : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host),
    1 ≤ j → j ≤ D.R.m → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 →
    phiKop D T S In i j b k P * eGT D T S In.rho In.chi i j b * piKop D T S In i j b = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero | exact GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero | (intros; apply GlobalTheory.HeightCounting.FormsStep.phiKop_eGT_piKop_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckePolyMulCentralIdempotentMulGenericProjector
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckePolyMulCentralIdempotentMulGenericProjector
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

section HeckeKill

variable (D : D7) (S : RatDat D.ntw)

theorem actL_mul (j : ℕ) (g h : G0g D.nd) : actL D S j (g * h) = actL D S j g * actL D S j h := by
  unfold actL
  rw [map_mul, map_mul, map_mul, Units.val_mul, mul_inv, smul_mul_smul_comm]

theorem actL_one (j : ℕ) : actL D S j 1 = 1 := by
  unfold actL
  rw [map_one, map_one, map_one, Units.val_one, inv_one, one_smul]

def actLHom (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun := actL D S j
  map_one' := actL_one D S j
  map_mul' := actL_mul D S j

def actAlg (j : ℕ) : MonoidAlgebra ↥D.LL0 (G0g D.nd) →+* Module.End D.what₂.LL (S.WL j) :=
  (MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (actLHom D S j)).toRingHom.comp
    (MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL))

theorem actAlg_of (j : ℕ) (g : G0g D.nd) : actAlg D S j (MonoidAlgebra.of _ _ g) = actL D S j g := by
  simp [actAlg, MonoidAlgebra.of_apply, actLHom]

theorem actAlg_eL (j : ℕ) : actAlg D S j (eL D) = eLop D S j := by
  letI := Fintype.ofFinite (G0g D.nd)
  rw [eLop, finsum_eq_sum_of_fintype]
  simp [actAlg, eL, MonoidAlgebra.lift_apply, actLHom]
  rw [Finsupp.sum_fintype _ (fun a (b : D.what₂.LL) => b • actL D S j a) (fun _ => zero_smul _ _)]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1

theorem eLop_idem (j : ℕ) : eLop D S j * eLop D S j = eLop D S j := by
  rw [← actAlg_eL, ← map_mul, (eIdem_all D).1]

theorem eLop_comm (j : ℕ) (g : G0g D.nd) : eLop D S j * actL D S j g = actL D S j g * eLop D S j := by
  rw [← actAlg_eL, ← actAlg_of, ← map_mul, (eIdem_all D).2 g, map_mul]

theorem piCoef_shift (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (u w : Formalism.IndefR.NX.U D.nd) :
    piCoef D θ (u⁻¹ * w) = (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0)) * piCoef D θ w := by
  unfold piCoef
  rw [map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]
  ring

theorem actL_piLop (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ)
    (u : Formalism.IndefR.NX.U D.nd) :
    actL D S j u * piLop D S θ j =
      ((((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) • piLop D S θ j := by
  letI := Fintype.ofFinite (Formalism.IndefR.NX.U D.nd)
  rw [piLop, finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.smul_sum]
  have h1 : ∀ v : Formalism.IndefR.NX.U D.nd,
      actL D S j u * (((piCoef D θ v : ↥D.LL0) : D.what₂.LL) • actL D S j (v : G0g D.nd)) =
        ((piCoef D θ (u⁻¹ * (u * v)) : ↥D.LL0) : D.what₂.LL) • actL D S j ((u * v : Formalism.IndefR.NX.U D.nd) : G0g D.nd) := by
    intro v
    rw [inv_mul_cancel_left, mul_smul_comm, Subgroup.coe_mul, actL_mul]
  simp_rw [h1]
  rw [Fintype.sum_equiv (Equiv.mulLeft u)
    (fun v => ((piCoef D θ (u⁻¹ * (u * v)) : ↥D.LL0) : D.what₂.LL) • actL D S j ((u * v : Formalism.IndefR.NX.U D.nd) : G0g D.nd))
    (fun w => ((piCoef D θ (u⁻¹ * w) : ↥D.LL0) : D.what₂.LL) • actL D S j (w : G0g D.nd)) (fun v => rfl)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [piCoef_shift, IntermediateField.coe_mul, mul_smul]

theorem eig_le_ker (In : RatIn D S) (j k : ℕ) (P : PlE D.host) (r : ↥D.LL0) (hr : r ∈ evRoots D S In j k P) :
    Module.End.eigenspace (In.hL j k P) ((r : ↥D.LL0) : D.what₂.LL) ≤ LinearMap.ker (phiLop D S In j k P) := by
  intro x hx
  rw [LinearMap.mem_ker]
  by_cases h0 : x = 0
  · rw [h0, map_zero]
  have hev : (In.hL j k P).HasEigenvector ((r : ↥D.LL0) : D.what₂.LL) x := Module.End.hasEigenvector_iff.mpr ⟨hx, h0⟩
  unfold phiLop
  rw [Module.End.aeval_apply_of_hasEigenvector hev, eval_map,
    show ((r : ↥D.LL0) : D.what₂.LL) = algebraMap ↥D.LL0 D.what₂.LL r from rfl, eval₂_at_apply]
  have he : (evPol D S In j k P).eval r = 0 := by
    unfold evPol
    rw [eval_prod]
    exact Finset.prod_eq_zero hr (by simp)
  rw [he, map_zero, zero_smul]

end HeckeKill

theorem phiLop_eLop_piLop : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (j k : ℕ) (P : PlE D.host), 1 ≤ j → j ≤ D.R.m → 1 ≤ k → k ≤ D.R.r →
    IsSplitPl D.host P → P ∉ In.Sb → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 := by
  intro D S In j k P hj1 hj2 hk1 hk2 hsp hP
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.zero_apply, Module.End.mul_apply, Module.End.mul_apply]
  have hg : eLop D S j (piLop D S In.θ j y) ∈ goodL D S In.θ j := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · change eLop D S j (piLop D S In.θ j y) ∈ Module.End.eigenspace (eLop D S j) 1
      rw [Module.End.mem_eigenspace_iff, one_smul, ← Module.End.mul_apply, eLop_idem]
    · refine Submodule.mem_iInf _ |>.mpr fun u => ?_
      rw [Module.End.mem_eigenspace_iff, ← Module.End.mul_apply, ← eLop_comm, Module.End.mul_apply,
        ← Module.End.mul_apply (actL D S j u), actL_piLop, LinearMap.smul_apply, map_smul]
  have hs := In.span j hj1 hj2 hg
  have hle : (⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D S In.θ j ⊓ ⨅ (k : ℕ) (P : PlE D.host)
      (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ In.Sb),
        Module.End.eigenspace (In.hL j k P) ((In.eig j σ k P : ↥D.LL0) : D.what₂.LL)) ≤
      LinearMap.ker (phiLop D S In j k P) := by
    refine iSup₂_le fun σ hσ => inf_le_right.trans ?_
    refine (iInf_le _ k).trans ((iInf_le _ P).trans ((iInf_le _ ⟨hk1, hk2, hsp, hP⟩).trans ?_))
    classical
    exact eig_le_ker D S In j k P _ (Finset.mem_image.mpr ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩, rfl⟩)
  exact LinearMap.mem_ker.mp (hle hs)

end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckePolyMulCentralIdempotentMulGenericProjectorStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePoly_mul_centralIdempotent_mul_genericProjector : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (j k : ℕ) (P : PlE D.host), 1 ≤ j → j ≤ D.R.m → 1 ≤ k → k ≤ D.R.r →
    IsSplitPl D.host P → P ∉ In.Sb → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop | exact GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop | (intros; apply GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericCharacterProjectorOnTwistFormsFix
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericCharacterProjectorOnTwistFormsFix
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem piKop_fix : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool),
    ∀ y ∈ Fm0T D T S In.rho In.chi In.θ i j b, piKop D T S In i j b y = y := by
  intro D T S In i j b y hy
  classical
  haveI : Fintype (Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  have hu : ∀ u : Formalism.IndefR.NX.U D.nd, (actGT D T S In.rho In.chi i j b (u : G0g D.nd)) y =
      ((psiUT D T In.θ i b u : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) • y := by
    intro u
    have h := (Submodule.mem_iInf _).1 hy u
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    simpa using h
  unfold piKop
  rw [finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  have hterm : ∀ u : Formalism.IndefR.NX.U D.nd,
      (readT D T i b (piCoef D In.θ u) • (actGT D T S In.rho In.chi i j b (u : G0g D.nd)).toLinearMap) y =
        readT D T i b ((Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹) • y := by
    intro u
    rw [LinearMap.smul_apply, LinearEquiv.coe_toLinearMap, hu, smul_smul]
    congr 1
    unfold piCoef psiUT
    simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, ← map_mul, mul_assoc, Units.inv_mul, mul_one]
  rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul (FractionRing (T.O i)), smul_smul]
  have hne : (Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : ((Nat.card (Formalism.IndefR.NX.U D.nd) : ℕ) : FractionRing (T.O i)) *
      readT D T i b ((Nat.card (Formalism.IndefR.NX.U D.nd) : ↥D.LL0)⁻¹) = 1 := by
    rw [← map_natCast (readT D T i b), ← map_mul, mul_inv_cancel₀ hne, map_one]
  rw [this, one_smul]

end GlobalTheory.HeightCounting.FormsStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericCharacterProjectorOnTwistFormsFixStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericCharacterProjectorOnTwistForms_fix : ∀ (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool),
    ∀ y ∈ Fm0T D T S In.rho In.chi In.θ i j b, piKop D T S In i j b y = y := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.piKop_fix | exact GlobalTheory.HeightCounting.FormsStep.piKop_fix | (intros; apply GlobalTheory.HeightCounting.FormsStep.piKop_fix <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

end GlobalTheory.HeightCounting.FormsStep
