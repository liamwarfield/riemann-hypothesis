module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MonicNormLtOne

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate

namespace Formalism.L2.Pj.FJ

section Core

variable {r ρ : ℕ}

def cM {m n : Type} (A : Matrix m n ℂ) : Matrix m n ℂ := A.map (starRingEnd ℂ)

theorem cM_cM {m n : Type} (A : Matrix m n ℂ) : cM (cM A) = A := by
  ext i j
  simp [cM]

theorem cM_mul {m n o : Type} [Fintype n] (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    cM (A * B) = cM A * cM B := by
  simp only [cM]
  exact Matrix.map_mul

theorem cM_transpose {m n : Type} (A : Matrix m n ℂ) : cM Aᵀ = (cM A)ᵀ := by
  simp only [cM]
  exact Matrix.transpose_map

theorem cM_add {m n : Type} (A B : Matrix m n ℂ) : cM (A + B) = cM A + cM B := by
  ext i j
  simp [cM]

theorem cM_one : cM (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [cM]
  · simp [cM, Matrix.one_apply, h]

theorem unitary_core (g : Matrix (Fin r) (Fin r) ℂ) (F : Matrix (Fin r) (Fin ρ) ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) ℂ) (hg : (cM g)ᵀ = g) (hiso : Fᵀ * g * cM F = 0)
    (hsk : cM β = -βᵀ) :
    (1 + F * β * (g * cM F)ᵀ)ᵀ * g * cM (1 + F * β * (g * cM F)ᵀ) = g := by
  have hg' : cM g = gᵀ := by
    have := congrArg Matrix.transpose hg
    simpa using this
  have key : ∀ X : Matrix (Fin ρ) (Fin r) ℂ, Fᵀ * (g * (cM F * X)) = 0 := by
    intro X
    rw [← Matrix.mul_assoc g, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hiso, Matrix.zero_mul]
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    cM_add, cM_one, cM_mul, cM_transpose, cM_cM, hg', hsk]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.mul_neg, Matrix.neg_mul, key, neg_zero, Matrix.mul_zero, add_zero, neg_neg]
  abel

theorem det_ne_core (g : Matrix (Fin r) (Fin r) ℂ) (F : Matrix (Fin r) (Fin ρ) ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) ℂ) (hiso : Fᵀ * g * cM F = 0) :
    (1 + F * β * (g * cM F)ᵀ).det ≠ 0 := by
  have hT : (g * cM F)ᵀ * F = 0 := by
    have := congrArg Matrix.transpose hiso
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  generalize (g * cM F)ᵀ = H at hT ⊢
  have key : ∀ X : Matrix (Fin ρ) (Fin r) ℂ, H * (F * X) = 0 := by
    intro X
    rw [← Matrix.mul_assoc, hT, Matrix.zero_mul]
  have hinv : (1 + F * β * H) * (1 - F * β * H) = 1 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, Matrix.mul_assoc, key, Matrix.mul_zero, sub_zero]
    first | abel | skip
  intro h0
  have := congrArg Matrix.det hinv
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end Core

section FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem emb_cc' (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by unfold cc; exact NumberField.IsCMField.complexEmbedding_complexConj E τ x

def Fm (τ : E →+* ℂ) (e : Fin ρ → Fin r → E) : Matrix (Fin r) (Fin ρ) ℂ :=
  Matrix.of fun k a => τ (e a k)

theorem zMatC_eq (X : Data E r) (e : Fin ρ → Fin r → E) (τ : E →+* ℂ) (β : Matrix (Fin ρ) (Fin ρ) ℂ) :
    zMatC X e τ β = 1 + Fm τ e * β * (X.Gm.map τ * cM (Fm τ e))ᵀ := by
  unfold zMatC
  ext k l
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply, Fm, cM,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem gram_eq (X : Data E r) (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm A = Aᵀ * X.Gm.map τ * cM A := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, cM, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem herm_g (X : Data E r) (τ : E →+* ℂ) : (cM (X.Gm.map τ))ᵀ = X.Gm.map τ := by
  ext i j
  simp only [Matrix.transpose_apply, cM, Matrix.map_apply]
  rw [← emb_cc', X.4 j i]

theorem iso_F (X : Data E r) (cu : CuspFD X ρ) (τ : E →+* ℂ) :
    (Fm τ cu.e)ᵀ * X.Gm.map τ * cM (Fm τ cu.e) = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fm, cM, Matrix.of_apply, Matrix.map_apply,
    Matrix.zero_apply, Finset.sum_mul]
  have h := congrArg τ (cu.3 a b)
  unfold ReciprocityTheory.ChartRestriction.G.FD.herm at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_zero, emb_cc'] at h
  rw [Finset.sum_comm]
  exact h

theorem skew_beta (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k)) (τ : E →+* ℂ)
    (t : Fin (nZ X ρ) → ℝ) :
    cM (∑ k, (t k : ℂ) • (zBas X cu k).map τ) = -(∑ k, (t k : ℂ) • (zBas X cu k).map τ)ᵀ := by
  have h' := hb
  unfold IsSkew at h'
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cM, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal, ← emb_cc', h', map_neg, mul_neg, Finset.sum_neg_distrib]

theorem zBas_skew (X : Data E r) (cu : CuspFD X ρ) (h : ∃ bs, IsZBasis X cu bs) (k : Fin (nZ X ρ)) :
    IsSkew (zBas X cu k) := by
  have hs : LinearIndependent ℤ (zBas X cu) ∧
      ∀ β, β ∈ zGam X cu ↔ β ∈ Submodule.span ℤ (Set.range (zBas X cu)) := Classical.epsilon_spec h
  have hm : zBas X cu k ∈ zGam X cu := (hs.2 _).2 (Submodule.subset_span ⟨k, rfl⟩)
  exact hm.1

theorem zAct_mem_dom (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k))
    (t : Fin (nZ X ρ) → ℝ) (x : Frame X.Ψ r) (hx : x ∈ X.dom) : zAct X cu t x ∈ X.dom := by
  unfold zAct ReciprocityTheory.ChartRestriction.G.FD.Data.dom at *
  unfold GG at *
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  unfold dmin mat at *
  beta_reduce
  set M := zMatC X cu.e (τ : E →+* ℂ) (∑ k, ((t k : ℝ) : ℂ) • (zBas X cu k).map (τ : E →+* ℂ)) with hMdef
  have hU : Mᵀ * X.Gm.map (τ : E →+* ℂ) * cM M = X.Gm.map (τ : E →+* ℂ) := by
    rw [hMdef, zMatC_eq]
    exact unitary_core _ _ _ (herm_g X _) (iso_F X cu _) (skew_beta X cu hb _ t)
  have hD : M.det ≠ 0 := by
    rw [hMdef, zMatC_eq]
    exact det_ne_core _ _ _ (iso_F X cu _)
  have hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ,
      Mᵀ * (X.Gm.map (τ : E →+* ℂ) * (cM M * Y)) = X.Gm.map (τ : E →+* ℂ) * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  have hG : ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (M * of (x τ)) =
      ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (of (x τ)) := by
    simp only [gram_eq, Matrix.transpose_mul, cM_mul, Matrix.mul_assoc, hU']
  refine ⟨?_, fun i => ?_⟩
  · show (M * of (x τ)).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hD hdet
  · have := hpos i
    rw [← hG] at this
    exact this

theorem orbDom_of_latZ {Comp : Type} (X : Comp → Data E r) (h : LatZ X ρ) : OrbDom X ρ := by
  intro cu t x hx
  exact zAct_mem_dom (X cu.1) cu.2 (fun k => zBas_skew _ _ (h cu) k) t x hx

theorem rdOrbInt_of_latZ {Comp K : Type} [Field K] (σ : K →+* ℂ) {C : Type} [AddCommGroup C]
    [Module K C] (X : Comp → Data E r) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ))
    (hc : ∀ f c, ContinuousOn (rd f c) (X c).dom) (h : LatZ X ρ) : RdOrbInt σ X ρ rd :=
  rdOrbInt_of σ X rd hc (orbDom_of_latZ X h)

end FD

end Formalism.L2.Pj.FJ
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

abbrev FDSec (X : Comp → Data E r) : Type := ∀ c, Frame (X c).Ψ r → ℂ

abbrev FPt (X : Comp → Data E r) : Type := Σ c, ((X c).dom : Set (Frame (X c).Ψ r))

def IsHolCusp (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : Prop :=
  ∀ c, P c ∈ (X c).SS (la c)

def supE (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ENNReal :=
  ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)

def supN (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ℝ := (supE X la P).toReal

theorem pnorm_fac_nonneg (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    0 ≤ ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

theorem pnorm_smul (X : Data E r) (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
  simp only [Data.pnorm, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

def holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) : Submodule ℂ (FDSec X) :=
  Submodule.span ℂ {P | IsHolCusp X la P}

theorem holCusp_mem_holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X}
    (h : IsHolCusp X la P) : P ∈ holSub X la :=
  Submodule.subset_span h

end Formalism.L2.PjFree
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace Formalism.L2.Pj.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

def trBE (n : ℕ) : LinearMap.BilinForm ℚ (Fin n → E) :=
  LinearMap.mk₂ ℚ (fun l x => Algebra.trace ℚ E (∑ i, l i * x i))
    (fun l₁ l₂ x => by
      rw [← map_add (f := _)]; congr 1; simp [add_mul, Finset.sum_add_distrib])
    (fun c l x => by
      rw [← map_smul]; congr 1; simp [Finset.smul_sum])
    (fun l x₁ x₂ => by
      rw [← map_add (f := _)]; congr 1; simp [mul_add, Finset.sum_add_distrib])
    (fun c l x => by
      rw [← map_smul]; congr 1; simp [Finset.smul_sum])

theorem trBE_apply {n : ℕ} (l x : Fin n → E) :
    trBE n l x = Algebra.trace ℚ E (∑ i, l i * x i) := rfl

theorem trBE_symm (n : ℕ) : (trBE (E := E) n).IsSymm :=
  ⟨fun l x => by rw [trBE_apply, trBE_apply]; simp only [mul_comm]⟩

theorem trBE_sepLeft (n : ℕ) : LinearMap.SeparatingLeft (trBE (E := E) n) := by
  intro l hl
  funext i
  refine (traceForm_nondegenerate ℚ E).1 (l i) (fun y => ?_)
  have h := hl (Pi.single i y)
  rw [trBE_apply] at h
  simpa [Pi.single_apply, Algebra.traceForm_apply] using h

theorem trBE_nondeg (n : ℕ) : (trBE (E := E) n).Nondegenerate :=
  ⟨trBE_sepLeft n, fun x hx => trBE_sepLeft n x fun l => by rw [(trBE_symm n).eq]; exact hx l⟩

theorem dualZE_eq {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) :
    dualZE Xs = ((trBE n).dualSubmodule (Xs.restrictScalars ℤ) : Set (Fin n → E)) := by
  ext l
  simp only [dualZE, Set.mem_ofPred_eq, SetLike.mem_coe,
    LinearMap.BilinForm.mem_dualSubmodule, Submodule.restrictScalars_mem, Submodule.mem_one, trBE_apply,
    Set.mem_range, algebraMap_int_eq, eq_intCast]

def dualZSubE {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := dualZE Xs
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨u, hu⟩ := ha x hx
    obtain ⟨v, hv⟩ := hb x hx
    have h : ∑ i, (a + b) i * x i = ∑ i, a i * x i + ∑ i, b i * x i := by
      simp [add_mul, Finset.sum_add_distrib]
    exact ⟨u + v, by rw [h, map_add (f := _), ← hu, ← hv, Int.cast_add]⟩
  smul_mem' := by
    intro c a ha x hx
    obtain ⟨u, hu⟩ := ha (c • x) (Xs.smul_mem c hx)
    have h : ∑ i, (c • a) i * x i = ∑ i, a i * (c • x) i := by
      simp only [Pi.smul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def]; ring
    exact ⟨u, by rw [h]; exact hu⟩

theorem xcFD_coe (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    (XcFD 𝔄 cu : Set (Fin ρ → E)) = dualZE (crdI 𝔄 cu) := by
  have h : XcFD 𝔄 cu = dualZSubE (crdI 𝔄 cu) := Submodule.span_eq (dualZSubE (crdI 𝔄 cu))
  rw [h]; rfl

theorem exists_crdMap {X : Data E r} (cu : CuspFD X ρ) :
    ∃ Ψ : (Fin r → E) →ₗ[E] (Fin ρ → E), ∀ v : Fin ρ → E, Ψ (∑ i, v i • cu.e i) = v := by
  let b := Module.Basis.span cu.ind
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (Submodule.span E (Set.range cu.e)).subtype (Submodule.ker_subtype _)
  refine ⟨b.equivFun.toLinearMap.comp g, fun v => ?_⟩
  have hmem : ∑ i, v i • cu.e i ∈ Submodule.span E (Set.range cu.e) :=
    sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hgv : g (∑ i, v i • cu.e i) = ⟨_, hmem⟩ := by
    have := LinearMap.congr_fun hg ⟨_, hmem⟩
    simpa using this
  have hb : (⟨_, hmem⟩ : Submodule.span E (Set.range cu.e)) = b.equivFun.symm v := by
    rw [Module.Basis.equivFun_symm_apply]
    ext
    simp [b, Module.Basis.span_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hgv, hb, LinearEquiv.apply_symm_apply]

theorem crdI_fg (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    (crdI 𝔄 cu).FG := by
  obtain ⟨Ψ, hΨ⟩ := exists_crdMap cu
  obtain ⟨d, hd, hdA⟩ := 𝔄.isFractional
  have hI : cu.I.FG := Submodule.FG.of_le X.Λ_fg inf_le_left
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hd
      (IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero]))
  set Ψ' : (Fin r → E) →ₗ[E] (Fin ρ → E) := (algebraMap (𝓞 E) E d)⁻¹ • Ψ
  refine Submodule.FG.of_le (hI.map (Ψ'.restrictScalars (𝓞 E))) ?_
  rw [crdI, Submodule.span_le]
  rintro v ⟨a, ha, x, hx, hax⟩
  obtain ⟨o, ho⟩ := hdA a ha
  refine ⟨o • x, cu.I.smul_mem o hx, ?_⟩
  show Ψ' (o • x) = v
  have hcoef : (algebraMap (𝓞 E) E d)⁻¹ * algebraMap (𝓞 E) E o = a := by
    rw [ho, Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
  rw [← hΨ v, ← hax]
  show ((algebraMap (𝓞 E) E d)⁻¹ • Ψ) (o • x) = Ψ (a • x)
  rw [LinearMap.smul_apply, ← algebraMap_smul E o x, map_smul, smul_smul, hcoef, map_smul]

theorem span_rat_smul_mem {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) (e : E)
    {w : Fin n → E} (hw : w ∈ Submodule.span ℚ (Xs : Set (Fin n → E))) :
    e • w ∈ Submodule.span ℚ (Xs : Set (Fin n → E)) := by
  have halg : IsAlgebraic ℤ e := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ e)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  set o : 𝓞 E := ⟨m • e, hint⟩
  have hmE : (m : E) ≠ 0 := Int.cast_ne_zero.2 hm
  have key : ∀ x ∈ Xs, e • x ∈ Submodule.span ℚ (Xs : Set (Fin n → E)) := by
    intro x hx
    have hox : o • x ∈ Xs := Xs.smul_mem _ hx
    have h1 : o • x = ((m : E) * e) • x := by
      rw [← algebraMap_smul E o x]
      congr 1
      simp [o, zsmul_eq_mul]
    have h2 : e • x = ((m : ℚ)⁻¹) • (o • x) := by
      rw [h1]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Rat.smul_def, Rat.cast_inv, Rat.cast_intCast]
      field_simp
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hox)
  induction hw using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem exists_smul_mem (X : Data E r) (w : Fin r → E) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • w ∈ X.Λ := by
  first | exact UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem .. | (apply UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› ‹_› r X w | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› ‹_› r X | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› ‹_› r | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› ‹_› | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E ‹_› | exact @UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem E

theorem crdI_span (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h𝔄 : 𝔄 ≠ 0) {X : Data E r}
    (cu : CuspFD X ρ) : Submodule.span ℚ (crdI 𝔄 cu : Set (Fin ρ → E)) = ⊤ := by
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ (𝔄 : Submodule (𝓞 E) E), a ≠ 0 := by
    by_contra hne
    push Not at hne
    apply h𝔄
    ext x
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨fun hx => hne x hx, fun hx => hx ▸ (𝔄 : Submodule (𝓞 E) E).zero_mem⟩
  classical
  rw [eq_top_iff]
  intro w _
  rw [pi_eq_sum_univ w]
  refine sum_mem fun i _ => span_rat_smul_mem _ (w i) ?_
  obtain ⟨c, hc, hcI⟩ := exists_smul_mem X (cu.e i)
  set cE : E := algebraMap (𝓞 E) E c
  have hcE : cE ≠ 0 := by
    intro h
    exact hc (IsFractionRing.injective (𝓞 E) E (by rw [map_zero]; exact h))
  have hx : c • cu.e i ∈ cu.I :=
    ⟨hcI, Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩ :
      cu.e i ∈ (Submodule.span E (Set.range cu.e)).restrictScalars (𝓞 E))⟩
  have hv : (Pi.single i (a * cE) : Fin ρ → E) ∈ crdI 𝔄 cu := by
    refine Submodule.subset_span ⟨a, ha, c • cu.e i, hx, ?_⟩
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    rw [← algebraMap_smul E c, smul_smul]
    simp [cE]
  have hsp := span_rat_smul_mem _ (a * cE)⁻¹ (Submodule.subset_span hv)
  convert hsp using 1
  funext j
  by_cases h : i = j
  · subst h; simp; field_simp
  · simp [h, Ne.symm h]

theorem crdI_lat (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h𝔄 : 𝔄 ≠ 0) {X : Data E r}
    (cu : CuspFD X ρ) : Submodule.IsLattice ℚ ((crdI 𝔄 cu).restrictScalars ℤ) :=
  Submodule.IsLattice.of_fg ℚ ((crdI_fg 𝔄 cu).restrictScalars)

theorem exists_basis (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h𝔄 : 𝔄 ≠ 0) {X : Data E r}
    (cu : CuspFD X ρ) : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℚ (Fin ρ → E)),
      Submodule.span ℤ (Set.range b) = (crdI 𝔄 cu).restrictScalars ℤ := by
  classical
  set X0 := (crdI 𝔄 cu).restrictScalars ℤ
  letI : Submodule.IsFullLattice ℚ X0 := {
    toIsLattice := crdI_lat 𝔄 h𝔄 cu
    span_eq_top := by rw [Submodule.coe_restrictScalars]; exact crdI_span 𝔄 h𝔄 cu }
  letI : Module.Finite ℤ X0 := Submodule.IsLattice.finite ℚ X0
  letI : Module.Free ℤ X0 := Submodule.IsLattice.free ℚ X0
  let b := Module.Free.chooseBasis ℤ X0
  refine ⟨_, inferInstance, b.extendOfIsFullLattice ℚ, ?_⟩
  have hr : Set.range (b.extendOfIsFullLattice ℚ) = X0.subtype '' Set.range b := by
    ext v
    simp [Module.Basis.extendOfIsFullLattice_apply]
  rw [hr, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

theorem xcFD_restrict (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    (XcFD 𝔄 cu).restrictScalars ℤ = (trBE ρ).dualSubmodule ((crdI 𝔄 cu).restrictScalars ℤ) := by
  apply SetLike.coe_injective
  rw [Submodule.coe_restrictScalars, xcFD_coe, dualZE_eq]

theorem xcFD_lat (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h𝔄 : 𝔄 ≠ 0) {X : Data E r}
    (cu : CuspFD X ρ) : Submodule.IsLattice E (XcFD 𝔄 cu) := by
  classical
  obtain ⟨ι, _, b, hb⟩ := exists_basis 𝔄 h𝔄 cu
  have hX : (XcFD 𝔄 cu).restrictScalars ℤ =
      Submodule.span ℤ (Set.range ((trBE ρ).dualBasis (trBE_nondeg ρ) b)) := by
    rw [xcFD_restrict, ← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis _ (trBE_nondeg ρ) b]
  refine ⟨?_, ?_⟩
  · rw [← Submodule.FG.restrictScalars_iff (R := ℤ), hX]
    exact Submodule.fg_span (Set.finite_range _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem xcLatF {Comp : Type} (X : Comp → Data E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (h𝔄 : 𝔄 ≠ 0) : XcLatF X 𝔄 ρ :=
  fun cu => xcFD_lat 𝔄 h𝔄 cu.2

end Formalism.L2.Pj.FJ
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.HeckeStabSet
noncomputable section

namespace Formalism.L2.Pj

section Hecke

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable (hkIdx : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], pts Ω → Type)
variable (quotR : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω), hkIdx Ω y → pts Ω → Prop)

def hkTerm (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) (H : hkIdx Ω y) : Ω :=
  open Classical in
  if h : ∃ z : pts Ω, quotR Ω y H z then evalAt pts mapR f h.choose else 0

def hkVal (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) : Ω :=
  ∑ᶠ H : hkIdx Ω y, hkTerm pts mapR hkIdx quotR f y H

def HkFin : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω), Finite (hkIdx Ω y)

theorem hkTerm_add (f g : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω)
    (H : hkIdx Ω y) :
    hkTerm pts mapR hkIdx quotR (f + g) y H = hkTerm pts mapR hkIdx quotR f y H + hkTerm pts mapR hkIdx quotR g y H := by
  unfold hkTerm
  split_ifs with h
  · exact evalAt_add _ _ _ _ _
  · exact (add_zero 0).symm

theorem hkTerm_smul (c : K) (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω)
    (H : hkIdx Ω y) :
    hkTerm pts mapR hkIdx quotR (c • f) y H = algebraMap K Ω c * hkTerm pts mapR hkIdx quotR f y H := by
  unfold hkTerm
  split_ifs with h
  · exact evalAt_smul _ _ _ _ _
  · exact (mul_zero _).symm

theorem hkVal_add (hF : HkFin pts hkIdx) (f g : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (y : pts Ω) :
    hkVal pts mapR hkIdx quotR (f + g) y = hkVal pts mapR hkIdx quotR f y + hkVal pts mapR hkIdx quotR g y := by
  haveI := hF Ω y
  unfold hkVal
  simp_rw [hkTerm_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

theorem hkVal_smul (c : K) (f : Rules pts) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) :
    hkVal pts mapR hkIdx quotR (c • f) y = algebraMap K Ω c * hkVal pts mapR hkIdx quotR f y := by
  unfold hkVal
  simp_rw [hkTerm_smul]
  exact (mul_finsum (fun H => hkTerm pts mapR hkIdx quotR f y H) (algebraMap K Ω c)).symm

def HkRel (c : K) (f g : Rules pts) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω),
    evalAt pts mapR g y = algebraMap K Ω c * hkVal pts mapR hkIdx quotR f y

def HkTotal : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) (H : hkIdx Ω y), ∃ z, quotR Ω y H z

def HkFun : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω) (H : hkIdx Ω y) (z z' : pts Ω),
    quotR Ω y H z → quotR Ω y H z' → mapR (AlgHom.id K Ω) z z'

def PtsDetect [Fintype ι] (e : ι → ℕ) : Prop :=
  ∀ g ∈ secW pts mapR borR e, (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω),
    evalAt pts mapR g y = 0) → g = 0

def HkEx [Fintype ι] (e : ι → ℕ) (c : K) : Prop :=
  ∀ f ∈ secW pts mapR borR e, ∃ g ∈ secW pts mapR borR e, HkRel pts mapR hkIdx quotR c f g

variable {pts mapR borR hkIdx quotR}

theorem hkRel_unique [Fintype ι] {e : ι → ℕ} (hD : PtsDetect pts mapR borR e) {c : K} {f g g' : Rules pts}
    (hg : g ∈ secW pts mapR borR e) (hg' : g' ∈ secW pts mapR borR e)
    (h : HkRel pts mapR hkIdx quotR c f g) (h' : HkRel pts mapR hkIdx quotR c f g') : g = g' := by
  have hz : g - g' = 0 := by
    refine hD _ (Submodule.sub_mem _ hg hg') ?_
    intro Ω _ _ _ y
    rw [sub_eq_add_neg, ← neg_one_smul K g', evalAt_add, evalAt_smul, h Ω y, h' Ω y]
    simp
  exact sub_eq_zero.1 hz

theorem hkRel_add (hF : HkFin pts hkIdx) {c : K} {f f' g g' : Rules pts} (h : HkRel pts mapR hkIdx quotR c f g)
    (h' : HkRel pts mapR hkIdx quotR c f' g') : HkRel pts mapR hkIdx quotR c (f + f') (g + g') := by
  intro Ω _ _ _ y
  rw [evalAt_add, h Ω y, h' Ω y, hkVal_add _ _ _ _ hF, mul_add]

theorem hkRel_smul {c : K} (a : K) {f g : Rules pts} (h : HkRel pts mapR hkIdx quotR c f g) :
    HkRel pts mapR hkIdx quotR c (a • f) (a • g) := by
  intro Ω _ _ _ y
  rw [evalAt_smul, h Ω y, hkVal_smul, mul_left_comm]

def hkOp [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) : secW pts mapR borR e →ₗ[K] secW pts mapR borR e where
  toFun f := ⟨(hE f.1 f.2).choose, (hE f.1 f.2).choose_spec.1⟩
  map_add' f f' := by
    apply Subtype.ext
    exact hkRel_unique hD (hE _ (f + f').2).choose_spec.1
      (Submodule.add_mem _ (hE f.1 f.2).choose_spec.1 (hE f'.1 f'.2).choose_spec.1)
      (hE _ (f + f').2).choose_spec.2 (hkRel_add hF (hE f.1 f.2).choose_spec.2 (hE f'.1 f'.2).choose_spec.2)
  map_smul' a f := by
    apply Subtype.ext
    exact hkRel_unique hD (hE _ (a • f).2).choose_spec.1
      (Submodule.smul_mem _ a (hE f.1 f.2).choose_spec.1)
      (hE _ (a • f).2).choose_spec.2 (hkRel_smul a (hE f.1 f.2).choose_spec.2)

theorem hkOp_spec [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) (f : secW pts mapR borR e) :
    HkRel pts mapR hkIdx quotR c f (hkOp hE hD hF f) := (hE f.1 f.2).choose_spec.2

def HeckeStabW [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) (W : Submodule K (secW pts mapR borR e)) : Prop :=
  ∀ f ∈ W, hkOp hE hD hF f ∈ W

end Hecke

end Formalism.L2.Pj
end
end
