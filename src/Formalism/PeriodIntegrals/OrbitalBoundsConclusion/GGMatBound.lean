module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.IrreducibleOfMinimal
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnMinorLeft
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GammaMatrixInverse
open Finset

open scoped ComplexConjugate

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic PI.GGConvScalarW

theorem addChar_inv_eq_conj {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (a : F) :
    (ψ₀ a)⁻¹ = conj (ψ₀ a) := by
  rw [← AddChar.map_neg_eq_inv, AddChar.map_neg_eq_conj]

theorem psiNat_inv {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) :
    psiNat ψ₀ u⁻¹ = conj (psiNat ψ₀ u) := by
  unfold psiNat
  by_cases hu : IsUni k u
  · rw [if_pos (isUni_inv hu), if_pos hu]
    rw [eq_inv_of_mul_eq_one_left (psiU_inv_mul ψ₀ hu)]
    unfold psiU
    exact addChar_inv_eq_conj ψ₀ _
  · have hu' : ¬ IsUni k u⁻¹ := fun h => hu (by simpa using isUni_inv h)
    rw [if_neg hu', if_neg hu, map_zero]

end PI.GGMatBoundW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.MatrixCoefficientEquation
open Finset Matrix

open scoped ComplexConjugate

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

section General

variable {G : Type} [Group G] {X : Type} [MulAction Gᵐᵒᵖ X]

theorem eq_of_smul_eq_of_free (hfree : ∀ (x : Gᵐᵒᵖ) (j : X), x • j = j → x = 1) {a b : Gᵐᵒᵖ} {j : X}
    (h : a • j = b • j) : a = b := by
  have h1 : (b⁻¹ * a) • j = j := by rw [mul_smul, h, inv_smul_smul]
  exact (inv_mul_eq_one.mp (hfree _ _ h1)).symm

theorem exists_smul_comm (i j : X) : (∃ x : Gᵐᵒᵖ, x • j = i) ↔ ∃ x : Gᵐᵒᵖ, x • i = j :=
  ⟨fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [← hx, inv_smul_smul]⟩, fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [← hx, inv_smul_smul]⟩⟩

theorem sum_orbit [Fintype G] (hfree : ∀ (x : Gᵐᵒᵖ) (j : X), x • j = j → x = 1) (d : X → X → G)
    (hd : ∀ i j, (∃ x : Gᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) (f : G → ℂ) (i j : X) :
    (∑ x : G, if MulOpposite.op x • j = i then f x else 0) =
      if ∃ x : Gᵐᵒᵖ, x • j = i then f (d i j) else 0 := by
  by_cases h : ∃ x : Gᵐᵒᵖ, x • j = i
  · rw [if_pos h]
    have hdij := hd i j h
    rw [Finset.sum_eq_single (d i j)]
    · rw [if_pos hdij]
    · intro b _ hb
      rw [if_neg]
      intro hbj
      exact hb (MulOpposite.op_injective (eq_of_smul_eq_of_free hfree (hbj.trans hdij.symm)))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg]
    intro hx
    exact h ⟨_, hx⟩

end General

section Prod

variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

private theorem gam_inv_eq_conj {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ)
    (x : GL (Fin k) F) : gam ψ₀ x⁻¹ = conj (gam ψ₀ x) := by
  unfold gam
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← psiNat_inv]
  congr 1
  group

theorem gamProd_inv (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)) :
    gamProd ψ x⁻¹ = conj (gamProd ψ x) := by
  unfold gamProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.inv_apply, gam_inv_eq_conj]

theorem toMatrix'_totOp_apply (ψ : ∀ v, AddChar (Fq v) ℂ) (X : Type) [Fintype X]
    [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X] (i j : X) :
    LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) i j =
      ∑ x : (∀ v, GL (Fin k) (Fq v)), if MulOpposite.op x • i = j then gamProd ψ x else 0 := by
  rw [LinearMap.toMatrix'_apply]
  simp [totOp, permRep, LinearMap.funLeft, Finset.sum_apply, Pi.single_apply, mul_ite]

end Prod

theorem totally_hermitian_form : TotHerm := by
  intro ι _ Fq _ _ k ψ X _ _
  refine Matrix.IsHermitian.ext fun i j => ?_
  rw [toMatrix'_totOp_apply, toMatrix'_totOp_apply, star_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ fun x => ?_
  have hiff : MulOpposite.op x • j = i ↔ MulOpposite.op x⁻¹ • i = j := by
    rw [MulOpposite.op_inv]
    constructor
    · intro h
      rw [← h, inv_smul_smul]
    · intro h
      rw [← h, smul_inv_smul]
  simp only [Equiv.inv_apply]
  split_ifs with h1 h2 h2
  · rw [gamProd_inv]
    rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · exact star_zero _

theorem matrix_coefficient_equation : MatrixEq := by
  intro ι _ Fq _ _ k ψ X _ _ hfree d hd
  constructor
  · ext i j
    rw [Matrix.of_apply, toMatrix'_totOp_apply, sum_orbit hfree d hd,
      exists_smul_comm (G := ∀ v, GL (Fin k) (Fq v)) i j]
    split_ifs with h
    · have h1 := hd j i h
      have h3 := hd i j ((exists_smul_comm (G := ∀ v, GL (Fin k) (Fq v)) i j).mpr h)
      have hdd : d j i = (d i j)⁻¹ := by
        apply MulOpposite.op_injective
        apply eq_of_smul_eq_of_free hfree (j := i)
        rw [h1, MulOpposite.op_inv]
        exact eq_inv_smul_iff.mpr h3
      rw [hdd, gamProd_inv]
    · rfl
  · ext i j
    rw [Matrix.of_apply, Matrix.transpose_apply, toMatrix'_totOp_apply, sum_orbit hfree d hd]

end PI.GGMatBoundW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.JointEigenvectorExists
noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

theorem gamProd_conj (ψ : ∀ v, AddChar (Fq v) ℂ) (g x : ∀ v, GL (Fin k) (Fq v)) :
    gamProd ψ (g * x * g⁻¹) = gamProd ψ x := by
  unfold gamProd
  refine Finset.prod_congr rfl fun v _ => ?_
  exact PI.GGConvScalarW.gam_conj (ψ v) (g v) (x v)

theorem totOp_comm (ψ : ∀ v, AddChar (Fq v) ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) (g : ∀ v, GL (Fin k) (Fq v)) :
    π g ∘ₗ totOp ψ π = totOp ψ π ∘ₗ π g := by
  unfold totOp
  show π g * (∑ x, gamProd ψ x • π x) = (∑ x, gamProd ψ x • π x) * π g
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ (fun x => ?_)
  simp only [mul_smul_comm, smul_mul_assoc, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply]
  rw [gamProd_conj]
  congr 1
  rw [← map_mul, ← map_mul]
  congr 1
  group

theorem mulSingle_conj (v : ι) (g : ∀ v, GL (Fin k) (Fq v)) (y : GL (Fin k) (Fq v)) :
    g * Pi.mulSingle v y * g⁻¹ = Pi.mulSingle v (g v * y * (g v)⁻¹) := by
  funext w
  by_cases h : w = v
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h]

theorem placeOp_comm (ψ : ∀ v, AddChar (Fq v) ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) (v : ι) (g : ∀ v, GL (Fin k) (Fq v)) :
    π g ∘ₗ placeOp ψ π v = placeOp ψ π v ∘ₗ π g := by
  unfold placeOp
  show π g * (∑ y, gam (ψ v) y • π (Pi.mulSingle v y)) = (∑ y, gam (ψ v) y • π (Pi.mulSingle v y)) * π g
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (MulAut.conj (g v)).toEquiv _ _ (fun y => ?_)
  simp only [mul_smul_comm, smul_mul_assoc, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply]
  rw [PI.GGConvScalarW.gam_conj]
  congr 1
  rw [← map_mul, ← map_mul, ← mulSingle_conj]
  congr 1
  group

theorem placeOp_mem (ψ : ∀ v, AddChar (Fq v) ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V) (v : ι) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ x ∈ W, π g x ∈ W) (x : V) (hx : x ∈ W) : placeOp ψ π v x ∈ W := by
  unfold placeOp
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (hW _ x hx)

theorem joint_eigenvector_exists : JointEig := by
  intro ι _ Fq _ _ k ψ V _ _ _ π w μ hw hμ
  let E : Submodule ℂ V := LinearMap.ker (totOp ψ π - μ • LinearMap.id)
  have memE : ∀ x, x ∈ E ↔ totOp ψ π x = μ • x := by
    intro x
    show x ∈ LinearMap.ker _ ↔ _
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    simp
  have Einv : ∀ g, ∀ x ∈ E, π g x ∈ E := by
    intro g x hx
    rw [memE] at hx ⊢
    have h1 := congrArg (fun e : V →ₗ[ℂ] V => e x) (totOp_comm ψ π g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hx, map_smul]
  have hex : ∃ n, ∃ W : Submodule ℂ V, W ≠ ⊥ ∧ W ≤ E ∧ (∀ g, ∀ x ∈ W, π g x ∈ W) ∧
      Module.finrank ℂ W = n := by
    refine ⟨_, E, ?_, le_rfl, Einv, rfl⟩
    intro h
    apply hw
    have : w ∈ E := (memE w).2 hμ
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  obtain ⟨W, hW, hWE, hWinv, hWn⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ V, W' ≠ ⊥ → W' ≤ W → (∀ g, ∀ x ∈ W', π g x ∈ W') → W' = W := by
    intro W' hW' hle hinv
    have h1 : Nat.find hex ≤ Module.finrank ℂ W' :=
      Nat.find_min' hex ⟨W', hW', hle.trans hWE, hinv, rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨W, hW, hWinv, fun x hx => (memE x).1 (hWE hx), fun v => ?_⟩
  have hmaps : ∀ x ∈ W, placeOp ψ π v x ∈ W := fun x hx => placeOp_mem ψ π v W hWinv x hx
  let A : W →ₗ[ℂ] W := (placeOp ψ π v).restrict hmaps
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨u, hu⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  let W' : Submodule ℂ V := W ⊓ LinearMap.ker (placeOp ψ π v - c • LinearMap.id)
  have memW' : ∀ x, x ∈ W' ↔ x ∈ W ∧ placeOp ψ π v x = c • x := by
    intro x
    simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      LinearMap.smul_apply, LinearMap.id_apply]
  have hu' : (u : V) ∈ W' := by
    rw [memW']
    refine ⟨u.2, ?_⟩
    have h2 := congrArg Subtype.val hu.apply_eq_smul
    exact h2
  have hW'ne : W' ≠ ⊥ := by
    intro h
    rw [h] at hu'
    exact hu.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hu'))
  have hW'inv : ∀ g, ∀ x ∈ W', π g x ∈ W' := by
    intro g x hx
    rw [memW'] at hx ⊢
    refine ⟨hWinv g x hx.1, ?_⟩
    have h1 := congrArg (fun e : V →ₗ[ℂ] V => e x) (placeOp_comm ψ π v g)
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hx.2, map_smul]
  have heq := hmin W' hW'ne inf_le_left hW'inv
  intro x hx
  have hx' : x ∈ W' := heq ▸ hx
  exact ((memW' x).1 hx').2

end PI.GGMatBoundW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GgMatrixBoundOfLitOf
open Finset Matrix

open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

theorem ggMatrixBound_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hC : ConvScalar) (hR : GenericRatio) : GGMatrixBound := by
  intro ι _ Fq _ _ k ψ hψ hq X _ _ hfree d hd
  obtain ⟨hA, hAt⟩ := hM ι Fq k ψ X hfree d hd
  set A := LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) with hAdef
  have hherm : A.IsHermitian := hH ι Fq k ψ X
  have hspec := hS X A _ hherm (fun w μ hw hAw =>
    hE hC hR ι Fq k ψ hψ hq (X → ℂ) (permRep (∀ v, GL (Fin k) (Fq v)) X) w μ hw
      (by rw [← hAw, hAdef, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']))
  rw [hAt, hA]
  exact ⟨hspec.1.transpose, hspec.2⟩

theorem ggMatrixBoundOfLit_of (hM : MatrixEq) (hH : TotHerm) (hE : EigBound) (hS : SpecPSD)
    (hCL : ConvScalarOfLit) (hRB : GenericRatioOfBound) (hCU : CardUni) : GGMatrixBoundOfLit :=
  fun hGG hMB => ggMatrixBound_of hM hH hE hS (hCL hGG) (hRB hMB hCU)

end PI.GGMatBoundW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GamOneReal
open Finset

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

theorem eigBound_of (hP : PlaceBound) (hJ : JointEig) (hF : ProdFormula) : EigBound := by
  intro hC hR ι _ Fq _ _ k ψ hψ hq V _ _ _ π w μ hw he
  obtain ⟨W, hW0, hWinv, hWeig, hv⟩ := hJ ι Fq k ψ V π w μ hw he
  choose μv hμv using hv
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hpl : ∀ v, ∃ c : ℝ, μv v = gam (ψ v) (1 : GL (Fin k) (Fq v)) * (c : ℂ) ∧ 0 ≤ c ∧
      c ≤ 1 + 3 / (Fintype.card (Fq v) : ℝ) := by
    intro v
    refine hP hC hR (Fq v) k (ψ v) (hψ v) (hq v) V
      (π.comp (MonoidHom.mulSingle (fun v => GL (Fin k) (Fq v)) v)) W (μv v) hW0 ?_ ?_
    · intro g y hy; exact hWinv _ y hy
    · intro y hy
      rw [← hμv v y hy]
      simp [repGam, placeOp, LinearMap.sum_apply]
  choose c hc using hpl
  have h1 : totOp ψ π x = (∏ v, μv v) • x := hF ι Fq k ψ V π μv x (fun v => hμv v x hxW)
  have h2 : μ = ∏ v, μv v := by
    have h3 := hWeig x hxW
    rw [h1] at h3
    exact (smul_left_injective ℂ hx0 h3).symm
  set g : ι → ℝ := fun v => (Fintype.card (GL (Fin k) (Fq v)) : ℝ) / (cardU (Fq v) k : ℝ) with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hG1 : gamProd ψ (1 : ∀ v, GL (Fin k) (Fq v)) = ((∏ v, g v : ℝ) : ℂ) := by
    unfold gamProd
    push_cast
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Pi.one_apply, gam_one_real]
  refine ⟨(∏ v, g v) * ∏ v, c v, ?_, ?_, ?_⟩
  · rw [h2]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [(hc v).1, gam_one_real]
  · exact mul_nonneg (Finset.prod_nonneg fun v _ => hg0 v) (Finset.prod_nonneg fun v _ => (hc v).2.1)
  · rw [hG1, Complex.ofReal_re, mul_comm (∏ v, (1 + 3 / (Fintype.card (Fq v) : ℝ)))]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun v _ => (hc v).2.1) (fun v _ => (hc v).2.2))
      (Finset.prod_nonneg fun v _ => hg0 v)

end PI.GGMatBoundW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.ProdFormula
open Finset

noncomputable section

open Classical

namespace PI.GGMatBoundW

open Formalism.L2.SG.GGMirabolic

section Prod

variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

def beta (ψ : ∀ v, AddChar (Fq v) ℂ) (s : Finset ι) (x : ∀ v, GL (Fin k) (Fq v)) : ℂ :=
  if ∀ w, w ∉ s → x w = 1 then ∏ v ∈ s, gam (ψ v) (x v) else 0

theorem beta_insert (ψ : ∀ v, AddChar (Fq v) ℂ) {a : ι} {s : Finset ι} (ha : a ∉ s)
    (z : ∀ v, GL (Fin k) (Fq v)) :
    beta ψ (insert a s) z =
      ∑ y : GL (Fin k) (Fq a), gam (ψ a) y * beta ψ s ((Pi.mulSingle a y)⁻¹ * z) := by
  have hz : ∀ w, ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = if w = a then 1 else z w := by
    intro w
    by_cases hw : w = a
    · subst hw
      simp
    · simp [hw, Pi.mulSingle_eq_of_ne hw]
  rw [Finset.sum_eq_single (z a)]
  · unfold beta
    have hcond : (∀ w, w ∉ insert a s → z w = 1) ↔
        (∀ w, w ∉ s → ((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) w = 1) := by
      constructor
      · intro h w hw
        rw [hz]
        by_cases hwa : w = a
        · rw [if_pos hwa]
        · rw [if_neg hwa]
          exact h w (by simp [hwa, hw])
      · intro h w hw
        simp only [Finset.mem_insert, not_or] at hw
        have := h w hw.2
        rwa [hz, if_neg hw.1] at this
    have hprod : ∏ v ∈ s, gam (ψ v) (((Pi.mulSingle a (z a))⁻¹ * z : ∀ v, GL (Fin k) (Fq v)) v) =
        ∏ v ∈ s, gam (ψ v) (z v) := by
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [hz, if_neg (fun (h : v = a) => ha (h ▸ hv))]
    by_cases h : ∀ w, w ∉ insert a s → z w = 1
    · rw [if_pos h, if_pos (hcond.mp h), hprod, Finset.prod_insert ha]
    · rw [if_neg h, if_neg (fun h' => h (hcond.mpr h')), mul_zero]
  · intro y _ hy
    unfold beta
    rw [if_neg, mul_zero]
    intro h
    apply hy
    have := h a ha
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] at this
    exact inv_mul_eq_one.mp this
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem beta_univ (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)) :
    beta ψ Finset.univ x = gamProd ψ x := by
  unfold beta gamProd
  rw [if_pos (fun w hw => absurd (Finset.mem_univ w) hw)]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem placeOp_apply (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (v : ι) (w : V) : placeOp ψ π v w = ∑ y, gam (ψ v) y • π (Pi.mulSingle v y) w := by
  simp only [placeOp, LinearMap.sum_apply, LinearMap.smul_apply]

theorem totOp_apply (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (w : V) : totOp ψ π w = ∑ x, gamProd ψ x • π x w := by
  simp only [totOp, LinearMap.sum_apply, LinearMap.smul_apply]

theorem sum_beta_empty (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    (w : V) : ∑ x, beta ψ ∅ x • π x w = w := by
  rw [Finset.sum_eq_single 1]
  · unfold beta
    simp
  · intro b _ hb
    unfold beta
    rw [if_neg, zero_smul]
    intro h
    exact hb (funext fun v => h v (by simp))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_beta_insert (ψ : ∀ v, AddChar (Fq v) ℂ) (π : Representation ℂ (∀ v, GL (Fin k) (Fq v)) V)
    {a : ι} {s : Finset ι} (ha : a ∉ s) (w : V) :
    ∑ x, beta ψ (insert a s) x • π x w = placeOp ψ π a (∑ x, beta ψ s x • π x w) := by
  rw [placeOp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [beta_insert ψ ha, Finset.sum_smul, map_sum, map_smul, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Fintype.sum_equiv (Equiv.mulLeft (Pi.mulSingle a y)⁻¹) _ _ fun z => ?_
  simp only [Equiv.coe_mulLeft]
  have hπ : π (Pi.mulSingle a y) (π ((Pi.mulSingle a y)⁻¹ * z) w) = π z w := by
    have h2 := congrArg (fun f => f w) (map_mul π (Pi.mulSingle a y) ((Pi.mulSingle a y)⁻¹ * z))
    simp only [mul_inv_cancel_left] at h2
    exact h2.symm
  rw [hπ, mul_smul]

end Prod

theorem prod_formula' : ProdFormula := by
  intro ι _ Fq _ _ k ψ V _ _ π μ w hμ
  have key : ∀ s : Finset ι, ∑ x, beta ψ s x • π x w = (∏ v ∈ s, μ v) • w := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [sum_beta_empty, Finset.prod_empty, one_smul]
    | @insert a s ha ih =>
      rw [sum_beta_insert ψ π ha w, ih, map_smul, hμ, smul_smul, Finset.prod_insert ha, mul_comm]
  rw [totOp_apply, ← key Finset.univ]
  simp_rw [beta_univ]

end PI.GGMatBoundW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.SpectrumPositiveSemidefinite
open Matrix

open scoped ComplexOrder

noncomputable section

open Classical

namespace PI.GGMatBoundW

theorem spectrum_positive_semidefinite : SpecPSD := by
  intro X _ M c hM hev
  have gen : ∀ (A : Matrix X X ℂ) (hA : A.IsHermitian) (b : ℝ),
      (∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → A *ᵥ w = μ • w → ∃ r : ℝ, μ = r ∧ b ≤ r) →
      ∀ j, b ≤ hA.eigenvalues j := by
    intro A hA b h j
    have hv := hA.mulVec_eigenvectorBasis j
    have hne := hA.eigenvectorBasis.orthonormal.ne_zero j
    have key : ∀ v : X → ℂ, v ≠ 0 → A *ᵥ v = hA.eigenvalues j • v → b ≤ hA.eigenvalues j := by
      intro v hv0 hAv
      obtain ⟨r, hr, hbr⟩ := h v (hA.eigenvalues j : ℂ) hv0 (by rw [hAv]; ext i; simp)
      have hre : hA.eigenvalues j = r := by exact_mod_cast hr
      rw [hre]
      exact hbr
    exact key _ (fun h0 => hne (by ext i; simpa using congrFun h0 i)) hv
  have h1 : ((c : ℂ) • (1 : Matrix X X ℂ)).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  have hN : ((c : ℂ) • (1 : Matrix X X ℂ) - M).IsHermitian := h1.sub hM
  have hNev : ∀ (w : X → ℂ) (μ : ℂ), w ≠ 0 → ((c : ℂ) • (1 : Matrix X X ℂ) - M) *ᵥ w = μ • w →
      ∃ r : ℝ, μ = r ∧ 0 ≤ r := by
    intro w μ hw h
    have hMw : M *ᵥ w = ((c : ℂ) - μ) • w := by
      rw [Matrix.sub_mulVec] at h
      first
        | rw [Matrix.smul_mulVec] at h
        | rw [Matrix.smul_mulVec_assoc] at h
        | simp only [Matrix.smul_mulVec_assoc] at h
      rw [Matrix.one_mulVec] at h
      rw [sub_smul, ← h]
      abel
    obtain ⟨r, hr, _, hrc⟩ := hev w ((c : ℂ) - μ) hw hMw
    refine ⟨c - r, ?_, by linarith⟩
    push_cast
    linear_combination -hr
  constructor
  · refine hM.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen M hM 0 ?_ j
    intro w μ hw h
    obtain ⟨r, hr, h0, _⟩ := hev w μ hw h
    exact ⟨r, hr, h0⟩
  · exact hN.posSemidef_iff_eigenvalues_nonneg.mpr fun j => gen _ hN 0 hNev j

end PI.GGMatBoundW
end
end

theorem gg_matrix_bound : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit :=
  PI.GGMatBoundW.ggMatrixBoundOfLit_of PI.GGMatBoundW.matrix_coefficient_equation PI.GGMatBoundW.totally_hermitian_form
    (PI.GGMatBoundW.eigBound_of PI.GGMatBoundW.local_place_bound PI.GGMatBoundW.joint_eigenvector_exists
      PI.GGMatBoundW.prod_formula')
    PI.GGMatBoundW.spectrum_positive_semidefinite convolution_scalar generic_ratio_bound mirabolic_card_unipotent
