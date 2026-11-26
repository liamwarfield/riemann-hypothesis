module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CompactUnitaryGroups.IsCompactUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CoefficientGluing.SumFinVal
noncomputable section

set_option linter.unusedSectionVars false

open Matrix Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz.CGlue

section Tens

variable {n : ℕ} {P : Type} [Fintype P] [DecidableEq P]

theorem pm_apply' {M : Type} [AddCommGroup M] [Module ℂ M] (σ : Equiv.Perm P) (f : TV n M P) (I : P → Fin n) :
    pm σ f I = f (I ∘ σ) := rfl

theorem tE_diag_sum (S : Finset P) (f : TV n ℂ P) :
    ∑ i, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i i f = (S.card : ℂ) • f := by
  funext I
  simp [tE, lift, eAt, Finset.sum_apply]
  rw [Finset.sum_comm]
  have key : ∀ p, ∑ c : Fin n, (if I p = c then (LinearMap.proj (Function.update I p c) : TV n ℂ P →ₗ[ℂ] ℂ) else 0) f =
      ∑ c : Fin n, if I p = c then f I else 0 := by
    intro p
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with h
    · subst h; simp
    · simp
  simp [key]

theorem cas_shift (S : Finset P) (s : ℂ) (f : TV n ℂ P) :
    ∑ i, ∑ j, (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i j
        (tE S 0 j i f - if j = i then s • f else 0) - if i = j then s • (tE S 0 j i f - if j = i then s • f else 0) else 0) =
      (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a : Module.End ℂ (TV n ℂ P)) f -
        (2 * s * S.card - n * s ^ 2) • f := by
  have h1 : ∀ i j, (tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) i j (tE S 0 j i f - if j = i then s • f else 0) -
      if i = j then s • (tE S 0 j i f - if j = i then s • f else 0) else 0) =
      tE S 0 i j (tE S 0 j i f) - if i = j then (s • tE S 0 i i f + s • tE S 0 i i f - (s * s) • f) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h; simp only [if_true, map_sub, map_smul, smul_sub, smul_smul]; abel
    · rw [if_neg h, if_neg (Ne.symm h), if_neg h]; simp
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, tE_diag_sum]
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

def colAnti {C : Type} (col : P → C) : Submodule ℂ (TV n ℂ P) where
  carrier := {f | ∀ p p', col p = col p' → p ≠ p' → pm (Equiv.swap p p') f = -f}
  add_mem' := fun {f g} hf hg p p' h1 h2 => by rw [map_add (f := _), hf p p' h1 h2, hg p p' h1 h2, neg_add]
  zero_mem' := fun p p' _ _ => by simp
  smul_mem' := fun c f hf p p' h1 h2 => by rw [map_smul, hf p p' h1 h2, smul_neg]

variable {M : Type} [AddCommGroup M] [Module ℂ M] {d : ℕ}

def tmap (Jh : Matrix (Fin d) (P → Fin n) ℂ) : TV n M P →ₗ[ℂ] M ⊗[ℂ] (Fin d → ℂ) :=
  ∑ I, (TensorProduct.mk ℂ M (Fin d → ℂ)).flip (fun m => Jh m I) ∘ₗ LinearMap.proj I

theorem tmap_apply (Jh : Matrix (Fin d) (P → Fin n) ℂ) (f : TV n M P) :
    tmap Jh f = ∑ I, f I ⊗ₜ (fun m => Jh m I) := by
  simp [tmap]

theorem actT_apply {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (γ : Γ) (f : TV n M P) (I : P → Fin n) :
    actT lab κ ρ γ f I = ∑ J : P → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) • ρ γ (f J) := by
  simp [actT]

theorem tmap_actT {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (Jh : Matrix (Fin d) (P → Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ)
    (h : Jh * Matrix.of (fun I J : P → Fin n => ∏ p, κ (lab p) γ (I p) (J p)) = B * Jh) (f : TV n M P) :
    tmap Jh (actT lab κ ρ γ f) = TensorProduct.map (ρ γ) (Matrix.toLin' B) (tmap Jh f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tmap_apply, tmap_apply, map_sum]
  simp only [actT_apply, TensorProduct.sum_tmul, TensorProduct.smul_tmul, TensorProduct.map_tmul, Matrix.toLin'_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← TensorProduct.tmul_sum]
  congr 1
  funext m
  have := congrFun (congrFun h m) J
  simp only [Matrix.mul_apply, Matrix.of_apply] at this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, ← this]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _

theorem tmap_ne (Jh : Matrix (Fin d) (P → Fin n) ℂ) (f : TV n M P) (lam : M →ₗ[ℂ] ℂ)
    (h : Jh *ᵥ (fun I => lam (f I)) ≠ 0) : tmap Jh f ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg (fun x => TensorProduct.lid ℂ (Fin d → ℂ) (lam.rTensor _ x)) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [tmap_apply, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h1
  funext m
  have h2 := congrFun h1 m
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← h2]
  exact Finset.sum_congr rfl fun I _ => mul_comm _ _

end Tens

theorem sum_fin_val (n : ℕ) : (∑ i : Fin n, ((i : ℕ) : ℝ)) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc, add_mul]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

theorem arith (n : ℕ) (s : ℤ) (ν : Fin n → ℕ) (l : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (h : ∀ i, s - l (w i) = (ν i : ℤ) + (i : ℕ)) :
    (∑ i, (ν i : ℝ) * ((ν i : ℝ) + 2 * (i : ℕ) + 1 - n)) - (2 * s * ∑ i, (ν i : ℝ) - n * (s : ℝ) ^ 2) =
      ∑ k, (((l k : ℝ) + ((n : ℝ) - 1) / 2) ^ 2 - (((n : ℝ) - 1) / 2 - (k : ℕ)) ^ 2) := by
  have hl : ∀ i, (l (w i) : ℝ) = s - ν i - (i : ℕ) := by
    intro i
    have := congrArg (Int.cast : ℤ → ℝ) (h i)
    push_cast at this
    linarith
  have hm := sum_fin_val n
  rw [Finset.sum_sub_distrib, ← Equiv.sum_comp w (fun k => ((l k : ℝ) + ((n : ℝ) - 1) / 2) ^ 2),
    ← Finset.sum_sub_distrib]
  simp only [hl]
  have e : ∀ i : Fin n, ((s : ℝ) - ν i - (i : ℕ) + ((n : ℝ) - 1) / 2) ^ 2 - (((n : ℝ) - 1) / 2 - (i : ℕ)) ^ 2 =
      (ν i : ℝ) * ((ν i : ℝ) + 2 * (i : ℕ) + 1 - n) - 2 * s * ν i + (s : ℝ) ^ 2 + s * (n - 1) - 2 * s * (i : ℕ) := by
    intro i; ring
  rw [Finset.sum_congr rfl fun i _ => e i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  linear_combination (s : ℝ) * hm

theorem sum_shift (n : ℕ) (s : ℤ) (ν : Fin n → ℕ) (l : Fin n → ℤ) (w : Equiv.Perm (Fin n))
    (h : ∀ i, s - l (w i) = (ν i : ℤ) + (i : ℕ)) :
    ∑ k, ((l k : ℝ) + (k : ℕ)) = n * s - ∑ i, (ν i : ℝ) := by
  have hl : ∀ i, (l (w i) : ℝ) = s - ν i - (i : ℕ) := by
    intro i
    have := congrArg (Int.cast : ℤ → ℝ) (h i)
    push_cast at this
    linarith
  rw [Finset.sum_add_distrib, ← Equiv.sum_comp w (fun k => (l k : ℝ))]
  simp only [hl, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end PositivityTheory.Rg.Cz.CGlue
end
end

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct Classical

set_option linter.unusedSimpArgs false

namespace PositivityTheory.Rg.Cz.CGlue

theorem prod_coord_det {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (k : Kinf E a) :
    ∏ τ : E →+* ℂ, coord τ (k.1.det) = 1 := by
  have hne : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ := by
    intro τ h
    have h1 : (InfinitePlace.mk τ).IsReal :=
      InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h)
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h1
  have hu : k.1.det * star k.1.det = 1 := by
    have h2 : k.1 * star k.1 = 1 := Unitary.mul_star_self_of_mem k.2
    have h3 := congrArg Matrix.det h2
    rwa [Matrix.det_mul, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, Matrix.det_one] at h3
  refine Finset.prod_involution (fun τ _ => ComplexEmbedding.conjugate τ) (fun τ _ => ?_) (fun τ _ _ => hne τ)
    (fun τ _ => Finset.mem_univ _) (fun τ _ => by simp [ComplexEmbedding.conjugate])
  rw [J.coord_conjugate, ← J.coord_star, ← map_mul, hu, map_one]

theorem bigM_kap {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Q : Type} [Fintype Q]
    [DecidableEq Q] (lab : Q → (E →+* ℂ)) (s : ℤ) (k : Kinf E a) :
    bigM lab s (Unitary.toUnits k) = Matrix.of (fun I J : Q → Fin a => ∏ p, kap E a (lab p) k (I p) (J p)) := by
  ext I J
  simp only [bigM, Matrix.of_apply, kap, Matrix.map_apply]
  rw [show ((Unitary.toUnits k : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = k.1 from rfl,
    prod_coord_det k, _root_.one_zpow, one_mul]

theorem cx_mul {E : Type} [Field E] {a : ℕ} {A B : Type} [Fintype A] [Fintype B] (τ : E →+* ℂ)
    (φ : Lie E a → Matrix A A ℂ) (ψ : Lie E a → Matrix B B ℂ) (J : Matrix A B ℂ) (h : ∀ X, φ X * J = J * ψ X)
    (i j : Fin a) : cx τ φ i j * J = J * cx τ ψ i j := by
  simp only [cx, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h]

theorem glRel_cx {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (τ : E →+* ℂ) : GlRel (cx τ (lieOp π)) := by
  intro i j k l
  refine LinearMap.ext fun φ => Subtype.ext ?_
  have key : ∀ i j (ψ : π.V), ((cx τ (lieOp π) i j) ψ).1 = Eop τ i j ψ.1 := fun i j ψ => by
    rw [← GlobalTheory.WigCap.res_Eop]; rfl
  have h := LinearMap.congr_fun (glRel_Eop (a := a) τ i j k l) φ.1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, key] at h ⊢
  split_ifs at h ⊢ <;> simpa [key] using h

end PositivityTheory.Rg.Cz.CGlue

namespace PositivityTheory.Rg.Cz

open CGlue

theorem coefGlue_holds : CoefGlue := by
  intro hCB hBR hBC hSum hCo hCV E _ _ _ a π l s hch hKT
  obtain ⟨q, N, lab, col, b, tl, η, hcl, htab, htl, hw, hinv, hanti, halt⟩ := hKT
  obtain ⟨ω₀, hω0, hcoc, hω0a⟩ := hCo E a π.V (fun k => π.op (.cpt k)) q N lab tl η htl hinv halt
  obtain ⟨X, hX⟩ : ∃ X, ω₀ X ≠ 0 := by
    by_contra h; push_neg at h; exact hω0 (AlternatingMap.ext h)
  obtain ⟨I₀, hI⟩ : ∃ I, ω₀ X I ≠ 0 := by
    by_contra h; push_neg at h; exact hX (funext h)
  obtain ⟨lam, hlam⟩ : ∃ lam : π.V →ₗ[ℂ] ℂ, lam (ω₀ X I₀) ≠ 0 := by
    by_contra h; push_neg at h; exact hI ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  set v₀ : TV a ℂ (Fin q) := fun I => lam (ω₀ X I) with hv₀
  have hv₀D : v₀ ∈ colAnti (n := a) col := by
    intro p p' h1 h2
    funext I
    have := congrFun (hω0a p p' (hanti p p' h1 h2) X) I
    simp only [pm_apply'] at this ⊢
    simp [hv₀, this]
  have hv₀0 : v₀ ≠ 0 := fun h => hlam (congrFun h I₀)
  have hDst : ∀ y, ∀ v ∈ colAnti (n := a) col, bigM lab s y *ᵥ v ∈ colAnti (n := a) col := by
    intro y v hv p p' h1 h2
    rw [← (hBC E a (Fin q) lab s).2 y p p' (hcl p p' h1) v, hv p p' h1 h2, Matrix.mulVec_neg]
  have hrep := hBR E a (Fin q) lab s
  obtain ⟨Ξ, J, hJJ, hJD, hJv, hRJ, hJR, hdJ⟩ :=
    hSum E a (Fin q → Fin a) (bigM lab s) (bigD lab s) hrep (colAnti col) hDst v₀ hv₀D hv₀0
  have hdm : ∀ Y, Ξ.dmat Y = Jᴴ * bigD lab s Y * J := by
    intro Y; rw [Matrix.mul_assoc, hdJ, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hcx : ∀ τ i j, cx τ (⇑Ξ.dmat) i j = Jᴴ * cx τ (bigD lab s) i j * J := by
    intro τ i j
    rw [Matrix.mul_assoc, cx_mul τ (bigD lab s) (⇑Ξ.dmat) J hdJ, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  let ω : Herm E a [⋀^Fin N]→ₗ[ℝ] (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
    ((tmap Jᴴ).restrictScalars ℝ).compAlternatingMap ω₀
  refine ⟨Ξ, N, ω, ⟨?_, fun τ => ?_⟩, ?_, ?_⟩
  · intro Y
    rw [hdm, hdm, hrep.dstar]
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · have hBC1 := (hBC E a (Fin q) lab s).1 τ
    obtain ⟨htr, hcas⟩ := hCV a π.V (cx τ (lieOp π)) (fun k => (l τ k : ℂ)) (glRel_cx π τ) (hch τ)
    obtain ⟨w, hw'⟩ := hw τ
    set ν : Fin a → ℕ := fun i => ((fib lab τ).filter fun p => b p = i).card with hν
    have hνeq : ∀ i, s - l τ (w i) = (ν i : ℤ) + (i : ℕ) := by
      intro i; rw [hw' i, hν]; simp only [fib, Finset.filter_filter]
    have hsumν : ∑ i, (ν i : ℝ) = (fib lab τ).card := by
      rw [hν]; exact_mod_cast (Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ (b p))).symm
    have ht : ∑ k, ((l τ k : ℝ) + (k : ℕ)) = a * s - (fib lab τ).card := by
      rw [sum_shift a s ν (l τ) w hνeq, hsumν]
    refine ⟨∑ k, (((l τ k : ℝ) + ((a : ℝ) - 1) / 2) ^ 2 - (((a : ℝ) - 1) / 2 - (k : ℕ)) ^ 2),
      ∑ k, ((l τ k : ℝ) + (k : ℕ)), ?_, ?_, ?_, ?_⟩
    · rw [hcas]; push_cast; rfl
    · rw [htr]; push_cast; rfl
    · have hsumB : ∑ i, cx τ (bigD lab s) i i = (((fib lab τ).card : ℂ) - a * s) • (1 : Matrix (Fin q → Fin a) (Fin q → Fin a) ℂ) := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun f => ?_
        simp only [Matrix.toLin'_apply, Matrix.sum_mulVec, hBC1, Finset.sum_sub_distrib, tE_diag_sum,
          Matrix.smul_mulVec, Matrix.one_mulVec]
        simp only [if_pos rfl, if_true, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [← Nat.cast_smul_eq_nsmul ℂ]
        module
      rw [Finset.sum_congr rfl fun i _ => hcx τ i i, ← Matrix.sum_mul, ← Matrix.mul_sum, hsumB, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, hJJ, Algebra.algebraMap_eq_smul_one, ht]
      push_cast
      ring_nf
    · intro v
      have hfD : J *ᵥ v ∈ colAnti (n := a) col := hJD v
      set Cb : Matrix (Fin q → Fin a) (Fin q → Fin a) ℂ :=
        ∑ i, ∑ j, cx τ (bigD lab s) i j * cx τ (bigD lab s) j i with hCb
      have hCasM : ∑ i, ∑ j, cx τ (⇑Ξ.dmat) i j * cx τ (⇑Ξ.dmat) j i = Jᴴ * Cb * J := by
        rw [hCb]
        simp only [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hcx τ i j, Matrix.mul_assoc, ← cx_mul τ (bigD lab s) (⇑Ξ.dmat) J hdJ j i]
        simp only [Matrix.mul_assoc]
      have hvv : star v ⬝ᵥ v = star (J *ᵥ v) ⬝ᵥ (J *ᵥ v) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
      have hquad : ∀ C : Matrix (Fin q → Fin a) (Fin q → Fin a) ℂ,
          star v ⬝ᵥ ((Jᴴ * C * J) *ᵥ v) = star (J *ᵥ v) ⬝ᵥ (C *ᵥ (J *ᵥ v)) := by
        intro C
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
      have hC : Cb *ᵥ (J *ᵥ v) =
          (∑ i, ∑ j, tE (fib lab τ) (0 : Fin a → Fin a → Module.End ℂ ℂ) i j * tE (fib lab τ) 0 j i :
            Module.End ℂ (TV a ℂ (Fin q))) (J *ᵥ v) -
            (2 * (s : ℂ) * (fib lab τ).card - a * (s : ℂ) ^ 2) • (J *ᵥ v) := by
        rw [← cas_shift, hCb]
        simp only [Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hBC1]
      have hcolS : ∀ p p', col p = col p' → (p ∈ fib lab τ ↔ p' ∈ fib lab τ) := by
        intro p p' h; simp [fib, hcl p p' h]
      have hb := hCB a (Fin q) ℕ col b (fib lab τ) htab hcolS (J *ᵥ v) hfD
      have har := arith a s ν (l τ) w hνeq
      rw [hCasM, hquad, hvv, hC, dotProduct_sub, dotProduct_smul, ← har, hsumν]
      rw [show (2 * (s : ℂ) * (fib lab τ).card - a * (s : ℂ) ^ 2) =
        ((2 * (s : ℝ) * (fib lab τ).card - a * (s : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul, sub_mul]
      linarith [hb]
  · intro k Y
    change tmap Jᴴ (ω₀ fun i => adHerm k (Y i)) = tensorK π Ξ k (tmap Jᴴ (ω₀ Y))
    rw [hcoc k Y]
    refine tmap_actT lab (kap E a) (fun k => π.op (.cpt k)) k Jᴴ _ ?_ (ω₀ Y)
    rw [← bigM_kap lab s k]
    exact hJR _
  · intro h0
    exact tmap_ne Jᴴ (ω₀ X) lam hJv (by simpa [ω] using congrArg (fun f => f X) h0)

end PositivityTheory.Rg.Cz
