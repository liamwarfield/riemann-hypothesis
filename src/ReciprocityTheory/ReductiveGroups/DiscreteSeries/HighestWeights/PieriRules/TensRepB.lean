module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensRepA
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Gen

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]

def piIn (i : ι) : V →L[ℂ] PiLp 2 (fun _ : ι => V) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : ι => V) i

theorem piIn_apply (i : ι) (v : V) (j : ι) : piIn i v j = Pi.single (M := fun _ : ι => V) i v j := rfl

theorem piIn_same (i : ι) (v : V) : piIn i v i = v :=
  (piIn_apply i v i).trans (Pi.single_eq_same (M := fun _ : ι => V) i v)

theorem piIn_ne {i j : ι} (h : j ≠ i) (v : V) : piIn i v j = 0 :=
  (piIn_apply i v j).trans (Pi.single_eq_of_ne (M := fun _ : ι => V) h v)

def tensL (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) : PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V) :=
  ∑ i, ∑ j, m i j • (piIn i ∘L S ∘L PiLp.proj 2 (fun _ : ι => V) j)

@[simp] theorem tensL_apply (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensL m S x i = ∑ j, m i j • S (x j) := by
  simp only [tensL, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    PiLp.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp only [piIn_same]
  · intro k _ hk
    simp only [piIn_ne (Ne.symm hk), smul_zero, Finset.sum_const_zero]
  · simp

theorem tensL_mul (m m' : Matrix ι ι ℂ) (S S' : V →L[ℂ] V) :
    tensL (m * m') (S * S') = tensL m S * tensL m' S' := by
  refine ContinuousLinearMap.ext fun x => PiLp.ext fun i => ?_
  have hSS : ∀ v : V, (S * S') v = S (S' v) := fun v => rfl
  show tensL (m * m') (S * S') x i = tensL m S (tensL m' S' x) i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [tensL_apply, hSS, Matrix.mul_apply, map_sum, map_smul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem tensL_one : tensL (1 : Matrix ι ι ℂ) (1 : V →L[ℂ] V) = 1 := by
  refine ContinuousLinearMap.ext fun x => PiLp.ext fun i => ?_
  simp [Matrix.one_apply, ite_smul]

theorem tensL_star [CompleteSpace V] (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    star (tensL m S) = tensL (star m) (star S) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, tensL_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, starRingEnd_apply, star_star]
  exact Finset.sum_comm

theorem tensL_mem_unitary [CompleteSpace V] {m : Matrix ι ι ℂ} {S : V →L[ℂ] V}
    (hm : m ∈ unitary (Matrix ι ι ℂ)) (hS : S ∈ unitary (V →L[ℂ] V)) :
    tensL m S ∈ unitary (PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V)) := by
  rw [Unitary.mem_iff] at hm hS ⊢
  rw [tensL_star, ← tensL_mul, ← tensL_mul, hm.1, hm.2, hS.1, hS.2, tensL_one]
  exact ⟨rfl, rfl⟩

theorem continuous_tensL {X : Type*} [TopologicalSpace X] {m : X → Matrix ι ι ℂ} {S : X → V →L[ℂ] V}
    (hm : Continuous m) (hS : Continuous S) : Continuous fun x => tensL (m x) (S x) := by
  simp only [tensL]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (hm.matrix_elem i j).smul (continuous_const.clm_comp (hS.clm_comp continuous_const))

theorem hasDerivAt_tensL {m : ℝ → Matrix ι ι ℂ} {m' : Matrix ι ι ℂ} {S : ℝ → V →L[ℂ] V}
    {S' : V →L[ℂ] V} {t₀ : ℝ} (hm : ∀ i j, HasDerivAt (fun t => m t i j) (m' i j) t₀)
    (hS : HasDerivAt S S' t₀) :
    HasDerivAt (fun t => tensL (m t) (S t)) (tensL m' (S t₀) + tensL (m t₀) S') t₀ := by
  have h : ∀ i j, HasDerivAt
      (fun t => m t i j • (piIn i ∘L S t ∘L PiLp.proj 2 (fun _ : ι => V) j))
      (m t₀ i j • (piIn i ∘L S' ∘L PiLp.proj 2 (fun _ : ι => V) j) +
        m' i j • (piIn i ∘L S t₀ ∘L PiLp.proj 2 (fun _ : ι => V) j)) t₀ := by
    intro i j
    let L : (V →L[ℂ] V) →L[ℂ] (PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V)) :=
      (ContinuousLinearMap.compL ℂ (PiLp 2 (fun _ : ι => V)) V (PiLp 2 (fun _ : ι => V)) (piIn i)).comp
        ((ContinuousLinearMap.compL ℂ (PiLp 2 (fun _ : ι => V)) V V).flip
          (PiLp.proj 2 (fun _ : ι => V) j))
    have hc : HasDerivAt (fun t => L (S t)) (L S') t₀ :=
      (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t₀ hS
    exact (hm i j).smul hc
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => h i j
  refine hs.congr_deriv ?_
  simp only [tensL, Finset.sum_add_distrib]
  exact add_comm _ _

variable {G : Type*} [Monoid G] [CompleteSpace V]

def tensHom (ρ : G →* unitary (Matrix ι ι ℂ)) (σ : G →* unitary (V →L[ℂ] V)) :
    G →* unitary (PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V)) where
  toFun g := ⟨tensL ((ρ g : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) ((σ g : unitary (V →L[ℂ] V)) : V →L[ℂ] V),
    tensL_mem_unitary (ρ g).2 (σ g).2⟩
  map_one' := Subtype.ext (by simp only [map_one, OneMemClass.coe_one, tensL_one])
  map_mul' g h := Subtype.ext (by simp only [map_mul, Submonoid.coe_mul, tensL_mul])

theorem continuous_tensHom [TopologicalSpace G] {ρ : G →* unitary (Matrix ι ι ℂ)}
    {σ : G →* unitary (V →L[ℂ] V)}
    (hρ : Continuous (fun g : G => ((ρ g : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ))) (hσ : Continuous σ) :
    Continuous (tensHom ρ σ) :=
  continuous_induced_rng.2 (continuous_tensL hρ (continuous_subtype_val.comp hσ))

end Gen

section KT

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
  (ρ : KG ε →* unitary (Matrix ι ι ℂ))

def tensOp (k : KG ε) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V) :=
  tensL ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) (T.op k)

theorem tensOp_eq (k : KG ε) :
    tensOp T ρ k = tensL ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) (T.op k) := rfl

@[simp] theorem tensOp_apply (k : KG ε) (x : PiLp 2 (fun _ : ι => T.V)) (i : ι) :
    tensOp T ρ k x i = ∑ j, ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j • T.op k (x j) :=
  tensL_apply _ _ _ _

def tensTau : KG ε →* unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :=
  tensHom ρ T.τ

@[simp] theorem tensTau_coe (k : KG ε) :
    ((tensTau T ρ k : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V))) :
      PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) = tensOp T ρ k := rfl

theorem tensTau_cont (h : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ))) :
    Continuous (tensTau T ρ) :=
  continuous_tensHom h T.cont

end KT

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Lin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensL_add_left (m m' : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (m + m') S = tensL m S + tensL m' S := by
  ext x i
  simp [tensL_apply, add_smul, Finset.sum_add_distrib]

theorem tensL_smul_left (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (c • m) S = c • tensL m S := by
  ext x i
  simp [tensL_apply, mul_smul, Finset.smul_sum]

theorem tensL_add_right (m : Matrix ι ι ℂ) (S S' : V →L[ℂ] V) :
    tensL m (S + S') = tensL m S + tensL m S' := by
  ext x i
  simp [tensL_apply, smul_add, Finset.sum_add_distrib]

theorem tensL_smul_right (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL m (c • S) = c • tensL m S := by
  ext x i
  simp [tensL_apply, Finset.smul_sum, smul_comm c]

end Lin

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]

def tensD (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) where
  toFun X := tensL (dρ X) 1 + tensL 1 (T.dτ X)
  map_add' X Y := by
    simp only [map_add (f := _), tensL_add_left, tensL_add_right]
    abel
  map_smul' c X := by
    simp only [map_smul, tensL_smul_left, tensL_smul_right, RingHom.id_apply, smul_add]

theorem tensD_apply (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (x : PiLp 2 (fun _ : ι => T.V)) (i : ι) :
    tensD T dρ X x i = T.dτ X (x i) + ∑ j, dρ X i j • x j := by
  simp [tensD, Matrix.one_apply, add_comm]

theorem tens_curve_zero {X : Matrix (Fin n) (Fin n) ℂ} (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ 0 = 1 := by
  apply onep_KG_ext
  rw [hγ]
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
  simp

theorem tensD_hasDeriv (ρ : KG ε →* unitary (Matrix ι ι ℂ))
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X))
    (hd : ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
      (dρ X i j) 0) :
    HasDerivAt (fun t : ℝ => ((tensTau T ρ (γ t) : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ]
      PiLp 2 (fun _ : ι => T.V))) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
      (tensD T dρ X) 0 := by
  have h0 := tens_curve_zero γ hγ
  have hD := hasDerivAt_tensL (V := T.V) hd (T.hasDeriv X hX γ hγ)
  simp only [tensTau_coe, tensOp_eq]
  convert hD using 1
  simp [tensD, h0]

theorem tensD_units (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (a b : Fin n) :
    ((tensD T dρ (Matrix.single a b 1) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :
      Module.End ℂ (PiLp 2 (fun _ : ι => T.V))) =
      tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b := by
  refine LinearMap.ext fun x => PiLp.ext fun i => ?_
  simp [tensAct, tensD_apply, kunits]


include T in
def tensKRep (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) : KRep ε where
  V := PiLp 2 (fun _ : ι => T.V)
  τ := tensTau T ρ
  cont := tensTau_cont T ρ hc
  dτ := tensD T dρ
  hasDeriv X hX γ hγ := tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ)

theorem tensKRep_units (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) :
    (tensKRep T ρ dρ hc hd).units = tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) :=
  funext fun a => funext fun b => tensD_units T dρ a b

theorem tensRep : TensRepStatement := by
  intro n ε Λ T ι _ _ ρ dρ hc hd
  exact ⟨tensTau T ρ, tensD T dρ, tensTau_cont T ρ hc,
    fun X hX γ hγ => tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ), fun a b => tensD_units T dρ a b⟩

end ReciprocityTheory.ChartRestriction.DS.HW
