module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceFormIndependence

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def frameBasisRadius (r p0 f : ℕ) (d laStar ρ : ℝ) : ℝ :=
  (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (laStar / Real.sqrt f)) ρ) ^ (2 * p0 + 1)

def frameRadius (w : ℝ) (r : ℕ) : ℝ := 1 / (10 * Real.sqrt (w * r))

def LamBasis {r : ℕ} (X : DataX E r) (La : ℝ) (x : Frame X.Ψ r) (lam : Fin r → Fin r → E) : Prop :=
  (∀ j, lam j ∈ X.L') ∧ LinearIndependent E lam ∧
  (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
  (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
  (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
  (∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2) ∧
  ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) =
    Submodule.span ℂ (Set.range fun a : Fin X.p0 => Data.emb τ.1 (lam (Fin.castLE X.p0_le a)))

def LatticeBoundAtMaximum : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (z0 x0 : Frame X.Ψ r) (laStar ρ : ℝ),
    z0 ∈ X.dom → x0 ∈ X.dom → X.IsOrtho x0 → X.SameFlag z0 x0 → 0 < laStar → laStar ≤ 1 → 0 < ρ → ρ ≤ 1 →
    (∀ v ∈ X.L', v ≠ 0 → laStar ^ 2 ≤ ∑ τ, X.maj z0 τ (Data.emb τ.1 v)) →
    ∃ (lam : Fin r → Fin r → E) (Z : X.Coord), X.zN Z ≤ ρ / 3 ∧
      LamBasis X (frameBasisRadius r X.p0 (fdeg E) (dE E) laStar ρ) (X.xZ x0 Z) lam

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

section Mat

variable {n : ℕ}

lemma sub_mul_sub {i : ℕ} (h : i ≤ n) (M N : Matrix (Fin n) (Fin n) ℂ)
    (hz : ∀ (a c : Fin i) (k : Fin n), i ≤ (k : ℕ) → M (Fin.castLE h a) k * N k (Fin.castLE h c) = 0) :
    (M * N).submatrix (Fin.castLE h) (Fin.castLE h) =
      M.submatrix (Fin.castLE h) (Fin.castLE h) * N.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_) (fun k => rfl)
  apply hz a c k
  by_contra hlt
  exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩

lemma upper_lt {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) {a k : Fin n} (h : a < k) :
    N k a = 0 := hN h

lemma det_sub_upper {i : ℕ} (h : i ≤ n) {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) :
    (N.submatrix (Fin.castLE h) (Fin.castLE h)).det = ∏ j : Fin i, N (Fin.castLE h j) (Fin.castLE h j) := by
  have ht : (N.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := fun a c hca =>
    hN (show Fin.castLE h c < Fin.castLE h a from hca)
  rw [Matrix.det_of_isUpperTriangular ht]
  rfl

lemma lminor_conj {N A : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular id) (i : Fin (n + 1)) :
    lminor (Nᵀ * A * N.map (starRingEnd ℂ)) i =
      (∏ j : Fin i, N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) *
        lminor A i *
        conj (∏ j : Fin i, N (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) := by
  have h := Nat.le_of_lt_succ i.isLt
  unfold lminor
  rw [sub_mul_sub h (Nᵀ * A) (N.map (starRingEnd ℂ)) (fun a c k hk => ?_),
    sub_mul_sub h Nᵀ A (fun a c k hk => ?_), Matrix.det_mul, Matrix.det_mul, ← Matrix.transpose_submatrix, Matrix.det_transpose,
    det_sub_upper h hN]
  · congr 1
    rw [show (N.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
        (starRingEnd ℂ).mapMatrix (N.submatrix (Fin.castLE h) (Fin.castLE h)) from rfl,
      ← RingHom.map_det, det_sub_upper h hN]
  all_goals
    have h1 : N k (Fin.castLE h c) = 0 :=
      upper_lt hN (show Fin.castLE h c < k by rw [Fin.lt_def]; simp; omega)
    have h2 : N k (Fin.castLE h a) = 0 :=
      upper_lt hN (show Fin.castLE h a < k by rw [Fin.lt_def]; simp; omega)
    simp [h1, h2]

end Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma gram_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianLatticeMaps
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace HermitianLatticeMaps

open Matrix NumberField Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def ty (f : Basis ι ℤ X.Λ) :
    (ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ) :=
  (fun i j => herm X.Gm (f i : Fin r → E) (f j : Fin r → E),
    fun k i j => f.repr (RingOfIntegers.basis E k • f i) j)

noncomputable def mulQ (α : E) : (Fin r → E) →ₗ[ℚ] (Fin r → E) :=
  (α • LinearMap.id : (Fin r → E) →ₗ[E] (Fin r → E)).restrictScalars ℚ

theorem mulQ_apply (α : E) (v : Fin r → E) : mulQ α v = α • v := rfl

noncomputable def hL (y : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun x := herm X.Gm x y
  map_add' x x' := by simp [herm, add_mul, Finset.sum_add_distrib]
  map_smul' q x := by
    simp only [herm, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

noncomputable def hR (x : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun y := herm X.Gm x y
  map_add' y y' := by simp [herm, cc, mul_add, Finset.sum_add_distrib]
  map_smul' q y := by
    simp only [herm, cc, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum, map_mul,
      map_ratCast]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem coe_expand (f : Basis ι ℤ X.Λ) (v : X.Λ) :
    (v : Fin r → E) = ∑ i, f.repr v i • (f i : Fin r → E) := by
  first
    | (conv_lhs => rw [← f.sum_repr v]
       rw [Submodule.coe_sum]
       rfl)
    | (conv_lhs => rw [← f.sum_repr v]
       rw [Submodule.coe_sum]
       exact Finset.sum_congr rfl fun i _ => Submodule.coe_smul_of_tower _ _)
    | (conv_lhs => rw [← f.sum_repr v]
       push_cast
       rfl)
    | (have e := congrArg (fun w : X.Λ => (w : Fin r → E)) (f.sum_repr v)
       simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at e
       exact e.symm)

variable (f f' : Basis ι ℤ X.Λ)

noncomputable def phi : (Fin r → E) →ₗ[ℚ] (Fin r → E) :=
  (RealPlaceEmbeddings.qb X f).constr ℚ fun i => (f' i : Fin r → E)

theorem phi_f (i : ι) : phi X f f' (f i : Fin r → E) = f' i := by
  first
    | (rw [← RealPlaceEmbeddings.qb_apply X f i]; unfold phi; rw [Basis.constr_basis])
    | (rw [← RealPlaceEmbeddings.qb_apply (X := X) f i]; unfold phi; rw [Basis.constr_basis])
    | (have e := (RealPlaceEmbeddings.qb X f).constr_basis ℚ (fun j => (f' j : Fin r → E)) i
       rw [RealPlaceEmbeddings.qb_apply] at e
       exact e)

theorem phi_zsum (n : ι → ℤ) :
    phi X f f' (∑ i, n i • (f i : Fin r → E)) = ∑ i, n i • (f' i : Fin r → E) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, phi_f]

theorem phi_mem {x : Fin r → E} (hx : x ∈ X.Λ) : phi X f f' x ∈ X.Λ := by
  have e : x = ∑ i, f.repr ⟨x, hx⟩ i • (f i : Fin r → E) := coe_expand X f ⟨x, hx⟩
  rw [e, phi_zsum]
  exact Submodule.sum_mem _ fun i _ => zsmul_mem (f' i).2 _

theorem phi_phi (x : Fin r → E) : phi X f' f (phi X f f' x) = x := by
  have e : (phi X f' f).comp (phi X f f') = LinearMap.id := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f, LinearMap.id_apply]
  exact LinearMap.congr_fun e x

theorem smul_coe (ω : 𝓞 E) (v : X.Λ) : ((ω • v : X.Λ) : Fin r → E) = (ω : E) • (v : Fin r → E) := by
  first
    | rfl
    | (rw [Submodule.coe_smul]; rfl)
    | (rw [Submodule.coe_smul, Algebra.smul_def]; rfl)

variable {f f'}

theorem phi_omega (h : ty X f = ty X f') (k : Free.ChooseBasisIndex ℤ (𝓞 E)) (i : ι) :
    phi X f f' ((RingOfIntegers.basis E k : E) • (f i : Fin r → E)) =
      (RingOfIntegers.basis E k : E) • (f' i : Fin r → E) := by
  have h2 := congrArg Prod.snd h
  have hk : ∀ j, f.repr (RingOfIntegers.basis E k • f i) j =
      f'.repr (RingOfIntegers.basis E k • f' i) j :=
    fun j => congrFun (congrFun (congrFun h2 k) i) j
  have e1 := coe_expand X f (RingOfIntegers.basis E k • f i)
  have e2 := coe_expand X f' (RingOfIntegers.basis E k • f' i)
  rw [smul_coe] at e1 e2
  rw [e1, phi_zsum, e2]
  simp only [hk]

theorem phi_smul (h : ty X f = ty X f') (α : E) (v : Fin r → E) :
    phi X f f' (α • v) = α • phi X f f' v := by
  have key : ∀ i, phi X f f' (α • (f i : Fin r → E)) = α • (f' i : Fin r → E) := by
    intro i
    have hα := (NumberField.integralBasis E).sum_repr α
    rw [← hα]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_smul, map_sum, smul_assoc, map_smul, NumberField.integralBasis_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact phi_omega X h k i
  have e : (phi X f f').comp (mulQ α) = (mulQ α).comp (phi X f f') := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply, RealPlaceEmbeddings.qb_apply, key, phi_f]
  have := LinearMap.congr_fun e v
  rwa [LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply] at this

theorem phi_herm (h : ty X f = ty X f') (x y : Fin r → E) :
    herm X.Gm (phi X f f' x) (phi X f f' y) = herm X.Gm x y := by
  have h1 := congrArg Prod.fst h
  have hb : ∀ i j, herm X.Gm (f' i : Fin r → E) (f' j) = herm X.Gm (f i : Fin r → E) (f j) :=
    fun i j => (congrFun (congrFun h1 i) j).symm
  have s1 : ∀ i y, herm X.Gm (phi X f f' (f i)) (phi X f f' y) =
      herm X.Gm (f i : Fin r → E) y := by
    intro i y
    have e : (hR X (phi X f f' (f i))).comp (phi X f f') = hR X (f i) := by
      refine (RealPlaceEmbeddings.qb X f).ext fun j => ?_
      rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f]
      exact hb i j
    exact LinearMap.congr_fun e y
  have e2 : (hL X (phi X f f' y)).comp (phi X f f') = hL X y := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply]
    exact s1 i y
  exact LinearMap.congr_fun e2 x

noncomputable def phiE (h : ty X f = ty X f') : (Fin r → E) →ₗ[E] (Fin r → E) where
  toFun := phi X f f'
  map_add' := map_add _
  map_smul' := phi_smul X h

theorem exists_gl (h : ty X f = ty X f') :
    ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧
      (∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f i : Fin r → E) = f' i) ∧
      ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
        ∑ i, (RealPlaceEmbeddings.qb X f').repr v i • (f i : Fin r → E) := by
  have h' : ty X f' = ty X f := h.symm
  have hc : (phiE X h).comp (phiE X h') = LinearMap.id :=
    LinearMap.ext fun v => phi_phi X f' f v
  have hc' : (phiE X h').comp (phiE X h) = LinearMap.id :=
    LinearMap.ext fun v => phi_phi X f f' v
  have hMM : LinearMap.toMatrix' (phiE X h) * LinearMap.toMatrix' (phiE X h') = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id]
  have hMM' : LinearMap.toMatrix' (phiE X h') * LinearMap.toMatrix' (phiE X h) = 1 := by
    rw [← LinearMap.toMatrix'_comp, hc', LinearMap.toMatrix'_id]
  have hv : ∀ v, LinearMap.toMatrix' (phiE X h) *ᵥ v = phi X f f' v := fun v =>
    LinearMap.toMatrix'_mulVec (phiE X h) v
  have hv' : ∀ v, LinearMap.toMatrix' (phiE X h') *ᵥ v = phi X f' f v := fun v =>
    LinearMap.toMatrix'_mulVec (phiE X h') v
  refine ⟨⟨LinearMap.toMatrix' (phiE X h), LinearMap.toMatrix' (phiE X h'), hMM, hMM'⟩,
    ⟨fun x y => ?_, fun x => ?_⟩, fun i => ?_, fun v => ?_⟩
  · show herm X.Gm (LinearMap.toMatrix' (phiE X h) *ᵥ x) (LinearMap.toMatrix' (phiE X h) *ᵥ y) = _
    rw [hv, hv, phi_herm X h]
  · show x ∈ X.Λ ↔ LinearMap.toMatrix' (phiE X h) *ᵥ x ∈ X.Λ
    rw [hv]
    refine ⟨phi_mem X f f', fun hx => ?_⟩
    rw [← phi_phi X f f' x]
    exact phi_mem X f' f hx
  · show LinearMap.toMatrix' (phiE X h) *ᵥ _ = _
    rw [hv, phi_f]
  · show LinearMap.toMatrix' (phiE X h') *ᵥ v = _
    rw [hv', phi, Basis.constr_apply_fintype]
    simp only [Basis.equivFun_apply]

end HermitianLatticeMaps

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientLemmas
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace IsotropicCoefficientLemmas

lemma smul_O {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := by
  rfl

lemma herm_add_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma herm_smul_left {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (e : E) (x z : Fin r → E) :
    herm G (e • x) z = e * herm G x z := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

def Mp {r : ℕ} (X : Data E r) (ξ : Fin r → E) : Submodule (𝓞 E) (Fin r → E) where
  carrier := {μ | μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0}
  add_mem' := fun ha hb => ⟨X.Λ.add_mem ha.1 hb.1, by rw [herm_add_left, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨X.Λ.zero_mem, by simp [herm]⟩
  smul_mem' := fun β μ h => ⟨X.Λ.smul_mem β h.1, by
    rw [smul_O, herm_smul_left, h.2, mul_zero]⟩

def Nx {r : ℕ} (X : Data E r) (ξ : Fin r → E) : Submodule (𝓞 E) (Mp X ξ) where
  carrier := {m | ∃ e : E, (m : Fin r → E) = e • ξ}
  add_mem' := by
    rintro m m' ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [Submodule.coe_add, he, he', add_smul]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro β m ⟨e, he⟩
    exact ⟨(β : E) * e, by rw [Submodule.coe_smul, smul_O, he, smul_smul]⟩

lemma torsion_bot {r : ℕ} (X : Data E r) (ξ : Fin r → E) :
    Submodule.torsion (𝓞 E) (Mp X ξ ⧸ Nx X ξ) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨⟨a, ha⟩, haq⟩ := (Submodule.mem_torsion_iff q).1 hq
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have haq' : (a : 𝓞 E) • (Submodule.Quotient.mk m : Mp X ξ ⧸ Nx X ξ) = 0 := haq
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at haq'
  obtain ⟨e, he⟩ := haq'
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have ha0 : (a : E) ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.ne_zero ha)
  rw [Submodule.coe_smul, smul_O] at he
  show ∃ e : E, (m : Fin r → E) = e • ξ
  refine ⟨e / a, ?_⟩
  rw [div_eq_inv_mul, mul_smul, ← he, smul_smul, inv_mul_cancel₀ ha0, one_smul]

end IsotropicCoefficientLemmas

open IsotropicCoefficientLemmas in
theorem isotropicCoefficientSplitting_holds : IsotropicCoefficientSplitting (E := E) := by
  intro r X ξ hξ
  classical
  have hξ0 : ξ ≠ 0 := hξ.2.2
  have hle : Mp X ξ ≤ X.Λ := fun μ h => h.1
  haveI : Module.Finite (𝓞 E) (Mp X ξ) := by
    haveI : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.2 X.Λ_fg
    have h1 : ((Mp X ξ).comap X.Λ.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map X.Λ.subtype
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.2 hle] at h2
    exact Module.Finite.iff_fg.2 h2
  haveI : Module.Flat (𝓞 E) (Mp X ξ ⧸ Nx X ξ) :=
    IsDedekindDomain.flat_iff_torsion_eq_bot.2 (torsion_bot X ξ)
  haveI : Module.FinitePresentation (𝓞 E) (Mp X ξ ⧸ Nx X ξ) :=
    Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (Mp X ξ ⧸ Nx X ξ) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Nx X ξ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  set ρ : Mp X ξ →ₗ[𝓞 E] Mp X ξ := LinearMap.id - s ∘ₗ (Nx X ξ).mkQ with hρdef
  have hρN : ∀ m, ∃ e : E, ((ρ m : Mp X ξ) : Fin r → E) = e • ξ := by
    intro m
    have h1 : (Nx X ξ).mkQ (s ((Nx X ξ).mkQ m)) = (Nx X ξ).mkQ m := LinearMap.congr_fun hs _
    have h2 : (Nx X ξ).mkQ (ρ m) = 0 := by
      rw [hρdef, LinearMap.sub_apply, map_sub, LinearMap.id_apply, LinearMap.comp_apply, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero _).1 h2
  choose coef hcoef using hρN
  have hρid : ∀ m ∈ Nx X ξ, ρ m = m := by
    intro m hm
    have : (Nx X ξ).mkQ m = 0 := (Submodule.Quotient.mk_eq_zero _).2 hm
    simp [hρdef, this]
  have huniq : ∀ e e' : E, e • ξ = e' • ξ → e = e' := fun e e' h => smul_left_injective E hξ0 h
  have hmemMp : ∀ μ ∈ X.Λp ξ, μ ∈ Mp X ξ := fun μ h => ⟨h.1, h.2⟩
  refine ⟨fun μ => if h : μ ∈ Mp X ξ then coef ⟨μ, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    simp only [dif_pos (hmemMp μ hμ)]
    rw [← hcoef]
    exact (ρ _).2.1
  · intro μ hμ μ' hμ'
    have hs' := (Mp X ξ).add_mem (hmemMp μ hμ) (hmemMp μ' hμ')
    simp only [dif_pos hs', dif_pos (hmemMp μ hμ), dif_pos (hmemMp μ' hμ')]
    apply huniq
    rw [← hcoef, add_smul, ← hcoef, ← hcoef]
    have : (⟨μ + μ', hs'⟩ : Mp X ξ) = ⟨μ, hmemMp μ hμ⟩ + ⟨μ', hmemMp μ' hμ'⟩ := rfl
    rw [this, map_add (f := _)]
    rfl
  · intro α μ hμ
    have hs' : (α : E) • μ ∈ Mp X ξ := by
      rw [← smul_O]
      exact (Mp X ξ).smul_mem α (hmemMp μ hμ)
    simp only [dif_pos hs', dif_pos (hmemMp μ hμ)]
    apply huniq
    rw [← hcoef, mul_smul, ← hcoef]
    have : (⟨(α : E) • μ, hs'⟩ : Mp X ξ) = α • ⟨μ, hmemMp μ hμ⟩ := Subtype.ext (smul_O α μ).symm
    rw [this, map_smul, Submodule.coe_smul, smul_O]
  · intro e he
    have hmem : e • ξ ∈ Mp X ξ := ⟨he, by rw [herm_smul_left, hξ.2.1, mul_zero]⟩
    simp only [dif_pos hmem]
    apply huniq
    rw [← hcoef, hρid _ ⟨e, rfl⟩]

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PackingSeparation
namespace ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation

open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical

theorem pack {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] (μ : Measure W) [μ.IsAddHaarMeasure]
    (S : Finset W) (R : ℝ) (hR : 0 ≤ R) (hS : ∀ p ∈ S, ‖p‖ ≤ R)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) :
    (S.card : ℝ) ≤ (1 + 2 * R) ^ finrank ℝ W := by
  set d := finrank ℝ W
  have hdisj : (S : Set W).PairwiseDisjoint fun p => ball p (1 / 2) := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    rw [mem_ball, dist_eq_norm] at hzp hzq
    have h1 := hsep p hp q hq hpq
    have h2 : ‖p - q‖ ≤ ‖z - p‖ + ‖z - q‖ := by
      calc ‖p - q‖ = ‖(z - q) - (z - p)‖ := by congr 1; abel
        _ ≤ ‖z - q‖ + ‖z - p‖ := norm_sub_le _ _
        _ = ‖z - p‖ + ‖z - q‖ := add_comm _ _
    linarith
  have hsub : (⋃ p ∈ S, ball p (1 / 2)) ⊆ ball (0 : W) (R + 1 / 2) := by
    intro z hz
    simp only [Set.mem_iUnion, mem_ball, dist_eq_norm] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    rw [mem_ball, dist_eq_norm, sub_zero]
    calc ‖z‖ = ‖(z - p) + p‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - p‖ + ‖p‖ := norm_add_le _ _
      _ < 1 / 2 + R := by linarith [hS p hp]
      _ = R + 1 / 2 := add_comm _ _
  have h := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at h
  simp only [Measure.addHaar_ball μ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Measure.addHaar_ball μ _ (by positivity : (0 : ℝ) ≤ R + 1 / 2), Finset.sum_const,
    nsmul_eq_mul] at h
  rw [← mul_assoc] at h
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hctop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hctop).mp h
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have h3 : (S.card : ℝ) = (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d := by
    rw [mul_assoc, ← mul_pow]
    norm_num
  rw [h3]
  calc (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d ≤ (R + 1 / 2) ^ d * 2 ^ d :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (1 + 2 * R) ^ d := by
        rw [← mul_pow]
        congr 1
        ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma one_le_abs_norm (γ : 𝓞 E) (hγ : γ ≠ 0) : 1 ≤ |(Algebra.norm ℚ (γ : E) : ℝ)| := by
  have h := Algebra.coe_norm_int γ
  have hne : Algebra.norm ℤ γ ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at h
    exact (Algebra.norm_ne_zero_iff.mpr (by exact_mod_cast hγ : (γ : E) ≠ 0)) h.symm
  rw [← h]
  have := Int.one_le_abs hne
  push_cast
  exact_mod_cast this

lemma sep (γ : 𝓞 E) (hγ : γ ≠ 0) : ∃ w : CP E, 1 ≤ ‖w.1.embedding (γ : E)‖ := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  set w1 : CP E := ⟨w0, IsTotallyComplex.isComplex w0⟩
  have h := prod_norm (E := E) (γ : E)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w1)] at h
  have hle : ∏ w ∈ Finset.univ.erase w1, ‖w.1.embedding (γ : E)‖ ^ 2 ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => by positivity)
      (fun w _ => pow_le_one₀ (norm_nonneg _) (hcon w).le)
  have hlt : ‖w1.1.embedding (γ : E)‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) (hcon w1) two_ne_zero
  have := one_le_abs_norm γ hγ
  rw [← h] at this
  nlinarith [mul_le_of_le_one_right (sq_nonneg ‖w1.1.embedding (γ : E)‖) hle]

theorem count (R : ℝ) (hR : 0 ≤ R) :
    {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.Finite ∧
      ({α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R) ^ (2 * fdeg E) := by
  set T := {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}
  have hT : T.Finite := by
    have h := Embeddings.finite_of_norm_le E ℂ R
    refine (h.preimage (Set.injOn_of_injective RingOfIntegers.coe_injective)).subset ?_
    intro α hα
    exact ⟨α.isIntegral_coe, hα⟩
  refine ⟨hT, ?_⟩
  let p : 𝓞 E → (CP E → ℂ) := fun α w => w.1.embedding (α : E)
  have hpinj : Function.Injective p := by
    intro α β h
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    have := congrFun h ⟨w0, IsTotallyComplex.isComplex w0⟩
    exact RingOfIntegers.coe_injective (w0.embedding.injective this)
  have hd : finrank ℝ (CP E → ℂ) = 2 * fdeg E := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, (card_CP (E := E)).1, mul_comm]
  have hcard : T.ncard = (hT.toFinset.image p).card := by
    rw [Finset.card_image_of_injective _ hpinj, Set.ncard_eq_toFinset_card _ hT]
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have : Nonempty (CP E) := ⟨⟨w0, IsTotallyComplex.isComplex w0⟩⟩
  rw [hcard, ← hd]
  refine pack volume _ R hR ?_ ?_
  · intro q hq
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hq
    rw [Set.Finite.mem_toFinset] at hα
    exact (pi_norm_le_iff_of_nonneg hR).mpr fun w => hα _
  · intro q hq q' hq' hne
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hq'
    have hαβ : α - β ≠ 0 := sub_ne_zero.mpr fun h => hne (by rw [h])
    obtain ⟨w, hw⟩ := sep (α - β) hαβ
    calc (1 : ℝ) ≤ ‖w.1.embedding ((α - β : 𝓞 E) : E)‖ := hw
      _ = ‖(p α - p β) w‖ := by simp [p]
      _ ≤ ‖p α - p β‖ := norm_le_pi_norm _ w

end ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
end
