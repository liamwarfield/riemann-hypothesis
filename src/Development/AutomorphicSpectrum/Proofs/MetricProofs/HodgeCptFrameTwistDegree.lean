module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsReversedTriangularFrameChange
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsReversedTriangularFrameChange
open Matrix

namespace GlobalTheory.CompanionTheory.AdaptedFrame

variable {Φ : Type} [Field Φ] {r : ℕ}

def revMatrix (Φ : Type) [Field Φ] (r : ℕ) : Matrix (Fin r) (Fin r) Φ :=
  Matrix.of fun a b => if a = Fin.rev b then 1 else 0

theorem mul_revMatrix_apply (A : Matrix (Fin r) (Fin r) Φ) (a b : Fin r) :
    (A * revMatrix Φ r) a b = A a (Fin.rev b) := by
  simp [Matrix.mul_apply, revMatrix]

theorem revMatrix_mul_apply (A : Matrix (Fin r) (Fin r) Φ) (a b : Fin r) :
    (revMatrix Φ r * A) a b = A (Fin.rev a) b := by
  have : ∀ x : Fin r, (a = Fin.rev x) ↔ (x = Fin.rev a) := fun x => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [Matrix.mul_apply, revMatrix, this]

theorem revMatrix_mul_self : revMatrix Φ r * revMatrix Φ r = 1 := by
  ext a b
  rw [mul_revMatrix_apply]
  simp [revMatrix, Matrix.one_apply, Fin.rev_rev]

theorem revMatrix_transpose : (revMatrix Φ r)ᵀ = revMatrix Φ r := by
  ext a b
  simp only [revMatrix, Matrix.transpose_apply, Matrix.of_apply]
  have : (b = Fin.rev a) ↔ (a = Fin.rev b) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [this]

theorem inv_diag (U : Matrix (Fin r) (Fin r) Φ) (hU : U.BlockTriangular id)
    (hd : ∀ l, U l l ≠ 0) (l : Fin r) : U⁻¹ l l = (U l l)⁻¹ := by
  have hdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular hU]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have hinv : U⁻¹.BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet U hdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have h1 : (U * U⁻¹) l l = 1 := by
    rw [Matrix.mul_nonsing_inv U hdet]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single l] at h1
  · exact eq_inv_of_mul_eq_one_right h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hU (show id k < id l from h)]; simp
    · rw [hinv (show id l < id k from h)]; simp
  · simp

theorem reversed_dual_frame :
    ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (r : ℕ) (u T U Rm Rm' : Matrix (Fin r) (Fin r) Φ),
      IsUnit u.det → IsUnit T.det → U.BlockTriangular id → (∀ l, U l l ≠ 0) →
      (∀ a b, Rm a b ∈ R) → (∀ a b, Rm' a b ∈ R) → Rm * Rm' = 1 →
      (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) * U = Tᵀ⁻¹ * Rm →
      ∃ U₂ R₂ R₂' : Matrix (Fin r) (Fin r) Φ, U₂.BlockTriangular id ∧
        (∀ l, U₂ l l = (U l.rev l.rev)⁻¹) ∧ (∀ a b, R₂ a b ∈ R) ∧ (∀ a b, R₂' a b ∈ R) ∧
        R₂ * R₂' = 1 ∧ u * U₂ = T * R₂ := by
  intro Φ _ R r u T U Rm Rm' hu hT hU hd hRm hRm' hmul h
  have hUdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular hU]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have hUinv : U⁻¹.BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet U hUdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have hutdet : IsUnit (uᵀ).det := by rwa [Matrix.det_transpose]
  have hTtdet : IsUnit (Tᵀ).det := by rwa [Matrix.det_transpose]
  have hUtdet : IsUnit (Uᵀ).det := by rwa [Matrix.det_transpose]
  set P := revMatrix Φ r with hP
  have hPP : P * P = 1 := revMatrix_mul_self
  have hPt : Pᵀ = P := revMatrix_transpose
  have hrev : (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) = uᵀ⁻¹ * P := by
    ext a b
    rw [mul_revMatrix_apply]; rfl
  rw [hrev] at h

  have e1 : Tᵀ * (uᵀ⁻¹ * P * U * Rm') = 1 := by
    rw [h, Matrix.mul_assoc (Tᵀ⁻¹), hmul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hTtdet]
  have e2 : Rm'ᵀ * Uᵀ * P * u⁻¹ * T = 1 := by
    have := congrArg Matrix.transpose e1
    simp only [Matrix.transpose_mul, Matrix.transpose_one, hPt, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv] at this
    simpa [Matrix.mul_assoc] using this
  have e3 : T * (Rm'ᵀ * Uᵀ * P * u⁻¹) = 1 := mul_eq_one_comm.1 e2
  have e4 : T * Rm'ᵀ = u * P * Uᵀ⁻¹ := by
    have hk : (Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹) = 1 := by
      calc (Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹)
          = Uᵀ * P * (u⁻¹ * u) * P * Uᵀ⁻¹ := by simp only [Matrix.mul_assoc]
        _ = Uᵀ * (P * P) * Uᵀ⁻¹ := by
            rw [Matrix.nonsing_inv_mul _ hu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = 1 := by rw [hPP, Matrix.mul_one, Matrix.mul_nonsing_inv _ hUtdet]
    calc T * Rm'ᵀ = T * Rm'ᵀ * ((Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹)) := by rw [hk, Matrix.mul_one]
      _ = (T * (Rm'ᵀ * Uᵀ * P * u⁻¹)) * (u * P * Uᵀ⁻¹) := by simp only [Matrix.mul_assoc]
      _ = u * P * Uᵀ⁻¹ := by rw [e3, Matrix.one_mul]
  have hent : ∀ a b, (P * Uᵀ⁻¹ * P) a b = U⁻¹ (Fin.rev b) (Fin.rev a) := by
    intro a b
    rw [hP, mul_revMatrix_apply, revMatrix_mul_apply, ← Matrix.transpose_nonsing_inv,
      Matrix.transpose_apply]
  refine ⟨P * Uᵀ⁻¹ * P, Rm'ᵀ * P, P * Rmᵀ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    rw [hent]
    exact hUinv (show id (Fin.rev a) < id (Fin.rev b) from Fin.rev_lt_rev.2 hab')
  · intro l
    rw [hent]
    exact inv_diag U hU hd _
  · intro a b
    rw [mul_revMatrix_apply]; exact hRm' _ _
  · intro a b
    rw [revMatrix_mul_apply]; exact hRm _ _
  · calc Rm'ᵀ * P * (P * Rmᵀ) = Rm'ᵀ * (P * P) * Rmᵀ := by simp only [Matrix.mul_assoc]
      _ = (Rm * Rm')ᵀ := by rw [hPP, Matrix.mul_one, Matrix.transpose_mul]
      _ = 1 := by rw [hmul, Matrix.transpose_one]
  · calc u * (P * Uᵀ⁻¹ * P) = (u * P * Uᵀ⁻¹) * P := by simp only [Matrix.mul_assoc]
      _ = T * (Rm'ᵀ * P) := by rw [← e4, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.AdaptedFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsReversedTriangularFrameChangeStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reversed_triangular_frame_change : ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (r : ℕ) (u T U Rm Rm' : Matrix (Fin r) (Fin r) Φ), IsUnit u.det → IsUnit T.det → U.BlockTriangular id → (∀ l, U l l ≠ 0) → (∀ a b, Rm a b ∈ R) → (∀ a b, Rm' a b ∈ R) → Rm * Rm' = 1 → (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) * U = Tᵀ⁻¹ * Rm → ∃ U₂ R₂ R₂' : Matrix (Fin r) (Fin r) Φ, U₂.BlockTriangular id ∧ (∀ l, U₂ l l = (U l.rev l.rev)⁻¹) ∧ (∀ a b, R₂ a b ∈ R) ∧ (∀ a b, R₂' a b ∈ R) ∧ R₂ * R₂' = 1 ∧ u * U₂ = T * R₂ := by
  first | exact @GlobalTheory.CompanionTheory.AdaptedFrame.reversed_dual_frame | exact GlobalTheory.CompanionTheory.AdaptedFrame.reversed_dual_frame | (intros; apply GlobalTheory.CompanionTheory.AdaptedFrame.reversed_dual_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistDegree
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun


set_option maxHeartbeats 4000000 in
theorem map_transpose_inv {Ω Φ : Type} [Field Ω] [Field Φ] (i : Ω →+* Φ) {r : ℕ} (T : Matrix (Fin r) (Fin r) Ω)
    (hT : IsUnit T.det) : (Tᵀ⁻¹).map i = (T.map i)ᵀ⁻¹ := by
  have h1 : IsUnit (Tᵀ).det := by rwa [Matrix.det_transpose]
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.transpose_map, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ h1, Matrix.map_one _ (map_zero i) (map_one i)]


set_option maxHeartbeats 4000000 in
theorem isUnit_det_rev {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (hM : IsUnit M.det) :
    IsUnit (Matrix.of fun a b => M a (Fin.rev b)).det := by
  have e : (Matrix.of fun a b => M a (Fin.rev b)) = M.submatrix id (Fin.revPerm : Equiv.Perm (Fin r)) := by
    ext a b; rfl
  rw [e, Matrix.det_permute']
  exact IsUnit.mul ((Units.isUnit _).map (Int.castRingHom R)) hM


set_option maxHeartbeats 4000000 in
theorem isFrameAt_of_map {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E'] {L : Lat ξ E} {f : E →ₗ[Ω] E'}
    (hf : Function.Injective f) {r : ℕ} {b : Fin r → E} {p : Cpt ξ}
    (h : (L.map f).IsFrameAt (fun a => f (b a)) p) : L.IsFrameAt b p := by
  unfold Lat.IsFrameAt at h ⊢
  unfold Lat.map at h
  refine ⟨LinearIndependent.of_comp f h.1, ?_⟩
  have e2 : Submodule.map (f.restrictScalars (regAt ξ p)) (Submodule.span (regAt ξ p) (Set.range b)) =
      Submodule.span (regAt ξ p) (Set.range fun a => f (b a)) := by
    rw [Submodule.map_span]
    congr 1
    ext x
    simp
  exact Submodule.map_injective_of_injective (f := f.restrictScalars (regAt ξ p)) hf (h.2.trans e2.symm)


set_option maxHeartbeats 4000000 in
theorem forms_quotient {Ω Φ : Type} [Field Ω] [Field Φ] (i : Ω →+* Φ) (R₀ : Subring Ω) (R : Subring Φ)
    (hi : ∀ a ∈ R₀, i a ∈ R) {n r : ℕ} (A : Matrix (Fin n) (Fin r) Ω) (T : Matrix (Fin r) (Fin r) Ω)
    (C₀ : Matrix (Fin r) (Fin n) Ω) (t : Ω) (u U R₂ R₂' : Matrix (Fin r) (Fin r) Φ)
    (hreg : ∀ a b, (A * T) a b / t ∈ R₀) (hC₀ : ∀ a b, C₀ a b ∈ R₀)
    (hinv : ∀ a b, ∑ k, C₀ a k * ((A * T) k b / t) = if a = b then 1 else 0)
    (h2 : ∀ a b, R₂ a b ∈ R) (h2' : ∀ a b, R₂' a b ∈ R) (h1 : R₂ * R₂' = 1) (hu : u * U = T.map i * R₂) :
    ∃ C : Matrix (Fin r) (Fin n) Φ, (∀ a b, (A.map i * u * U) a b / i t ∈ R) ∧ (∀ a b, C a b ∈ R) ∧
      ∀ a b, ∑ k, C a k * ((A.map i * u * U) k b / i t) = if a = b then 1 else 0 := by
  classical
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀ : Matrix (Fin n) (Fin r) Ω, Y₀ = Matrix.of fun k b => (A * T) k b / t := ⟨_, rfl⟩
  have hCY : C₀ * Y₀ = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply, hY₀]
    exact hinv a b
  have hX : ∀ a b, (A.map i * u * U) a b / i t = (Y₀.map i * R₂) a b := by
    intro a b
    rw [Matrix.mul_assoc, hu, ← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.map_apply, Matrix.map_apply, hY₀, Matrix.of_apply, map_div₀, div_mul_eq_mul_div]
  have hR : R₂' * R₂ = 1 := by
    rw [← Matrix.inv_eq_right_inv h1]
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h1)
  refine ⟨R₂' * C₀.map i, ?_, ?_, ?_⟩
  · intro a b
    rw [hX, Matrix.mul_apply]
    refine R.sum_mem fun k _ => R.mul_mem ?_ (h2 k b)
    rw [Matrix.map_apply, hY₀, Matrix.of_apply]
    exact hi _ (hreg a k)
  · intro a b
    rw [Matrix.mul_apply]
    exact R.sum_mem fun k _ => R.mul_mem (h2' a k) (hi _ (hC₀ k b))
  · intro a b
    simp_rw [hX]
    have e : (R₂' * C₀.map i) * (Y₀.map i * R₂) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C₀.map i), ← Matrix.map_mul, hCY,
        Matrix.map_one _ (map_zero i) (map_one i), Matrix.one_mul, hR]
    have e2 := congrFun (congrFun e a) b
    rwa [Matrix.mul_apply, Matrix.one_apply] at e2

set_option maxHeartbeats 4000000 in
private theorem linearIndependent_of_dual_pairing {Ω W : Type} [Field Ω] [AddCommGroup W] [Module Ω W] {r : ℕ}
    (B : Fin r → Module.Dual Ω W) (v : Fin r → W) (hBv : ∀ a b, B a (v b) = if a = b then 1 else 0) :
    LinearIndependent Ω v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h1 := congrArg (B a) hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hBv, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, map_zero] at h1
  exact h1

set_option maxHeartbeats 4000000 in
private theorem isFrameAt_of_dual_basis {X : Scheme.{0}} {Ω W : Type} [Field Ω] [AddCommGroup W] [Module Ω W]
    [FiniteDimensional Ω W] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ W) (p : Cpt ξ) {r : ℕ}
    (hr : Module.finrank Ω W = r)
    (hmem : ∀ e : W, e ∈ L p ↔ ∀ w ∈ L.dual p, w e ∈ regAt ξ p)
    (B : Fin r → Module.Dual Ω W) (hB : L.dual p = Submodule.span (regAt ξ p) (Set.range B))
    (v : Fin r → W) (hBv : ∀ a b, B a (v b) = if a = b then 1 else 0) : L.IsFrameAt v p := by
  classical
  have hli := linearIndependent_of_dual_pairing B v hBv
  have hBmem : ∀ a, B a ∈ L.dual p := fun a => by rw [hB]; exact Submodule.subset_span ⟨a, rfl⟩
  refine ⟨hli, le_antisymm ?_ ?_⟩
  · intro e he
    have hc : ∀ a, B a e ∈ regAt ξ p := fun a => (hmem e).1 he _ (hBmem a)
    have htop : Submodule.span Ω (Set.range v) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin, hr])
    obtain ⟨bv, hbv⟩ : ∃ bv : Module.Basis (Fin r) Ω W, ⇑bv = v :=
      ⟨Module.Basis.mk hli htop.ge, Module.Basis.coe_mk _ _⟩
    have hs := bv.sum_repr e
    rw [hbv] at hs
    have hco : ∀ b, bv.repr e b = B b e := by
      intro b
      conv_rhs => rw [← hs]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hBv, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [← hs]
    refine Submodule.sum_mem _ fun b _ => ?_
    have e1 : bv.repr e b • v b = (⟨B b e, hc b⟩ : regAt ξ p) • v b := by rw [hco]; rfl
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    refine (hmem (v b)).2 fun w hw => ?_
    rw [hB] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [hBv]
      split_ifs
      · exact (regAt ξ p).one_mem
      · exact (regAt ξ p).zero_mem
    | zero => rw [LinearMap.zero_apply]; exact (regAt ξ p).zero_mem
    | add x y _ _ hx hy => rw [LinearMap.add_apply]; exact (regAt ξ p).add_mem hx hy
    | smul a x _ hx => rw [LinearMap.smul_apply]; exact (regAt ξ p).mul_mem a.2 hx


set_option maxHeartbeats 4000000 in
theorem adapted_frame_om : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (rk (CMType H) D.p D.q (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (n (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ))) = if a = b then 1 else 0) ∧ ∀ l : Fin D.q, ((𝔐'.V (.inr τ)).gr (Fl.b (.inr τ)) l.rev).IsGenAt p' (U l l)⁻¹ := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hI
  unfold FormsOK at hF
  unfold HodgeOver at hO
  unfold ColFlags at hC
  obtain ⟨hd, -, -, hj, -⟩ := hO
  obtain ⟨T, C₀, hT, hfr, hreg, hC₀, hinv⟩ := GlobalTheory.T.exists_local_twist_trivialization 𝔐.X Ω 𝔐.ξ (EE 𝔐) (∀ k, J₀ k) (seg x₀)
    (LL 𝔐 (.inr τ)) (m (.inr τ)) _ (n (.inr τ)) (VV 𝔐 (.inr τ)) (φ (.inr τ)) (cc 𝔐 bW bO (.inr τ))
    (hF.2.2.1 _) (hF.1 _) (hF.2.1 _).1 (hF.2.1 _).2 ⟨pr p'.1, hp⟩ c₁ hI
  have e1 : colFrame (cc 𝔐 bW bO (.inr τ)) T = fun a => inO 𝔐 τ (colFrame (bO τ) T a) := by
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [colFrame, cc, map_sum, map_smul]
    rfl
  rw [e1] at hfr
  have hom : (omBundle 𝔐 τ).IsFrameAt (colFrame (bO τ) T) ⟨pr p'.1, hp⟩ :=
    isFrameAt_of_map (GenBases.inO_injective 𝔐 τ) hfr
  have hvb := 𝔐.vb (.inr τ)
  obtain ⟨hcVB, hcmap⟩ := Lat.restrict_isVBOn _ _ _ _ _ _ _ _ hvb
  have hbid := (Lat.isVBOn_dual_and_bidual _ _ _ _ _ _ _ hcVB).2 ⟨pr p'.1, hp⟩ (Set.mem_univ _)
  obtain ⟨U', hpU, b₀, hb₀span, hb₀fr⟩ := hcVB ⟨pr p'.1, hp⟩ (Set.mem_univ _)
  have hb₀ := (hb₀fr ⟨pr p'.1, hp⟩ (Set.mem_univ _) hpU).1
  have : FiniteDimensional Ω (𝔐.Vgen (.inr τ)) := Module.Finite.of_basis (Module.Basis.mk hb₀ hb₀span.ge)
  have hrank : Module.finrank Ω (𝔐.Vgen (.inr τ)) = D.q := by
    rw [← Subspace.dual_finrank_eq, Module.finrank_eq_card_basis (bO τ), Fintype.card_fin]
  obtain ⟨v, hv⟩ : ∃ v : Fin (rk (CMType H) D.p D.q (.inr τ)) → 𝔐.Vgen (.inr τ), ∀ a b : Fin (rk (CMType H) D.p D.q (.inr τ)), bO τ a (v b) = if a = b then 1 else 0 := by
    refine ⟨fun b => (Module.evalEquiv Ω _).symm ((bO τ).dualBasis b), fun a b => ?_⟩
    simp only [Module.apply_evalEquiv_symm_apply]
    exact (bO τ).dualBasis_apply_self b a
  have hTt : IsUnit Tᵀ.det := by rwa [Matrix.det_transpose]
  have hBv : ∀ a b : Fin (rk (CMType H) D.p D.q (.inr τ)), colFrame (r := rk (CMType H) D.p D.q (.inr τ)) (bO τ) T a (colFrame v Tᵀ⁻¹ b) = if a = b then 1 else 0 := by
    intro a b
    have hm := congrFun (congrFun (Matrix.mul_nonsing_inv _ hTt) a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at hm
    rw [← hm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [colFrame, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hv, smul_eq_mul,
      Matrix.transpose_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    try exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hLc := isFrameAt_of_dual_basis ((𝔐.V (.inr τ)).comap (𝔐.Vgen (.inr τ)).subtype) ⟨pr p'.1, hp⟩ hrank hbid
    (colFrame (bO τ) T) hom.2 (colFrame v Tᵀ⁻¹) hBv
  have hVfr : (𝔐.V (.inr τ)).IsFrameAt (fun k => ((colFrame v Tᵀ⁻¹ k : 𝔐.Vgen (.inr τ)) : 𝔐.Li))
      ⟨pr p'.1, hp⟩ := by
    refine ⟨hLc.1.map' _ (Submodule.ker_subtype _), ?_⟩
    have hc2 : ((𝔐.V (.inr τ)).comap (𝔐.Vgen (.inr τ)).subtype).map (𝔐.Vgen (.inr τ)).subtype ⟨pr p'.1, hp⟩ =
        𝔐.V (.inr τ) ⟨pr p'.1, hp⟩ := hcmap _ (Set.mem_univ _)
    rw [← hc2]
    unfold Lat.map
    rw [hLc.2, Submodule.map_span]
    congr 1
    ext x
    simp
    exact Iff.rfl
  have hpull := FlagPull.pull_isFrameAt hd hj p' hp hVfr
  rw [← hV (.inr τ)] at hpull
  have hcol : (fun k => j ((colFrame v Tᵀ⁻¹ k : 𝔐.Vgen (.inr τ)) : 𝔐.Li)) =
      colFrame (fun a => j (v a : 𝔐.Li)) ((Tᵀ⁻¹).map (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)))) := by
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [colFrame, Submodule.coe_sum, Submodule.coe_smul, map_sum, hj.1, Matrix.map_apply]
  rw [hcol, map_transpose_inv _ T hT] at hpull
  have hgdet : IsUnit (Matrix.of fun a b => (genU Ω (rk (CMType H) D.p D.q) (.inr τ))ᵀ⁻¹ a (Fin.rev b)).det := by
    apply isUnit_det_rev
    apply Matrix.isUnit_nonsing_inv_det
    rw [Matrix.det_transpose, DetG.det_genU]
    exact isUnit_one
  have hFl : Fl.b (.inr τ) = colFrame (fun a => j (v a : 𝔐.Li))
      (Matrix.of fun a b => (genU Ω (rk (CMType H) D.p D.q) (.inr τ))ᵀ⁻¹ a (Fin.rev b)) := by
    funext k
    rw [hC.2 τ v hv k, DetG.omBlock_gMat]
    rfl
  have hw : LinearIndependent (GenField Ω (rk (CMType H) D.p D.q)) (fun a => j (v a : 𝔐.Li)) :=
    hj.2 _ (fun a => (v a : 𝔐.Li)) ((linearIndependent_of_dual_pairing _ v hv).map' _ (Submodule.ker_subtype _))
  have hsub : (𝔐'.V (.inr τ)).IsFlagVBOn Set.univ (colFrame (fun a => j (v a : 𝔐.Li))
      (Matrix.of fun a b => (genU Ω (rk (CMType H) D.p D.q) (.inr τ))ᵀ⁻¹ a (Fin.rev b))) := by
    rw [← hFl]
    exact Fl.sub (.inr τ)
  obtain ⟨U₀, Rm, Rm', hU₀, hRm, hRm', hRR, hgU, hgr⟩ :=
    GlobalTheory.T.exists_triangular_regular_frame_change 𝔐'.X _ 𝔐'.ξ 𝔐'.Li (𝔐'.V (.inr τ)) _ (fun a => j (v a : 𝔐.Li)) _ _ p' hw hgdet hpull hsub
  have hTi : IsUnit (T.map (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)))).det := by
    have h := hT.map (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)))
    rw [RingHom.map_det] at h
    exact h
  obtain ⟨U₂, R₂, R₂', hU₂, hU₂d, hR₂, hR₂', hRR₂, hu⟩ :=
    GlobalTheory.T.exists_reversed_triangular_frame_change _ (regAt 𝔐'.ξ p') _ (genU Ω (rk (CMType H) D.p D.q) (.inr τ)) _ U₀ Rm Rm'
      (by rw [DetG.det_genU]; exact isUnit_one) hTi hU₀ (fun l => (hgr l).1) hRm hRm' hRR hgU
  obtain ⟨C, hC1, hC2, hC3⟩ := forms_quotient (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)))
    (regAt 𝔐.ξ ⟨pr p'.1, hp⟩) (regAt 𝔐'.ξ p') (fun a ha => LatModel.dominates_regAt hd p' hp ha)
    (aOf 𝔐 bW bO φ (.inr τ)) T C₀ (seg x₀ c₁ ^ m (.inr τ)) _ U₂ R₂ R₂' hreg hC₀ hinv hR₂ hR₂' hRR₂ hu
  refine ⟨U₂, C, hU₂, hC1, hC2, hC3, fun l => ?_⟩
  rw [hU₂d l, inv_inv, hFl]
  exact hgr l.rev

end GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistDegreeStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_twist_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (rk (CMType H) D.p D.q (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inr τ))) (Fin (n (.inr τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inr τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inr τ))) = if a = b then 1 else 0) ∧ ∀ l : Fin D.q, ((𝔐'.V (.inr τ)).gr (Fl.b (.inr τ)) l.rev).IsGenAt p' (U l l)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsOm.adapted_frame_om <;> assumption)
end
