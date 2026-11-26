module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentEqKappaLatticePoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineHomTransportLatticeVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineHomTransportLatticeVacua
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapVac

variable {D : D7}

theorem lnk_simil {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') :
    l.τᴴ ⬝ (L.gram ⬝ l.τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L.gram := by
  rw [Int.cast_one, one_mul]
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  exact mul_right_cancel₀ b c

theorem lnk_tau_ne {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') : l.τ ≠ 0 := by
  intro h0
  have e := l.map
  rw [h0, Matrix.zero_mulVec] at e
  have hz : ζ = 0 := neg_eq_zero.mp e.symm
  have n : D.host.xi0 * star D.host.xi0 * (star ζ' ⬝ᵥ L.gram *ᵥ ζ') = 0 := by
    rw [← l.norm, hz]; simp
  rcases mul_eq_zero.1 n with h1 | h1
  · rcases mul_eq_zero.1 h1 with h3 | h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D h3
    · exact GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D (star_eq_zero.1 h3)
  · exact h.2 h1

theorem kap_surj {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) :
    Function.Surjective (l.κ S) := by
  obtain ⟨σ, _, hτσ⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  intro x
  refine ⟨(rat σ : Mx D L.rank L.rank) ⬝ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S x, ?_⟩
  rw [Lnk.κ, ← Matrix.mul_assoc, ← rat_mul, hτσ, rat_one, Matrix.one_mul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

theorem kap_add {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : l.κ S (v + w) = l.κ S v + l.κ S w :=
  (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).1 v w

theorem kap_sympl {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    (v w : WO S L) : symplOH L S (l.κ S v) (l.κ S w) = -symplOH S L v w := by
  have e := (GlobalTheory.LinkKappa.kappa_props D L L S l.τ 1 (lnk_simil h l) (l.κ S) (fun _ => rfl)).2.2.2.2.1 v w
  unfold symplOH
  rw [e, Int.cast_one, one_mul, mul_neg]

theorem kap_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E}
    (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D) (Ξ : WO L S → ℂ) (w' : WO S L)
    (hw : heisO ψ S L w' (fun w => star (Ξ (l.κ S w))) = fun w => star (Ξ (l.κ S w))) :
    heisO ψ L S (l.κ S w') Ξ = Ξ := by
  funext x
  obtain ⟨v, rfl⟩ := kap_surj h l S x
  have e := congrFun hw v
  simp only [heisO] at e
  have e2 := congrArg (starRingEnd ℂ) e
  rw [map_mul, GlobalTheory.AdjLawPf.conj_psi ψ hψ] at e2
  simp only [starRingEnd_apply, star_star] at e2
  simp only [heisO]
  rw [kap_sympl h l, ← kap_add h l]
  exact e2

theorem half_mul_left {m n k : ℕ} {e : AE D} (M : Mx D m n) {x : Mx D n k} (hx : IsHalf e x) : IsHalf e (M ⬝ x) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx]

theorem half_mul_right {m n k : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (M : Mx D n k) : IsHalf e (x ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, hx]

theorem half_smul {m n : ℕ} {e : AE D} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx]

theorem half_adj {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) := by
  intro i j
  show cA D e * cA D (x j i) = cA D (x j i)
  rw [← map_mul, hx]

theorem split_conj {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := he
  exact ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hv,
    by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]⟩

theorem kap_half {L : HSp D} {ζ ζ' : Fin L.rank → D.host.E} (h : IsLineVec L ζ') (l : Lnk L ζ L ζ') (S : HSp D)
    {e : AE D} {w : WO S L} (hh : IsHalf e (l.κ S w)) : IsHalf (cA D e) w := by
  obtain ⟨σ, hστ, _⟩ := GlobalTheory.Unf.LinkGram.exists_inv_of_rank_one h.1 h.1 l.τ (lnk_tau_ne h l)
  have h1 : IsHalf (cA D e) (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj L S (l.κ S w)) :=
    half_smul _ (half_mul_left _ (half_mul_right (half_adj hh) _))
  rw [Lnk.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj_ofAdj] at h1
  have h2 := half_mul_left (rat σ : Mx D L.rank L.rank) h1
  rwa [← Matrix.mul_assoc, ← rat_mul, hστ, rat_one, Matrix.one_mul] at h2

theorem kappa_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → ∀ (L S : HSp D) (ζ ζ' : Fin L.rank → D.host.E), IsLineVec L ζ' → ∀ (l : Lnk L ζ L ζ') (Λ : AddSubgroup (WO S L)) (Ξ : WO L S → ℂ), IsLatVac (heisO ψ S L) Λ (fun w => star (Ξ (l.κ S w))) → ∀ w ∈ Λ, heisO ψ L S (2 • l.κ S w) Ξ = Ξ ∧ ∀ e, IsSplitIdem D e → IsHalf e (l.κ S w) → heisO ψ L S (l.κ S w) Ξ = Ξ := by
  intro D ψ hψ L S ζ ζ' h l Λ Ξ hv w hw
  refine ⟨?_, fun e he hh => ?_⟩
  · have e2 : (2 • l.κ S w : WO L S) = l.κ S (2 • w) := by rw [two_nsmul, two_nsmul, kap_add h l]
    rw [e2]
    exact kap_heis ψ hψ h l S Ξ _ (hv.1 w hw)
  · exact kap_heis ψ hψ h l S Ξ w (hv.2 (cA D e) (split_conj he) w hw (kap_half h l S hh))

end GlobalTheory.KapVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineHomTransportLatticeVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_line_hom_transport_lattice_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → ∀ (L S : HSp D) (ζ ζ' : Fin L.rank → D.host.E), IsLineVec L ζ' → ∀ (l : Lnk L ζ L ζ') (Λ : AddSubgroup (WO S L)) (Ξ : WO L S → ℂ), IsLatVac (heisO ψ S L) Λ (fun w => star (Ξ (l.κ S w))) → ∀ w ∈ Λ, heisO ψ L S (2 • l.κ S w) Ξ = Ξ ∧ ∀ e, IsSplitIdem D e → IsHalf e (l.κ S w) → heisO ψ L S (l.κ S w) Ξ = Ξ := by
  first | exact @GlobalTheory.KapVac.kappa_vac | exact GlobalTheory.KapVac.kappa_vac | (intros; apply GlobalTheory.KapVac.kappa_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCoreComponentMemDepthLatticeGridCore
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCoreComponentMemDepthLatticeGridCore
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LatSandwich

variable {D : D7}

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem rat_mul_tmul_mul {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (X : Matrix (Fin l) (Fin m) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (p : AF D.host.F) :
    rat A ⬝ (Matrix.of fun i j => p ⊗ₜ[D.host.F] X i j : Mx D l m) ⬝ rat B =
      Matrix.of fun i j => p ⊗ₜ[D.host.F] (A * X * B) i j := by
  ext i j
  simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, incA_eq, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← TensorProduct.tmul_sum]

theorem sandwich_hatMx {k l m n : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin l) (Fin m) D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (h : ∀ x ∈ M, A * x * B ∈ M') {z : Mx D l m} (hz : z ∈ hatMx M) :
    rat A ⬝ z ⬝ rat B ∈ hatMx M' := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    rw [rat_mul_tmul_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, _, h x hx, rfl⟩
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem sandwich_homLat {k l m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin l → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₂' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ₂') (hB : ∀ y ∈ Λ₂, B *ᵥ y ∈ Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) : ∀ x ∈ 𝔪 • homLat Λ Λ', A * x * B ∈ 𝔪 • homLat Λ₂ Λ₂' := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr x hx => ?_) (fun x y hx hy => ?_)
  · have e : A * (r • x) * B = r • (A * x * B) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e]
    refine Submodule.smul_mem_smul hr fun y hy => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hA _ (hx _ (hB y hy))
  · rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy

theorem sandwich_entry {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E)
    (a : D.host.E) (t : Fin l → D.host.E) (r : Fin m → D.host.E) (i : Fin k) (j : Fin n) :
    (A * Matrix.of (fun i j => a * t i * r j) * B) i j = a * (A *ᵥ t) i * ∑ m, r m * B m j := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sandwich_latO {S T S' T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)} (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (B : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT')
    (hB : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ k, star (s' k) * S'.gram k j = ∑ m, (∑ k, star (s k) * S.gram k m) * B m j)
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {w : WO S T} (hw : w ∈ latO S T LS LT P) :
    (rat A ⬝ w ⬝ rat B : WO S' T') ∈ latO S' T' LS' LT' P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', e⟩ := hB s hs
    have e1 : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
        Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
          (Matrix.of (fun i j => a * t i * ∑ k, star (s k) * S.gram k j) : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j := rfl
    rw [e1, rat_mul_tmul_mul]
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s', hs', A *ᵥ t, hA t ht, ?_⟩
    ext i j
    simp only [Matrix.of_apply]
    rw [sandwich_entry, e j]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) {y : Fin A.rank → D.host.E} (hy : y ∈ Λ) :
    M *ᵥ y ∈ d.lat Λ 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).val.zero_mem, by rw [hM, Matrix.mulVec_zero, add_zero]⟩

theorem orthogonalSumAuxiliaryVectors_projection_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) (hiso : Mᴴ * B.gram * M = A.gram)
    {x : Fin B.rank → D.host.E} (hx : x ∈ d.lat Λ 𝔟) : (A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ x ∈ Λ := by
  obtain ⟨y, hy, u, -, rfl⟩ := hx
  have h1 : A.gram⁻¹ * (Mᴴ * B.gram) * M = 1 := by
    rw [Matrix.mul_assoc, hiso, Matrix.nonsing_inv_mul _ (gram_isUnit_det A)]
  have h2 : A.gram⁻¹ * (Mᴴ * B.gram) * d.a = 0 := by
    have := d.perp
    rw [cT_sig, ← hM] at this
    rw [Matrix.mul_assoc, this, Matrix.mul_zero]
  rw [← hM, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h2, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero]
  exact hy

theorem proj_form {A B : HSp D} (M : Matrix (Fin B.rank) (Fin A.rank) D.host.E) (s : Fin B.rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j = ∑ m, (∑ k, star (s k) * B.gram k m) * M m j := by
  have e1 : (A.gram⁻¹ * (Mᴴ * B.gram))ᴴ * A.gram = B.gram * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, gram_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det A),
      Matrix.mul_one]
  have e2 : (fun j => ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j) =
      star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have e3 : (fun j => ∑ m, (∑ k, star (s k) * B.gram k m) * M m j) = (star s ᵥ* B.gram) ᵥ* M := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have key : star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram = (star s ᵥ* B.gram) ᵥ* M := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul]
  exact congrFun (e2.trans (key.trans e3.symm)) j

end GlobalTheory.LatSandwich

namespace GlobalTheory.AscFin

open GlobalTheory.LatSandwich

theorem pcBF_core_mem_latCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀,
    ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 ∈ latCore G (2 * ρ + 1) := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h u hu
  simp only [pcBF, piecesOf, AddSubgroup.mem_comap, AddMonoidHom.coe_comp, Function.comp_apply] at hu
  rw [OrthDec.resS_apply]

  have key : rat (F.dJ ρ h).q0 ⬝ (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ⬝ rat ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      u ⬝ (F.oB ρ h).jA := by
    rw [rat_mul, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply]
    change (F.dJ ρ h).p0 ⬝ ((F.dJ ρ h).j0 ⬝ u ⬝ (F.dB ρ h).p0) ⬝ ((F.dB ρ h).j0 ⬝ (F.oB ρ h).jA) = _
    simp only [← Matrix.mul_assoc]
    rw [HypDec.p0_j0, Matrix.one_mul, Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← key]

  have lat1 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  have lat2 : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat (2 * ρ + 2) (by omega) h
  have iso2 : ((F.dB ρ h).i₀ * (F.oB ρ h).iA)ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      (G.V (.core (2 * ρ + 2))).gram := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (F.oB ρ h).iAᴴ * ((F.dB ρ h).i₀ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * (F.dB ρ h).i₀) * (F.oB ρ h).iA := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [(F.dB ρ h).iso, (F.oB ρ h).isoA]

  have hA : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), (F.dJ ρ h).q0 *ᵥ t ∈ G.Λ (.core (2 * ρ + 1)) := fun t ht =>
    orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aJ ρ h) (F.dJ ρ h).iso (lat1 ▸ ht)

  have hB1 : ∀ y ∈ G.Λ (.core (2 * ρ + 2)), ((F.dB ρ h).i₀ * (F.oB ρ h).iA) *ᵥ y ∈ G.Λ (.grid (2 * ρ + 2) 0) :=
    fun y hy => lat2 ▸ orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice _ _ _ (hF.aB ρ h) hy

  have hB : ∀ s ∈ (G.Λ (.grid (2 * ρ + 2) 0) : Set (Fin (negSp (G.V (.grid (2 * ρ + 2) 0))).rank → D.host.E)),
      ∃ s' ∈ (G.Λ (.core (2 * ρ + 2)) : Set (Fin (negSp (G.V (.core (2 * ρ + 2)))).rank → D.host.E)), ∀ j,
        ∑ k, star (s' k) * (negSp (G.V (.core (2 * ρ + 2)))).gram k j =
          ∑ m, (∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k m) * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) m j := by
    intro s hs
    rw [SetLike.mem_coe, lat2] at hs
    refine ⟨_, orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aB ρ h) iso2 hs, fun j => ?_⟩
    simp only [negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_mul]
    rw [proj_form]
  have hu1 : (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈ latO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := hu.1
  have hu2 : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈
      hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) := hu.2
  refine ⟨?_, fun e he => ?_⟩
  · have h1 := sandwich_latO (S' := negSp (G.V (.core (2 * ρ + 2)))) (T' := G.V (.core (2 * ρ + 1)))
      (LS' := (G.Λ (.core (2 * ρ + 2)) : Set _)) (LT' := (G.Λ (.core (2 * ρ + 1)) : Set _)) _ _ hA hB _ hu1
    exact h1
  · have h2 := sandwich_hatMx _ _ (sandwich_homLat _ _ hA hB1 G.modul) (hu2 e he)
    rw [Matrix.mul_smul, Matrix.smul_mul] at h2
    exact h2

end GlobalTheory.AscFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCoreComponentMemDepthLatticeGridCoreStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_coreComponent_mem_depthLatticeGridCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 ∈ latCore G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.pcBF_core_mem_latCore | exact GlobalTheory.AscFin.pcBF_core_mem_latCore | (intros; apply GlobalTheory.AscFin.pcBF_core_mem_latCore <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoxDepthDataMulLineVacuaBesselLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.BoxBF

theorem isHalf_mul {D : D7} {m n k : ℕ} {e : AE D} {u : Mx D m n} (h : IsHalf e u) (M : Mx D n k) : IsHalf e (u ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem main : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ Ξ₁ Ξ₂, VacG W.ψ _ _ (latCore G (2 * ρ + 1)) Ξ₁ → IsThetaFunO W.ψ _ _ Ξ₂ →
    VacG W.ψ _ _ (lineLat F ρ) (fun w => star (Ξ₂ ((F.lnk ρ).κ _ w))) → VacG W.ψ _ _ (pcBF W F ρ h).Γ₀ ((F.oB ρ h).boxS _ Ξ₁ Ξ₂) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h Ξ₁ Ξ₂ h1 h2 h3
  have hn : ∀ x, ‖W.ψ x‖ = 1 := W.ψ_std.1.2.1
  refine ⟨(F.oB ρ h).isThetaFunO_boxS h1.1 h2, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw, hw'⟩ := GlobalTheory.T.besselStep_lineComponent_eq_kappa_lattice_point D hq T L μ0 hL sc G W M hM F hF ρ h u hu
    rw [OrthDec.heisO_boxS, map_nsmul, Prod.smul_fst, Prod.smul_snd,
      h1.2.1 _ (GlobalTheory.T.besselStep_coreComponent_mem_depthLatticeGridCore D hq T L μ0 hL sc G W M hM F hF ρ h u hu), hw',
      (GlobalTheory.T.linked_line_hom_transport_lattice_vacua D W.ψ hn _ _ _ _ (F.line ρ) (F.lnk ρ) _ Ξ₂ h3.2 w hw).1]
  · intro e he u hu hh
    obtain ⟨w, hw, hw'⟩ := GlobalTheory.T.besselStep_lineComponent_eq_kappa_lattice_point D hq T L μ0 hL sc G W M hM F hF ρ h u hu
    have ha : IsHalf e ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 := isHalf_mul hh _
    have hb : IsHalf e ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 := isHalf_mul hh _
    rw [OrthDec.heisO_boxS, h1.2.2 e he _ (GlobalTheory.T.besselStep_coreComponent_mem_depthLatticeGridCore D hq T L μ0 hL sc G W M hM F hF ρ h u hu) ha, hw']
    rw [hw'] at hb
    rw [(GlobalTheory.T.linked_line_hom_transport_lattice_vacua D W.ψ hn _ _ _ _ (F.line ρ) (F.lnk ρ) _ Ξ₂ h3.2 w hw).2 e he hb]

end GlobalTheory.AscFin.BoxBF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoxDepthDataMulLineVacuaBesselLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxDepthData_mul_lineVacua_besselLevel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ Ξ₁ Ξ₂, VacG W.ψ _ _ (latCore G (2 * ρ + 1)) Ξ₁ → IsThetaFunO W.ψ _ _ Ξ₂ → VacG W.ψ _ _ (lineLat F ρ) (fun w => star (Ξ₂ ((F.lnk ρ).κ _ w))) → VacG W.ψ _ _ (pcBF W F ρ h).Γ₀ ((F.oB ρ h).boxS _ Ξ₁ Ξ₂) := by
  first | exact @GlobalTheory.AscFin.BoxBF.main | exact GlobalTheory.AscFin.BoxBF.main | (intros; apply GlobalTheory.AscFin.BoxBF.main <;> assumption)
end
