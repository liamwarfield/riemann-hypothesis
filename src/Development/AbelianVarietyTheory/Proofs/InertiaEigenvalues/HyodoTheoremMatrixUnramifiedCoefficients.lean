module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToMatrixRepOf
noncomputable section

namespace GlobalTheory.PMon

variable {F G ι : Type} [Field F] [Group G] [Fintype ι] [DecidableEq ι]

def repOf (ρ₀ : G →* GL ι F) : Representation F G (ι → F) where
  toFun g := Matrix.toLin' (ρ₀ g : Matrix ι ι F)
  map_one' := by simp; rfl
  map_mul' g h := by simp [Matrix.toLin'_mul]; rfl

@[simp] theorem repOf_apply (ρ₀ : G →* GL ι F) (g : G) (v : ι → F) :
    repOf ρ₀ g v = (ρ₀ g : Matrix ι ι F).mulVec v := rfl

theorem toMatrix_repOf (ρ₀ : G →* GL ι F) (g : G) :
    LinearMap.toMatrix (Pi.basisFun F ι) (Pi.basisFun F ι) (repOf ρ₀ g) = (ρ₀ g : Matrix ι ι F) := by
  rw [LinearMap.toMatrix_eq_toMatrix']
  exact LinearMap.toMatrix'_toLin' _

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCoordsUnramifiedFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCoordsUnramifiedFrobenius
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem coef_unr_continuous : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) ∧ (∀ k, fr l r (ω k) = ω k) ∧
    ∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k) := by
  intro l _ r hr
  obtain ⟨E, ω, -, -, -, hω, hli, hspan, hdet⟩ := UnrDeg.fixed_field_deg l r hr
  refine ⟨ω, Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, fun m k => rfl, hω, ?_⟩
  intro X _ x hx hcont

  set v : Fin r → Om l := fun k => ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l) with hv
  have hliv : LinearIndependent ℚ_[l] v := by
    have := hli.map' (MaximalUnramifiedExtension l).val.toLinearMap (LinearMap.ker_eq_bot.2 (fun a b h => Subtype.ext h))
    exact this
  set ψ : (Fin r → ℚ_[l]) →ₗ[ℚ_[l]] Om l := Fintype.linearCombination ℚ_[l] v with hψ
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    rw [hψ, Fintype.linearCombination_apply] at hg
    funext i
    exact Fintype.linearIndependent_iff.1 hliv g hg i
  let e := LinearEquiv.ofInjective ψ hinj
  haveI : FiniteDimensional ℚ_[l] ↥(LinearMap.range ψ) := LinearEquiv.finiteDimensional e
  have hmem : ∀ t, ((x t : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ LinearMap.range ψ := by
    intro t
    obtain ⟨a, ha⟩ := hspan (x t) (hx t)
    refine ⟨a, ?_⟩
    rw [hψ, Fintype.linearCombination_apply, ha]
    simp [hv]
  refine ⟨fun t => e.symm ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩, ?_, ?_⟩
  · exact (LinearMap.continuous_of_finiteDimensional (e.symm : ↥(LinearMap.range ψ) →ₗ[ℚ_[l]] (Fin r → ℚ_[l]))).comp
      (hcont.subtype_mk _)
  · intro t m
    have key : ψ (e.symm ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩) = ((x t : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      have h1 := congrArg Subtype.val (e.apply_symm_apply ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩)
      rw [LinearEquiv.ofInjective_apply] at h1
      exact h1
    set a := e.symm ⟨((x t : ↥(MaximalUnramifiedExtension l)) : Om l), hmem t⟩
    have hxt : x t = ∑ k, a k • ω k := by
      apply Subtype.ext
      rw [← key, hψ, Fintype.linearCombination_apply]
      simp [hv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hxt, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, fr_q, mul_comm]
    rfl

end GlobalTheory.PMon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCoordsUnramifiedFrobeniusStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_coords_unramified_frobenius : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) ∧ (∀ k, fr l r (ω k) = ω k) ∧
    ∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k) := by
  first | exact @GlobalTheory.PMon.coef_unr_continuous | exact GlobalTheory.PMon.coef_unr_continuous | (intros; apply GlobalTheory.PMon.coef_unr_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundarySemistableTensorColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundarySemistableTensorColumns
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMonCob

theorem coboundary_cols (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P) :
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  intro h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] (ι → Bst P) :=
    TensorProduct.lift (LinearMap.mk₂ ℚ_[l] (fun (v : ι → ℚ_[l]) (a : Bst P) (x : ι) => v x • a)
      (fun v w a => by funext x; simp [add_smul])
      (fun c v a => by funext x; simp [mul_smul])
      (fun v a a' => by funext x; simp [smul_add])
      (fun c v a => by funext x; simp [smul_comm c]))
  have hΦ : ∀ (v : ι → ℚ_[l]) (a : Bst P), Φ (v ⊗ₜ a) = fun x => v x • a := fun v a => by
    simp [Φ]
  have hst : ∀ (g : ↥(GK K)) (y : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
      Φ (stRep P (repOf ρ₀) g y) = ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec
        (fun x => actSt P (g : GQ l) (Φ y x)) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => funext x; simp [Matrix.mulVec, dotProduct]
    | tmul v a =>
      rw [stRep_tmul, repOf_apply, hΦ, hΦ]
      funext x
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, map_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]
    | add y z hy hz =>
      rw [map_add (f := _), map_add (f := _), hy, hz, ← Matrix.mulVec_add]
      congr 1
      funext x
      simp
  refine ⟨Φ b, fun g => ?_⟩
  have := congrArg Φ (h g)
  rw [map_sub, hst, hΦ] at this
  rw [← this]
  funext x
  simp [Algebra.algebraMap_eq_smul_one]

end GlobalTheory.PMonCob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundarySemistableTensorColumnsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_semistableTensor_columns : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (b : (ι → ℚ_[l]) ⊗[ℚ_[l]] Bst P),
    (∀ g, c₀ g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P (repOf ρ₀) g b - b) →
    ∃ β : ι → Bst P, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec (fun x => actSt P (g : GQ l) (β x)) - β := by
  first | exact @GlobalTheory.PMonCob.coboundary_cols | exact GlobalTheory.PMonCob.coboundary_cols | (intros; apply GlobalTheory.PMonCob.coboundary_cols <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryRestrictionScalarsBlockZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryRestrictionScalarsBlockZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon
open Matrix

theorem blockDiagonal_map_mulVec {R S : Type*} [CommSemiring R] [CommSemiring S] {n : Type} [Fintype n]
    [DecidableEq n] {r : ℕ} (D : Fin r → Matrix n n R) (f : R →+* S) (w : n × Fin r → S) (i : n) (k : Fin r) :
    ((blockDiagonal D).map f *ᵥ w) (i, k) = ((D k).map f *ᵥ fun j => w (j, k)) i := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type, map_apply, blockDiagonal_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [apply_ite f]

theorem ks_algebraMap_q {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    algebraMap ℚ_[l] (Bst P) q = ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) := by
  simp only [ks, RingHom.comp_apply]
  rw [Polynomial.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem coboundary_block_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ), 0 < r →
    ∀ (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]) (β : n × Fin r → Bst P),
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec
        (fun x => actSt P (g : GQ l) (β x)) - β) →
    ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) =
      ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  intro l _ P n _ _ K r hr σ ρ₀ p c c₀ β hK hconj hpc hβ
  set M : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
  refine ⟨fun i => (M.map (ks P) *ᵥ β) (i, ⟨0, hr⟩), fun g => ?_⟩
  have hD : M.map (ks P) *ᵥ (fun x => actSt P (g : GQ l) (β x)) =
      fun x => actSt P (g : GQ l) ((M.map (ks P) *ᵥ β) x) := by
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [act_ks P g (hK x j)]
  have hC : M.map (ks P) * (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) =
      (Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))).map (ks P) * M.map (ks P) := by
    have e : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) =
        ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).map (ks P) := by
      rw [Matrix.map_map]; congr 1; funext q; exact ks_algebraMap_q P q
    rw [e, ← Matrix.map_mul, hconj g, Matrix.map_mul]
  have h1 : (fun x : n × Fin r => ks P (fr l x.2 (c g x.1))) =
      M.map (ks P) *ᵥ (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) := by
    funext x
    have e : (ks P) ∘ (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) = fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x) := by
      funext y; exact (ks_algebraMap_q P _).symm
    rw [← congrFun (hpc g) x, RingHom.map_mulVec, e]
  have hv : (fun x : n × Fin r => ks P (fr l x.2 (c g x.1))) =
      (Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))).map (ks P) *ᵥ
        (fun x => actSt P (g : GQ l) ((M.map (ks P) *ᵥ β) x)) - M.map (ks P) *ᵥ β := by
    rw [h1, hβ g, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hC, ← Matrix.mulVec_mulVec, hD]
  funext i
  have h := congrFun hv (i, ⟨0, hr⟩)
  rw [Pi.sub_apply, blockDiagonal_map_mulVec] at h
  exact h

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryRestrictionScalarsBlockZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_restrictionScalars_block_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ), 0 < r →
    ∀ (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]) (β : n × Fin r → Bst P),
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] (Bst P) (c₀ g x)) =
      ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P))).mulVec
        (fun x => actSt P (g : GQ l) (β x)) - β) →
    ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) =
      ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  first | exact @GlobalTheory.PMon.coboundary_block_zero | exact GlobalTheory.PMon.coboundary_block_zero | (intros; apply GlobalTheory.PMon.coboundary_block_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamTrivialRationalCocycleRestrictionScalars
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamTrivialRationalCocycleRestrictionScalars
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

open Matrix

namespace GlobalTheory.PMon.DRvec

theorem blockDiag_mulVec {R : Type*} [CommRing R] {n o : Type} [Fintype n] [Fintype o] [DecidableEq o]
    (M : o → Matrix n n R) (v : n × o → R) (i : n) (m : o) :
    (Matrix.blockDiagonal M *ᵥ v) (i, m) = (M m *ᵥ fun j => v (j, m)) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type, ite_mul, Finset.sum_ite_eq]

theorem kd_q {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] P.R.BdR q := by
  show algebraMap (Om l) P.R.BdR (algebraMap ↥(MaximalUnramifiedExtension l) (Om l) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)) = _
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem ratCocycle_trivial : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) =
      (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) →
    ∃ β : n × Fin r → P.R.BdR, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
        (fun x => P.actQdR (g : GQ l) (β x)) - β := by
  intro l _ P n _ _ K r σ ρ₀ p c c₀ hp hconj hpc hdr
  choose b hb using hdr
  let pG : GL (n × Fin r) P.R.BdR := Matrix.GeneralLinearGroup.map (kd P) p
  let β' : n × Fin r → P.R.BdR := fun x => b x.2 x.1
  have hinvmul : ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) = 1 := pG.inv_mul
  have hmulinv : (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) = 1 := pG.mul_inv
  have hpG : ∀ i j, (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i j =
      kd P ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j) := fun i j => rfl
  refine ⟨((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *ᵥ β', fun g => ?_⟩
  set pinv := ((pG⁻¹ : GL (n × Fin r) P.R.BdR) : Matrix (n × Fin r) (n × Fin r) P.R.BdR) with hpinv
  set pM := (pG : Matrix (n × Fin r) (n × Fin r) P.R.BdR) with hpM
  set BD := Matrix.blockDiagonal (fun m : Fin r => matD P σ m g) with hBD
  set R0 := (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR) with hR0

  have hfix : ∀ i j, P.actQdR (g : GQ l) (pinv i j) = pinv i j := by
    let φ : P.R.BdR →+* P.R.BdR := (P.actQdR (g : GQ l)).toAlgHom.toRingHom
    have h1 : Matrix.GeneralLinearGroup.map φ pG = pG := by
      ext i j
      show φ (kd P _) = kd P _
      exact act_kd P g (hp i j)
    have h2 : Matrix.GeneralLinearGroup.map φ pG⁻¹ = pG⁻¹ := by rw [map_inv, h1]
    intro i j
    exact congrArg (fun A : GL (n × Fin r) P.R.BdR => (A : Matrix (n × Fin r) (n × Fin r) P.R.BdR) i j) h2
  have hactv : (fun x => P.actQdR (g : GQ l) ((pinv *ᵥ β') x)) = pinv *ᵥ (fun x => P.actQdR (g : GQ l) (β' x)) := by
    funext x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hfix]

  have hd : pM * R0 = BD * pM := by
    have h1 : pM = (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).map (kd P) := rfl
    have h2 : R0 = ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).map (kd P) := by
      ext i j; simp [hR0, kd_q]
    have h3 : BD = (Matrix.blockDiagonal fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (kd P) := by
      rw [hBD, Matrix.blockDiagonal_map _ _ (map_zero (kd P))]
      rfl
    rw [h1, h2, h3, ← Matrix.map_mul, ← Matrix.map_mul, hconj g]
  have hR : R0 * pinv = pinv * BD := by
    calc R0 * pinv = pinv * (pM * R0) * pinv := by rw [← Matrix.mul_assoc, hinvmul, Matrix.one_mul]
    _ = pinv * (BD * pM) * pinv := by rw [hd]
    _ = pinv * BD := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hmulinv, Matrix.mul_one]
  have hvec : (fun x : n × Fin r => kd P (fr l x.2 (c g x.1))) = pM *ᵥ fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x) := by
    funext x
    have h := congrArg (fun v => kd P (v x)) (hpc g)
    simp only [Matrix.mulVec, dotProduct] at h ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, kd_q, hpG]
  have hbt : (fun x : n × Fin r => kd P (fr l x.2 (c g x.1))) = BD *ᵥ (fun x => P.actQdR (g : GQ l) (β' x)) - β' := by
    funext ⟨i, m⟩
    rw [Pi.sub_apply, hBD, blockDiag_mulVec]
    exact congrFun (hb m g) i
  rw [hactv, Matrix.mulVec_mulVec, hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, ← hbt, hvec, Matrix.mulVec_mulVec,
    hinvmul, Matrix.one_mulVec]

end GlobalTheory.PMon.DRvec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamTrivialRationalCocycleRestrictionScalarsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_trivial_rational_cocycle_restrictionScalars : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) =
      (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) →
    ∃ β : n × Fin r → P.R.BdR, ∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
        (fun x => P.actQdR (g : GQ l) (β x)) - β := by
  first | exact @GlobalTheory.PMon.DRvec.ratCocycle_trivial | exact GlobalTheory.PMon.DRvec.ratCocycle_trivial | (intros; apply GlobalTheory.PMon.DRvec.ratCocycle_trivial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleRestrictionScalarsRationalCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleRestrictionScalarsRationalCoords
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.PMon.cocycle_rat_coords : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) →
    ∀ g h, c₀ (g * h) = c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h) := by
  intro l _ n _ _ K r σ ρ₀ p c c₀ hint hc0 hc g h
  set f : ℚ_[l] →+* ↥(MaximalUnramifiedExtension l) := algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) with hf
  set P : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) with hP

  have hC : (fun x : n × Fin r => fr l x.2 (c (g * h) x.1)) =
      (fun x : n × Fin r => fr l x.2 (c g x.1)) +
        (Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))).mulVec
          (fun x : n × Fin r => fr l x.2 (c h x.1)) := by
    funext ⟨i, m⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hc, Pi.add_apply, map_add (f := _), Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.blockDiagonal_apply, Matrix.map_apply, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single m]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  have key : P.mulVec (fun x => f (c₀ (g * h) x)) =
      P.mulVec (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    rw [hc0, hC, ← hc0 g, ← hc0 h, Matrix.mulVec_mulVec, ← hint g]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add]
    congr 1
    congr 1
    funext x
    simp only [Pi.add_apply, map_add, RingHom.map_mulVec, Function.comp_def]
  have inj : (fun x => f (c₀ (g * h) x)) =
      (fun x => f ((c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h)) x)) := by
    have := congrArg (fun v => ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec v) key
    simp only [hP, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
    exact this
  funext x
  exact f.injective (congrFun inj x)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleRestrictionScalarsRationalCoordsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_restrictionScalars_rational_coords : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l))
    (c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l)) (c₀ : ↥(GK K) → n × Fin r → ℚ_[l]),
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1)) →
    (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) →
    ∀ g h, c₀ (g * h) = c₀ g + (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).mulVec (c₀ h) := by
  first | exact @GlobalTheory.PMon.cocycle_rat_coords | exact GlobalTheory.PMon.cocycle_rat_coords | (intros; apply GlobalTheory.PMon.cocycle_rat_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalFormUnramifiedRestrictionScalars
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalFormUnramifiedRestrictionScalars
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem intertwine_mul {G ι R S : Type} [Monoid G] [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (B : G → Matrix ι ι S) (hB1 : B 1 = 1)
    (hBm : ∀ g h, B (g * h) = B g * B h) (p : GL ι S) (T : G → Matrix ι ι R)
    (hT : ∀ g, (p : Matrix ι ι S) * (T g).map f = B g * p) :
    T 1 = 1 ∧ ∀ g h, T (g * h) = T g * T h := by
  have hinj : Function.Injective (fun M : Matrix ι ι R => M.map f) := Matrix.map_injective hf
  refine ⟨?_, fun g h => ?_⟩
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T 1).map f = (p : Matrix ι ι S) * (1 : Matrix ι ι R).map f
    rw [hT, hB1, one_mul, Matrix.map_one f (map_zero f) (map_one f), mul_one]
  · apply hinj
    apply (Units.mul_right_inj p).1
    show (p : Matrix ι ι S) * (T (g * h)).map f = (p : Matrix ι ι S) * (T g * T h).map f
    calc (p : Matrix ι ι S) * (T (g * h)).map f = B g * B h * p := by rw [hT, hBm]
      _ = B g * ((p : Matrix ι ι S) * (T h).map f) := by rw [mul_assoc, hT]
      _ = ((p : Matrix ι ι S) * (T g).map f) * (T h).map f := by rw [← mul_assoc, hT]
      _ = (p : Matrix ι ι S) * (T g * T h).map f := by rw [Matrix.map_mul, mul_assoc]

theorem exists_ratForm : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)), IsRat r σ →
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) → (∀ k, fr l r (ω k) = ω k) →
    (∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k)) →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) ∧
      (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) ∧
      ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) →
        (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) →
        ∃ c₀ : ↥(GK K) → n × Fin r → ℚ_[l], Continuous c₀ ∧ ∀ g,
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1) := by
  intro l _ n _ _ K r σ ω W hσ hW hω hcoef
  classical

  let P0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  let Q0 : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
    Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) ((W⁻¹ : GL (Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l))
  have hPQ : P0 * Q0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  have hQP : Q0 * P0 = 1 := by
    simp only [P0, Q0]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_kronecker_one]
  let p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l) := ⟨P0, Q0, hPQ, hQP⟩
  have hp : ∀ i m j k, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) (i, m) (j, k) =
      if i = j then (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k else 0 := by
    intro i m j k
    show P0 (i, m) (j, k) = _
    simp only [P0, Matrix.kronecker_apply, Matrix.one_apply]
    split_ifs <;> simp

  have hA : ∀ (i j : n) (k : Fin r), ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
      fr l m ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) =
        ∑ k', (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k' * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k') := by
    intro i j k
    refine hcoef ↥(GK K) (fun g => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) (fun g => ?_) ?_
    · rw [map_mul, hσ.rat, hω]
    · show Continuous fun g => (((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) * ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l)
      exact (hσ.cont i j).mul continuous_const
  choose A hAc hA using hA
  let T : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ℚ_[l] := fun g x y => A x.1 y.1 y.2 g x.2
  let B : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := fun g =>
    Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
  have hB1 : B 1 = 1 := by
    simp only [B, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.blockDiagonal_one
  have hBm : ∀ g h, B (g * h) = B g * B h := by
    intro g h
    simp only [B, map_mul, Units.val_mul, Matrix.map_mul]
    rw [Matrix.blockDiagonal_mul]
  have hT : ∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * (T g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
      B g * p := by
    intro g
    refine Matrix.ext ?_
    rintro ⟨i, m⟩ ⟨j, k⟩
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [hp, B, T, Matrix.map_apply, Matrix.blockDiagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    refine (show _ = ∑ x, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m x * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (A i j k g x)
      from rfl).trans ?_
    rw [← hA i j k g m, map_mul]
    symm
    simp [hW]
  obtain ⟨hT1, hTm⟩ := intertwine_mul (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).injective
    B hB1 hBm p T hT
  let T' : ↥(GK K) →* Matrix (n × Fin r) (n × Fin r) ℚ_[l] :=
    { toFun := T, map_one' := hT1, map_mul' := hTm }
  refine ⟨T'.toHomUnits, p, ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, k'⟩ ⟨j, k⟩
    exact (continuous_apply k').comp (hAc i j k)
  · rintro ⟨i, m⟩ ⟨j, k⟩
    apply hσ.le
    rw [hp]
    split_ifs
    · rw [hW]; exact fr_comm (hω k) m
    · exact map_zero _
  · intro g
    exact hT g
  · intro c hc hcc
    have hC : ∀ i : n, ∃ a : ↥(GK K) → Fin r → ℚ_[l], Continuous a ∧ ∀ g (m : Fin r),
        fr l m (c g i) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a g k) :=
      fun i => hcoef ↥(GK K) (fun g => c g i) (fun g => hc g i) (hcc i)
    choose a hac ha using hC
    refine ⟨fun g x => a x.1 g x.2, continuous_pi fun x => (continuous_apply x.2).comp (hac x.1), fun g => ?_⟩
    funext ⟨i, m⟩
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    simp only [hp, ite_mul, zero_mul]
    rw [Fintype.sum_eq_single i (fun x hx => by simp [Ne.symm hx])]
    simp only [if_true]
    rw [ha i g m]

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalFormUnramifiedRestrictionScalarsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_form_unramified_restrictionScalars : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (W : GL (Fin r) ↥(MaximalUnramifiedExtension l)), IsRat r σ →
    (∀ m k : Fin r, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k = fr l m (ω k)) → (∀ k, fr l r (ω k) = ω k) →
    (∀ (X : Type) [TopologicalSpace X] (x : X → ↥(MaximalUnramifiedExtension l)), (∀ t, fr l r (x t) = x t) →
      Continuous (fun t => ((x t : ↥(MaximalUnramifiedExtension l)) : Om l)) →
      ∃ a : X → Fin r → ℚ_[l], Continuous a ∧ ∀ t (m : Fin r),
        fr l m (x t) = ∑ k, (W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l)) m k * algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (a t k)) →
    ∃ (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l]) (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
      (∀ i j, Continuous fun g => (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j) ∧
      (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) ∧
      (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) ∧
      ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) →
        (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) →
        ∃ c₀ : ↥(GK K) → n × Fin r → ℚ_[l], Continuous c₀ ∧ ∀ g,
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)).mulVec (fun x => algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (c₀ g x)) =
            fun x => fr l x.2 (c g x.1) := by
  first | exact @GlobalTheory.PMon.exists_ratForm | exact GlobalTheory.PMon.exists_ratForm | (intros; apply GlobalTheory.PMon.exists_ratForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryTmulOfColumnDeRham
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryTmulOfColumnDeRham
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CobColumn

theorem coboundary_tmul_of_column : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (β : ι → P.R.BdR),
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun x => P.actQdR (g : GQ l) (β x)) - β) →
    ∃ b : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR, ∀ g,
      c₀ g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) (repOf ρ₀) g b - b := by
  intro l _ P K ι _ _ ρ₀ c₀ β h
  let Φ : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (ι → P.R.BdR) :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).toLinearMap ∘ₗ (TensorProduct.comm ℚ_[l] _ _).toLinearMap
  have hΦinj : Function.Injective Φ :=
    (piScalarRight ℚ_[l] ℚ_[l] P.R.BdR ι).injective.comp (TensorProduct.comm ℚ_[l] _ _).injective
  have hΦ : ∀ v b i, Φ (v ⊗ₜ b) i = algebraMap ℚ_[l] P.R.BdR (v i) * b := by
    intro v b i
    simp [Φ, piScalarRight_apply, piScalarRightHom_tmul, Algebra.smul_def]
  have hact : ∀ g v b, actVdR (P.PD K) (repOf ρ₀) g (v ⊗ₜ b) = repOf ρ₀ g v ⊗ₜ P.actQdR (g : GQ l) b := by
    intro g v b
    rw [← P.PD_actdR K g b]
    rfl
  refine ⟨∑ x, Pi.single x 1 ⊗ₜ β x, fun g => hΦinj ?_⟩
  funext i
  have hi := congrFun (h g) i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, hact, hΦ, repOf_apply, mul_one]
  rw [hi]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    rw [Finset.sum_eq_single x (fun y _ hy => by simp [Pi.single_eq_of_ne hy]) (by simp)]
    simp
  · rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx; simp [Pi.single_eq_of_ne' hx]
    · simp

end GlobalTheory.CobColumn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryTmulOfColumnDeRhamStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_tmul_of_column_deRham : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (ι : Type) [Fintype ι] [DecidableEq ι]
    (ρ₀ : ↥(GK K) →* GL ι ℚ_[l]) (c₀ : ↥(GK K) → ι → ℚ_[l]) (β : ι → P.R.BdR),
    (∀ g : ↥(GK K), (fun x => algebraMap ℚ_[l] P.R.BdR (c₀ g x)) =
      ((ρ₀ g : Matrix ι ι ℚ_[l]).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun x => P.actQdR (g : GQ l) (β x)) - β) →
    ∃ b : (ι → ℚ_[l]) ⊗[ℚ_[l]] P.R.BdR, ∀ g,
      c₀ g ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) = actVdR (P.PD K) (repOf ρ₀) g b - b := by
  first | exact @GlobalTheory.CobColumn.coboundary_tmul_of_column | exact GlobalTheory.CobColumn.coboundary_tmul_of_column | (intros; apply GlobalTheory.CobColumn.coboundary_tmul_of_column <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodMatrixRestrictionScalarsBlockDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodMatrixRestrictionScalarsBlockDiagonal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem unramifiedToBst_algebraMap_padic {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] (Bst P) q := by
  simp only [ks, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, Polynomial.algebraMap_apply]

theorem frobeniusSemistablePow_unramifiedToBst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    (phiSt P ^ m) (ks P c) = ks P (fr l m c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, add_comm, fr_add, fr_one]
    have := phiSt_algebraMap P (fr l m c)
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply] at this
    exact this

theorem frobeniusSemistablePow_galoisAction_comm {l : ℕ} [Fact l.Prime] (P : LocPrime l) (g : GQ l) (m : ℕ) (b : Bst P) :
    (phiSt P ^ m) (actSt P g b) = actSt P g ((phiSt P ^ m) b) := by
  induction m generalizing b with
  | zero => rfl
  | succ m ih => rw [pow_succ', AlgHom.mul_apply, ih, phiSt_actSt, AlgHom.mul_apply]

end GlobalTheory.PMon

namespace GlobalTheory.PMon

theorem inv_entries_mem_finiteExtension_unramified {l : ℕ} [Fact l.Prime] {N : Type} [Fintype N] [DecidableEq N] (K : FinExt l)
    (p : GL N ↥(MaximalUnramifiedExtension l)) (h : ∀ i j, (((p : Matrix N N ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) (i j : N) :
    ((((p⁻¹ : GL N ↥(MaximalUnramifiedExtension l)) : Matrix N N ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := by
  let S : Subfield ↥(MaximalUnramifiedExtension l) := K.1.toSubfield.comap (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))
  let A : Matrix N N S := Matrix.of fun i j => ⟨(p : Matrix N N ↥(MaximalUnramifiedExtension l)) i j, h i j⟩
  have hA : (S.subtype).mapMatrix A = (p : Matrix N N ↥(MaximalUnramifiedExtension l)) := by refine Matrix.ext fun i j => ?_; rfl
  have hmem : ((p : Matrix N N ↥(MaximalUnramifiedExtension l))⁻¹ i j) ∈ S := by
    rw [Matrix.inv_def, ← hA, ← RingHom.map_adjugate, ← RingHom.map_det]
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, Ring.inverse_eq_inv']
    exact S.mul_mem (S.inv_mem (A.det).2) (A.adjugate i j).2
  rw [Matrix.coe_units_inv]
  exact hmem

theorem period_resScalars : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l])
    (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) →
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    ∃ Q₀ : GL (n × Fin r) (Bst P), ∀ g : ↥(GK K),
      (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) *
        (Q₀ : Matrix (n × Fin r) (n × Fin r) (Bst P)).map (actSt P (g : GQ l)) = Q₀ := by
  intro l _ P n _ _ K r σ Q ρ₀ p h1 h2 h3
  classical
  let φm : Fin r → Bst P →+* Bst P := fun m => ((phiSt P ^ (m : ℕ) : Bst P →ₐ[ℚ_[l]] Bst P) : Bst P →+* Bst P)
  let Pu : GL (n × Fin r) (Bst P) := Units.map (RingHom.mapMatrix (m := n × Fin r) (ks P)).toMonoidHom p⁻¹
  let Du : GL (n × Fin r) (Bst P) := Units.map (Matrix.blockDiagonalRingHom n (Fin r) (Bst P)).toMonoidHom
    (MulEquiv.piUnits.symm fun m => Units.map (RingHom.mapMatrix (m := n) (φm m)).toMonoidHom Q)
  refine ⟨Pu * Du, fun g => ?_⟩
  set pv : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) with hpv
  have hPu : (Pu : Matrix (n × Fin r) (n × Fin r) (Bst P)) = pv.map (ks P) := rfl
  have hDu : (Du : Matrix (n × Fin r) (n × Fin r) (Bst P)) =
      Matrix.blockDiagonal fun m => (Q : Matrix n n (Bst P)).map (φm m) := rfl
  set act := actSt P (g : GQ l)

  have hPfix : (pv.map (ks P)).map act = pv.map (ks P) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact act_ks P g (inv_entries_mem_finiteExtension_unramified K p h2 i j)

  have hrel : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) * pv =
      pv * Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) := by
    have hp : pv * (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
      rw [hpv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hp' : (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * pv = 1 := by
      rw [hpv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc _ = pv * ((p : Matrix _ _ ↥(MaximalUnramifiedExtension l)) * (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map
            (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) * pv := by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]
      _ = _ := by rw [h3, Matrix.mul_assoc, Matrix.mul_assoc, hp', Matrix.mul_one]
  have hrelB := congrArg (fun M => M.map (ks P)) hrel
  simp only [Matrix.map_mul, Matrix.map_map] at hrelB
  have hks : (ks P) ∘ (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = algebraMap ℚ_[l] (Bst P) := funext (unramifiedToBst_algebraMap_padic P)
  rw [hks, Matrix.blockDiagonal_map _ _ (map_zero _)] at hrelB

  have hblock : ∀ m : Fin r, ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (ks P) *
      ((Q : Matrix n n (Bst P)).map (φm m)).map act = (Q : Matrix n n (Bst P)).map (φm m) := by
    intro m
    have e1 : ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (ks P) =
        ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).map (φm m) := by
      refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply, φm, AlgHom.coe_toRingHom]; exact (frobeniusSemistablePow_unramifiedToBst P m _).symm
    have e2 : ((Q : Matrix n n (Bst P)).map (φm m)).map act =
        ((Q : Matrix n n (Bst P)).map act).map (φm m) := by
      refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply, φm, AlgHom.coe_toRingHom, act]; exact (frobeniusSemistablePow_galoisAction_comm P _ m _).symm
    rw [e1, e2, ← Matrix.map_mul, h1 g]
  rw [Units.val_mul, hPu, hDu, Matrix.map_mul, hPfix, Matrix.blockDiagonal_map _ _ (map_zero _),
    ← Matrix.mul_assoc, hrelB, Matrix.mul_assoc, ← Matrix.blockDiagonal_mul]
  congr 2
  funext m
  exact hblock m

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodMatrixRestrictionScalarsBlockDiagonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodMatrix_restrictionScalars_blockDiagonal : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l])
    (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) →
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    ∃ Q₀ : GL (n × Fin r) (Bst P), ∀ g : ↥(GK K),
      (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) *
        (Q₀ : Matrix (n × Fin r) (n × Fin r) (Bst P)).map (actSt P (g : GQ l)) = Q₀ := by
  first | exact @GlobalTheory.PMon.period_resScalars | exact GlobalTheory.PMon.period_resScalars | (intros; apply GlobalTheory.PMon.period_resScalars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficients
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem hyodo_mat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)), IsRat r σ → (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) → (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) → (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) → (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) = (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) → ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) = ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  intro l _ P AI T n _ _ K r σ Q hσ hQ c hcr hcc hcoc hdR
  obtain ⟨ω, W, hW, hω, hcoef⟩ := GlobalTheory.T.exists_continuous_coords_unramified_frobenius l r hσ.pos
  obtain ⟨ρ₀, p, hρc, hpK, hint, hc₀⟩ := GlobalTheory.T.exists_rational_form_unramified_restrictionScalars l n K r σ ω W hσ hW hω hcoef
  obtain ⟨c₀, hc₀c, hpc⟩ := hc₀ c hcr hcc
  have hcoc₀ := GlobalTheory.T.cocycle_restrictionScalars_rational_coords l n K r σ ρ₀ p c c₀ hint hpc hcoc
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.T.periodMatrix_restrictionScalars_blockDiagonal l P n K r σ Q ρ₀ p hQ hpK hint
  have hsst : IsSst P (repOf ρ₀) :=
    GlobalTheory.T.isSemistable_of_invertible_periodMatrix_semistableRing l P AI T (n × Fin r) K (n × Fin r → ℚ_[l]) (Pi.basisFun ℚ_[l] _) (repOf ρ₀) Q₀
      (fun g => by rw [toMatrix_repOf]; exact hQ₀ g)
  obtain ⟨β, hβ⟩ := GlobalTheory.T.deRham_trivial_rational_cocycle_restrictionScalars l P n K r σ ρ₀ p c c₀ hpK hint hpc hdR
  obtain ⟨bd, hbd⟩ := GlobalTheory.T.coboundary_tmul_of_column_deRham l P K _ ρ₀ c₀ β hβ
  have hcontρ : ∀ v : n × Fin r → ℚ_[l], Continuous fun g => repOf ρ₀ g v := by
    intro v
    simp only [repOf_apply]
    refine continuous_pi fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => (hρc i j).mul continuous_const
  obtain ⟨bs, hbs⟩ := GlobalTheory.T.hyodo_statement l P AI T K (n × Fin r → ℚ_[l]) (repOf ρ₀) hcontρ hsst c₀ hc₀c
    hcoc₀ ⟨bd, hbd⟩
  obtain ⟨β', hβ'⟩ := GlobalTheory.T.coboundary_semistableTensor_columns l P K _ ρ₀ c₀ bs hbs
  exact GlobalTheory.T.coboundary_restrictionScalars_block_zero l P n K r hσ.pos σ ρ₀ p c c₀ β' hpK hint hpc hβ'

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoTheoremMatrixUnramifiedCoefficientsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyodo_theorem_matrix_unramifiedCoefficients : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)), IsRat r σ → (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → ∀ c : ↥(GK K) → n → ↥(MaximalUnramifiedExtension l), (∀ g i, fr l r (c g i) = c g i) → (∀ i, Continuous fun g => ((c g i : ↥(MaximalUnramifiedExtension l)) : Om l)) → (∀ g h, c (g * h) = c g + (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).mulVec (c h)) → (∀ m : ℕ, ∃ b : n → P.R.BdR, ∀ g : ↥(GK K), (fun i => kd P (fr l m (c g i))) = (matD P σ m g).mulVec (fun i => P.actQdR (g : GQ l) (b i)) - b) → ∃ b : n → Bst P, ∀ g : ↥(GK K), (fun i => ks P (c g i)) = ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (b i)) - b := by
  first | exact @GlobalTheory.PMon.hyodo_mat | exact GlobalTheory.PMon.hyodo_mat | (intros; apply GlobalTheory.PMon.hyodo_mat <;> assumption)
end
