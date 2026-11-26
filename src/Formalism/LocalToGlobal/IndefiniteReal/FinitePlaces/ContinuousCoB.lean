module

public import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LinIndepOneDelta
noncomputable section

open scoped TensorProduct

namespace Formalism.IndefR.Fin.U1

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]

theorem exists_delta (σ : E →ₐ[F] E) (hinv : ∀ e, σ (σ e) = e)
    (hfix : ∀ e, σ e = e ↔ e ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2) :
    ∃ δ : E, σ δ = -δ ∧ δ ≠ 0 := by
  have hex : ∃ e : E, e ∉ (algebraMap F E).range := by
    by_contra hne
    push_neg at hne
    have hsurj : Function.Surjective (Algebra.linearMap F E) := fun e => by
      obtain ⟨x, hx⟩ := hne e
      exact ⟨x, hx⟩
    have hinj : Function.Injective (Algebra.linearMap F E) := (algebraMap F E).injective
    have hfr := (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨hinj, hsurj⟩).finrank_eq
    rw [Module.finrank_self, h2] at hfr
    norm_num at hfr
  obtain ⟨e, he⟩ := hex
  refine ⟨e - σ e, ?_, ?_⟩
  · rw [map_sub, hinv]
    abel
  · intro h0
    apply he
    rw [← hfix]
    exact (sub_eq_zero.mp h0).symm

variable (σ : E →ₐ[F] E) (δ : E)

theorem linIndep_one_delta (hδ : σ δ = -δ) (hδ0 : δ ≠ 0) : LinearIndependent F ![(1 : E), δ] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h' : σ (s • (1 : E) + t • δ) = 0 := by rw [h, map_zero]
  rw [map_add (f := _), map_smul, map_smul, map_one, hδ] at h'
  have hs : (2 : F) • (s • (1 : E)) = 0 := by
    rw [two_smul]
    calc s • (1 : E) + s • 1 = (s • 1 + t • δ) + (s • 1 + t • -δ) := by rw [smul_neg]; abel
      _ = 0 := by rw [h, h', add_zero]
  have hs0 : s = 0 := by
    rw [smul_smul, smul_eq_zero] at hs
    rcases hs with hs | hs
    · rcases mul_eq_zero.mp hs with h2' | h2'
      · exact absurd h2' two_ne_zero
      · exact h2'
    · exact absurd hs one_ne_zero
  subst hs0
  refine ⟨rfl, ?_⟩
  rw [zero_smul, zero_add, smul_eq_zero] at h
  exact h.resolve_right hδ0

end Gen

section Coords

variable {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F]
variable (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ) (hδ0 : δ ≠ 0) (h2 : Module.finrank F E = 2)
variable (R : Type) [CommRing R] [Algebra F R]

def bE : Module.Basis (Fin 2) F E :=
  basisOfLinearIndependentOfCardEqFinrank (linIndep_one_delta σ δ hδ hδ0) (by simp [h2])

theorem bE_zero : bE σ δ hδ hδ0 h2 0 = 1 := by
  simp [bE, coe_basisOfLinearIndependentOfCardEqFinrank]
theorem bE_one : bE σ δ hδ hδ0 h2 1 = δ := by
  simp [bE, coe_basisOfLinearIndependentOfCardEqFinrank]

def bR : Module.Basis (Fin 2) R (R ⊗[F] E) := Algebra.TensorProduct.basis R (bE σ δ hδ hδ0 h2)

def mkE (a b : R) : R ⊗[F] E := a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] δ

theorem mkE_eq (a b : R) :
    mkE δ R a b = a • bR σ δ hδ hδ0 h2 R 0 + b • bR σ δ hδ hδ0 h2 R 1 := by
  simp only [mkE, bR, Algebra.TensorProduct.basis_apply, bE_zero, bE_one, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

def cP : R ⊗[F] E →ₗ[R] R := (bR σ δ hδ hδ0 h2 R).coord 0

def cQ : R ⊗[F] E →ₗ[R] R := (bR σ δ hδ hδ0 h2 R).coord 1

theorem re_mk (a b : R) : cP σ δ hδ hδ0 h2 R (mkE δ R a b) = a := by
  rw [mkE_eq σ δ hδ hδ0 h2 R]
  simp [cP, Module.Basis.coord_apply, Finsupp.single_apply]

theorem cQ_mkE (a b : R) : cQ σ δ hδ hδ0 h2 R (mkE δ R a b) = b := by
  rw [mkE_eq σ δ hδ hδ0 h2 R]
  simp [cQ, Module.Basis.coord_apply, Finsupp.single_apply]

theorem mkE_cP_cQ (x : R ⊗[F] E) :
    mkE δ R (cP σ δ hδ hδ0 h2 R x) (cQ σ δ hδ hδ0 h2 R x) = x := by
  rw [mkE_eq σ δ hδ hδ0 h2 R]
  have hx := (bR σ δ hδ hδ0 h2 R).sum_repr x
  rw [Fin.sum_univ_two] at hx
  simpa [cP, cQ, Module.Basis.coord_apply] using hx

include σ hδ hδ0 h2 in
theorem mkE_inj {a b a' b' : R} (h : mkE (F := F) δ R a b = mkE (F := F) δ R a' b') : a = a' ∧ b = b' := by
  have h1 := congrArg (cP σ δ hδ hδ0 h2 R) h
  have h2' := congrArg (cQ σ δ hδ hδ0 h2 R) h
  rw [re_mk, re_mk] at h1
  rw [cQ_mkE, cQ_mkE] at h2'
  exact ⟨h1, h2'⟩

end Coords

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (σ : E →ₐ[F] E) (δ : E) (hδ : σ δ = -δ) (Δ : F) (hΔ : algebraMap F E Δ = δ * δ)
variable (R : Type) [CommRing R] [Algebra F R]

include hΔ in
theorem mkE_mul (a b a' b' : R) :
    mkE (F := F) δ R a b * mkE (F := F) δ R a' b' =
      mkE (F := F) δ R (a * a' + algebraMap F R Δ * (b * b')) (a * b' + b * a') := by
  simp only [mkE, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [← hΔ, Algebra.algebraMap_eq_smul_one (A := E) Δ, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Algebra.smul_def Δ (b * b'), TensorProduct.add_tmul, TensorProduct.add_tmul]
  abel

theorem mkE_one : mkE (F := F) δ R 1 0 = 1 := by
  simp [mkE, Algebra.TensorProduct.one_def]

theorem mkE_zero : mkE (F := F) δ R 0 0 = 0 := by
  simp [mkE]

theorem mkE_add (a b a' b' : R) :
    mkE (F := F) δ R a b + mkE (F := F) δ R a' b' = mkE (F := F) δ R (a + a') (b + b') := by
  simp only [mkE, TensorProduct.add_tmul]
  abel

theorem mkE_sub (a b a' b' : R) :
    mkE (F := F) δ R a b - mkE (F := F) δ R a' b' = mkE (F := F) δ R (a - a') (b - b') := by
  simp only [mkE, TensorProduct.sub_tmul]
  abel

theorem algebraMap_eq_mkE (a : R) : algebraMap R (R ⊗[F] E) a = mkE (F := F) δ R a 0 := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]
  simp [mkE]

theorem smul_mkE (r a b : R) : algebraMap R (R ⊗[F] E) r * mkE (F := F) δ R a b = mkE (F := F) δ R (r * a) (r * b) := by
  rw [← Algebra.smul_def]
  simp only [mkE, smul_add, TensorProduct.smul_tmul', smul_eq_mul]

include hδ in
theorem conj_mkE (a b : R) :
    (Algebra.TensorProduct.map (AlgHom.id F R) σ) (mkE (F := F) δ R a b) = mkE (F := F) δ R a (-b) := by
  simp only [mkE, map_add (f := _), Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, hδ,
    TensorProduct.tmul_neg, TensorProduct.neg_tmul]


theorem incl_eq_mkE (α β : F) :
    (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) (algebraMap F E α + algebraMap F E β * δ) =
      mkE (F := F) δ R (algebraMap F R α) (algebraMap F R β) := by
  rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_add, ← Algebra.smul_def,
    Algebra.algebraMap_eq_smul_one (A := E) α, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one]
  rfl

end Alg

end Formalism.IndefR.Fin.U1

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

variable {D : D7}

theorem sig_sig (D : D7) (e : D.host.E) : D.sp.cm.sig (D.sp.cm.sig e) = e := star_star e

theorem sig_fix (D : D7) (e : D.host.E) : D.sp.cm.sig e = e ↔ e ∈ (algebraMap D.host.F D.host.E).range :=
  D.sp.cm.fixed e

theorem exists_delta_D (D : D7) : ∃ δ : D.host.E, D.sp.cm.sig δ = -δ ∧ δ ≠ 0 :=
  exists_delta D.sp.cm.sig (sig_sig D) (sig_fix D) D.sp.cm.deg2

theorem exists_Delta (D : D7) (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) :
    ∃ Δ : D.host.F, algebraMap D.host.F D.host.E Δ = δ * δ := by
  have : D.sp.cm.sig (δ * δ) = δ * δ := by rw [map_mul, hδ, neg_mul_neg]
  obtain ⟨Δ, hΔ⟩ := (sig_fix D _).1 this
  exact ⟨Δ, hΔ⟩

theorem isModTop (D : D7) : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩

section Pts

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

abbrev pt (a b : AF D.host.F) : AE D := mkE (F := D.host.F) δ (AF D.host.F) a b

abbrev DA (Δ : D.host.F) : AF D.host.F := algebraMap D.host.F (AF D.host.F) Δ


include hΔ in
theorem pt_mul (a b a' b' : AF D.host.F) :
    pt δ a b * pt δ a' b' = pt δ (a * a' + DA Δ * (b * b')) (a * b' + b * a') :=
  mkE_mul δ Δ hΔ (AF D.host.F) a b a' b'


theorem pt_one : pt (D := D) δ 1 0 = 1 := mkE_one δ (AF D.host.F)

abbrev coA : AE D →ₗ[AF D.host.F] AF D.host.F := cP D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F)
abbrev coB : AE D →ₗ[AF D.host.F] AF D.host.F := cQ D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F)

theorem pt_co (x : AE D) : pt δ (coA δ hδ hδ0 x) (coB δ hδ hδ0 x) = x :=
  mkE_cP_cQ D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F) x

include hδ hδ0 in
theorem pt_inj {a b a' b' : AF D.host.F} (h : pt (D := D) δ a b = pt δ a' b') : a = a' ∧ b = b' :=
  mkE_inj D.sp.cm.sig δ hδ hδ0 D.sp.cm.deg2 (AF D.host.F) h

theorem pt_eq_smul (a b : AF D.host.F) :
    pt (D := D) δ a b = a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) + b • ((1 : AF D.host.F) ⊗ₜ[D.host.F] δ) := by
  simp only [pt, mkE, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem continuous_pt : Continuous fun p : AF D.host.F × AF D.host.F => pt (D := D) δ p.1 p.2 := by
  have := isModTop D
  have hA : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have hS : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  simp only [pt_eq_smul]
  exact ((continuous_fst (X := AF D.host.F) (Y := AF D.host.F)).smul
    (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E))))).add
    ((continuous_snd (X := AF D.host.F) (Y := AF D.host.F)).smul
    (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] δ))))

end Pts

section Unit

variable (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)




theorem incA_eq_pt (α β : D.host.F) :
    incA D (algebraMap D.host.F D.host.E α + algebraMap D.host.F D.host.E β * δ) =
      pt δ (algebraMap D.host.F (AF D.host.F) α) (algebraMap D.host.F (AF D.host.F) β) :=
  incl_eq_mkE δ (AF D.host.F) α β

end Unit

end Formalism.IndefR.Fin.U1

end
